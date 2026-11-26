-- Prove2me | solution 1 for RHHeight1000.em_main_0027_0027
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:55:43.527477+00:00
-- url     : https://prove2.me/submissions/6e3a1e6e-d579-4729-b3dc-dfb03d696b19

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

noncomputable def EMRow27.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow27.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow27.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow27.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow27.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz0 := (@instHMul Real Real.instMul)

noncomputable abbrev qz807 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz249 := qz807

noncomputable def ep3 := @BSN.isNear_log_image_fff (@HMul.hMul Real Real Real qz0 qz249 Real.pi) 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 25000000012931 6465500000000000000 4138529546116343 2251799813685248 25000000012931 6465500000000000000 481788 262144

noncomputable abbrev qz250 := (@Enclosure.Real.IsNear.mulLit_ff qz807 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 262144 qz250 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 258620 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz1 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 25000000012931 6465500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000517240 258620000000000000000 4138529546116343 2251799813685248 25000000012931 6465500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 258620 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 258620 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 25000000012931 6465500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000517240 258620000000000000000 4138529546116343 2251799813685248 25000000012931 6465500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 258620 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz251 := (Real.log (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi))

theorem EMRow27.d4 : Enclosure.Real.IsNear qz251 Bool.false 120447 65536 1 131072 := @Enclosure.Real.IsNear.of_eq qz251 (Real.log (@HMul.hMul Real Real Real qz0 qz249 Real.pi)) Bool.false 120447 65536 1 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log (@HMul.hMul Real Real Real qz0 qz249 Real.pi)) Bool.false 481788 262144 2 262144 120447 65536 1 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable abbrev qz539 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz808 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz809 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz810 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz811 := (Enclosure.sfrac Bool.false 93095 1000)

noncomputable abbrev qz540 := (@HAdd.hAdd Complex Complex Complex qz808 (@HAdd.hAdd Complex Complex Complex qz808 qz809 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz810 (↑qz811) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 4))

noncomputable abbrev qz252 := (@HPow.hPow Complex Nat Complex qz539 qz540 3)

noncomputable abbrev qz2 := qz252

noncomputable def ep22 := Enclosure.Complex.IsNear qz2 Bool.true 17630895211 640000 0 1 Bool.true 6293169140659 64000000 0 1

noncomputable abbrev qz541 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz253 := qz541

noncomputable abbrev qz3 := qz253

noncomputable abbrev qz254 := qz539

noncomputable abbrev qz255 := qz540

noncomputable abbrev qz4 := (@HPow.hPow Complex Nat Complex qz254 qz255 2)

noncomputable abbrev qz5 := qz255

noncomputable def ep23 := @Enclosure.Complex.IsNear.of_eq qz2 (@HMul.hMul Complex Complex Complex qz3 qz4 qz5) Bool.true 17630895211 640000 0 1 Bool.true 6293169140659 64000000

noncomputable def ep24 := @Enclosure.Complex.IsNear.mul qz4 qz5 Bool.true 17630895211 640000 0 1 Bool.true 6293169140659 64000000 0

noncomputable def ep25 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz4) (Complex.re qz5)) (@HMul.hMul Real Real Real qz0 (Complex.im qz4) (Complex.im qz5)) 5844211737 640000 0 1 5893341737 320000

noncomputable def ep26 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz4) (Complex.re qz5) 343777161 160000 0 1 17000 4000 0 1

noncomputable def ep27 := @Enclosure.Complex.IsNear.re_isNear qz4 Bool.true 343777161 160000 0 1 Bool.false 316523 800 0 1

noncomputable abbrev qz256 := (@HPow.hPow Complex Nat Complex qz539 qz540 1)

noncomputable abbrev qz6 := qz256

noncomputable def ep28 := @Enclosure.Complex.IsNear.of_eq qz4 (@HMul.hMul Complex Complex Complex qz3 qz6 qz5) Bool.true 343777161 160000 0 1 Bool.false 316523 800

noncomputable def ep29 := @Enclosure.Complex.IsNear.mul qz6 qz5 Bool.true 343777161 160000 0 1 Bool.false 316523 800 0

noncomputable abbrev qz7 := (Complex.re qz256)

noncomputable abbrev qz8 := (Complex.im qz256)

noncomputable def ep30 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz7 (Complex.re qz5)) (@HMul.hMul Real Real Real qz0 qz8 (Complex.im qz5)) 289 16 0 1 346667161 160000

noncomputable def ep31 := @Enclosure.Real.IsNear.mulLit_ff qz7 (Complex.re qz5) 17000 4000 0 1 17000 4000 0 1

noncomputable def ep32 := @Enclosure.Complex.IsNear.re_isNear qz6 Bool.false 17000 4000 0 1 Bool.false 186190 4000 0 1

noncomputable def ep33 := @Enclosure.Complex.IsNear.of_eq qz6 qz5 Bool.false 17000 4000 0 1 Bool.false 186190 4000 0

noncomputable abbrev qz257 := qz811

noncomputable abbrev qz9 := qz257

noncomputable abbrev qz812 := (Enclosure.sfrac Bool.false 17000 4000)

noncomputable abbrev qz258 := (Complex.mk qz812 (Enclosure.sfrac Bool.false 186190 4000))

noncomputable abbrev qz813 := (BSN.w_shift_mk qz9 Bool.false 93095 1000 4 (@Eq.refl Real qz9) rfl)

noncomputable def ep34 := @Enclosure.Complex.IsNear.of_eq qz5 qz258 Bool.false 17000 4000 0 1 Bool.false 186190 4000 0 1 qz813

noncomputable abbrev qz259 := (Enclosure.sfrac Bool.false 186190 4000)

noncomputable abbrev qz814 := (Enclosure.Real.IsNear.const Bool.false 17000 4000)

noncomputable abbrev qz10 := (@ep33 1 (BSN.pow_one_c qz255) (ep34 (@Enclosure.Complex.IsNear.mk qz812 qz259 Bool.false 17000 4000 0 1 Bool.false 186190 4000 0 1 qz814 (Enclosure.Real.IsNear.const Bool.false 186190 4000))))

noncomputable abbrev qz11 := (ep34 (@Enclosure.Complex.IsNear.mk qz812 qz259 Bool.false 17000 4000 0 1 Bool.false 186190 4000 0 1 qz814 (Enclosure.Real.IsNear.const Bool.false 186190 4000)))

noncomputable abbrev qz542 := (@Enclosure.Complex.IsNear.re_isNear qz5 Bool.false 17000 4000 0 1 Bool.false 186190 4000 0 1 qz11)

noncomputable def ep35 := @ep31 289 16 0 1 (ep32 qz10) qz542

noncomputable def ep36 := @Enclosure.Real.IsNear.mulLit_ff qz8 (Complex.im qz5) 186190 4000 0 1 186190 4000 0 1

noncomputable def ep37 := @Enclosure.Complex.IsNear.im_isNear qz6 Bool.false 17000 4000 0 1 Bool.false 186190 4000 0 1

noncomputable abbrev qz543 := (@Enclosure.Complex.IsNear.im_isNear qz5 Bool.false 17000 4000 0 1 Bool.false 186190 4000 0 1 qz11)

noncomputable def ep38 := @ep36 346667161 160000 0 1 (ep37 qz10) qz543

noncomputable def ep39 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz7 (Complex.im qz5)) (@HMul.hMul Real Real Real qz0 qz8 (Complex.re qz5)) 316523 1600 0 1 316523 1600

noncomputable def ep40 := @Enclosure.Real.IsNear.mulLit_ff qz7 (Complex.im qz5) 17000 4000 0 1 186190 4000 0 1

noncomputable def ep41 := @ep40 316523 1600 0 1 (ep32 qz10) qz543

noncomputable def ep42 := @Enclosure.Real.IsNear.mulLit_ff qz8 (Complex.re qz5) 186190 4000 0 1 17000 4000 0 1

noncomputable def ep43 := @ep42 316523 1600 0 1 (ep37 qz10) qz542

noncomputable abbrev qz544 := (@ep28 0 1 (BSN.pow_succ_c qz5 1 2 rfl) (@ep29 1 (@ep30 0 1 5500434576 343777161 160000 0 1 (ep35 rfl) (ep38 rfl) rfl rfl) (@ep39 0 1 1012873600 316523 800 0 1 (ep41 rfl) (ep43 rfl) rfl rfl)))

noncomputable def ep44 := @ep26 5844211737 640000 0 1 (ep27 qz544) qz542

noncomputable def ep45 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz4) (Complex.im qz5) 316523 800 0 1 186190 4000 0 1

noncomputable def ep46 := @Enclosure.Complex.IsNear.im_isNear qz4 Bool.true 343777161 160000 0 1 Bool.false 316523 800 0 1

noncomputable def ep47 := @ep45 5893341737 320000 0 1 (ep46 qz544) qz543

noncomputable def ep48 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re qz4) (Complex.im qz5)) (@HMul.hMul Real Real Real qz0 (Complex.im qz4) (Complex.re qz5)) 6400786960659 64000000 0 1 5380891 3200

noncomputable def ep49 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz4) (Complex.im qz5) 343777161 160000 0 1 186190 4000 0 1

noncomputable def ep50 := @ep49 6400786960659 64000000 0 1 (ep27 qz544) qz543

noncomputable def ep51 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz4) (Complex.re qz5) 316523 800 0 1 17000 4000 0 1

noncomputable def ep52 := @ep51 5380891 3200 0 1 (ep46 qz544) qz542

theorem EMRow27.d5 : ep22 := @ep23 0 1 (BSN.pow_succ_c qz5 2 3 rfl) (@ep24 1 (@ep25 0 1 5641886467520000 17630895211 640000 0 1 (ep44 rfl) (ep47 rfl) rfl rfl) (@ep48 0 1 20138141250108800 6293169140659 64000000 0 1 (ep50 rfl) (ep52 rfl) rfl rfl))

noncomputable def ep53 := nat_lit 8589934592000000000000000

noncomputable def ep54 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep53 ep2 ep53 600168 524288 1 258620 600168 524288 1 258620 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep55 := nat_lit 17179869184000000000000000

noncomputable def ep56 := nat_lit 18396140817044028275299783

noncomputable def ep57 := nat_lit 35576010001044028275299783

noncomputable def ep58 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep59 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep60 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep61 := BSN.log_dyadic_bound ep56 ep57 11 10 ep58 524288 258620 ep59 ep60 600168 ep5 ep55 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep56) (BSN.artanhQ ep57) 0 10 ep59 ep58 ep60 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep62 := nat_lit 18396140817044045455168967

noncomputable def ep63 := nat_lit 35576010001044045455168967

noncomputable def ep64 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep65 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep66 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep67 := BSN.log_dyadic_bound ep62 ep63 11 10 ep64 524288 258620 ep65 ep66 600168 ep14 ep55 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep62) (BSN.artanhQ ep63) 0 10 ep65 ep64 ep66 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep54 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep53 600168 524288 1 258620 Bool.false (BSN.logfrac_isNear ep5 ep55 1 ep0 ep53 600168 524288 258620 rfl rfl rfl (ep61 rfl))) (BSN.isNear_log_sfrac ep2 ep53 600168 524288 1 258620 Bool.false (BSN.logfrac_isNear ep14 ep55 1 ep2 ep53 600168 524288 258620 rfl rfl rfl (ep67 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow27.d6 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep68

noncomputable abbrev qz545 := qz808

noncomputable abbrev qz546 := (@HDiv.hDiv Complex Complex Complex qz810 (1 : Complex) (2 : Complex))

noncomputable abbrev qz260 := (@HAdd.hAdd Complex Complex Complex qz545 qz546 (@HMul.hMul Complex Complex Complex qz541 Complex.I ↑qz811))

noncomputable abbrev qz12 := qz260

noncomputable abbrev qz261 := qz545

noncomputable abbrev qz13 := qz261

noncomputable abbrev qz815 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz14 := qz815

noncomputable abbrev qz15 := (@Neg.neg Complex Complex.instNeg qz260)

noncomputable abbrev qz816 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 8) qz15)

noncomputable def ep69 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 9) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 8) qz816) Bool.false 139475645627 274877906944 43868409361493 17772231073464320 Bool.false 140104265 274877906944 43976001359063 17772231073464320

noncomputable def ep70 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 8) qz816 Bool.false 12954950275 34359738368 19638548726911 8886115536732160 Bool.true 45097442759 137438953472 9841420026383 4443057768366080 Bool.false

noncomputable abbrev qz817 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 7) qz15)

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 8) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 7) qz817) Bool.false 12954950275 34359738368 19638548726911 8886115536732160 Bool.true 45097442759 137438953472 9841420026383 4443057768366080

noncomputable def ep72 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 7) qz817 Bool.false 52685355521 274877906944 34352665809911 17772231073464320 Bool.true 2823999321 4294967296 17214166198463 8886115536732160 Bool.false

noncomputable abbrev qz818 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 6) qz15)

noncomputable def ep73 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 7) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 6) qz818) Bool.false 52685355521 274877906944 34352665809911 17772231073464320 Bool.true 2823999321 4294967296 17214166198463 8886115536732160

noncomputable def ep74 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 6) qz818 Bool.false 159912901429 274877906944 29033116319891 17772231073464320 Bool.true 53457238603 68719476736 14565588406353 8886115536732160 Bool.true

noncomputable abbrev qz819 := (@Nat.cast Complex Complex.instNatCast 5)

noncomputable abbrev qz16 := qz819

noncomputable def ep75 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 6) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 5) (@HPow.hPow Complex Complex Complex qz14 qz16 qz15)) Bool.false 159912901429 274877906944 29033116319891 17772231073464320 Bool.true 53457238603 68719476736 14565588406353 8886115536732160

noncomputable def ep76 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 5) (@HPow.hPow Complex Complex Complex qz14 qz16 qz15) Bool.false 90016285715 274877906944 23206867047631 17772231073464320 Bool.true 78738155121 68719476736 5824079164559 4443057768366080 Bool.false

noncomputable abbrev qz547 := (@Nat.cast Complex Complex.instNatCast 4)

noncomputable abbrev qz262 := qz547

noncomputable abbrev qz17 := qz262

noncomputable def ep77 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 5) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 4) (@HPow.hPow Complex Complex Complex qz14 qz17 qz15)) Bool.false 90016285715 274877906944 23206867047631 17772231073464320 Bool.true 78738155121 68719476736 5824079164559 4443057768366080

noncomputable def ep78 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 4) (@HPow.hPow Complex Complex Complex qz14 qz17 qz15) Bool.false 111565333057 137438953472 208732804169 222152888418304 Bool.true 43644498819 34359738368 420311734369 444305776836608 Bool.true

noncomputable abbrev qz548 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable def ep79 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 4) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 3) (@HPow.hPow Complex Complex Complex qz14 qz548 qz15)) Bool.false 111565333057 137438953472 208732804169 222152888418304 Bool.true 43644498819 34359738368 420311734369 444305776836608

noncomputable def ep80 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 3) (@HPow.hPow Complex Complex Complex qz14 qz548 qz15) Bool.false 7828134893 8589934592 919014630233 1777223107346432 Bool.true 24104132127 34359738368 462445180127 888611553673216 Bool.true

noncomputable abbrev qz549 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable def ep81 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 3) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 2) (@HPow.hPow Complex Complex Complex qz14 qz549 qz15)) Bool.false 7828134893 8589934592 919014630233 1777223107346432 Bool.true 24104132127 34359738368 462445180127 888611553673216

noncomputable def ep82 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 2) (@HPow.hPow Complex Complex Complex qz14 qz549 qz15) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz263 := (Enclosure.sfrac Bool.false 0 1)

noncomputable def ep83 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz263) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz12)

noncomputable abbrev qz264 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable abbrev qz265 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log qz807))

noncomputable def ep84 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz549 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz264 (Real.cos qz265)) (@HMul.hMul Real Real Real qz0 qz264 (@Neg.neg Real Real.instNeg (Real.sin qz265)))) Bool.true 761799699 8589934592 919014630233 1777223107346432 Bool.true 24104132127 34359738368 462445180127 888611553673216 (BSN.cpow_neg_s_mk qz9 93095 1000 2 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz266 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep85 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2) qz266)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2) qz266)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep86 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 129310 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz267 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz268 := (BSN.sinOddQ 1073741824)

noncomputable def ep87 := BSN.sin_dyadic_bound_f 135026180 1073741824 1 0 524288 258873 0 1 1 0 1 1 65756 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 135026180) qz267 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 135026180) qz268 0 0 rfl) rfl rfl

noncomputable abbrev qz269 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz270 := (Real.log qz807)

noncomputable abbrev qz271 := (Enclosure.Real.IsNear.const Bool.false 93095 1000)

noncomputable abbrev qz272 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz550 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 129310 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 129310 rfl rfl rfl (ep86 rfl)))

noncomputable abbrev qz820 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33831467) qz269)

noncomputable def ep88 := @Enclosure.Real.IsNear.cos_image qz265 qz820 Bool.false 33831467 524288 379 524288 Bool.true 65756 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz265 Bool.false 422893347 6553600 18619 25862000 33831467 524288 379 524288 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz270 93095 1000 0 1 181704 262144 1 129310 422893347 6553600 18619 25862000 qz271 qz550 rfl) rfl) (Enclosure.sfrac_false_div 33831467 524288) (BSN.cos_reduce1 qz820 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9501622740552813379584) qz272) 226375608064910080 72057594037927936 Bool.false 65756 524288 10 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 33831467 524288 226375608064910080 72057594037927936 10 9501622740552813379584 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 65756 524288 9501622740552813379584 75557863725914323419136 135026180 1073741824 258873 258620 (ep87 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep89 := nat_lit 332408350427348939200021977760000

noncomputable def ep90 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep91 := nat_lit 478522078482569714245370541700924047360

noncomputable abbrev qz273 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz274 := (BSN.cosOddQ 1073741824)

noncomputable def ep92 := BSN.cos_dyadic_bound_f 135026180 1073741824 2 1 524288 258873 ep89 ep90 ep89 ep89 ep91 ep89 520147 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 135026180) qz273 0 1 ep89 ep90 ep89 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 135026180) qz274 0 1 ep89 ep91 ep89 rfl rfl rfl rfl) rfl rfl

noncomputable def ep93 := @Enclosure.Real.IsNear.sin_image qz265 qz820 Bool.false 33831467 524288 379 524288 Bool.false 520147 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz265 Bool.false 422893347 6553600 18619 25862000 33831467 524288 379 524288 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz270 93095 1000 0 1 181704 262144 1 129310 422893347 6553600 18619 25862000 qz271 qz550 rfl) rfl) (Enclosure.sfrac_false_div 33831467 524288) (BSN.sin_reduce1 qz820 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9501622740552813379584) qz272) 226375608064910080 72057594037927936 Bool.false 520147 524288 10 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 33831467 524288 226375608064910080 72057594037927936 10 9501622740552813379584 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 520147 524288 9501622740552813379584 75557863725914323419136 135026180 1073741824 258873 258620 (ep92 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz551 := (@Enclosure.Real.IsNear.recentre' qz264 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep85 rfl rfl) rfl)

noncomputable def ep94 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz264 (Real.cos qz265)) (@HMul.hMul Real Real Real qz0 qz264 (@Neg.neg Real Real.instNeg (Real.sin qz265))) Bool.true 761799699 8589934592 919014630233 1777223107346432 Bool.true 24104132127 34359738368 462445180127 888611553673216 (@Enclosure.Real.IsNear.mulLit_ft qz264 (Real.cos qz265) 46341 65536 1 262144 16439 131072 24766389 33897840640 761799699 8589934592 919014630233 1777223107346432 qz551 (@Enclosure.Real.IsNear.recentre' (Real.cos qz265) Bool.true 65756 524288 49532778 67795681280 16439 131072 24766389 33897840640 (ep88 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz264 (@Neg.neg Real Real.instNeg (Real.sin qz265)) 46341 65536 1 262144 520147 524288 24766389 33897840640 24104132127 34359738368 462445180127 888611553673216 qz551 (@Enclosure.Real.IsNear.neg (Real.sin qz265) Bool.false 520147 524288 24766389 33897840640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz265) Bool.false 520147 524288 49532778 67795681280 520147 524288 24766389 33897840640 (ep93 rfl rfl) rfl)) rfl)

noncomputable abbrev qz275 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable def ep95 := @ep82 761799699 8589934592 919014630233 1777223107346432 Bool.true 24104132127 34359738368 462445180127 888611553673216 Bool.false 7828134893 7828134893 8589934592 919014630233 1777223107346432 Bool.true 24104132127 24104132127 34359738368 462445180127 888611553673216 (ep83 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz263 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz275)) (ep84 ep94) rfl rfl

noncomputable abbrev qz276 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz277 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep96 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz548 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz276 (Real.cos qz277)) (@HMul.hMul Real Real Real qz0 qz276 (@Neg.neg Real Real.instNeg (Real.sin qz277)))) Bool.true 13684825231 137438953472 750847803119 1777223107346432 Bool.true 4885091673 8589934592 378178288611 888611553673216 (BSN.cpow_neg_s_mk qz9 93095 1000 3 (@Eq.refl Real qz9) rfl)

noncomputable def ep97 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3) qz266)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3) qz266)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep98 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 129310 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep99 := nat_lit 1199705358899395129822172335645456

noncomputable def ep100 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep101 := nat_lit 1116551516459329333239197930635489443840

noncomputable def ep102 := BSN.sin_dyadic_bound_f 186109546 1073741824 2 1 524288 258873 ep99 ep100 ep99 ep99 ep101 ep99 90419 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 186109546) qz267 0 1 ep99 ep100 ep99 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 186109546) qz268 0 1 ep99 ep101 ep99 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz278 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz279 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz280 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz552 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 129310 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 129310 rfl rfl rfl (ep98 rfl)))

noncomputable abbrev qz821 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26810801) qz278)

noncomputable def ep103 := @Enclosure.Real.IsNear.cos_image qz277 qz821 Bool.false 26810801 262144 379 524288 Bool.true 90419 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz277 Bool.false 2681080143 26214400 18619 25862000 26810801 262144 379 524288 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz279 93095 1000 0 1 287994 262144 1 129310 2681080143 26214400 18619 25862000 qz271 qz552 rfl) rfl) (Enclosure.sfrac_false_div 26810801 262144) (BSN.cos_reduce1 qz821 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6548147542438468124672) qz280) 226375608064910080 72057594037927936 Bool.false 90419 524288 16 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 26810801 262144 226375608064910080 72057594037927936 16 6548147542438468124672 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 90419 524288 6548147542438468124672 37778931862957161709568 186109546 1073741824 258873 258620 (ep102 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep104 := BSN.cos_dyadic_bound_f 186109546 1073741824 2 1 524288 258873 ep99 ep90 ep99 ep99 ep91 ep99 516432 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 186109546) qz273 0 1 ep99 ep90 ep99 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 186109546) qz274 0 1 ep99 ep91 ep99 rfl rfl rfl rfl) rfl rfl

noncomputable def ep105 := @Enclosure.Real.IsNear.sin_image qz277 qz821 Bool.false 26810801 262144 379 524288 Bool.false 516432 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz277 Bool.false 2681080143 26214400 18619 25862000 26810801 262144 379 524288 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz279 93095 1000 0 1 287994 262144 1 129310 2681080143 26214400 18619 25862000 qz271 qz552 rfl) rfl) (Enclosure.sfrac_false_div 26810801 262144) (BSN.sin_reduce1 qz821 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6548147542438468124672) qz280) 226375608064910080 72057594037927936 Bool.false 516432 524288 16 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 26810801 262144 226375608064910080 72057594037927936 16 6548147542438468124672 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 516432 524288 6548147542438468124672 37778931862957161709568 186109546 1073741824 258873 258620 (ep104 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz553 := (@Enclosure.Real.IsNear.recentre' qz276 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep97 rfl rfl) rfl)

noncomputable def ep106 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz276 (Real.cos qz277)) (@HMul.hMul Real Real Real qz0 qz276 (@Neg.neg Real Real.instNeg (Real.sin qz277))) Bool.true 13684825231 137438953472 750847803119 1777223107346432 Bool.true 4885091673 8589934592 378178288611 888611553673216 (@Enclosure.Real.IsNear.mulLit_ft qz276 (Real.cos qz277) 151349 262144 1 262144 90419 524288 24766389 33897840640 13684825231 137438953472 750847803119 1777223107346432 qz553 (@Enclosure.Real.IsNear.recentre' (Real.cos qz277) Bool.true 90419 524288 49532778 67795681280 90419 524288 24766389 33897840640 (ep103 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz276 (@Neg.neg Real Real.instNeg (Real.sin qz277)) 151349 262144 1 262144 32277 32768 24766389 33897840640 4885091673 8589934592 378178288611 888611553673216 qz553 (@Enclosure.Real.IsNear.neg (Real.sin qz277) Bool.false 32277 32768 24766389 33897840640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz277) Bool.false 516432 524288 49532778 67795681280 32277 32768 24766389 33897840640 (ep105 rfl rfl) rfl)) rfl)

noncomputable def ep107 := @ep80 13684825231 137438953472 750847803119 1777223107346432 Bool.true 4885091673 8589934592 378178288611 888611553673216 Bool.false 958338913694325407744 111565333057 137438953472 208732804169 222152888418304 Bool.true 374903390155831246848 43644498819 34359738368 420311734369 444305776836608 (ep81 (BSN.head_sum_c_succ qz12 2 3 rfl rfl) (ep95 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep96 ep106) rfl rfl

noncomputable abbrev qz281 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable abbrev qz282 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep108 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz17 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz281 (Real.cos qz282)) (@HMul.hMul Real Real Real qz0 qz281 (@Neg.neg Real Real.instNeg (Real.sin qz282)))) Bool.true 133114380399 274877906944 6508242714111 17772231073464320 Bool.false 8550842517 68719476736 1620961820869 4443057768366080 (BSN.cpow_neg_s_mk qz9 93095 1000 4 (@Eq.refl Real qz9) rfl)

noncomputable def ep109 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4) qz266)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4) qz266)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep110 := nat_lit 318077276165597140789031982421875

noncomputable def ep111 := nat_lit 49379992292270016474244603430625

noncomputable def ep112 := nat_lit 20095619060363156210525625

noncomputable def ep113 := BSN.log_dyadic_bound 3 5 14 13 ep110 262144 129310 ep111 ep112 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep111 ep110 ep112 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep114 := nat_lit 5318694945634758753176536953655296

noncomputable def ep115 := BSN.cos_dyadic_bound_f 270054408 1073741824 2 1 524288 258873 ep114 ep90 ep114 ep114 ep91 ep114 507793 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 270054408) qz273 0 1 ep114 ep90 ep114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 270054408) qz274 0 1 ep114 ep91 ep114 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz283 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz554 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 129310 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 129310 rfl rfl rfl (ep113 rfl)))

noncomputable abbrev qz822 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67662935) qz269)

noncomputable def ep116 := @Enclosure.Real.IsNear.cos_image qz282 qz822 Bool.false 67662935 524288 189 262144 Bool.true 507793 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz282 Bool.false 422893347 3276800 18619 25862000 67662935 524288 189 262144 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz283 93095 1000 0 1 363408 262144 1 129310 422893347 3276800 18619 25862000 qz271 qz554 rfl) rfl) (Enclosure.sfrac_false_div 67662935 524288) (BSN.cos_reduce2 qz822 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19003389596293702615040) qz272) 226375608064910080 72057594037927936 Bool.false 507793 524288 20 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 67662935 524288 226375608064910080 72057594037927936 20 19003389596293702615040 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 507793 524288 19003389596293702615040 75557863725914323419136 270054408 1073741824 258873 258620 (ep115 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep117 := BSN.sin_dyadic_bound_f 270054408 1073741824 2 1 524288 258873 ep114 ep100 ep114 ep114 ep101 ep114 130476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 270054408) qz267 0 1 ep114 ep100 ep114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 270054408) qz268 0 1 ep114 ep101 ep114 rfl rfl rfl rfl) rfl rfl

noncomputable def ep118 := @Enclosure.Real.IsNear.sin_image qz282 qz822 Bool.false 67662935 524288 189 262144 Bool.true 130476 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz282 Bool.false 422893347 3276800 18619 25862000 67662935 524288 189 262144 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz283 93095 1000 0 1 363408 262144 1 129310 422893347 3276800 18619 25862000 qz271 qz554 rfl) rfl) (Enclosure.sfrac_false_div 67662935 524288) (BSN.sin_reduce2 qz822 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19003389596293702615040) qz272) 226375608064910080 72057594037927936 Bool.false 130476 524288 20 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 67662935 524288 226375608064910080 72057594037927936 20 19003389596293702615040 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 130476 524288 19003389596293702615040 75557863725914323419136 270054408 1073741824 258873 258620 (ep117 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz555 := (@Enclosure.Real.IsNear.recentre' qz281 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep109 rfl rfl) rfl)

noncomputable def ep119 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz281 (Real.cos qz282)) (@HMul.hMul Real Real Real qz0 qz281 (@Neg.neg Real Real.instNeg (Real.sin qz282))) Bool.true 133114380399 274877906944 6508242714111 17772231073464320 Bool.false 8550842517 68719476736 1620961820869 4443057768366080 (@Enclosure.Real.IsNear.mulLit_ft qz281 (Real.cos qz282) 262143 524288 1 524288 507793 524288 12350867 16948920320 133114380399 274877906944 6508242714111 17772231073464320 qz555 (@Enclosure.Real.IsNear.recentre' (Real.cos qz282) Bool.true 507793 524288 24701734 33897840640 507793 524288 12350867 16948920320 (ep116 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz281 (@Neg.neg Real Real.instNeg (Real.sin qz282)) 262143 524288 1 524288 32619 131072 12350867 16948920320 8550842517 68719476736 1620961820869 4443057768366080 qz555 (@Enclosure.Real.IsNear.neg (Real.sin qz282) Bool.true 32619 131072 12350867 16948920320 (@Enclosure.Real.IsNear.recentre' (Real.sin qz282) Bool.true 130476 524288 24701734 33897840640 32619 131072 12350867 16948920320 (ep118 rfl rfl) rfl)) rfl)

noncomputable def ep120 := @ep78 133114380399 274877906944 6508242714111 17772231073464320 Bool.false 8550842517 68719476736 1620961820869 4443057768366080 Bool.false 12371744104106143252480 90016285715 274877906944 23206867047631 17772231073464320 Bool.true 2705422409536559382528 78738155121 68719476736 5824079164559 4443057768366080 (ep79 (BSN.head_sum_c_succ qz12 3 4 rfl rfl) (ep107 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep108 ep119) rfl rfl

noncomputable abbrev qz284 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable abbrev qz285 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep121 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz16 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz284 (Real.cos qz285)) (@HMul.hMul Real Real Real qz0 qz284 (@Neg.neg Real Real.instNeg (Real.sin qz285)))) Bool.false 34948307857 137438953472 291312463613 888611553673216 Bool.false 12640458259 34359738368 583486015447 1777223107346432 (BSN.cpow_neg_s_mk qz9 93095 1000 5 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz286 := (@Nat.cast Real Real.instNatCast 5)

noncomputable def ep122 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz286) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz286) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz286 qz266)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz286 qz266)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep123 := nat_lit 11734546589655452485523914939250625

noncomputable def ep124 := nat_lit 2429970938528035899633153341031900

noncomputable def ep125 := nat_lit 824199001261152424427520000

noncomputable def ep126 := BSN.log_dyadic_bound 2 3 17 16 ep123 262144 129310 ep124 ep125 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep124 ep123 ep125 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep127 := nat_lit 177841377630898903499003099740435216

noncomputable def ep128 := BSN.sin_dyadic_bound_f 649393898 1073741824 2 1 524288 258873 ep127 ep100 ep127 ep127 ep101 ep127 298106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 649393898) qz267 0 1 ep127 ep100 ep127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 649393898) qz268 0 1 ep127 ep101 ep127 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz287 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz556 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 129310 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 129310 rfl rfl rfl (ep126 rfl)))

noncomputable abbrev qz823 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78554305) qz269)

noncomputable def ep129 := @Enclosure.Real.IsNear.cos_image qz285 qz823 Bool.false 78554305 524288 379 524288 Bool.false 298106 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz285 Bool.false 490964411 3276800 18619 25862000 78554305 524288 379 524288 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz287 93095 1000 0 1 421904 262144 1 129310 490964411 3276800 18619 25862000 qz271 qz556 rfl) rfl) (Enclosure.sfrac_false_div 78554305 524288) (BSN.cos_reduce3 qz823 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45697033135265582940160) qz272) 226375608064910080 72057594037927936 Bool.false 298106 524288 23 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 78554305 524288 226375608064910080 72057594037927936 23 45697033135265582940160 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 298106 524288 45697033135265582940160 75557863725914323419136 649393898 1073741824 258873 258620 (ep128 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep130 := BSN.cos_dyadic_bound_f 649393898 1073741824 2 1 524288 258873 ep127 ep90 ep127 ep127 ep91 ep127 431288 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 649393898) qz273 0 1 ep127 ep90 ep127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 649393898) qz274 0 1 ep127 ep91 ep127 rfl rfl rfl rfl) rfl rfl

noncomputable def ep131 := @Enclosure.Real.IsNear.sin_image qz285 qz823 Bool.false 78554305 524288 379 524288 Bool.true 431288 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz285 Bool.false 490964411 3276800 18619 25862000 78554305 524288 379 524288 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz287 93095 1000 0 1 421904 262144 1 129310 490964411 3276800 18619 25862000 qz271 qz556 rfl) rfl) (Enclosure.sfrac_false_div 78554305 524288) (BSN.sin_reduce3 qz823 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45697033135265582940160) qz272) 226375608064910080 72057594037927936 Bool.false 431288 524288 23 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 78554305 524288 226375608064910080 72057594037927936 23 45697033135265582940160 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 431288 524288 45697033135265582940160 75557863725914323419136 649393898 1073741824 258873 258620 (ep130 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz557 := (@Enclosure.Real.IsNear.recentre' qz284 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep122 rfl rfl) rfl)

noncomputable def ep132 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz284 (Real.cos qz285)) (@HMul.hMul Real Real Real qz0 qz284 (@Neg.neg Real Real.instNeg (Real.sin qz285))) Bool.false 34948307857 137438953472 291312463613 888611553673216 Bool.false 12640458259 34359738368 583486015447 1777223107346432 (@Enclosure.Real.IsNear.mulLit_ff qz284 (Real.cos qz285) 234469 524288 1 524288 149053 262144 24766389 33897840640 34948307857 137438953472 291312463613 888611553673216 qz557 (@Enclosure.Real.IsNear.recentre' (Real.cos qz285) Bool.false 298106 524288 49532778 67795681280 149053 262144 24766389 33897840640 (ep129 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz284 (@Neg.neg Real Real.instNeg (Real.sin qz285)) 234469 524288 1 524288 53911 65536 24766389 33897840640 12640458259 34359738368 583486015447 1777223107346432 qz557 (@Enclosure.Real.IsNear.neg (Real.sin qz285) Bool.true 53911 65536 24766389 33897840640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz285) Bool.true 431288 524288 49532778 67795681280 53911 65536 24766389 33897840640 (ep131 rfl rfl) rfl)) rfl)

noncomputable def ep133 := @ep76 34948307857 137438953472 291312463613 888611553673216 Bool.false 12640458259 34359738368 583486015447 1777223107346432 Bool.false 21978261819072853311488 159912901429 274877906944 29033116319891 17772231073464320 Bool.true 1836776732274829819904 53457238603 68719476736 14565588406353 8886115536732160 (ep77 (BSN.head_sum_c_succ qz12 4 5 rfl rfl) (ep120 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep121 ep132) rfl rfl

noncomputable abbrev qz824 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz288 := (@Inv.inv Real Real.instInv (Real.sqrt qz824))

noncomputable abbrev qz289 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep134 := @Enclosure.Complex.IsNear.of_eq qz818 (Complex.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz289)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz289)))) Bool.true 26806886477 68719476736 265977474501 888611553673216 Bool.false 8273249467 68719476736 264857779211 888611553673216 (BSN.cpow_neg_s_mk qz9 93095 1000 6 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz825 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz266)

noncomputable def ep135 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz824) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz824) (Real.sqrt qz825) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz825) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep136 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 129310 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz290 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep137 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz290 93095 1000 0 1 4034681531866359 2251799813685248 50000000012931 6465500000000000000 75121735441819738221 450359962737049600 930950000240762289 1293100000000000000000 qz271 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 50000000012931 6465500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz825) Bool.false 16922680887833197019136 9444732965739290427392 1000000000258620 129310000000000000000 4034681531866359 2251799813685248 50000000012931 6465500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep136 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep138 := nat_lit 10673721844562690534941159325250625

noncomputable def ep139 := BSN.cos_dyadic_bound_f 321424495 1073741824 2 1 524288 258873 ep138 ep90 ep138 ep138 ep91 ep138 500972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 321424495) qz273 0 1 ep138 ep90 ep138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 321424495) qz274 0 1 ep138 ep91 ep138 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz826 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43726605) qz278)

noncomputable def ep140 := @Enclosure.Real.IsNear.cos_image qz289 qz826 Bool.false 43726605 262144 189 262144 Bool.true 500972 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz289 Bool.false 75121735441819738221 450359962737049600 930950000240762289 1293100000000000000000 43726605 262144 189 262144 (ep137 rfl) rfl) (Enclosure.sfrac_false_div 43726605 262144) (BSN.cos_reduce2 qz826 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11309119033474222653440) qz280) 226375608064910080 72057594037927936 Bool.false 500972 524288 26 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 43726605 262144 226375608064910080 72057594037927936 26 11309119033474222653440 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 500972 524288 11309119033474222653440 37778931862957161709568 321424495 1073741824 258873 258620 (ep139 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep141 := BSN.sin_dyadic_bound_f 321424495 1073741824 2 1 524288 258873 ep138 ep100 ep138 ep138 ep101 ep138 154612 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 321424495) qz267 0 1 ep138 ep100 ep138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 321424495) qz268 0 1 ep138 ep101 ep138 rfl rfl rfl rfl) rfl rfl

noncomputable def ep142 := @Enclosure.Real.IsNear.sin_image qz289 qz826 Bool.false 43726605 262144 189 262144 Bool.true 154612 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz289 Bool.false 75121735441819738221 450359962737049600 930950000240762289 1293100000000000000000 43726605 262144 189 262144 (ep137 rfl) rfl) (Enclosure.sfrac_false_div 43726605 262144) (BSN.sin_reduce2 qz826 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11309119033474222653440) qz280) 226375608064910080 72057594037927936 Bool.false 154612 524288 26 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 43726605 262144 226375608064910080 72057594037927936 26 11309119033474222653440 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 154612 524288 11309119033474222653440 37778931862957161709568 321424495 1073741824 258873 258620 (ep141 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz558 := (@Enclosure.Real.IsNear.recentre' qz288 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep135 rfl rfl) rfl)

noncomputable def ep143 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz289)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz289))) Bool.true 26806886477 68719476736 265977474501 888611553673216 Bool.false 8273249467 68719476736 264857779211 888611553673216 (@Enclosure.Real.IsNear.mulLit_ft qz288 (Real.cos qz289) 214039 524288 1 524288 125243 131072 12350867 16948920320 26806886477 68719476736 265977474501 888611553673216 qz558 (@Enclosure.Real.IsNear.recentre' (Real.cos qz289) Bool.true 500972 524288 24701734 33897840640 125243 131072 12350867 16948920320 (ep140 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz288 (@Neg.neg Real Real.instNeg (Real.sin qz289)) 214039 524288 1 524288 38653 131072 12350867 16948920320 8273249467 68719476736 264857779211 888611553673216 qz558 (@Enclosure.Real.IsNear.neg (Real.sin qz289) Bool.true 38653 131072 12350867 16948920320 (@Enclosure.Real.IsNear.recentre' (Real.sin qz289) Bool.true 154612 524288 24701734 33897840640 38653 131072 12350867 16948920320 (ep142 rfl rfl) rfl)) rfl)

noncomputable def ep144 := @ep74 26806886477 68719476736 265977474501 888611553673216 Bool.false 8273249467 68719476736 264857779211 888611553673216 Bool.false 3620510063053248659456 52685355521 274877906944 34352665809911 17772231073464320 Bool.true 3105020090271028740096 2823999321 4294967296 17214166198463 8886115536732160 (ep75 (BSN.head_sum_c_succ qz12 5 6 rfl rfl) (ep133 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep134 ep143) rfl rfl

noncomputable abbrev qz827 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz291 := (@Inv.inv Real Real.instInv (Real.sqrt qz827))

noncomputable abbrev qz292 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep145 := @Enclosure.Complex.IsNear.of_eq qz817 (Complex.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz292)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz292)))) Bool.false 50954246679 274877906944 4924431643911 17772231073464320 Bool.false 45270535513 137438953472 2468673854303 8886115536732160 (BSN.cpow_neg_s_mk qz9 93095 1000 7 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz828 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz266)

noncomputable def ep146 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz827) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz827) (Real.sqrt qz828) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz828) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep147 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 129310 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz293 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep148 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz293 93095 1000 0 1 4381792198794487 2251799813685248 50000000012931 6465500000000000000 81584588949354553453 450359962737049600 930950000240762289 1293100000000000000000 qz271 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 50000000012931 6465500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz828) Bool.false 18378568546572512002048 9444732965739290427392 1000000000258620 129310000000000000000 4381792198794487 2251799813685248 50000000012931 6465500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep147 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep149 := nat_lit 91772156958293005885100586181640625

noncomputable def ep150 := BSN.sin_dyadic_bound_f 550399125 1073741824 2 1 524288 258873 ep149 ep100 ep149 ep149 ep101 ep149 257133 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 550399125) qz267 0 1 ep149 ep100 ep149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 550399125) qz268 0 1 ep149 ep101 ep149 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz829 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94976961) qz269)

noncomputable def ep151 := @Enclosure.Real.IsNear.cos_image qz292 qz829 Bool.false 94976961 524288 379 524288 Bool.false 257133 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz292 Bool.false 81584588949354553453 450359962737049600 930950000240762289 1293100000000000000000 94976961 524288 379 524288 (ep148 rfl) rfl) (Enclosure.sfrac_false_div 94976961 524288) (BSN.cos_reduce3 qz829 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38730895257636953915392) qz272) 226375608064910080 72057594037927936 Bool.false 257133 524288 28 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 94976961 524288 226375608064910080 72057594037927936 28 38730895257636953915392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 257133 524288 38730895257636953915392 75557863725914323419136 550399125 1073741824 258873 258620 (ep150 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep152 := BSN.cos_dyadic_bound_f 550399125 1073741824 2 1 524288 258873 ep149 ep90 ep149 ep149 ep91 ep149 456902 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 550399125) qz273 0 1 ep149 ep90 ep149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 550399125) qz274 0 1 ep149 ep91 ep149 rfl rfl rfl rfl) rfl rfl

noncomputable def ep153 := @Enclosure.Real.IsNear.sin_image qz292 qz829 Bool.false 94976961 524288 379 524288 Bool.true 456902 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz292 Bool.false 81584588949354553453 450359962737049600 930950000240762289 1293100000000000000000 94976961 524288 379 524288 (ep148 rfl) rfl) (Enclosure.sfrac_false_div 94976961 524288) (BSN.sin_reduce3 qz829 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38730895257636953915392) qz272) 226375608064910080 72057594037927936 Bool.false 456902 524288 28 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 94976961 524288 226375608064910080 72057594037927936 28 38730895257636953915392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 456902 524288 38730895257636953915392 75557863725914323419136 550399125 1073741824 258873 258620 (ep152 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz559 := (@Enclosure.Real.IsNear.recentre' qz291 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep146 rfl rfl) rfl)

noncomputable def ep154 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz292)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz292))) Bool.false 50954246679 274877906944 4924431643911 17772231073464320 Bool.false 45270535513 137438953472 2468673854303 8886115536732160 (@Enclosure.Real.IsNear.mulLit_ff qz291 (Real.cos qz292) 198163 524288 1 524288 257133 524288 24766389 33897840640 50954246679 274877906944 4924431643911 17772231073464320 qz559 (@Enclosure.Real.IsNear.recentre' (Real.cos qz292) Bool.false 257133 524288 49532778 67795681280 257133 524288 24766389 33897840640 (ep151 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz291 (@Neg.neg Real Real.instNeg (Real.sin qz292)) 198163 524288 1 524288 228451 262144 24766389 33897840640 45270535513 137438953472 2468673854303 8886115536732160 qz559 (@Enclosure.Real.IsNear.neg (Real.sin qz292) Bool.true 228451 262144 24766389 33897840640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz292) Bool.true 456902 524288 49532778 67795681280 228451 262144 24766389 33897840640 (ep153 rfl rfl) rfl)) rfl)

noncomputable def ep155 := @ep72 50954246679 274877906944 4924431643911 17772231073464320 Bool.false 45270535513 137438953472 2468673854303 8886115536732160 Bool.false 28488236929244777676800 12954950275 34359738368 19638548726911 8886115536732160 Bool.true 193692041783137009664 45097442759 137438953472 9841420026383 4443057768366080 (ep73 (BSN.head_sum_c_succ qz12 6 7 rfl rfl) (ep144 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep145 ep154) rfl rfl

noncomputable abbrev qz830 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz294 := (@Inv.inv Real Real.instInv (Real.sqrt qz830))

noncomputable abbrev qz295 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep156 := @Enclosure.Complex.IsNear.of_eq qz816 (Complex.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz295)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz295)))) Bool.false 35836043427 274877906944 4591311907671 17772231073464320 Bool.false 90334989783 274877906944 4610321253531 17772231073464320 (BSN.cpow_neg_s_mk qz9 93095 1000 8 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz831 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz266)

noncomputable def ep157 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz830) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz830) (Real.sqrt qz831) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz831) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep158 := BSN.log_dyadic_bound 0 16 1 0 1 262144 129310 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz296 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep159 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz296 93095 1000 0 1 9364972152248037 4503599627370496 100000000038793 12931000000000000000 174366416502706200903 900719925474099200 1861900000722286867 2586200000000000000000 qz271 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz831) Bool.false 19639770079031275290624 9444732965739290427392 1000000000387930 129310000000000000000 9364972152248037 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep158 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep160 := nat_lit 27040152445516738441749615725138176

noncomputable def ep161 := BSN.sin_dyadic_bound_f 405510668 1073741824 2 1 524288 258873 ep160 ep100 ep160 ep160 ep101 ep160 193329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 405510668) qz267 0 1 ep160 ep100 ep160 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 405510668) qz268 0 1 ep160 ep101 ep160 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz832 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz560 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25373653) qz832)

noncomputable abbrev qz561 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep162 := @Enclosure.Real.IsNear.cos_image qz295 qz560 Bool.false 25373653 131072 189 262144 Bool.false 193329 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz295 Bool.false 174366416502706200903 900719925474099200 1861900000722286867 2586200000000000000000 25373653 131072 189 262144 (ep159 rfl) rfl) (Enclosure.sfrac_false_div 25373653 131072) (BSN.cos_reduce3 qz560 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7133819131585611431936) qz561) 226375608064910080 72057594037927936 Bool.false 193329 524288 30 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 25373653 131072 226375608064910080 72057594037927936 30 7133819131585611431936 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 193329 524288 7133819131585611431936 18889465931478580854784 405510668 1073741824 258873 258620 (ep161 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep163 := BSN.cos_dyadic_bound_f 405510668 1073741824 2 1 524288 258873 ep160 ep90 ep160 ep160 ep91 ep160 487341 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 405510668) qz273 0 1 ep160 ep90 ep160 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 405510668) qz274 0 1 ep160 ep91 ep160 rfl rfl rfl rfl) rfl rfl

noncomputable def ep164 := @Enclosure.Real.IsNear.sin_image qz295 qz560 Bool.false 25373653 131072 189 262144 Bool.true 487341 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz295 Bool.false 174366416502706200903 900719925474099200 1861900000722286867 2586200000000000000000 25373653 131072 189 262144 (ep159 rfl) rfl) (Enclosure.sfrac_false_div 25373653 131072) (BSN.sin_reduce3 qz560 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7133819131585611431936) qz561) 226375608064910080 72057594037927936 Bool.false 487341 524288 30 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 25373653 131072 226375608064910080 72057594037927936 30 7133819131585611431936 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 487341 524288 7133819131585611431936 18889465931478580854784 405510668 1073741824 258873 258620 (ep163 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz562 := (@Enclosure.Real.IsNear.recentre' qz294 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep157 rfl rfl) rfl)

noncomputable def ep165 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz295)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz295))) Bool.false 35836043427 274877906944 4591311907671 17772231073464320 Bool.false 90334989783 274877906944 4610321253531 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ff qz294 (Real.cos qz295) 185363 524288 1 524288 193329 524288 12350867 16948920320 35836043427 274877906944 4591311907671 17772231073464320 qz562 (@Enclosure.Real.IsNear.recentre' (Real.cos qz295) Bool.false 193329 524288 24701734 33897840640 193329 524288 12350867 16948920320 (ep162 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz294 (@Neg.neg Real Real.instNeg (Real.sin qz295)) 185363 524288 1 524288 487341 524288 12350867 16948920320 90334989783 274877906944 4610321253531 17772231073464320 qz562 (@Enclosure.Real.IsNear.neg (Real.sin qz295) Bool.true 487341 524288 12350867 16948920320 (@Enclosure.Real.IsNear.recentre' (Real.sin qz295) Bool.true 487341 524288 24701734 33897840640 487341 524288 12350867 16948920320 (ep164 rfl rfl) rfl)) rfl)

noncomputable def ep166 := @ep70 35836043427 274877906944 4591311907671 17772231073464320 Bool.false 90334989783 274877906944 4610321253531 17772231073464320 Bool.false 4792346692451603316736 139475645627 274877906944 43868409361493 17772231073464320 Bool.false 19255783558563758080 140104265 274877906944 43976001359063 17772231073464320 (ep71 (BSN.head_sum_c_succ qz12 7 8 rfl rfl) (ep155 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep156 ep165) rfl rfl

theorem EMRow27.d7 : Enclosure.Complex.IsNear (BSN.headSumC qz12 9) Bool.false 139475645627 274877906944 43868409361493 17772231073464320 Bool.false 140104265 274877906944 43976001359063 17772231073464320 := ep69 (BSN.head_sum_c_succ qz12 8 9 rfl rfl) (ep166 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz833 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 16) qz15)

noncomputable def ep167 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 17) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 16) qz833) Bool.false 19698319881 17179869184 7382704196381 1777223107346432 Bool.true 68168483723 274877906944 14769480506903 3554446214692864

noncomputable def ep168 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 16) qz833 Bool.false 254983873115 274877906944 70551171537597 17772231073464320 Bool.true 17504612323 137438953472 35292432760511 8886115536732160 Bool.false

noncomputable abbrev qz834 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 15) qz15)

noncomputable def ep169 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 16) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 15) qz834) Bool.false 254983873115 274877906944 70551171537597 17772231073464320 Bool.true 17504612323 137438953472 35292432760511 8886115536732160

noncomputable def ep170 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 15) qz834 Bool.false 51109186957 68719476736 33587176971427 8886115536732160 Bool.false 14812312081 274877906944 67208394477079 17772231073464320 Bool.false

noncomputable abbrev qz835 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 14) qz15)

noncomputable def ep171 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 15) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 14) qz835) Bool.false 51109186957 68719476736 33587176971427 8886115536732160 Bool.false 14812312081 274877906944 67208394477079 17772231073464320

noncomputable def ep172 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 14) qz835 Bool.false 145445666707 274877906944 63685877751651 17772231073464320 Bool.false 29297610173 137438953472 15931733920239 4443057768366080 Bool.false

noncomputable abbrev qz836 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 13) qz15)

noncomputable def ep173 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 14) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 13) qz836) Bool.false 145445666707 274877906944 63685877751651 17772231073464320 Bool.false 29297610173 137438953472 15931733920239 4443057768366080

noncomputable def ep174 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 13) qz836 Bool.false 69227909413 274877906944 60060060030373 17772231073464320 Bool.false 60316159531 274877906944 60134241944623 17772231073464320 Bool.false

noncomputable abbrev qz837 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 12) qz15)

noncomputable def ep175 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 13) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 12) qz837) Bool.false 69227909413 274877906944 60060060030373 17772231073464320 Bool.false 60316159531 274877906944 60134241944623 17772231073464320

noncomputable def ep176 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 12) qz837 Bool.false 18246544125 137438953472 28148841509619 8886115536732160 Bool.true 2991841531 68719476736 14088742516187 4443057768366080 Bool.false

noncomputable abbrev qz838 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 11) qz15)

noncomputable def ep177 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 12) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 11) qz838) Bool.false 18246544125 137438953472 28148841509619 8886115536732160 Bool.true 2991841531 68719476736 14088742516187 4443057768366080

noncomputable def ep178 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 11) qz838 Bool.false 118051893273 274877906944 52349254339383 17772231073464320 Bool.true 13350322541 137438953472 26216936658159 8886115536732160 Bool.true

noncomputable abbrev qz839 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 10) qz15)

noncomputable def ep179 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 11) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 10) qz839) Bool.false 118051893273 274877906944 52349254339383 17772231073464320 Bool.true 13350322541 137438953472 26216936658159 8886115536732160

noncomputable def ep180 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 10) qz839 Bool.false 53312593263 274877906944 48228559294029 17772231073464320 Bool.false 31304891003 274877906944 48315804233789 17772231073464320 Bool.false

noncomputable abbrev qz840 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 9) qz15)

noncomputable def ep181 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 10) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 9) qz840) Bool.false 53312593263 274877906944 48228559294029 17772231073464320 Bool.false 31304891003 274877906944 48315804233789 17772231073464320

noncomputable def ep182 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 9) qz840 Bool.false 139475645627 274877906944 43868409361493 17772231073464320 Bool.false 140104265 274877906944 43976001359063 17772231073464320 Bool.true

noncomputable abbrev qz841 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz297 := (@Inv.inv Real Real.instInv (Real.sqrt qz841))

noncomputable abbrev qz298 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep183 := @Enclosure.Complex.IsNear.of_eq qz840 (Complex.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz298)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz298)))) Bool.true 21540763091 68719476736 545018741567 2221528884183040 Bool.false 15582393369 137438953472 2169901437363 8886115536732160 (BSN.cpow_neg_s_mk qz9 93095 1000 9 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz842 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz266)

noncomputable def ep184 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz841) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz841) (Real.sqrt qz842) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz842) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep185 := BSN.log_dyadic_bound 1 17 2 1 867 262144 129310 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz299 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep186 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz299 93095 1000 0 1 9895417793173221 4503599627370496 100000000038793 12931000000000000000 184242783891092201799 900719925474099200 1861900000722286867 2586200000000000000000 qz271 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz842) Bool.false 20752195215788806766592 9444732965739290427392 1000000000387930 129310000000000000000 9895417793173221 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep185 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep187 := nat_lit 19284156487380682673965685519077041

noncomputable def ep188 := BSN.cos_dyadic_bound_f 372649173 1073741824 2 1 524288 258873 ep187 ep90 ep187 ep187 ep91 ep187 493028 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 372649173) qz273 0 1 ep187 ep90 ep187 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 372649173) qz274 0 1 ep187 ep91 ep187 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz843 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53621707) qz278)

noncomputable def ep189 := @Enclosure.Real.IsNear.cos_image qz298 qz843 Bool.false 53621707 262144 379 524288 Bool.true 493028 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz298 Bool.false 184242783891092201799 900719925474099200 1861900000722286867 2586200000000000000000 53621707 262144 379 524288 (ep186 rfl) rfl) (Enclosure.sfrac_false_div 53621707 262144) (BSN.cos_reduce2 qz843 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13111427179624901115904) qz280) 226375608064910080 72057594037927936 Bool.false 493028 524288 32 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 53621707 262144 226375608064910080 72057594037927936 32 13111427179624901115904 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 493028 524288 13111427179624901115904 37778931862957161709568 372649173 1073741824 258873 258620 (ep188 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep190 := BSN.sin_dyadic_bound_f 372649173 1073741824 2 1 524288 258873 ep187 ep100 ep187 ep187 ep101 ep187 178326 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 372649173) qz267 0 1 ep187 ep100 ep187 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 372649173) qz268 0 1 ep187 ep101 ep187 rfl rfl rfl rfl) rfl rfl

noncomputable def ep191 := @Enclosure.Real.IsNear.sin_image qz298 qz843 Bool.false 53621707 262144 379 524288 Bool.true 178326 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz298 Bool.false 184242783891092201799 900719925474099200 1861900000722286867 2586200000000000000000 53621707 262144 379 524288 (ep186 rfl) rfl) (Enclosure.sfrac_false_div 53621707 262144) (BSN.sin_reduce2 qz843 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13111427179624901115904) qz280) 226375608064910080 72057594037927936 Bool.false 178326 524288 32 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 53621707 262144 226375608064910080 72057594037927936 32 13111427179624901115904 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 178326 524288 13111427179624901115904 37778931862957161709568 372649173 1073741824 258873 258620 (ep190 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz563 := (@Enclosure.Real.IsNear.recentre' qz297 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep184 rfl rfl) rfl)

noncomputable def ep192 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz298)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz298))) Bool.true 21540763091 68719476736 545018741567 2221528884183040 Bool.false 15582393369 137438953472 2169901437363 8886115536732160 (@Enclosure.Real.IsNear.mulLit_ft qz297 (Real.cos qz298) 174763 524288 1 524288 123257 131072 24766389 33897840640 21540763091 68719476736 545018741567 2221528884183040 qz563 (@Enclosure.Real.IsNear.recentre' (Real.cos qz298) Bool.true 493028 524288 49532778 67795681280 123257 131072 24766389 33897840640 (ep189 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz297 (@Neg.neg Real Real.instNeg (Real.sin qz298)) 174763 524288 1 524288 89163 262144 24766389 33897840640 15582393369 137438953472 2169901437363 8886115536732160 qz563 (@Enclosure.Real.IsNear.neg (Real.sin qz298) Bool.true 89163 262144 24766389 33897840640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz298) Bool.true 178326 524288 49532778 67795681280 89163 262144 24766389 33897840640 (ep191 rfl rfl) rfl)) rfl)

noncomputable def ep193 := @ep182 21540763091 68719476736 545018741567 2221528884183040 Bool.false 15582393369 137438953472 2169901437363 8886115536732160 Bool.false 3663613512472558829568 53312593263 274877906944 48228559294029 17772231073464320 Bool.false 4302511458007348412416 31304891003 274877906944 48315804233789 17772231073464320 EMRow27.d7 (ep183 ep192) rfl rfl

noncomputable abbrev qz844 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz300 := (@Inv.inv Real Real.instInv (Real.sqrt qz844))

noncomputable abbrev qz301 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep194 := @Enclosure.Complex.IsNear.of_eq qz839 (Complex.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz301)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz301)))) Bool.false 32369650005 137438953472 2060347522677 8886115536732160 Bool.true 58005536085 274877906944 4118069082529 17772231073464320 (BSN.cpow_neg_s_mk qz9 93095 1000 10 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz845 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz266)

noncomputable def ep195 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz844) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz844) (Real.sqrt qz845) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz845) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep196 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 129310 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz302 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep197 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz302 93095 1000 0 1 10369908600166117 4503599627370496 100000000038793 12931000000000000000 193077328226492932423 900719925474099200 1861900000722286867 2586200000000000000000 qz271 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz845) Bool.false 21747274560655572598784 9444732965739290427392 1000000000387930 129310000000000000000 10369908600166117 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep196 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep198 := nat_lit 845835799537117818095659126551182259090588308171548620141373911754392712321

noncomputable def ep199 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep200 := nat_lit 143419205544629949812863948126473578273274837621029184497556595165607041

noncomputable def ep201 := nat_lit 2537220560200264194387351651757293830115218374839403802055126622072846922881

noncomputable def ep202 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable def ep203 := BSN.cos_dyadic_bound_f 784469231 1073741824 3 2 524288 258873 ep198 ep199 ep200 ep201 ep202 ep200 390478 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 784469231) qz273 0 2 ep198 ep199 ep200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 784469231) qz274 0 2 ep201 ep202 ep200 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz564 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28096449) qz832)

noncomputable def ep204 := @Enclosure.Real.IsNear.cos_image qz301 qz564 Bool.false 28096449 131072 189 262144 Bool.false 390478 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz301 Bool.false 193077328226492932423 900719925474099200 1861900000722286867 2586200000000000000000 28096449 131072 189 262144 (ep197 rfl) rfl) (Enclosure.sfrac_false_div 28096449 131072) (BSN.cos_reduce0 qz564 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13800528660083054215168) qz561) 226375608064910080 72057594037927936 Bool.false 390478 524288 34 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 28096449 131072 226375608064910080 72057594037927936 34 13800528660083054215168 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 390478 524288 13800528660083054215168 18889465931478580854784 784469231 1073741824 258873 258620 (ep203 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep205 := nat_lit 378707282138368643507781910858912321

noncomputable def ep206 := BSN.sin_dyadic_bound_f 784469231 1073741824 2 1 524288 258873 ep205 ep100 ep205 ep205 ep101 ep205 349863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 784469231) qz267 0 1 ep205 ep100 ep205 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 784469231) qz268 0 1 ep205 ep101 ep205 rfl rfl rfl rfl) rfl rfl

noncomputable def ep207 := @Enclosure.Real.IsNear.sin_image qz301 qz564 Bool.false 28096449 131072 189 262144 Bool.false 349863 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz301 Bool.false 193077328226492932423 900719925474099200 1861900000722286867 2586200000000000000000 28096449 131072 189 262144 (ep197 rfl) rfl) (Enclosure.sfrac_false_div 28096449 131072) (BSN.sin_reduce0 qz564 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13800528660083054215168) qz561) 226375608064910080 72057594037927936 Bool.false 349863 524288 34 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 28096449 131072 226375608064910080 72057594037927936 34 13800528660083054215168 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 349863 524288 13800528660083054215168 18889465931478580854784 784469231 1073741824 258873 258620 (ep206 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz565 := (@Enclosure.Real.IsNear.recentre' qz300 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep195 rfl rfl) rfl)

noncomputable def ep208 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz301)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz301))) Bool.false 32369650005 137438953472 2060347522677 8886115536732160 Bool.true 58005536085 274877906944 4118069082529 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ff qz300 (Real.cos qz301) 165795 524288 1 524288 195239 262144 12350867 16948920320 32369650005 137438953472 2060347522677 8886115536732160 qz565 (@Enclosure.Real.IsNear.recentre' (Real.cos qz301) Bool.false 390478 524288 24701734 33897840640 195239 262144 12350867 16948920320 (ep204 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz300 (@Neg.neg Real Real.instNeg (Real.sin qz301)) 165795 524288 1 524288 349863 524288 12350867 16948920320 58005536085 274877906944 4118069082529 17772231073464320 qz565 (@Enclosure.Real.IsNear.neg (Real.sin qz301) Bool.false 349863 524288 12350867 16948920320 (@Enclosure.Real.IsNear.recentre' (Real.sin qz301) Bool.false 349863 524288 24701734 33897840640 349863 524288 12350867 16948920320 (ep207 rfl rfl) rfl)) rfl)

noncomputable def ep209 := @ep180 32369650005 137438953472 2060347522677 8886115536732160 Bool.true 58005536085 274877906944 4118069082529 17772231073464320 Bool.false 16224928666829356793856 118051893273 274877906944 52349254339383 17772231073464320 Bool.true 7339417434194767249408 13350322541 137438953472 26216936658159 8886115536732160 (ep181 (BSN.head_sum_c_succ qz12 9 10 rfl rfl) (ep193 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep194 ep208) rfl rfl

noncomputable abbrev qz846 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz303 := (@Inv.inv Real Real.instInv (Real.sqrt qz846))

noncomputable abbrev qz304 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep210 := @Enclosure.Complex.IsNear.of_eq qz838 (Complex.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz304)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz304)))) Bool.true 81558805023 274877906944 789685735971 3554446214692864 Bool.false 7366639479 137438953472 392109674843 1777223107346432 (BSN.cpow_neg_s_mk qz9 93095 1000 11 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz847 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz266)

noncomputable def ep211 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz846) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz846) (Real.sqrt qz847) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz847) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep212 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 129310 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz305 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep213 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz305 93095 1000 0 1 10799147631728357 4503599627370496 100000000038793 12931000000000000000 201069329755150278983 900719925474099200 1861900000722286867 2586200000000000000000 qz271 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz847) Bool.false 22647454054174387339264 9444732965739290427392 1000000000387930 129310000000000000000 10799147631728357 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep212 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep214 := nat_lit 1356094118865199435074223108263936

noncomputable def ep215 := BSN.cos_dyadic_bound_f 191898888 1073741824 2 1 524288 258873 ep214 ep90 ep214 ep214 ep91 ep214 515937 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 191898888) qz273 0 1 ep214 ep90 ep214 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 191898888) qz274 0 1 ep214 ep91 ep214 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz848 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117037753) qz269)

noncomputable def ep216 := @Enclosure.Real.IsNear.cos_image qz304 qz848 Bool.false 117037753 524288 379 524288 Bool.true 515937 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz304 Bool.false 201069329755150278983 900719925474099200 1861900000722286867 2586200000000000000000 117037753 524288 379 524288 (ep213 rfl) rfl) (Enclosure.sfrac_false_div 117037753 524288) (BSN.cos_reduce2 qz848 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13503683809313015463936) qz272) 226375608064910080 72057594037927936 Bool.false 515937 524288 35 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 117037753 524288 226375608064910080 72057594037927936 35 13503683809313015463936 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 515937 524288 13503683809313015463936 75557863725914323419136 191898888 1073741824 258873 258620 (ep215 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep217 := BSN.sin_dyadic_bound_f 191898888 1073741824 2 1 524288 258873 ep214 ep100 ep214 ep214 ep101 ep214 93202 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 191898888) qz267 0 1 ep214 ep100 ep214 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 191898888) qz268 0 1 ep214 ep101 ep214 rfl rfl rfl rfl) rfl rfl

noncomputable def ep218 := @Enclosure.Real.IsNear.sin_image qz304 qz848 Bool.false 117037753 524288 379 524288 Bool.true 93202 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz304 Bool.false 201069329755150278983 900719925474099200 1861900000722286867 2586200000000000000000 117037753 524288 379 524288 (ep213 rfl) rfl) (Enclosure.sfrac_false_div 117037753 524288) (BSN.sin_reduce2 qz848 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13503683809313015463936) qz272) 226375608064910080 72057594037927936 Bool.false 93202 524288 35 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 117037753 524288 226375608064910080 72057594037927936 35 13503683809313015463936 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 93202 524288 13503683809313015463936 75557863725914323419136 191898888 1073741824 258873 258620 (ep217 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz566 := (@Enclosure.Real.IsNear.recentre' qz303 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep211 rfl rfl) rfl)

noncomputable def ep219 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz304)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz304))) Bool.true 81558805023 274877906944 789685735971 3554446214692864 Bool.false 7366639479 137438953472 392109674843 1777223107346432 (@Enclosure.Real.IsNear.mulLit_ft qz303 (Real.cos qz304) 158079 524288 1 524288 515937 524288 24766389 33897840640 81558805023 274877906944 789685735971 3554446214692864 qz566 (@Enclosure.Real.IsNear.recentre' (Real.cos qz304) Bool.true 515937 524288 49532778 67795681280 515937 524288 24766389 33897840640 (ep216 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz303 (@Neg.neg Real Real.instNeg (Real.sin qz304)) 158079 524288 1 524288 46601 262144 24766389 33897840640 7366639479 137438953472 392109674843 1777223107346432 qz566 (@Enclosure.Real.IsNear.neg (Real.sin qz304) Bool.true 46601 262144 24766389 33897840640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz304) Bool.true 93202 524288 49532778 67795681280 46601 262144 24766389 33897840640 (ep218 rfl rfl) rfl)) rfl)

noncomputable def ep220 := @ep178 81558805023 274877906944 789685735971 3554446214692864 Bool.false 7366639479 137438953472 392109674843 1777223107346432 Bool.false 10031143716082679808000 18246544125 137438953472 28148841509619 8886115536732160 Bool.true 822391137949412491264 2991841531 68719476736 14088742516187 4443057768366080 (ep179 (BSN.head_sum_c_succ qz12 10 11 rfl rfl) (ep209 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep210 ep219) rfl rfl

noncomputable abbrev qz849 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz306 := (@Inv.inv Real Real.instInv (Real.sqrt qz849))

noncomputable abbrev qz307 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep221 := @Enclosure.Complex.IsNear.of_eq qz837 (Complex.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz307)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz307)))) Bool.false 32734821163 274877906944 752475402227 3554446214692864 Bool.false 72283525655 274877906944 755854375975 3554446214692864 (BSN.cpow_neg_s_mk qz9 93095 1000 12 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz850 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz266)

noncomputable def ep222 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz849) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz849) (Real.sqrt qz850) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz850) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep223 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 129310 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz308 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep224 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz308 93095 1000 0 1 11191020447815397 4503599627370496 100000000038793 12931000000000000000 208365609717874876743 900719925474099200 1861900000722286867 2586200000000000000000 qz271 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz850) Bool.false 23469270914176955449344 9444732965739290427392 1000000000387930 129310000000000000000 11191020447815397 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep223 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep225 := nat_lit 43463123515641000545430210472500625

noncomputable def ep226 := BSN.sin_dyadic_bound_f 456594035 1073741824 2 1 524288 258873 ep225 ep100 ep225 ep225 ep101 ep225 216287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 456594035) qz267 0 1 ep225 ep100 ep225 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 456594035) qz268 0 1 ep225 ep101 ep225 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz851 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 121284747) qz269)

noncomputable def ep227 := @Enclosure.Real.IsNear.cos_image qz307 qz851 Bool.false 121284747 524288 379 524288 Bool.false 216287 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz307 Bool.false 208365609717874876743 900719925474099200 1861900000722286867 2586200000000000000000 121284747 524288 379 524288 (ep224 rfl) rfl) (Enclosure.sfrac_false_div 121284747 524288) (BSN.cos_reduce3 qz851 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32129948870666568597504) qz272) 226375608064910080 72057594037927936 Bool.false 216287 524288 36 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 121284747 524288 226375608064910080 72057594037927936 36 32129948870666568597504 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 216287 524288 32129948870666568597504 75557863725914323419136 456594035 1073741824 258873 258620 (ep226 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep228 := BSN.cos_dyadic_bound_f 456594035 1073741824 2 1 524288 258873 ep225 ep90 ep225 ep225 ep91 ep225 477595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 456594035) qz273 0 1 ep225 ep90 ep225 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 456594035) qz274 0 1 ep225 ep91 ep225 rfl rfl rfl rfl) rfl rfl

noncomputable def ep229 := @Enclosure.Real.IsNear.sin_image qz307 qz851 Bool.false 121284747 524288 379 524288 Bool.true 477595 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz307 Bool.false 208365609717874876743 900719925474099200 1861900000722286867 2586200000000000000000 121284747 524288 379 524288 (ep224 rfl) rfl) (Enclosure.sfrac_false_div 121284747 524288) (BSN.sin_reduce3 qz851 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32129948870666568597504) qz272) 226375608064910080 72057594037927936 Bool.false 477595 524288 36 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 121284747 524288 226375608064910080 72057594037927936 36 32129948870666568597504 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 477595 524288 32129948870666568597504 75557863725914323419136 456594035 1073741824 258873 258620 (ep228 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz567 := (@Enclosure.Real.IsNear.recentre' qz306 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep222 rfl rfl) rfl)

noncomputable def ep230 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz307)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz307))) Bool.false 32734821163 274877906944 752475402227 3554446214692864 Bool.false 72283525655 274877906944 755854375975 3554446214692864 (@Enclosure.Real.IsNear.mulLit_ff qz306 (Real.cos qz307) 151349 524288 1 524288 216287 524288 24766389 33897840640 32734821163 274877906944 752475402227 3554446214692864 qz567 (@Enclosure.Real.IsNear.recentre' (Real.cos qz307) Bool.false 216287 524288 49532778 67795681280 216287 524288 24766389 33897840640 (ep227 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz306 (@Neg.neg Real Real.instNeg (Real.sin qz307)) 151349 524288 1 524288 477595 524288 24766389 33897840640 72283525655 274877906944 755854375975 3554446214692864 qz567 (@Enclosure.Real.IsNear.neg (Real.sin qz307) Bool.true 477595 524288 24766389 33897840640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz307) Bool.true 477595 524288 49532778 67795681280 477595 524288 24766389 33897840640 (ep229 rfl rfl) rfl)) rfl)

noncomputable def ep231 := @ep176 32734821163 274877906944 752475402227 3554446214692864 Bool.false 72283525655 274877906944 755854375975 3554446214692864 Bool.false 9514611420777137831936 69227909413 274877906944 60060060030373 17772231073464320 Bool.false 4144894921695419170816 60316159531 274877906944 60134241944623 17772231073464320 (ep177 (BSN.head_sum_c_succ qz12 11 12 rfl rfl) (ep220 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep221 ep230) rfl rfl

noncomputable abbrev qz852 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz309 := (@Inv.inv Real Real.instInv (Real.sqrt qz852))

noncomputable abbrev qz310 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep232 := @Enclosure.Complex.IsNear.of_eq qz836 (Complex.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz310)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz310)))) Bool.false 38108878647 137438953472 1812908860639 8886115536732160 Bool.true 1720939185 274877906944 3592693736333 17772231073464320 (BSN.cpow_neg_s_mk qz9 93095 1000 13 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz853 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz266)

noncomputable def ep233 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz852) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz852) (Real.sqrt qz853) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz853) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep234 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 129310 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz311 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep235 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz311 93095 1000 0 1 11551488463034085 4503599627370496 100000000038793 12931000000000000000 43015432738646325723 180143985094819840 1861900000722286867 2586200000000000000000 qz271 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz853) Bool.false 24225227133228857425920 9444732965739290427392 1000000000387930 129310000000000000000 11551488463034085 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep234 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep236 := BSN.cos_dyadic_bound_f 24242142 1073741824 1 0 524288 258873 0 1 1 0 1 1 524154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 24242142) qz273 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 24242142) qz274 0 0 rfl) rfl rfl

noncomputable abbrev qz854 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62595693) qz278)

noncomputable def ep237 := @Enclosure.Real.IsNear.cos_image qz310 qz854 Bool.false 62595693 262144 189 262144 Bool.false 524154 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz310 Bool.false 43015432738646325723 180143985094819840 1861900000722286867 2586200000000000000000 62595693 262144 189 262144 (ep235 rfl) rfl) (Enclosure.sfrac_false_div 62595693 262144) (BSN.cos_reduce0 qz854 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 852944547231098208256) qz280) 226375608064910080 72057594037927936 Bool.false 524154 524288 38 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 62595693 262144 226375608064910080 72057594037927936 38 852944547231098208256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524154 524288 852944547231098208256 37778931862957161709568 24242142 1073741824 258873 258620 (ep236 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep238 := BSN.sin_dyadic_bound_f 24242142 1073741824 1 0 524288 258873 0 1 1 0 1 1 11835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 24242142) qz267 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 24242142) qz268 0 0 rfl) rfl rfl

noncomputable def ep239 := @Enclosure.Real.IsNear.sin_image qz310 qz854 Bool.false 62595693 262144 189 262144 Bool.false 11835 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz310 Bool.false 43015432738646325723 180143985094819840 1861900000722286867 2586200000000000000000 62595693 262144 189 262144 (ep235 rfl) rfl) (Enclosure.sfrac_false_div 62595693 262144) (BSN.sin_reduce0 qz854 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 852944547231098208256) qz280) 226375608064910080 72057594037927936 Bool.false 11835 524288 38 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 62595693 262144 226375608064910080 72057594037927936 38 852944547231098208256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 11835 524288 852944547231098208256 37778931862957161709568 24242142 1073741824 258873 258620 (ep238 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz568 := (@Enclosure.Real.IsNear.recentre' qz309 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep233 rfl rfl) rfl)

noncomputable def ep240 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz310)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz310))) Bool.false 38108878647 137438953472 1812908860639 8886115536732160 Bool.true 1720939185 274877906944 3592693736333 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ff qz309 (Real.cos qz310) 145411 524288 1 524288 262077 262144 12350867 16948920320 38108878647 137438953472 1812908860639 8886115536732160 qz568 (@Enclosure.Real.IsNear.recentre' (Real.cos qz310) Bool.false 524154 524288 24701734 33897840640 262077 262144 12350867 16948920320 (ep237 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz309 (@Neg.neg Real Real.instNeg (Real.sin qz310)) 145411 524288 1 524288 11835 524288 12350867 16948920320 1720939185 274877906944 3592693736333 17772231073464320 qz568 (@Enclosure.Real.IsNear.neg (Real.sin qz310) Bool.false 11835 524288 12350867 16948920320 (@Enclosure.Real.IsNear.recentre' (Real.sin qz310) Bool.false 11835 524288 24701734 33897840640 11835 524288 12350867 16948920320 (ep239 rfl rfl) rfl)) rfl)

noncomputable def ep241 := @ep174 38108878647 137438953472 1812908860639 8886115536732160 Bool.true 1720939185 274877906944 3592693736333 17772231073464320 Bool.false 19989900219247392456704 145445666707 274877906944 63685877751651 17772231073464320 Bool.false 16106531525630963482624 29297610173 137438953472 15931733920239 4443057768366080 (ep175 (BSN.head_sum_c_succ qz12 12 13 rfl rfl) (ep231 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep232 ep240) rfl rfl

noncomputable abbrev qz855 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz312 := (@Inv.inv Real Real.instInv (Real.sqrt qz855))

noncomputable abbrev qz313 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep242 := @Enclosure.Complex.IsNear.of_eq qz835 (Complex.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz313)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz313)))) Bool.false 58991081121 274877906944 3488476191203 17772231073464320 Bool.true 43782908265 274877906944 3481458796123 17772231073464320 (BSN.cpow_neg_s_mk qz9 93095 1000 14 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz856 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz266)

noncomputable def ep243 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz855) 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz855) (Real.sqrt qz856) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz856) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep244 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 129310 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz314 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable def ep245 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz314 93095 1000 0 1 11885241781671653 4503599627370496 100000000038793 12931000000000000000 221291316732944507207 900719925474099200 1861900000722286867 2586200000000000000000 qz271 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz856) Bool.false 24925158572916270432256 9444732965739290427392 1000000000387930 129310000000000000000 11885241781671653 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep244 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep246 := nat_lit 220906770423805009155699657800200161

noncomputable def ep247 := BSN.cos_dyadic_bound_f 685570713 1073741824 2 1 524288 258873 ep246 ep90 ep246 ep246 ep91 ep246 421001 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 685570713) qz273 0 1 ep246 ep90 ep246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 685570713) qz274 0 1 ep246 ep91 ep246 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz857 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128808499) qz269)

noncomputable def ep248 := @Enclosure.Real.IsNear.cos_image qz313 qz857 Bool.false 128808499 524288 189 262144 Bool.false 421001 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz313 Bool.false 221291316732944507207 900719925474099200 1861900000722286867 2586200000000000000000 128808499 524288 189 262144 (ep245 rfl) rfl) (Enclosure.sfrac_false_div 128808499 524288) (BSN.cos_reduce0 qz857 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48242750176543153061888) qz272) 226375608064910080 72057594037927936 Bool.false 421001 524288 39 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 128808499 524288 226375608064910080 72057594037927936 39 48242750176543153061888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 421001 524288 48242750176543153061888 75557863725914323419136 685570713 1073741824 258873 258620 (ep247 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep249 := BSN.sin_dyadic_bound_f 685570713 1073741824 2 1 524288 258873 ep246 ep100 ep246 ep246 ep101 ep246 312465 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 685570713) qz267 0 1 ep246 ep100 ep246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 685570713) qz268 0 1 ep246 ep101 ep246 rfl rfl rfl rfl) rfl rfl

noncomputable def ep250 := @Enclosure.Real.IsNear.sin_image qz313 qz857 Bool.false 128808499 524288 189 262144 Bool.false 312465 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz313 Bool.false 221291316732944507207 900719925474099200 1861900000722286867 2586200000000000000000 128808499 524288 189 262144 (ep245 rfl) rfl) (Enclosure.sfrac_false_div 128808499 524288) (BSN.sin_reduce0 qz857 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48242750176543153061888) qz272) 226375608064910080 72057594037927936 Bool.false 312465 524288 39 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 128808499 524288 226375608064910080 72057594037927936 39 48242750176543153061888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 312465 524288 48242750176543153061888 75557863725914323419136 685570713 1073741824 258873 258620 (ep249 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz569 := (@Enclosure.Real.IsNear.recentre' qz312 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep243 rfl rfl) rfl)

noncomputable def ep251 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz313)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz313))) Bool.false 58991081121 274877906944 3488476191203 17772231073464320 Bool.true 43782908265 274877906944 3481458796123 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ff qz312 (Real.cos qz313) 140121 524288 1 524288 421001 524288 12350867 16948920320 58991081121 274877906944 3488476191203 17772231073464320 qz569 (@Enclosure.Real.IsNear.recentre' (Real.cos qz313) Bool.false 421001 524288 24701734 33897840640 421001 524288 12350867 16948920320 (ep248 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz312 (@Neg.neg Real Real.instNeg (Real.sin qz313)) 140121 524288 1 524288 312465 524288 12350867 16948920320 43782908265 274877906944 3481458796123 17772231073464320 qz569 (@Enclosure.Real.IsNear.neg (Real.sin qz313) Bool.false 312465 524288 12350867 16948920320 (@Enclosure.Real.IsNear.recentre' (Real.sin qz313) Bool.false 312465 524288 24701734 33897840640 312465 524288 12350867 16948920320 (ep250 rfl rfl) rfl)) rfl)

noncomputable def ep252 := @ep172 58991081121 274877906944 3488476191203 17772231073464320 Bool.true 43782908265 274877906944 3481458796123 17772231073464320 Bool.false 56195145345398978117632 51109186957 68719476736 33587176971427 8886115536732160 Bool.false 2035788670913302495232 14812312081 274877906944 67208394477079 17772231073464320 (ep173 (BSN.head_sum_c_succ qz12 13 14 rfl rfl) (ep241 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep242 ep251) rfl rfl

noncomputable abbrev qz858 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz315 := (@Inv.inv Real Real.instInv (Real.sqrt qz858))

noncomputable abbrev qz316 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep253 := @Enclosure.Complex.IsNear.of_eq qz834 (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz316)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz316)))) Bool.false 50547125287 274877906944 3376817594743 17772231073464320 Bool.true 49821536727 274877906944 3376471043943 17772231073464320 (BSN.cpow_neg_s_mk qz9 93095 1000 15 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz859 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz266)

noncomputable def ep254 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz858) 2030559 524288 1 524288 67685 67686 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz858) (Real.sqrt qz859) Bool.false 2030559 524288 1 524288 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz859) Bool.false 2030559 524288 1 524288 2030559 524288 1 524288 (BSN.sqrt_enclosure 15 1 1015279 1015280 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep255 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 262144 129310 14087658153505881 266939110305 164785 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz317 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable def ep256 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz317 93095 1000 0 1 12195956895733477 4503599627370496 100000000038793 12931000000000000000 227076521441661608263 900719925474099200 1861900000722286867 2586200000000000000000 qz271 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz859) Bool.false 25576775395801252757504 9444732965739290427392 1000000000387930 129310000000000000000 12195956895733477 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep255 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep257 := nat_lit 1088676169099775440604467597587400753814154033287577395887075567726053395041

noncomputable def ep258 := nat_lit 237569315906301961849773900934352483256713894657389547514196497268836961

noncomputable def ep259 := nat_lit 3265553368667513717889703244960333556475948672073417408566198310183622511201

noncomputable def ep260 := BSN.cos_dyadic_bound_f 835552597 1073741824 3 2 524288 258873 ep257 ep199 ep258 ep259 ep202 ep258 373397 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 835552597) qz273 0 2 ep257 ep199 ep258 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 835552597) qz274 0 2 ep259 ep202 ep258 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz860 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132175931) qz269)

noncomputable def ep261 := @Enclosure.Real.IsNear.cos_image qz316 qz860 Bool.false 132175931 524288 379 524288 Bool.false 373397 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz316 Bool.false 227076521441661608263 900719925474099200 1861900000722286867 2586200000000000000000 132175931 524288 379 524288 (ep256 rfl) rfl) (Enclosure.sfrac_false_div 132175931 524288) (BSN.cos_reduce0 qz860 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58796786984656339730432) qz272) 226375608064910080 72057594037927936 Bool.false 373397 524288 40 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 132175931 524288 226375608064910080 72057594037927936 40 58796786984656339730432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 373397 524288 58796786984656339730432 75557863725914323419136 835552597 1073741824 258873 258620 (ep260 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep262 := nat_lit 487410828671565279012199106253359281

noncomputable def ep263 := BSN.sin_dyadic_bound_f 835552597 1073741824 2 1 524288 258873 ep262 ep100 ep262 ep262 ep101 ep262 368037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 835552597) qz267 0 1 ep262 ep100 ep262 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 835552597) qz268 0 1 ep262 ep101 ep262 rfl rfl rfl rfl) rfl rfl

noncomputable def ep264 := @Enclosure.Real.IsNear.sin_image qz316 qz860 Bool.false 132175931 524288 379 524288 Bool.false 368037 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz316 Bool.false 227076521441661608263 900719925474099200 1861900000722286867 2586200000000000000000 132175931 524288 379 524288 (ep256 rfl) rfl) (Enclosure.sfrac_false_div 132175931 524288) (BSN.sin_reduce0 qz860 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58796786984656339730432) qz272) 226375608064910080 72057594037927936 Bool.false 368037 524288 40 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 132175931 524288 226375608064910080 72057594037927936 40 58796786984656339730432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 368037 524288 58796786984656339730432 75557863725914323419136 835552597 1073741824 258873 258620 (ep263 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz570 := (@Enclosure.Real.IsNear.recentre' qz315 Bool.false 135371 524288 1 524288 135371 524288 1 524288 (ep254 rfl rfl) rfl)

noncomputable def ep265 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz316)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz316))) Bool.false 50547125287 274877906944 3376817594743 17772231073464320 Bool.true 49821536727 274877906944 3376471043943 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ff qz315 (Real.cos qz316) 135371 524288 1 524288 373397 524288 24766389 33897840640 50547125287 274877906944 3376817594743 17772231073464320 qz570 (@Enclosure.Real.IsNear.recentre' (Real.cos qz316) Bool.false 373397 524288 49532778 67795681280 373397 524288 24766389 33897840640 (ep261 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz315 (@Neg.neg Real Real.instNeg (Real.sin qz316)) 135371 524288 1 524288 368037 524288 24766389 33897840640 49821536727 274877906944 3376471043943 17772231073464320 qz570 (@Enclosure.Real.IsNear.neg (Real.sin qz316) Bool.false 368037 524288 24766389 33897840640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz316) Bool.false 368037 524288 49532778 67795681280 368037 524288 24766389 33897840640 (ep264 rfl rfl) rfl)) rfl)

noncomputable def ep266 := @ep170 50547125287 274877906944 3376817594743 17772231073464320 Bool.true 49821536727 274877906944 3376471043943 17772231073464320 Bool.false 17522358336581418352640 254983873115 274877906944 70551171537597 17772231073464320 Bool.true 9623262394424779341824 17504612323 137438953472 35292432760511 8886115536732160 (ep171 (BSN.head_sum_c_succ qz12 14 15 rfl rfl) (ep252 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep253 ep265) rfl rfl

noncomputable abbrev qz861 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz318 := (@Inv.inv Real Real.instInv (Real.sqrt qz861))

noncomputable abbrev qz319 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep267 := @Enclosure.Complex.IsNear.of_eq qz833 (Complex.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz319)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz319)))) Bool.false 60189244981 274877906944 3275870426213 17772231073464320 Bool.true 33159259077 274877906944 3262537013493 17772231073464320 (BSN.cpow_neg_s_mk qz9 93095 1000 16 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz862 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz266)

noncomputable def ep268 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz861) 2097153 524288 1 524288 65535 65536 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz861) (Real.sqrt qz862) Bool.false 2097153 524288 1 524288 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz862) Bool.false 2097153 524288 1 524288 2097153 524288 1 524288 (BSN.sqrt_enclosure 16 1 1048576 1048577 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep269 := BSN.log_dyadic_bound 0 32 1 0 1 262144 129310 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz320 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable def ep270 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz320 93095 1000 0 1 3121657384082679 1125899906842624 25000000012931 3232750000000000000 58122138834235400301 225179981368524800 465475000240762289 646550000000000000000 qz271 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz862) Bool.false 26186360105375033720832 9444732965739290427392 1000000000517240 129310000000000000000 3121657384082679 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep269 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep271 := nat_lit 85459803912340355087643150722909761

noncomputable def ep272 := BSN.cos_dyadic_bound_f 540680209 1073741824 2 1 524288 258873 ep271 ep90 ep271 ep271 ep91 ep271 459211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 540680209) qz273 0 1 ep271 ep90 ep271 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 540680209) qz274 0 1 ep271 ep91 ep271 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz863 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 135326149) qz269)

noncomputable def ep273 := @Enclosure.Real.IsNear.cos_image qz319 qz863 Bool.false 135326149 524288 379 524288 Bool.false 459211 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz319 Bool.false 58122138834235400301 225179981368524800 465475000240762289 646550000000000000000 135326149 524288 379 524288 (ep270 rfl) rfl) (Enclosure.sfrac_false_div 135326149 524288) (BSN.cos_reduce0 qz863 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38046987330060569018368) qz272) 226375608064910080 72057594037927936 Bool.false 459211 524288 41 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 135326149 524288 226375608064910080 72057594037927936 41 38046987330060569018368 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 459211 524288 38046987330060569018368 75557863725914323419136 540680209 1073741824 258873 258620 (ep272 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep274 := BSN.sin_dyadic_bound_f 540680209 1073741824 2 1 524288 258873 ep271 ep100 ep271 ep271 ep101 ep271 252987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 540680209) qz267 0 1 ep271 ep100 ep271 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 540680209) qz268 0 1 ep271 ep101 ep271 rfl rfl rfl rfl) rfl rfl

noncomputable def ep275 := @Enclosure.Real.IsNear.sin_image qz319 qz863 Bool.false 135326149 524288 379 524288 Bool.false 252987 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz319 Bool.false 58122138834235400301 225179981368524800 465475000240762289 646550000000000000000 135326149 524288 379 524288 (ep270 rfl) rfl) (Enclosure.sfrac_false_div 135326149 524288) (BSN.sin_reduce0 qz863 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38046987330060569018368) qz272) 226375608064910080 72057594037927936 Bool.false 252987 524288 41 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 135326149 524288 226375608064910080 72057594037927936 41 38046987330060569018368 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 252987 524288 38046987330060569018368 75557863725914323419136 540680209 1073741824 258873 258620 (ep274 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz571 := (@Enclosure.Real.IsNear.recentre' qz318 Bool.false 131071 524288 1 524288 131071 524288 1 524288 (ep268 rfl rfl) rfl)

noncomputable def ep276 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz319)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz319))) Bool.false 60189244981 274877906944 3275870426213 17772231073464320 Bool.true 33159259077 274877906944 3262537013493 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ff qz318 (Real.cos qz319) 131071 524288 1 524288 459211 524288 24766389 33897840640 60189244981 274877906944 3275870426213 17772231073464320 qz571 (@Enclosure.Real.IsNear.recentre' (Real.cos qz319) Bool.false 459211 524288 49532778 67795681280 459211 524288 24766389 33897840640 (ep273 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz318 (@Neg.neg Real Real.instNeg (Real.sin qz319)) 131071 524288 1 524288 252987 524288 24766389 33897840640 33159259077 274877906944 3262537013493 17772231073464320 qz571 (@Enclosure.Real.IsNear.neg (Real.sin qz319) Bool.false 252987 524288 24766389 33897840640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz319) Bool.false 252987 524288 49532778 67795681280 252987 524288 24766389 33897840640 (ep275 rfl rfl) rfl)) rfl)

noncomputable def ep277 := @ep168 60189244981 274877906944 3275870426213 17772231073464320 Bool.true 33159259077 274877906944 3262537013493 17772231073464320 Bool.false 86634127027242610458624 19698319881 17179869184 7382704196381 1777223107346432 Bool.true 9369005062662186336256 68168483723 274877906944 14769480506903 3554446214692864 (ep169 (BSN.head_sum_c_succ qz12 15 16 rfl rfl) (ep266 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep267 ep276) rfl rfl

theorem EMRow27.d8 : Enclosure.Complex.IsNear (BSN.headSumC qz12 17) Bool.false 19698319881 17179869184 7382704196381 1777223107346432 Bool.true 68168483723 274877906944 14769480506903 3554446214692864 := ep167 (BSN.head_sum_c_succ qz12 16 17 rfl rfl) (ep277 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow27.d9 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow27.d10 : @Eq Nat (Nat.pow 24 1) 24 := @Eq.refl Nat 24

theorem EMRow27.d11 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

noncomputable abbrev qz18 := (@HAdd.hAdd Complex Complex Complex qz261 qz260 qz549)

noncomputable def ep278 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) qz18) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1

noncomputable def ep279 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz18)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz18)) 346637161 16000 0 1 346667161 20000 0 1

noncomputable def ep280 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz18) 346637161 40000 0 1 5 2 0 1 346637161 16000

noncomputable abbrev qz572 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz19 := (@HAdd.hAdd Complex Complex Complex qz261 qz260 qz572)

noncomputable def ep281 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz19) Bool.true 346637161 40000 0 1 Bool.false 18619 100 0 1

noncomputable def ep282 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz19)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz19)) 3 4 0 1 346667161 40000 0 1

noncomputable def ep283 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz19) 1 2 0 1 3 2 0 1 3 4

noncomputable def ep284 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz12 Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 (BSN.ascPochhammer_one_eval qz12)

noncomputable abbrev qz321 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz322 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable def ep285 := ep284 (@Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk qz321 qz9) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 (BSN.s_crit_mk qz9 Bool.false 93095 1000 (@Eq.refl Real qz9)) (@Enclosure.Complex.IsNear.mk qz321 qz9 Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 qz322 qz271))

noncomputable def ep286 := @ep283 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep285)

noncomputable def ep287 := @Enclosure.Complex.IsNear.of_eq qz19 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz9) Bool.false 3 2 0 1 Bool.false 93095 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 93095 1000 1 (@Eq.refl Real qz9))

noncomputable abbrev qz573 := (ep287 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz9 Bool.false 3 2 0 1 Bool.false 93095 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz271))

noncomputable def ep288 := ep286 (@Enclosure.Complex.IsNear.re_isNear qz19 Bool.false 3 2 0 1 Bool.false 93095 1000 0 1 qz573)

noncomputable def ep289 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz19) 93095 1000 0 1 93095 1000 0 1 346667161 40000

noncomputable def ep290 := @ep289 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep285)

noncomputable def ep291 := ep290 (@Enclosure.Complex.IsNear.im_isNear qz19 Bool.false 3 2 0 1 Bool.false 93095 1000 0 1 qz573)

noncomputable def ep292 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz19 Bool.true 346637161 40000 0 1 Bool.false 18619 100 0 1 (@ep282 1386548644 346637161 40000 0 1 (ep288 rfl) (ep291 rfl) rfl rfl)

noncomputable def ep293 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz19)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz19)) 18619 400 0 1 55857 400 0 1

noncomputable def ep294 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz19) 1 2 0 1 93095 1000 0 1 18619 400

noncomputable def ep295 := @ep294 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep285)

noncomputable def ep296 := ep295 (@Enclosure.Complex.IsNear.im_isNear qz19 Bool.false 3 2 0 1 Bool.false 93095 1000 0 1 qz573)

noncomputable def ep297 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz19) 93095 1000 0 1 3 2 0 1 55857 400

noncomputable def ep298 := @ep297 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep285)

noncomputable def ep299 := ep298 (@Enclosure.Complex.IsNear.re_isNear qz19 Bool.false 3 2 0 1 Bool.false 93095 1000 0 1 qz573)

noncomputable abbrev qz574 := (ep281 (BSN.ascPochhammer_succ_eval_c 1 2 qz12 rfl) (ep292 (@ep293 29790400 18619 100 0 1 (ep296 rfl) (ep299 rfl) rfl rfl)))

noncomputable def ep300 := @ep280 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 346637161 40000 0 1 Bool.false 18619 100 0 1 qz574)

noncomputable def ep301 := @Enclosure.Complex.IsNear.of_eq qz18 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz9) Bool.false 5 2 0 1 Bool.false 93095 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 93095 1000 2 (@Eq.refl Real qz9))

noncomputable abbrev qz575 := (ep301 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz9 Bool.false 5 2 0 1 Bool.false 93095 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz271))

noncomputable def ep302 := ep300 (@Enclosure.Complex.IsNear.re_isNear qz18 Bool.false 5 2 0 1 Bool.false 93095 1000 0 1 qz575)

noncomputable def ep303 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz18) 18619 100 0 1 93095 1000 0 1 346667161 20000

noncomputable def ep304 := @ep303 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 346637161 40000 0 1 Bool.false 18619 100 0 1 qz574)

noncomputable def ep305 := ep304 (@Enclosure.Complex.IsNear.im_isNear qz18 Bool.false 5 2 0 1 Bool.false 93095 1000 0 1 qz575)

noncomputable def ep306 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) qz18 Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 (@ep279 12479417796000 3119854449 80000 0 1 (ep302 rfl) (ep305 rfl) rfl rfl)

noncomputable def ep307 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz18)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz18)) 6454037300659 8000000 0 1 18619 40 0 1

noncomputable def ep308 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz18) 346637161 40000 0 1 93095 1000 0 1 6454037300659 8000000

noncomputable def ep309 := @ep308 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 346637161 40000 0 1 Bool.false 18619 100 0 1 qz574)

noncomputable def ep310 := ep309 (@Enclosure.Complex.IsNear.im_isNear qz18 Bool.false 5 2 0 1 Bool.false 93095 1000 0 1 qz575)

noncomputable def ep311 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz18) 18619 100 0 1 5 2 0 1 18619 40

noncomputable def ep312 := @ep311 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 346637161 40000 0 1 Bool.false 18619 100 0 1 qz574)

noncomputable def ep313 := ep312 (@Enclosure.Complex.IsNear.re_isNear qz18 Bool.false 5 2 0 1 Bool.false 93095 1000 0 1 qz575)

noncomputable abbrev qz576 := (ep306 (@ep307 258012540026360 6450313500659 8000000 0 1 (ep310 rfl) (ep313 rfl) rfl rfl))

theorem EMRow27.d12 : Enclosure.Complex.IsNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 := ep278 (BSN.ascPochhammer_succ_eval_c 2 3 qz12 rfl) qz576

theorem EMRow27.d13 : @Eq Nat (Nat.pow 24 3) 13824 := @Eq.refl Nat 13824

noncomputable def ep314 := nat_lit 15525755524518471707844999773351530961

noncomputable def ep315 := nat_lit 11946672526496135369069439221760000000

noncomputable def ep316 := nat_lit 804404645895693351401784847383741018619376027

noncomputable def ep317 := nat_lit 133040972824575883144166378487974908133376000000

noncomputable abbrev qz577 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz20 := qz577

noncomputable abbrev qz21 := (Complex.Stirling.logGammaStirling 2 qz255)

noncomputable abbrev qz578 := (@HAdd.hAdd Complex Complex Complex qz808 qz809 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz810 (↑qz811) (2 : Complex))))

noncomputable abbrev qz323 := qz578

noncomputable abbrev qz22 := qz323

noncomputable abbrev qz324 := (@instHSub Real Real.instSub)

noncomputable abbrev qz325 := (@HMul.hMul Real Real Real qz0 (@HDiv.hDiv Real Real Real qz1 qz9 (2 : Real)) (Real.log Real.pi))

noncomputable def ep318 := Complex.re (@HMul.hMul Complex Complex Complex qz3 (Complex.exp (@HMul.hMul Complex Complex Complex qz3 Complex.I ↑(@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz325))) (zetaApproximant qz12 2 24))

noncomputable def ep319 := @Enclosure.Real.IsNear.of_eq ep318 (@HSub.hSub Real Real Real qz324 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz325)) (Complex.re (zetaApproximant qz12 2 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz325)) (Complex.im (zetaApproximant qz12 2 24))))

noncomputable def ep320 := nat_lit 574451971113212953211024212729096697503

noncomputable def ep321 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz325)) (Complex.re (zetaApproximant qz12 2 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz325)) (Complex.im (zetaApproximant qz12 2 24))) ep320

noncomputable def ep322 := nat_lit 442026883480357008655569251205120000000

noncomputable def ep323 := nat_lit 20084387417961389583941938740080014137537515441

noncomputable def ep324 := nat_lit 3326024320614397078604159462199372703334400000000

noncomputable def ep325 := nat_lit 491646985249989620389442454974027

noncomputable def ep326 := nat_lit 221013441740178504327784625602560000000

noncomputable def ep327 := nat_lit 4288121571824033517113740752251887991147539

noncomputable def ep328 := nat_lit 554337386769066179767359910366562117222400000000

noncomputable def ep329 := nat_lit 126961824571345458707628995321015219105616441472589893136345005471825920000000

noncomputable def ep330 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz325)) (Complex.re (zetaApproximant qz12 2 24)) 524287 524288 8212947

noncomputable def ep331 := nat_lit 1095682271567315140774087880739169

noncomputable def ep332 := nat_lit 843099371872629182158602240000000

noncomputable def ep333 := nat_lit 530451795620378815018984457872837993

noncomputable def ep334 := nat_lit 98119061799164711590435970088960000000

noncomputable def ep335 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz325)) Bool.true 524287 524288 16425894

noncomputable abbrev qz864 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20588825) qz278)

noncomputable def ep336 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz325) qz864 Bool.false 20588825 262144 125

noncomputable def ep337 := nat_lit 3259822028361998855406615773

noncomputable def ep338 := nat_lit 41505174165846491136000000

noncomputable def ep339 := nat_lit 12450310110825151166791999437381841

noncomputable def ep340 := nat_lit 26206221051687547699200000000000000000

noncomputable def ep341 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz325) Bool.false ep337 ep338 ep339 ep340

noncomputable def ep342 := nat_lit 5471396251542230262449175773

noncomputable def ep343 := nat_lit 3143714694539246270791999437381841

noncomputable def ep344 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz325 ep342 ep338 ep343 ep340 1396815999 26214400

noncomputable def ep345 := nat_lit 85454278580292782795171188519731200

noncomputable def ep346 := nat_lit 30364336777337850083466917

noncomputable def ep347 := nat_lit 1302333762115504023045520815126289

noncomputable def ep348 := nat_lit 6551555262921886924800000000000000000

noncomputable def ep349 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true ep346 415051741658464911360000 ep347 ep348 Bool.false ep342 ep338

noncomputable def ep350 := nat_lit 23986707866608303024266917

noncomputable def ep351 := nat_lit 1251668266163451727261239302780689

noncomputable def ep352 := nat_lit 5725946008619981955761175773

noncomputable def ep353 := nat_lit 2738390728023489188688624341983441

noncomputable def ep354 := @Enclosure.Complex.IsNear.subLitP qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))) Bool.true ep350 415051741658464911360000 ep351 ep348 Bool.false ep352 ep338 ep353

noncomputable def ep355 := nat_lit 68374407897885494503770045186282058940416

noncomputable def ep356 := nat_lit 770030566238809900322675320658018953068544

noncomputable abbrev qz326 := (@HSub.hSub Complex Complex Complex qz577 qz540 qz546)

noncomputable abbrev qz327 := (Complex.log qz540)

noncomputable abbrev qz23 := (@HSub.hSub Complex Complex Complex qz577 (@HMul.hMul Complex Complex Complex qz253 qz326 qz327) qz255)

noncomputable abbrev qz328 := qz546

noncomputable abbrev qz24 := qz328

noncomputable abbrev qz579 := qz810

noncomputable abbrev qz329 := qz579

noncomputable abbrev qz25 := qz329

noncomputable abbrev qz865 := (@instHMul Nat instMulNat)

noncomputable abbrev qz26 := qz865

noncomputable abbrev qz580 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz27 := qz580

noncomputable abbrev qz28 := (@instHSub Int Int.instSub)

noncomputable abbrev qz866 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz330 := qz866

noncomputable abbrev qz29 := qz330

noncomputable abbrev qz30 := (@instHMul Int Int.instMul)

noncomputable abbrev qz581 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz31 := qz581

noncomputable abbrev qz867 := (@HMul.hMul Complex Complex Complex qz3 qz24 ↑qz251)

noncomputable def ep357 := @Enclosure.Complex.IsNear.of_eq qz21 (@HAdd.hAdd Complex Complex Complex qz13 (@HAdd.hAdd Complex Complex Complex qz13 qz23 qz867) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k)))))) Bool.true ep350

noncomputable def ep358 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz13 qz23 qz867) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) Bool.true 52054633580020768841 900719925474099200

noncomputable def ep359 := nat_lit 2075258708292324556800000

noncomputable def ep360 := nat_lit 207525870829232455680000000

noncomputable def ep361 := nat_lit 21605305721980419714587673837383750936166400

noncomputable def ep362 := nat_lit 4125978929722324738099588887527348680030945280

noncomputable def ep363 := @ep358 1976362280727561289 10344800000000000000000 Bool.false 99410064262847349859 720575940379279360 1080950002667781679 10344800000000000000000 Bool.false 67287065267257665883 415051741658464911360000 342272837295211 ep359 Bool.true 73692920025396117224227 ep338 374856274813940659 ep360 Bool.true ep361 ep350 415051741658464911360000 ep351 ep348 Bool.false ep362

noncomputable def ep364 := @Enclosure.Complex.IsNear.addLitP qz23 qz867 Bool.true 52882339061462868041 900719925474099200 1936900000454123789 10344800000000000000000

noncomputable def ep365 := nat_lit 6822904932600482213527552

noncomputable def ep366 := @ep364 Bool.false 99410064262847349859 720575940379279360 1080950002667781679 10344800000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep365 52054633580020768841 900719925474099200 1976362280727561289 10344800000000000000000 Bool.false 99410064262847349859 99410064262847349859 720575940379279360

noncomputable abbrev qz32 := (@HMul.hMul Complex Complex Complex qz253 qz326 qz327)

noncomputable def ep367 := @Enclosure.Complex.IsNear.subLitP qz32 qz5 Bool.true 49054279378197946441 900719925474099200 1936900000454123789 10344800000000000000000 Bool.false 664755364238259279343

noncomputable def ep368 := nat_lit 1988201285256946997180000

noncomputable def ep369 := @ep367 3602879701896396800 1080950002667781679 10344800000000000000000 Bool.false 17000 4000 0 1 Bool.false 186190 4000 0 1 Bool.true 211529356245851472164000 52882339061462868041 900719925474099200 1936900000454123789 10344800000000000000000 Bool.false ep368 99410064262847349859 720575940379279360 1080950002667781679 10344800000000000000000

noncomputable abbrev qz33 := qz326

noncomputable abbrev qz34 := qz327

noncomputable def ep370 := @Enclosure.Complex.IsNear.mul qz33 qz34 Bool.true 49054279378197946441 900719925474099200 1936900000454123789 10344800000000000000000 Bool.false 664755364238259279343 3602879701896396800 1080950002667781679

noncomputable def ep371 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re qz33) (Complex.re qz34)) (@HMul.hMul Real Real Real qz0 (Complex.im qz33) (Complex.im qz34)) 519439388529371955 36028797018963968 150000000426723 20689600000000000000 15510066022858061329 225179981368524800

noncomputable def ep372 := nat_lit 441841668657160955632716807743209472

noncomputable def ep373 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz33) (Complex.re qz34) 15000 4000 0 1 34629292568624797 9007199254740992 50000000142241 25862000000000000000

noncomputable def ep374 := @Enclosure.Complex.IsNear.re_isNear qz33 Bool.false 15000 4000 0 1 Bool.false 186190 4000 0 1

noncomputable def ep375 := @Enclosure.Complex.IsNear.of_eq qz33 (Complex.mk (Enclosure.sfrac Bool.false 15000 4000) qz259) Bool.false 15000 4000 0 1 Bool.false 186190 4000 0

noncomputable def ep376 := @Enclosure.Complex.IsNear.of_eq qz34 (Complex.log qz258) Bool.false 34629292568624797 9007199254740992 50000000142241 25862000000000000000 Bool.false 833023579293091 562949953421312 100000000012931 25862000000000000000

noncomputable def ep377 := BSN.log_dyadic_bound 2187716100 67723716100 2 1 13759505167180197630000 524288 258620 4786101734199210000 4786101734199210000 33884 69911432200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2187716100) (BSN.artanhQ 67723716100) 0 1 4786101734199210000 13759505167180197630000 4786101734199210000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz582 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep378 := @Enclosure.Real.IsNear.mulLit_ff qz321 (Real.log (Enclosure.sfrac Bool.false 34955716100 16000000)) 1 2 0 1 34629292568624797 4503599627370496 50000000142241 12931000000000000000 34629292568624797 9007199254740992 50000000142241 25862000000000000000 qz322 (BSN.isNear_log_sfrac 34955716100 16000000 34629292568624797 4503599627370496 50000000142241 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34955716100) qz582)) Bool.false 145245780337753260556288 18889465931478580854784 1000000002844820 258620000000000000000 34629292568624797 4503599627370496 50000000142241 12931000000000000000 (BSN.log_rat_reduce_isNear 34955716100 16000000 11 69911432200 65536000000 33884 524288 24973259072661432 36028797018963968 258620 1000000000000000 rfl rfl rfl rfl (ep377 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep379 := BSN.arctan_dyadic_bound_f 17000 186190 1 0 524288 258620 0 1 1 0 1 1 47736 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 17000) (BSN.arctanEvenQ 186190) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 17000) (BSN.arctanOddQ 186190) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz331 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz332 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz583 := (@Nat.cast Real Real.instNatCast 17000)

noncomputable abbrev qz584 := (@Nat.cast Real Real.instNatCast 186190)

noncomputable def ep380 := @Enclosure.Real.IsNear.subLit_ff_p qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz583 qz584)) 884279719003555 562949953421312 1 2000000000000000 47736 524288 1 258620 436744266340416094208 833023579293091 562949953421312 100000000012931 25862000000000000000 qz332 (ep379 rfl) rfl rfl

noncomputable abbrev qz585 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 186190) (@Nat.cast Real Real.instNatCast 17000)))

noncomputable def ep381 := @Enclosure.Complex.IsNear.re_isNear qz34 Bool.false 34629292568624797 9007199254740992 50000000142241 25862000000000000000 Bool.false 833023579293091 562949953421312 100000000012931 25862000000000000000 (ep376 (@congrArg Complex Complex qz5 qz258 Complex.log qz813) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz258) Bool.false 34629292568624797 9007199254740992 50000000142241 25862000000000000000 Bool.false 833023579293091 562949953421312 100000000012931 25862000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz258)) (@HMul.hMul Real Real Real qz0 qz321 (Real.log (Enclosure.sfrac Bool.false 34955716100 16000000))) Bool.false 34629292568624797 9007199254740992 50000000142241 25862000000000000000 (Enclosure.clog_re_eq 17000 186190 4000 34955716100 16000000 rfl rfl rfl) (ep378 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz258)) qz585 Bool.false 833023579293091 562949953421312 100000000012931 25862000000000000000 (Enclosure.clog_im_eq 17000 186190 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz585 (@HSub.hSub Real Real Real qz324 qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz583 qz584))) Bool.false 833023579293091 562949953421312 100000000012931 25862000000000000000 (BSN.arctan_recip 186190 17000 rfl rfl) ep380))))

noncomputable def ep382 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz33) (Complex.im qz34) 186190 4000 0 1 833023579293091 562949953421312 100000000012931 25862000000000000000

noncomputable def ep383 := @Enclosure.Complex.IsNear.im_isNear qz33 Bool.false 15000 4000 0 1 Bool.false 186190 4000 0 1

noncomputable def ep384 := @Enclosure.Complex.IsNear.im_isNear qz34 Bool.false 34629292568624797 9007199254740992 50000000142241 25862000000000000000 Bool.false 833023579293091 562949953421312 100000000012931 25862000000000000000 (ep376 (@congrArg Complex Complex qz5 qz258 Complex.log qz813) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz258) Bool.false 34629292568624797 9007199254740992 50000000142241 25862000000000000000 Bool.false 833023579293091 562949953421312 100000000012931 25862000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz258)) (@HMul.hMul Real Real Real qz0 qz321 (Real.log (Enclosure.sfrac Bool.false 34955716100 16000000))) Bool.false 34629292568624797 9007199254740992 50000000142241 25862000000000000000 (Enclosure.clog_re_eq 17000 186190 4000 34955716100 16000000 rfl rfl rfl) (ep378 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz258)) qz585 Bool.false 833023579293091 562949953421312 100000000012931 25862000000000000000 (Enclosure.clog_im_eq 17000 186190 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz585 (@HSub.hSub Real Real Real qz324 qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz583 qz584))) Bool.false 833023579293091 562949953421312 100000000012931 25862000000000000000 (BSN.arctan_recip 186190 17000 rfl rfl) ep380))))

noncomputable abbrev qz333 := (@ep375 1 (BSN.w_sub_half_mk qz9 Bool.false 93095 1000 4 (@Eq.refl Real qz9) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 15000 4000) (Enclosure.sfrac Bool.false 186190 4000) Bool.false 15000 4000 0 1 Bool.false 186190 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 15000 4000) (Enclosure.Real.IsNear.const Bool.false 186190 4000)))

noncomputable def ep385 := @ep371 1861900000240762289 10344800000000000000000 ep372 49054279378197946441 900719925474099200 1936900000454123789 10344800000000000000000 (@ep373 519439388529371955 36028797018963968 150000000426723 20689600000000000000 (ep374 qz333) ep381 rfl) (@ep382 15510066022858061329 225179981368524800 1861900000240762289 10344800000000000000000 (ep383 qz333) ep384 rfl) rfl

noncomputable def ep386 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz33) (Complex.im qz34)) (@HMul.hMul Real Real Real qz0 (Complex.im qz33) (Complex.re qz34)) 12495353689396365 2251799813685248 300000000038793 20689600000000000000 644762798335225095343 3602879701896396800

noncomputable def ep387 := nat_lit 1496896005337981416503620857510232064

noncomputable def ep388 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz33) (Complex.im qz34) 15000 4000 0 1 833023579293091 562949953421312 100000000012931 25862000000000000000

noncomputable def ep389 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz33) (Complex.re qz34) 186190 4000 0 1 34629292568624797 9007199254740992 50000000142241 25862000000000000000

noncomputable def ep390 := @ep386 930950002648385179 10344800000000000000000 ep387 664755364238259279343 3602879701896396800 1080950002667781679 10344800000000000000000 (@ep388 12495353689396365 2251799813685248 300000000038793 20689600000000000000 (ep374 qz333) ep384 rfl) (@ep389 644762798335225095343 3602879701896396800 930950002648385179 10344800000000000000000 (ep383 qz333) ep381 rfl) rfl

noncomputable def ep391 := ep369 (@ep370 10344800000000000000000 (ep385 rfl) (ep390 rfl)) qz11 rfl rfl rfl rfl rfl rfl

noncomputable def ep392 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz24) (Complex.re ↑qz251)) (@HMul.hMul Real Real Real qz0 (Complex.im qz24) (Complex.im ↑qz251)) 120447 131072 1 262144 0 1 0 1 120447 120447

noncomputable def ep393 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz24) (Complex.re ↑qz251) 1 2 0 1 120447 65536 1 131072 120447 131072 1 262144

noncomputable abbrev qz334 := (@Enclosure.Complex.IsNear.of_eq qz24 (Complex.mk (Enclosure.sfrac Bool.false 1 2) (Enclosure.sfrac Bool.false 0 1)) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) (Enclosure.sfrac Bool.false 0 1) Bool.false 1 2 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 2) (Enclosure.Real.IsNear.const Bool.false 0 1)))

noncomputable def ep394 := ep393 (@Enclosure.Complex.IsNear.re_isNear qz24 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz334) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz251) qz251 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz251) EMRow27.d4)

noncomputable def ep395 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz24) (Complex.im ↑qz251) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep396 := ep395 (@Enclosure.Complex.IsNear.im_isNear qz24 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz334) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz251) qz263 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz251) (0 : Real) qz263 (Complex.ofReal_im qz251) Enclosure.sfrac_zero_eq) qz275)

noncomputable def ep397 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz24) (Complex.im ↑qz251)) (@HMul.hMul Real Real Real qz0 (Complex.im qz24) (Complex.re ↑qz251)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep398 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz24) (Complex.im ↑qz251) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep399 := ep398 (@Enclosure.Complex.IsNear.re_isNear qz24 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz334) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz251) qz263 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz251) (0 : Real) qz263 (Complex.ofReal_im qz251) Enclosure.sfrac_zero_eq) qz275)

noncomputable def ep400 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz24) (Complex.re ↑qz251) 0 1 0 1 120447 65536 1 131072 0 1 0 1

noncomputable def ep401 := ep400 (@Enclosure.Complex.IsNear.im_isNear qz24 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz334) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz251) qz251 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz251) EMRow27.d4)

noncomputable def ep402 := @ep366 1080950002667781679 10344800000000000000000 (ep391 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz24 (↑qz251) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep392 131072 1 262144 (ep394 rfl) (ep396 rfl) rfl rfl) (@ep397 1 0 1 (ep399 rfl) (ep401 rfl) rfl rfl))

noncomputable abbrev qz35 := (@HMul.hMul Nat Nat Nat qz865 2 2)

noncomputable abbrev qz36 := (@HMul.hMul Complex Complex Complex qz253 (@HMul.hMul Complex Complex Complex qz253 (2 : Complex) qz549) (@HSub.hSub Complex Complex Complex qz577 (@HMul.hMul Complex Complex Complex qz253 (2 : Complex) qz549) (1 : Complex)))

noncomputable abbrev qz37 := (@HPow.hPow Complex Int Complex qz580 qz255 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz330 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz581 (@Nat.cast Int instNatCastInt 2))))

noncomputable def ep403 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz37)) Bool.false 67287065267257665883 415051741658464911360000 342272837295211 ep359

noncomputable def ep404 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz37) Bool.false 16710167 103079215104 17 103079215104 Bool.true

noncomputable def ep405 := nat_lit 6935897874400540189746719096832

noncomputable def ep406 := nat_lit 759620835493967551016249433312460800

noncomputable def ep407 := @ep404 18301564669 10307921510400 18619 10307921510400 Bool.false 3045790040385883 415051741658464911360000 17630895211 ep359 Bool.true 1087163848556264227 ep338 6293169140659 ep360 Bool.false ep405 67287065267257665883 415051741658464911360000 342272837295211 ep359 Bool.true ep406 73692920025396117224227 ep338 374856274813940659

noncomputable abbrev qz38 := (@HMul.hMul Nat Nat Nat qz865 2 1)

noncomputable abbrev qz39 := (@HMul.hMul Complex Complex Complex qz253 (@HMul.hMul Complex Complex Complex qz253 (2 : Complex) qz572) (@HSub.hSub Complex Complex Complex qz577 (@HMul.hMul Complex Complex Complex qz253 (2 : Complex) qz572) (1 : Complex)))

noncomputable abbrev qz40 := (@HPow.hPow Complex Int Complex qz580 qz255 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz330 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz581 (@Nat.cast Int instNatCastInt 1))))

noncomputable def ep408 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz40)) Bool.false 16710167 103079215104 17 103079215104

noncomputable def ep409 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz40) Bool.false 0 1 0 1 Bool.false

noncomputable def ep410 := @ep409 0 1 0 1 Bool.false 16710167 103079215104 17 103079215104 Bool.true 18301564669 10307921510400 18619 10307921510400 Bool.false 16710167 16710167 103079215104 17 103079215104 Bool.true 18301564669 18301564669 10307921510400 18619

noncomputable def ep411 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz263 qz263) Bool.false 0 1 0 1 Bool.false

noncomputable def ep412 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz40 Bool.false 16710167 103079215104 17 103079215104 Bool.true 18301564669 10307921510400 18619 10307921510400

noncomputable def ep413 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz40)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz40)) 16710167 103079215104 17 103079215104 0 1 0

noncomputable def ep414 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz40) 1 12 0 1 16710167 8589934592 17 8589934592 16710167

noncomputable def ep415 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz263) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz586 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz263 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz275)

noncomputable def ep416 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep415 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz586)

noncomputable def ep417 := @Enclosure.Complex.IsNear.re_isNear qz40 Bool.false 16710167 8589934592 17 8589934592 Bool.true 18301564669 858993459200 18619 858993459200

noncomputable def ep418 := @Enclosure.Complex.IsNear.of_eq qz40 (@Inv.inv Complex Complex.instInv qz6) Bool.false 16710167 8589934592 17 8589934592 Bool.true 18301564669 858993459200 18619

noncomputable def ep419 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz6) Bool.false 16710167 8589934592 17 8589934592 Bool.true 18301564669 858993459200 18619

noncomputable abbrev qz335 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz336 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable def ep420 := @Enclosure.Real.IsNear.mulLit_ff qz7 (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz6)) 17000 4000 0 1 982951 2147483648 1 2147483648

noncomputable def ep421 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz6)) Bool.false 982951 2147483648 1 2147483648 982951 2147483648 1

noncomputable abbrev qz337 := (@instHAdd Real Real.instAdd)

noncomputable def ep422 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz6) (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 qz7 qz7) (@HMul.hMul Real Real Real qz0 qz8 qz8)) Bool.false 349557161 160000 0 1

noncomputable def ep423 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz7 qz7) (@HMul.hMul Real Real Real qz0 qz8 qz8) 289 16 0 1 346667161 160000

noncomputable def ep424 := @Enclosure.Real.IsNear.mulLit_ff qz7 qz7 17000 4000 0 1 17000 4000 0 1

noncomputable def ep425 := @Enclosure.Real.IsNear.mulLit_ff qz8 qz8 186190 4000 0 1 186190 4000 0 1

noncomputable def ep426 := @ep423 0 1 5592914576 349557161 160000 0 1 (@ep424 289 16 0 1 (ep32 qz10) (ep32 qz10) rfl) (@ep425 346667161 160000 0 1 (ep37 qz10) (ep37 qz10) rfl)

noncomputable def ep427 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz6) 349557161 160000 0 1 491475 491476 1073741824 (ep422 (Enclosure.Complex.normSq_eq_mul_add_mul qz6) (ep426 rfl rfl)) rfl

noncomputable def ep428 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz6)) (@HMul.hMul Real Real Real qz0 qz7 (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz6))) Bool.false 16710167 8589934592 17 8589934592 (Enclosure.Complex.inv_re_eq_mul qz6) (@ep420 16710167 8589934592 17 8589934592 (ep32 qz10) (@ep421 2147483648 (ep427 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep429 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz6)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz8) (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz6))) Bool.true 18301564669 858993459200 18619 858993459200 (Enclosure.Complex.inv_im_eq_mul qz6)

noncomputable def ep430 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz8) (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz6)) 186190 4000 0 1 982951 2147483648 1

noncomputable def ep431 := @ep430 2147483648 18301564669 858993459200 18619 858993459200 (@Enclosure.Real.IsNear.neg qz8 Bool.false 186190 4000 0 1 (ep37 qz10)) (@ep421 2147483648 (ep427 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep432 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz40) 0 1 0 1 18301564669 858993459200 18619 858993459200 0

noncomputable def ep433 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep415 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz586)

noncomputable def ep434 := @Enclosure.Complex.IsNear.im_isNear qz40 Bool.false 16710167 8589934592 17 8589934592 Bool.true 18301564669 858993459200 18619 858993459200

noncomputable abbrev qz587 := (@ep418 858993459200 (BSN.zpow_one_sub_two_mul qz5 1 1 rfl rfl) (@ep419 858993459200 ep428 (ep429 ep431)))

noncomputable def ep435 := @ep413 1 16710167 16710167 103079215104 17 103079215104 (@ep414 103079215104 17 103079215104 ep416 (ep417 qz587) rfl) (@ep432 1 0 1 ep433 (ep434 qz587) rfl) rfl

noncomputable def ep436 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz40)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz40)) 18301564669 10307921510400 18619 10307921510400 0 1 0

noncomputable def ep437 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz40) 1 12 0 1 18301564669 858993459200 18619 858993459200 18301564669

noncomputable def ep438 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz40) 0 1 0 1 16710167 8589934592 17 8589934592 0

noncomputable def ep439 := @ep436 1 18301564669 18301564669 10307921510400 18619 10307921510400 (@ep437 10307921510400 18619 10307921510400 ep416 (ep434 qz587) rfl) (@ep438 1 0 1 ep433 (ep417 qz587) rfl) rfl

noncomputable abbrev qz338 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 0 1) (Enclosure.sfrac Bool.false 0 1) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 0 1) (Enclosure.Real.IsNear.const Bool.false 0 1))

noncomputable def ep440 := @ep410 10307921510400 (@ep411 0 1 0 1 (BSN.stirling_sum_base qz5) qz338) (ep412 (ep435 rfl) (ep439 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep441 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz37 Bool.false 3045790040385883 415051741658464911360000 17630895211 ep359 Bool.true 1087163848556264227 ep338 6293169140659 ep360

noncomputable def ep442 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz37)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz37)) 3045790040385883 415051741658464911360000 17630895211 ep359 0 1 0

noncomputable def ep443 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz37) 1 360 0 1 3045790040385883 1152921504606846976000 17630895211 5764607523034234880000 3045790040385883

noncomputable def ep444 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) (Complex.mk (Enclosure.sfrac Bool.true 1 360) qz263) Bool.true 1 360 0 1 Bool.false 0 1 0 1

noncomputable def ep445 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) Bool.true 1 360 0 1 Bool.false 0 1 0 1 (ep444 (BSN.stirling_coeff_mk 2 1 30 Bool.true BSN.bern_real_2 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 360) qz263 Bool.true 1 360 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 360) qz275))

noncomputable def ep446 := @Enclosure.Complex.IsNear.re_isNear qz37 Bool.true 3045790040385883 1152921504606846976000 17630895211 5764607523034234880000 Bool.false 1087163848556264227 115292150460684697600000 6293169140659 576460752303423488000000

noncomputable def ep447 := @Enclosure.Complex.IsNear.of_eq qz37 (@Inv.inv Complex Complex.instInv qz2) Bool.true 3045790040385883 1152921504606846976000 17630895211 5764607523034234880000 Bool.false 1087163848556264227 115292150460684697600000 6293169140659

noncomputable def ep448 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz2) Bool.true 3045790040385883 1152921504606846976000 17630895211 5764607523034234880000 Bool.false 1087163848556264227 115292150460684697600000 6293169140659

noncomputable abbrev qz41 := (Complex.re qz252)

noncomputable def ep449 := @Enclosure.Real.IsNear.mulLit_tf qz41 (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz2)) 17630895211 640000 0 1 863765 9007199254740992 1 9007199254740992

noncomputable def ep450 := @Enclosure.Complex.IsNear.re_isNear qz2 Bool.true 17630895211 640000 0 1 Bool.true 6293169140659 64000000 0 1

noncomputable def ep451 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz2)) Bool.false 863765 9007199254740992 1 9007199254740992 863765 9007199254740992 1

noncomputable def ep452 := nat_lit 42712462492355363872164281

noncomputable abbrev qz42 := (Complex.im qz252)

noncomputable def ep453 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz2) (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 qz41 qz41) (@HMul.hMul Real Real Real qz0 qz42 qz42)) Bool.false ep452 4096000000000000 0 1

noncomputable def ep454 := nat_lit 39603977832942736526954281

noncomputable def ep455 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz41 qz41) (@HMul.hMul Real Real Real qz0 qz42 qz42) 310848465941262734521 409600000000 0 1 ep454 4096000000000000

noncomputable def ep456 := nat_lit 17495024636868757042038489497600000000

noncomputable def ep457 := @Enclosure.Real.IsNear.mulLit_tt qz41 qz41 17630895211 640000 0 1 17630895211 640000 0 1

noncomputable def ep458 := @Enclosure.Real.IsNear.mulLit_tt qz42 qz42 6293169140659 64000000 0 1 6293169140659 64000000 0 1

noncomputable def ep459 := @Enclosure.Complex.IsNear.im_isNear qz2 Bool.true 17630895211 640000 0 1 Bool.true 6293169140659 64000000 0 1

noncomputable def ep460 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz2) ep452 4096000000000000 0 1 431882 431883 4503599627370496 (ep453 (Enclosure.Complex.normSq_eq_mul_add_mul qz2) (@ep455 0 1 ep456 ep452 4096000000000000 0 1 (@ep457 310848465941262734521 409600000000 0 1 (ep450 EMRow27.d5) (ep450 EMRow27.d5) rfl) (@ep458 ep454 4096000000000000 0 1 (ep459 EMRow27.d5) (ep459 EMRow27.d5) rfl) rfl rfl)) rfl

noncomputable def ep461 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz2)) (@HMul.hMul Real Real Real qz0 qz41 (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz2))) Bool.true 3045790040385883 1152921504606846976000 17630895211 5764607523034234880000 (Enclosure.Complex.inv_re_eq_mul qz2) (@ep449 3045790040385883 1152921504606846976000 17630895211 5764607523034234880000 (ep450 EMRow27.d5) (@ep451 9007199254740992 (ep460 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep462 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz2)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz42) (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz2))) Bool.false 1087163848556264227 115292150460684697600000 6293169140659 576460752303423488000000 (Enclosure.Complex.inv_im_eq_mul qz2)

noncomputable def ep463 := @Enclosure.Real.IsNear.mulLit_ff (@Neg.neg Real Real.instNeg qz42) (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz2)) 6293169140659 64000000 0 1 863765 9007199254740992 1

noncomputable def ep464 := @ep463 9007199254740992 1087163848556264227 115292150460684697600000 6293169140659 576460752303423488000000 (@Enclosure.Real.IsNear.neg qz42 Bool.true 6293169140659 64000000 0 1 (ep459 EMRow27.d5)) (@ep451 9007199254740992 (ep460 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep465 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz37) 0 1 0 1 1087163848556264227 115292150460684697600000 6293169140659 576460752303423488000000 0

noncomputable def ep466 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) Bool.true 1 360 0 1 Bool.false 0 1 0 1 (ep444 (BSN.stirling_coeff_mk 2 1 30 Bool.true BSN.bern_real_2 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 360) qz263 Bool.true 1 360 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 360) qz275))

noncomputable def ep467 := @Enclosure.Complex.IsNear.im_isNear qz37 Bool.true 3045790040385883 1152921504606846976000 17630895211 5764607523034234880000 Bool.false 1087163848556264227 115292150460684697600000 6293169140659 576460752303423488000000

noncomputable abbrev qz588 := (@ep447 576460752303423488000000 (BSN.zpow_one_sub_two_mul qz5 2 3 rfl rfl) (@ep448 576460752303423488000000 ep461 (ep462 ep464)))

noncomputable def ep468 := @ep442 1 3045790040385883 3045790040385883 415051741658464911360000 17630895211 ep359 (@ep443 415051741658464911360000 17630895211 ep359 ep445 (ep446 qz588) rfl) (@ep465 1 0 1 ep466 (ep467 qz588) rfl) rfl

noncomputable def ep469 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz37)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz37)) 1087163848556264227 ep338 6293169140659 ep360 0 1 0

noncomputable def ep470 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz37) 1 360 0 1 1087163848556264227 115292150460684697600000 6293169140659 576460752303423488000000 1087163848556264227

noncomputable def ep471 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz37) 0 1 0 1 3045790040385883 1152921504606846976000 17630895211 5764607523034234880000 0

noncomputable def ep472 := @ep469 1 1087163848556264227 1087163848556264227 ep338 6293169140659 ep360 (@ep470 ep338 6293169140659 ep360 ep445 (ep467 qz588) rfl) (@ep471 1 0 1 ep466 (ep446 qz588) rfl) rfl

noncomputable def ep473 := @ep407 ep360 (@ep408 Bool.true 18301564669 10307921510400 18619 10307921510400 (BSN.stirling_sum_succ qz5 0 1 rfl) (ep440 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep441 (ep468 rfl) (ep472 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep474 := @ep363 ep352 ep338 ep353 ep340 (ep402 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep403 Bool.true 73692920025396117224227 ep338 374856274813940659 ep360 (BSN.stirling_sum_succ qz5 1 2 rfl) (ep473 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep475 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz9 4) Bool.false 34600851295190685 2251799813685248 50000000142241 6465500000000000000 Bool.false 863138010924451 140737488355328

noncomputable abbrev qz868 := (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz548)

noncomputable def ep476 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 4) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz9 3) (Complex.log qz868)) Bool.false 34600851295190685 2251799813685248 50000000142241 6465500000000000000 Bool.false 863138010924451 140737488355328 100000000012931 6465500000000000000

noncomputable def ep477 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz9 3) (Complex.log qz868) Bool.false 103789600264207319 9007199254740992 150000000426723 25862000000000000000 Bool.false 2607513293394153 562949953421312 300000000038793 25862000000000000000 Bool.false

noncomputable def ep478 := nat_lit 1246627047997781702890699704238080

noncomputable def ep479 := nat_lit 1943614012184334314637621198848

noncomputable abbrev qz869 := (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz549)

noncomputable def ep480 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 3) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz9 2) (Complex.log qz869)) Bool.false 103789600264207319 9007199254740992 150000000426723 25862000000000000000 Bool.false 2607513293394153 562949953421312 300000000038793 25862000000000000000

noncomputable def ep481 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz9 2) (Complex.log qz869) Bool.false 34593592800460445 4503599627370496 50000000142241 12931000000000000000 Bool.false 875211969299875 281474976710656 100000000012931 12931000000000000000 Bool.false

noncomputable def ep482 := nat_lit 467426805074816815038557767860224

noncomputable def ep483 := nat_lit 733949743530845141245643194368

noncomputable abbrev qz870 := (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz572)

noncomputable def ep484 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 2) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz9 1) (Complex.log qz870)) Bool.false 34593592800460445 4503599627370496 50000000142241 12931000000000000000 Bool.false 875211969299875 281474976710656 100000000012931 12931000000000000000

noncomputable def ep485 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz9 1) (Complex.log qz870) Bool.false 34592038022299293 9007199254740992 50000000142241 25862000000000000000 Bool.false 881257135768995 562949953421312 100000000012931 25862000000000000000 Bool.false

noncomputable def ep486 := nat_lit 623182766582241333153813632122880

noncomputable def ep487 := nat_lit 985401074702278758731087872000

noncomputable abbrev qz871 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep488 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 1) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz9 0) qz871) Bool.false 34592038022299293 9007199254740992 50000000142241 25862000000000000000 Bool.false 881257135768995 562949953421312 100000000012931 25862000000000000000

noncomputable def ep489 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz9 0) qz871 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz589 := (Enclosure.sfrac Bool.false 1000 4000)

noncomputable def ep490 := @Enclosure.Complex.IsNear.of_eq qz871 (Complex.log (Complex.mk qz589 qz259)) Bool.false 34592038022299293 9007199254740992 50000000142241 25862000000000000000 Bool.false 881257135768995 562949953421312 100000000012931 25862000000000000000

noncomputable def ep491 := BSN.log_dyadic_bound 1899716100 67435716100 2 1 13642727417759397630000 524288 258620 3608921260599210000 3608921260599210000 29547 69335432200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1899716100) (BSN.artanhQ 67435716100) 0 1 3608921260599210000 13642727417759397630000 3608921260599210000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep492 := @Enclosure.Real.IsNear.mulLit_ff qz321 (Real.log (Enclosure.sfrac Bool.false 34667716100 16000000)) 1 2 0 1 34592038022299293 4503599627370496 50000000142241 12931000000000000000 34592038022299293 9007199254740992 50000000142241 25862000000000000000 qz322 (BSN.isNear_log_sfrac 34667716100 16000000 34592038022299293 4503599627370496 50000000142241 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34667716100) qz582)) Bool.false 145089523445082013827072 18889465931478580854784 1000000002844820 258620000000000000000 34592038022299293 4503599627370496 50000000142241 12931000000000000000 (BSN.log_rat_reduce_isNear 34667716100 16000000 11 69335432200 65536000000 29547 524288 24973259072661432 36028797018963968 258620 1000000000000000 rfl rfl rfl rfl (ep491 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep493 := BSN.arctan_dyadic_bound_f 1000 186190 1 0 524288 258620 0 1 1 0 1 1 2815 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 186190) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 186190) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz872 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable def ep494 := @Enclosure.Real.IsNear.subLit_ff_p qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz872 qz584)) 884279719003555 562949953421312 1 2000000000000000 2815 524288 1 258620 462032541198054850560 881257135768995 562949953421312 100000000012931 25862000000000000000 qz332 (ep493 rfl) rfl rfl

noncomputable abbrev qz873 := (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable def ep495 := @ep489 34592038022299293 9007199254740992 50000000142241 25862000000000000000 Bool.false 881257135768995 562949953421312 100000000012931 25862000000000000000 Bool.false 34592038022299293 34592038022299293 9007199254740992 50000000142241 25862000000000000000 Bool.false 881257135768995 881257135768995 562949953421312 100000000012931 25862000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 0) (Complex.mk qz263 qz263) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz9) qz338) (ep490 (@congrArg Complex Complex qz873 (Complex.mk qz589 qz259) Complex.log (BSN.w_shift_mk qz9 Bool.false 93095 1000 0 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz589 qz259)) Bool.false 34592038022299293 9007199254740992 50000000142241 25862000000000000000 Bool.false 881257135768995 562949953421312 100000000012931 25862000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz589 qz259))) (@HMul.hMul Real Real Real qz0 qz321 (Real.log (Enclosure.sfrac Bool.false 34667716100 16000000))) Bool.false 34592038022299293 9007199254740992 50000000142241 25862000000000000000 (Enclosure.clog_re_eq 1000 186190 4000 34667716100 16000000 rfl rfl rfl) (ep492 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz589 qz259))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz584 qz872)) Bool.false 881257135768995 562949953421312 100000000012931 25862000000000000000 (Enclosure.clog_im_eq 1000 186190 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz584 qz872)) (@HSub.hSub Real Real Real qz324 qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz872 qz584))) Bool.false 881257135768995 562949953421312 100000000012931 25862000000000000000 (BSN.arctan_recip 186190 1000 rfl rfl) ep494)))) rfl rfl

noncomputable abbrev qz590 := (Enclosure.sfrac Bool.false 5000 4000)

noncomputable def ep496 := @Enclosure.Complex.IsNear.of_eq (Complex.log qz870) (Complex.log (Complex.mk qz590 qz259)) Bool.false 34595147578621597 9007199254740992 50000000142241 25862000000000000000 Bool.false 869166802830755 562949953421312 100000000012931 25862000000000000000

noncomputable def ep497 := BSN.log_dyadic_bound 1923716100 67459716100 2 1 13652439888877797630000 524288 258620 3700683633399210000 3700683633399210000 29909 69383432200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1923716100) (BSN.artanhQ 67459716100) 0 1 3700683633399210000 13652439888877797630000 3700683633399210000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep498 := @Enclosure.Real.IsNear.mulLit_ff qz321 (Real.log (Enclosure.sfrac Bool.false 34691716100 16000000)) 1 2 0 1 34595147578621597 4503599627370496 50000000142241 12931000000000000000 34595147578621597 9007199254740992 50000000142241 25862000000000000000 qz322 (BSN.isNear_log_sfrac 34691716100 16000000 34595147578621597 4503599627370496 50000000142241 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34691716100) qz582)) Bool.false 145102565869602878783488 18889465931478580854784 1000000002844820 258620000000000000000 34595147578621597 4503599627370496 50000000142241 12931000000000000000 (BSN.log_rat_reduce_isNear 34691716100 16000000 11 69383432200 65536000000 29909 524288 24973259072661432 36028797018963968 258620 1000000000000000 rfl rfl rfl rfl (ep497 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep499 := BSN.arctan_dyadic_bound_f 5000 186190 1 0 524288 258620 0 1 1 0 1 1 14075 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 186190) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 186190) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz874 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep500 := @Enclosure.Real.IsNear.subLit_ff_p qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz874 qz584)) 884279719003555 562949953421312 1 2000000000000000 14075 524288 1 258620 455693724722530877440 869166802830755 562949953421312 100000000012931 25862000000000000000 qz332 (ep499 rfl) rfl rfl

noncomputable def ep501 := @ep485 34595147578621597 9007199254740992 50000000142241 25862000000000000000 Bool.false 869166802830755 562949953421312 100000000012931 25862000000000000000 Bool.false ep486 34593592800460445 4503599627370496 50000000142241 12931000000000000000 Bool.false ep487 875211969299875 281474976710656 100000000012931 12931000000000000000 (ep488 (BSN.log_sum_c_succ qz9 0 1 rfl) (ep495 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep496 (@congrArg Complex Complex qz870 (Complex.mk qz590 qz259) Complex.log (BSN.w_shift_mk qz9 Bool.false 93095 1000 1 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz590 qz259)) Bool.false 34595147578621597 9007199254740992 50000000142241 25862000000000000000 Bool.false 869166802830755 562949953421312 100000000012931 25862000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz590 qz259))) (@HMul.hMul Real Real Real qz0 qz321 (Real.log (Enclosure.sfrac Bool.false 34691716100 16000000))) Bool.false 34595147578621597 9007199254740992 50000000142241 25862000000000000000 (Enclosure.clog_re_eq 5000 186190 4000 34691716100 16000000 rfl rfl rfl) (ep498 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz590 qz259))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz584 qz874)) Bool.false 869166802830755 562949953421312 100000000012931 25862000000000000000 (Enclosure.clog_im_eq 5000 186190 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz584 qz874)) (@HSub.hSub Real Real Real qz324 qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz874 qz584))) Bool.false 869166802830755 562949953421312 100000000012931 25862000000000000000 (BSN.arctan_recip 186190 5000 rfl rfl) ep500)))) rfl rfl

noncomputable abbrev qz591 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable def ep502 := @Enclosure.Complex.IsNear.of_eq (Complex.log qz869) (Complex.log (Complex.mk qz591 qz259)) Bool.false 34602414663286429 9007199254740992 50000000142241 25862000000000000000 Bool.false 857089354794403 562949953421312 100000000012931 25862000000000000000

noncomputable def ep503 := BSN.log_dyadic_bound 1979716100 67515716100 2 1 13675115761487397630000 524288 258620 3919275836599210000 3919275836599210000 30755 69495432200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1979716100) (BSN.artanhQ 67515716100) 0 1 3919275836599210000 13675115761487397630000 3919275836599210000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep504 := @Enclosure.Real.IsNear.mulLit_ff qz321 (Real.log (Enclosure.sfrac Bool.false 34747716100 16000000)) 1 2 0 1 34602414663286429 4503599627370496 50000000142241 12931000000000000000 34602414663286429 9007199254740992 50000000142241 25862000000000000000 qz322 (BSN.isNear_log_sfrac 34747716100 16000000 34602414663286429 4503599627370496 50000000142241 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34747716100) qz582)) Bool.false 145133046231880922300416 18889465931478580854784 1000000002844820 258620000000000000000 34602414663286429 4503599627370496 50000000142241 12931000000000000000 (BSN.log_rat_reduce_isNear 34747716100 16000000 11 69495432200 65536000000 30755 524288 24973259072661432 36028797018963968 258620 1000000000000000 rfl rfl rfl rfl (ep503 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep505 := BSN.arctan_dyadic_bound_f 9000 186190 1 0 524288 258620 0 1 1 0 1 1 25323 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 186190) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 186190) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz875 := (@Nat.cast Real Real.instNatCast 9000)

noncomputable def ep506 := @Enclosure.Real.IsNear.subLit_ff_p qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz875 qz584)) 884279719003555 562949953421312 1 2000000000000000 25323 524288 1 258620 449361663646447960064 857089354794403 562949953421312 100000000012931 25862000000000000000 qz332 (ep505 rfl) rfl rfl

noncomputable def ep507 := @ep481 34602414663286429 9007199254740992 50000000142241 25862000000000000000 Bool.false 857089354794403 562949953421312 100000000012931 25862000000000000000 Bool.false ep482 103789600264207319 9007199254740992 150000000426723 25862000000000000000 Bool.false ep483 2607513293394153 562949953421312 300000000038793 25862000000000000000 (ep484 (BSN.log_sum_c_succ qz9 1 2 rfl) (ep501 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep502 (@congrArg Complex Complex qz869 (Complex.mk qz591 qz259) Complex.log (BSN.w_shift_mk qz9 Bool.false 93095 1000 2 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz591 qz259)) Bool.false 34602414663286429 9007199254740992 50000000142241 25862000000000000000 Bool.false 857089354794403 562949953421312 100000000012931 25862000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz591 qz259))) (@HMul.hMul Real Real Real qz0 qz321 (Real.log (Enclosure.sfrac Bool.false 34747716100 16000000))) Bool.false 34602414663286429 9007199254740992 50000000142241 25862000000000000000 (Enclosure.clog_re_eq 9000 186190 4000 34747716100 16000000 rfl rfl rfl) (ep504 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz591 qz259))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz584 qz875)) Bool.false 857089354794403 562949953421312 100000000012931 25862000000000000000 (Enclosure.clog_im_eq 9000 186190 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz584 qz875)) (@HSub.hSub Real Real Real qz324 qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz875 qz584))) Bool.false 857089354794403 562949953421312 100000000012931 25862000000000000000 (BSN.arctan_recip 186190 9000 rfl rfl) ep506)))) rfl rfl

noncomputable abbrev qz592 := (Enclosure.sfrac Bool.false 13000 4000)

noncomputable def ep508 := @Enclosure.Complex.IsNear.of_eq (Complex.log qz868) (Complex.log (Complex.mk qz592 qz259)) Bool.false 34613804916555421 9007199254740992 50000000142241 25862000000000000000 Bool.false 845038750303651 562949953421312 100000000012931 25862000000000000000

noncomputable def ep509 := BSN.log_dyadic_bound 2067716100 67603716100 2 1 13710787291588197630000 524288 258620 4275449870199210000 4275449870199210000 32081 69671432200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2067716100) (BSN.artanhQ 67603716100) 0 1 4275449870199210000 13710787291588197630000 4275449870199210000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep510 := @Enclosure.Real.IsNear.mulLit_ff qz321 (Real.log (Enclosure.sfrac Bool.false 34835716100 16000000)) 1 2 0 1 34613804916555421 4503599627370496 50000000142241 12931000000000000000 34613804916555421 9007199254740992 50000000142241 25862000000000000000 qz322 (BSN.isNear_log_sfrac 34835716100 16000000 34613804916555421 4503599627370496 50000000142241 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34835716100) qz582)) Bool.false 145180820416728068521984 18889465931478580854784 1000000002844820 258620000000000000000 34613804916555421 4503599627370496 50000000142241 12931000000000000000 (BSN.log_rat_reduce_isNear 34835716100 16000000 11 69671432200 65536000000 32081 524288 24973259072661432 36028797018963968 258620 1000000000000000 rfl rfl rfl rfl (ep509 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep511 := BSN.arctan_dyadic_bound_f 13000 186190 1 0 524288 258620 0 1 1 0 1 1 36546 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 13000) (BSN.arctanEvenQ 186190) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 13000) (BSN.arctanOddQ 186190) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz876 := (@Nat.cast Real Real.instNatCast 13000)

noncomputable def ep512 := @Enclosure.Real.IsNear.subLit_ff_p qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz876 qz584)) 884279719003555 562949953421312 1 2000000000000000 36546 524288 1 258620 443043676319200575488 845038750303651 562949953421312 100000000012931 25862000000000000000 qz332 (ep511 rfl) rfl rfl

noncomputable def ep513 := @ep477 34613804916555421 9007199254740992 50000000142241 25862000000000000000 Bool.false 845038750303651 562949953421312 100000000012931 25862000000000000000 Bool.false ep478 34600851295190685 2251799813685248 50000000142241 6465500000000000000 Bool.false ep479 863138010924451 140737488355328 100000000012931 6465500000000000000 (ep480 (BSN.log_sum_c_succ qz9 2 3 rfl) (ep507 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep508 (@congrArg Complex Complex qz868 (Complex.mk qz592 qz259) Complex.log (BSN.w_shift_mk qz9 Bool.false 93095 1000 3 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz592 qz259)) Bool.false 34613804916555421 9007199254740992 50000000142241 25862000000000000000 Bool.false 845038750303651 562949953421312 100000000012931 25862000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz592 qz259))) (@HMul.hMul Real Real Real qz0 qz321 (Real.log (Enclosure.sfrac Bool.false 34835716100 16000000))) Bool.false 34613804916555421 9007199254740992 50000000142241 25862000000000000000 (Enclosure.clog_re_eq 13000 186190 4000 34835716100 16000000 rfl rfl rfl) (ep510 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz592 qz259))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz584 qz876)) Bool.false 845038750303651 562949953421312 100000000012931 25862000000000000000 (Enclosure.clog_im_eq 13000 186190 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz584 qz876)) (@HSub.hSub Real Real Real qz324 qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz876 qz584))) Bool.false 845038750303651 562949953421312 100000000012931 25862000000000000000 (BSN.arctan_recip 186190 13000 rfl rfl) ep512)))) rfl rfl

noncomputable def ep514 := @ep354 ep340 Bool.false 34600851295190685 2251799813685248 50000000142241 6465500000000000000 Bool.false 863138010924451 140737488355328 100000000012931 6465500000000000000 Bool.true ep355 ep346 415051741658464911360000 ep347 ep348 Bool.false ep356 ep342 ep338 ep343 ep340 (@ep357 415051741658464911360000 ep351 ep348 Bool.false ep352 ep338 ep353 ep340 (BSN.logGammaStirling_unfold 2 qz5) (ep474 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep475 100000000012931 6465500000000000000 (BSN.log_sum_c_eq qz9 4) (ep476 (BSN.log_sum_c_succ qz9 3 4 rfl) (ep513 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable def ep515 := @Enclosure.Real.IsNear.mulLit_ff (@HDiv.hDiv Real Real Real qz1 qz9 (2 : Real)) (Real.log Real.pi) 93095 2000 0 1 75021 65536 1 131072 1396815999 26214400 18619 52428800 (@Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real qz1 qz9 (2 : Real)) (Enclosure.sfrac Bool.false 93095 2000) Bool.false 93095 2000 0 1 (BSN.t_half_eq qz9 Bool.false 93095 1000 (@Eq.refl Real qz9)) (Enclosure.Real.IsNear.const Bool.false 93095 2000)) EMRow27.d6 rfl

noncomputable def ep516 := @ep344 18619 52428800 ep345 ep337 ep338 ep339 ep340 (@ep349 ep343 ep340 (ep514 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep515 rfl rfl

noncomputable def ep517 := BSN.cos_dyadic_bound_f 341546 1073741824 1 0 524288 258873 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 341546) qz273 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 341546) qz274 0 0 rfl) rfl rfl

noncomputable def ep518 := @ep336 262144 Bool.true 524287 524288 1 129310 (@ep341 20588825 262144 125 262144 ep516 rfl) (Enclosure.sfrac_false_div 20588825 262144) (BSN.cos_reduce2 qz864 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12017107493873254400) qz280) 226375608064910080 72057594037927936 Bool.false 524287 524288 12 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 20588825 262144 226375608064910080 72057594037927936 12 12017107493873254400 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 12017107493873254400 37778931862957161709568 341546 1073741824 258873 258620 (ep517 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep519 := nat_lit 5923457653614332775776415120169

noncomputable def ep520 := nat_lit 35360837382840815151006615099807449

noncomputable def ep521 := nat_lit 6541270786610980772695731339264000000

noncomputable abbrev qz593 := (@Nat.cast Complex Complex.instNatCast 24)

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz815 qz593 (@Neg.neg Complex Complex.instNeg qz260))

noncomputable abbrev qz44 := (@HAdd.hAdd Complex Complex Complex qz261 (@HDiv.hDiv Complex Complex Complex qz329 qz593 (@HSub.hSub Complex Complex Complex qz577 qz260 (1 : Complex))) qz328)

noncomputable abbrev qz45 := (@instHSub Nat instSubNat)

noncomputable abbrev qz46 := qz254

noncomputable abbrev qz47 := qz593

noncomputable def ep522 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz12 2 24) (@HAdd.hAdd Complex Complex Complex qz13 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz15) (@HMul.hMul Complex Complex Complex qz3 qz43 (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) Bool.false ep331 ep332 ep333

noncomputable def ep523 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz15) (@HMul.hMul Complex Complex Complex qz3 qz43 (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) Bool.false 164410209487 137438953472 23585727993499 4443057768366080

noncomputable def ep524 := nat_lit 87131632565421858661616840739169

noncomputable def ep525 := nat_lit 9592148228609590042092029584837993

noncomputable def ep526 := nat_lit 23970165292782301530833055120169

noncomputable def ep527 := nat_lit 638010999283353554939204360607449

noncomputable def ep528 := nat_lit 150589424742035494148810994304149733158944768

noncomputable def ep529 := nat_lit 50882113803028910937641207898491529986048

noncomputable def ep530 := @ep523 Bool.false 183869237 8589934592 47169893598923 8886115536732160 Bool.false ep524 ep332 ep525 ep334 Bool.true ep526 ep332 ep527 ep521 Bool.false ep528 ep331 ep332 ep333 ep334 Bool.true ep529 ep519 ep332

noncomputable def ep531 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz15) (BSN.headSumC qz12 24) Bool.false 164410209487 137438953472 23585727993499 4443057768366080 Bool.false 183869237 8589934592 47169893598923

noncomputable abbrev qz877 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 23) qz15)

noncomputable def ep532 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 24) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 23) qz877) Bool.false 164410209487 137438953472 23585727993499 4443057768366080 Bool.false 183869237 8589934592 47169893598923 8886115536732160

noncomputable def ep533 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 23) qz877 Bool.false 192033877051 137438953472 11451224305201 2221528884183040 Bool.false 21141856875 274877906944 91630320270493 17772231073464320 Bool.true

noncomputable abbrev qz878 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 22) qz15)

noncomputable def ep534 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 23) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 22) qz878) Bool.false 192033877051 137438953472 11451224305201 2221528884183040 Bool.false 21141856875 274877906944 91630320270493 17772231073464320

noncomputable def ep535 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 22) qz878 Bool.false 183245588513 137438953472 22209617001067 4443057768366080 Bool.true 34764633533 274877906944 88836823116413 17772231073464320 Bool.false

noncomputable abbrev qz879 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 21) qz15)

noncomputable def ep536 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 22) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 21) qz879) Bool.false 183245588513 137438953472 22209617001067 4443057768366080 Bool.true 34764633533 274877906944 88836823116413 17772231073464320

noncomputable def ep537 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 21) qz879 Bool.false 320084484037 274877906944 85986117191573 17772231073464320 Bool.false 3240663359 274877906944 85989220114333 17772231073464320 Bool.false

noncomputable abbrev qz880 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 20) qz15)

noncomputable def ep538 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 21) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 20) qz880) Bool.false 320084484037 274877906944 85986117191573 17772231073464320 Bool.false 3240663359 274877906944 85989220114333 17772231073464320

noncomputable def ep539 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 20) qz880 Bool.false 5726933273 4294967296 41532286750547 8886115536732160 Bool.false 43506196459 274877906944 83071081220809 17772231073464320 Bool.true

noncomputable abbrev qz881 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 19) qz15)

noncomputable def ep540 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 20) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 19) qz881) Bool.false 5726933273 4294967296 41532286750547 8886115536732160 Bool.false 43506196459 274877906944 83071081220809 17772231073464320

noncomputable def ep541 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 19) qz881 Bool.false 205369024657 137438953472 20017420471721 4443057768366080 Bool.true 1457702111 274877906944 80075786676639 17772231073464320 Bool.true

noncomputable abbrev qz882 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 18) qz15)

noncomputable def ep542 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 19) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 18) qz882) Bool.false 205369024657 137438953472 20017420471721 4443057768366080 Bool.true 1457702111 274877906944 80075786676639 17772231073464320

noncomputable def ep543 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 18) qz882 Bool.false 95306528741 68719476736 114927909893 26525718020096 Bool.true 29567363443 137438953472 14364378417 3315714752512 Bool.false

noncomputable abbrev qz883 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 17) qz15)

noncomputable def ep544 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 18) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 17) qz883) Bool.false 95306528741 68719476736 114927909893 26525718020096 Bool.true 29567363443 137438953472 14364378417 3315714752512

noncomputable def ep545 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 17) qz883 Bool.false 19698319881 17179869184 7382704196381 1777223107346432 Bool.true 68168483723 274877906944 14769480506903 3554446214692864 Bool.false

noncomputable abbrev qz884 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz339 := (@Inv.inv Real Real.instInv (Real.sqrt qz884))

noncomputable abbrev qz340 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable def ep546 := @Enclosure.Complex.IsNear.of_eq qz883 (Complex.mk (@HMul.hMul Real Real Real qz0 qz339 (Real.cos qz340)) (@HMul.hMul Real Real Real qz0 qz339 (@Neg.neg Real Real.instNeg (Real.sin qz340)))) Bool.false 16513249217 68719476736 158732883225 888611553673216 Bool.false 9033756837 274877906944 629133156121 3554446214692864 (BSN.cpow_neg_s_mk qz9 93095 1000 17 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz885 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz266)

noncomputable def ep547 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz884) 2161695 524288 1 524288 63579 63580 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz884) (Real.sqrt qz885) Bool.false 2161695 524288 1 524288 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz885) Bool.false 2161695 524288 1 524288 2161695 524288 1 524288 (BSN.sqrt_enclosure 17 1 1080847 1080848 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep548 := BSN.log_dyadic_bound 1 33 2 1 3267 262144 129310 1 1 15892 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz341 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable def ep549 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz341 93095 1000 0 1 3189913004350711 1125899906842624 25000000012931 3232750000000000000 59392990228005888109 225179981368524800 465475000240762289 646550000000000000000 qz271 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz885) Bool.false 26758929747600409100288 9444732965739290427392 1000000000517240 129310000000000000000 3189913004350711 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep548 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep550 := nat_lit 22680033238119678363418799600821375437701640779383589870863773012961447870720

noncomputable def ep551 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep552 := nat_lit 31747398403958113083982522315166492362620558935070465367526099191093494016

noncomputable def ep553 := nat_lit 59348686502421320673484693918402856587298149707728811765476744206684878766336

noncomputable def ep554 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable def ep555 := BSN.sin_dyadic_bound_f 1540683806 1073741824 3 2 524288 258873 ep550 ep551 ep552 ep553 ep554 ep552 519452 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1540683806) qz267 0 2 ep550 ep551 ep552 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1540683806) qz268 0 2 ep553 ep554 ep552 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz886 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 138285081) qz269)

noncomputable def ep556 := @Enclosure.Real.IsNear.cos_image qz340 qz886 Bool.false 138285081 524288 189 262144 Bool.false 519452 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz340 Bool.false 59392990228005888109 225179981368524800 465475000240762289 646550000000000000000 138285081 524288 189 262144 (ep549 rfl) rfl) (Enclosure.sfrac_false_div 138285081 524288) (BSN.cos_reduce3 qz886 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108415984610322207997952) qz272) 226375608064910080 72057594037927936 Bool.false 519452 524288 41 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 138285081 524288 226375608064910080 72057594037927936 41 108415984610322207997952 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 519452 524288 108415984610322207997952 75557863725914323419136 1540683806 1073741824 258873 258620 (ep555 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep557 := nat_lit 12614128420468247141047769788151949239773187348073136801754329940174623703296

noncomputable def ep558 := nat_lit 37778890464596825196975344319825514734594320926349269474527937622141684121856

noncomputable def ep559 := BSN.cos_dyadic_bound_f 1540683806 1073741824 3 2 524288 258873 ep557 ep199 ep552 ep558 ep202 ep552 71043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1540683806) qz273 0 2 ep557 ep199 ep552 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1540683806) qz274 0 2 ep558 ep202 ep552 rfl rfl rfl rfl) rfl rfl

noncomputable def ep560 := @Enclosure.Real.IsNear.sin_image qz340 qz886 Bool.false 138285081 524288 189 262144 Bool.true 71043 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz340 Bool.false 59392990228005888109 225179981368524800 465475000240762289 646550000000000000000 138285081 524288 189 262144 (ep549 rfl) rfl) (Enclosure.sfrac_false_div 138285081 524288) (BSN.sin_reduce3 qz886 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108415984610322207997952) qz272) 226375608064910080 72057594037927936 Bool.false 71043 524288 41 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 138285081 524288 226375608064910080 72057594037927936 41 108415984610322207997952 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 71043 524288 108415984610322207997952 75557863725914323419136 1540683806 1073741824 258873 258620 (ep559 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz594 := (@Enclosure.Real.IsNear.recentre' qz339 Bool.false 127159 524288 1 524288 127159 524288 1 524288 (ep547 rfl rfl) rfl)

noncomputable def ep561 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz339 (Real.cos qz340)) (@HMul.hMul Real Real Real qz0 qz339 (@Neg.neg Real Real.instNeg (Real.sin qz340))) Bool.false 16513249217 68719476736 158732883225 888611553673216 Bool.false 9033756837 274877906944 629133156121 3554446214692864 (@Enclosure.Real.IsNear.mulLit_ff qz339 (Real.cos qz340) 127159 524288 1 524288 129863 131072 12350867 16948920320 16513249217 68719476736 158732883225 888611553673216 qz594 (@Enclosure.Real.IsNear.recentre' (Real.cos qz340) Bool.false 519452 524288 24701734 33897840640 129863 131072 12350867 16948920320 (ep556 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz339 (@Neg.neg Real Real.instNeg (Real.sin qz340)) 127159 524288 1 524288 71043 524288 12350867 16948920320 9033756837 274877906944 629133156121 3554446214692864 qz594 (@Enclosure.Real.IsNear.neg (Real.sin qz340) Bool.true 71043 524288 12350867 16948920320 (@Enclosure.Real.IsNear.recentre' (Real.sin qz340) Bool.true 71043 524288 24701734 33897840640 71043 524288 12350867 16948920320 (ep560 rfl rfl) rfl)) rfl)

noncomputable def ep562 := @ep545 16513249217 68719476736 158732883225 888611553673216 Bool.false 9033756837 274877906944 629133156121 3554446214692864 Bool.false 1637353696151516217344 95306528741 68719476736 114927909893 26525718020096 Bool.true 16254829954128762896384 29567363443 137438953472 14364378417 3315714752512 EMRow27.d8 (ep546 ep561) rfl rfl

noncomputable abbrev qz887 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz342 := (@Inv.inv Real Real.instInv (Real.sqrt qz887))

noncomputable abbrev qz343 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 18 1)))

noncomputable def ep563 := @Enclosure.Complex.IsNear.of_eq qz882 (Complex.mk (@HMul.hMul Real Real Real qz0 qz342 (Real.cos qz343)) (@HMul.hMul Real Real Real qz0 qz342 (@Neg.neg Real Real.instNeg (Real.sin qz343)))) Bool.false 14755967175 137438953472 1533991129287 8886115536732160 Bool.false 57677024775 274877906944 3082718361519 17772231073464320 (BSN.cpow_neg_s_mk qz9 93095 1000 18 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz888 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz266)

noncomputable def ep564 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz887) 2224365 524288 1 524288 61787 61788 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz887) (Real.sqrt qz888) Bool.false 2224365 524288 1 524288 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz888) Bool.false 2224365 524288 1 524288 2224365 524288 1 524288 (BSN.sqrt_enclosure 18 1 1112182 1112183 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep565 := BSN.log_dyadic_bound 2 34 2 1 3468 262144 129310 4 4 30876 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz344 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable def ep566 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz344 93095 1000 0 1 3254268794313975 1125899906842624 25000000012931 3232750000000000000 2423649227253276021 9007199254740992 465475000240762289 646550000000000000000 qz271 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz888) Bool.false 27298785242132565196800 9444732965739290427392 1000000000517240 129310000000000000000 3254268794313975 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep565 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep567 := nat_lit 66503087397785628022154182394812641

noncomputable def ep568 := BSN.sin_dyadic_bound_f 507820761 1073741824 2 1 524288 258873 ep567 ep100 ep567 ep567 ep101 ep567 238818 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 507820761) qz267 0 1 ep567 ep100 ep567 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 507820761) qz268 0 1 ep567 ep101 ep567 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz595 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17634369) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep569 := @Enclosure.Real.IsNear.cos_image qz343 qz595 Bool.false 17634369 65536 189 262144 Bool.false 238818 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz343 Bool.false 2423649227253276021 9007199254740992 465475000240762289 646550000000000000000 17634369 65536 189 262144 (ep566 rfl) rfl) (Enclosure.sfrac_false_div 17634369 65536) (BSN.cos_reduce3 qz595 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4466838659769500172288) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 238818 524288 42 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 17634369 65536 226375608064910080 72057594037927936 42 4466838659769500172288 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 238818 524288 4466838659769500172288 9444732965739290427392 507820761 1073741824 258873 258620 (ep568 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep570 := BSN.cos_dyadic_bound_f 507820761 1073741824 2 1 524288 258873 ep567 ep90 ep567 ep567 ep91 ep567 466737 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 507820761) qz273 0 1 ep567 ep90 ep567 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 507820761) qz274 0 1 ep567 ep91 ep567 rfl rfl rfl rfl) rfl rfl

noncomputable def ep571 := @Enclosure.Real.IsNear.sin_image qz343 qz595 Bool.false 17634369 65536 189 262144 Bool.true 466737 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz343 Bool.false 2423649227253276021 9007199254740992 465475000240762289 646550000000000000000 17634369 65536 189 262144 (ep566 rfl) rfl) (Enclosure.sfrac_false_div 17634369 65536) (BSN.sin_reduce3 qz595 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4466838659769500172288) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 466737 524288 42 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 17634369 65536 226375608064910080 72057594037927936 42 4466838659769500172288 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 466737 524288 4466838659769500172288 9444732965739290427392 507820761 1073741824 258873 258620 (ep570 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz596 := (@Enclosure.Real.IsNear.recentre' qz342 Bool.false 123575 524288 1 524288 123575 524288 1 524288 (ep564 rfl rfl) rfl)

noncomputable def ep572 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz342 (Real.cos qz343)) (@HMul.hMul Real Real Real qz0 qz342 (@Neg.neg Real Real.instNeg (Real.sin qz343))) Bool.false 14755967175 137438953472 1533991129287 8886115536732160 Bool.false 57677024775 274877906944 3082718361519 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ff qz342 (Real.cos qz343) 123575 524288 1 524288 119409 262144 12350867 16948920320 14755967175 137438953472 1533991129287 8886115536732160 qz596 (@Enclosure.Real.IsNear.recentre' (Real.cos qz343) Bool.false 238818 524288 24701734 33897840640 119409 262144 12350867 16948920320 (ep569 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz342 (@Neg.neg Real Real.instNeg (Real.sin qz343)) 123575 524288 1 524288 466737 524288 12350867 16948920320 57677024775 274877906944 3082718361519 17772231073464320 qz596 (@Enclosure.Real.IsNear.neg (Real.sin qz343) Bool.true 466737 524288 12350867 16948920320 (@Enclosure.Real.IsNear.recentre' (Real.sin qz343) Bool.true 466737 524288 24701734 33897840640 466737 524288 12350867 16948920320 (ep571 rfl rfl) rfl)) rfl)

noncomputable def ep573 := @ep543 14755967175 137438953472 1533991129287 8886115536732160 Bool.false 57677024775 274877906944 3082718361519 17772231073464320 Bool.false 14112851912211721879552 205369024657 137438953472 20017420471721 4443057768366080 Bool.true 200345052609765179392 1457702111 274877906944 80075786676639 17772231073464320 (ep544 (BSN.head_sum_c_succ qz12 17 18 rfl rfl) (ep562 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep563 ep572) rfl rfl

noncomputable abbrev qz889 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz345 := (@Inv.inv Real Real.instInv (Real.sqrt qz889))

noncomputable abbrev qz346 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_eq qz881 (Complex.mk (@HMul.hMul Real Real Real qz0 qz345 (Real.cos qz346)) (@HMul.hMul Real Real Real qz0 qz345 (@Neg.neg Real Real.instNeg (Real.sin qz346)))) Bool.true 22107159921 137438953472 299489161421 1777223107346432 Bool.false 22481949285 137438953472 299529454417 1777223107346432 (BSN.cpow_neg_s_mk qz9 93095 1000 19 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz890 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz266)

noncomputable def ep575 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz889) 2285319 524288 1 524288 60139 60140 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz889) (Real.sqrt qz890) Bool.false 2285319 524288 1 524288 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz890) Bool.false 2285319 524288 1 524288 2285319 524288 1 524288 (BSN.sqrt_enclosure 19 1 1142659 1142660 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep576 := BSN.log_dyadic_bound 3 35 3 2 22509375 262144 129310 55368 243 45049 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz347 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable def ep577 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz347 93095 1000 0 1 3315141365800183 1125899906842624 25000000012931 3232750000000000000 61724617089833607277 225179981368524800 465475000240762289 646550000000000000000 qz271 (BSN.isNear_log_sfrac 19 1 3315141365800183 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz890) Bool.false 27809421382282341515264 9444732965739290427392 1000000000517240 129310000000000000000 3315141365800183 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 45049 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep576 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep578 := nat_lit 1178858584853733442606212529038343208255252963408804085486361589923376800000

noncomputable def ep579 := nat_lit 278548380723011226153895572013805273724963694786537239749181600100000000

noncomputable def ep580 := nat_lit 3536018657799754305366329795971002014218308962836839181979586406569930400000

noncomputable def ep581 := BSN.cos_dyadic_bound_f 852339430 1073741824 3 2 524288 258873 ep578 ep199 ep579 ep580 ep202 ep579 367598 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 852339430) qz273 0 2 ep578 ep199 ep579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 852339430) qz274 0 2 ep580 ep202 ep579 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz891 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 143713823) qz269)

noncomputable def ep582 := @Enclosure.Real.IsNear.cos_image qz346 qz891 Bool.false 143713823 524288 189 262144 Bool.true 367598 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz346 Bool.false 61724617089833607277 225179981368524800 465475000240762289 646550000000000000000 143713823 524288 189 262144 (ep577 rfl) rfl) (Enclosure.sfrac_false_div 143713823 524288) (BSN.cos_reduce2 qz891 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59978055347671134109696) qz272) 226375608064910080 72057594037927936 Bool.false 367598 524288 43 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 143713823 524288 226375608064910080 72057594037927936 43 59978055347671134109696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 367598 524288 59978055347671134109696 75557863725914323419136 852339430 1073741824 258873 258620 (ep581 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep583 := nat_lit 527776828520361649794825139080010000

noncomputable def ep584 := BSN.sin_dyadic_bound_f 852339430 1073741824 2 1 524288 258873 ep583 ep100 ep583 ep583 ep101 ep583 373830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 852339430) qz267 0 1 ep583 ep100 ep583 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 852339430) qz268 0 1 ep583 ep101 ep583 rfl rfl rfl rfl) rfl rfl

noncomputable def ep585 := @Enclosure.Real.IsNear.sin_image qz346 qz891 Bool.false 143713823 524288 189 262144 Bool.true 373830 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz346 Bool.false 61724617089833607277 225179981368524800 465475000240762289 646550000000000000000 143713823 524288 189 262144 (ep577 rfl) rfl) (Enclosure.sfrac_false_div 143713823 524288) (BSN.sin_reduce2 qz891 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59978055347671134109696) qz272) 226375608064910080 72057594037927936 Bool.false 373830 524288 43 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 143713823 524288 226375608064910080 72057594037927936 43 59978055347671134109696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 373830 524288 59978055347671134109696 75557863725914323419136 852339430 1073741824 258873 258620 (ep584 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz597 := (@Enclosure.Real.IsNear.recentre' qz345 Bool.false 120279 524288 1 524288 120279 524288 1 524288 (ep575 rfl rfl) rfl)

noncomputable def ep586 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz345 (Real.cos qz346)) (@HMul.hMul Real Real Real qz0 qz345 (@Neg.neg Real Real.instNeg (Real.sin qz346))) Bool.true 22107159921 137438953472 299489161421 1777223107346432 Bool.false 22481949285 137438953472 299529454417 1777223107346432 (@Enclosure.Real.IsNear.mulLit_ft qz345 (Real.cos qz346) 120279 524288 1 524288 183799 262144 12350867 16948920320 22107159921 137438953472 299489161421 1777223107346432 qz597 (@Enclosure.Real.IsNear.recentre' (Real.cos qz346) Bool.true 367598 524288 24701734 33897840640 183799 262144 12350867 16948920320 (ep582 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz345 (@Neg.neg Real Real.instNeg (Real.sin qz346)) 120279 524288 1 524288 186915 262144 12350867 16948920320 22481949285 137438953472 299529454417 1777223107346432 qz597 (@Enclosure.Real.IsNear.neg (Real.sin qz346) Bool.true 186915 262144 12350867 16948920320 (@Enclosure.Real.IsNear.recentre' (Real.sin qz346) Bool.true 373830 524288 24701734 33897840640 186915 262144 12350867 16948920320 (ep585 rfl rfl) rfl)) rfl)

noncomputable def ep587 := @ep541 22107159921 137438953472 299489161421 1777223107346432 Bool.false 22481949285 137438953472 299529454417 1777223107346432 Bool.false 25187318900643061563392 5726933273 4294967296 41532286750547 8886115536732160 Bool.false 5979446110872192155648 43506196459 274877906944 83071081220809 17772231073464320 (ep542 (BSN.head_sum_c_succ qz12 18 19 rfl rfl) (ep573 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep574 ep586) rfl rfl

noncomputable abbrev qz892 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz348 := (@Inv.inv Real Real.instInv (Real.sqrt qz892))

noncomputable abbrev qz349 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable def ep588 := @Enclosure.Complex.IsNear.of_eq qz880 (Complex.mk (@HMul.hMul Real Real Real qz0 qz348 (Real.cos qz349)) (@HMul.hMul Real Real Real qz0 qz348 (@Neg.neg Real Real.instNeg (Real.sin qz349)))) Bool.true 46439245435 274877906944 2921543690479 17772231073464320 Bool.true 10066383275 68719476736 729534723381 4443057768366080 (BSN.cpow_neg_s_mk qz9 93095 1000 20 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz893 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz266)

noncomputable def ep589 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz892) 2344687 524288 1 524288 58617 58618 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz892) (Real.sqrt qz893) Bool.false 2344687 524288 1 524288 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz893) Bool.false 2344687 524288 1 524288 2344687 524288 1 524288 (BSN.sqrt_enclosure 20 1 1172343 1172344 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep590 := BSN.log_dyadic_bound 4 36 3 2 25194240 262144 129310 104448 768 58495 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz350 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable def ep591 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz350 93095 1000 0 1 3372891496062199 1125899906842624 25000000012931 3232750000000000000 62799866765182083181 225179981368524800 465475000240762289 646550000000000000000 qz271 (BSN.isNear_log_sfrac 20 1 3372891496062199 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz893) Bool.false 28293864586999331028992 9444732965739290427392 1000000000517240 129310000000000000000 3372891496062199 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 58495 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep590 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep592 := nat_lit 715274855260795192743238727947359121

noncomputable def ep593 := BSN.sin_dyadic_bound_f 919640819 1073741824 2 1 524288 258873 ep592 ep100 ep592 ep592 ep101 ep592 396121 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 919640819) qz267 0 1 ep592 ep100 ep592 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 919640819) qz268 0 1 ep592 ep101 ep592 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz894 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 73108667) qz278)

noncomputable def ep594 := @Enclosure.Real.IsNear.cos_image qz349 qz894 Bool.false 73108667 262144 189 262144 Bool.true 396121 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz349 Bool.false 62799866765182083181 225179981368524800 465475000240762289 646550000000000000000 73108667 262144 189 262144 (ep591 rfl) rfl) (Enclosure.sfrac_false_div 73108667 262144) (BSN.cos_reduce1 qz894 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32356984779619208003584) qz280) 226375608064910080 72057594037927936 Bool.false 396121 524288 44 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 73108667 262144 226375608064910080 72057594037927936 44 32356984779619208003584 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 396121 524288 32356984779619208003584 37778931862957161709568 919640819 1073741824 258873 258620 (ep593 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep595 := nat_lit 1597794066771904691857776773571034086798597184439997354674976932440224421921

noncomputable def ep596 := nat_lit 511618118568351512416248399283846523878543292429100968105247238141892641

noncomputable def ep597 := nat_lit 4792358964078577372548497823914534567348034466735133862088720302844389480481

noncomputable def ep598 := BSN.cos_dyadic_bound_f 919640819 1073741824 3 2 524288 258873 ep595 ep199 ep596 ep597 ep202 ep596 343460 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 919640819) qz273 0 2 ep595 ep199 ep596 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 919640819) qz274 0 2 ep597 ep202 ep596 rfl rfl rfl rfl) rfl rfl

noncomputable def ep599 := @Enclosure.Real.IsNear.sin_image qz349 qz894 Bool.false 73108667 262144 189 262144 Bool.false 343460 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz349 Bool.false 62799866765182083181 225179981368524800 465475000240762289 646550000000000000000 73108667 262144 189 262144 (ep591 rfl) rfl) (Enclosure.sfrac_false_div 73108667 262144) (BSN.sin_reduce1 qz894 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32356984779619208003584) qz280) 226375608064910080 72057594037927936 Bool.false 343460 524288 44 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 73108667 262144 226375608064910080 72057594037927936 44 32356984779619208003584 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 343460 524288 32356984779619208003584 37778931862957161709568 919640819 1073741824 258873 258620 (ep598 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz598 := (@Enclosure.Real.IsNear.recentre' qz348 Bool.false 117235 524288 1 524288 117235 524288 1 524288 (ep589 rfl rfl) rfl)

noncomputable def ep600 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz348 (Real.cos qz349)) (@HMul.hMul Real Real Real qz0 qz348 (@Neg.neg Real Real.instNeg (Real.sin qz349))) Bool.true 46439245435 274877906944 2921543690479 17772231073464320 Bool.true 10066383275 68719476736 729534723381 4443057768366080 (@Enclosure.Real.IsNear.mulLit_ft qz348 (Real.cos qz349) 117235 524288 1 524288 396121 524288 12350867 16948920320 46439245435 274877906944 2921543690479 17772231073464320 qz598 (@Enclosure.Real.IsNear.recentre' (Real.cos qz349) Bool.true 396121 524288 24701734 33897840640 396121 524288 12350867 16948920320 (ep594 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz348 (@Neg.neg Real Real.instNeg (Real.sin qz349)) 117235 524288 1 524288 85865 131072 12350867 16948920320 10066383275 68719476736 729534723381 4443057768366080 qz598 (@Enclosure.Real.IsNear.neg (Real.sin qz349) Bool.false 85865 131072 12350867 16948920320 (@Enclosure.Real.IsNear.recentre' (Real.sin qz349) Bool.false 343460 524288 24701734 33897840640 85865 131072 12350867 16948920320 (ep599 rfl rfl) rfl)) rfl)

noncomputable def ep601 := @ep539 46439245435 274877906944 2921543690479 17772231073464320 Bool.true 10066383275 68719476736 729534723381 4443057768366080 Bool.false 1374752390895949053952 320084484037 274877906944 85986117191573 17772231073464320 Bool.false 222696690308008116224 3240663359 274877906944 85989220114333 17772231073464320 (ep540 (BSN.head_sum_c_succ qz12 19 20 rfl rfl) (ep587 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep588 ep600) rfl rfl

noncomputable abbrev qz895 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz351 := (@Inv.inv Real Real.instInv (Real.sqrt qz895))

noncomputable abbrev qz352 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 21 1)))

noncomputable def ep602 := @Enclosure.Complex.IsNear.of_eq qz879 (Complex.mk (@HMul.hMul Real Real Real qz0 qz351 (Real.cos qz352)) (@HMul.hMul Real Real Real qz0 qz351 (@Neg.neg Real Real.instNeg (Real.sin qz352)))) Bool.false 46406692989 274877906944 570470162539 3554446214692864 Bool.true 9501324223 68719476736 17797518763 111076444209152 (BSN.cpow_neg_s_mk qz9 93095 1000 21 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz896 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz266)

noncomputable def ep603 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz895) 2402589 524288 1 524288 57204 57205 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz895) (Real.sqrt qz896) Bool.false 2402589 524288 1 524288 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz896) Bool.false 2402589 524288 1 524288 2402589 524288 1 524288 (BSN.sqrt_enclosure 21 1 1201294 1201295 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep604 := BSN.log_dyadic_bound 5 37 3 2 28112415 262144 129310 173000 1875 71285 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 37) 0 2 173000 28112415 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz353 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable def ep605 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz353 93095 1000 0 1 3427824127778039 1125899906842624 25000000012931 3232750000000000000 63822657435099308141 225179981368524800 465475000240762289 646550000000000000000 qz271 (BSN.isNear_log_sfrac 21 1 3427824127778039 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz896) Bool.false 28754672900871880179712 9444732965739290427392 1000000000517240 129310000000000000000 3427824127778039 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 71285 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep604 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep606 := nat_lit 658200951120837023439572938583125101694683475162410650600991592598732800000

noncomputable def ep607 := nat_lit 86853008366254777630229955473066122231527194722368823431371161600000000

noncomputable def ep608 := nat_lit 1974429147345778560763458355838429172839587371097787214156112035472998400000

noncomputable def ep609 := BSN.cos_dyadic_bound_f 736797440 1073741824 3 2 524288 258873 ep606 ep199 ep607 ep608 ep202 ep607 405621 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 736797440) qz273 0 2 ep606 ep199 ep607 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 736797440) qz274 0 2 ep608 ep202 ep607 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz599 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9287419) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep610 := @Enclosure.Real.IsNear.cos_image qz352 qz599 Bool.false 9287419 32768 189 262144 Bool.false 405621 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz352 Bool.false 63822657435099308141 225179981368524800 465475000240762289 646550000000000000000 9287419 32768 189 262144 (ep605 rfl) rfl) (Enclosure.sfrac_false_div 9287419 32768) (BSN.cos_reduce0 qz599 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3240469411502036615168) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 405621 524288 45 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 9287419 32768 226375608064910080 72057594037927936 45 3240469411502036615168 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 405621 524288 3240469411502036615168 4722366482869645213696 736797440 1073741824 258873 258620 (ep609 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep611 := nat_lit 294708344581986306589815954472960000

noncomputable def ep612 := BSN.sin_dyadic_bound_f 736797440 1073741824 2 1 524288 258873 ep611 ep100 ep611 ep611 ep101 ep611 332188 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 736797440) qz267 0 1 ep611 ep100 ep611 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 736797440) qz268 0 1 ep611 ep101 ep611 rfl rfl rfl rfl) rfl rfl

noncomputable def ep613 := @Enclosure.Real.IsNear.sin_image qz352 qz599 Bool.false 9287419 32768 189 262144 Bool.false 332188 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz352 Bool.false 63822657435099308141 225179981368524800 465475000240762289 646550000000000000000 9287419 32768 189 262144 (ep605 rfl) rfl) (Enclosure.sfrac_false_div 9287419 32768) (BSN.sin_reduce0 qz599 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3240469411502036615168) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 332188 524288 45 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 9287419 32768 226375608064910080 72057594037927936 45 3240469411502036615168 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 332188 524288 3240469411502036615168 4722366482869645213696 736797440 1073741824 258873 258620 (ep612 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz600 := (@Enclosure.Real.IsNear.recentre' qz351 Bool.false 114409 524288 1 524288 114409 524288 1 524288 (ep603 rfl rfl) rfl)

noncomputable def ep614 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz351 (Real.cos qz352)) (@HMul.hMul Real Real Real qz0 qz351 (@Neg.neg Real Real.instNeg (Real.sin qz352))) Bool.false 46406692989 274877906944 570470162539 3554446214692864 Bool.true 9501324223 68719476736 17797518763 111076444209152 (@Enclosure.Real.IsNear.mulLit_ff qz351 (Real.cos qz352) 114409 524288 1 524288 405621 524288 12350867 16948920320 46406692989 274877906944 570470162539 3554446214692864 qz600 (@Enclosure.Real.IsNear.recentre' (Real.cos qz352) Bool.false 405621 524288 24701734 33897840640 405621 524288 12350867 16948920320 (ep610 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz351 (@Neg.neg Real Real.instNeg (Real.sin qz352)) 114409 524288 1 524288 83047 131072 12350867 16948920320 9501324223 68719476736 17797518763 111076444209152 qz600 (@Enclosure.Real.IsNear.neg (Real.sin qz352) Bool.false 83047 131072 12350867 16948920320 (@Enclosure.Real.IsNear.recentre' (Real.sin qz352) Bool.false 332188 524288 24701734 33897840640 83047 131072 12350867 16948920320 (ep613 rfl rfl) rfl)) rfl)

noncomputable def ep615 := @ep537 46406692989 274877906944 570470162539 3554446214692864 Bool.true 9501324223 68719476736 17797518763 111076444209152 Bool.false 100740327654349858668544 183245588513 137438953472 22209617001067 4443057768366080 Bool.true 2389007425306558988288 34764633533 274877906944 88836823116413 17772231073464320 (ep538 (BSN.head_sum_c_succ qz12 20 21 rfl rfl) (ep601 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep602 ep614) rfl rfl

noncomputable abbrev qz897 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz354 := (@Inv.inv Real Real.instInv (Real.sqrt qz897))

noncomputable abbrev qz355 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 22 1)))

noncomputable def ep616 := @Enclosure.Complex.IsNear.of_eq qz878 (Complex.mk (@HMul.hMul Real Real Real qz0 qz354 (Real.cos qz355)) (@HMul.hMul Real Real Real qz0 qz354 (@Neg.neg Real Real.instNeg (Real.sin qz355)))) Bool.false 4394144269 68719476736 138566321867 888611553673216 Bool.false 6988311301 34359738368 17459357213 111076444209152 (BSN.cpow_neg_s_mk qz9 93095 1000 22 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz898 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz266)

noncomputable def ep617 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz897) 2459129 524288 1 524288 55889 55890 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz897) (Real.sqrt qz898) Bool.false 2459129 524288 1 524288 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz898) Bool.false 2459129 524288 1 524288 2459129 524288 1 524288 (BSN.sqrt_enclosure 22 1 1229564 1229565 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep618 := BSN.log_dyadic_bound 6 38 4 3 316148320320 262144 129310 2667271104 699840 83480 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz356 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable def ep619 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz356 93095 1000 0 1 3480201253952759 1125899906842624 25000000012931 3232750000000000000 64797867147346419821 225179981368524800 465475000240762289 646550000000000000000 qz271 (BSN.isNear_log_sfrac 22 1 3480201253952759 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz898) Bool.false 29194044080518145769472 9444732965739290427392 1000000000517240 129310000000000000000 3480201253952759 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 83480 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep618 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep620 := nat_lit 11443671362114755286634496706685841

noncomputable def ep621 := BSN.sin_dyadic_bound_f 327070477 1073741824 2 1 524288 258873 ep620 ep100 ep620 ep620 ep101 ep620 157244 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 327070477) qz267 0 1 ep620 ep100 ep620 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 327070477) qz268 0 1 ep620 ep101 ep620 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz899 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 150869291) qz269)

noncomputable def ep622 := @Enclosure.Real.IsNear.cos_image qz355 qz899 Bool.false 150869291 524288 189 262144 Bool.false 157244 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz355 Bool.false 64797867147346419821 225179981368524800 465475000240762289 646550000000000000000 150869291 524288 189 262144 (ep619 rfl) rfl) (Enclosure.sfrac_false_div 150869291 524288) (BSN.cos_reduce3 qz899 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23015538728219214610432) qz272) 226375608064910080 72057594037927936 Bool.false 157244 524288 45 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 150869291 524288 226375608064910080 72057594037927936 45 23015538728219214610432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 157244 524288 23015538728219214610432 75557863725914323419136 327070477 1073741824 258873 258620 (ep621 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep623 := BSN.cos_dyadic_bound_f 327070477 1073741824 2 1 524288 258873 ep620 ep90 ep620 ep620 ep91 ep620 500152 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 327070477) qz273 0 1 ep620 ep90 ep620 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 327070477) qz274 0 1 ep620 ep91 ep620 rfl rfl rfl rfl) rfl rfl

noncomputable def ep624 := @Enclosure.Real.IsNear.sin_image qz355 qz899 Bool.false 150869291 524288 189 262144 Bool.true 500152 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz355 Bool.false 64797867147346419821 225179981368524800 465475000240762289 646550000000000000000 150869291 524288 189 262144 (ep619 rfl) rfl) (Enclosure.sfrac_false_div 150869291 524288) (BSN.sin_reduce3 qz899 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23015538728219214610432) qz272) 226375608064910080 72057594037927936 Bool.false 500152 524288 45 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 150869291 524288 226375608064910080 72057594037927936 45 23015538728219214610432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 500152 524288 23015538728219214610432 75557863725914323419136 327070477 1073741824 258873 258620 (ep623 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz601 := (@Enclosure.Real.IsNear.recentre' qz354 Bool.false 111779 524288 1 524288 111779 524288 1 524288 (ep617 rfl rfl) rfl)

noncomputable def ep625 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz354 (Real.cos qz355)) (@HMul.hMul Real Real Real qz0 qz354 (@Neg.neg Real Real.instNeg (Real.sin qz355))) Bool.false 4394144269 68719476736 138566321867 888611553673216 Bool.false 6988311301 34359738368 17459357213 111076444209152 (@Enclosure.Real.IsNear.mulLit_ff qz354 (Real.cos qz355) 111779 524288 1 524288 39311 131072 12350867 16948920320 4394144269 68719476736 138566321867 888611553673216 qz601 (@Enclosure.Real.IsNear.recentre' (Real.cos qz355) Bool.false 157244 524288 24701734 33897840640 39311 131072 12350867 16948920320 (ep622 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz354 (@Neg.neg Real Real.instNeg (Real.sin qz355)) 111779 524288 1 524288 62519 65536 12350867 16948920320 6988311301 34359738368 17459357213 111076444209152 qz601 (@Enclosure.Real.IsNear.neg (Real.sin qz355) Bool.true 62519 65536 12350867 16948920320 (@Enclosure.Real.IsNear.recentre' (Real.sin qz355) Bool.true 500152 524288 24701734 33897840640 62519 65536 12350867 16948920320 (ep624 rfl rfl) rfl)) rfl)

noncomputable def ep626 := @ep535 4394144269 68719476736 138566321867 888611553673216 Bool.false 6988311301 34359738368 17459357213 111076444209152 Bool.false 13196467546530078785536 192033877051 137438953472 11451224305201 2221528884183040 Bool.false 726428670838702080000 21141856875 274877906944 91630320270493 17772231073464320 (ep536 (BSN.head_sum_c_succ qz12 21 22 rfl rfl) (ep615 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep616 ep625) rfl rfl

noncomputable abbrev qz900 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz357 := (@Inv.inv Real Real.instInv (Real.sqrt qz900))

noncomputable abbrev qz358 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable def ep627 := @Enclosure.Complex.IsNear.of_eq qz877 (Complex.mk (@HMul.hMul Real Real Real qz0 qz357 (Real.cos qz358)) (@HMul.hMul Real Real Real qz0 qz357 (@Neg.neg Real Real.instNeg (Real.sin qz358)))) Bool.true 6905916891 34359738368 683279383097 4443057768366080 Bool.true 15258041291 274877906944 2709466927353 17772231073464320 (BSN.cpow_neg_s_mk qz9 93095 1000 23 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz901 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz266)

noncomputable def ep628 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz900) 2514397 524288 1 524288 54660 54661 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz900) (Real.sqrt qz901) Bool.false 2514397 524288 1 524288 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz901) Bool.false 2514397 524288 1 524288 2514397 524288 1 524288 (BSN.sqrt_enclosure 23 1 1257198 1257199 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep629 := BSN.log_dyadic_bound 7 39 4 3 369468094905 262144 129310 4046006391 1764735 95133 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz359 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable def ep630 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz359 93095 1000 0 1 3530250507853047 1125899906842624 25000000012931 3232750000000000000 65729734205715882093 225179981368524800 465475000240762289 646550000000000000000 qz271 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz901) Bool.false 29613887652180132888576 9444732965739290427392 1000000000517240 129310000000000000000 3530250507853047 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 95133 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep629 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep631 := nat_lit 15337363668024138709829008143731982708083915941906216361433051006203050942720

noncomputable def ep632 := nat_lit 14531670666424741081589795408884656956626683579651573037005166312768758016

noncomputable def ep633 := nat_lit 40145758330412818468753399755302712886099527122053987923598077604120650670336

noncomputable def ep634 := BSN.sin_dyadic_bound_f 1397299306 1073741824 3 2 524288 258873 ep631 ep551 ep632 ep633 ep554 ep632 505368 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1397299306) qz267 0 2 ep631 ep551 ep632 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1397299306) qz268 0 2 ep633 ep554 ep632 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz902 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153038963) qz269)

noncomputable def ep635 := @Enclosure.Real.IsNear.cos_image qz358 qz902 Bool.false 153038963 524288 189 262144 Bool.true 505368 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz358 Bool.false 65729734205715882093 225179981368524800 465475000240762289 646550000000000000000 153038963 524288 189 262144 (ep630 rfl) rfl) (Enclosure.sfrac_false_div 153038963 524288) (BSN.cos_reduce1 qz902 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 98326197468866424078336) qz272) 226375608064910080 72057594037927936 Bool.false 505368 524288 46 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 153038963 524288 226375608064910080 72057594037927936 46 98326197468866424078336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 505368 524288 98326197468866424078336 75557863725914323419136 1397299306 1073741824 258873 258620 (ep634 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep636 := nat_lit 8527216113642932501496822211143939129805120715983298677701475077362925527296

noncomputable def ep637 := nat_lit 25552584999595948022327287042614048075502108780790592887030414899463239065856

noncomputable def ep638 := BSN.cos_dyadic_bound_f 1397299306 1073741824 3 2 524288 258873 ep636 ep199 ep632 ep637 ep202 ep632 139571 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1397299306) qz273 0 2 ep636 ep199 ep632 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1397299306) qz274 0 2 ep637 ep202 ep632 rfl rfl rfl rfl) rfl rfl

noncomputable def ep639 := @Enclosure.Real.IsNear.sin_image qz358 qz902 Bool.false 153038963 524288 189 262144 Bool.false 139571 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz358 Bool.false 65729734205715882093 225179981368524800 465475000240762289 646550000000000000000 153038963 524288 189 262144 (ep630 rfl) rfl) (Enclosure.sfrac_false_div 153038963 524288) (BSN.sin_reduce1 qz902 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 98326197468866424078336) qz272) 226375608064910080 72057594037927936 Bool.false 139571 524288 46 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 153038963 524288 226375608064910080 72057594037927936 46 98326197468866424078336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 139571 524288 98326197468866424078336 75557863725914323419136 1397299306 1073741824 258873 258620 (ep638 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz602 := (@Enclosure.Real.IsNear.recentre' qz357 Bool.false 109321 524288 1 524288 109321 524288 1 524288 (ep628 rfl rfl) rfl)

noncomputable def ep640 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz357 (Real.cos qz358)) (@HMul.hMul Real Real Real qz0 qz357 (@Neg.neg Real Real.instNeg (Real.sin qz358))) Bool.true 6905916891 34359738368 683279383097 4443057768366080 Bool.true 15258041291 274877906944 2709466927353 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ft qz357 (Real.cos qz358) 109321 524288 1 524288 63171 65536 12350867 16948920320 6905916891 34359738368 683279383097 4443057768366080 qz602 (@Enclosure.Real.IsNear.recentre' (Real.cos qz358) Bool.true 505368 524288 24701734 33897840640 63171 65536 12350867 16948920320 (ep635 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz357 (@Neg.neg Real Real.instNeg (Real.sin qz358)) 109321 524288 1 524288 139571 524288 12350867 16948920320 15258041291 274877906944 2709466927353 17772231073464320 qz602 (@Enclosure.Real.IsNear.neg (Real.sin qz358) Bool.false 139571 524288 12350867 16948920320 (@Enclosure.Real.IsNear.recentre' (Real.sin qz358) Bool.false 139571 524288 24701734 33897840640 139571 524288 12350867 16948920320 (ep639 rfl rfl) rfl)) rfl)

noncomputable def ep641 := @ep533 6905916891 34359738368 683279383097 4443057768366080 Bool.true 15258041291 274877906944 2709466927353 17772231073464320 Bool.false 5649091783001391497216 164410209487 137438953472 23585727993499 4443057768366080 Bool.false 1617330912574409015296 183869237 8589934592 47169893598923 8886115536732160 (ep534 (BSN.head_sum_c_succ qz12 22 23 rfl rfl) (ep626 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep627 ep640) rfl rfl

noncomputable def ep642 := @Enclosure.Complex.IsNear.mul qz43 (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false ep524 ep332 ep525 ep334 Bool.true

noncomputable def ep643 := nat_lit 246443571319536582826387565947

noncomputable def ep644 := nat_lit 2810331239575430607195340800000

noncomputable def ep645 := nat_lit 1653380080246378578989627719373

noncomputable def ep646 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re qz43) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz43) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) ep643 ep644 ep645

noncomputable def ep647 := nat_lit 21804235955369935908985771130880000

noncomputable def ep648 := nat_lit 13198561169560883813700570955069

noncomputable def ep649 := nat_lit 2151937867500886436638704847659493

noncomputable def ep650 := nat_lit 244868748953812968843226567929132436076800509309044863795200000

noncomputable def ep651 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz43) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 47800999521 274877906944 534491662065 3554446214692864 46400538986667379763

noncomputable abbrev qz360 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 24)))

noncomputable abbrev qz361 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable abbrev qz903 := (@Neg.neg Real Real.instNeg (Real.sin qz361))

noncomputable def ep652 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz360 (Real.cos qz361)) (@HMul.hMul Real Real Real qz0 qz360 qz903)) Bool.false 47800999521 274877906944 534491662065 3554446214692864 Bool.true 29381103279 274877906944 532266004207 3554446214692864 (BSN.cpow_neg_s_mk qz9 93095 1000 24 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz603 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz266)

noncomputable def ep653 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 24)) 2568477 524288 1 524288 53509 53510 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 24)) (Real.sqrt qz603) Bool.false 2568477 524288 1 524288 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz603) Bool.false 2568477 524288 1 524288 2568477 524288 1 524288 (BSN.sqrt_enclosure 24 1 1284238 1284239 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep654 := BSN.log_dyadic_bound 8 40 4 3 430080000000 262144 129310 5875957760 3932160 106290 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz362 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable def ep655 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz362 93095 1000 0 1 3578169457974519 1125899906842624 25000000012931 3232750000000000000 66621937138027569261 225179981368524800 465475000240762289 646550000000000000000 qz271 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz603) Bool.false 30015860940520713879552 9444732965739290427392 1000000000517240 129310000000000000000 3578169457974519 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 106290 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep654 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep656 := nat_lit 122630621597064040976990879745140641

noncomputable def ep657 := BSN.cos_dyadic_bound_f 591765623 1073741824 2 1 524288 258873 ep656 ep90 ep656 ep656 ep91 ep656 446659 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 591765623) qz273 0 1 ep656 ep90 ep656 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 591765623) qz274 0 1 ep656 ep91 ep656 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz904 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 155116285) qz269)

noncomputable def ep658 := @Enclosure.Real.IsNear.cos_image qz361 qz904 Bool.false 155116285 524288 189 262144 Bool.false 446659 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz361 Bool.false 66621937138027569261 225179981368524800 465475000240762289 646550000000000000000 155116285 524288 189 262144 (ep655 rfl) rfl) (Enclosure.sfrac_false_div 155116285 524288) (BSN.cos_reduce0 qz904 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41641803789572767744000) qz272) 226375608064910080 72057594037927936 Bool.false 446659 524288 47 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 155116285 524288 226375608064910080 72057594037927936 47 41641803789572767744000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 446659 524288 41641803789572767744000 75557863725914323419136 591765623 1073741824 258873 258620 (ep657 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep659 := BSN.sin_dyadic_bound_f 591765623 1073741824 2 1 524288 258873 ep656 ep100 ep656 ep656 ep101 ep656 274541 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 591765623) qz267 0 1 ep656 ep100 ep656 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 591765623) qz268 0 1 ep656 ep101 ep656 rfl rfl rfl rfl) rfl rfl

noncomputable def ep660 := @Enclosure.Real.IsNear.sin_image qz361 qz904 Bool.false 155116285 524288 189 262144 Bool.false 274541 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz361 Bool.false 66621937138027569261 225179981368524800 465475000240762289 646550000000000000000 155116285 524288 189 262144 (ep655 rfl) rfl) (Enclosure.sfrac_false_div 155116285 524288) (BSN.sin_reduce0 qz904 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41641803789572767744000) qz272) 226375608064910080 72057594037927936 Bool.false 274541 524288 47 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 155116285 524288 226375608064910080 72057594037927936 47 41641803789572767744000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 274541 524288 41641803789572767744000 75557863725914323419136 591765623 1073741824 258873 258620 (ep659 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz604 := (@Enclosure.Real.IsNear.recentre' qz360 Bool.false 107019 524288 1 524288 107019 524288 1 524288 (ep653 rfl rfl) rfl)

noncomputable def ep661 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz360 (Real.cos qz361)) (@HMul.hMul Real Real Real qz0 qz360 qz903) Bool.false 47800999521 274877906944 534491662065 3554446214692864 Bool.true 29381103279 274877906944 532266004207 3554446214692864 (@Enclosure.Real.IsNear.mulLit_ff qz360 (Real.cos qz361) 107019 524288 1 524288 446659 524288 12350867 16948920320 47800999521 274877906944 534491662065 3554446214692864 qz604 (@Enclosure.Real.IsNear.recentre' (Real.cos qz361) Bool.false 446659 524288 24701734 33897840640 446659 524288 12350867 16948920320 (ep658 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz360 qz903 107019 524288 1 524288 274541 524288 12350867 16948920320 29381103279 274877906944 532266004207 3554446214692864 qz604 (@Enclosure.Real.IsNear.neg (Real.sin qz361) Bool.false 274541 524288 12350867 16948920320 (@Enclosure.Real.IsNear.recentre' (Real.sin qz361) Bool.false 274541 524288 24701734 33897840640 274541 524288 12350867 16948920320 (ep660 rfl rfl) rfl)) rfl)

noncomputable def ep662 := @ep651 92015329414348800000 0 1 ep643 ep644 ep645 ep647 (@Enclosure.Complex.IsNear.re_isNear qz43 Bool.false 47800999521 274877906944 534491662065 3554446214692864 Bool.true 29381103279 274877906944 532266004207 3554446214692864 (ep652 ep661))

noncomputable def ep663 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false 46400538986667379763 92015329414348800000 0 1 Bool.false

noncomputable def ep664 := @Enclosure.Complex.IsNear.addLitP qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) Bool.false 345717161 693354322 0 1 Bool.true 89371200

noncomputable def ep665 := @ep664 346677161 0 1 Bool.false 1500751483 265420800000 0 1 Bool.false 32189219100659 79626240000000 0 1 Bool.false 92801077973334759526 46400538986667379763 92015329414348800000 0 1 Bool.false 4042974472335435349099 4042974472335435349099 27604598824304640000000 0 1

noncomputable abbrev qz48 := (@HDiv.hDiv Complex Complex Complex qz329 qz593 (@HSub.hSub Complex Complex Complex qz577 qz260 (1 : Complex)))

noncomputable def ep666 := @Enclosure.Complex.IsNear.addLitP qz48 qz24 Bool.true 48000000 34667716100 0 1 Bool.true 8937120000 34667716100 0 1

noncomputable def ep667 := @Enclosure.Complex.IsNear.of_eq qz48 (Complex.mk (Enclosure.sfrac Bool.true 48000000 34667716100) (Enclosure.sfrac Bool.true 8937120000 34667716100)) Bool.true 48000000 34667716100 0 1 Bool.true 8937120000 34667716100 0 1

noncomputable def ep668 := @ep666 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 34571716100 345717161 693354322 0 1 Bool.true 8937120000 89371200 346677161 0 1 (ep667 (BSN.N_div_s_sub_one_mk qz9 93095 1000 24 (@Eq.refl Real qz9) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 48000000 34667716100) (Enclosure.sfrac Bool.true 8937120000 34667716100) Bool.true 48000000 34667716100 0 1 Bool.true 8937120000 34667716100 0 1 (Enclosure.Real.IsNear.const Bool.true 48000000 34667716100) (Enclosure.Real.IsNear.const Bool.true 8937120000 34667716100))) qz334 rfl

noncomputable abbrev qz49 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz865 2 2)))

noncomputable abbrev qz50 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz254 qz593 3))

noncomputable def ep669 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz50)) Bool.false 1500751483 265420800000 0 1

noncomputable def ep670 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz50) Bool.false 1 576 0 1 Bool.false

noncomputable def ep671 := @ep670 18619 57600 0 1 Bool.false 1039951483 265420800000 0 1 Bool.false 6450313500659 79626240000000 0 1 Bool.false 864432854208 1500751483 265420800000 0 1 Bool.false 1854099020197958400 32189219100659 79626240000000 0

noncomputable abbrev qz51 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz865 2 1)))

noncomputable abbrev qz52 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz254 qz593 1))

noncomputable def ep672 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz52)) Bool.false 1 576 0 1

noncomputable def ep673 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz52) Bool.false 0 1 0 1 Bool.false

noncomputable def ep674 := @ep673 0 1 0 1 Bool.false 1 576 0 1 Bool.false 18619 57600 0 1 Bool.false 1 1 576 0 1 Bool.false 18619 18619 57600 0

noncomputable def ep675 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (Complex.mk qz263 qz263) Bool.false 0 1 0 1 Bool.false

noncomputable def ep676 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz52 Bool.false 1 576 0 1 Bool.false 18619 57600 0 1

noncomputable def ep677 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52)) 1 576 0 1 0 1 0

noncomputable def ep678 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52) 1 24 0 1 1 24 0 1 1

noncomputable def ep679 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep680 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep681 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz263) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow27.d9 rfl) qz586

noncomputable def ep682 := @ep680 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep681) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep285)

noncomputable def ep683 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 93095 1000 0 1 0 1 0

noncomputable def ep684 := @ep683 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep681) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep285)

noncomputable def ep685 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) 18619 2400 0 1 0 1 0 1 18619

noncomputable def ep686 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 93095 1000 0 1 18619 2400 0

noncomputable def ep687 := @ep686 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep681) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep285)

noncomputable def ep688 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep689 := @ep688 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep681) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 93095 1000 0 1 ep285)

noncomputable def ep690 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 18619 2400 0 1 (@ep679 1 24 0 1 (ep682 rfl) (ep684 rfl) rfl rfl) (@ep685 18619 2400 0 1 (ep687 rfl) (ep689 rfl) rfl rfl)

noncomputable def ep691 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 18619 2400 0 1 ep690

noncomputable abbrev qz53 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz254 qz593 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 24) qz263) Bool.false 1 24 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 24 1 24 EMRow27.d10 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 24) qz263 Bool.false 1 24 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 24) qz275))

noncomputable abbrev qz905 := (@Enclosure.Complex.IsNear.re_isNear qz52 Bool.false 1 24 0 1 Bool.false 0 1 0 1 qz53)

noncomputable def ep692 := @ep678 576 0 1 ep691 qz905

noncomputable def ep693 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52) 18619 2400 0 1 0 1 0 1 0

noncomputable def ep694 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 18619 2400 0 1 ep690

noncomputable abbrev qz906 := (@Enclosure.Complex.IsNear.im_isNear qz52 Bool.false 1 24 0 1 Bool.false 0 1 0 1 qz53)

noncomputable def ep695 := @ep693 1 0 1 ep694 qz906

noncomputable def ep696 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52)) 0 1 0 1 18619 57600 0

noncomputable def ep697 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52) 1 24 0 1 0 1 0 1 0

noncomputable def ep698 := @ep697 1 0 1 ep691 qz906

noncomputable def ep699 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52) 18619 2400 0 1 1 24 0 1 18619

noncomputable def ep700 := @ep699 57600 0 1 ep694 qz905

noncomputable def ep701 := @ep674 1 (@ep675 0 1 0 1 (BSN.bern_sum_base qz12 24) qz338) (ep676 (@ep677 1 1 1 576 0 1 (ep692 rfl) (ep695 rfl) rfl rfl) (@ep696 1 18619 18619 57600 0 1 (ep698 rfl) (ep700 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep702 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz50 Bool.false 1039951483 265420800000 0 1 Bool.false 6450313500659 79626240000000 0 1

noncomputable def ep703 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50)) 1039951483 265420800000 0 1 0 1 0

noncomputable def ep704 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50) 1039951483 19200000 0 1 1 13824 0 1 1039951483

noncomputable def ep705 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) 1039951483 19200000 0 1 0 1 0 1 1039951483

noncomputable def ep706 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3119854449 80000 0 1 1039951483 19200000 0

noncomputable def ep707 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz263) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow27.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz263 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz275)

noncomputable def ep708 := @ep706 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep707) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 EMRow27.d12)

noncomputable def ep709 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 6450313500659 8000000 0 1 0 1 0

noncomputable def ep710 := @ep709 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep707) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 EMRow27.d12)

noncomputable def ep711 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) 6450313500659 5760000000 0 1 0 1 0 1 6450313500659

noncomputable def ep712 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 6450313500659 8000000 0 1 6450313500659 5760000000 0

noncomputable def ep713 := @ep712 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep707) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 EMRow27.d12)

noncomputable def ep714 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3119854449 80000 0 1 0 1 0

noncomputable def ep715 := @ep714 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep707) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 EMRow27.d12)

noncomputable def ep716 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1039951483 19200000 0 1 Bool.false 6450313500659 5760000000 0 1 (@ep705 1039951483 19200000 0 1 (ep708 rfl) (ep710 rfl) rfl rfl) (@ep711 6450313500659 5760000000 0 1 (ep713 rfl) (ep715 rfl) rfl rfl)

noncomputable def ep717 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1039951483 19200000 0 1 Bool.false 6450313500659 5760000000 0 1 ep716

noncomputable abbrev qz54 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz254 qz593 3)) (Complex.mk (Enclosure.sfrac Bool.false 1 13824) qz263) Bool.false 1 13824 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 24 3 13824 EMRow27.d13 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 13824) qz263 Bool.false 1 13824 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 13824) qz275))

noncomputable abbrev qz907 := (@Enclosure.Complex.IsNear.re_isNear qz50 Bool.false 1 13824 0 1 Bool.false 0 1 0 1 qz54)

noncomputable def ep718 := @ep704 265420800000 0 1 ep717 qz907

noncomputable def ep719 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50) 6450313500659 5760000000 0 1 0 1 0 1 0

noncomputable def ep720 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1039951483 19200000 0 1 Bool.false 6450313500659 5760000000 0 1 ep716

noncomputable abbrev qz908 := (@Enclosure.Complex.IsNear.im_isNear qz50 Bool.false 1 13824 0 1 Bool.false 0 1 0 1 qz54)

noncomputable def ep721 := @ep719 1 0 1 ep720 qz908

noncomputable def ep722 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50)) 0 1 0 1 6450313500659 79626240000000 0

noncomputable def ep723 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50) 1039951483 19200000 0 1 0 1 0 1 0

noncomputable def ep724 := @ep723 1 0 1 ep717 qz908

noncomputable def ep725 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50) 6450313500659 5760000000 0 1 1 13824 0 1 6450313500659

noncomputable def ep726 := @ep725 79626240000000 0 1 ep720 qz907

noncomputable def ep727 := @ep671 1 (@ep672 Bool.false 18619 57600 0 1 (BSN.bern_sum_succ qz12 24 0 1 1 rfl rfl) (ep701 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep702 (@ep703 1 1039951483 1039951483 265420800000 0 1 (ep718 rfl) (ep721 rfl) rfl rfl) (@ep722 1 6450313500659 6450313500659 79626240000000 0 1 (ep724 rfl) (ep726 rfl) rfl rfl)) rfl rfl rfl rfl

noncomputable def ep728 := ep665 (ep668 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep669 Bool.false 32189219100659 79626240000000 0 1 (BSN.bern_sum_succ qz12 24 1 2 3 rfl rfl) (ep727 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep729 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im qz43) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 29381103279 274877906944 532266004207 3554446214692864 4042974472335435349099

noncomputable def ep730 := @ep729 27604598824304640000000 0 1 ep648 ep332 ep649 ep334 (@Enclosure.Complex.IsNear.im_isNear qz43 Bool.false 47800999521 274877906944 534491662065 3554446214692864 Bool.true 29381103279 274877906944 532266004207 3554446214692864 (ep652 ep661))

noncomputable def ep731 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false 46400538986667379763 92015329414348800000 0 1 Bool.false

noncomputable def ep732 := nat_lit 21473135646169041430400862975731

noncomputable def ep733 := nat_lit 144062409693662213462351867348629

noncomputable def ep734 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re qz43) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz43) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) ep732 ep332 ep733

noncomputable def ep735 := nat_lit 151477669796504476537446393653

noncomputable def ep736 := nat_lit 24697429479484567073842624662941

noncomputable def ep737 := nat_lit 327063539330549038634786566963200000

noncomputable def ep738 := nat_lit 67364104340092849987416060251188462789728459266200908595200000

noncomputable def ep739 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz43) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 47800999521 274877906944 534491662065 3554446214692864 4042974472335435349099

noncomputable def ep740 := @ep739 27604598824304640000000 0 1 ep732 ep332 ep733 ep521 (@Enclosure.Complex.IsNear.re_isNear qz43 Bool.false 47800999521 274877906944 534491662065 3554446214692864 Bool.true 29381103279 274877906944 532266004207 3554446214692864 (ep652 ep661))

noncomputable def ep741 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im qz43) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 29381103279 274877906944 532266004207 3554446214692864 46400538986667379763

noncomputable def ep742 := @ep741 92015329414348800000 0 1 ep735 ep644 ep736 ep737 (@Enclosure.Complex.IsNear.im_isNear qz43 Bool.false 47800999521 274877906944 534491662065 3554446214692864 Bool.true 29381103279 274877906944 532266004207 3554446214692864 (ep652 ep661))

noncomputable abbrev qz909 := (ep728 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep743 := @ep642 ep526 ep332 ep527 ep521 (@ep646 ep647 ep648 ep332 ep649 ep334 ep650 ep524 ep332 ep525 ep334 (ep662 (@ep663 4042974472335435349099 27604598824304640000000 0 1 qz909) rfl) (ep730 (@ep731 4042974472335435349099 27604598824304640000000 0 1 qz909) rfl) rfl rfl) (@ep734 ep521 ep735 ep644 ep736 ep737 ep738 ep526 ep332 ep527 ep521 (ep740 (@ep731 4042974472335435349099 27604598824304640000000 0 1 qz909) rfl) (ep742 (@ep663 4042974472335435349099 27604598824304640000000 0 1 qz909) rfl) rfl rfl)

noncomputable def ep744 := @ep530 ep520 ep521 (@ep531 8886115536732160 (BSN.head_sum_c_eq qz12 24) (ep532 (BSN.head_sum_c_succ qz12 23 24 rfl rfl) (ep641 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep743 rfl rfl rfl

noncomputable def ep745 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz12 2 24) Bool.false ep331 ep332 ep333 ep334 Bool.true ep519 ep332 ep520 ep521 (@ep522 ep334 Bool.true ep519 ep332 ep520 ep521 (BSN.zetaApproximant_eq_folded' qz12 2 24 rfl) (ep744 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep746 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz325)) (Complex.im (zetaApproximant qz12 2 24)) 83 262144 8212947

noncomputable def ep747 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz325)) Bool.true 166 524288 16425894

noncomputable def ep748 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz325) qz864 Bool.false 20588825 262144 125

noncomputable def ep749 := BSN.sin_dyadic_bound_f 341546 1073741824 1 0 524288 258873 0 1 1 0 1 1 166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 341546) qz267 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 341546) qz268 0 0 rfl) rfl rfl

noncomputable def ep750 := @ep748 262144 Bool.true 166 524288 1 129310 (@ep341 20588825 262144 125 262144 ep516 rfl) (Enclosure.sfrac_false_div 20588825 262144) (BSN.sin_reduce2 qz864 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12017107493873254400) qz280) 226375608064910080 72057594037927936 Bool.false 166 524288 12 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 20588825 262144 226375608064910080 72057594037927936 12 12017107493873254400 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 166 524288 12017107493873254400 37778931862957161709568 341546 1073741824 258873 258620 (ep749 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep751 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz12 2 24) Bool.false ep331 ep332 ep333 ep334 Bool.true ep519 ep332 ep520 ep521 (@ep522 ep334 Bool.true ep519 ep332 ep520 ep521 (BSN.zetaApproximant_eq_folded' qz12 2 24 rfl) (ep744 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow27.d14 : Enclosure.Real.IsNear (hardyZApproximantEM 2 24 qz9) Bool.true ep314 ep315 ep316 ep317 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 2 24 qz9) ep318 Bool.true ep314 ep315 ep316 ep317 (@Eq.refl Real ep318) (@ep319 Bool.true ep314 ep315 ep316 ep317 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz325) (zetaApproximant qz12 2 24)) (@ep321 ep322 ep323 ep324 ep325 ep326 ep327 ep328 ep329 ep314 ep315 ep316 ep317 (@ep330 16948920320 ep331 ep332 ep333 ep334 ep320 ep322 ep323 ep324 (@ep335 33897840640 524287 524288 8212947 16948920320 (ep518 rfl rfl) rfl) ep745 rfl) (@ep746 16948920320 ep519 ep332 ep520 ep521 ep325 ep326 ep327 ep328 (@ep747 33897840640 83 262144 8212947 16948920320 (ep750 rfl rfl) rfl) ep751 rfl) rfl rfl))

noncomputable abbrev qz910 := (Enclosure.sfrac Bool.false 95415 1000)

noncomputable abbrev qz605 := (@HAdd.hAdd Complex Complex Complex qz808 (@HAdd.hAdd Complex Complex Complex qz808 qz809 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz810 (↑qz910) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 4))

noncomputable abbrev qz363 := (@HPow.hPow Complex Nat Complex qz539 qz605 3)

noncomputable abbrev qz55 := qz363

noncomputable def ep752 := Enclosure.Complex.IsNear qz55 Bool.true 18523075339 640000 0 1 Bool.true 6783832634787 64000000 0 1

noncomputable abbrev qz364 := qz605

noncomputable abbrev qz56 := (@HPow.hPow Complex Nat Complex qz254 qz364 2)

noncomputable abbrev qz57 := qz364

noncomputable def ep753 := @Enclosure.Complex.IsNear.of_eq qz55 (@HMul.hMul Complex Complex Complex qz3 qz56 qz57) Bool.true 18523075339 640000 0 1 Bool.true 6783832634787 64000000

noncomputable def ep754 := @Enclosure.Complex.IsNear.mul qz56 qz57 Bool.true 18523075339 640000 0 1 Bool.true 6783832634787 64000000 0

noncomputable def ep755 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz56) (Complex.re qz57)) (@HMul.hMul Real Real Real qz0 (Complex.im qz56) (Complex.im qz57)) 6141605113 640000 0 1 6190735113 320000

noncomputable def ep756 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz56) (Complex.re qz57) 361270889 160000 0 1 17000 4000 0 1

noncomputable def ep757 := @Enclosure.Complex.IsNear.re_isNear qz56 Bool.true 361270889 160000 0 1 Bool.false 324411 800 0 1

noncomputable abbrev qz365 := (@HPow.hPow Complex Nat Complex qz539 qz605 1)

noncomputable abbrev qz58 := qz365

noncomputable def ep758 := @Enclosure.Complex.IsNear.of_eq qz56 (@HMul.hMul Complex Complex Complex qz3 qz58 qz57) Bool.true 361270889 160000 0 1 Bool.false 324411 800

noncomputable def ep759 := @Enclosure.Complex.IsNear.mul qz58 qz57 Bool.true 361270889 160000 0 1 Bool.false 324411 800 0

noncomputable abbrev qz59 := (Complex.re qz365)

noncomputable abbrev qz60 := (Complex.im qz365)

noncomputable def ep760 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz59 (Complex.re qz57)) (@HMul.hMul Real Real Real qz0 qz60 (Complex.im qz57)) 289 16 0 1 364160889 160000

noncomputable def ep761 := @Enclosure.Real.IsNear.mulLit_ff qz59 (Complex.re qz57) 17000 4000 0 1 17000 4000 0 1

noncomputable def ep762 := @Enclosure.Complex.IsNear.re_isNear qz58 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1

noncomputable def ep763 := @Enclosure.Complex.IsNear.of_eq qz58 qz57 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0

noncomputable abbrev qz366 := qz910

noncomputable abbrev qz61 := qz366

noncomputable abbrev qz367 := (Complex.mk qz812 (Enclosure.sfrac Bool.false 190830 4000))

noncomputable abbrev qz911 := (BSN.w_shift_mk qz61 Bool.false 95415 1000 4 (@Eq.refl Real qz61) rfl)

noncomputable def ep764 := @Enclosure.Complex.IsNear.of_eq qz57 qz367 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1 qz911

noncomputable abbrev qz368 := (Enclosure.sfrac Bool.false 190830 4000)

noncomputable abbrev qz62 := (@ep763 1 (BSN.pow_one_c qz364) (ep764 (@Enclosure.Complex.IsNear.mk qz812 qz368 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1 qz814 (Enclosure.Real.IsNear.const Bool.false 190830 4000))))

noncomputable abbrev qz63 := (ep764 (@Enclosure.Complex.IsNear.mk qz812 qz368 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1 qz814 (Enclosure.Real.IsNear.const Bool.false 190830 4000)))

noncomputable abbrev qz606 := (@Enclosure.Complex.IsNear.re_isNear qz57 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1 qz63)

noncomputable def ep765 := @ep761 289 16 0 1 (ep762 qz62) qz606

noncomputable def ep766 := @Enclosure.Real.IsNear.mulLit_ff qz60 (Complex.im qz57) 190830 4000 0 1 190830 4000 0 1

noncomputable def ep767 := @Enclosure.Complex.IsNear.im_isNear qz58 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1

noncomputable abbrev qz607 := (@Enclosure.Complex.IsNear.im_isNear qz57 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1 qz63)

noncomputable def ep768 := @ep766 364160889 160000 0 1 (ep767 qz62) qz607

noncomputable def ep769 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz59 (Complex.im qz57)) (@HMul.hMul Real Real Real qz0 qz60 (Complex.re qz57)) 324411 1600 0 1 324411 1600

noncomputable def ep770 := @Enclosure.Real.IsNear.mulLit_ff qz59 (Complex.im qz57) 17000 4000 0 1 190830 4000 0 1

noncomputable def ep771 := @ep770 324411 1600 0 1 (ep762 qz62) qz607

noncomputable def ep772 := @Enclosure.Real.IsNear.mulLit_ff qz60 (Complex.re qz57) 190830 4000 0 1 17000 4000 0 1

noncomputable def ep773 := @ep772 324411 1600 0 1 (ep767 qz62) qz606

noncomputable abbrev qz608 := (@ep758 0 1 (BSN.pow_succ_c qz57 1 2 rfl) (@ep759 1 (@ep760 0 1 5780334224 361270889 160000 0 1 (ep765 rfl) (ep768 rfl) rfl rfl) (@ep769 0 1 1038115200 324411 800 0 1 (ep771 rfl) (ep773 rfl) rfl rfl)))

noncomputable def ep774 := @ep756 6141605113 640000 0 1 (ep757 qz608) qz606

noncomputable def ep775 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz56) (Complex.im qz57) 324411 800 0 1 190830 4000 0 1

noncomputable def ep776 := @Enclosure.Complex.IsNear.im_isNear qz56 Bool.true 361270889 160000 0 1 Bool.false 324411 800 0 1

noncomputable def ep777 := @ep775 6190735113 320000 0 1 (ep776 qz608) qz607

noncomputable def ep778 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re qz56) (Complex.im qz57)) (@HMul.hMul Real Real Real qz0 (Complex.im qz56) (Complex.re qz57)) 6894132374787 64000000 0 1 5514987 3200

noncomputable def ep779 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz56) (Complex.im qz57) 361270889 160000 0 1 190830 4000 0 1

noncomputable def ep780 := @ep779 6894132374787 64000000 0 1 (ep757 qz608) qz607

noncomputable def ep781 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz56) (Complex.re qz57) 324411 800 0 1 17000 4000 0 1

noncomputable def ep782 := @ep781 5514987 3200 0 1 (ep776 qz608) qz606

theorem EMRow27.d15 : ep752 := @ep753 0 1 (BSN.pow_succ_c qz57 2 3 rfl) (@ep754 1 (@ep755 0 1 5927384108480000 18523075339 640000 0 1 (ep774 rfl) (ep777 rfl) rfl rfl) (@ep778 0 1 21708264431318400 6783832634787 64000000 0 1 (ep780 rfl) (ep782 rfl) rfl rfl))

noncomputable abbrev qz369 := (@HAdd.hAdd Complex Complex Complex qz545 qz546 (@HMul.hMul Complex Complex Complex qz541 Complex.I ↑qz910))

noncomputable abbrev qz64 := qz369

noncomputable abbrev qz65 := (@Neg.neg Complex Complex.instNeg qz369)

noncomputable abbrev qz912 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 8) qz65)

noncomputable def ep783 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 9) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 8) qz912) Bool.true 121926352165 274877906944 45015275656623 17772231073464320 Bool.false 28445369709 137438953472 22470871148339 8886115536732160

noncomputable def ep784 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 8) qz912 Bool.true 36158892065 274877906944 40286700472747 17772231073464320 Bool.false 11190047857 274877906944 40227142485017 17772231073464320 Bool.true

noncomputable abbrev qz913 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 7) qz65)

noncomputable def ep785 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 8) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 7) qz913) Bool.true 36158892065 274877906944 40286700472747 17772231073464320 Bool.false 11190047857 274877906944 40227142485017 17772231073464320

noncomputable def ep786 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 7) qz913 Bool.false 31316347733 137438953472 8807837553109 4443057768366080 Bool.true 20969825413 274877906944 35193532274491 17772231073464320 Bool.true

noncomputable abbrev qz914 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 6) qz65)

noncomputable def ep787 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 7) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 6) qz914) Bool.false 31316347733 137438953472 8807837553109 4443057768366080 Bool.true 20969825413 274877906944 35193532274491 17772231073464320

noncomputable def ep788 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 6) qz914 Bool.false 34200396823 274877906944 29797214928841 17772231073464320 Bool.false 87586474607 274877906944 29735193844231 17772231073464320 Bool.false

noncomputable def ep789 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 6) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 5) (@HPow.hPow Complex Complex Complex qz14 qz16 qz65)) Bool.false 34200396823 274877906944 29797214928841 17772231073464320 Bool.false 87586474607 274877906944 29735193844231 17772231073464320

noncomputable def ep790 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 5) (@HPow.hPow Complex Complex Complex qz14 qz16 qz65) Bool.false 148645184661 274877906944 23822244544551 17772231073464320 Bool.false 132463372269 274877906944 23779406857061 17772231073464320 Bool.true

noncomputable def ep791 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 5) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 4) (@HPow.hPow Complex Complex Complex qz14 qz17 qz65)) Bool.false 148645184661 274877906944 23822244544551 17772231073464320 Bool.false 132463372269 274877906944 23779406857061 17772231073464320

noncomputable def ep792 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 4) (@HPow.hPow Complex Complex Complex qz14 qz17 qz65) Bool.false 4612638249 68719476736 1714523275463 1777223107346432 Bool.false 44123293173 68719476736 1712364677771 1777223107346432 Bool.false

noncomputable def ep793 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 4) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 3) (@HPow.hPow Complex Complex Complex qz14 qz548 qz65)) Bool.false 4612638249 68719476736 1714523275463 1777223107346432 Bool.false 44123293173 68719476736 1712364677771 1777223107346432

noncomputable def ep794 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 3) (@HPow.hPow Complex Complex Complex qz14 qz548 qz65) Bool.false 10386009815 34359738368 946426565755 1777223107346432 Bool.false 3944036169 34359738368 940837477211 1777223107346432 Bool.true

noncomputable def ep795 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 3) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 2) (@HPow.hPow Complex Complex Complex qz14 qz549 qz65)) Bool.false 10386009815 34359738368 946426565755 1777223107346432 Bool.false 3944036169 34359738368 940837477211 1777223107346432

noncomputable def ep796 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 2) (@HPow.hPow Complex Complex Complex qz14 qz549 qz65) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep797 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz263) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz64)

noncomputable abbrev qz370 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log qz807))

noncomputable def ep798 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz549 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz264 (Real.cos qz370)) (@HMul.hMul Real Real Real qz0 qz264 (@Neg.neg Real Real.instNeg (Real.sin qz370)))) Bool.true 23973728553 34359738368 946426565755 1777223107346432 Bool.false 3944036169 34359738368 940837477211 1777223107346432 (BSN.cpow_neg_s_mk qz61 95415 1000 2 (@Eq.refl Real qz61) rfl)

noncomputable def ep799 := nat_lit 939598279022791561238646693236881

noncomputable def ep800 := BSN.cos_dyadic_bound_f 175079603 1073741824 2 1 524288 258873 ep799 ep90 ep799 ep799 ep91 ep799 517333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 175079603) qz273 0 1 ep799 ep90 ep799 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 175079603) qz274 0 1 ep799 ep91 ep799 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz371 := (Enclosure.Real.IsNear.const Bool.false 95415 1000)

noncomputable abbrev qz915 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17337287) qz278)

noncomputable abbrev qz916 := (@Nat.cast Real Real.instNatCast 6160065906243927015424)

noncomputable def ep801 := @Enclosure.Real.IsNear.cos_image qz370 qz915 Bool.false 17337287 262144 97 131072 Bool.true 517333 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz370 Bool.false 433432179 6553600 19083 25862000 17337287 262144 97 131072 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz270 95415 1000 0 1 181704 262144 1 129310 433432179 6553600 19083 25862000 qz371 qz550 rfl) rfl) (Enclosure.sfrac_false_div 17337287 262144) (BSN.cos_reduce2 qz915 (@HDiv.hDiv Real Real Real qz1 qz916 qz280) 226375608064910080 72057594037927936 Bool.false 517333 524288 10 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 17337287 262144 226375608064910080 72057594037927936 10 6160065906243927015424 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 517333 524288 6160065906243927015424 37778931862957161709568 175079603 1073741824 258873 258620 (ep800 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep802 := BSN.sin_dyadic_bound_f 175079603 1073741824 1 0 524288 258873 0 1 1 0 1 1 85109 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 175079603) qz267 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 175079603) qz268 0 0 rfl) rfl rfl

noncomputable def ep803 := @Enclosure.Real.IsNear.sin_image qz370 qz915 Bool.false 17337287 262144 97 131072 Bool.true 85109 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz370 Bool.false 433432179 6553600 19083 25862000 17337287 262144 97 131072 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz270 95415 1000 0 1 181704 262144 1 129310 433432179 6553600 19083 25862000 qz371 qz550 rfl) rfl) (Enclosure.sfrac_false_div 17337287 262144) (BSN.sin_reduce2 qz915 (@HDiv.hDiv Real Real Real qz1 qz916 qz280) 226375608064910080 72057594037927936 Bool.false 85109 524288 10 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 17337287 262144 226375608064910080 72057594037927936 10 6160065906243927015424 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 85109 524288 6160065906243927015424 37778931862957161709568 175079603 1073741824 258873 258620 (ep802 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep804 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz264 (Real.cos qz370)) (@HMul.hMul Real Real Real qz0 qz264 (@Neg.neg Real Real.instNeg (Real.sin qz370))) Bool.true 23973728553 34359738368 946426565755 1777223107346432 Bool.false 3944036169 34359738368 940837477211 1777223107346432 (@Enclosure.Real.IsNear.mulLit_ft qz264 (Real.cos qz370) 46341 65536 1 262144 517333 524288 6337071 8474460160 23973728553 34359738368 946426565755 1777223107346432 qz551 (@Enclosure.Real.IsNear.recentre' (Real.cos qz370) Bool.true 517333 524288 12674142 16948920320 517333 524288 6337071 8474460160 (ep801 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz264 (@Neg.neg Real Real.instNeg (Real.sin qz370)) 46341 65536 1 262144 85109 524288 6337071 8474460160 3944036169 34359738368 940837477211 1777223107346432 qz551 (@Enclosure.Real.IsNear.neg (Real.sin qz370) Bool.true 85109 524288 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz370) Bool.true 85109 524288 12674142 16948920320 85109 524288 6337071 8474460160 (ep803 rfl rfl) rfl)) rfl)

noncomputable def ep805 := @ep796 23973728553 34359738368 946426565755 1777223107346432 Bool.false 3944036169 34359738368 940837477211 1777223107346432 Bool.false 10386009815 10386009815 34359738368 946426565755 1777223107346432 Bool.false 3944036169 3944036169 34359738368 940837477211 1777223107346432 (ep797 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz263 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz275)) (ep798 ep804) rfl rfl

noncomputable abbrev qz372 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep806 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz548 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz276 (Real.cos qz372)) (@HMul.hMul Real Real Real qz0 qz276 (@Neg.neg Real Real.instNeg (Real.sin qz372)))) Bool.true 16159381381 68719476736 192024177427 444305776836608 Bool.false 36235220835 68719476736 48220450035 111076444209152 (BSN.cpow_neg_s_mk qz61 95415 1000 3 (@Eq.refl Real qz61) rfl)

noncomputable def ep807 := nat_lit 5220700417892955486284780150433083555797645759468172494689254653528456034241

noncomputable def ep808 := nat_lit 5454213181156467732164255102720123855020227699023129471704749657027508161

noncomputable def ep809 := nat_lit 15651192827316553523390011941093810419682896823006471225124354461271313086401

noncomputable def ep810 := BSN.cos_dyadic_bound_f 1236207897 1073741824 3 2 524288 258873 ep807 ep199 ep808 ep809 ep202 ep808 213538 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1236207897) qz273 0 2 ep807 ep199 ep808 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1236207897) qz274 0 2 ep809 ep202 ep808 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz917 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54957895) qz269)

noncomputable def ep811 := @Enclosure.Real.IsNear.cos_image qz372 qz917 Bool.false 54957895 524288 387 524288 Bool.true 213538 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz372 Bool.false 2747894751 26214400 19083 25862000 54957895 524288 387 524288 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz279 95415 1000 0 1 287994 262144 1 129310 2747894751 26214400 19083 25862000 qz371 qz552 rfl) rfl) (Enclosure.sfrac_false_div 54957895 524288) (BSN.cos_reduce2 qz917 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 86990397303191030988800) qz272) 226375608064910080 72057594037927936 Bool.false 213538 524288 16 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 54957895 524288 226375608064910080 72057594037927936 16 86990397303191030988800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 213538 524288 86990397303191030988800 75557863725914323419136 1236207897 1073741824 258873 258620 (ep810 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep812 := nat_lit 9392897381662394701126872866697374301351746184883491986863294576625598855105

noncomputable def ep813 := nat_lit 24591614892536780412337353475945862017298826306039298708354440010765190559681

noncomputable def ep814 := BSN.sin_dyadic_bound_f 1236207897 1073741824 3 2 524288 258873 ep812 ep551 ep808 ep813 ep554 ep808 478830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1236207897) qz267 0 2 ep812 ep551 ep808 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1236207897) qz268 0 2 ep813 ep554 ep808 rfl rfl rfl rfl) rfl rfl

noncomputable def ep815 := @Enclosure.Real.IsNear.sin_image qz372 qz917 Bool.false 54957895 524288 387 524288 Bool.true 478830 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz372 Bool.false 2747894751 26214400 19083 25862000 54957895 524288 387 524288 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz279 95415 1000 0 1 287994 262144 1 129310 2747894751 26214400 19083 25862000 qz371 qz552 rfl) rfl) (Enclosure.sfrac_false_div 54957895 524288) (BSN.sin_reduce2 qz917 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 86990397303191030988800) qz272) 226375608064910080 72057594037927936 Bool.false 478830 524288 16 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 54957895 524288 226375608064910080 72057594037927936 16 86990397303191030988800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 478830 524288 86990397303191030988800 75557863725914323419136 1236207897 1073741824 258873 258620 (ep814 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep816 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz276 (Real.cos qz372)) (@HMul.hMul Real Real Real qz0 qz276 (@Neg.neg Real Real.instNeg (Real.sin qz372))) Bool.true 16159381381 68719476736 192024177427 444305776836608 Bool.false 36235220835 68719476736 48220450035 111076444209152 (@Enclosure.Real.IsNear.mulLit_ft qz276 (Real.cos qz372) 151349 262144 1 262144 106769 262144 25283629 33897840640 16159381381 68719476736 192024177427 444305776836608 qz553 (@Enclosure.Real.IsNear.recentre' (Real.cos qz372) Bool.true 213538 524288 50567258 67795681280 106769 262144 25283629 33897840640 (ep811 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz276 (@Neg.neg Real Real.instNeg (Real.sin qz372)) 151349 262144 1 262144 239415 262144 25283629 33897840640 36235220835 68719476736 48220450035 111076444209152 qz553 (@Enclosure.Real.IsNear.neg (Real.sin qz372) Bool.true 239415 262144 25283629 33897840640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz372) Bool.true 478830 524288 50567258 67795681280 239415 262144 25283629 33897840640 (ep815 rfl rfl) rfl)) rfl)

noncomputable def ep817 := @ep794 16159381381 68719476736 192024177427 444305776836608 Bool.false 36235220835 68719476736 48220450035 111076444209152 Bool.false 158489043421869637632 4612638249 68719476736 1714523275463 1777223107346432 Bool.false 1516064809358840561664 44123293173 68719476736 1712364677771 1777223107346432 (ep795 (BSN.head_sum_c_succ qz64 2 3 rfl rfl) (ep805 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep806 ep816) rfl rfl

noncomputable abbrev qz373 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep818 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz17 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz281 (Real.cos qz373)) (@HMul.hMul Real Real Real qz0 qz281 (@Neg.neg Real Real.instNeg (Real.sin qz373)))) Bool.false 130194631665 274877906944 6677011789921 17772231073464320 Bool.true 44029800423 274877906944 6655760079351 17772231073464320 (BSN.cpow_neg_s_mk qz61 95415 1000 4 (@Eq.refl Real qz61) rfl)

noncomputable def ep819 := nat_lit 15033572464364664979818347091790096

noncomputable def ep820 := BSN.cos_dyadic_bound_f 350159206 1073741824 2 1 524288 258873 ep819 ep90 ep819 ep819 ep91 ep819 496655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 350159206) qz273 0 1 ep819 ep90 ep819 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 350159206) qz274 0 1 ep819 ep91 ep819 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz918 := (@Nat.cast Real Real.instNatCast 17337287)

noncomputable abbrev qz609 := (@HDiv.hDiv Real Real Real qz1 qz918 qz832)

noncomputable def ep821 := @Enclosure.Real.IsNear.cos_image qz373 qz609 Bool.false 17337287 131072 97 131072 Bool.false 496655 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz373 Bool.false 433432179 3276800 19083 25862000 17337287 131072 97 131072 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz283 95415 1000 0 1 363408 262144 1 129310 433432179 3276800 19083 25862000 qz371 qz554 rfl) rfl) (Enclosure.sfrac_false_div 17337287 131072) (BSN.cos_reduce0 qz609 (@HDiv.hDiv Real Real Real qz1 qz916 qz561) 226375608064910080 72057594037927936 Bool.false 496655 524288 21 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 17337287 131072 226375608064910080 72057594037927936 21 6160065906243927015424 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 496655 524288 6160065906243927015424 18889465931478580854784 350159206 1073741824 258873 258620 (ep820 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep822 := BSN.sin_dyadic_bound_f 350159206 1073741824 2 1 524288 258873 ep819 ep100 ep819 ep819 ep101 ep819 167961 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 350159206) qz267 0 1 ep819 ep100 ep819 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 350159206) qz268 0 1 ep819 ep101 ep819 rfl rfl rfl rfl) rfl rfl

noncomputable def ep823 := @Enclosure.Real.IsNear.sin_image qz373 qz609 Bool.false 17337287 131072 97 131072 Bool.false 167961 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz373 Bool.false 433432179 3276800 19083 25862000 17337287 131072 97 131072 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz283 95415 1000 0 1 363408 262144 1 129310 433432179 3276800 19083 25862000 qz371 qz554 rfl) rfl) (Enclosure.sfrac_false_div 17337287 131072) (BSN.sin_reduce0 qz609 (@HDiv.hDiv Real Real Real qz1 qz916 qz561) 226375608064910080 72057594037927936 Bool.false 167961 524288 21 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 17337287 131072 226375608064910080 72057594037927936 21 6160065906243927015424 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 167961 524288 6160065906243927015424 18889465931478580854784 350159206 1073741824 258873 258620 (ep822 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep824 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz281 (Real.cos qz373)) (@HMul.hMul Real Real Real qz0 qz281 (@Neg.neg Real Real.instNeg (Real.sin qz373))) Bool.false 130194631665 274877906944 6677011789921 17772231073464320 Bool.true 44029800423 274877906944 6655760079351 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ff qz281 (Real.cos qz373) 262143 524288 1 524288 496655 524288 6337071 8474460160 130194631665 274877906944 6677011789921 17772231073464320 qz555 (@Enclosure.Real.IsNear.recentre' (Real.cos qz373) Bool.false 496655 524288 12674142 16948920320 496655 524288 6337071 8474460160 (ep821 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz281 (@Neg.neg Real Real.instNeg (Real.sin qz373)) 262143 524288 1 524288 167961 524288 6337071 8474460160 44029800423 274877906944 6655760079351 17772231073464320 qz555 (@Enclosure.Real.IsNear.neg (Real.sin qz373) Bool.false 167961 524288 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz373) Bool.false 167961 524288 12674142 16948920320 167961 524288 6337071 8474460160 (ep823 rfl rfl) rfl)) rfl)

noncomputable def ep825 := @ep792 130194631665 274877906944 6677011789921 17772231073464320 Bool.true 44029800423 274877906944 6655760079351 17772231073464320 Bool.false 10214819309230013546496 148645184661 274877906944 23822244544551 17772231073464320 Bool.false 9102813629011653033984 132463372269 274877906944 23779406857061 17772231073464320 (ep793 (BSN.head_sum_c_succ qz64 3 4 rfl rfl) (ep817 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep818 ep824) rfl rfl

noncomputable abbrev qz374 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep826 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz16 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz284 (Real.cos qz374)) (@HMul.hMul Real Real Real qz0 qz284 (@Neg.neg Real Real.instNeg (Real.sin qz374)))) Bool.true 57222393919 137438953472 597497038429 1777223107346432 Bool.true 22438448831 137438953472 595578698717 1777223107346432 (BSN.cpow_neg_s_mk qz61 95415 1000 5 (@Eq.refl Real qz61) rfl)

noncomputable def ep827 := nat_lit 10979688508742516793957659855052724398003746264719808239467276476580982947840

noncomputable def ep828 := nat_lit 7451227934959324776258576034504038777082338679688432416348747887129133056

noncomputable def ep829 := nat_lit 28744263153859514601203738116320319265323106906880002212787826132561508171776

noncomputable def ep830 := BSN.sin_dyadic_bound_f 1285370952 1073741824 3 2 524288 258873 ep827 ep551 ep828 ep829 ep554 ep828 488102 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1285370952) qz267 0 2 ep827 ep551 ep828 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1285370952) qz268 0 2 ep829 ep554 ep828 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz610 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20127985) qz832)

noncomputable def ep831 := @Enclosure.Real.IsNear.cos_image qz374 qz610 Bool.false 20127985 131072 97 131072 Bool.true 488102 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz374 Bool.false 503199627 3276800 19083 25862000 20127985 131072 97 131072 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz287 95415 1000 0 1 421904 262144 1 129310 503199627 3276800 19083 25862000 qz371 qz556 rfl) rfl) (Enclosure.sfrac_false_div 20127985 131072) (BSN.cos_reduce1 qz610 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22612484935468135219200) qz561) 226375608064910080 72057594037927936 Bool.false 488102 524288 24 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 20127985 131072 226375608064910080 72057594037927936 24 22612484935468135219200 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 488102 524288 22612484935468135219200 18889465931478580854784 1285370952 1073741824 258873 258620 (ep830 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep832 := nat_lit 6103138606161380140988148175489070905014117853146421658555753041605936807936

noncomputable def ep833 := nat_lit 18294513362614221773411927374398204637488188882079888110834561629043552157696

noncomputable def ep834 := BSN.cos_dyadic_bound_f 1285370952 1073741824 3 2 524288 258873 ep832 ep199 ep828 ep833 ep202 ep828 191398 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1285370952) qz273 0 2 ep832 ep199 ep828 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1285370952) qz274 0 2 ep833 ep202 ep828 rfl rfl rfl rfl) rfl rfl

noncomputable def ep835 := @Enclosure.Real.IsNear.sin_image qz374 qz610 Bool.false 20127985 131072 97 131072 Bool.false 191398 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz374 Bool.false 503199627 3276800 19083 25862000 20127985 131072 97 131072 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz287 95415 1000 0 1 421904 262144 1 129310 503199627 3276800 19083 25862000 qz371 qz556 rfl) rfl) (Enclosure.sfrac_false_div 20127985 131072) (BSN.sin_reduce1 qz610 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22612484935468135219200) qz561) 226375608064910080 72057594037927936 Bool.false 191398 524288 24 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 20127985 131072 226375608064910080 72057594037927936 24 22612484935468135219200 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 191398 524288 22612484935468135219200 18889465931478580854784 1285370952 1073741824 258873 258620 (ep834 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep836 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz284 (Real.cos qz374)) (@HMul.hMul Real Real Real qz0 qz284 (@Neg.neg Real Real.instNeg (Real.sin qz374))) Bool.true 57222393919 137438953472 597497038429 1777223107346432 Bool.true 22438448831 137438953472 595578698717 1777223107346432 (@Enclosure.Real.IsNear.mulLit_ft qz284 (Real.cos qz374) 234469 524288 1 524288 244051 262144 6337071 8474460160 57222393919 137438953472 597497038429 1777223107346432 qz557 (@Enclosure.Real.IsNear.recentre' (Real.cos qz374) Bool.true 488102 524288 12674142 16948920320 244051 262144 6337071 8474460160 (ep831 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz284 (@Neg.neg Real Real.instNeg (Real.sin qz374)) 234469 524288 1 524288 95699 262144 6337071 8474460160 22438448831 137438953472 595578698717 1777223107346432 qz557 (@Enclosure.Real.IsNear.neg (Real.sin qz374) Bool.false 95699 262144 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz374) Bool.false 191398 524288 12674142 16948920320 95699 262144 6337071 8474460160 (ep835 rfl rfl) rfl)) rfl)

noncomputable def ep837 := @ep790 57222393919 137438953472 597497038429 1777223107346432 Bool.true 22438448831 137438953472 595578698717 1777223107346432 Bool.false 4700466747680233619456 34200396823 274877906944 29797214928841 17772231073464320 Bool.false 12037793408287982485504 87586474607 274877906944 29735193844231 17772231073464320 (ep791 (BSN.head_sum_c_succ qz64 4 5 rfl rfl) (ep825 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep826 ep836) rfl rfl

noncomputable abbrev qz375 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep838 := @Enclosure.Complex.IsNear.of_eq qz914 (Complex.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz375)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz375)))) Bool.false 28432298643 274877906944 1086827056719 3554446214692864 Bool.true 27139075005 68719476736 272916921513 888611553673216 (BSN.cpow_neg_s_mk qz61 95415 1000 6 (@Eq.refl Real qz61) rfl)

noncomputable def ep839 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz290 95415 1000 0 1 4034681531866359 2251799813685248 50000000012931 6465500000000000000 76993827672605728797 450359962737049600 954150000246762273 1293100000000000000000 qz371 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 50000000012931 6465500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz825) Bool.false 16922680887833197019136 9444732965739290427392 1000000000258620 129310000000000000000 4034681531866359 2251799813685248 50000000012931 6465500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep136 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep840 := nat_lit 8881834017769696943425834478379068290296169719945948867069881953276500443136

noncomputable def ep841 := nat_lit 15763217475471950530519782397704582895027268150511204556617829981324640256

noncomputable def ep842 := nat_lit 26613975618358146929216463870341795705098454623536824192096410199866852048896

noncomputable def ep843 := BSN.cos_dyadic_bound_f 1411580364 1073741824 3 2 524288 258873 ep840 ep199 ep841 ep842 ep202 ep841 132837 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1411580364) qz273 0 2 ep840 ep199 ep841 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1411580364) qz274 0 2 ep842 ep202 ep841 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz611 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22408153) qz832)

noncomputable def ep844 := @Enclosure.Real.IsNear.cos_image qz375 qz611 Bool.false 22408153 131072 97 131072 Bool.false 132837 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz375 Bool.false 76993827672605728797 450359962737049600 954150000246762273 1293100000000000000000 22408153 131072 97 131072 (ep839 rfl) rfl) (Enclosure.sfrac_false_div 22408153 131072) (BSN.cos_reduce0 qz611 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24832784396893433102336) qz561) 226375608064910080 72057594037927936 Bool.false 132837 524288 27 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 22408153 131072 226375608064910080 72057594037927936 27 24832784396893433102336 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 132837 524288 24832784396893433102336 18889465931478580854784 1411580364 1073741824 258873 258620 (ep843 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep845 := nat_lit 15974690658005076937742086235164159256217083681382298997080493251912641085440

noncomputable def ep846 := nat_lit 41812954133148246917037003349166990632071841683757574470690577268372867710976

noncomputable def ep847 := BSN.sin_dyadic_bound_f 1411580364 1073741824 3 2 524288 258873 ep845 ep551 ep841 ep846 ep554 ep841 507180 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1411580364) qz267 0 2 ep845 ep551 ep841 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1411580364) qz268 0 2 ep846 ep554 ep841 rfl rfl rfl rfl) rfl rfl

noncomputable def ep848 := @Enclosure.Real.IsNear.sin_image qz375 qz611 Bool.false 22408153 131072 97 131072 Bool.false 507180 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz375 Bool.false 76993827672605728797 450359962737049600 954150000246762273 1293100000000000000000 22408153 131072 97 131072 (ep839 rfl) rfl) (Enclosure.sfrac_false_div 22408153 131072) (BSN.sin_reduce0 qz611 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24832784396893433102336) qz561) 226375608064910080 72057594037927936 Bool.false 507180 524288 27 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 22408153 131072 226375608064910080 72057594037927936 27 24832784396893433102336 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 507180 524288 24832784396893433102336 18889465931478580854784 1411580364 1073741824 258873 258620 (ep847 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep849 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz375)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz375))) Bool.false 28432298643 274877906944 1086827056719 3554446214692864 Bool.true 27139075005 68719476736 272916921513 888611553673216 (@Enclosure.Real.IsNear.mulLit_ff qz288 (Real.cos qz375) 214039 524288 1 524288 132837 524288 6337071 8474460160 28432298643 274877906944 1086827056719 3554446214692864 qz558 (@Enclosure.Real.IsNear.recentre' (Real.cos qz375) Bool.false 132837 524288 12674142 16948920320 132837 524288 6337071 8474460160 (ep844 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz288 (@Neg.neg Real Real.instNeg (Real.sin qz375)) 214039 524288 1 524288 126795 131072 6337071 8474460160 27139075005 68719476736 272916921513 888611553673216 qz558 (@Enclosure.Real.IsNear.neg (Real.sin qz375) Bool.false 126795 131072 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz375) Bool.false 507180 524288 12674142 16948920320 126795 131072 6337071 8474460160 (ep848 rfl rfl) rfl)) rfl)

noncomputable def ep850 := @ep788 28432298643 274877906944 1086827056719 3554446214692864 Bool.true 27139075005 68719476736 272916921513 888611553673216 Bool.false 17216344235955038715904 31316347733 137438953472 8807837553109 4443057768366080 Bool.true 1441035429626635091968 20969825413 274877906944 35193532274491 17772231073464320 (ep789 (BSN.head_sum_c_succ qz64 5 6 rfl rfl) (ep837 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep838 ep849) rfl rfl

noncomputable abbrev qz376 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep851 := @Enclosure.Complex.IsNear.of_eq qz913 (Complex.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz376)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz376)))) Bool.true 98791587531 274877906944 5055350260311 17772231073464320 Bool.false 16079936635 137438953472 2516805105263 8886115536732160 (BSN.cpow_neg_s_mk qz61 95415 1000 7 (@Eq.refl Real qz61) rfl)

noncomputable def ep852 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz293 95415 1000 0 1 4381792198794487 2251799813685248 50000000012931 6465500000000000000 83617740529595195421 450359962737049600 954150000246762273 1293100000000000000000 qz371 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 50000000012931 6465500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz828) Bool.false 18378568546572512002048 9444732965739290427392 1000000000258620 129310000000000000000 4381792198794487 2251799813685248 50000000012931 6465500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep147 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep853 := nat_lit 13039522349213437370664654910387216

noncomputable def ep854 := BSN.cos_dyadic_bound_f 337921186 1073741824 2 1 524288 258873 ep853 ep90 ep853 ep853 ep91 ep853 498537 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 337921186) qz273 0 1 ep853 ep90 ep853 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 337921186) qz274 0 1 ep853 ep91 ep853 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz919 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97343861) qz269)

noncomputable def ep855 := @Enclosure.Real.IsNear.cos_image qz376 qz919 Bool.false 97343861 524288 97 131072 Bool.true 498537 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz376 Bool.false 83617740529595195421 450359962737049600 954150000246762273 1293100000000000000000 97343861 524288 97 131072 (ep852 rfl) rfl) (Enclosure.sfrac_false_div 97343861 524288) (BSN.cos_reduce2 qz919 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23779089510973489283072) qz272) 226375608064910080 72057594037927936 Bool.false 498537 524288 29 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 97343861 524288 226375608064910080 72057594037927936 29 23779089510973489283072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 498537 524288 23779089510973489283072 75557863725914323419136 337921186 1073741824 258873 258620 (ep854 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep856 := BSN.sin_dyadic_bound_f 337921186 1073741824 2 1 524288 258873 ep853 ep100 ep853 ep853 ep101 ep853 162290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 337921186) qz267 0 1 ep853 ep100 ep853 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 337921186) qz268 0 1 ep853 ep101 ep853 rfl rfl rfl rfl) rfl rfl

noncomputable def ep857 := @Enclosure.Real.IsNear.sin_image qz376 qz919 Bool.false 97343861 524288 97 131072 Bool.true 162290 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz376 Bool.false 83617740529595195421 450359962737049600 954150000246762273 1293100000000000000000 97343861 524288 97 131072 (ep852 rfl) rfl) (Enclosure.sfrac_false_div 97343861 524288) (BSN.sin_reduce2 qz919 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23779089510973489283072) qz272) 226375608064910080 72057594037927936 Bool.false 162290 524288 29 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 97343861 524288 226375608064910080 72057594037927936 29 23779089510973489283072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 162290 524288 23779089510973489283072 75557863725914323419136 337921186 1073741824 258873 258620 (ep856 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep858 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz376)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz376))) Bool.true 98791587531 274877906944 5055350260311 17772231073464320 Bool.false 16079936635 137438953472 2516805105263 8886115536732160 (@Enclosure.Real.IsNear.mulLit_ft qz291 (Real.cos qz376) 198163 524288 1 524288 498537 524288 6337071 8474460160 98791587531 274877906944 5055350260311 17772231073464320 qz559 (@Enclosure.Real.IsNear.recentre' (Real.cos qz376) Bool.true 498537 524288 12674142 16948920320 498537 524288 6337071 8474460160 (ep855 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz291 (@Neg.neg Real Real.instNeg (Real.sin qz376)) 198163 524288 1 524288 81145 262144 6337071 8474460160 16079936635 137438953472 2516805105263 8886115536732160 qz559 (@Enclosure.Real.IsNear.neg (Real.sin qz376) Bool.true 81145 262144 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz376) Bool.true 162290 524288 12674142 16948920320 81145 262144 6337071 8474460160 (ep857 rfl rfl) rfl)) rfl)

noncomputable def ep859 := @ep786 98791587531 274877906944 5055350260311 17772231073464320 Bool.false 16079936635 137438953472 2516805105263 8886115536732160 Bool.true 4969640284120604999680 36158892065 274877906944 40286700472747 17772231073464320 Bool.false 1537948466767676309504 11190047857 274877906944 40227142485017 17772231073464320 (ep787 (BSN.head_sum_c_succ qz64 6 7 rfl rfl) (ep850 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep851 ep858) rfl rfl

noncomputable abbrev qz377 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep860 := @Enclosure.Complex.IsNear.of_eq qz912 (Complex.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz377)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz377)))) Bool.true 21441865025 68719476736 1182143795969 4443057768366080 Bool.false 45700691561 274877906944 4714599811661 17772231073464320 (BSN.cpow_neg_s_mk qz61 95415 1000 8 (@Eq.refl Real qz61) rfl)

noncomputable def ep861 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz296 95415 1000 0 1 9364972152248037 4503599627370496 100000000038793 12931000000000000000 178711763581349290071 900719925474099200 1908300000740286819 2586200000000000000000 qz371 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz831) Bool.false 19639770079031275290624 9444732965739290427392 1000000000387930 129310000000000000000 9364972152248037 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep158 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep862 := nat_lit 76362992373586844046052601270246881

noncomputable def ep863 := BSN.cos_dyadic_bound_f 525679129 1073741824 2 1 524288 258873 ep862 ep90 ep862 ep862 ep91 ep862 462700 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 525679129) qz273 0 1 ep862 ep90 ep862 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 525679129) qz274 0 1 ep862 ep91 ep862 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz920 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104023937) qz269)

noncomputable def ep864 := @Enclosure.Real.IsNear.cos_image qz377 qz920 Bool.false 104023937 524288 97 131072 Bool.true 462700 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 178711763581349290071 900719925474099200 1908300000740286819 2586200000000000000000 104023937 524288 97 131072 (ep861 rfl) rfl) (Enclosure.sfrac_false_div 104023937 524288) (BSN.cos_reduce2 qz920 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36991380202899871105024) qz272) 226375608064910080 72057594037927936 Bool.false 462700 524288 31 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 104023937 524288 226375608064910080 72057594037927936 31 36991380202899871105024 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 462700 524288 36991380202899871105024 75557863725914323419136 525679129 1073741824 258873 258620 (ep863 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep865 := BSN.sin_dyadic_bound_f 525679129 1073741824 2 1 524288 258873 ep862 ep100 ep862 ep862 ep101 ep862 246547 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 525679129) qz267 0 1 ep862 ep100 ep862 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 525679129) qz268 0 1 ep862 ep101 ep862 rfl rfl rfl rfl) rfl rfl

noncomputable def ep866 := @Enclosure.Real.IsNear.sin_image qz377 qz920 Bool.false 104023937 524288 97 131072 Bool.true 246547 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 178711763581349290071 900719925474099200 1908300000740286819 2586200000000000000000 104023937 524288 97 131072 (ep861 rfl) rfl) (Enclosure.sfrac_false_div 104023937 524288) (BSN.sin_reduce2 qz920 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36991380202899871105024) qz272) 226375608064910080 72057594037927936 Bool.false 246547 524288 31 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 104023937 524288 226375608064910080 72057594037927936 31 36991380202899871105024 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 246547 524288 36991380202899871105024 75557863725914323419136 525679129 1073741824 258873 258620 (ep865 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep867 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz377)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz377))) Bool.true 21441865025 68719476736 1182143795969 4443057768366080 Bool.false 45700691561 274877906944 4714599811661 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ft qz294 (Real.cos qz377) 185363 524288 1 524288 115675 131072 6337071 8474460160 21441865025 68719476736 1182143795969 4443057768366080 qz562 (@Enclosure.Real.IsNear.recentre' (Real.cos qz377) Bool.true 462700 524288 12674142 16948920320 115675 131072 6337071 8474460160 (ep864 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz294 (@Neg.neg Real Real.instNeg (Real.sin qz377)) 185363 524288 1 524288 246547 524288 6337071 8474460160 45700691561 274877906944 4714599811661 17772231073464320 qz562 (@Enclosure.Real.IsNear.neg (Real.sin qz377) Bool.true 246547 524288 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz377) Bool.true 246547 524288 12674142 16948920320 246547 524288 6337071 8474460160 (ep866 rfl rfl) rfl)) rfl)

noncomputable def ep868 := @ep784 21441865025 68719476736 1182143795969 4443057768366080 Bool.false 45700691561 274877906944 4714599811661 17772231073464320 Bool.true 8378715121108060733440 121926352165 274877906944 45015275656623 17772231073464320 Bool.false 15638007375716356718592 28445369709 137438953472 22470871148339 8886115536732160 (ep785 (BSN.head_sum_c_succ qz64 7 8 rfl rfl) (ep859 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep860 ep867) rfl rfl

theorem EMRow27.d16 : Enclosure.Complex.IsNear (BSN.headSumC qz64 9) Bool.true 121926352165 274877906944 45015275656623 17772231073464320 Bool.false 28445369709 137438953472 22470871148339 8886115536732160 := ep783 (BSN.head_sum_c_succ qz64 8 9 rfl rfl) (ep868 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz921 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 16) qz65)

noncomputable def ep869 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 17) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 16) qz921) Bool.false 8303683425 34359738368 3783269415577 888611553673216 Bool.true 7356088589 34359738368 7554419678127 1777223107346432

noncomputable def ep870 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 16) qz921 Bool.false 1479865023 34359738368 18079002370553 4443057768366080 Bool.true 8554836523 137438953472 18050289343673 4443057768366080 Bool.false

noncomputable abbrev qz922 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 15) qz65)

noncomputable def ep871 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 16) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 15) qz922) Bool.false 1479865023 34359738368 18079002370553 4443057768366080 Bool.true 8554836523 137438953472 18050289343673 4443057768366080

noncomputable def ep872 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 15) qz922 Bool.true 9683515241 68719476736 8607550906053 2221528884183040 Bool.false 16342868539 137438953472 8593240814903 2221528884183040 Bool.false

noncomputable abbrev qz923 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 14) qz65)

noncomputable def ep873 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 15) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 14) qz923) Bool.true 9683515241 68719476736 8607550906053 2221528884183040 Bool.false 16342868539 137438953472 8593240814903 2221528884183040

noncomputable def ep874 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 14) qz923 Bool.true 51983416015 137438953472 32639227560573 8886115536732160 Bool.false 66473253929 274877906944 65178483943771 17772231073464320 Bool.false

noncomputable abbrev qz924 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 13) qz65)

noncomputable def ep875 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 14) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 13) qz924) Bool.true 51983416015 137438953472 32639227560573 8886115536732160 Bool.false 66473253929 274877906944 65178483943771 17772231073464320

noncomputable def ep876 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 13) qz924 Bool.true 176571562207 274877906944 61569629366913 17772231073464320 Bool.false 21610653987 137438953472 7686450278231 2221528884183040 Bool.false

noncomputable abbrev qz925 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 12) qz65)

noncomputable def ep877 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 13) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 12) qz925) Bool.true 176571562207 274877906944 61569629366913 17772231073464320 Bool.false 21610653987 137438953472 7686450278231 2221528884183040

noncomputable def ep878 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 12) qz925 Bool.true 42301313757 68719476736 28869902647129 8886115536732160 Bool.true 35786351053 274877906944 57631173579633 17772231073464320 Bool.true

noncomputable abbrev qz926 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 11) qz65)

noncomputable def ep879 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 12) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 11) qz926) Bool.true 42301313757 68719476736 28869902647129 8886115536732160 Bool.true 35786351053 274877906944 57631173579633 17772231073464320

noncomputable def ep880 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 11) qz926 Bool.true 24544299687 68719476736 26851848887469 8886115536732160 Bool.false 6920903903 274877906944 53606649391493 17772231073464320 Bool.true

noncomputable abbrev qz927 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 10) qz65)

noncomputable def ep881 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 11) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 10) qz927) Bool.true 24544299687 68719476736 26851848887469 8886115536732160 Bool.false 6920903903 274877906944 53606649391493 17772231073464320

noncomputable def ep882 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 10) qz927 Bool.true 45795239607 68719476736 24733952401877 8886115536732160 Bool.true 11250228097 274877906944 49396919109429 17772231073464320 Bool.false

noncomputable abbrev qz928 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 9) qz65)

noncomputable def ep883 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 10) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 9) qz928) Bool.true 45795239607 68719476736 24733952401877 8886115536732160 Bool.true 11250228097 274877906944 49396919109429 17772231073464320

noncomputable def ep884 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 9) qz928 Bool.true 121926352165 274877906944 45015275656623 17772231073464320 Bool.false 28445369709 137438953472 22470871148339 8886115536732160 Bool.true

noncomputable abbrev qz378 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep885 := @Enclosure.Complex.IsNear.of_eq qz928 (Complex.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz378)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz378)))) Bool.true 61254606263 274877906944 4452629147131 17772231073464320 Bool.true 68140967515 274877906944 4455176812751 17772231073464320 (BSN.cpow_neg_s_mk qz61 95415 1000 9 (@Eq.refl Real qz61) rfl)

noncomputable def ep886 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz299 95415 1000 0 1 9895417793173221 4503599627370496 100000000038793 12931000000000000000 188834257747124576343 900719925474099200 1908300000740286819 2586200000000000000000 qz371 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz842) Bool.false 20752195215788806766592 9444732965739290427392 1000000000387930 129310000000000000000 9895417793173221 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep185 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep887 := nat_lit 382107858362926091327419670046243856

noncomputable def ep888 := BSN.sin_dyadic_bound_f 786224354 1073741824 2 1 524288 258873 ep887 ep100 ep887 ep887 ep101 ep887 350501 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 786224354) qz267 0 1 ep887 ep100 ep887 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 786224354) qz268 0 1 ep887 ep101 ep887 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz612 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27479001) qz832)

noncomputable def ep889 := @Enclosure.Real.IsNear.cos_image qz378 qz612 Bool.false 27479001 131072 97 131072 Bool.true 350501 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz378 Bool.false 188834257747124576343 900719925474099200 1908300000740286819 2586200000000000000000 27479001 131072 97 131072 (ep886 rfl) rfl) (Enclosure.sfrac_false_div 27479001 131072) (BSN.cos_reduce1 qz612 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13831405113873679777792) qz561) 226375608064910080 72057594037927936 Bool.false 350501 524288 33 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 27479001 131072 226375608064910080 72057594037927936 33 13831405113873679777792 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 350501 524288 13831405113873679777792 18889465931478580854784 786224354 1073741824 258873 258620 (ep888 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep890 := nat_lit 853432223827726208536641795593432571289295825681833997168908023795131842816

noncomputable def ep891 := nat_lit 146006415422701986870580761343072564563630680114884988144233534217748736

noncomputable def ep892 := nat_lit 2560004658652333221636184225257611568738760215685272221530435604316960030976

noncomputable def ep893 := BSN.cos_dyadic_bound_f 786224354 1073741824 3 2 524288 258873 ep890 ep199 ep891 ep892 ep202 ep891 389905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 786224354) qz273 0 2 ep890 ep199 ep891 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 786224354) qz274 0 2 ep892 ep202 ep891 rfl rfl rfl rfl) rfl rfl

noncomputable def ep894 := @Enclosure.Real.IsNear.sin_image qz378 qz612 Bool.false 27479001 131072 97 131072 Bool.false 389905 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz378 Bool.false 188834257747124576343 900719925474099200 1908300000740286819 2586200000000000000000 27479001 131072 97 131072 (ep886 rfl) rfl) (Enclosure.sfrac_false_div 27479001 131072) (BSN.sin_reduce1 qz612 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13831405113873679777792) qz561) 226375608064910080 72057594037927936 Bool.false 389905 524288 33 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 27479001 131072 226375608064910080 72057594037927936 33 13831405113873679777792 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 389905 524288 13831405113873679777792 18889465931478580854784 786224354 1073741824 258873 258620 (ep893 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep895 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz378)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz378))) Bool.true 61254606263 274877906944 4452629147131 17772231073464320 Bool.true 68140967515 274877906944 4455176812751 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ft qz297 (Real.cos qz378) 174763 524288 1 524288 350501 524288 6337071 8474460160 61254606263 274877906944 4452629147131 17772231073464320 qz563 (@Enclosure.Real.IsNear.recentre' (Real.cos qz378) Bool.true 350501 524288 12674142 16948920320 350501 524288 6337071 8474460160 (ep889 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz297 (@Neg.neg Real Real.instNeg (Real.sin qz378)) 174763 524288 1 524288 389905 524288 6337071 8474460160 68140967515 274877906944 4455176812751 17772231073464320 qz563 (@Enclosure.Real.IsNear.neg (Real.sin qz378) Bool.false 389905 524288 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz378) Bool.false 389905 524288 12674142 16948920320 389905 524288 6337071 8474460160 (ep894 rfl rfl) rfl)) rfl)

noncomputable def ep896 := @ep884 61254606263 274877906944 4452629147131 17772231073464320 Bool.true 68140967515 274877906944 4455176812751 17772231073464320 Bool.true 50352398444684516524032 45795239607 68719476736 24733952401877 8886115536732160 Bool.true 1546219575972970102784 11250228097 274877906944 49396919109429 17772231073464320 EMRow27.d16 (ep885 ep895) rfl rfl

noncomputable abbrev qz379 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep897 := @Enclosure.Complex.IsNear.of_eq qz927 (Complex.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz379)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz379)))) Bool.false 1328183745 4294967296 264737060699 1110764442091520 Bool.false 567847875 8589934592 263108142629 1110764442091520 (BSN.cpow_neg_s_mk qz61 95415 1000 10 (@Eq.refl Real qz61) rfl)

noncomputable def ep898 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz302 95415 1000 0 1 10369908600166117 4503599627370496 100000000038793 12931000000000000000 197888965816970010711 900719925474099200 1908300000740286819 2586200000000000000000 qz371 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz845) Bool.false 21747274560655572598784 9444732965739290427392 1000000000387930 129310000000000000000 10369908600166117 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep196 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep899 := nat_lit 18309584202557646481123073900395872068495571949431159359030660295547608198625

noncomputable def ep900 := nat_lit 20701975651848294103597545231528765430852829473678201398017818482132741601

noncomputable def ep901 := nat_lit 47920155427071795926773654665900046940124164810314700280912081448891711319521

noncomputable def ep902 := BSN.sin_dyadic_bound_f 1460499707 1073741824 3 2 524288 258873 ep899 ep551 ep900 ep901 ep554 ep900 512704 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1460499707) qz267 0 2 ep899 ep551 ep900 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1460499707) qz268 0 2 ep901 ep554 ep900 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz929 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57593269) qz278)

noncomputable def ep903 := @Enclosure.Real.IsNear.cos_image qz379 qz929 Bool.false 57593269 262144 97 131072 Bool.false 512704 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz379 Bool.false 197888965816970010711 900719925474099200 1908300000740286819 2586200000000000000000 57593269 262144 97 131072 (ep898 rfl) rfl) (Enclosure.sfrac_false_div 57593269 262144) (BSN.cos_reduce3 qz929 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51386765159437107724288) qz280) 226375608064910080 72057594037927936 Bool.false 512704 524288 34 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 57593269 262144 226375608064910080 72057594037927936 34 51386765159437107724288 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 512704 524288 51386765159437107724288 37778931862957161709568 1460499707 1073741824 258873 258620 (ep902 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep904 := nat_lit 10181192101710625064669973298100608378244585673894501066749485861296285773281

noncomputable def ep905 := nat_lit 30502172353828178605802724803838767603872051362736146797452421946924591836641

noncomputable def ep906 := BSN.cos_dyadic_bound_f 1460499707 1073741824 3 2 524288 258873 ep904 ep199 ep900 ep905 ep202 ep900 109600 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1460499707) qz273 0 2 ep904 ep199 ep900 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1460499707) qz274 0 2 ep905 ep202 ep900 rfl rfl rfl rfl) rfl rfl

noncomputable def ep907 := @Enclosure.Real.IsNear.sin_image qz379 qz929 Bool.false 57593269 262144 97 131072 Bool.true 109600 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz379 Bool.false 197888965816970010711 900719925474099200 1908300000740286819 2586200000000000000000 57593269 262144 97 131072 (ep898 rfl) rfl) (Enclosure.sfrac_false_div 57593269 262144) (BSN.sin_reduce3 qz929 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51386765159437107724288) qz280) 226375608064910080 72057594037927936 Bool.false 109600 524288 34 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 57593269 262144 226375608064910080 72057594037927936 34 51386765159437107724288 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 109600 524288 51386765159437107724288 37778931862957161709568 1460499707 1073741824 258873 258620 (ep906 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep908 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz379)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz379))) Bool.false 1328183745 4294967296 264737060699 1110764442091520 Bool.false 567847875 8589934592 263108142629 1110764442091520 (@Enclosure.Real.IsNear.mulLit_ff qz300 (Real.cos qz379) 165795 524288 1 524288 8011 8192 6337071 8474460160 1328183745 4294967296 264737060699 1110764442091520 qz565 (@Enclosure.Real.IsNear.recentre' (Real.cos qz379) Bool.false 512704 524288 12674142 16948920320 8011 8192 6337071 8474460160 (ep903 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz300 (@Neg.neg Real Real.instNeg (Real.sin qz379)) 165795 524288 1 524288 3425 16384 6337071 8474460160 567847875 8589934592 263108142629 1110764442091520 qz565 (@Enclosure.Real.IsNear.neg (Real.sin qz379) Bool.true 3425 16384 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz379) Bool.true 109600 524288 12674142 16948920320 3425 16384 6337071 8474460160 (ep907 rfl rfl) rfl)) rfl)

noncomputable def ep909 := @ep882 1328183745 4294967296 264737060699 1110764442091520 Bool.false 567847875 8589934592 263108142629 1110764442091520 Bool.true 105416964458888036352 24544299687 68719476736 26851848887469 8886115536732160 Bool.false 59450111844287512576 6920903903 274877906944 53606649391493 17772231073464320 (ep883 (BSN.head_sum_c_succ qz64 9 10 rfl rfl) (ep896 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep897 ep908) rfl rfl

noncomputable abbrev qz380 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep910 := @Enclosure.Complex.IsNear.of_eq qz926 (Complex.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz380)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz380)))) Bool.true 8878507035 34359738368 100902687983 444305776836608 Bool.true 10676813739 68719476736 201226209407 888611553673216 (BSN.cpow_neg_s_mk qz61 95415 1000 11 (@Eq.refl Real qz61) rfl)

noncomputable def ep911 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz305 95415 1000 0 1 10799147631728357 4503599627370496 100000000038793 12931000000000000000 206080134256272236631 900719925474099200 1908300000740286819 2586200000000000000000 qz371 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz847) Bool.false 22647454054174387339264 9444732965739290427392 1000000000387930 129310000000000000000 10799147631728357 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep212 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep912 := nat_lit 6002719967583444516449172224647828113475637586924591377061160911399947030625

noncomputable def ep913 := nat_lit 2228492173585913784965769732563148078527878889370618235292966596250390625

noncomputable def ep914 := nat_lit 15717801403961310825524554104034447581261434257076853558017328060129741590625

noncomputable def ep915 := BSN.sin_dyadic_bound_f 1105354005 1073741824 3 2 524288 258873 ep912 ep551 ep913 ep914 ep554 ep913 449320 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1105354005) qz267 0 2 ep912 ep551 ep913 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1105354005) qz268 0 2 ep914 ep554 ep913 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz930 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 119954425) qz269)

noncomputable def ep916 := @Enclosure.Real.IsNear.cos_image qz380 qz930 Bool.false 119954425 524288 97 131072 Bool.true 449320 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz380 Bool.false 206080134256272236631 900719925474099200 1908300000740286819 2586200000000000000000 119954425 524288 97 131072 (ep911 rfl) rfl) (Enclosure.sfrac_false_div 119954425 524288) (BSN.cos_reduce1 qz930 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 77782373241488985292800) qz272) 226375608064910080 72057594037927936 Bool.false 449320 524288 36 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 119954425 524288 226375608064910080 72057594037927936 36 77782373241488985292800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 449320 524288 77782373241488985292800 75557863725914323419136 1105354005 1073741824 258873 258620 (ep915 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep917 := nat_lit 3335834867401285137487302689129932573299144383353382150916330713709415190625

noncomputable def ep918 := nat_lit 10003047617856683584891976527924671423740377392281405216278406207935744790625

noncomputable def ep919 := BSN.cos_dyadic_bound_f 1105354005 1073741824 3 2 524288 258873 ep917 ep199 ep913 ep918 ep202 ep913 270164 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1105354005) qz273 0 2 ep917 ep199 ep913 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1105354005) qz274 0 2 ep918 ep202 ep913 rfl rfl rfl rfl) rfl rfl

noncomputable def ep920 := @Enclosure.Real.IsNear.sin_image qz380 qz930 Bool.false 119954425 524288 97 131072 Bool.false 270164 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz380 Bool.false 206080134256272236631 900719925474099200 1908300000740286819 2586200000000000000000 119954425 524288 97 131072 (ep911 rfl) rfl) (Enclosure.sfrac_false_div 119954425 524288) (BSN.sin_reduce1 qz930 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 77782373241488985292800) qz272) 226375608064910080 72057594037927936 Bool.false 270164 524288 36 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 119954425 524288 226375608064910080 72057594037927936 36 77782373241488985292800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 270164 524288 77782373241488985292800 75557863725914323419136 1105354005 1073741824 258873 258620 (ep919 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep921 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz380)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz380))) Bool.true 8878507035 34359738368 100902687983 444305776836608 Bool.true 10676813739 68719476736 201226209407 888611553673216 (@Enclosure.Real.IsNear.mulLit_ft qz303 (Real.cos qz380) 158079 524288 1 524288 56165 65536 6337071 8474460160 8878507035 34359738368 100902687983 444305776836608 qz566 (@Enclosure.Real.IsNear.recentre' (Real.cos qz380) Bool.true 449320 524288 12674142 16948920320 56165 65536 6337071 8474460160 (ep916 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz303 (@Neg.neg Real Real.instNeg (Real.sin qz380)) 158079 524288 1 524288 67541 131072 6337071 8474460160 10676813739 68719476736 201226209407 888611553673216 qz566 (@Enclosure.Real.IsNear.neg (Real.sin qz380) Bool.false 67541 131072 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz380) Bool.false 270164 524288 12674142 16948920320 67541 131072 6337071 8474460160 (ep920 rfl rfl) rfl)) rfl)

noncomputable def ep922 := @ep880 8878507035 34359738368 100902687983 444305776836608 Bool.true 10676813739 68719476736 201226209407 888611553673216 Bool.true 1453462073313199128576 42301313757 68719476736 28869902647129 8886115536732160 Bool.true 2459219318652962603008 35786351053 274877906944 57631173579633 17772231073464320 (ep881 (BSN.head_sum_c_succ qz64 10 11 rfl rfl) (ep909 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep910 ep921) rfl rfl

noncomputable abbrev qz381 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep923 := @Enclosure.Complex.IsNear.of_eq qz925 (Complex.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz381)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz381)))) Bool.true 7366307179 274877906944 765964814531 3554446214692864 Bool.false 79007659027 274877906944 772085729243 3554446214692864 (BSN.cpow_neg_s_mk qz61 95415 1000 12 (@Eq.refl Real qz61) rfl)

noncomputable def ep924 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz308 95415 1000 0 1 11191020447815397 4503599627370496 100000000038793 12931000000000000000 213558243205661220951 900719925474099200 1908300000740286819 2586200000000000000000 qz371 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz850) Bool.false 23469270914176955449344 9444732965739290427392 1000000000387930 129310000000000000000 11191020447815397 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep223 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep925 := nat_lit 14198319204148617991959038398655814208494496228008060530412010221874924486656

noncomputable def ep926 := nat_lit 40197013666566827330495764662340109951999581147123416863192278290426494976

noncomputable def ep927 := nat_lit 42514563585112720321216123666642762405579489521729934757509646109043920470016

noncomputable def ep928 := BSN.cos_dyadic_bound_f 1586807424 1073741824 3 2 524288 258873 ep925 ep199 ep926 ep927 ep202 ep926 48671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1586807424) qz273 0 2 ep925 ep199 ep926 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1586807424) qz274 0 2 ep927 ep202 ep926 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz931 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62153629) qz278)

noncomputable def ep929 := @Enclosure.Real.IsNear.cos_image qz381 qz931 Bool.false 62153629 262144 387 524288 Bool.true 48671 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz381 Bool.false 213558243205661220951 900719925474099200 1908300000740286819 2586200000000000000000 62153629 262144 387 524288 (ep924 rfl) rfl) (Enclosure.sfrac_false_div 62153629 262144) (BSN.cos_reduce2 qz931 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55830822846801524031488) qz280) 226375608064910080 72057594037927936 Bool.false 48671 524288 37 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 62153629 262144 226375608064910080 72057594037927936 37 55830822846801524031488 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 48671 524288 55830822846801524031488 37778931862957161709568 1586807424 1073741824 258873 258620 (ep928 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep930 := nat_lit 25524816956534258923661872505850593487328493545496810221251064576742522880000

noncomputable def ep931 := nat_lit 66785630197367665174865053896345860860223769487777255523593334012331631312896

noncomputable def ep932 := BSN.sin_dyadic_bound_f 1586807424 1073741824 3 2 524288 258873 ep930 ep551 ep926 ep931 ep554 ep926 522023 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1586807424) qz267 0 2 ep930 ep551 ep926 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1586807424) qz268 0 2 ep931 ep554 ep926 rfl rfl rfl rfl) rfl rfl

noncomputable def ep933 := @Enclosure.Real.IsNear.sin_image qz381 qz931 Bool.false 62153629 262144 387 524288 Bool.true 522023 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz381 Bool.false 213558243205661220951 900719925474099200 1908300000740286819 2586200000000000000000 62153629 262144 387 524288 (ep924 rfl) rfl) (Enclosure.sfrac_false_div 62153629 262144) (BSN.sin_reduce2 qz931 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55830822846801524031488) qz280) 226375608064910080 72057594037927936 Bool.false 522023 524288 37 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 62153629 262144 226375608064910080 72057594037927936 37 55830822846801524031488 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 522023 524288 55830822846801524031488 37778931862957161709568 1586807424 1073741824 258873 258620 (ep932 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep934 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz381)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz381))) Bool.true 7366307179 274877906944 765964814531 3554446214692864 Bool.false 79007659027 274877906944 772085729243 3554446214692864 (@Enclosure.Real.IsNear.mulLit_ft qz306 (Real.cos qz381) 151349 524288 1 524288 48671 524288 25283629 33897840640 7366307179 274877906944 765964814531 3554446214692864 qz567 (@Enclosure.Real.IsNear.recentre' (Real.cos qz381) Bool.true 48671 524288 50567258 67795681280 48671 524288 25283629 33897840640 (ep929 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz306 (@Neg.neg Real Real.instNeg (Real.sin qz381)) 151349 524288 1 524288 522023 524288 25283629 33897840640 79007659027 274877906944 772085729243 3554446214692864 qz567 (@Enclosure.Real.IsNear.neg (Real.sin qz381) Bool.true 522023 524288 25283629 33897840640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz381) Bool.true 522023 524288 50567258 67795681280 522023 524288 25283629 33897840640 (ep933 rfl rfl) rfl)) rfl)

noncomputable def ep935 := @ep878 7366307179 274877906944 765964814531 3554446214692864 Bool.false 79007659027 274877906944 772085729243 3554446214692864 Bool.true 12133905361323113316352 176571562207 274877906944 61569629366913 17772231073464320 Bool.false 11880582671275137171456 21610653987 137438953472 7686450278231 2221528884183040 (ep879 (BSN.head_sum_c_succ qz64 11 12 rfl rfl) (ep922 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep923 ep934) rfl rfl

noncomputable abbrev qz382 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep936 := @Enclosure.Complex.IsNear.of_eq qz924 (Complex.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz382)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz382)))) Bool.false 72604730177 274877906944 3708825754233 17772231073464320 Bool.false 23251945955 274877906944 3686881717923 17772231073464320 (BSN.cpow_neg_s_mk qz61 95415 1000 13 (@Eq.refl Real qz61) rfl)

noncomputable def ep937 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz311 95415 1000 0 1 11551488463034085 4503599627370496 100000000038793 12931000000000000000 44087410868015888811 180143985094819840 1908300000740286819 2586200000000000000000 qz371 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz853) Bool.false 24225227133228857425920 9444732965739290427392 1000000000387930 129310000000000000000 11551488463034085 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep234 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep938 := nat_lit 13514943850539657412557410109366410708660579528016341233523486180689416249600

noncomputable def ep939 := nat_lit 11286007056331571738842165490225225517720176503778992330071868554581074176

noncomputable def ep940 := nat_lit 35378008930465042107216043923261187205177589906655727719265204590812482724096

noncomputable def ep941 := BSN.sin_dyadic_bound_f 1353840618 1073741824 3 2 524288 258873 ep938 ep551 ep939 ep940 ep554 ep939 499307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1353840618) qz267 0 2 ep938 ep551 ep939 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1353840618) qz268 0 2 ep940 ep554 ep939 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz932 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128311253) qz269)

noncomputable def ep942 := @Enclosure.Real.IsNear.cos_image qz382 qz932 Bool.false 128311253 524288 387 524288 Bool.false 499307 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz382 Bool.false 44087410868015888811 180143985094819840 1908300000740286819 2586200000000000000000 128311253 524288 387 524288 (ep937 rfl) rfl) (Enclosure.sfrac_false_div 128311253 524288) (BSN.cos_reduce3 qz932 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95268064167711700156416) qz272) 226375608064910080 72057594037927936 Bool.false 499307 524288 38 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 128311253 524288 226375608064910080 72057594037927936 38 95268064167711700156416 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 499307 524288 95268064167711700156416 75557863725914323419136 1353840618 1073741824 258873 258620 (ep941 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep943 := nat_lit 7513318142324845927749157689865883827263753149566313570770857597518378393856

noncomputable def ep944 := nat_lit 22517382412861874639769788738617201030755819095691382727652429055445973033216

noncomputable def ep945 := BSN.cos_dyadic_bound_f 1353840618 1073741824 3 2 524288 258873 ep943 ep199 ep939 ep944 ep202 ep939 159905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1353840618) qz273 0 2 ep943 ep199 ep939 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1353840618) qz274 0 2 ep944 ep202 ep939 rfl rfl rfl rfl) rfl rfl

noncomputable def ep946 := @Enclosure.Real.IsNear.sin_image qz382 qz932 Bool.false 128311253 524288 387 524288 Bool.true 159905 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz382 Bool.false 44087410868015888811 180143985094819840 1908300000740286819 2586200000000000000000 128311253 524288 387 524288 (ep937 rfl) rfl) (Enclosure.sfrac_false_div 128311253 524288) (BSN.sin_reduce3 qz932 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95268064167711700156416) qz272) 226375608064910080 72057594037927936 Bool.false 159905 524288 38 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 128311253 524288 226375608064910080 72057594037927936 38 95268064167711700156416 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 159905 524288 95268064167711700156416 75557863725914323419136 1353840618 1073741824 258873 258620 (ep945 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep947 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz382)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz382))) Bool.false 72604730177 274877906944 3708825754233 17772231073464320 Bool.false 23251945955 274877906944 3686881717923 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ff qz309 (Real.cos qz382) 145411 524288 1 524288 499307 524288 25283629 33897840640 72604730177 274877906944 3708825754233 17772231073464320 qz568 (@Enclosure.Real.IsNear.recentre' (Real.cos qz382) Bool.false 499307 524288 50567258 67795681280 499307 524288 25283629 33897840640 (ep942 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz309 (@Neg.neg Real Real.instNeg (Real.sin qz382)) 145411 524288 1 524288 159905 524288 25283629 33897840640 23251945955 274877906944 3686881717923 17772231073464320 qz568 (@Enclosure.Real.IsNear.neg (Real.sin qz382) Bool.true 159905 524288 25283629 33897840640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz382) Bool.true 159905 524288 50567258 67795681280 159905 524288 25283629 33897840640 (ep946 rfl rfl) rfl)) rfl)

noncomputable def ep948 := @ep876 72604730177 274877906944 3708825754233 17772231073464320 Bool.false 23251945955 274877906944 3686881717923 17772231073464320 Bool.true 28578185180004818616320 51983416015 137438953472 32639227560573 8886115536732160 Bool.false 9136014453880272191488 66473253929 274877906944 65178483943771 17772231073464320 (ep877 (BSN.head_sum_c_succ qz64 12 13 rfl rfl) (ep935 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep936 ep947) rfl rfl

noncomputable abbrev qz383 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep949 := @Enclosure.Complex.IsNear.of_eq qz923 (Complex.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz383)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz383)))) Bool.false 32616385533 137438953472 1790976063639 8886115536732160 Bool.true 33787516851 274877906944 3567442575453 17772231073464320 (BSN.cpow_neg_s_mk qz61 95415 1000 14 (@Eq.refl Real qz61) rfl)

noncomputable def ep950 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz314 95415 1000 0 1 11885241781671653 4503599627370496 100000000038793 12931000000000000000 226806068919640154199 900719925474099200 1908300000740286819 2586200000000000000000 qz371 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz856) Bool.false 24925158572916270432256 9444732965739290427392 1000000000387930 129310000000000000000 11885241781671653 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep244 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep951 := nat_lit 69338012947220322518533763729000625

noncomputable def ep952 := BSN.cos_dyadic_bound_f 513148245 1073741824 2 1 524288 258873 ep951 ep90 ep951 ep951 ep91 ep951 465546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 513148245) qz273 0 1 ep951 ep90 ep951 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 513148245) qz274 0 1 ep951 ep91 ep951 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz933 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132018507) qz269)

noncomputable def ep953 := @Enclosure.Real.IsNear.cos_image qz383 qz933 Bool.false 132018507 524288 97 131072 Bool.false 465546 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz383 Bool.false 226806068919640154199 900719925474099200 1908300000740286819 2586200000000000000000 132018507 524288 97 131072 (ep950 rfl) rfl) (Enclosure.sfrac_false_div 132018507 524288) (BSN.cos_reduce0 qz933 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36109597617002804936704) qz272) 226375608064910080 72057594037927936 Bool.false 465546 524288 40 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 132018507 524288 226375608064910080 72057594037927936 40 36109597617002804936704 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 465546 524288 36109597617002804936704 75557863725914323419136 513148245 1073741824 258873 258620 (ep952 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep954 := BSN.sin_dyadic_bound_f 513148245 1073741824 2 1 524288 258873 ep951 ep100 ep951 ep951 ep101 ep951 241131 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 513148245) qz267 0 1 ep951 ep100 ep951 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 513148245) qz268 0 1 ep951 ep101 ep951 rfl rfl rfl rfl) rfl rfl

noncomputable def ep955 := @Enclosure.Real.IsNear.sin_image qz383 qz933 Bool.false 132018507 524288 97 131072 Bool.false 241131 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz383 Bool.false 226806068919640154199 900719925474099200 1908300000740286819 2586200000000000000000 132018507 524288 97 131072 (ep950 rfl) rfl) (Enclosure.sfrac_false_div 132018507 524288) (BSN.sin_reduce0 qz933 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36109597617002804936704) qz272) 226375608064910080 72057594037927936 Bool.false 241131 524288 40 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 132018507 524288 226375608064910080 72057594037927936 40 36109597617002804936704 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 241131 524288 36109597617002804936704 75557863725914323419136 513148245 1073741824 258873 258620 (ep954 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep956 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz383)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz383))) Bool.false 32616385533 137438953472 1790976063639 8886115536732160 Bool.true 33787516851 274877906944 3567442575453 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ff qz312 (Real.cos qz383) 140121 524288 1 524288 232773 262144 6337071 8474460160 32616385533 137438953472 1790976063639 8886115536732160 qz569 (@Enclosure.Real.IsNear.recentre' (Real.cos qz383) Bool.false 465546 524288 12674142 16948920320 232773 262144 6337071 8474460160 (ep953 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz312 (@Neg.neg Real Real.instNeg (Real.sin qz383)) 140121 524288 1 524288 241131 524288 6337071 8474460160 33787516851 274877906944 3567442575453 17772231073464320 qz569 (@Enclosure.Real.IsNear.neg (Real.sin qz383) Bool.false 241131 524288 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz383) Bool.false 241131 524288 12674142 16948920320 241131 524288 6337071 8474460160 (ep955 rfl rfl) rfl)) rfl)

noncomputable def ep957 := @ep874 32616385533 137438953472 1790976063639 8886115536732160 Bool.true 33787516851 274877906944 3567442575453 17772231073464320 Bool.true 2661784401306403733504 9683515241 68719476736 8607550906053 2221528884183040 Bool.false 8984586994922534469632 16342868539 137438953472 8593240814903 2221528884183040 (ep875 (BSN.head_sum_c_succ qz64 13 14 rfl rfl) (ep948 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep949 ep956) rfl rfl

noncomputable abbrev qz384 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep958 := @Enclosure.Complex.IsNear.of_eq qz922 (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz384)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz384)))) Bool.false 12643245287 68719476736 863900558447 4443057768366080 Bool.true 12448852531 68719476736 863807713867 4443057768366080 (BSN.cpow_neg_s_mk qz61 95415 1000 15 (@Eq.refl Real qz61) rfl)

noncomputable def ep959 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz317 95415 1000 0 1 12195956895733477 4503599627370496 100000000038793 12931000000000000000 232735445441281941591 900719925474099200 1908300000740286819 2586200000000000000000 qz371 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 100000000038793 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz859) Bool.false 25576775395801252757504 9444732965739290427392 1000000000387930 129310000000000000000 12195956895733477 4503599627370496 100000000038793 12931000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep255 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep960 := nat_lit 1085778836119913643487456303974358941404818687365939884728466365472031235201

noncomputable def ep961 := nat_lit 236306769450809928445163559299392524615529361386304614391109479568366721

noncomputable def ep962 := nat_lit 3256863894820839310605478584804478039165225003375047044956616877456956972161

noncomputable def ep963 := BSN.cos_dyadic_bound_f 834996241 1073741824 3 2 524288 258873 ep960 ep199 ep961 ep962 ep202 ep961 373588 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 834996241) qz273 0 2 ep960 ep199 ep961 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 834996241) qz274 0 2 ep962 ep202 ep961 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz934 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67734929) qz278)

noncomputable def ep964 := @Enclosure.Real.IsNear.cos_image qz384 qz934 Bool.false 67734929 262144 97 131072 Bool.false 373588 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz384 Bool.false 232735445441281941591 900719925474099200 1908300000740286819 2586200000000000000000 67734929 262144 97 131072 (ep959 rfl) rfl) (Enclosure.sfrac_false_div 67734929 262144) (BSN.cos_reduce0 qz934 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29378818446626870263808) qz280) 226375608064910080 72057594037927936 Bool.false 373588 524288 41 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 67734929 262144 226375608064910080 72057594037927936 41 29378818446626870263808 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 373588 524288 29378818446626870263808 37778931862957161709568 834996241 1073741824 258873 258620 (ep963 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep965 := nat_lit 486113946982402396947534899329066561

noncomputable def ep966 := BSN.sin_dyadic_bound_f 834996241 1073741824 2 1 524288 258873 ep965 ep100 ep965 ep965 ep101 ep965 367844 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 834996241) qz267 0 1 ep965 ep100 ep965 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 834996241) qz268 0 1 ep965 ep101 ep965 rfl rfl rfl rfl) rfl rfl

noncomputable def ep967 := @Enclosure.Real.IsNear.sin_image qz384 qz934 Bool.false 67734929 262144 97 131072 Bool.false 367844 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz384 Bool.false 232735445441281941591 900719925474099200 1908300000740286819 2586200000000000000000 67734929 262144 97 131072 (ep959 rfl) rfl) (Enclosure.sfrac_false_div 67734929 262144) (BSN.sin_reduce0 qz934 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29378818446626870263808) qz280) 226375608064910080 72057594037927936 Bool.false 367844 524288 41 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 67734929 262144 226375608064910080 72057594037927936 41 29378818446626870263808 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 367844 524288 29378818446626870263808 37778931862957161709568 834996241 1073741824 258873 258620 (ep966 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep968 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz384)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz384))) Bool.false 12643245287 68719476736 863900558447 4443057768366080 Bool.true 12448852531 68719476736 863807713867 4443057768366080 (@Enclosure.Real.IsNear.mulLit_ff qz315 (Real.cos qz384) 135371 524288 1 524288 93397 131072 6337071 8474460160 12643245287 68719476736 863900558447 4443057768366080 qz570 (@Enclosure.Real.IsNear.recentre' (Real.cos qz384) Bool.false 373588 524288 12674142 16948920320 93397 131072 6337071 8474460160 (ep964 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz315 (@Neg.neg Real Real.instNeg (Real.sin qz384)) 135371 524288 1 524288 91961 131072 6337071 8474460160 12448852531 68719476736 863807713867 4443057768366080 qz570 (@Enclosure.Real.IsNear.neg (Real.sin qz384) Bool.false 91961 131072 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz384) Bool.false 367844 524288 12674142 16948920320 91961 131072 6337071 8474460160 (ep967 rfl rfl) rfl)) rfl)

noncomputable def ep969 := @ep872 12643245287 68719476736 863900558447 4443057768366080 Bool.true 12448852531 68719476736 863807713867 4443057768366080 Bool.false 203391100040937209856 1479865023 34359738368 18079002370553 4443057768366080 Bool.true 587883889422581628928 8554836523 137438953472 18050289343673 4443057768366080 (ep873 (BSN.head_sum_c_succ qz64 14 15 rfl rfl) (ep957 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep958 ep968) rfl rfl

noncomputable abbrev qz385 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep970 := @Enclosure.Complex.IsNear.of_eq qz921 (Complex.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz385)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz385)))) Bool.false 3411909201 17179869184 209336176833 1110764442091520 Bool.true 20869517833 137438953472 1671519703289 8886115536732160 (BSN.cpow_neg_s_mk qz61 95415 1000 16 (@Eq.refl Real qz61) rfl)

noncomputable def ep971 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz320 95415 1000 0 1 3121657384082679 1125899906842624 25000000012931 3232750000000000000 59570587860449763357 225179981368524800 477075000246762273 646550000000000000000 qz371 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz862) Bool.false 26186360105375033720832 9444732965739290427392 1000000000517240 129310000000000000000 3121657384082679 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep269 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep972 := nat_lit 241345707657075469778575413610845841

noncomputable def ep973 := BSN.cos_dyadic_bound_f 700906189 1073741824 2 1 524288 258873 ep972 ep90 ep972 ep972 ep91 ep972 416496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 700906189) qz273 0 1 ep972 ep90 ep972 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 700906189) qz274 0 1 ep972 ep91 ep972 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz935 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 138698583) qz269)

noncomputable def ep974 := @Enclosure.Real.IsNear.cos_image qz385 qz935 Bool.false 138698583 524288 97 131072 Bool.false 416496 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz385 Bool.false 59570587860449763357 225179981368524800 477075000246762273 646550000000000000000 138698583 524288 97 131072 (ep971 rfl) rfl) (Enclosure.sfrac_false_div 138698583 524288) (BSN.cos_reduce0 qz935 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49321888308929186758656) qz272) 226375608064910080 72057594037927936 Bool.false 416496 524288 42 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 138698583 524288 226375608064910080 72057594037927936 42 49321888308929186758656 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 416496 524288 49321888308929186758656 75557863725914323419136 700906189 1073741824 258873 258620 (ep973 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep975 := BSN.sin_dyadic_bound_f 700906189 1073741824 2 1 524288 258873 ep972 ep100 ep972 ep972 ep101 ep972 318446 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 700906189) qz267 0 1 ep972 ep100 ep972 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 700906189) qz268 0 1 ep972 ep101 ep972 rfl rfl rfl rfl) rfl rfl

noncomputable def ep976 := @Enclosure.Real.IsNear.sin_image qz385 qz935 Bool.false 138698583 524288 97 131072 Bool.false 318446 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz385 Bool.false 59570587860449763357 225179981368524800 477075000246762273 646550000000000000000 138698583 524288 97 131072 (ep971 rfl) rfl) (Enclosure.sfrac_false_div 138698583 524288) (BSN.sin_reduce0 qz935 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49321888308929186758656) qz272) 226375608064910080 72057594037927936 Bool.false 318446 524288 42 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 138698583 524288 226375608064910080 72057594037927936 42 49321888308929186758656 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 318446 524288 49321888308929186758656 75557863725914323419136 700906189 1073741824 258873 258620 (ep975 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep977 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz385)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz385))) Bool.false 3411909201 17179869184 209336176833 1110764442091520 Bool.true 20869517833 137438953472 1671519703289 8886115536732160 (@Enclosure.Real.IsNear.mulLit_ff qz318 (Real.cos qz385) 131071 524288 1 524288 26031 32768 6337071 8474460160 3411909201 17179869184 209336176833 1110764442091520 qz571 (@Enclosure.Real.IsNear.recentre' (Real.cos qz385) Bool.false 416496 524288 12674142 16948920320 26031 32768 6337071 8474460160 (ep974 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz318 (@Neg.neg Real Real.instNeg (Real.sin qz385)) 131071 524288 1 524288 159223 262144 6337071 8474460160 20869517833 137438953472 1671519703289 8886115536732160 qz571 (@Enclosure.Real.IsNear.neg (Real.sin qz385) Bool.false 159223 262144 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz385) Bool.false 318446 524288 12674142 16948920320 159223 262144 6337071 8474460160 (ep976 rfl rfl) rfl)) rfl)

noncomputable def ep978 := @ep870 3411909201 17179869184 209336176833 1110764442091520 Bool.true 20869517833 137438953472 1671519703289 8886115536732160 Bool.false 142656194986849075200 8303683425 34359738368 3783269415577 888611553673216 Bool.true 4044052469277924524032 7356088589 34359738368 7554419678127 1777223107346432 (ep871 (BSN.head_sum_c_succ qz64 15 16 rfl rfl) (ep969 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep970 ep977) rfl rfl

theorem EMRow27.d17 : Enclosure.Complex.IsNear (BSN.headSumC qz64 17) Bool.false 8303683425 34359738368 3783269415577 888611553673216 Bool.true 7356088589 34359738368 7554419678127 1777223107346432 := ep869 (BSN.head_sum_c_succ qz64 16 17 rfl rfl) (ep978 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz66 := (@HAdd.hAdd Complex Complex Complex qz261 qz369 qz549)

noncomputable def ep979 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) qz66) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1

noncomputable def ep980 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66)) 364130889 16000 0 1 364160889 20000 0 1

noncomputable def ep981 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66) 364130889 40000 0 1 5 2 0 1 364130889 16000

noncomputable abbrev qz67 := (@HAdd.hAdd Complex Complex Complex qz261 qz369 qz572)

noncomputable def ep982 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz67) Bool.true 364130889 40000 0 1 Bool.false 19083 100 0 1

noncomputable def ep983 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67)) 3 4 0 1 364160889 40000 0 1

noncomputable def ep984 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67) 1 2 0 1 3 2 0 1 3 4

noncomputable def ep985 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz64 Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 (BSN.ascPochhammer_one_eval qz64)

noncomputable def ep986 := ep985 (@Enclosure.Complex.IsNear.of_eq qz64 (Complex.mk qz321 qz61) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 (BSN.s_crit_mk qz61 Bool.false 95415 1000 (@Eq.refl Real qz61)) (@Enclosure.Complex.IsNear.mk qz321 qz61 Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 qz322 qz371))

noncomputable def ep987 := @ep984 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep986)

noncomputable def ep988 := @Enclosure.Complex.IsNear.of_eq qz67 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz61) Bool.false 3 2 0 1 Bool.false 95415 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 95415 1000 1 (@Eq.refl Real qz61))

noncomputable abbrev qz613 := (ep988 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz61 Bool.false 3 2 0 1 Bool.false 95415 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz371))

noncomputable def ep989 := ep987 (@Enclosure.Complex.IsNear.re_isNear qz67 Bool.false 3 2 0 1 Bool.false 95415 1000 0 1 qz613)

noncomputable def ep990 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67) 95415 1000 0 1 95415 1000 0 1 364160889 40000

noncomputable def ep991 := @ep990 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep986)

noncomputable def ep992 := ep991 (@Enclosure.Complex.IsNear.im_isNear qz67 Bool.false 3 2 0 1 Bool.false 95415 1000 0 1 qz613)

noncomputable def ep993 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz67 Bool.true 364130889 40000 0 1 Bool.false 19083 100 0 1 (@ep983 1456523556 364130889 40000 0 1 (ep989 rfl) (ep992 rfl) rfl rfl)

noncomputable def ep994 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67)) 19083 400 0 1 57249 400 0 1

noncomputable def ep995 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67) 1 2 0 1 95415 1000 0 1 19083 400

noncomputable def ep996 := @ep995 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep986)

noncomputable def ep997 := ep996 (@Enclosure.Complex.IsNear.im_isNear qz67 Bool.false 3 2 0 1 Bool.false 95415 1000 0 1 qz613)

noncomputable def ep998 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67) 95415 1000 0 1 3 2 0 1 57249 400

noncomputable def ep999 := @ep998 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep986)

noncomputable def ep1000 := ep999 (@Enclosure.Complex.IsNear.re_isNear qz67 Bool.false 3 2 0 1 Bool.false 95415 1000 0 1 qz613)

noncomputable abbrev qz614 := (ep982 (BSN.ascPochhammer_succ_eval_c 1 2 qz64 rfl) (ep993 (@ep994 30532800 19083 100 0 1 (ep997 rfl) (ep1000 rfl) rfl rfl)))

noncomputable def ep1001 := @ep981 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 364130889 40000 0 1 Bool.false 19083 100 0 1 qz614)

noncomputable def ep1002 := @Enclosure.Complex.IsNear.of_eq qz66 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz61) Bool.false 5 2 0 1 Bool.false 95415 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 95415 1000 2 (@Eq.refl Real qz61))

noncomputable abbrev qz615 := (ep1002 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz61 Bool.false 5 2 0 1 Bool.false 95415 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz371))

noncomputable def ep1003 := ep1001 (@Enclosure.Complex.IsNear.re_isNear qz66 Bool.false 5 2 0 1 Bool.false 95415 1000 0 1 qz615)

noncomputable def ep1004 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66) 19083 100 0 1 95415 1000 0 1 364160889 20000

noncomputable def ep1005 := @ep1004 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 364130889 40000 0 1 Bool.false 19083 100 0 1 qz614)

noncomputable def ep1006 := ep1005 (@Enclosure.Complex.IsNear.im_isNear qz66 Bool.false 5 2 0 1 Bool.false 95415 1000 0 1 qz615)

noncomputable def ep1007 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) qz66 Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 (@ep980 13109192004000 3277298001 80000 0 1 (ep1003 rfl) (ep1006 rfl) rfl rfl)

noncomputable def ep1008 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66)) 6948709754787 8000000 0 1 19083 40 0 1

noncomputable def ep1009 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66) 364130889 40000 0 1 95415 1000 0 1 6948709754787 8000000

noncomputable def ep1010 := @ep1009 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 364130889 40000 0 1 Bool.false 19083 100 0 1 qz614)

noncomputable def ep1011 := ep1010 (@Enclosure.Complex.IsNear.im_isNear qz66 Bool.false 5 2 0 1 Bool.false 95415 1000 0 1 qz615)

noncomputable def ep1012 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66) 19083 100 0 1 5 2 0 1 19083 40

noncomputable def ep1013 := @ep1012 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 364130889 40000 0 1 Bool.false 19083 100 0 1 qz614)

noncomputable def ep1014 := ep1013 (@Enclosure.Complex.IsNear.re_isNear qz66 Bool.false 5 2 0 1 Bool.false 95415 1000 0 1 qz615)

noncomputable abbrev qz616 := (ep1007 (@ep1008 277795726191480 6944893154787 8000000 0 1 (ep1011 rfl) (ep1014 rfl) rfl rfl))

theorem EMRow27.d18 : Enclosure.Complex.IsNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 := ep979 (BSN.ascPochhammer_succ_eval_c 2 3 qz64 rfl) qz616

noncomputable def ep1015 := nat_lit 74446297036252599495477174088283804597

noncomputable def ep1016 := nat_lit 154777356022539777172764056616960000000

noncomputable def ep1017 := nat_lit 2248023750222110114798625423361637215549112273

noncomputable def ep1018 := nat_lit 388206592291452139407424595705534506598400000000

noncomputable abbrev qz68 := (Complex.Stirling.logGammaStirling 2 qz364)

noncomputable abbrev qz617 := (@HAdd.hAdd Complex Complex Complex qz808 qz809 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz810 (↑qz910) (2 : Complex))))

noncomputable abbrev qz386 := qz617

noncomputable abbrev qz69 := qz386

noncomputable abbrev qz387 := (@HMul.hMul Real Real Real qz0 (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1019 := Complex.re (@HMul.hMul Complex Complex Complex qz3 (Complex.exp (@HMul.hMul Complex Complex Complex qz3 Complex.I ↑(@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz387))) (zetaApproximant qz64 2 24))

noncomputable def ep1020 := @Enclosure.Real.IsNear.of_eq ep1019 (@HSub.hSub Real Real Real qz324 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz387)) (Complex.re (zetaApproximant qz64 2 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz387)) (Complex.im (zetaApproximant qz64 2 24))))

noncomputable def ep1021 := nat_lit 14889271964799951077476493941708625983

noncomputable def ep1022 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz387)) (Complex.re (zetaApproximant qz64 2 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz387)) (Complex.im (zetaApproximant qz64 2 24))) ep1021

noncomputable def ep1023 := nat_lit 30955471204507955434552811323392000000

noncomputable def ep1024 := nat_lit 2246066611504404955177404160417303271918851823

noncomputable def ep1025 := nat_lit 3488208175327328071978903295851

noncomputable def ep1026 := nat_lit 8598742001252209842931336478720000000

noncomputable def ep1027 := nat_lit 13047591451367730808141752962226290868403

noncomputable def ep1028 := nat_lit 2588043948609680929382830638036896710656000000

noncomputable def ep1029 := nat_lit 128028900232664627161904774979209015717255498177417381731074905735168000000

noncomputable def ep1030 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz387)) (Complex.re (zetaApproximant qz64 2 24)) 524287 524288 65679

noncomputable def ep1031 := nat_lit 28399086692593848555231188150209

noncomputable def ep1032 := nat_lit 59042875679984961384873984000000

noncomputable def ep1033 := nat_lit 63496237767469186421302940748373087

noncomputable def ep1034 := nat_lit 11452251381268283035017082306560000000

noncomputable def ep1035 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz387)) Bool.false 524287 524288 131358

noncomputable abbrev qz936 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42824649) qz269)

noncomputable def ep1036 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz387) qz936 Bool.false 42824649 524288 1

noncomputable def ep1037 := nat_lit 376689603252002468980186327

noncomputable def ep1038 := nat_lit 4611686018427387904000000

noncomputable def ep1039 := nat_lit 7335066713497441634394059023001

noncomputable def ep1040 := nat_lit 15087058751691161600000000000000000

noncomputable def ep1041 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz387) Bool.false ep1037 ep1038 ep1039 ep1040

noncomputable def ep1042 := nat_lit 628543867420315338991066327

noncomputable def ep1043 := nat_lit 1843689032556385634394059023001

noncomputable def ep1044 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz387 ep1042 ep1038 ep1043 ep1040 1431625743 26214400

noncomputable def ep1045 := nat_lit 9874691935489293522834196450508800

noncomputable def ep1046 := nat_lit 10374382190366030985966557

noncomputable def ep1047 := nat_lit 1331719749690713008479257697042673

noncomputable def ep1048 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true ep1046 138350580552821637120000 ep1047 ep348 Bool.false ep1042 ep1038

noncomputable def ep1049 := nat_lit 8234910117648809282286557

noncomputable def ep1050 := nat_lit 1281054253738660712694976184697073

noncomputable def ep1051 := nat_lit 656843974299960166639066327

noncomputable def ep1052 := nat_lit 310795987003853862759900603061593

noncomputable def ep1053 := @Enclosure.Complex.IsNear.subLitP qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))) Bool.true ep1049 138350580552821637120000 ep1050 ep348 Bool.false ep1051 ep1038 ep1052

noncomputable def ep1054 := nat_lit 2911802339076394188800000000000000000

noncomputable def ep1055 := nat_lit 23361031883365783622935640677925452251136

noncomputable def ep1056 := nat_lit 88459685221879456300196938076384191840256

noncomputable abbrev qz388 := (@HSub.hSub Complex Complex Complex qz577 qz605 qz546)

noncomputable abbrev qz389 := (Complex.log qz605)

noncomputable abbrev qz70 := (@HSub.hSub Complex Complex Complex qz577 (@HMul.hMul Complex Complex Complex qz253 qz388 qz389) qz364)

noncomputable def ep1057 := @Enclosure.Complex.IsNear.of_eq qz68 (@HAdd.hAdd Complex Complex Complex qz13 (@HAdd.hAdd Complex Complex Complex qz13 qz70 qz867) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k)))))) Bool.true ep1049

noncomputable def ep1058 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz13 qz70 qz867) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) Bool.true 53612835140918771209 900719925474099200

noncomputable def ep1059 := nat_lit 23058430092136939520000000

noncomputable def ep1060 := nat_lit 7417347627454540971929657811232855844454400

noncomputable def ep1061 := nat_lit 2366529822318285006154235996643654037510553600

noncomputable def ep1062 := @ep1058 2022762280733561273 10344800000000000000000 Bool.false 513165598809171677823 3602879701896396800 1104150002733781503 10344800000000000000000 Bool.false 21359996313975415843 138350580552821637120000 342273729475339 ep359 Bool.true 7992175779580974373673 ep1038 42688702149581643 ep1059 Bool.true ep1060 ep1049 138350580552821637120000 ep1050 ep348 Bool.false ep1061

noncomputable def ep1063 := @Enclosure.Complex.IsNear.addLitP qz70 qz867 Bool.true 54440540622360870409 900719925474099200 1983300000460123773 10344800000000000000000

noncomputable def ep1064 := nat_lit 7027141527590505179906048

noncomputable def ep1065 := @ep1063 Bool.false 513165598809171677823 3602879701896396800 1104150002733781503 10344800000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep1064 53612835140918771209 900719925474099200 2022762280733561273 10344800000000000000000 Bool.false 513165598809171677823 513165598809171677823 3602879701896396800

noncomputable abbrev qz71 := (@HMul.hMul Complex Complex Complex qz253 qz388 qz389)

noncomputable def ep1066 := @Enclosure.Complex.IsNear.subLitP qz71 qz57 Bool.true 50612480939095948809 900719925474099200 1983300000460123773 10344800000000000000000 Bool.false 685049982187394028159

noncomputable def ep1067 := nat_lit 2052662395236686711292000

noncomputable def ep1068 := @ep1066 3602879701896396800 1104150002733781503 10344800000000000000000 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1 Bool.true 217762162489443481636000 54440540622360870409 900719925474099200 1983300000460123773 10344800000000000000000 Bool.false ep1067 513165598809171677823 3602879701896396800 1104150002733781503 10344800000000000000000

noncomputable abbrev qz72 := qz388

noncomputable abbrev qz73 := qz389

noncomputable def ep1069 := @Enclosure.Complex.IsNear.mul qz72 qz73 Bool.true 50612480939095948809 900719925474099200 1983300000460123773 10344800000000000000000 Bool.false 685049982187394028159 3602879701896396800 1104150002733781503

noncomputable def ep1070 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.re qz73)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.im qz73)) 522738309959756595 36028797018963968 150000000426723 20689600000000000000 15920234672022465921 225179981368524800

noncomputable def ep1071 := nat_lit 455876700595217693022869573785878528

noncomputable def ep1072 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.re qz73) 15000 4000 0 1 34849220663983773 9007199254740992 50000000142241 25862000000000000000

noncomputable def ep1073 := @Enclosure.Complex.IsNear.re_isNear qz72 Bool.false 15000 4000 0 1 Bool.false 190830 4000 0 1

noncomputable def ep1074 := @Enclosure.Complex.IsNear.of_eq qz72 (Complex.mk (Enclosure.sfrac Bool.false 15000 4000) qz368) Bool.false 15000 4000 0 1 Bool.false 190830 4000 0

noncomputable def ep1075 := @Enclosure.Complex.IsNear.of_eq qz73 (Complex.log qz367) Bool.false 34849220663983773 9007199254740992 50000000142241 25862000000000000000 Bool.false 834262677357987 562949953421312 100000000012931 25862000000000000000

noncomputable def ep1076 := nat_lit 349427993474415459646076329243144561500000000

noncomputable def ep1077 := nat_lit 374791488353424522467541601762432800000000

noncomputable def ep1078 := nat_lit 720812218947507634011815220912300000000

noncomputable def ep1079 := BSN.log_dyadic_bound 3937088900 69473088900 3 2 ep1076 524288 258620 ep1077 ep1078 59487 73410177800 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3937088900) (BSN.artanhQ 69473088900) 0 2 ep1077 ep1076 ep1078 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1080 := @Enclosure.Real.IsNear.mulLit_ff qz321 (Real.log (Enclosure.sfrac Bool.false 36705088900 16000000)) 1 2 0 1 34849220663983773 4503599627370496 50000000142241 12931000000000000000 34849220663983773 9007199254740992 50000000142241 25862000000000000000 qz322 (BSN.isNear_log_sfrac 36705088900 16000000 34849220663983773 4503599627370496 50000000142241 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36705088900) qz582)) Bool.false 146168225627829795028992 18889465931478580854784 1000000002844820 258620000000000000000 34849220663983773 4503599627370496 50000000142241 12931000000000000000 (BSN.log_rat_reduce_isNear 36705088900 16000000 11 73410177800 65536000000 59487 524288 24973259072661432 36028797018963968 258620 1000000000000000 rfl rfl rfl rfl (ep1079 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1081 := BSN.arctan_dyadic_bound_f 17000 190830 1 0 524288 258620 0 1 1 0 1 1 46582 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 17000) (BSN.arctanEvenQ 190830) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 17000) (BSN.arctanOddQ 190830) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz618 := (@Nat.cast Real Real.instNatCast 190830)

noncomputable def ep1082 := @Enclosure.Real.IsNear.subLit_ff_p qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz583 qz618)) 884279719003555 562949953421312 1 2000000000000000 46582 524288 1 258620 437393910586664288256 834262677357987 562949953421312 100000000012931 25862000000000000000 qz332 (ep1081 rfl) rfl rfl

noncomputable abbrev qz619 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 190830) (@Nat.cast Real Real.instNatCast 17000)))

noncomputable def ep1083 := @Enclosure.Complex.IsNear.re_isNear qz73 Bool.false 34849220663983773 9007199254740992 50000000142241 25862000000000000000 Bool.false 834262677357987 562949953421312 100000000012931 25862000000000000000 (ep1075 (@congrArg Complex Complex qz57 qz367 Complex.log qz911) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz367) Bool.false 34849220663983773 9007199254740992 50000000142241 25862000000000000000 Bool.false 834262677357987 562949953421312 100000000012931 25862000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz367)) (@HMul.hMul Real Real Real qz0 qz321 (Real.log (Enclosure.sfrac Bool.false 36705088900 16000000))) Bool.false 34849220663983773 9007199254740992 50000000142241 25862000000000000000 (Enclosure.clog_re_eq 17000 190830 4000 36705088900 16000000 rfl rfl rfl) (ep1080 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz367)) qz619 Bool.false 834262677357987 562949953421312 100000000012931 25862000000000000000 (Enclosure.clog_im_eq 17000 190830 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz619 (@HSub.hSub Real Real Real qz324 qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz583 qz618))) Bool.false 834262677357987 562949953421312 100000000012931 25862000000000000000 (BSN.arctan_recip 190830 17000 rfl rfl) ep1082))))

noncomputable def ep1084 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.im qz73) 190830 4000 0 1 834262677357987 562949953421312 100000000012931 25862000000000000000

noncomputable def ep1085 := @Enclosure.Complex.IsNear.im_isNear qz72 Bool.false 15000 4000 0 1 Bool.false 190830 4000 0 1

noncomputable def ep1086 := @Enclosure.Complex.IsNear.im_isNear qz73 Bool.false 34849220663983773 9007199254740992 50000000142241 25862000000000000000 Bool.false 834262677357987 562949953421312 100000000012931 25862000000000000000 (ep1075 (@congrArg Complex Complex qz57 qz367 Complex.log qz911) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz367) Bool.false 34849220663983773 9007199254740992 50000000142241 25862000000000000000 Bool.false 834262677357987 562949953421312 100000000012931 25862000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz367)) (@HMul.hMul Real Real Real qz0 qz321 (Real.log (Enclosure.sfrac Bool.false 36705088900 16000000))) Bool.false 34849220663983773 9007199254740992 50000000142241 25862000000000000000 (Enclosure.clog_re_eq 17000 190830 4000 36705088900 16000000 rfl rfl rfl) (ep1080 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz367)) qz619 Bool.false 834262677357987 562949953421312 100000000012931 25862000000000000000 (Enclosure.clog_im_eq 17000 190830 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz619 (@HSub.hSub Real Real Real qz324 qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz583 qz618))) Bool.false 834262677357987 562949953421312 100000000012931 25862000000000000000 (BSN.arctan_recip 190830 17000 rfl rfl) ep1082))))

noncomputable abbrev qz390 := (@ep1074 1 (BSN.w_sub_half_mk qz61 Bool.false 95415 1000 4 (@Eq.refl Real qz61) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 15000 4000) (Enclosure.sfrac Bool.false 190830 4000) Bool.false 15000 4000 0 1 Bool.false 190830 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 15000 4000) (Enclosure.Real.IsNear.const Bool.false 190830 4000)))

noncomputable def ep1087 := @ep1070 1908300000246762273 10344800000000000000000 ep1071 50612480939095948809 900719925474099200 1983300000460123773 10344800000000000000000 (@ep1072 522738309959756595 36028797018963968 150000000426723 20689600000000000000 (ep1073 qz390) ep1083 rfl) (@ep1084 15920234672022465921 225179981368524800 1908300000246762273 10344800000000000000000 (ep1085 qz390) ep1086 rfl) rfl

noncomputable def ep1088 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.im qz73)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.re qz73)) 12513940160369805 2251799813685248 300000000038793 20689600000000000000 665027677930802340159 3602879701896396800

noncomputable def ep1089 := nat_lit 1542595422254656333759700317274898432

noncomputable def ep1090 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.im qz73) 15000 4000 0 1 834262677357987 562949953421312 100000000012931 25862000000000000000

noncomputable def ep1091 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.re qz73) 190830 4000 0 1 34849220663983773 9007199254740992 50000000142241 25862000000000000000

noncomputable def ep1092 := @ep1088 954150002714385003 10344800000000000000000 ep1089 685049982187394028159 3602879701896396800 1104150002733781503 10344800000000000000000 (@ep1090 12513940160369805 2251799813685248 300000000038793 20689600000000000000 (ep1073 qz390) ep1086 rfl) (@ep1091 665027677930802340159 3602879701896396800 954150002714385003 10344800000000000000000 (ep1085 qz390) ep1083 rfl) rfl

noncomputable def ep1093 := ep1068 (@ep1069 10344800000000000000000 (ep1087 rfl) (ep1092 rfl)) qz63 rfl rfl rfl rfl rfl rfl

noncomputable def ep1094 := @ep1065 1104150002733781503 10344800000000000000000 (ep1093 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz24 (↑qz251) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep392 131072 1 262144 (ep394 rfl) (ep396 rfl) rfl rfl) (@ep397 1 0 1 (ep399 rfl) (ep401 rfl) rfl rfl))

noncomputable abbrev qz74 := (@HPow.hPow Complex Int Complex qz580 qz364 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz330 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz581 (@Nat.cast Int instNatCastInt 2))))

noncomputable def ep1095 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz74)) Bool.false 21359996313975415843 138350580552821637120000 342273729475339 ep359

noncomputable def ep1096 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz74) Bool.false 15913751 103079215104 17 103079215104 Bool.true

noncomputable def ep1097 := nat_lit 733923884889639670349482164224

noncomputable def ep1098 := nat_lit 27460906877746871614991694718566400

noncomputable def ep1099 := @ep1096 5954551183 3435973836800 6361 3435973836800 Bool.false 307094066045281 46116860184273879040000 18523075339 ep359 Bool.true 112469161252133673 ep1038 753759181643 ep1059 Bool.false ep1097 21359996313975415843 138350580552821637120000 342273729475339 ep359 Bool.true ep1098 7992175779580974373673 ep1038 42688702149581643

noncomputable abbrev qz75 := (@HPow.hPow Complex Int Complex qz580 qz364 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz330 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz581 (@Nat.cast Int instNatCastInt 1))))

noncomputable def ep1100 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz75)) Bool.false 15913751 103079215104 17 103079215104

noncomputable def ep1101 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz75) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1102 := @ep1101 0 1 0 1 Bool.false 15913751 103079215104 17 103079215104 Bool.true 5954551183 3435973836800 6361 3435973836800 Bool.false 15913751 15913751 103079215104 17 103079215104 Bool.true 5954551183 5954551183 3435973836800 6361

noncomputable def ep1103 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz263 qz263) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1104 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz75 Bool.false 15913751 103079215104 17 103079215104 Bool.true 5954551183 3435973836800 6361 3435973836800

noncomputable def ep1105 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz75)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz75)) 15913751 103079215104 17 103079215104 0 1 0

noncomputable def ep1106 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz75) 1 12 0 1 15913751 8589934592 17 8589934592 15913751

noncomputable def ep1107 := @Enclosure.Complex.IsNear.re_isNear qz75 Bool.false 15913751 8589934592 17 8589934592 Bool.true 17863653549 858993459200 19083 858993459200

noncomputable def ep1108 := @Enclosure.Complex.IsNear.of_eq qz75 (@Inv.inv Complex Complex.instInv qz58) Bool.false 15913751 8589934592 17 8589934592 Bool.true 17863653549 858993459200 19083

noncomputable def ep1109 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz58) Bool.false 15913751 8589934592 17 8589934592 Bool.true 17863653549 858993459200 19083

noncomputable def ep1110 := @Enclosure.Real.IsNear.mulLit_ff qz59 (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz58)) 17000 4000 0 1 936103 2147483648 1 2147483648

noncomputable def ep1111 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz58)) Bool.false 936103 2147483648 1 2147483648 936103 2147483648 1

noncomputable def ep1112 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz58) (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 qz59 qz59) (@HMul.hMul Real Real Real qz0 qz60 qz60)) Bool.false 367050889 160000 0 1

noncomputable def ep1113 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz59 qz59) (@HMul.hMul Real Real Real qz0 qz60 qz60) 289 16 0 1 364160889 160000

noncomputable def ep1114 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz59 17000 4000 0 1 17000 4000 0 1

noncomputable def ep1115 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz60 190830 4000 0 1 190830 4000 0 1

noncomputable def ep1116 := @ep1113 0 1 5872814224 367050889 160000 0 1 (@ep1114 289 16 0 1 (ep762 qz62) (ep762 qz62) rfl) (@ep1115 364160889 160000 0 1 (ep767 qz62) (ep767 qz62) rfl)

noncomputable def ep1117 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz58) 367050889 160000 0 1 468051 468052 1073741824 (ep1112 (Enclosure.Complex.normSq_eq_mul_add_mul qz58) (ep1116 rfl rfl)) rfl

noncomputable def ep1118 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz58)) (@HMul.hMul Real Real Real qz0 qz59 (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz58))) Bool.false 15913751 8589934592 17 8589934592 (Enclosure.Complex.inv_re_eq_mul qz58) (@ep1110 15913751 8589934592 17 8589934592 (ep762 qz62) (@ep1111 2147483648 (ep1117 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1119 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz58)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz60) (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz58))) Bool.true 17863653549 858993459200 19083 858993459200 (Enclosure.Complex.inv_im_eq_mul qz58)

noncomputable def ep1120 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz60) (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz58)) 190830 4000 0 1 936103 2147483648 1

noncomputable def ep1121 := @ep1120 2147483648 17863653549 858993459200 19083 858993459200 (@Enclosure.Real.IsNear.neg qz60 Bool.false 190830 4000 0 1 (ep767 qz62)) (@ep1111 2147483648 (ep1117 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1122 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz75) 0 1 0 1 17863653549 858993459200 19083 858993459200 0

noncomputable def ep1123 := @Enclosure.Complex.IsNear.im_isNear qz75 Bool.false 15913751 8589934592 17 8589934592 Bool.true 17863653549 858993459200 19083 858993459200

noncomputable abbrev qz620 := (@ep1108 858993459200 (BSN.zpow_one_sub_two_mul qz57 1 1 rfl rfl) (@ep1109 858993459200 ep1118 (ep1119 ep1121)))

noncomputable def ep1124 := @ep1105 1 15913751 15913751 103079215104 17 103079215104 (@ep1106 103079215104 17 103079215104 ep416 (ep1107 qz620) rfl) (@ep1122 1 0 1 ep433 (ep1123 qz620) rfl) rfl

noncomputable def ep1125 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz75)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz75)) 5954551183 3435973836800 6361 3435973836800 0 1 0

noncomputable def ep1126 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz75) 1 12 0 1 17863653549 858993459200 19083 858993459200 5954551183

noncomputable def ep1127 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz75) 0 1 0 1 15913751 8589934592 17 8589934592 0

noncomputable def ep1128 := @ep1125 1 5954551183 5954551183 3435973836800 6361 3435973836800 (@ep1126 3435973836800 6361 3435973836800 ep416 (ep1123 qz620) rfl) (@ep1127 1 0 1 ep433 (ep1107 qz620) rfl) rfl

noncomputable def ep1129 := @ep1102 3435973836800 (@ep1103 0 1 0 1 (BSN.stirling_sum_base qz57) qz338) (ep1104 (ep1124 rfl) (ep1128 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1130 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz74 Bool.false 307094066045281 46116860184273879040000 18523075339 ep359 Bool.true 112469161252133673 ep1038 753759181643 ep1059

noncomputable def ep1131 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz74)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz74)) 307094066045281 46116860184273879040000 18523075339 ep359 0 1 0

noncomputable def ep1132 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz74) 1 360 0 1 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 307094066045281

noncomputable def ep1133 := @Enclosure.Complex.IsNear.re_isNear qz74 Bool.true 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 Bool.false 1012222451269203057 115292150460684697600000 6783832634787 576460752303423488000000

noncomputable def ep1134 := @Enclosure.Complex.IsNear.of_eq qz74 (@Inv.inv Complex Complex.instInv qz55) Bool.true 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 Bool.false 1012222451269203057 115292150460684697600000 6783832634787

noncomputable def ep1135 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz55) Bool.true 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 Bool.false 1012222451269203057 115292150460684697600000 6783832634787

noncomputable abbrev qz76 := (Complex.re qz363)

noncomputable def ep1136 := @Enclosure.Real.IsNear.mulLit_tf qz76 (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz55)) 18523075339 640000 0 1 746055 9007199254740992 1 9007199254740992

noncomputable def ep1137 := @Enclosure.Complex.IsNear.re_isNear qz55 Bool.true 18523075339 640000 0 1 Bool.true 6783832634787 64000000 0 1

noncomputable def ep1138 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz55)) Bool.false 746055 9007199254740992 1 9007199254740992 746055 9007199254740992 1

noncomputable def ep1139 := nat_lit 49451428416943830171745369

noncomputable abbrev qz77 := (Complex.im qz363)

noncomputable def ep1140 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz55) (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 qz76 qz76) (@HMul.hMul Real Real Real qz0 qz77 qz77)) Bool.false ep1139 4096000000000000 0 1

noncomputable def ep1141 := nat_lit 46020385216801130522535369

noncomputable def ep1142 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz76 qz76) (@HMul.hMul Real Real Real qz0 qz77 qz77) 343104320014269964921 409600000000 0 1 ep1141 4096000000000000

noncomputable def ep1143 := nat_lit 20255305079580192838346903142400000000

noncomputable def ep1144 := @Enclosure.Real.IsNear.mulLit_tt qz76 qz76 18523075339 640000 0 1 18523075339 640000 0 1

noncomputable def ep1145 := @Enclosure.Real.IsNear.mulLit_tt qz77 qz77 6783832634787 64000000 0 1 6783832634787 64000000 0 1

noncomputable def ep1146 := @Enclosure.Complex.IsNear.im_isNear qz55 Bool.true 18523075339 640000 0 1 Bool.true 6783832634787 64000000 0 1

noncomputable def ep1147 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz55) ep1139 4096000000000000 0 1 373027 373028 4503599627370496 (ep1140 (Enclosure.Complex.normSq_eq_mul_add_mul qz55) (@ep1142 0 1 ep1143 ep1139 4096000000000000 0 1 (@ep1144 343104320014269964921 409600000000 0 1 (ep1137 EMRow27.d15) (ep1137 EMRow27.d15) rfl) (@ep1145 ep1141 4096000000000000 0 1 (ep1146 EMRow27.d15) (ep1146 EMRow27.d15) rfl) rfl rfl)) rfl

noncomputable def ep1148 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz55)) (@HMul.hMul Real Real Real qz0 qz76 (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz55))) Bool.true 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 (Enclosure.Complex.inv_re_eq_mul qz55) (@ep1136 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 (ep1137 EMRow27.d15) (@ep1138 9007199254740992 (ep1147 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1149 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz55)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz77) (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz55))) Bool.false 1012222451269203057 115292150460684697600000 6783832634787 576460752303423488000000 (Enclosure.Complex.inv_im_eq_mul qz55)

noncomputable def ep1150 := @Enclosure.Real.IsNear.mulLit_ff (@Neg.neg Real Real.instNeg qz77) (@Inv.inv Real Real.instInv (@DFunLike.coe qz335 Complex (fun (x : Complex) => Real) qz336 Complex.normSq qz55)) 6783832634787 64000000 0 1 746055 9007199254740992 1

noncomputable def ep1151 := @ep1150 9007199254740992 1012222451269203057 115292150460684697600000 6783832634787 576460752303423488000000 (@Enclosure.Real.IsNear.neg qz77 Bool.true 6783832634787 64000000 0 1 (ep1146 EMRow27.d15)) (@ep1138 9007199254740992 (ep1147 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1152 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz74) 0 1 0 1 1012222451269203057 115292150460684697600000 6783832634787 576460752303423488000000 0

noncomputable def ep1153 := @Enclosure.Complex.IsNear.im_isNear qz74 Bool.true 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 Bool.false 1012222451269203057 115292150460684697600000 6783832634787 576460752303423488000000

noncomputable abbrev qz621 := (@ep1134 576460752303423488000000 (BSN.zpow_one_sub_two_mul qz57 2 3 rfl rfl) (@ep1135 576460752303423488000000 ep1148 (ep1149 ep1151)))

noncomputable def ep1154 := @ep1131 1 307094066045281 307094066045281 46116860184273879040000 18523075339 ep359 (@ep1132 46116860184273879040000 18523075339 ep359 ep445 (ep1133 qz621) rfl) (@ep1152 1 0 1 ep466 (ep1153 qz621) rfl) rfl

noncomputable def ep1155 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz74)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz74)) 112469161252133673 ep1038 753759181643 ep1059 0 1 0

noncomputable def ep1156 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz74) 1 360 0 1 1012222451269203057 115292150460684697600000 6783832634787 576460752303423488000000 112469161252133673

noncomputable def ep1157 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz74) 0 1 0 1 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 0

noncomputable def ep1158 := @ep1155 1 112469161252133673 112469161252133673 ep1038 753759181643 ep1059 (@ep1156 ep1038 753759181643 ep1059 ep445 (ep1153 qz621) rfl) (@ep1157 1 0 1 ep466 (ep1133 qz621) rfl) rfl

noncomputable def ep1159 := @ep1099 ep1059 (@ep1100 Bool.true 5954551183 3435973836800 6361 3435973836800 (BSN.stirling_sum_succ qz57 0 1 rfl) (ep1129 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1130 (ep1154 rfl) (ep1158 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1160 := @ep1062 ep1051 ep1038 ep1052 ep1054 (ep1094 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1095 Bool.true 7992175779580974373673 ep1038 42688702149581643 ep1059 (BSN.stirling_sum_succ qz57 1 2 rfl) (ep1159 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1161 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz61 4) Bool.false 34822136600215197 2251799813685248 50000000142241 6465500000000000000 Bool.false 863650722645411 140737488355328

noncomputable abbrev qz937 := (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz548)

noncomputable def ep1162 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 4) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz61 3) (Complex.log qz937)) Bool.false 34822136600215197 2251799813685248 50000000142241 6465500000000000000 Bool.false 863650722645411 140737488355328 100000000012931 6465500000000000000

noncomputable def ep1163 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 3) (Complex.log qz937) Bool.false 104454074654571479 9007199254740992 150000000426723 25862000000000000000 Bool.false 2608613878763753 562949953421312 300000000038793 25862000000000000000 Bool.false

noncomputable def ep1164 := nat_lit 1254599691335789373206118789021696

noncomputable def ep1165 := nat_lit 1944768536342066285499465596928

noncomputable abbrev qz938 := (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz549)

noncomputable def ep1166 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 3) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz61 2) (Complex.log qz938)) Bool.false 104454074654571479 9007199254740992 150000000426723 25862000000000000000 Bool.false 2608613878763753 562949953421312 300000000038793 25862000000000000000

noncomputable def ep1167 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 2) (Complex.log qz938) Bool.false 34815225997835933 4503599627370496 50000000142241 12931000000000000000 Bool.false 875432086373795 281474976710656 100000000012931 12931000000000000000 Bool.false

noncomputable def ep1168 := nat_lit 470419331691658083512458447683584

noncomputable def ep1169 := nat_lit 734259530772121389971661651968

noncomputable abbrev qz939 := (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz572)

noncomputable def ep1170 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 2) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz61 1) (Complex.log qz939)) Bool.false 34815225997835933 4503599627370496 50000000142241 12931000000000000000 Bool.false 875432086373795 281474976710656 100000000012931 12931000000000000000

noncomputable def ep1171 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 1) (Complex.log qz939) Bool.false 34813744234118813 9007199254740992 50000000142241 25862000000000000000 Bool.false 881330150213027 562949953421312 100000000012931 25862000000000000000 Bool.false

noncomputable def ep1172 := nat_lit 627175355322694050549164851331072

noncomputable def ep1173 := nat_lit 985648904495299757711902638080

noncomputable abbrev qz940 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1174 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 1) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz61 0) qz940) Bool.false 34813744234118813 9007199254740992 50000000142241 25862000000000000000 Bool.false 881330150213027 562949953421312 100000000012931 25862000000000000000

noncomputable def ep1175 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 0) qz940 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep1176 := @Enclosure.Complex.IsNear.of_eq qz940 (Complex.log (Complex.mk qz589 qz368)) Bool.false 34813744234118813 9007199254740992 50000000142241 25862000000000000000 Bool.false 881330150213027 562949953421312 100000000012931 25862000000000000000

noncomputable def ep1177 := BSN.log_dyadic_bound 3649088900 69185088900 2 1 14359729578302709630000 524288 258620 13315849800103210000 13315849800103210000 55357 72834177800 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 3649088900) (BSN.artanhQ 69185088900) 0 1 13315849800103210000 14359729578302709630000 13315849800103210000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1178 := @Enclosure.Real.IsNear.mulLit_ff qz321 (Real.log (Enclosure.sfrac Bool.false 36417088900 16000000)) 1 2 0 1 34813744234118813 4503599627370496 50000000142241 12931000000000000000 34813744234118813 9007199254740992 50000000142241 25862000000000000000 qz322 (BSN.isNear_log_sfrac 36417088900 16000000 34813744234118813 4503599627370496 50000000142241 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36417088900) qz582)) Bool.false 146019426696141473841152 18889465931478580854784 1000000002844820 258620000000000000000 34813744234118813 4503599627370496 50000000142241 12931000000000000000 (BSN.log_rat_reduce_isNear 36417088900 16000000 11 72834177800 65536000000 55357 524288 24973259072661432 36028797018963968 258620 1000000000000000 rfl rfl rfl rfl (ep1177 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1179 := BSN.arctan_dyadic_bound_f 1000 190830 1 0 524288 258620 0 1 1 0 1 1 2747 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 190830) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 190830) 0 0 rfl) rfl rfl rfl

noncomputable def ep1180 := @Enclosure.Real.IsNear.subLit_ff_p qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz872 qz618)) 884279719003555 562949953421312 1 2000000000000000 2747 524288 1 258620 462070821794887499776 881330150213027 562949953421312 100000000012931 25862000000000000000 qz332 (ep1179 rfl) rfl rfl

noncomputable abbrev qz941 := (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable def ep1181 := @ep1175 34813744234118813 9007199254740992 50000000142241 25862000000000000000 Bool.false 881330150213027 562949953421312 100000000012931 25862000000000000000 Bool.false 34813744234118813 34813744234118813 9007199254740992 50000000142241 25862000000000000000 Bool.false 881330150213027 881330150213027 562949953421312 100000000012931 25862000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 0) (Complex.mk qz263 qz263) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz61) qz338) (ep1176 (@congrArg Complex Complex qz941 (Complex.mk qz589 qz368) Complex.log (BSN.w_shift_mk qz61 Bool.false 95415 1000 0 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz589 qz368)) Bool.false 34813744234118813 9007199254740992 50000000142241 25862000000000000000 Bool.false 881330150213027 562949953421312 100000000012931 25862000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz589 qz368))) (@HMul.hMul Real Real Real qz0 qz321 (Real.log (Enclosure.sfrac Bool.false 36417088900 16000000))) Bool.false 34813744234118813 9007199254740992 50000000142241 25862000000000000000 (Enclosure.clog_re_eq 1000 190830 4000 36417088900 16000000 rfl rfl rfl) (ep1178 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz589 qz368))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz872)) Bool.false 881330150213027 562949953421312 100000000012931 25862000000000000000 (Enclosure.clog_im_eq 1000 190830 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz872)) (@HSub.hSub Real Real Real qz324 qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz872 qz618))) Bool.false 881330150213027 562949953421312 100000000012931 25862000000000000000 (BSN.arctan_recip 190830 1000 rfl rfl) ep1180)))) rfl rfl

noncomputable def ep1182 := @Enclosure.Complex.IsNear.of_eq (Complex.log qz939) (Complex.log (Complex.mk qz590 qz368)) Bool.false 34816707761553053 9007199254740992 50000000142241 25862000000000000000 Bool.false 869534022534563 562949953421312 100000000012931 25862000000000000000

noncomputable def ep1183 := BSN.log_dyadic_bound 3673088900 69209088900 2 1 14369693959104309630000 524288 258620 13491582067303210000 13491582067303210000 55702 72882177800 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 3673088900) (BSN.artanhQ 69209088900) 0 1 13491582067303210000 14369693959104309630000 13491582067303210000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1184 := @Enclosure.Real.IsNear.mulLit_ff qz321 (Real.log (Enclosure.sfrac Bool.false 36441088900 16000000)) 1 2 0 1 34816707761553053 4503599627370496 50000000142241 12931000000000000000 34816707761553053 9007199254740992 50000000142241 25862000000000000000 qz322 (BSN.isNear_log_sfrac 36441088900 16000000 34816707761553053 4503599627370496 50000000142241 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36441088900) qz582)) Bool.false 146031856631113016410112 18889465931478580854784 1000000002844820 258620000000000000000 34816707761553053 4503599627370496 50000000142241 12931000000000000000 (BSN.log_rat_reduce_isNear 36441088900 16000000 11 72882177800 65536000000 55702 524288 24973259072661432 36028797018963968 258620 1000000000000000 rfl rfl rfl rfl (ep1183 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1185 := BSN.arctan_dyadic_bound_f 5000 190830 1 0 524288 258620 0 1 1 0 1 1 13733 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 190830) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 190830) 0 0 rfl) rfl rfl rfl

noncomputable def ep1186 := @Enclosure.Real.IsNear.subLit_ff_p qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz874 qz618)) 884279719003555 562949953421312 1 2000000000000000 13733 524288 1 258620 455886253606600966144 869534022534563 562949953421312 100000000012931 25862000000000000000 qz332 (ep1185 rfl) rfl rfl

noncomputable def ep1187 := @ep1171 34816707761553053 9007199254740992 50000000142241 25862000000000000000 Bool.false 869534022534563 562949953421312 100000000012931 25862000000000000000 Bool.false ep1172 34815225997835933 4503599627370496 50000000142241 12931000000000000000 Bool.false ep1173 875432086373795 281474976710656 100000000012931 12931000000000000000 (ep1174 (BSN.log_sum_c_succ qz61 0 1 rfl) (ep1181 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1182 (@congrArg Complex Complex qz939 (Complex.mk qz590 qz368) Complex.log (BSN.w_shift_mk qz61 Bool.false 95415 1000 1 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz590 qz368)) Bool.false 34816707761553053 9007199254740992 50000000142241 25862000000000000000 Bool.false 869534022534563 562949953421312 100000000012931 25862000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz590 qz368))) (@HMul.hMul Real Real Real qz0 qz321 (Real.log (Enclosure.sfrac Bool.false 36441088900 16000000))) Bool.false 34816707761553053 9007199254740992 50000000142241 25862000000000000000 (Enclosure.clog_re_eq 5000 190830 4000 36441088900 16000000 rfl rfl rfl) (ep1184 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz590 qz368))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz874)) Bool.false 869534022534563 562949953421312 100000000012931 25862000000000000000 (Enclosure.clog_im_eq 5000 190830 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz874)) (@HSub.hSub Real Real Real qz324 qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz874 qz618))) Bool.false 869534022534563 562949953421312 100000000012931 25862000000000000000 (BSN.arctan_recip 190830 5000 rfl rfl) ep1186)))) rfl rfl

noncomputable def ep1188 := @Enclosure.Complex.IsNear.of_eq (Complex.log qz938) (Complex.log (Complex.mk qz591 qz368)) Bool.false 34823622658899613 9007199254740992 50000000142241 25862000000000000000 Bool.false 857749706016163 562949953421312 100000000012931 25862000000000000000

noncomputable def ep1189 := BSN.log_dyadic_bound 3729088900 69265088900 2 1 14392957620974709630000 524288 258620 13906104024103210000 13906104024103210000 56507 72994177800 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 3729088900) (BSN.artanhQ 69265088900) 0 1 13906104024103210000 14392957620974709630000 13906104024103210000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1190 := @Enclosure.Real.IsNear.mulLit_ff qz321 (Real.log (Enclosure.sfrac Bool.false 36497088900 16000000)) 1 2 0 1 34823622658899613 4503599627370496 50000000142241 12931000000000000000 34823622658899613 9007199254740992 50000000142241 25862000000000000000 qz322 (BSN.isNear_log_sfrac 36497088900 16000000 34823622658899613 4503599627370496 50000000142241 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36497088900) qz582)) Bool.false 146060859812713282404352 18889465931478580854784 1000000002844820 258620000000000000000 34823622658899613 4503599627370496 50000000142241 12931000000000000000 (BSN.log_rat_reduce_isNear 36497088900 16000000 11 72994177800 65536000000 56507 524288 24973259072661432 36028797018963968 258620 1000000000000000 rfl rfl rfl rfl (ep1189 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1191 := BSN.arctan_dyadic_bound_f 9000 190830 1 0 524288 258620 0 1 1 0 1 1 24708 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 190830) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 190830) 0 0 rfl) rfl rfl rfl

noncomputable def ep1192 := @Enclosure.Real.IsNear.subLit_ff_p qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz875 qz618)) 884279719003555 562949953421312 1 2000000000000000 24708 524288 1 258620 449707877867802066944 857749706016163 562949953421312 100000000012931 25862000000000000000 qz332 (ep1191 rfl) rfl rfl

noncomputable def ep1193 := @ep1167 34823622658899613 9007199254740992 50000000142241 25862000000000000000 Bool.false 857749706016163 562949953421312 100000000012931 25862000000000000000 Bool.false ep1168 104454074654571479 9007199254740992 150000000426723 25862000000000000000 Bool.false ep1169 2608613878763753 562949953421312 300000000038793 25862000000000000000 (ep1170 (BSN.log_sum_c_succ qz61 1 2 rfl) (ep1187 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1188 (@congrArg Complex Complex qz938 (Complex.mk qz591 qz368) Complex.log (BSN.w_shift_mk qz61 Bool.false 95415 1000 2 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz591 qz368)) Bool.false 34823622658899613 9007199254740992 50000000142241 25862000000000000000 Bool.false 857749706016163 562949953421312 100000000012931 25862000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz591 qz368))) (@HMul.hMul Real Real Real qz0 qz321 (Real.log (Enclosure.sfrac Bool.false 36497088900 16000000))) Bool.false 34823622658899613 9007199254740992 50000000142241 25862000000000000000 (Enclosure.clog_re_eq 9000 190830 4000 36497088900 16000000 rfl rfl rfl) (ep1190 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz591 qz368))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz875)) Bool.false 857749706016163 562949953421312 100000000012931 25862000000000000000 (Enclosure.clog_im_eq 9000 190830 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz875)) (@HSub.hSub Real Real Real qz324 qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz875 qz618))) Bool.false 857749706016163 562949953421312 100000000012931 25862000000000000000 (BSN.arctan_recip 190830 9000 rfl rfl) ep1192)))) rfl rfl

noncomputable def ep1194 := @Enclosure.Complex.IsNear.of_eq (Complex.log qz937) (Complex.log (Complex.mk qz592 qz368)) Bool.false 34834471746289309 9007199254740992 50000000142241 25862000000000000000 Bool.false 845989011817891 562949953421312 100000000012931 25862000000000000000

noncomputable def ep1195 := nat_lit 347019990971142435529317874586344561500000000

noncomputable def ep1196 := nat_lit 351038542685386520059200984802432800000000

noncomputable def ep1197 := nat_lit 636869357839730811140083860912300000000

noncomputable def ep1198 := BSN.log_dyadic_bound 3817088900 69353088900 3 2 ep1195 524288 258620 ep1196 ep1197 57770 73170177800 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3817088900) (BSN.artanhQ 69353088900) 0 2 ep1196 ep1195 ep1197 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1199 := @Enclosure.Real.IsNear.mulLit_ff qz321 (Real.log (Enclosure.sfrac Bool.false 36585088900 16000000)) 1 2 0 1 34834471746289309 4503599627370496 50000000142241 12931000000000000000 34834471746289309 9007199254740992 50000000142241 25862000000000000000 qz322 (BSN.isNear_log_sfrac 36585088900 16000000 34834471746289309 4503599627370496 50000000142241 12931000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36585088900) qz582)) Bool.false 146106364183348233895936 18889465931478580854784 1000000002844820 258620000000000000000 34834471746289309 4503599627370496 50000000142241 12931000000000000000 (BSN.log_rat_reduce_isNear 36585088900 16000000 11 73170177800 65536000000 57770 524288 24973259072661432 36028797018963968 258620 1000000000000000 rfl rfl rfl rfl (ep1198 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1200 := BSN.arctan_dyadic_bound_f 13000 190830 1 0 524288 258620 0 1 1 0 1 1 35661 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 13000) (BSN.arctanEvenQ 190830) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 13000) (BSN.arctanOddQ 190830) 0 0 rfl) rfl rfl rfl

noncomputable def ep1201 := @Enclosure.Real.IsNear.subLit_ff_p qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz876 qz618)) 884279719003555 562949953421312 1 2000000000000000 35661 524288 1 258620 443541887027978436608 845989011817891 562949953421312 100000000012931 25862000000000000000 qz332 (ep1200 rfl) rfl rfl

noncomputable def ep1202 := @ep1163 34834471746289309 9007199254740992 50000000142241 25862000000000000000 Bool.false 845989011817891 562949953421312 100000000012931 25862000000000000000 Bool.false ep1164 34822136600215197 2251799813685248 50000000142241 6465500000000000000 Bool.false ep1165 863650722645411 140737488355328 100000000012931 6465500000000000000 (ep1166 (BSN.log_sum_c_succ qz61 2 3 rfl) (ep1193 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1194 (@congrArg Complex Complex qz937 (Complex.mk qz592 qz368) Complex.log (BSN.w_shift_mk qz61 Bool.false 95415 1000 3 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz592 qz368)) Bool.false 34834471746289309 9007199254740992 50000000142241 25862000000000000000 Bool.false 845989011817891 562949953421312 100000000012931 25862000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz592 qz368))) (@HMul.hMul Real Real Real qz0 qz321 (Real.log (Enclosure.sfrac Bool.false 36585088900 16000000))) Bool.false 34834471746289309 9007199254740992 50000000142241 25862000000000000000 (Enclosure.clog_re_eq 13000 190830 4000 36585088900 16000000 rfl rfl rfl) (ep1199 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz592 qz368))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz876)) Bool.false 845989011817891 562949953421312 100000000012931 25862000000000000000 (Enclosure.clog_im_eq 13000 190830 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz876)) (@HSub.hSub Real Real Real qz324 qz331 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz876 qz618))) Bool.false 845989011817891 562949953421312 100000000012931 25862000000000000000 (BSN.arctan_recip 190830 13000 rfl rfl) ep1201)))) rfl rfl

noncomputable def ep1203 := @ep1053 ep1054 Bool.false 34822136600215197 2251799813685248 50000000142241 6465500000000000000 Bool.false 863650722645411 140737488355328 100000000012931 6465500000000000000 Bool.true ep1055 ep1046 138350580552821637120000 ep1047 ep348 Bool.false ep1056 ep1042 ep1038 ep1043 ep1040 (@ep1057 138350580552821637120000 ep1050 ep348 Bool.false ep1051 ep1038 ep1052 ep1054 (BSN.logGammaStirling_unfold 2 qz57) (ep1160 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1161 100000000012931 6465500000000000000 (BSN.log_sum_c_eq qz61 4) (ep1162 (BSN.log_sum_c_succ qz61 3 4 rfl) (ep1202 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable def ep1204 := @Enclosure.Real.IsNear.mulLit_ff (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Real.log Real.pi) 95415 2000 0 1 75021 65536 1 131072 1431625743 26214400 19083 52428800 (@Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Enclosure.sfrac Bool.false 95415 2000) Bool.false 95415 2000 0 1 (BSN.t_half_eq qz61 Bool.false 95415 1000 (@Eq.refl Real qz61)) (Enclosure.Real.IsNear.const Bool.false 95415 2000)) EMRow27.d6 rfl

noncomputable def ep1205 := @ep1044 19083 52428800 ep1045 ep1037 ep1038 ep1039 ep1040 (@ep1048 ep1043 ep1040 (ep1203 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1204 rfl rfl

noncomputable def ep1206 := BSN.cos_dyadic_bound_f 136072 1073741824 1 0 524288 258873 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 136072) qz273 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 136072) qz274 0 0 rfl) rfl rfl

noncomputable def ep1207 := @ep1036 2048 Bool.false 524287 524288 1 129310 (@ep1041 42824649 524288 1 2048 ep1205 rfl) (Enclosure.sfrac_false_div 42824649 524288) (BSN.cos_reduce0 qz936 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9575258463139790848) qz272) 226375608064910080 72057594037927936 Bool.false 524287 524288 13 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 42824649 524288 226375608064910080 72057594037927936 13 9575258463139790848 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 9575258463139790848 75557863725914323419136 136072 1073741824 258873 258620 (ep1206 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1208 := nat_lit 317109834120666188361718481441

noncomputable def ep1209 := nat_lit 98404792799974935641456640000000

noncomputable def ep1210 := nat_lit 63404125692504189977812939382402591

noncomputable abbrev qz78 := (@HPow.hPow Complex Complex Complex qz815 qz593 (@Neg.neg Complex Complex.instNeg qz369))

noncomputable abbrev qz79 := (@HAdd.hAdd Complex Complex Complex qz261 (@HDiv.hDiv Complex Complex Complex qz329 qz593 (@HSub.hSub Complex Complex Complex qz577 qz369 (1 : Complex))) qz328)

noncomputable def ep1211 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz64 2 24) (@HAdd.hAdd Complex Complex Complex qz13 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz65) (@HMul.hMul Complex Complex Complex qz3 qz78 (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) Bool.false ep1031 ep1032 ep1033

noncomputable def ep1212 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz65) (@HMul.hMul Complex Complex Complex qz3 qz78 (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) Bool.false 31213327361 68719476736 24177097019959 4443057768366080

noncomputable def ep1213 := nat_lit 1581004040216126072117204150209

noncomputable def ep1214 := nat_lit 1178301072330228008723600460373087

noncomputable def ep1215 := nat_lit 10344756806864478033006601518559

noncomputable def ep1216 := nat_lit 1185138569282074715390358134402591

noncomputable def ep1217 := nat_lit 1951570377295350159287916845189926249037824

noncomputable def ep1218 := nat_lit 43583243737223878295889814276732094513152

noncomputable def ep1219 := @ep1212 Bool.false 14891101861 137438953472 6034677044591 1110764442091520 Bool.false ep1213 ep1032 ep1214 ep1034 Bool.true ep1215 ep1209 ep1216 ep1034 Bool.false ep1217 ep1031 ep1032 ep1033 ep1034 Bool.false ep1218 ep1208 ep1209

noncomputable def ep1220 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz65) (BSN.headSumC qz64 24) Bool.false 31213327361 68719476736 24177097019959 4443057768366080 Bool.false 14891101861 137438953472 6034677044591

noncomputable abbrev qz942 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 23) qz65)

noncomputable def ep1221 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 24) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 23) qz942) Bool.false 31213327361 68719476736 24177097019959 4443057768366080 Bool.false 14891101861 137438953472 6034677044591 1110764442091520

noncomputable def ep1222 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 23) qz942 Bool.false 167879322019 274877906944 93911816384763 17772231073464320 Bool.true 8083857653 274877906944 93761312734383 17772231073464320 Bool.true

noncomputable abbrev qz943 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 22) qz65)

noncomputable def ep1223 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 23) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 22) qz943) Bool.false 167879322019 274877906944 93911816384763 17772231073464320 Bool.true 8083857653 274877906944 93761312734383 17772231073464320

noncomputable def ep1224 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 22) qz943 Bool.false 113415674943 274877906944 91046882438423 17772231073464320 Bool.true 29721365799 274877906944 90915366021893 17772231073464320 Bool.false

noncomputable abbrev qz944 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 21) qz65)

noncomputable def ep1225 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 22) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 21) qz944) Bool.false 113415674943 274877906944 91046882438423 17772231073464320 Bool.true 29721365799 274877906944 90915366021893 17772231073464320

noncomputable def ep1226 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 21) qz944 Bool.false 53579380571 137438953472 5508953084293 1110764442091520 Bool.false 7483643961 68719476736 5498847249173 1110764442091520 Bool.false

noncomputable abbrev qz945 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 20) qz65)

noncomputable def ep1227 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 21) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 20) qz945) Bool.false 53579380571 137438953472 5508953084293 1110764442091520 Bool.false 7483643961 68719476736 5498847249173 1110764442091520

noncomputable def ep1228 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 20) qz945 Bool.false 42138624043 68719476736 42568829115737 8886115536732160 Bool.false 16423698327 137438953472 42504109072807 8886115536732160 Bool.true

noncomputable abbrev qz946 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 19) qz65)

noncomputable def ep1229 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 20) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 19) qz946) Bool.false 42138624043 68719476736 42568829115737 8886115536732160 Bool.false 16423698327 137438953472 42504109072807 8886115536732160

noncomputable def ep1230 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 19) qz946 Bool.false 182874793633 274877906944 82081068872309 17772231073464320 Bool.true 7141464489 68719476736 20481578587411 4443057768366080 Bool.true

noncomputable abbrev qz947 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 18) qz65)

noncomputable def ep1231 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 19) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 18) qz947) Bool.false 182874793633 274877906944 82081068872309 17772231073464320 Bool.true 7141464489 68719476736 20481578587411 4443057768366080

noncomputable def ep1232 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 18) qz947 Bool.false 132308892233 274877906944 235588576179 53051436040192 Bool.true 69071147881 274877906944 235142335089 53051436040192 Bool.false

noncomputable abbrev qz948 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 17) qz65)

noncomputable def ep1233 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 18) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 17) qz948) Bool.false 132308892233 274877906944 235588576179 53051436040192 Bool.true 69071147881 274877906944 235142335089 53051436040192

noncomputable def ep1234 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 17) qz948 Bool.false 8303683425 34359738368 3783269415577 888611553673216 Bool.true 7356088589 34359738368 7554419678127 1777223107346432 Bool.false

noncomputable abbrev qz391 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable def ep1235 := @Enclosure.Complex.IsNear.of_eq qz948 (Complex.mk (@HMul.hMul Real Real Real qz0 qz339 (Real.cos qz391)) (@HMul.hMul Real Real Real qz0 qz339 (@Neg.neg Real Real.instNeg (Real.sin qz391)))) Bool.false 65879424833 274877906944 651356941685 3554446214692864 Bool.true 10222439169 274877906944 645697094709 3554446214692864 (BSN.cpow_neg_s_mk qz61 95415 1000 17 (@Eq.refl Real qz61) rfl)

noncomputable def ep1236 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz341 95415 1000 0 1 3189913004350711 1125899906842624 25000000012931 3232750000000000000 60873109862024618013 225179981368524800 477075000246762273 646550000000000000000 qz371 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz885) Bool.false 26758929747600409100288 9444732965739290427392 1000000000517240 129310000000000000000 3189913004350711 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep548 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1237 := nat_lit 746524525289681917299700928352256

noncomputable def ep1238 := BSN.cos_dyadic_bound_f 165295496 1073741824 2 1 524288 258873 ep1237 ep90 ep1237 ep1237 ep91 ep1237 518087 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 165295496) qz273 0 1 ep1237 ep90 ep1237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 165295496) qz274 0 1 ep1237 ep91 ep1237 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz949 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141731253) qz269)

noncomputable def ep1239 := @Enclosure.Real.IsNear.cos_image qz391 qz949 Bool.false 141731253 524288 97 131072 Bool.false 518087 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz391 Bool.false 60873109862024618013 225179981368524800 477075000246762273 646550000000000000000 141731253 524288 97 131072 (ep1236 rfl) rfl) (Enclosure.sfrac_false_div 141731253 524288) (BSN.cos_reduce0 qz949 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11631636526392710004736) qz272) 226375608064910080 72057594037927936 Bool.false 518087 524288 43 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 141731253 524288 226375608064910080 72057594037927936 43 11631636526392710004736 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 518087 524288 11631636526392710004736 75557863725914323419136 165295496 1073741824 258873 258620 (ep1238 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1240 := BSN.sin_dyadic_bound_f 165295496 1073741824 1 0 524288 258873 0 1 1 0 1 1 80391 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 165295496) qz267 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 165295496) qz268 0 0 rfl) rfl rfl

noncomputable def ep1241 := @Enclosure.Real.IsNear.sin_image qz391 qz949 Bool.false 141731253 524288 97 131072 Bool.false 80391 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz391 Bool.false 60873109862024618013 225179981368524800 477075000246762273 646550000000000000000 141731253 524288 97 131072 (ep1236 rfl) rfl) (Enclosure.sfrac_false_div 141731253 524288) (BSN.sin_reduce0 qz949 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11631636526392710004736) qz272) 226375608064910080 72057594037927936 Bool.false 80391 524288 43 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 141731253 524288 226375608064910080 72057594037927936 43 11631636526392710004736 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 80391 524288 11631636526392710004736 75557863725914323419136 165295496 1073741824 258873 258620 (ep1240 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1242 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz339 (Real.cos qz391)) (@HMul.hMul Real Real Real qz0 qz339 (@Neg.neg Real Real.instNeg (Real.sin qz391))) Bool.false 65879424833 274877906944 651356941685 3554446214692864 Bool.true 10222439169 274877906944 645697094709 3554446214692864 (@Enclosure.Real.IsNear.mulLit_ff qz339 (Real.cos qz391) 127159 524288 1 524288 518087 524288 6337071 8474460160 65879424833 274877906944 651356941685 3554446214692864 qz594 (@Enclosure.Real.IsNear.recentre' (Real.cos qz391) Bool.false 518087 524288 12674142 16948920320 518087 524288 6337071 8474460160 (ep1239 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz339 (@Neg.neg Real Real.instNeg (Real.sin qz391)) 127159 524288 1 524288 80391 524288 6337071 8474460160 10222439169 274877906944 645697094709 3554446214692864 qz594 (@Enclosure.Real.IsNear.neg (Real.sin qz391) Bool.false 80391 524288 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz391) Bool.false 80391 524288 12674142 16948920320 80391 524288 6337071 8474460160 (ep1241 rfl rfl) rfl)) rfl)

noncomputable def ep1243 := @ep1234 65879424833 274877906944 651356941685 3554446214692864 Bool.true 10222439169 274877906944 645697094709 3554446214692864 Bool.false 4546098920885787295744 132308892233 274877906944 235588576179 53051436040192 Bool.true 2373266569968597598208 69071147881 274877906944 235142335089 53051436040192 EMRow27.d17 (ep1235 ep1242) rfl rfl

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 18 1)))

noncomputable def ep1244 := @Enclosure.Complex.IsNear.of_eq qz947 (Complex.mk (@HMul.hMul Real Real Real qz0 qz342 (Real.cos qz392)) (@HMul.hMul Real Real Real qz0 qz342 (@Neg.neg Real Real.instNeg (Real.sin qz392)))) Bool.false 6320737675 34359738368 394861981543 2221528884183040 Bool.false 40505289925 274877906944 3153632094829 17772231073464320 (BSN.cpow_neg_s_mk qz61 95415 1000 18 (@Eq.refl Real qz61) rfl)

noncomputable def ep1245 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz344 95415 1000 0 1 3254268794313975 1125899906842624 25000000012931 3232750000000000000 2484048456075743397 9007199254740992 477075000246762273 646550000000000000000 qz371 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz888) Bool.false 27298785242132565196800 9444732965739290427392 1000000000517240 129310000000000000000 3254268794313975 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep565 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1246 := nat_lit 3435444591010701464031471532714759947317866438952728896014435157063379289185

noncomputable def ep1247 := nat_lit 730161174771589468668127115322041068230982716812779588635502832906241121

noncomputable def ep1248 := nat_lit 8996410810745064118085534189399564176483942891906116894037158406769859462241

noncomputable def ep1249 := BSN.sin_dyadic_bound_f 961451413 1073741824 3 2 524288 258873 ep1246 ep551 ep1247 ep1248 ep554 ep1247 409192 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 961451413) qz267 0 2 ep1246 ep551 ep1247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 961451413) qz268 0 2 ep1248 ep554 ep1247 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz950 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72295325) qz278)

noncomputable def ep1250 := @Enclosure.Real.IsNear.cos_image qz392 qz950 Bool.false 72295325 262144 97 131072 Bool.false 409192 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz392 Bool.false 2484048456075743397 9007199254740992 477075000246762273 646550000000000000000 72295325 262144 97 131072 (ep1245 rfl) rfl) (Enclosure.sfrac_false_div 72295325 262144) (BSN.cos_reduce3 qz950 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33828064280762017382400) qz280) 226375608064910080 72057594037927936 Bool.false 409192 524288 43 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 72295325 262144 226375608064910080 72057594037927936 43 33828064280762017382400 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 409192 524288 33828064280762017382400 37778931862957161709568 961451413 1073741824 258873 258620 (ep1249 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1251 := nat_lit 1908904844416954853114670019115009766762472902847877288714079755183169045601

noncomputable def ep1252 := nat_lit 5725254210901321380406673803114385218150956743110006306964968259883694654561

noncomputable def ep1253 := BSN.cos_dyadic_bound_f 961451413 1073741824 3 2 524288 258873 ep1251 ep199 ep1247 ep1252 ep202 ep1247 327779 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 961451413) qz273 0 2 ep1251 ep199 ep1247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 961451413) qz274 0 2 ep1252 ep202 ep1247 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1254 := @Enclosure.Real.IsNear.sin_image qz392 qz950 Bool.false 72295325 262144 97 131072 Bool.true 327779 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz392 Bool.false 2484048456075743397 9007199254740992 477075000246762273 646550000000000000000 72295325 262144 97 131072 (ep1245 rfl) rfl) (Enclosure.sfrac_false_div 72295325 262144) (BSN.sin_reduce3 qz950 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33828064280762017382400) qz280) 226375608064910080 72057594037927936 Bool.false 327779 524288 43 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 72295325 262144 226375608064910080 72057594037927936 43 33828064280762017382400 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 327779 524288 33828064280762017382400 37778931862957161709568 961451413 1073741824 258873 258620 (ep1253 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1255 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz342 (Real.cos qz392)) (@HMul.hMul Real Real Real qz0 qz342 (@Neg.neg Real Real.instNeg (Real.sin qz392))) Bool.false 6320737675 34359738368 394861981543 2221528884183040 Bool.false 40505289925 274877906944 3153632094829 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ff qz342 (Real.cos qz392) 123575 524288 1 524288 51149 65536 6337071 8474460160 6320737675 34359738368 394861981543 2221528884183040 qz596 (@Enclosure.Real.IsNear.recentre' (Real.cos qz392) Bool.false 409192 524288 12674142 16948920320 51149 65536 6337071 8474460160 (ep1250 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz342 (@Neg.neg Real Real.instNeg (Real.sin qz392)) 123575 524288 1 524288 327779 524288 6337071 8474460160 40505289925 274877906944 3153632094829 17772231073464320 qz596 (@Enclosure.Real.IsNear.neg (Real.sin qz392) Bool.true 327779 524288 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz392) Bool.true 327779 524288 12674142 16948920320 327779 524288 6337071 8474460160 (ep1254 rfl rfl) rfl)) rfl)

noncomputable def ep1256 := @ep1232 6320737675 34359738368 394861981543 2221528884183040 Bool.false 40505289925 274877906944 3153632094829 17772231073464320 Bool.false 6283530063331872210944 182874793633 274877906944 82081068872309 17772231073464320 Bool.true 7852123245004890046464 7141464489 68719476736 20481578587411 4443057768366080 (ep1233 (BSN.head_sum_c_succ qz64 17 18 rfl rfl) (ep1243 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1244 ep1255) rfl rfl

noncomputable abbrev qz393 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable def ep1257 := @Enclosure.Complex.IsNear.of_eq qz946 (Complex.mk (@HMul.hMul Real Real Real qz0 qz345 (Real.cos qz393)) (@HMul.hMul Real Real Real qz0 qz345 (@Neg.neg Real Real.instNeg (Real.sin qz393)))) Bool.true 14320297461 274877906944 611317871833 3554446214692864 Bool.false 30706627305 137438953472 308190379597 1777223107346432 (BSN.cpow_neg_s_mk qz61 95415 1000 19 (@Eq.refl Real qz61) rfl)

noncomputable def ep1258 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz347 95415 1000 0 1 3315141365800183 1125899906842624 25000000012931 3232750000000000000 63262842683564892189 225179981368524800 477075000246762273 646550000000000000000 qz371 (BSN.isNear_log_sfrac 19 1 3315141365800183 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz890) Bool.false 27809421382282341515264 9444732965739290427392 1000000000517240 129310000000000000000 3315141365800183 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 45049 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep576 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1259 := nat_lit 9637855799201603657359550176083358945174261773557115230924019088878390640896

noncomputable def ep1260 := nat_lit 18555363021822010947137258472879776999950675384449865634477227368927887616

noncomputable def ep1261 := nat_lit 28876456671561166950184376011304317281522883969902445961503102811897316147456

noncomputable def ep1262 := BSN.cos_dyadic_bound_f 1440650658 1073741824 3 2 524288 258873 ep1259 ep199 ep1260 ep1261 ep202 ep1260 119059 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1440650658) qz273 0 2 ep1259 ep199 ep1260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1440650658) qz274 0 2 ep1261 ep202 ep1260 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz951 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147295283) qz269)

noncomputable def ep1263 := @Enclosure.Real.IsNear.cos_image qz393 qz951 Bool.false 147295283 524288 97 131072 Bool.true 119059 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz393 Bool.false 63262842683564892189 225179981368524800 477075000246762273 646550000000000000000 147295283 524288 97 131072 (ep1258 rfl) rfl) (Enclosure.sfrac_false_div 147295283 524288) (BSN.cos_reduce2 qz951 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101376777629283601350656) qz272) 226375608064910080 72057594037927936 Bool.false 119059 524288 44 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 147295283 524288 226375608064910080 72057594037927936 44 101376777629283601350656 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 119059 524288 101376777629283601350656 75557863725914323419136 1440650658 1073741824 258873 258620 (ep1262 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1264 := nat_lit 17333296148145428974489480510171742279713710652095247523155652578085960843520

noncomputable def ep1265 := nat_lit 45366685990726506915462798155779424426964560138198443730570888860199252295936

noncomputable def ep1266 := BSN.sin_dyadic_bound_f 1440650658 1073741824 3 2 524288 258873 ep1264 ep551 ep1260 ep1265 ep554 ep1260 510590 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1440650658) qz267 0 2 ep1264 ep551 ep1260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1440650658) qz268 0 2 ep1265 ep554 ep1260 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1267 := @Enclosure.Real.IsNear.sin_image qz393 qz951 Bool.false 147295283 524288 97 131072 Bool.true 510590 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz393 Bool.false 63262842683564892189 225179981368524800 477075000246762273 646550000000000000000 147295283 524288 97 131072 (ep1258 rfl) rfl) (Enclosure.sfrac_false_div 147295283 524288) (BSN.sin_reduce2 qz951 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101376777629283601350656) qz272) 226375608064910080 72057594037927936 Bool.false 510590 524288 44 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 147295283 524288 226375608064910080 72057594037927936 44 101376777629283601350656 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 510590 524288 101376777629283601350656 75557863725914323419136 1440650658 1073741824 258873 258620 (ep1266 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1268 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz345 (Real.cos qz393)) (@HMul.hMul Real Real Real qz0 qz345 (@Neg.neg Real Real.instNeg (Real.sin qz393))) Bool.true 14320297461 274877906944 611317871833 3554446214692864 Bool.false 30706627305 137438953472 308190379597 1777223107346432 (@Enclosure.Real.IsNear.mulLit_ft qz345 (Real.cos qz393) 120279 524288 1 524288 119059 524288 6337071 8474460160 14320297461 274877906944 611317871833 3554446214692864 qz597 (@Enclosure.Real.IsNear.recentre' (Real.cos qz393) Bool.true 119059 524288 12674142 16948920320 119059 524288 6337071 8474460160 (ep1263 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz345 (@Neg.neg Real Real.instNeg (Real.sin qz393)) 120279 524288 1 524288 255295 262144 6337071 8474460160 30706627305 137438953472 308190379597 1777223107346432 qz597 (@Enclosure.Real.IsNear.neg (Real.sin qz393) Bool.true 255295 262144 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz393) Bool.true 510590 524288 12674142 16948920320 255295 262144 6337071 8474460160 (ep1267 rfl rfl) rfl)) rfl)

noncomputable def ep1269 := @ep1230 14320297461 274877906944 611317871833 3554446214692864 Bool.false 30706627305 137438953472 308190379597 1777223107346432 Bool.false 46331907113759820218368 42138624043 68719476736 42568829115737 8886115536732160 Bool.false 1128627955101358620672 16423698327 137438953472 42504109072807 8886115536732160 (ep1231 (BSN.head_sum_c_succ qz64 18 19 rfl rfl) (ep1256 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1257 ep1268) rfl rfl

noncomputable abbrev qz394 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable def ep1270 := @Enclosure.Complex.IsNear.of_eq qz945 (Complex.mk (@HMul.hMul Real Real Real qz0 qz348 (Real.cos qz394)) (@HMul.hMul Real Real Real qz0 qz348 (@Neg.neg Real Real.instNeg (Real.sin qz394)))) Bool.true 30697867515 137438953472 1502795558607 8886115536732160 Bool.true 1456410405 137438953472 1486668920577 8886115536732160 (BSN.cpow_neg_s_mk qz61 95415 1000 20 (@Eq.refl Real qz61) rfl)

noncomputable def ep1271 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz350 95415 1000 0 1 3372891496062199 1125899906842624 25000000012931 3232750000000000000 64364888419354943517 225179981368524800 477075000246762273 646550000000000000000 qz371 (BSN.isNear_log_sfrac 20 1 3372891496062199 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz893) Bool.false 28293864586999331028992 9444732965739290427392 1000000000517240 129310000000000000000 3372891496062199 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 58495 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep590 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1272 := nat_lit 28826699203132631970836450546820034719657256455662699506924972750793307311745

noncomputable def ep1273 := nat_lit 51248567931101114659815974164536194583965257330527787668580123671749709441

noncomputable def ep1274 := nat_lit 75415524041077967642741477950167032331680680300581453719054370337561543429761

noncomputable def ep1275 := BSN.sin_dyadic_bound_f 1635724719 1073741824 3 2 524288 258873 ep1272 ep551 ep1273 ep1274 ep554 ep1273 523698 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1635724719) qz267 0 2 ep1272 ep551 ep1273 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1635724719) qz268 0 2 ep1274 ep554 ep1273 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz952 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 149861183) qz269)

noncomputable def ep1276 := @Enclosure.Real.IsNear.cos_image qz394 qz952 Bool.false 149861183 524288 97 131072 Bool.true 523698 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 64364888419354943517 225179981368524800 477075000246762273 646550000000000000000 149861183 524288 97 131072 (ep1271 rfl) rfl) (Enclosure.sfrac_false_div 149861183 524288) (BSN.cos_reduce1 qz952 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115103894309715455246336) qz272) 226375608064910080 72057594037927936 Bool.false 523698 524288 45 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 149861183 524288 226375608064910080 72057594037927936 45 115103894309715455246336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 523698 524288 115103894309715455246336 75557863725914323419136 1635724719 1073741824 258873 258620 (ep1275 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1277 := nat_lit 16037610031931951590313501847862035375180238145292845409477687138739281710721

noncomputable def ep1278 := nat_lit 48010332959933652541620873595257033736372783921217480653095901168874345713281

noncomputable def ep1279 := BSN.cos_dyadic_bound_f 1635724719 1073741824 3 2 524288 258873 ep1277 ep199 ep1273 ep1278 ep202 ep1273 24846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1635724719) qz273 0 2 ep1277 ep199 ep1273 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1635724719) qz274 0 2 ep1278 ep202 ep1273 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1280 := @Enclosure.Real.IsNear.sin_image qz394 qz952 Bool.false 149861183 524288 97 131072 Bool.false 24846 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 64364888419354943517 225179981368524800 477075000246762273 646550000000000000000 149861183 524288 97 131072 (ep1271 rfl) rfl) (Enclosure.sfrac_false_div 149861183 524288) (BSN.sin_reduce1 qz952 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115103894309715455246336) qz272) 226375608064910080 72057594037927936 Bool.false 24846 524288 45 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 149861183 524288 226375608064910080 72057594037927936 45 115103894309715455246336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 24846 524288 115103894309715455246336 75557863725914323419136 1635724719 1073741824 258873 258620 (ep1279 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1281 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz348 (Real.cos qz394)) (@HMul.hMul Real Real Real qz0 qz348 (@Neg.neg Real Real.instNeg (Real.sin qz394))) Bool.true 30697867515 137438953472 1502795558607 8886115536732160 Bool.true 1456410405 137438953472 1486668920577 8886115536732160 (@Enclosure.Real.IsNear.mulLit_ft qz348 (Real.cos qz394) 117235 524288 1 524288 261849 262144 6337071 8474460160 30697867515 137438953472 1502795558607 8886115536732160 qz598 (@Enclosure.Real.IsNear.recentre' (Real.cos qz394) Bool.true 523698 524288 12674142 16948920320 261849 262144 6337071 8474460160 (ep1276 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz348 (@Neg.neg Real Real.instNeg (Real.sin qz394)) 117235 524288 1 524288 12423 262144 6337071 8474460160 1456410405 137438953472 1486668920577 8886115536732160 qz598 (@Enclosure.Real.IsNear.neg (Real.sin qz394) Bool.false 12423 262144 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz394) Bool.false 24846 524288 12674142 16948920320 12423 262144 6337071 8474460160 (ep1280 rfl rfl) rfl)) rfl)

noncomputable def ep1282 := @ep1228 30697867515 137438953472 1502795558607 8886115536732160 Bool.true 1456410405 137438953472 1486668920577 8886115536732160 Bool.false 3681946996678124896256 53579380571 137438953472 5508953084293 1110764442091520 Bool.false 2057088388313785565184 7483643961 68719476736 5498847249173 1110764442091520 (ep1229 (BSN.head_sum_c_succ qz64 19 20 rfl rfl) (ep1269 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1270 ep1281) rfl rfl

noncomputable abbrev qz395 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 21 1)))

noncomputable def ep1283 := @Enclosure.Complex.IsNear.of_eq qz944 (Complex.mk (@HMul.hMul Real Real Real qz0 qz351 (Real.cos qz395)) (@HMul.hMul Real Real Real qz0 qz351 (@Neg.neg Real Real.instNeg (Real.sin qz395)))) Bool.false 6256913801 274877906944 580726617947 3554446214692864 Bool.true 59655941643 274877906944 586762007025 3554446214692864 (BSN.cpow_neg_s_mk qz61 95415 1000 21 (@Eq.refl Real qz61) rfl)

noncomputable def ep1284 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz353 95415 1000 0 1 3427824127778039 1125899906842624 25000000012931 3232750000000000000 65413167830388318237 225179981368524800 477075000246762273 646550000000000000000 qz371 (BSN.isNear_log_sfrac 21 1 3427824127778039 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz896) Bool.false 28754672900871880179712 9444732965739290427392 1000000000517240 129310000000000000000 3427824127778039 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 71285 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep604 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1285 := nat_lit 13758992666768844600742482465502444032634061447182087095289251641897577193441

noncomputable def ep1286 := nat_lit 37754531078377796365173775106401825994767575817047033078393151623504699361

noncomputable def ep1287 := nat_lit 41201468938149778209497099846294528445912649189912167219710968622445722181601

noncomputable def ep1288 := BSN.cos_dyadic_bound_f 1574421947 1073741824 3 2 524288 258873 ep1285 ep199 ep1286 ep1287 ep202 ep1286 54689 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1574421947) qz273 0 2 ep1285 ep199 ep1286 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1574421947) qz274 0 2 ep1287 ep202 ep1286 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz953 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 152301899) qz269)

noncomputable def ep1289 := @Enclosure.Real.IsNear.cos_image qz395 qz953 Bool.false 152301899 524288 97 131072 Bool.false 54689 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz395 Bool.false 65413167830388318237 225179981368524800 477075000246762273 646550000000000000000 152301899 524288 97 131072 (ep1284 rfl) rfl) (Enclosure.sfrac_false_div 152301899 524288) (BSN.cos_reduce0 qz953 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110790095286059367661568) qz272) 226375608064910080 72057594037927936 Bool.false 54689 524288 46 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 152301899 524288 226375608064910080 72057594037927936 46 110790095286059367661568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 54689 524288 110790095286059367661568 75557863725914323419136 1574421947 1073741824 258873 258620 (ep1288 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1290 := nat_lit 24735983175321218044244329417819277797945496544274119145057938434116835188705

noncomputable def ep1291 := nat_lit 64723591456476292731286771886973457943008581540823664469215297462915560742881

noncomputable def ep1292 := BSN.sin_dyadic_bound_f 1574421947 1073741824 3 2 524288 258873 ep1290 ep551 ep1286 ep1291 ep554 ep1286 521427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1574421947) qz267 0 2 ep1290 ep551 ep1286 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1574421947) qz268 0 2 ep1291 ep554 ep1286 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1293 := @Enclosure.Real.IsNear.sin_image qz395 qz953 Bool.false 152301899 524288 97 131072 Bool.false 521427 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz395 Bool.false 65413167830388318237 225179981368524800 477075000246762273 646550000000000000000 152301899 524288 97 131072 (ep1284 rfl) rfl) (Enclosure.sfrac_false_div 152301899 524288) (BSN.sin_reduce0 qz953 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110790095286059367661568) qz272) 226375608064910080 72057594037927936 Bool.false 521427 524288 46 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 152301899 524288 226375608064910080 72057594037927936 46 110790095286059367661568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 521427 524288 110790095286059367661568 75557863725914323419136 1574421947 1073741824 258873 258620 (ep1292 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1294 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz351 (Real.cos qz395)) (@HMul.hMul Real Real Real qz0 qz351 (@Neg.neg Real Real.instNeg (Real.sin qz395))) Bool.false 6256913801 274877906944 580726617947 3554446214692864 Bool.true 59655941643 274877906944 586762007025 3554446214692864 (@Enclosure.Real.IsNear.mulLit_ff qz351 (Real.cos qz395) 114409 524288 1 524288 54689 524288 6337071 8474460160 6256913801 274877906944 580726617947 3554446214692864 qz600 (@Enclosure.Real.IsNear.recentre' (Real.cos qz395) Bool.false 54689 524288 12674142 16948920320 54689 524288 6337071 8474460160 (ep1289 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz351 (@Neg.neg Real Real.instNeg (Real.sin qz395)) 114409 524288 1 524288 521427 524288 6337071 8474460160 59655941643 274877906944 586762007025 3554446214692864 qz600 (@Enclosure.Real.IsNear.neg (Real.sin qz395) Bool.false 521427 524288 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz395) Bool.false 521427 524288 12674142 16948920320 521427 524288 6337071 8474460160 (ep1293 rfl rfl) rfl)) rfl)

noncomputable def ep1295 := @ep1226 6256913801 274877906944 580726617947 3554446214692864 Bool.true 59655941643 274877906944 586762007025 3554446214692864 Bool.false 15587731671486453252096 113415674943 274877906944 91046882438423 17772231073464320 Bool.true 2042436705586526552064 29721365799 274877906944 90915366021893 17772231073464320 (ep1227 (BSN.head_sum_c_succ qz64 20 21 rfl rfl) (ep1282 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1283 ep1294) rfl rfl

noncomputable abbrev qz396 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 22 1)))

noncomputable def ep1296 := @Enclosure.Complex.IsNear.of_eq qz943 (Complex.mk (@HMul.hMul Real Real Real qz0 qz354 (Real.cos qz396)) (@HMul.hMul Real Real Real qz0 qz354 (@Neg.neg Real Real.instNeg (Real.sin qz396)))) Bool.false 13615911769 68719476736 143246697317 888611553673216 Bool.false 10818754073 137438953472 284594671249 1777223107346432 (BSN.cpow_neg_s_mk qz61 95415 1000 22 (@Eq.refl Real qz61) rfl)

noncomputable def ep1297 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz356 95415 1000 0 1 3480201253952759 1125899906842624 25000000012931 3232750000000000000 66412680529180499997 225179981368524800 477075000246762273 646550000000000000000 qz371 (BSN.isNear_log_sfrac 22 1 3480201253952759 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz898) Bool.false 29194044080518145769472 9444732965739290427392 1000000000517240 129310000000000000000 3480201253952759 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 83480 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep618 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1298 := nat_lit 10816830610314545074639008793768175345437558537091701886957224365273005424640

noncomputable def ep1299 := nat_lit 7231969815912350363079412389600791571880060094130887570310297212636102656

noncomputable def ep1300 := nat_lit 28318085552074236152038132554095391289791514166516340647869370951656460517376

noncomputable def ep1301 := BSN.sin_dyadic_bound_f 1280581064 1073741824 3 2 524288 258873 ep1298 ep551 ep1299 ep1300 ep554 ep1299 487244 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1280581064) qz267 0 2 ep1298 ep551 ep1299 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1280581064) qz268 0 2 ep1300 ep554 ep1299 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz954 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 154629071) qz269)

noncomputable def ep1302 := @Enclosure.Real.IsNear.cos_image qz396 qz954 Bool.false 154629071 524288 97 131072 Bool.false 487244 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz396 Bool.false 66412680529180499997 225179981368524800 477075000246762273 646550000000000000000 154629071 524288 97 131072 (ep1297 rfl) rfl) (Enclosure.sfrac_false_div 154629071 524288) (BSN.cos_reduce3 qz954 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90112881347518300946432) qz272) 226375608064910080 72057594037927936 Bool.false 487244 524288 46 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 154629071 524288 226375608064910080 72057594037927936 46 90112881347518300946432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 487244 524288 90112881347518300946432 75557863725914323419136 1280581064 1073741824 258873 258620 (ep1301 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1303 := nat_lit 6012564547870708308294151290933253321497256991759448109451929223912841281536

noncomputable def ep1304 := nat_lit 18023229703980300224156295048020558381348010855090082553215167077313251639296

noncomputable def ep1305 := BSN.cos_dyadic_bound_f 1280581064 1073741824 3 2 524288 258873 ep1303 ep199 ep1299 ep1304 ep202 ep1299 193574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1280581064) qz273 0 2 ep1303 ep199 ep1299 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1280581064) qz274 0 2 ep1304 ep202 ep1299 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1306 := @Enclosure.Real.IsNear.sin_image qz396 qz954 Bool.false 154629071 524288 97 131072 Bool.true 193574 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz396 Bool.false 66412680529180499997 225179981368524800 477075000246762273 646550000000000000000 154629071 524288 97 131072 (ep1297 rfl) rfl) (Enclosure.sfrac_false_div 154629071 524288) (BSN.sin_reduce3 qz954 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90112881347518300946432) qz272) 226375608064910080 72057594037927936 Bool.false 193574 524288 46 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q3 154629071 524288 226375608064910080 72057594037927936 46 90112881347518300946432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 193574 524288 90112881347518300946432 75557863725914323419136 1280581064 1073741824 258873 258620 (ep1305 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1307 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz354 (Real.cos qz396)) (@HMul.hMul Real Real Real qz0 qz354 (@Neg.neg Real Real.instNeg (Real.sin qz396))) Bool.false 13615911769 68719476736 143246697317 888611553673216 Bool.false 10818754073 137438953472 284594671249 1777223107346432 (@Enclosure.Real.IsNear.mulLit_ff qz354 (Real.cos qz396) 111779 524288 1 524288 121811 131072 6337071 8474460160 13615911769 68719476736 143246697317 888611553673216 qz601 (@Enclosure.Real.IsNear.recentre' (Real.cos qz396) Bool.false 487244 524288 12674142 16948920320 121811 131072 6337071 8474460160 (ep1302 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz354 (@Neg.neg Real Real.instNeg (Real.sin qz396)) 111779 524288 1 524288 96787 262144 6337071 8474460160 10818754073 137438953472 284594671249 1777223107346432 qz601 (@Enclosure.Real.IsNear.neg (Real.sin qz396) Bool.true 96787 262144 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz396) Bool.true 193574 524288 12674142 16948920320 96787 262144 6337071 8474460160 (ep1306 rfl rfl) rfl)) rfl)

noncomputable def ep1308 := @ep1224 13615911769 68719476736 143246697317 888611553673216 Bool.false 10818754073 137438953472 284594671249 1777223107346432 Bool.false 11536579163940123049984 167879322019 274877906944 93911816384763 17772231073464320 Bool.true 1111036935844938121216 8083857653 274877906944 93761312734383 17772231073464320 (ep1225 (BSN.head_sum_c_succ qz64 21 22 rfl rfl) (ep1295 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1296 ep1307) rfl rfl

noncomputable abbrev qz397 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable def ep1309 := @Enclosure.Complex.IsNear.of_eq qz942 (Complex.mk (@HMul.hMul Real Real Real qz0 qz357 (Real.cos qz397)) (@HMul.hMul Real Real Real qz0 qz357 (@Neg.neg Real Real.instNeg (Real.sin qz397)))) Bool.true 43026012575 274877906944 2796571695073 17772231073464320 Bool.false 37866061375 274877906944 2793519979073 17772231073464320 (BSN.cpow_neg_s_mk qz61 95415 1000 23 (@Eq.refl Real qz61) rfl)

noncomputable def ep1310 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz359 95415 1000 0 1 3530250507853047 1125899906842624 25000000012931 3232750000000000000 67367770441359695901 225179981368524800 477075000246762273 646550000000000000000 qz371 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz901) Bool.false 29613887652180132888576 9444732965739290427392 1000000000517240 129310000000000000000 3530250507853047 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 95133 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep629 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1311 := nat_lit 805371704328433773996679189463375454932266957490765404314716992439209557601

noncomputable def ep1312 := nat_lit 130027426281923272245985261379422247096869046936358264813479560388673121

noncomputable def ep1313 := nat_lit 2415855058132737475445545597867367520302607134378423496414524018196851326561

noncomputable def ep1314 := BSN.cos_dyadic_bound_f 774915541 1073741824 3 2 524288 258873 ep1311 ep199 ep1312 ep1313 ep202 ep1312 393575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 774915541) qz273 0 2 ep1311 ep199 ep1312 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 774915541) qz274 0 2 ep1313 ep202 ep1312 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz955 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 156852813) qz269)

noncomputable def ep1315 := @Enclosure.Real.IsNear.cos_image qz397 qz955 Bool.false 156852813 524288 97 131072 Bool.true 393575 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz397 Bool.false 67367770441359695901 225179981368524800 477075000246762273 646550000000000000000 156852813 524288 97 131072 (ep1310 rfl) rfl) (Enclosure.sfrac_false_div 156852813 524288) (BSN.cos_reduce2 qz955 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54529833506291461390336) qz272) 226375608064910080 72057594037927936 Bool.false 393575 524288 47 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 156852813 524288 226375608064910080 72057594037927936 47 54529833506291461390336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 393575 524288 54529833506291461390336 75557863725914323419136 774915541 1073741824 258873 258620 (ep1314 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1316 := nat_lit 360593158950531495307067276369027761

noncomputable def ep1317 := BSN.sin_dyadic_bound_f 774915541 1073741824 2 1 524288 258873 ep1316 ep100 ep1316 ep1316 ep101 ep1316 346375 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 774915541) qz267 0 1 ep1316 ep100 ep1316 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 774915541) qz268 0 1 ep1316 ep101 ep1316 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1318 := @Enclosure.Real.IsNear.sin_image qz397 qz955 Bool.false 156852813 524288 97 131072 Bool.true 346375 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz397 Bool.false 67367770441359695901 225179981368524800 477075000246762273 646550000000000000000 156852813 524288 97 131072 (ep1310 rfl) rfl) (Enclosure.sfrac_false_div 156852813 524288) (BSN.sin_reduce2 qz955 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54529833506291461390336) qz272) 226375608064910080 72057594037927936 Bool.false 346375 524288 47 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q2 156852813 524288 226375608064910080 72057594037927936 47 54529833506291461390336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 346375 524288 54529833506291461390336 75557863725914323419136 774915541 1073741824 258873 258620 (ep1317 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1319 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz357 (Real.cos qz397)) (@HMul.hMul Real Real Real qz0 qz357 (@Neg.neg Real Real.instNeg (Real.sin qz397))) Bool.true 43026012575 274877906944 2796571695073 17772231073464320 Bool.false 37866061375 274877906944 2793519979073 17772231073464320 (@Enclosure.Real.IsNear.mulLit_ft qz357 (Real.cos qz397) 109321 524288 1 524288 393575 524288 6337071 8474460160 43026012575 274877906944 2796571695073 17772231073464320 qz602 (@Enclosure.Real.IsNear.recentre' (Real.cos qz397) Bool.true 393575 524288 12674142 16948920320 393575 524288 6337071 8474460160 (ep1315 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz357 (@Neg.neg Real Real.instNeg (Real.sin qz397)) 109321 524288 1 524288 346375 524288 6337071 8474460160 37866061375 274877906944 2793519979073 17772231073464320 qz602 (@Enclosure.Real.IsNear.neg (Real.sin qz397) Bool.true 346375 524288 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' (Real.sin qz397) Bool.true 346375 524288 12674142 16948920320 346375 524288 6337071 8474460160 (ep1318 rfl rfl) rfl)) rfl)

noncomputable def ep1320 := @ep1222 43026012575 274877906944 2796571695073 17772231073464320 Bool.false 37866061375 274877906944 2793519979073 17772231073464320 Bool.false 34319416374998268379136 31213327361 68719476736 24177097019959 4443057768366080 Bool.false 8186469823283166445568 14891101861 137438953472 6034677044591 1110764442091520 (ep1223 (BSN.head_sum_c_succ qz64 22 23 rfl rfl) (ep1308 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1309 ep1319) rfl rfl

noncomputable def ep1321 := @Enclosure.Complex.IsNear.mul qz78 (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false ep1213 ep1032 ep1214 ep1034 Bool.true

noncomputable def ep1322 := nat_lit 21332575139313470813719260971

noncomputable def ep1323 := nat_lit 2952143783999248069243699200000

noncomputable def ep1324 := nat_lit 26482235684052979929749319375979

noncomputable def ep1325 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) ep1322 ep1323 ep1324

noncomputable def ep1326 := nat_lit 343567541438048491050512469196800000

noncomputable def ep1327 := nat_lit 2007655543002395488391589369629

noncomputable def ep1328 := nat_lit 886679648585386033195869443521361

noncomputable def ep1329 := nat_lit 34356754143804849105051246919680000000

noncomputable def ep1330 := nat_lit 4667351249801733794797465619402406240296234154063613132800000

noncomputable def ep1331 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 3936907953 274877906944 543030363433 3554446214692864 48767504484710830963

noncomputable abbrev qz398 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable abbrev qz399 := (Real.sin (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 24 1))))

noncomputable abbrev qz956 := (@Neg.neg Real Real.instNeg qz399)

noncomputable def ep1332 := @Enclosure.Complex.IsNear.of_eq qz78 (Complex.mk (@HMul.hMul Real Real Real qz0 qz360 (Real.cos qz398)) (@HMul.hMul Real Real Real qz0 qz360 qz956)) Bool.true 3936907953 274877906944 543030363433 3554446214692864 Bool.true 55970401905 274877906944 549317519081 3554446214692864 (BSN.cpow_neg_s_mk qz61 95415 1000 24 (@Eq.refl Real qz61) rfl)

noncomputable def ep1333 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz362 95415 1000 0 1 3578169457974519 1125899906842624 25000000012931 3232750000000000000 68282207766527746077 225179981368524800 477075000246762273 646550000000000000000 qz371 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 25000000012931 3232750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz603) Bool.false 30015860940520713879552 9444732965739290427392 1000000000517240 129310000000000000000 3578169457974519 1125899906842624 25000000012931 3232750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 106290 262144 24973259072661432 36028797018963968 129310 1000000000000000 rfl rfl rfl rfl (ep654 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1334 := BSN.sin_dyadic_bound_f 75402722 1073741824 1 0 524288 258873 0 1 1 0 1 1 36787 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 75402722) qz267 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 75402722) qz268 0 0 rfl) rfl rfl

noncomputable abbrev qz957 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 158981903) qz269)

noncomputable def ep1335 := @Enclosure.Real.IsNear.cos_image qz398 qz957 Bool.false 158981903 524288 97 131072 Bool.true 36787 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz398 Bool.false 68282207766527746077 225179981368524800 477075000246762273 646550000000000000000 158981903 524288 97 131072 (ep1333 rfl) rfl) (Enclosure.sfrac_false_div 158981903 524288) (BSN.cos_reduce1 qz957 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5305994883308711837696) qz272) 226375608064910080 72057594037927936 Bool.false 36787 524288 48 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 158981903 524288 226375608064910080 72057594037927936 48 5305994883308711837696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 36787 524288 5305994883308711837696 75557863725914323419136 75402722 1073741824 258873 258620 (ep1334 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1336 := nat_lit 32325711740008704897765566192656

noncomputable def ep1337 := BSN.cos_dyadic_bound_f 75402722 1073741824 2 1 524288 258873 ep1336 ep90 ep1336 ep1336 ep91 ep1336 522995 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 75402722) qz273 0 1 ep1336 ep90 ep1336 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 75402722) qz274 0 1 ep1336 ep91 ep1336 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1338 := @Enclosure.Real.IsNear.sin_image qz398 qz957 Bool.false 158981903 524288 97 131072 Bool.false 522995 524288 1 129310 (@Enclosure.Real.IsNear.recentre' qz398 Bool.false 68282207766527746077 225179981368524800 477075000246762273 646550000000000000000 158981903 524288 97 131072 (ep1333 rfl) rfl) (Enclosure.sfrac_false_div 158981903 524288) (BSN.sin_reduce1 qz957 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5305994883308711837696) qz272) 226375608064910080 72057594037927936 Bool.false 522995 524288 48 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q1 158981903 524288 226375608064910080 72057594037927936 48 5305994883308711837696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 522995 524288 5305994883308711837696 75557863725914323419136 75402722 1073741824 258873 258620 (ep1337 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1339 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz360 (Real.cos qz398)) (@HMul.hMul Real Real Real qz0 qz360 qz956) Bool.true 3936907953 274877906944 543030363433 3554446214692864 Bool.true 55970401905 274877906944 549317519081 3554446214692864 (@Enclosure.Real.IsNear.mulLit_ft qz360 (Real.cos qz398) 107019 524288 1 524288 36787 524288 6337071 8474460160 3936907953 274877906944 543030363433 3554446214692864 qz604 (@Enclosure.Real.IsNear.recentre' (Real.cos qz398) Bool.true 36787 524288 12674142 16948920320 36787 524288 6337071 8474460160 (ep1335 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz360 qz956 107019 524288 1 524288 522995 524288 6337071 8474460160 55970401905 274877906944 549317519081 3554446214692864 qz604 (@Enclosure.Real.IsNear.neg qz399 Bool.false 522995 524288 6337071 8474460160 (@Enclosure.Real.IsNear.recentre' qz399 Bool.false 522995 524288 12674142 16948920320 522995 524288 6337071 8474460160 (ep1338 rfl rfl) rfl)) rfl)

noncomputable def ep1340 := @ep1331 96658528695091200000 0 1 ep1322 ep1323 ep1324 ep1326 (@Enclosure.Complex.IsNear.re_isNear qz78 Bool.true 3936907953 274877906944 543030363433 3554446214692864 Bool.true 55970401905 274877906944 549317519081 3554446214692864 (ep1332 ep1339))

noncomputable def ep1341 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false 48767504484710830963 96658528695091200000 0 1 Bool.false

noncomputable def ep1342 := @Enclosure.Complex.IsNear.addLitP qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) Bool.false 363210889 728341778 0 1 Bool.true 91598400

noncomputable def ep1343 := @ep1342 364170889 0 1 Bool.false 1553232667 265420800000 0 1 Bool.false 11108410784929 26542080000000 0 1 Bool.false 97535008969421661926 48767504484710830963 96658528695091200000 0 1 Bool.false 1614147770252781731881 1614147770252781731881 9665852869509120000000 0 1

noncomputable abbrev qz80 := (@HDiv.hDiv Complex Complex Complex qz329 qz593 (@HSub.hSub Complex Complex Complex qz577 qz369 (1 : Complex)))

noncomputable def ep1344 := @Enclosure.Complex.IsNear.addLitP qz80 qz24 Bool.true 48000000 36417088900 0 1 Bool.true 9159840000 36417088900 0 1

noncomputable def ep1345 := @Enclosure.Complex.IsNear.of_eq qz80 (Complex.mk (Enclosure.sfrac Bool.true 48000000 36417088900) (Enclosure.sfrac Bool.true 9159840000 36417088900)) Bool.true 48000000 36417088900 0 1 Bool.true 9159840000 36417088900 0 1

noncomputable def ep1346 := @ep1344 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 36321088900 363210889 728341778 0 1 Bool.true 9159840000 91598400 364170889 0 1 (ep1345 (BSN.N_div_s_sub_one_mk qz61 95415 1000 24 (@Eq.refl Real qz61) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 48000000 36417088900) (Enclosure.sfrac Bool.true 9159840000 36417088900) Bool.true 48000000 36417088900 0 1 Bool.true 9159840000 36417088900 0 1 (Enclosure.Real.IsNear.const Bool.true 48000000 36417088900) (Enclosure.Real.IsNear.const Bool.true 9159840000 36417088900))) qz334 rfl

noncomputable def ep1347 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz50)) Bool.false 1553232667 265420800000 0 1

noncomputable def ep1348 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz50) Bool.false 1 576 0 1 Bool.false

noncomputable def ep1349 := @ep1348 6361 19200 0 1 Bool.false 1092432667 265420800000 0 1 Bool.false 2314964384929 26542080000000 0 1 Bool.false 894662016192 1553232667 265420800000 0 1 Bool.false 213281487070636800 11108410784929 26542080000000 0

noncomputable def ep1350 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz52)) Bool.false 1 576 0 1

noncomputable def ep1351 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz52) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1352 := @ep1351 0 1 0 1 Bool.false 1 576 0 1 Bool.false 6361 19200 0 1 Bool.false 1 1 576 0 1 Bool.false 6361 6361 19200 0

noncomputable def ep1353 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (Complex.mk qz263 qz263) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1354 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz52 Bool.false 1 576 0 1 Bool.false 6361 19200 0 1

noncomputable def ep1355 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52)) 1 576 0 1 0 1 0

noncomputable def ep1356 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52) 1 24 0 1 1 24 0 1 1

noncomputable def ep1357 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1358 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1359 := @ep1358 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep681) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep986)

noncomputable def ep1360 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 95415 1000 0 1 0 1 0

noncomputable def ep1361 := @ep1360 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep681) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep986)

noncomputable def ep1362 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) 6361 800 0 1 0 1 0 1 6361

noncomputable def ep1363 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 95415 1000 0 1 6361 800 0

noncomputable def ep1364 := @ep1363 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep681) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep986)

noncomputable def ep1365 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1366 := @ep1365 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep681) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep986)

noncomputable def ep1367 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 6361 800 0 1 (@ep1357 1 24 0 1 (ep1359 rfl) (ep1361 rfl) rfl rfl) (@ep1362 6361 800 0 1 (ep1364 rfl) (ep1366 rfl) rfl rfl)

noncomputable def ep1368 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 6361 800 0 1 ep1367

noncomputable def ep1369 := @ep1356 576 0 1 ep1368 qz905

noncomputable def ep1370 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52) 6361 800 0 1 0 1 0 1 0

noncomputable def ep1371 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 6361 800 0 1 ep1367

noncomputable def ep1372 := @ep1370 1 0 1 ep1371 qz906

noncomputable def ep1373 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52)) 0 1 0 1 6361 19200 0

noncomputable def ep1374 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52) 1 24 0 1 0 1 0 1 0

noncomputable def ep1375 := @ep1374 1 0 1 ep1368 qz906

noncomputable def ep1376 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52) 6361 800 0 1 1 24 0 1 6361

noncomputable def ep1377 := @ep1376 19200 0 1 ep1371 qz905

noncomputable def ep1378 := @ep1352 1 (@ep1353 0 1 0 1 (BSN.bern_sum_base qz64 24) qz338) (ep1354 (@ep1355 1 1 1 576 0 1 (ep1369 rfl) (ep1372 rfl) rfl rfl) (@ep1373 1 6361 6361 19200 0 1 (ep1375 rfl) (ep1377 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1379 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz50 Bool.false 1092432667 265420800000 0 1 Bool.false 2314964384929 26542080000000 0 1

noncomputable def ep1380 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50)) 1092432667 265420800000 0 1 0 1 0

noncomputable def ep1381 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50) 1092432667 19200000 0 1 1 13824 0 1 1092432667

noncomputable def ep1382 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) 1092432667 19200000 0 1 0 1 0 1 1092432667

noncomputable def ep1383 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3277298001 80000 0 1 1092432667 19200000 0

noncomputable def ep1384 := @ep1383 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep707) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 EMRow27.d18)

noncomputable def ep1385 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 6944893154787 8000000 0 1 0 1 0

noncomputable def ep1386 := @ep1385 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep707) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 EMRow27.d18)

noncomputable def ep1387 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) 2314964384929 1920000000 0 1 0 1 0 1 2314964384929

noncomputable def ep1388 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 6944893154787 8000000 0 1 2314964384929 1920000000 0

noncomputable def ep1389 := @ep1388 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep707) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 EMRow27.d18)

noncomputable def ep1390 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3277298001 80000 0 1 0 1 0

noncomputable def ep1391 := @ep1390 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep707) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 EMRow27.d18)

noncomputable def ep1392 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1092432667 19200000 0 1 Bool.false 2314964384929 1920000000 0 1 (@ep1382 1092432667 19200000 0 1 (ep1384 rfl) (ep1386 rfl) rfl rfl) (@ep1387 2314964384929 1920000000 0 1 (ep1389 rfl) (ep1391 rfl) rfl rfl)

noncomputable def ep1393 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1092432667 19200000 0 1 Bool.false 2314964384929 1920000000 0 1 ep1392

noncomputable def ep1394 := @ep1381 265420800000 0 1 ep1393 qz907

noncomputable def ep1395 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50) 2314964384929 1920000000 0 1 0 1 0 1 0

noncomputable def ep1396 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1092432667 19200000 0 1 Bool.false 2314964384929 1920000000 0 1 ep1392

noncomputable def ep1397 := @ep1395 1 0 1 ep1396 qz908

noncomputable def ep1398 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50)) 0 1 0 1 2314964384929 26542080000000 0

noncomputable def ep1399 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50) 1092432667 19200000 0 1 0 1 0 1 0

noncomputable def ep1400 := @ep1399 1 0 1 ep1393 qz908

noncomputable def ep1401 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50) 2314964384929 1920000000 0 1 1 13824 0 1 2314964384929

noncomputable def ep1402 := @ep1401 26542080000000 0 1 ep1396 qz907

noncomputable def ep1403 := @ep1349 1 (@ep1350 Bool.false 6361 19200 0 1 (BSN.bern_sum_succ qz64 24 0 1 1 rfl rfl) (ep1378 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1379 (@ep1380 1 1092432667 1092432667 265420800000 0 1 (ep1394 rfl) (ep1397 rfl) rfl rfl) (@ep1398 1 2314964384929 2314964384929 26542080000000 0 1 (ep1400 rfl) (ep1402 rfl) rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1404 := ep1343 (ep1346 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1347 Bool.false 11108410784929 26542080000000 0 1 (BSN.bern_sum_succ qz64 24 1 2 3 rfl rfl) (ep1403 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1405 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 55970401905 274877906944 549317519081 3554446214692864 1614147770252781731881

noncomputable def ep1406 := @ep1405 9665852869509120000000 0 1 ep1327 ep1032 ep1328 ep1329 (@Enclosure.Complex.IsNear.im_isNear qz78 Bool.true 3936907953 274877906944 543030363433 3554446214692864 Bool.true 55970401905 274877906944 549317519081 3554446214692864 (ep1332 ep1339))

noncomputable def ep1407 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false 48767504484710830963 96658528695091200000 0 1 Bool.false

noncomputable def ep1408 := nat_lit 706083466002821468957269172177

noncomputable def ep1409 := nat_lit 295214378399924806924369920000000

noncomputable def ep1410 := nat_lit 876531250314934650142562592707473

noncomputable def ep1411 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) ep1408 ep1409 ep1410

noncomputable def ep1412 := nat_lit 60656373909181225260125070767

noncomputable def ep1413 := nat_lit 590428756799849613848739840000

noncomputable def ep1414 := nat_lit 26788844575312894960285118105003

noncomputable def ep1415 := nat_lit 18323525702621327288841271228904702163258498478417568071680000

noncomputable def ep1416 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 3936907953 274877906944 543030363433 3554446214692864 1614147770252781731881

noncomputable def ep1417 := @ep1416 9665852869509120000000 0 1 ep1408 ep1409 ep1410 ep1329 (@Enclosure.Complex.IsNear.re_isNear qz78 Bool.true 3936907953 274877906944 543030363433 3554446214692864 Bool.true 55970401905 274877906944 549317519081 3554446214692864 (ep1332 ep1339))

noncomputable def ep1418 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 55970401905 274877906944 549317519081 3554446214692864 48767504484710830963

noncomputable def ep1419 := @ep1418 96658528695091200000 0 1 ep1412 ep1413 ep1414 ep1326 (@Enclosure.Complex.IsNear.im_isNear qz78 Bool.true 3936907953 274877906944 543030363433 3554446214692864 Bool.true 55970401905 274877906944 549317519081 3554446214692864 (ep1332 ep1339))

noncomputable abbrev qz958 := (ep1404 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1420 := @ep1321 ep1215 ep1209 ep1216 ep1034 (@ep1325 ep1326 ep1327 ep1032 ep1328 ep1329 ep1330 ep1213 ep1032 ep1214 ep1034 (ep1340 (@ep1341 1614147770252781731881 9665852869509120000000 0 1 qz958) rfl) (ep1406 (@ep1407 1614147770252781731881 9665852869509120000000 0 1 qz958) rfl) rfl rfl) (@ep1411 ep1329 ep1412 ep1413 ep1414 ep1326 ep1415 ep1215 ep1209 ep1216 ep1034 (ep1417 (@ep1407 1614147770252781731881 9665852869509120000000 0 1 qz958) rfl) (ep1419 (@ep1341 1614147770252781731881 9665852869509120000000 0 1 qz958) rfl) rfl rfl)

noncomputable def ep1421 := @ep1219 ep1210 ep1034 (@ep1220 1110764442091520 (BSN.head_sum_c_eq qz64 24) (ep1221 (BSN.head_sum_c_succ qz64 23 24 rfl rfl) (ep1320 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1420 rfl rfl rfl

noncomputable def ep1422 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz64 2 24) Bool.false ep1031 ep1032 ep1033 ep1034 Bool.false ep1208 ep1209 ep1210 ep1034 (@ep1211 ep1034 Bool.false ep1208 ep1209 ep1210 ep1034 (BSN.zetaApproximant_eq_folded' qz64 2 24 rfl) (ep1421 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1423 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz387)) (Complex.im (zetaApproximant qz64 2 24)) 33 262144 65679

noncomputable def ep1424 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz387)) Bool.false 66 524288 131358

noncomputable def ep1425 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz387) qz936 Bool.false 42824649 524288 1

noncomputable def ep1426 := BSN.sin_dyadic_bound_f 136072 1073741824 1 0 524288 258873 0 1 1 0 1 1 66 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 136072) qz267 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 136072) qz268 0 0 rfl) rfl rfl

noncomputable def ep1427 := @ep1425 2048 Bool.false 66 524288 1 129310 (@ep1041 42824649 524288 1 2048 ep1205 rfl) (Enclosure.sfrac_false_div 42824649 524288) (BSN.sin_reduce0 qz936 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9575258463139790848) qz272) 226375608064910080 72057594037927936 Bool.false 66 524288 13 1000000000000000 258620 129310 (BSN.sin_reduce_arg_pos_rat_q0 42824649 524288 226375608064910080 72057594037927936 13 9575258463139790848 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 66 524288 9575258463139790848 75557863725914323419136 136072 1073741824 258873 258620 (ep1426 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1428 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz64 2 24) Bool.false ep1031 ep1032 ep1033 ep1034 Bool.false ep1208 ep1209 ep1210 ep1034 (@ep1211 ep1034 Bool.false ep1208 ep1209 ep1210 ep1034 (BSN.zetaApproximant_eq_folded' qz64 2 24 rfl) (ep1421 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow27.d19 : Enclosure.Real.IsNear (hardyZApproximantEM 2 24 qz61) Bool.false ep1015 ep1016 ep1017 ep1018 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 2 24 qz61) ep1019 Bool.false ep1015 ep1016 ep1017 ep1018 (@Eq.refl Real ep1019) (@ep1020 Bool.false ep1015 ep1016 ep1017 ep1018 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz324 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz387) (zetaApproximant qz64 2 24)) (@ep1022 ep1023 ep1024 ep1018 ep1025 ep1026 ep1027 ep1028 ep1029 ep1015 ep1016 ep1017 ep1018 (@ep1030 132413440 ep1031 ep1032 ep1033 ep1034 ep1021 ep1023 ep1024 ep1018 (@ep1035 264826880 524287 524288 65679 132413440 (ep1207 rfl rfl) rfl) ep1422 rfl) (@ep1423 132413440 ep1208 ep1209 ep1210 ep1034 ep1025 ep1026 ep1027 ep1028 (@ep1424 264826880 33 262144 65679 132413440 (ep1427 rfl rfl) rfl) ep1428 rfl) rfl rfl))

theorem EMRow27.d20 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 2))) (Nat.pow 4 (Nat.mul 2 2))) 30720 := @Eq.refl Nat 30720

theorem EMRow27.d21 : @Eq Nat (Nat.mul (Nat.mul 2 2) (Nat.pow (Nat.succ (Nat.mul 4 4)) (Nat.mul 2 2))) 334084 := @Eq.refl Nat 334084

theorem EMRow27.d175 : @Eq Nat (TangentNumbers.tangentNumber 3) 16 := Height20.tangent_three

noncomputable abbrev qz232 := (@HMul.hMul Nat Nat Nat qz865 2 3)

theorem EMRow27.d176 : @Eq Real (@Rat.cast Real Real.instRatCast (bernoulli qz232)) (Enclosure.sfrac Bool.false 1 42) := BSN.bern_real_tangent_pos 2 16 1 42 EMRow27.d175 rfl rfl rfl

theorem EMRow27.d177 : @Eq Nat (BSN.factNat (Nat.mul 2 3)) 720 := @Eq.refl Nat 720

theorem EMRow27.d178 : @Eq Nat (Nat.pow 24 (Nat.succ (Nat.mul 2 5))) 1521681143169024 := @Eq.refl Nat 1521681143169024

noncomputable def ep1562 := nat_lit 1181671153346359170692730265957638242378174781758650

noncomputable def ep1563 := nat_lit 5986310706507378352962293074805895248510699696029696

noncomputable def ep1564 := nat_lit 2000000000000000000000000000000000000000000000000000

noncomputable def ep1565 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625

noncomputable def ep1566 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125

noncomputable def ep1567 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875

noncomputable def ep1568 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375

noncomputable def ep1569 := nat_lit 2442358029135994033939875

noncomputable def ep1570 := nat_lit 37260822860694382775919147000

noncomputable def ep1571 := nat_lit 116336546489037573337554931640625

noncomputable def ep1572 := nat_lit 57493278893883548332405996866302358825

noncomputable def ep1573 := nat_lit 40230676762013536063022911548614501953125

noncomputable def ep1574 := nat_lit 236310350532676991248348623960

noncomputable def ep1575 := nat_lit 344268321641720831394195556640625

noncomputable def ep1576 := nat_lit 81801971833623620377505564448994707675

noncomputable def ep1577 := nat_lit 56886557708273976459167897701263427734375

noncomputable def ep1578 := BSN.arctan_dyadic_bound_f 1 5 18 17 ep1563 ep1564 ep1565 ep1566 200200021673987500790625 ep1567 ep1568 ep1569 ep1562 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 ep1570 ep1571 151412625 ep1572 ep1573 1322214852783825 ep1565 ep1566 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 ep1570 ep1571 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 ep1572 ep1573 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 ep1574 ep1575 1267389585 ep1576 ep1577 1927077560082675 ep1567 ep1568 ep1569 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 ep1574 ep1575 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 ep1576 ep1577 1927077560082675 rfl rfl rfl rfl)) rfl

theorem EMRow27.d179 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz266 qz286)) Bool.false ep1562 ep1563 1 ep1564 := ep1578 rfl rfl rfl

noncomputable def ep1579 := nat_lit 25047178968060507272880539293402373975644382030403

noncomputable def ep1580 := nat_lit 4733915408010924740926662591654183582145509

noncomputable def ep1581 := nat_lit 77229300481955664312677298336960122659119574530232845

noncomputable def ep1582 := nat_lit 24516194103503660983641551147684725335332607

noncomputable def ep1583 := nat_lit 186647183216068817672719845704257068688983305564016735

noncomputable def ep1584 := BSN.arctan_dyadic_bound_f 1 239 6 5 ep1563 ep1564 ep1580 ep1581 9945 ep1582 ep1583 65835 ep1579 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 ep1580 ep1581 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 ep1582 ep1583 65835 rfl rfl rfl rfl) rfl rfl rfl

theorem EMRow27.d180 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz266 (@Nat.cast Real Real.instNatCast 239))) Bool.false ep1579 ep1563 1 ep1564 := ep1584 rfl

noncomputable def ep1585 := nat_lit 18806549737669504701992162098148602382148218980016788

noncomputable def ep1586 := nat_lit 100000000000000000000000000000000000000000000000000

theorem EMRow27.d181 : Enclosure.Real.IsNear Real.pi Bool.false ep1585 ep1563 1 ep1586 := BSN.pi_combine ep1562 ep1579 ep1563 ep1564 ep1586 ep1585 rfl rfl rfl rfl EMRow27.d179 EMRow27.d180

noncomputable def ep1587 := nat_lit 3081381023560590921039872

noncomputable def ep1588 := nat_lit 33895191259166500131438592

noncomputable abbrev qz531 := (@HAdd.hAdd Complex Complex Complex qz545 (@HAdd.hAdd Complex Complex Complex qz545 qz546 (@HMul.hMul Complex Complex Complex qz541 Complex.I ↑qz811)) qz819)

noncomputable abbrev qz233 := (@Norm.norm Complex Complex.instNorm qz531)

noncomputable abbrev qz234 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz865 2 3)))

noncomputable abbrev qz235 := (@HPow.hPow Complex Complex Complex qz815 qz593 (@HSub.hSub Complex Complex Complex qz577 (@Neg.neg Complex Complex.instNeg qz260) qz819))

noncomputable abbrev qz782 := (@HDiv.hDiv Real Real Real qz1 qz233 (@HAdd.hAdd Real Real Real qz337 (Complex.re qz12) qz286))

noncomputable def ep1589 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 24))) (@HMul.hMul Real Real Real qz0 qz782 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) 3444289965 44839995441152 24735855 44839995441152 3716984249587317537 36893488147419103232 13398937084353

noncomputable def ep1590 := nat_lit 166796628677329108154347897749504

noncomputable def ep1591 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 24)) 5055 85525504 15 85525504 681363 524288 2863 524288 3444289965 44839995441152

noncomputable abbrev qz532 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz533 := (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi)

noncomputable abbrev qz1095 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz532 qz533 4))

noncomputable def ep1592 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 30720 334084) qz1095 30720 334084 0 1 337 524288 1 524288 5055 85525504 15 85525504

noncomputable def ep1593 := nat_lit 611446774371975769155682509262542103857872115376664175900625

noncomputable def ep1594 := nat_lit 392318858461667547739736838950479151006397215279002157056

noncomputable def ep1595 := nat_lit 19652562622312316682495810535216024035134795670488584765154486969712234385047

noncomputable def ep1596 := nat_lit 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000

noncomputable def ep1597 := nat_lit 691463075802508163054686763366652189853178875

noncomputable def ep1598 := nat_lit 2787593149816327892691964784081045188247552

noncomputable def ep1599 := nat_lit 2184744797947834540264818678394244808492865883128339

noncomputable def ep1600 := nat_lit 9223372036854775808000000000000000000000000000000000000000000000

noncomputable def ep1601 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz532 qz533 3) qz533 ep1597 ep1598 ep1599 ep1600 884279719003555 140737488355328 1 500000000000000 ep1593 ep1594 ep1595 ep1596

noncomputable def ep1602 := nat_lit 781950621441006189802102638025

noncomputable def ep1603 := nat_lit 19807040628566084398385987584

noncomputable def ep1604 := nat_lit 26986075409044041160201671

noncomputable def ep1605 := nat_lit 1073741824000000000000000000000000000000

noncomputable def ep1606 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz532 qz533 2) qz533 ep1602 ep1603 ep1604 ep1605 884279719003555 140737488355328 1 500000000000000 ep1597 ep1598 ep1599 ep1600

noncomputable def ep1607 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz532 qz533 1) qz533 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1602 ep1603 ep1604 ep1605

noncomputable abbrev qz534 := (@Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi) (@HMul.hMul Real Real Real qz0 qz807 Real.pi) Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq (@Enclosure.Real.IsNear.mulLit_ff qz807 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl))

noncomputable def ep1608 := ep1607 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz532 qz533 1) qz533 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz533) qz534) qz534 rfl

noncomputable def ep1609 := @Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz532 qz533 3) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz532 qz533 2) qz533) Bool.false ep1597 ep1598 ep1599 ep1600 (BSN.pow_succ_r qz533 2 3 rfl) (ep1606 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz532 qz533 2) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz532 qz533 1) qz533) Bool.false ep1602 ep1603 ep1604 ep1605 (BSN.pow_succ_r qz533 1 2 rfl) ep1608) qz534 rfl)

noncomputable abbrev qz1096 := (@HPow.hPow Real Nat Real qz532 qz533 4)

noncomputable def ep1610 := @Enclosure.Real.IsNear.inv_image qz1096 ep1593 ep1594 ep1595 ep1596 168 169 262144 (@Enclosure.Real.IsNear.of_eq qz1096 (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz532 qz533 3) qz533) Bool.false ep1593 ep1594 ep1595 ep1596 (BSN.pow_succ_r qz533 3 4 rfl) (ep1601 ep1609 qz534 rfl))

noncomputable def ep1611 := ep1592 (Enclosure.Real.IsNear.const Bool.false 30720 334084) (@Enclosure.Real.IsNear.recentre' qz1095 Bool.false 337 524288 1 524288 337 524288 1 524288 (ep1610 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep1612 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 24)) (Real.sqrt (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 2 24)) (Complex.re (zetaApproximant qz12 2 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 2 24)) (Complex.im (zetaApproximant qz12 2 24))))) Bool.false 681363 524288 2863 524288

noncomputable def ep1613 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 2 24)) (Complex.re (zetaApproximant qz12 2 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 2 24)) (Complex.im (zetaApproximant qz12 2 24))))) Bool.false 681363 524288 2863 524288

noncomputable def ep1614 := nat_lit 1731516901941927877923712983905425456802796051692448678401

noncomputable def ep1615 := nat_lit 1025185144590505445713231785582167453387980800000000000000

noncomputable def ep1616 := nat_lit 13657450585480584905240459329274664286231352962255982835772475836251892453

noncomputable def ep1617 := nat_lit 962735028834830380984302418293038748203136015601126779031388160000000000000

noncomputable def ep1618 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 2 24)) (Complex.re (zetaApproximant qz12 2 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 2 24)) (Complex.im (zetaApproximant qz12 2 24)))) ep1614 ep1615 ep1616 ep1617 339250 342113

noncomputable def ep1619 := nat_lit 1200519640226911724953921083195262846612499976544577928889810810561

noncomputable def ep1620 := nat_lit 710816550852021870949805631121173089934290030533017600000000000000

noncomputable def ep1621 := nat_lit 27112374303296753376223230895581838316088055907635877392919849886153051467

noncomputable def ep1622 := nat_lit 1925470057669660761968604836586077496406272031202253558062776320000000000000

noncomputable def ep1623 := nat_lit 35087350574162216773700483080333110542967580916777042710588561

noncomputable def ep1624 := nat_lit 22502985296046270473076418107498917374961112986232030958344642927859271

noncomputable def ep1625 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 2 24)) (Complex.re (zetaApproximant qz12 2 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 2 24)) (Complex.im (zetaApproximant qz12 2 24))) ep1619 ep1620 ep1621 ep1622 ep1623 ep1620 ep1624

noncomputable def ep1626 := nat_lit 213941117518851195774289426287341944045141336800250395340308480000000000000

noncomputable def ep1627 := nat_lit 853374170565717261160566263445262597949171104141823763735502128200413849432168163815706086817456510788193671768650547200000000000000

noncomputable def ep1628 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz12 2 24)) (Complex.re (zetaApproximant qz12 2 24)) ep331 ep332 ep333 ep334 ep331 ep332 ep333 ep334 ep1619

noncomputable def ep1629 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz12 2 24)) (Complex.im (zetaApproximant qz12 2 24)) ep519 ep332 ep520 ep521 ep519 ep332 ep520 ep521 ep1623

noncomputable def ep1630 := @ep1589 405828369621610135552 ep1590 310682931313904203762017 ep1587 19817277758615508993 ep1588 (@ep1591 24735855 44839995441152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 2 4) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 30720 334084) qz1095) Bool.false 5055 85525504 15 85525504 (BSN.theta_err_eq 2 4 30720 334084 EMRow27.d20 EMRow27.d21 rfl) (ep1611 rfl)) (ep1612 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz12 2 24)) (@ep1613 681363 524288 2863 524288 (@ep1618 262144 (@ep1625 ep1626 ep1627 ep1614 ep1615 ep1616 ep1617 (@ep1628 ep1620 ep1621 ep1622 ep745 ep745 rfl) (@ep1629 ep1620 ep1624 ep1626 ep751 ep751 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz1097 := (Enclosure.sfrac Bool.false 2 11)

noncomputable def ep1631 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz782 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz233 qz1097) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) Bool.false 3716984249587317537 36893488147419103232 13398937084353 405828369621610135552 (BSN.zrb_shape_eq qz233 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) qz9 5)

noncomputable def ep1632 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz233 qz1097) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) 48893697 2883584 1 2883584 836239213931 140737488355328 256939 140737488355328

noncomputable def ep1633 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz1097 48893697 524288 1 524288 2 11 0 1 48893697 2883584

noncomputable abbrev qz236 := (Complex.re qz531)

noncomputable abbrev qz237 := (Complex.im qz531)

noncomputable abbrev qz238 := qz531

noncomputable abbrev qz1098 := (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 qz236 qz236) (@HMul.hMul Real Real Real qz0 qz237 qz237))

noncomputable def ep1634 := @Enclosure.Real.IsNear.of_eq qz233 (Real.sqrt qz1098) Bool.false 48893697 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz238)

noncomputable def ep1635 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz1098) Bool.false 48893697 524288 1 524288 48893697

noncomputable def ep1636 := @Enclosure.Real.IsNear.sqrt_image qz1098 347877161 40000 0 1 24446848 24446849 262144

noncomputable def ep1637 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz236 qz236) (@HMul.hMul Real Real Real qz0 qz237 qz237) 121 4 0 1 346667161 40000 0 1

noncomputable def ep1638 := @Enclosure.Real.IsNear.mulLit_ff qz236 qz236 11 2 0 1 11 2 0 1 121 4

noncomputable def ep1639 := @Enclosure.Complex.IsNear.of_eq qz238 (Complex.mk (Enclosure.sfrac Bool.false 11 2) qz9) Bool.false 11 2 0 1 Bool.false 93095 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 93095 1000 5 (@Eq.refl Real qz9))

noncomputable abbrev qz783 := (ep1639 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 11 2) qz9 Bool.false 11 2 0 1 Bool.false 93095 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 11 2) qz271))

noncomputable def ep1640 := @ep1638 0 1 (@Enclosure.Complex.IsNear.re_isNear qz238 Bool.false 11 2 0 1 Bool.false 93095 1000 0 1 qz783)

noncomputable def ep1641 := ep1640 (@Enclosure.Complex.IsNear.re_isNear qz238 Bool.false 11 2 0 1 Bool.false 93095 1000 0 1 qz783)

noncomputable def ep1642 := @Enclosure.Real.IsNear.mulLit_ff qz237 qz237 93095 1000 0 1 93095 1000 0 1 346667161 40000

noncomputable def ep1643 := @ep1642 0 1 (@Enclosure.Complex.IsNear.im_isNear qz238 Bool.false 11 2 0 1 Bool.false 93095 1000 0 1 qz783)

noncomputable def ep1644 := ep1643 (@Enclosure.Complex.IsNear.im_isNear qz238 Bool.false 11 2 0 1 Bool.false 93095 1000 0 1 qz783)

noncomputable def ep1645 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Real.sqrt (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))))) Bool.false 836239213931 140737488355328

noncomputable def ep1646 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))))) Bool.false 836239213931 140737488355328

noncomputable def ep1647 := nat_lit 5764500257229969518512828255359279518313737156936813029706279085170549741965841821

noncomputable def ep1648 := nat_lit 163275189700196669532826817139253103856911966267491961940765730406400000000000000000000

noncomputable def ep1649 := nat_lit 1770642224222576713441824254515516438071778653018713901551625467400651585802018547081453787047

noncomputable def ep1650 := nat_lit 81613500159875487721114665346524634053243579868994875532324476285247826098651136000000000000000000000000

noncomputable def ep1651 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)))) ep1647 ep1648 ep1649 ep1650

noncomputable def ep1652 := nat_lit 64159990046601935591733035544246696234145923715900132674098005148964456336714961

noncomputable def ep1653 := nat_lit 4535421936116574153689633809423697329358665729652554498354603622400000000000000000000

noncomputable def ep1654 := nat_lit 5000258500156019925739322650402678289680948706711521775627835427276134298431549141478819817

noncomputable def ep1655 := nat_lit 637605469999027247821208323019723703540965467726522465096284970978498641395712000000000000000000000000

noncomputable def ep1656 := nat_lit 138189624622091993488417559030655938155379356126576330137550035992313172553764129

noncomputable def ep1657 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) ep1652 ep1653 ep1654 ep1655 ep1656

noncomputable def ep1658 := nat_lit 6531007588007866781313072685570124154276478650699678477630629216256000000000000000000

noncomputable def ep1659 := nat_lit 1130609136202606162947190955263973616992617218559639114271262532709306395602780256972164850471

noncomputable def ep1660 := nat_lit 1045777636695617523592187978456436947764007617277617574862549127096926102344757278304291059885583100594062084577754774468281480478021346591680495616000000000000000000

noncomputable def ep1661 := nat_lit 8009993136489065406328573573735167521719

noncomputable def ep1662 := nat_lit 2129653008383425394514461385031680000000000

noncomputable def ep1663 := nat_lit 2354550890105590045229331259201993301442331

noncomputable def ep1664 := nat_lit 2258504762003440625592458845179384692736000000000000

noncomputable def ep1665 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) ep1661 ep1662 ep1663 ep1664 ep1661 ep1662 ep1663

noncomputable def ep1666 := nat_lit 11755408313712118502102362757359861062127

noncomputable def ep1667 := nat_lit 2555583610060110473417353662038016000000000

noncomputable def ep1668 := nat_lit 13603598247553295472437497380242510732726689

noncomputable def ep1669 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235) Bool.false ep1661 ep1662 ep1663 ep1664 Bool.false ep1666 ep1667 ep1668

noncomputable def ep1670 := nat_lit 9034019048013762502369835380717538770944000000000000

noncomputable def ep1671 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235 Bool.false ep1661 ep1662 ep1663 ep1664 Bool.false ep1666 ep1667 ep1668 ep1670

noncomputable def ep1672 := nat_lit 692355684273616885857924530510645333

noncomputable def ep1673 := nat_lit 1022233444024044189366941464815206400000

noncomputable def ep1674 := nat_lit 678390866655473160005213568582077720531

noncomputable def ep1675 := nat_lit 3613607619205505000947934152287015508377600000000

noncomputable def ep1676 := nat_lit 19702756382757090682373692405513969233907

noncomputable def ep1677 := nat_lit 6388959025150276183543384155095040000000000

noncomputable def ep1678 := nat_lit 241319574805739915028259097354774340763807

noncomputable def ep1679 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz235)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz235)) ep1672 ep1673 ep1674 ep1675 ep1676 ep1677 ep1678

noncomputable def ep1680 := nat_lit 282313095250430078199057355647423086592000000000000

noncomputable def ep1681 := nat_lit 24564248611566519571362484978838584223288919826531863719326806376180403404800000

noncomputable def ep1682 := nat_lit 933575050431316396160903953860526080

noncomputable def ep1683 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz235) 120046390774619921 3870720000000 0 1 432555081293618937975 ep1603 5651072575177310773411 ep1682 ep1672

noncomputable def ep1684 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) 120046390774619921 3870720000000 0 1 0 1 0 1 120046390774619921

noncomputable def ep1685 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 120046390774619921 128000000 0 1 120046390774619921 3870720000000 0

noncomputable def ep1686 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (Complex.mk (Enclosure.sfrac Bool.false 1 30240) qz263) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 3 1 42 720 Bool.false EMRow27.d176 EMRow27.d177 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 30240) qz263 Bool.false 1 30240 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 30240) qz275)

noncomputable abbrev qz239 := (@HAdd.hAdd Complex Complex Complex qz261 qz260 qz262)

noncomputable def ep1687 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) qz239) Bool.false 120046390774619921 128000000 0 1 Bool.false 2222754000130263029099 320000000000 0 1

noncomputable def ep1688 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz239)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz239)) 1078919975316059289 3200000000 0 1 120139987128089921 200000000 0 1

noncomputable def ep1689 := nat_lit 600231953873099605000000000

noncomputable def ep1690 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz239) 119879997257339921 1600000000 0 1 9 2 0 1 1078919975316059289 3200000000

noncomputable abbrev qz240 := (@HAdd.hAdd Complex Complex Complex qz261 qz260 qz548)

noncomputable def ep1691 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) qz240) Bool.false 119879997257339921 1600000000 0 1 Bool.true 6452547780659 1000000 0 1

noncomputable def ep1692 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz240)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz240)) 21838981143 160000 0 1 120098387068769921 1600000000 0 1

noncomputable def ep1693 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz240) 3119854449 80000 0 1 7 2 0 1 21838981143 160000

noncomputable abbrev qz784 := (ep278 (BSN.ascPochhammer_succ_eval_c 2 3 qz12 rfl) (ep306 (@ep307 258012540026360 6450313500659 8000000 0 1 (ep310 rfl) (ep313 rfl) rfl rfl)))

noncomputable def ep1694 := @ep1693 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 qz784)

noncomputable def ep1695 := @Enclosure.Complex.IsNear.of_eq qz240 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz9) Bool.false 7 2 0 1 Bool.false 93095 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 93095 1000 3 (@Eq.refl Real qz9))

noncomputable abbrev qz785 := (ep1695 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz9 Bool.false 7 2 0 1 Bool.false 93095 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz271))

noncomputable def ep1696 := ep1694 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 7 2 0 1 Bool.false 93095 1000 0 1 qz785)

noncomputable def ep1697 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz240) 6450313500659 8000000 0 1 93095 1000 0 1 120098387068769921 1600000000

noncomputable def ep1698 := @ep1697 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 qz784)

noncomputable def ep1699 := ep1698 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 7 2 0 1 Bool.false 93095 1000 0 1 qz785)

noncomputable def ep1700 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) qz240 Bool.false 119879997257339921 1600000000 0 1 Bool.true 6452547780659 1000000 0 1 (@ep1692 19180799561174387360000 119879997257339921 1600000000 0 1 (ep1696 rfl) (ep1699 rfl) rfl rfl)

noncomputable def ep1701 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz240)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz240)) 58088569985931 16000000 0 1 45152194504613 16000000 0 1

noncomputable def ep1702 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz240) 3119854449 80000 0 1 93095 1000 0 1 58088569985931 16000000

noncomputable def ep1703 := @ep1702 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 qz784)

noncomputable def ep1704 := ep1703 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 7 2 0 1 Bool.false 93095 1000 0 1 qz785)

noncomputable def ep1705 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz240) 6450313500659 8000000 0 1 7 2 0 1 45152194504613 16000000

noncomputable def ep1706 := @ep1705 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3119854449 80000 0 1 Bool.true 6450313500659 8000000 0 1 qz784)

noncomputable def ep1707 := ep1706 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 7 2 0 1 Bool.false 93095 1000 0 1 qz785)

noncomputable abbrev qz786 := (ep1691 (BSN.ascPochhammer_succ_eval_c 3 4 qz12 rfl) (ep1700 (@ep1701 1651852231848704000000 6452547780659 1000000 0 1 (ep1704 rfl) (ep1707 rfl) rfl rfl)))

noncomputable def ep1708 := @ep1690 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 119879997257339921 1600000000 0 1 Bool.true 6452547780659 1000000 0 1 qz786)

noncomputable def ep1709 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk (Enclosure.sfrac Bool.false 9 2) qz9) Bool.false 9 2 0 1 Bool.false 93095 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 93095 1000 4 (@Eq.refl Real qz9))

noncomputable abbrev qz787 := (ep1709 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9 2) qz9 Bool.false 9 2 0 1 Bool.false 93095 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 9 2) qz271))

noncomputable def ep1710 := ep1708 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 9 2 0 1 Bool.false 93095 1000 0 1 qz787)

noncomputable def ep1711 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz239) 6452547780659 1000000 0 1 93095 1000 0 1 120139987128089921 200000000

noncomputable def ep1712 := @ep1711 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 119879997257339921 1600000000 0 1 Bool.true 6452547780659 1000000 0 1 qz786)

noncomputable def ep1713 := ep1712 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 9 2 0 1 Bool.false 93095 1000 0 1 qz787)

noncomputable def ep1714 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) qz239 Bool.false 120046390774619921 128000000 0 1 Bool.false 2222754000130263029099 320000000000 0 1 (@ep1688 ep1689 120046390774619921 128000000 0 1 (ep1710 rfl) (ep1713 rfl) rfl rfl)

noncomputable def ep1715 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz239)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz239)) 2232045668934411989099 320000000000 0 1 58072930025931 2000000 0 1

noncomputable def ep1716 := nat_lit 4445508000260526058198000000

noncomputable def ep1717 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz239) 119879997257339921 1600000000 0 1 93095 1000 0 1 2232045668934411989099 320000000000

noncomputable def ep1718 := @ep1717 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 119879997257339921 1600000000 0 1 Bool.true 6452547780659 1000000 0 1 qz786)

noncomputable def ep1719 := ep1718 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 9 2 0 1 Bool.false 93095 1000 0 1 qz787)

noncomputable def ep1720 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz239) 6452547780659 1000000 0 1 9 2 0 1 58072930025931 2000000

noncomputable def ep1721 := @ep1720 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 119879997257339921 1600000000 0 1 Bool.true 6452547780659 1000000 0 1 qz786)

noncomputable def ep1722 := ep1721 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 9 2 0 1 Bool.false 93095 1000 0 1 qz787)

noncomputable abbrev qz788 := (ep1687 (BSN.ascPochhammer_succ_eval_c 4 5 qz12 rfl) (ep1714 (@ep1715 ep1716 2222754000130263029099 320000000000 0 1 (ep1719 rfl) (ep1722 rfl) rfl rfl)))

noncomputable def ep1723 := @ep1685 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1686) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 120046390774619921 128000000 0 1 Bool.false 2222754000130263029099 320000000000 0 1 qz788)

noncomputable def ep1724 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 2222754000130263029099 320000000000 0 1 0 1 0

noncomputable def ep1725 := @ep1724 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1686) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 120046390774619921 128000000 0 1 Bool.false 2222754000130263029099 320000000000 0 1 qz788)

noncomputable def ep1726 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) 2222754000130263029099 9676800000000000 0 1 0 1 0 1 2222754000130263029099

noncomputable def ep1727 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 2222754000130263029099 320000000000 0 1 2222754000130263029099 9676800000000000 0

noncomputable def ep1728 := @ep1727 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1686) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 120046390774619921 128000000 0 1 Bool.false 2222754000130263029099 320000000000 0 1 qz788)

noncomputable def ep1729 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 120046390774619921 128000000 0 1 0 1 0

noncomputable def ep1730 := @ep1729 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1686) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 120046390774619921 128000000 0 1 Bool.false 2222754000130263029099 320000000000 0 1 qz788)

noncomputable def ep1731 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 120046390774619921 3870720000000 0 1 Bool.false 2222754000130263029099 9676800000000000 0 1 (@ep1684 120046390774619921 3870720000000 0 1 (ep1723 rfl) (ep1725 rfl) rfl rfl) (@ep1726 2222754000130263029099 9676800000000000 0 1 (ep1728 rfl) (ep1730 rfl) rfl rfl)

noncomputable def ep1732 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 120046390774619921 3870720000000 0 1 Bool.false 2222754000130263029099 9676800000000000 0 1 ep1731

noncomputable def ep1733 := nat_lit 9903520314283042199192993792

noncomputable def ep1734 := nat_lit 29174220325978637380028248558141440

noncomputable def ep1735 := @Enclosure.Complex.IsNear.re_isNear qz235 Bool.false 432555081293618937975 ep1603 5651072575177310773411 ep1682 Bool.true 132961787819991035895 ep1733 108567828374888782493 ep1734

noncomputable abbrev qz535 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 1521681143169024)))

noncomputable def ep1736 := @Enclosure.Complex.IsNear.of_eq qz235 (Complex.mk (@HMul.hMul Real Real Real qz0 qz535 (Real.cos qz361)) (@HMul.hMul Real Real Real qz0 qz535 qz903)) Bool.false 432555081293618937975 ep1603 5651072575177310773411 ep1682 Bool.true 132961787819991035895 ep1733 108567828374888782493

noncomputable abbrev qz536 := (Real.sqrt (@Nat.cast Real Real.instNatCast 1521681143169024))

noncomputable abbrev qz537 := (@Nat.cast Real Real.instNatCast 1521681143169024)

noncomputable def ep1737 := @Enclosure.Real.IsNear.inv_image qz536 5489990913150197828255 140737488355328 1 140737488355328 1803922 1803923 70368744177664 (@Enclosure.Real.IsNear.of_eq qz536 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz537 qz266)) Bool.false 5489990913150197828255 140737488355328 1 140737488355328 (BSN.sqrt_natCast_div_one 1521681143169024) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz537 qz266)) Bool.false 5489990913150197828255 140737488355328 1 140737488355328 5489990913150197828255 140737488355328 1 140737488355328 (BSN.sqrt_enclosure 1521681143169024 1 2744995456575098914127 2744995456575098914128 70368744177664 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1738 := nat_lit 3477838078257875130179911680

noncomputable def ep1739 := nat_lit 30165436800000000000000000

noncomputable def ep1740 := nat_lit 8057323691196381544451112173568

noncomputable def ep1741 := nat_lit 2535301200456458802993406410752

noncomputable def ep1742 := nat_lit 24711525826560000000000000000

noncomputable def ep1743 := nat_lit 44992639437845299200000000000000000000

noncomputable def ep1744 := nat_lit 614724096498688896779568985355059200

noncomputable def ep1745 := BSN.log_dyadic_bound 8 40 10 9 ep1743 70368744177664 24711525826560 ep1744 620765814357606216499200 28532070465432 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 8) (BSN.artanhQ 40) 0 9 ep1744 ep1743 620765814357606216499200 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1746 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz362 93095 1000 0 1 3578170511529591 1125899906842624 6706824361 150827184000000000000000 66621956754169454829 225179981368524800 124874362777459 ep1739 qz271 (BSN.isNear_log_sfrac 24 1 3578170511529591 1125899906842624 6706824361 150827184000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz603) Bool.false ep1740 ep1741 1098846103306240 ep1742 3578170511529591 1125899906842624 6706824361 150827184000000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 28532070465432 70368744177664 24973259072661432 36028797018963968 24711525826560 1000000000000000 rfl rfl rfl rfl (ep1745 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1747 := nat_lit 928790212123343151394317993195449123449674297609138503091639812096

noncomputable def ep1748 := nat_lit 1684996666696914987166688442938726917102321526408785780068975640576

noncomputable def ep1749 := nat_lit 605760435021524736243710665720809012604318106672110969652595384855913918093402580720011724997261934575985607080341863792277141301495921857423626692511232040557369523504186862365824182316391209548526135418223037807841

noncomputable def ep1750 := nat_lit 157475844566194586710377858717712139937779852880999049736115734363710475742484286820110103296463932017452925328428721010605290554933102646532775267477867748133619504176774923002822752918037699780581068853165128522137600

noncomputable def ep1751 := nat_lit 258642559603458592344202939450318888813345008591618235759186788657049176320915930994872214574964329065364260564565026240198598871447043126481880393120642467719928899155262560599662290680834563261912204737761

noncomputable def ep1752 := nat_lit 3674812020491343901564377243991909660537045945387548641890703308199636594095999408112996264460333563187555626588542173850674855986487935535753122701011368299623679109904690972275220151122461833387619749142282650025185

noncomputable def ep1753 := nat_lit 14330301855523707390644385143311804734337966612170913525986531827097653292566070100630019399978217813588216204887013611965081440498912340834482549340485965080159374880086517993256870515541430680032877265638026695514521600

noncomputable def ep1754 := BSN.cos_dyadic_bound_f 158876012930708233 288230376151711744 4 3 140737488355328 49471316352001 ep1749 ep1750 ep1751 ep1752 ep1753 ep1751 119892922587755 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 158876012930708233) (BSN.cosEvenQ 288230376151711744) 0 3 ep1749 ep1750 ep1751 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 158876012930708233) (BSN.cosOddQ 288230376151711744) 0 3 ep1752 ep1753 ep1751 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz789 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41638722971355909) (@Nat.cast Real Real.instNatCast 140737488355328))

noncomputable def ep1755 := @Enclosure.Real.IsNear.cos_image qz361 qz789 Bool.false 41638722971355909 140737488355328 583 140737488355328 Bool.false 119892922587755 140737488355328 1 24711525826560 (@Enclosure.Real.IsNear.recentre' qz361 Bool.false 66621956754169454829 225179981368524800 124874362777459 ep1739 41638722971355909 140737488355328 583 140737488355328 (ep1746 rfl) rfl) (Enclosure.sfrac_false_div 41638722971355909 140737488355328) (BSN.cos_reduce0 qz789 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1747) (@Nat.cast Real Real.instNatCast ep1748)) ep1585 ep1563 Bool.false 119892922587755 140737488355328 47 ep1586 49423051653120 24711525826560 (BSN.sin_reduce_arg_pos_rat_q0 41638722971355909 140737488355328 ep1585 ep1563 47 ep1747 ep1748 rfl rfl rfl rfl) EMRow27.d181 (@BSN.cos_arg_round Bool.false 119892922587755 140737488355328 ep1747 ep1748 158876012930708233 288230376151711744 49471316352001 49423051653120 (ep1754 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1756 := nat_lit 1574938668548197972299558575455653932684754512835952736739441785673621673817779335883583809644217976274685045494490920491280239220834184506238009714525267413233340194785741631019641944332103413520486836048916006337761

noncomputable def ep1757 := nat_lit 2047185979360529627234912163330257819191138087452987646569504546728236184652295728661431342854031116226888029269573373137868777214130334404926078477212280725737053554298073999036695787934490097147553895091146670787788800

noncomputable def ep1758 := nat_lit 7874544738161658215887267160094339371890369776887037262880238339529100743243789119162737106544612915084956931900348277491159985452799999729784021152662505613050614169970495846610710807346431739952305279031050713988321

noncomputable def ep1759 := nat_lit 71651509277618536953221925716559023671689833060854567629932659135488266462830350503150096999891089067941081024435068059825407202494561704172412746702429825400796874400432589966284352577707153400164386328190133477572608000

noncomputable def ep1760 := BSN.sin_dyadic_bound_f 158876012930708233 288230376151711744 4 3 140737488355328 49471316352001 ep1756 ep1757 ep1751 ep1758 ep1759 ep1751 73707039975382 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 158876012930708233) (BSN.sinEvenQ 288230376151711744) 0 3 ep1756 ep1757 ep1751 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 158876012930708233) (BSN.sinOddQ 288230376151711744) 0 3 ep1758 ep1759 ep1751 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1761 := @Enclosure.Real.IsNear.sin_image qz361 qz789 Bool.false 41638722971355909 140737488355328 583 140737488355328 Bool.false 73707039975382 140737488355328 1 24711525826560 (@Enclosure.Real.IsNear.recentre' qz361 Bool.false 66621956754169454829 225179981368524800 124874362777459 ep1739 41638722971355909 140737488355328 583 140737488355328 (ep1746 rfl) rfl) (Enclosure.sfrac_false_div 41638722971355909 140737488355328) (BSN.sin_reduce0 qz789 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1747) (@Nat.cast Real Real.instNatCast ep1748)) ep1585 ep1563 Bool.false 73707039975382 140737488355328 47 ep1586 49423051653120 24711525826560 (BSN.sin_reduce_arg_pos_rat_q0 41638722971355909 140737488355328 ep1585 ep1563 47 ep1747 ep1748 rfl rfl rfl rfl) EMRow27.d181 (@BSN.sin_arg_round Bool.false 73707039975382 140737488355328 ep1747 ep1748 158876012930708233 288230376151711744 49471316352001 49423051653120 (ep1760 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz790 := (@Enclosure.Real.IsNear.recentre' qz535 Bool.false 3607845 140737488355328 1 140737488355328 3607845 140737488355328 1 140737488355328 (ep1737 rfl rfl) rfl)

noncomputable def ep1762 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz535 (Real.cos qz361)) (@HMul.hMul Real Real Real qz0 qz535 qz903) Bool.false 432555081293618937975 ep1603 5651072575177310773411 ep1682 Bool.true 132961787819991035895 ep1733 108567828374888782493 ep1734 (@Enclosure.Real.IsNear.mulLit_ff qz535 (Real.cos qz361) 3607845 140737488355328 1 140737488355328 119892922587755 140737488355328 27747263041 6633449703708410511360 432555081293618937975 ep1603 5651072575177310773411 ep1682 qz790 (@Enclosure.Real.IsNear.recentre' (Real.cos qz361) Bool.false 119892922587755 140737488355328 14547557045239808 ep1738 119892922587755 140737488355328 27747263041 6633449703708410511360 (ep1755 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz535 qz903 3607845 140737488355328 1 140737488355328 36853519987691 70368744177664 27747263041 6633449703708410511360 132961787819991035895 ep1733 108567828374888782493 ep1734 qz790 (@Enclosure.Real.IsNear.neg (Real.sin qz361) Bool.false 36853519987691 70368744177664 27747263041 6633449703708410511360 (@Enclosure.Real.IsNear.recentre' (Real.sin qz361) Bool.false 73707039975382 140737488355328 14547557045239808 ep1738 36853519987691 70368744177664 27747263041 6633449703708410511360 (ep1761 rfl rfl) rfl)) rfl)

noncomputable def ep1763 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz235) 2222754000130263029099 9676800000000000 0 1 132961787819991035895 ep1733 108567828374888782493 ep1734 ep1676

noncomputable def ep1764 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 120046390774619921 3870720000000 0 1 Bool.false 2222754000130263029099 9676800000000000 0 1 ep1731

noncomputable def ep1765 := @Enclosure.Complex.IsNear.im_isNear qz235 Bool.false 432555081293618937975 ep1603 5651072575177310773411 ep1682 Bool.true 132961787819991035895 ep1733 108567828374888782493 ep1734

noncomputable def ep1766 := nat_lit 1064105515915382884579692499712870953

noncomputable def ep1767 := nat_lit 2555583610060110473417353662038016000000

noncomputable def ep1768 := nat_lit 13033175950643767628677757348513843053

noncomputable def ep1769 := nat_lit 112925238100172031279622942258969234636800000000

noncomputable def ep1770 := nat_lit 12819513829627501386682055257072732015127

noncomputable def ep1771 := nat_lit 12560944171501794062143276792361403288486689

noncomputable def ep1772 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz235)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz235)) ep1766 ep1767 ep1768 ep1769 ep1770 ep1667 ep1771

noncomputable def ep1773 := nat_lit 30041928816087051461302079342456583395095894110741215244744705437211820032000000

noncomputable def ep1774 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz235) 120046390774619921 3870720000000 0 1 132961787819991035895 ep1733 108567828374888782493 ep1734 ep1766

noncomputable def ep1775 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz235) 2222754000130263029099 9676800000000000 0 1 432555081293618937975 ep1603 5651072575177310773411 ep1682 ep1770

noncomputable abbrev qz791 := (@ep1736 ep1734 (BSN.cpow_neg_s_sub_mk qz9 93095 1000 24 5 1521681143169024 (@Eq.refl Real qz9) rfl EMRow27.d178) ep1762)

noncomputable def ep1776 := ep1671 (@ep1679 ep1680 ep1681 ep1661 ep1662 ep1663 ep1664 (@ep1683 ep1673 ep1674 ep1675 ep1732 (ep1735 qz791) rfl) (@ep1763 ep1677 ep1678 ep1680 ep1764 (ep1765 qz791) rfl) rfl rfl) (@ep1772 ep1670 ep1773 ep1666 ep1667 ep1668 ep1670 (@ep1774 ep1767 ep1768 ep1769 ep1732 (ep1765 qz791) rfl) (@ep1775 ep1667 ep1771 ep1670 ep1764 (ep1735 qz791) rfl) rfl rfl)

noncomputable def ep1777 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) ep1666 ep1667 ep1668 ep1670 ep1666 ep1667 ep1668

noncomputable def ep1778 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235) Bool.false ep1661 ep1662 ep1663 ep1664 Bool.false ep1666 ep1667 ep1668

noncomputable def ep1779 := @ep1632 3716984249587317537 36893488147419103232 13398937084353 405828369621610135552 (@ep1633 1 2883584 (ep1634 (@ep1635 524288 1 524288 (ep1636 (@ep1637 1391508644 347877161 40000 0 1 (ep1641 rfl) (ep1644 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 11) rfl) (@ep1645 256939 140737488355328 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (@ep1646 256939 140737488355328 836239213931 140737488355328 256939 140737488355328 (@ep1651 418119478496 418119735435 70368744177664 (@ep1657 ep1658 ep1659 ep1650 ep1660 ep1647 ep1648 ep1649 ep1650 (@ep1665 ep1664 ep1652 ep1653 ep1654 ep1655 (@ep1669 ep1670 ep1776) (@ep1669 ep1670 ep1776) rfl) (@ep1777 ep1670 ep1656 ep1658 ep1659 ep1650 (@ep1778 ep1670 ep1776) (@ep1778 ep1670 ep1776) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow27.d182 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 24))) (@HMul.hMul Real Real Real qz0 qz782 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)))) Bool.false 310682931313904203762017 ep1587 19817277758615508993 ep1588 := ep1630 (ep1631 ep1779) rfl rfl

noncomputable def ep1780 := nat_lit 3958592069205634724454469

noncomputable abbrev qz538 := (@HAdd.hAdd Complex Complex Complex qz545 (@HAdd.hAdd Complex Complex Complex qz545 qz546 (@HMul.hMul Complex Complex Complex qz541 Complex.I ↑qz910)) qz819)

noncomputable abbrev qz241 := (@Norm.norm Complex Complex.instNorm qz538)

noncomputable abbrev qz242 := (@HPow.hPow Complex Complex Complex qz815 qz593 (@HSub.hSub Complex Complex Complex qz577 (@Neg.neg Complex Complex.instNeg qz369) qz819))

noncomputable abbrev qz792 := (@HDiv.hDiv Real Real Real qz1 qz241 (@HAdd.hAdd Real Real Real qz337 (Complex.re qz64) qz286))

noncomputable def ep1781 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 24))) (@HMul.hMul Real Real Real qz0 qz792 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) 637349565 22419997720576 9394845 22419997720576 47384831431332610309 405828369621610135552 14315916607691

noncomputable def ep1782 := nat_lit 1062626467215198115028369737252864

noncomputable def ep1783 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 24)) 5055 85525504 15 85525504 126083 262144 185 32768 637349565 22419997720576

noncomputable def ep1784 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 24)) (Real.sqrt (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 24)) (Complex.re (zetaApproximant qz64 2 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 24)) (Complex.im (zetaApproximant qz64 2 24))))) Bool.false 126083 262144 185 32768

noncomputable def ep1785 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 24)) (Complex.re (zetaApproximant qz64 2 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 24)) (Complex.im (zetaApproximant qz64 2 24))))) Bool.false 252166 524288 2960 524288

noncomputable def ep1786 := nat_lit 27684266866480079534224816794259444735794170051250807593

noncomputable def ep1787 := nat_lit 119657462810068256726906813716944407809228800000000000000

noncomputable def ep1788 := nat_lit 356130360216193084328962208122273394368769434511201615774548633650894169

noncomputable def ep1789 := nat_lit 65577030849880648338809240097331413864908863112198704909516800000000000000

noncomputable def ep1790 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 24)) (Complex.re (zetaApproximant qz64 2 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 24)) (Complex.im (zetaApproximant qz64 2 24)))) ep1786 ep1787 ep1788 ep1789 124603 127563

noncomputable def ep1791 := nat_lit 806508124973461016068211580866447187360178923156787059146743681

noncomputable def ep1792 := nat_lit 3486061168562159616233430765716563148437231560032256000000000000

noncomputable def ep1793 := nat_lit 703560788221972881984710134173117052761571256717238017943351018085150759

noncomputable def ep1794 := nat_lit 131154061699761296677618480194662827729817726224397409819033600000000000000

noncomputable def ep1795 := nat_lit 100558646896036425936154888222720906288108693631983061436481

noncomputable def ep1796 := nat_lit 9683503246005998933981752126990453190103421000089600000000000000

noncomputable def ep1797 := nat_lit 8699932210413286673214282071429735975967612305165213605746249216637579

noncomputable def ep1798 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 24)) (Complex.re (zetaApproximant qz64 2 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 24)) (Complex.im (zetaApproximant qz64 2 24))) ep1791 ep1792 ep1793 ep1794 ep1795 ep1796 ep1797

noncomputable def ep1799 := nat_lit 7810174599704829028276365053790452799758873662883597166479606170047493262441811105834539939398925318406419288948736000000000000

noncomputable def ep1800 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz64 2 24)) (Complex.re (zetaApproximant qz64 2 24)) ep1031 ep1032 ep1033 ep1034 ep1031 ep1032 ep1033 ep1034 ep1791

noncomputable def ep1801 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz64 2 24)) (Complex.im (zetaApproximant qz64 2 24)) ep1208 ep1209 ep1210 ep1034 ep1208 ep1209 ep1210 ep1034 ep1795

noncomputable def ep1802 := @ep1781 405828369621610135552 ep1782 ep1780 ep1588 15399073984139130251 ep1588 (@ep1783 9394845 22419997720576 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 2 4) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 30720 334084) qz1095) Bool.false 5055 85525504 15 85525504 (BSN.theta_err_eq 2 4 30720 334084 EMRow27.d20 EMRow27.d21 rfl) (ep1611 rfl)) (ep1784 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz64 2 24)) (@ep1785 126083 262144 185 32768 (@ep1790 262144 (@ep1798 ep1794 ep1799 ep1786 ep1787 ep1788 ep1789 (@ep1800 ep1792 ep1793 ep1794 ep1422 ep1422 rfl) (@ep1801 ep1796 ep1797 ep1794 ep1428 ep1428 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable def ep1803 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz792 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz241 qz1097) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) Bool.false 47384831431332610309 405828369621610135552 14315916607691 405828369621610135552 (BSN.zrb_shape_eq qz241 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) qz61 5)

noncomputable def ep1804 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz241 qz1097) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) 50107979 2883584 1 2883584 945654412271 140737488355328 266829 140737488355328

noncomputable def ep1805 := @Enclosure.Real.IsNear.mulLit_ff qz241 qz1097 50107979 524288 1 524288 2 11 0 1 50107979 2883584

noncomputable abbrev qz243 := (Complex.re qz538)

noncomputable abbrev qz244 := (Complex.im qz538)

noncomputable abbrev qz245 := qz538

noncomputable abbrev qz1099 := (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 qz243 qz243) (@HMul.hMul Real Real Real qz0 qz244 qz244))

noncomputable def ep1806 := @Enclosure.Real.IsNear.of_eq qz241 (Real.sqrt qz1099) Bool.false 50107979 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz245)

noncomputable def ep1807 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz1099) Bool.false 50107979 524288 1 524288 50107979

noncomputable def ep1808 := @Enclosure.Real.IsNear.sqrt_image qz1099 365370889 40000 0 1 25053989 25053990 262144

noncomputable def ep1809 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz243 qz243) (@HMul.hMul Real Real Real qz0 qz244 qz244) 121 4 0 1 364160889 40000 0 1

noncomputable def ep1810 := @Enclosure.Real.IsNear.mulLit_ff qz243 qz243 11 2 0 1 11 2 0 1 121 4

noncomputable def ep1811 := @Enclosure.Complex.IsNear.of_eq qz245 (Complex.mk (Enclosure.sfrac Bool.false 11 2) qz61) Bool.false 11 2 0 1 Bool.false 95415 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 95415 1000 5 (@Eq.refl Real qz61))

noncomputable abbrev qz793 := (ep1811 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 11 2) qz61 Bool.false 11 2 0 1 Bool.false 95415 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 11 2) qz371))

noncomputable def ep1812 := @ep1810 0 1 (@Enclosure.Complex.IsNear.re_isNear qz245 Bool.false 11 2 0 1 Bool.false 95415 1000 0 1 qz793)

noncomputable def ep1813 := ep1812 (@Enclosure.Complex.IsNear.re_isNear qz245 Bool.false 11 2 0 1 Bool.false 95415 1000 0 1 qz793)

noncomputable def ep1814 := @Enclosure.Real.IsNear.mulLit_ff qz244 qz244 95415 1000 0 1 95415 1000 0 1 364160889 40000

noncomputable def ep1815 := @ep1814 0 1 (@Enclosure.Complex.IsNear.im_isNear qz245 Bool.false 11 2 0 1 Bool.false 95415 1000 0 1 qz793)

noncomputable def ep1816 := ep1815 (@Enclosure.Complex.IsNear.im_isNear qz245 Bool.false 11 2 0 1 Bool.false 95415 1000 0 1 qz793)

noncomputable def ep1817 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Real.sqrt (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))))) Bool.false 945654412271 140737488355328

noncomputable def ep1818 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))))) Bool.false 945654412271 140737488355328

noncomputable def ep1819 := nat_lit 22752048293710717350154396163110429925820167666074654627310220864257442972915413

noncomputable def ep1820 := nat_lit 503935770679619350409959312158188592150962858850283833150511513600000000000000000000

noncomputable def ep1821 := nat_lit 713097265217648426243172153700952429112347817762861984315986850479242418631317571187136663

noncomputable def ep1822 := nat_lit 27988168779106820206143575221716266822099993096363126039891795708246853943296000000000000000000000000

noncomputable def ep1823 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)))) ep1819 ep1820 ep1821 ep1822

noncomputable def ep1824 := nat_lit 5460702899489091815102236574562405851457810829487892330806675480242572791791801

noncomputable def ep1825 := nat_lit 125983942669904837602489828039547148037740714712570958287627878400000000000000000000

noncomputable def ep1826 := nat_lit 3058487741082828698026840292155246306176407100631227475488812526967769055634881190213541

noncomputable def ep1827 := nat_lit 124947182049584018777426675096947619741517826323049669820945516554673455104000000000000000000000000

noncomputable def ep1828 := nat_lit 18555850933762246729498976833894010612018864247409904164969774352799016443841

noncomputable def ep1829 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) ep1824 ep1825 ep1826 ep1827 ep1828

noncomputable def ep1830 := nat_lit 10284403483257537763468557390983440656142099160209874145928806400000000000000000000

noncomputable def ep1831 := nat_lit 27996011215094797885159928258177256528832627221467029806492844438462150169104184579303479

noncomputable def ep1832 := nat_lit 58497811180770555035561816997792282243588815671389098055529588703461416767114179510792074049078172085961069753178162691578951185393936813260800000000000000000000

noncomputable def ep1833 := nat_lit 2336814690874972185821174431379863084651

noncomputable def ep1834 := nat_lit 354942168063904232419076897505280000000000

noncomputable def ep1835 := nat_lit 5553704393049253288716186695643229466087

noncomputable def ep1836 := nat_lit 2987440161380212467714892652353683456000000000000

noncomputable def ep1837 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) ep1833 ep1834 ep1835 ep1836 ep1833 ep1834 ep1835

noncomputable def ep1838 := nat_lit 136219862478869970152306161197782658529

noncomputable def ep1839 := nat_lit 101412048018258352119736256430080000000000

noncomputable def ep1840 := nat_lit 62291383503557744947225472948598282636727

noncomputable def ep1841 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242) Bool.false ep1833 ep1834 ep1835 ep1836 Bool.true ep1838 ep1839 ep1840

noncomputable def ep1842 := nat_lit 167296649037291898192033988531806273536000000000000

noncomputable def ep1843 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242 Bool.false ep1833 ep1834 ep1835 ep1836 Bool.true ep1838 ep1839 ep1840 ep1842

noncomputable def ep1844 := nat_lit 17503225084554229826819246932428141

noncomputable def ep1845 := nat_lit 283953734451123385935261518004224000000

noncomputable def ep1846 := nat_lit 3430731764391981473982229891909970207

noncomputable def ep1847 := nat_lit 200755978844750277830440786238167528243200000000

noncomputable def ep1848 := nat_lit 2358693722230664973104698490045398260901

noncomputable def ep1849 := nat_lit 231111377155323649704840947534571906196279

noncomputable def ep1850 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz242)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz242)) ep1844 ep1845 ep1846 ep1847 ep1848 ep1834 ep1849

noncomputable def ep1851 := nat_lit 125472486777968923644025491398854705152000000000000

noncomputable def ep1852 := nat_lit 663547258194195834960843255386434049428089150166326887616005301887565824000000

noncomputable def ep1853 := nat_lit 466787525215658198080451976930263040

noncomputable def ep1854 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz242) 14719419524383369 430080000000 0 1 17836870253843261835 ep1733 233075207803461452903 ep1853 ep1844

noncomputable def ep1855 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) 14719419524383369 430080000000 0 1 0 1 0 1 14719419524383369

noncomputable def ep1856 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 132474775719450321 128000000 0 1 14719419524383369 430080000000 0

noncomputable abbrev qz246 := (@HAdd.hAdd Complex Complex Complex qz261 qz369 qz262)

noncomputable def ep1857 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) qz246) Bool.false 132474775719450321 128000000 0 1 Bool.false 2514676674129239435643 320000000000 0 1

noncomputable def ep1858 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz246)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz246)) 1190699866914572889 3200000000 0 1 132573095379480321 200000000 0 1

noncomputable def ep1859 := nat_lit 662373878597251605000000000

noncomputable def ep1860 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz246) 132299985212730321 1600000000 0 1 9 2 0 1 1190699866914572889 3200000000

noncomputable abbrev qz247 := (@HAdd.hAdd Complex Complex Complex qz261 qz369 qz548)

noncomputable def ep1861 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) qz247) Bool.false 132299985212730321 1600000000 0 1 Bool.true 6947183114787 1000000 0 1

noncomputable def ep1862 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz247)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz247)) 22941086007 160000 0 1 132529396072800321 1600000000 0 1

noncomputable def ep1863 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz247) 3277298001 80000 0 1 7 2 0 1 22941086007 160000

noncomputable abbrev qz794 := (ep979 (BSN.ascPochhammer_succ_eval_c 2 3 qz64 rfl) (ep1007 (@ep1008 277795726191480 6944893154787 8000000 0 1 (ep1011 rfl) (ep1014 rfl) rfl rfl)))

noncomputable def ep1864 := @ep1863 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 qz794)

noncomputable def ep1865 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz61) Bool.false 7 2 0 1 Bool.false 95415 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 95415 1000 3 (@Eq.refl Real qz61))

noncomputable abbrev qz795 := (ep1865 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz61 Bool.false 7 2 0 1 Bool.false 95415 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz371))

noncomputable def ep1866 := ep1864 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 95415 1000 0 1 qz795)

noncomputable def ep1867 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz247) 6944893154787 8000000 0 1 95415 1000 0 1 132529396072800321 1600000000

noncomputable def ep1868 := @ep1867 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 qz794)

noncomputable def ep1869 := ep1868 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 95415 1000 0 1 qz795)

noncomputable def ep1870 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) qz247 Bool.false 132299985212730321 1600000000 0 1 Bool.true 6947183114787 1000000 0 1 (@ep1862 21167997634036851360000 132299985212730321 1600000000 0 1 (ep1866 rfl) (ep1869 rfl) rfl rfl)

noncomputable def ep1871 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz247)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz247)) 62540677753083 16000000 0 1 48614252083509 16000000 0 1

noncomputable def ep1872 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz247) 3277298001 80000 0 1 95415 1000 0 1 62540677753083 16000000

noncomputable def ep1873 := @ep1872 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 qz794)

noncomputable def ep1874 := ep1873 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 95415 1000 0 1 qz795)

noncomputable def ep1875 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz247) 6944893154787 8000000 0 1 7 2 0 1 48614252083509 16000000

noncomputable def ep1876 := @ep1875 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 qz794)

noncomputable def ep1877 := ep1876 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 95415 1000 0 1 qz795)

noncomputable abbrev qz796 := (ep1861 (BSN.ascPochhammer_succ_eval_c 3 4 qz64 rfl) (ep1870 (@ep1871 1778478877385472000000 6947183114787 1000000 0 1 (ep1874 rfl) (ep1877 rfl) rfl rfl)))

noncomputable def ep1878 := @ep1860 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 132299985212730321 1600000000 0 1 Bool.true 6947183114787 1000000 0 1 qz796)

noncomputable def ep1879 := @Enclosure.Complex.IsNear.of_eq qz246 (Complex.mk (Enclosure.sfrac Bool.false 9 2) qz61) Bool.false 9 2 0 1 Bool.false 95415 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 95415 1000 4 (@Eq.refl Real qz61))

noncomputable abbrev qz797 := (ep1879 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9 2) qz61 Bool.false 9 2 0 1 Bool.false 95415 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 9 2) qz371))

noncomputable def ep1880 := ep1878 (@Enclosure.Complex.IsNear.re_isNear qz246 Bool.false 9 2 0 1 Bool.false 95415 1000 0 1 qz797)

noncomputable def ep1881 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz246) 6947183114787 1000000 0 1 95415 1000 0 1 132573095379480321 200000000

noncomputable def ep1882 := @ep1881 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 132299985212730321 1600000000 0 1 Bool.true 6947183114787 1000000 0 1 qz796)

noncomputable def ep1883 := ep1882 (@Enclosure.Complex.IsNear.im_isNear qz246 Bool.false 9 2 0 1 Bool.false 95415 1000 0 1 qz797)

noncomputable def ep1884 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) qz246 Bool.false 132474775719450321 128000000 0 1 Bool.false 2514676674129239435643 320000000000 0 1 (@ep1858 ep1859 132474775719450321 128000000 0 1 (ep1880 rfl) (ep1883 rfl) rfl rfl)

noncomputable def ep1885 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz246)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz246)) 2524680617814532715643 320000000000 0 1 62524648033083 2000000 0 1

noncomputable def ep1886 := nat_lit 5029353348258478871286000000

noncomputable def ep1887 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz246) 132299985212730321 1600000000 0 1 95415 1000 0 1 2524680617814532715643 320000000000

noncomputable def ep1888 := @ep1887 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 132299985212730321 1600000000 0 1 Bool.true 6947183114787 1000000 0 1 qz796)

noncomputable def ep1889 := ep1888 (@Enclosure.Complex.IsNear.im_isNear qz246 Bool.false 9 2 0 1 Bool.false 95415 1000 0 1 qz797)

noncomputable def ep1890 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz246) 6947183114787 1000000 0 1 9 2 0 1 62524648033083 2000000

noncomputable def ep1891 := @ep1890 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 132299985212730321 1600000000 0 1 Bool.true 6947183114787 1000000 0 1 qz796)

noncomputable def ep1892 := ep1891 (@Enclosure.Complex.IsNear.re_isNear qz246 Bool.false 9 2 0 1 Bool.false 95415 1000 0 1 qz797)

noncomputable abbrev qz798 := (ep1857 (BSN.ascPochhammer_succ_eval_c 4 5 qz64 rfl) (ep1884 (@ep1885 ep1886 2514676674129239435643 320000000000 0 1 (ep1889 rfl) (ep1892 rfl) rfl rfl)))

noncomputable def ep1893 := @ep1856 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1686) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 132474775719450321 128000000 0 1 Bool.false 2514676674129239435643 320000000000 0 1 qz798)

noncomputable def ep1894 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 2514676674129239435643 320000000000 0 1 0 1 0

noncomputable def ep1895 := @ep1894 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1686) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 132474775719450321 128000000 0 1 Bool.false 2514676674129239435643 320000000000 0 1 qz798)

noncomputable def ep1896 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) 279408519347693270627 1075200000000000 0 1 0 1 0 1 279408519347693270627

noncomputable def ep1897 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 2514676674129239435643 320000000000 0 1 279408519347693270627 1075200000000000 0

noncomputable def ep1898 := @ep1897 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1686) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 132474775719450321 128000000 0 1 Bool.false 2514676674129239435643 320000000000 0 1 qz798)

noncomputable def ep1899 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 132474775719450321 128000000 0 1 0 1 0

noncomputable def ep1900 := @ep1899 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1686) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 132474775719450321 128000000 0 1 Bool.false 2514676674129239435643 320000000000 0 1 qz798)

noncomputable def ep1901 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 14719419524383369 430080000000 0 1 Bool.false 279408519347693270627 1075200000000000 0 1 (@ep1855 14719419524383369 430080000000 0 1 (ep1893 rfl) (ep1895 rfl) rfl rfl) (@ep1896 279408519347693270627 1075200000000000 0 1 (ep1898 rfl) (ep1900 rfl) rfl rfl)

noncomputable def ep1902 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 14719419524383369 430080000000 0 1 Bool.false 279408519347693270627 1075200000000000 0 1 ep1901

noncomputable def ep1903 := nat_lit 4951760157141521099596496896

noncomputable def ep1904 := nat_lit 116696881303914549520112994232565760

noncomputable def ep1905 := @Enclosure.Complex.IsNear.re_isNear qz242 Bool.true 17836870253843261835 ep1733 233075207803461452903 ep1853 Bool.true 126626081108976273945 ep1903 827145062344111554077 ep1904

noncomputable def ep1906 := @Enclosure.Complex.IsNear.of_eq qz242 (Complex.mk (@HMul.hMul Real Real Real qz0 qz535 (Real.cos qz398)) (@HMul.hMul Real Real Real qz0 qz535 qz956)) Bool.true 17836870253843261835 ep1733 233075207803461452903 ep1853 Bool.true 126626081108976273945 ep1903 827145062344111554077

noncomputable def ep1907 := nat_lit 1738919039128937565089955840

noncomputable def ep1908 := nat_lit 10055145600000000000000000

noncomputable def ep1909 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz362 95415 1000 0 1 3578170511529591 1125899906842624 6706824361 150827184000000000000000 68282227871519185053 225179981368524800 42662109760321 ep1908 qz371 (BSN.isNear_log_sfrac 24 1 3578170511529591 1125899906842624 6706824361 150827184000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz603) Bool.false ep1740 ep1741 1098846103306240 ep1742 3578170511529591 1125899906842624 6706824361 150827184000000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 28532070465432 70368744177664 24973259072661432 36028797018963968 24711525826560 1000000000000000 rfl rfl rfl rfl (ep1745 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1910 := nat_lit 59240397723558570122214237905631398364384594442408167035333771264

noncomputable def ep1911 := nat_lit 842498333348457493583344221469363458551160763204392890034487820288

noncomputable def ep1912 := nat_lit 168715372356585192657954456905841204448267235928416295277841123521

noncomputable def ep1913 := nat_lit 828209561614867654492170703473243054294133076660446386619502906855915520

noncomputable def ep1914 := nat_lit 5797466931304073581445194924312701380058931536623124706336520347991408640

noncomputable def ep1915 := BSN.sin_dyadic_bound_f 20266962489261233 288230376151711744 2 1 140737488355328 49471316352001 ep1912 ep1913 ep1912 ep1912 ep1914 ep1912 9887825144286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 20266962489261233) (BSN.sinEvenQ 288230376151711744) 0 1 ep1912 ep1913 ep1912 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 20266962489261233) (BSN.sinOddQ 288230376151711744) 0 1 ep1912 ep1914 ep1912 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz799 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21338196209849745) (@Nat.cast Real Real.instNatCast 70368744177664))

noncomputable def ep1916 := @Enclosure.Real.IsNear.cos_image qz398 qz799 Bool.false 21338196209849745 70368744177664 299 70368744177664 Bool.true 9887825144286 140737488355328 1 24711525826560 (@Enclosure.Real.IsNear.recentre' qz398 Bool.false 68282227871519185053 225179981368524800 42662109760321 ep1908 21338196209849745 70368744177664 299 70368744177664 (ep1909 rfl) rfl) (Enclosure.sfrac_false_div 21338196209849745 70368744177664) (BSN.cos_reduce1 qz799 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1910) (@Nat.cast Real Real.instNatCast ep1911)) ep1585 ep1563 Bool.false 9887825144286 140737488355328 48 ep1586 49423051653120 24711525826560 (BSN.sin_reduce_arg_pos_rat_q1 21338196209849745 70368744177664 ep1585 ep1563 48 ep1910 ep1911 rfl rfl rfl rfl) EMRow27.d181 (@BSN.sin_arg_round Bool.false 9887825144286 140737488355328 ep1910 ep1911 20266962489261233 288230376151711744 49471316352001 49423051653120 (ep1915 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1917 := nat_lit 1956243612544789033493353892920784052544938293417189914888555953631715997586940976479384535329460731260434898016620348762838653797632680321

noncomputable def ep1918 := nat_lit 1920607018260815532978912358173530051388297685428644360391864145082015815875441738941203950126953068194034147076646652757941625662062128655237120

noncomputable def ep1919 := nat_lit 28464876869421190985109909534764432681789213911802744649850049230739348993838516887677391942190330325535746943204039309411579437441

noncomputable def ep1920 := nat_lit 5868730780704613361637679708542533088105949516673141921060178561195049531282124941761119830633598309400644042978367159880437342569739166081

noncomputable def ep1921 := nat_lit 86427315821736698984051056117808852312473395844288996217633886528690711714394878252354177755712888068731536618449099374107373154792795789485670400

noncomputable def ep1922 := BSN.cos_dyadic_bound_f 20266962489261233 288230376151711744 3 2 140737488355328 49471316352001 ep1917 ep1918 ep1919 ep1920 ep1921 ep1919 140389713093524 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 20266962489261233) (BSN.cosEvenQ 288230376151711744) 0 2 ep1917 ep1918 ep1919 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 20266962489261233) (BSN.cosOddQ 288230376151711744) 0 2 ep1920 ep1921 ep1919 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1923 := @Enclosure.Real.IsNear.sin_image qz398 qz799 Bool.false 21338196209849745 70368744177664 299 70368744177664 Bool.false 140389713093524 140737488355328 1 24711525826560 (@Enclosure.Real.IsNear.recentre' qz398 Bool.false 68282227871519185053 225179981368524800 42662109760321 ep1908 21338196209849745 70368744177664 299 70368744177664 (ep1909 rfl) rfl) (Enclosure.sfrac_false_div 21338196209849745 70368744177664) (BSN.sin_reduce1 qz799 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1910) (@Nat.cast Real Real.instNatCast ep1911)) ep1585 ep1563 Bool.false 140389713093524 140737488355328 48 ep1586 49423051653120 24711525826560 (BSN.sin_reduce_arg_pos_rat_q1 21338196209849745 70368744177664 ep1585 ep1563 48 ep1910 ep1911 rfl rfl rfl rfl) EMRow27.d181 (@BSN.cos_arg_round Bool.false 140389713093524 140737488355328 ep1910 ep1911 20266962489261233 288230376151711744 49471316352001 49423051653120 (ep1922 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1924 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz535 (Real.cos qz398)) (@HMul.hMul Real Real Real qz0 qz535 qz956) Bool.true 17836870253843261835 ep1733 233075207803461452903 ep1853 Bool.true 126626081108976273945 ep1903 827145062344111554077 ep1904 (@Enclosure.Real.IsNear.mulLit_ft qz535 (Real.cos qz398) 3607845 140737488355328 1 140737488355328 4943912572143 70368744177664 14227132733 3316724851854205255680 17836870253843261835 ep1733 233075207803461452903 ep1853 qz790 (@Enclosure.Real.IsNear.recentre' (Real.cos qz398) Bool.true 9887825144286 140737488355328 7459114966319104 ep1907 4943912572143 70368744177664 14227132733 3316724851854205255680 (ep1916 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz535 qz956 3607845 140737488355328 1 140737488355328 35097428273381 35184372088832 14227132733 3316724851854205255680 126626081108976273945 ep1903 827145062344111554077 ep1904 qz790 (@Enclosure.Real.IsNear.neg qz399 Bool.false 35097428273381 35184372088832 14227132733 3316724851854205255680 (@Enclosure.Real.IsNear.recentre' qz399 Bool.false 140389713093524 140737488355328 7459114966319104 ep1907 35097428273381 35184372088832 14227132733 3316724851854205255680 (ep1923 rfl rfl) rfl)) rfl)

noncomputable def ep1925 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz242) 279408519347693270627 1075200000000000 0 1 126626081108976273945 ep1903 827145062344111554077 ep1904 ep1848

noncomputable def ep1926 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 14719419524383369 430080000000 0 1 Bool.false 279408519347693270627 1075200000000000 0 1 ep1901

noncomputable def ep1927 := @Enclosure.Complex.IsNear.im_isNear qz242 Bool.true 17836870253843261835 ep1733 233075207803461452903 ep1853 Bool.true 126626081108976273945 ep1903 827145062344111554077 ep1904

noncomputable def ep1928 := nat_lit 124257494038107830163164841823068047

noncomputable def ep1929 := nat_lit 141976867225561692967630759002112000000

noncomputable def ep1930 := nat_lit 12175095180165214590920775301722945413

noncomputable def ep1931 := nat_lit 50188994711187569457610196559541882060800000000

noncomputable def ep1932 := nat_lit 332251567161550640250318919269138374703

noncomputable def ep1933 := nat_lit 709884336127808464838153795010560000000000

noncomputable def ep1934 := nat_lit 65123198709021088932468665828565393780181

noncomputable def ep1935 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz242)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz242)) ep1928 ep1929 ep1930 ep1931 ep1932 ep1933 ep1934

noncomputable def ep1936 := nat_lit 501889947111875694576101965595418820608000000000000

noncomputable def ep1937 := nat_lit 135380485300527564014117866601558641599095070403455472689326673400692736000000

noncomputable def ep1938 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz242) 14719419524383369 430080000000 0 1 126626081108976273945 ep1903 827145062344111554077 ep1904 ep1928

noncomputable def ep1939 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz242) 279408519347693270627 1075200000000000 0 1 17836870253843261835 ep1733 233075207803461452903 ep1853 ep1932

noncomputable abbrev qz800 := (@ep1906 ep1904 (BSN.cpow_neg_s_sub_mk qz61 95415 1000 24 5 1521681143169024 (@Eq.refl Real qz61) rfl EMRow27.d178) ep1924)

noncomputable def ep1940 := ep1843 (@ep1850 ep1851 ep1852 ep1833 ep1834 ep1835 ep1836 (@ep1854 ep1845 ep1846 ep1847 ep1902 (ep1905 qz800) rfl) (@ep1925 ep1834 ep1849 ep1851 ep1926 (ep1927 qz800) rfl) rfl rfl) (@ep1935 ep1936 ep1937 ep1838 ep1839 ep1840 ep1842 (@ep1938 ep1929 ep1930 ep1931 ep1902 (ep1927 qz800) rfl) (@ep1939 ep1933 ep1934 ep1936 ep1926 (ep1905 qz800) rfl) rfl rfl)

noncomputable def ep1941 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) ep1838 ep1839 ep1840 ep1842 ep1838 ep1839 ep1840

noncomputable def ep1942 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242) Bool.false ep1833 ep1834 ep1835 ep1836 Bool.true ep1838 ep1839 ep1840

noncomputable def ep1943 := @ep1804 47384831431332610309 405828369621610135552 14315916607691 405828369621610135552 (@ep1805 1 2883584 (ep1806 (@ep1807 524288 1 524288 (ep1808 (@ep1809 1461483556 365370889 40000 0 1 (ep1813 rfl) (ep1816 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 11) rfl) (@ep1817 266829 140737488355328 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (@ep1818 266829 140737488355328 945654412271 140737488355328 266829 140737488355328 (@ep1823 472827072721 472827339550 70368744177664 (@ep1829 ep1830 ep1831 ep1822 ep1832 ep1819 ep1820 ep1821 ep1822 (@ep1837 ep1836 ep1824 ep1825 ep1826 ep1827 (@ep1841 ep1842 ep1940) (@ep1841 ep1842 ep1940) rfl) (@ep1941 ep1842 ep1828 ep1830 ep1831 ep1822 (@ep1942 ep1842 ep1940) (@ep1942 ep1842 ep1940) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow27.d183 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 24))) (@HMul.hMul Real Real Real qz0 qz792 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)))) Bool.false ep1780 ep1588 15399073984139130251 ep1588 := ep1802 (ep1803 ep1943) rfl rfl

noncomputable def EMRow27.d184 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz248 := (@Enclosure.dec_le_dec qz257 qz366 93095 1000 95415 1000 (@Eq.refl Real qz257) (@Eq.refl Real qz366) rfl rfl rfl)

noncomputable abbrev qz801 := (EMRow27.d3 qz9 qz61 qz248 24 24 2 2)

noncomputable def ep1944 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz801 (@Enclosure.dec_nonneg qz9 93095 1000 (@Eq.refl Real qz9)) (@Enclosure.pos_of_ble 2 rfl) (@Enclosure.pos_of_ble 24 rfl)

noncomputable abbrev qz802 := (Zeta.Certificates.ZIntervalEM.fstVal (EMRow27.d3 qz9 qz61 qz248 24 24 2 2))

noncomputable def ep1945 := @Enclosure.Real.IsNear.neg_val qz802 ep314 ep315

noncomputable def ep1946 := @Enclosure.Real.IsNear.of_eq qz802 (hardyZApproximantEM 2 24 qz9) Bool.true

noncomputable abbrev qz803 := (Zeta.Certificates.ZIntervalEM.sndVal (EMRow27.d3 qz9 qz61 qz248 24 24 2 2))

noncomputable def ep1947 := BSN.mul_neg_of_neg_pos_r qz802 qz803 (@ep1945 ep316 ep317 (@ep1946 ep314 ep315 ep316 ep317 (@Eq.refl Real (hardyZApproximantEM 2 24 qz9)) EMRow27.d14) rfl rfl rfl)

noncomputable def ep1948 := @Enclosure.Real.IsNear.pos_val qz803 ep1015 ep1016

noncomputable def ep1949 := @Enclosure.Real.IsNear.of_eq qz803 (hardyZApproximantEM 2 24 qz61) Bool.false

noncomputable def ep1950 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz802) (BSN.hardyZErrorBoundStrong 2 24 qz9)

noncomputable def ep1951 := @Enclosure.norm_gt_of_isNear qz802 (BSN.hardyZErrorBoundStrong 2 24 qz9) Bool.true

noncomputable def ep1952 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 2 24 qz9) (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 24))) (@HMul.hMul Real Real Real qz0 qz782 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)))) Bool.false 310682931313904203762017 ep1587 19817277758615508993 ep1588 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 24))) (@HMul.hMul Real Real Real qz0 qz782 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)))))

noncomputable def ep1953 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz803) (BSN.hardyZErrorBoundStrong 2 24 qz61)

noncomputable def ep1954 := @Enclosure.norm_gt_of_isNear qz803 (BSN.hardyZErrorBoundStrong 2 24 qz61) Bool.false

noncomputable def ep1955 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 2 24 qz61) (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 24))) (@HMul.hMul Real Real Real qz0 qz792 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)))) Bool.false ep1780 ep1588 15399073984139130251 ep1588 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz337 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 24))) (@HMul.hMul Real Real Real qz0 qz792 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)))))

noncomputable def ep1956 := @List.cons EMRow27.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz801 (ep1944 (@Enclosure.pos_of_ble 2 rfl) (@Enclosure.pos_of_ble 24 rfl) (ep1947 (@ep1948 ep1017 ep1018 (@ep1949 ep1015 ep1016 ep1017 ep1018 (@Eq.refl Real (hardyZApproximantEM 2 24 qz61)) EMRow27.d19) rfl rfl rfl)) (ep1950 (hardyZErrorBoundEM 2 24 qz9) (BSN.hardyZErrorBoundEM_le_strong 2 24 qz9 rfl) (@ep1951 Bool.false ep314 ep315 ep316 ep317 310682931313904203762017 ep1587 19817277758615508993 ep1588 (@ep1946 ep314 ep315 ep316 ep317 (@Eq.refl Real (hardyZApproximantEM 2 24 qz9)) EMRow27.d14) (ep1952 EMRow27.d182) rfl rfl rfl rfl rfl)) (ep1953 (hardyZErrorBoundEM 2 24 qz61) (BSN.hardyZErrorBoundEM_le_strong 2 24 qz61 rfl) (@ep1954 Bool.false ep1015 ep1016 ep1017 ep1018 ep1780 ep1588 15399073984139130251 ep1588 (@ep1949 ep1015 ep1016 ep1017 ep1018 (@Eq.refl Real (hardyZApproximantEM 2 24 qz61)) EMRow27.d19) (ep1955 EMRow27.d183) rfl rfl rfl rfl rfl)))) (@List.nil EMRow27.d0)

noncomputable abbrev qz804 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz805 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1956 (@List.IsChain.singleton EMRow27.d1 EMRow27.d184 (EMRow27.d2 qz9 qz61 qz248))))

noncomputable def ep1957 := And (@Eq (Option Real) (@Option.map qz804 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz804 qz805)) (@Option.some Real qz9))

noncomputable def ep1958 := ep1957 (@Eq (Option Real) (@Option.map qz804 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz804 qz805)) (@Option.some Real qz61))

noncomputable def ep1959 := @And.intro (@Eq Nat (@List.length qz804 qz805) 1) ep1958

noncomputable def ep1960 := @And.intro (@Eq (Option Real) (@Option.map qz804 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz804 qz805)) (@Option.some Real qz9))

noncomputable def ep1961 := @ep1960 (@Eq (Option Real) (@Option.map qz804 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz804 qz805)) (@Option.some Real qz61))

noncomputable abbrev qz806 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1956 (@List.IsChain.singleton EMRow27.d1 EMRow27.d184 (EMRow27.d2 qz9 qz61 qz248)))

theorem EMRow27.d185 : Zeta.Certificates.BatchSpec 1 93095 1000 95415 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz804 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz804 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz804 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz9)) (@Eq (Option Real) (@Option.map qz804 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz804 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz61)))) qz806 (ep1959 (@Eq.refl Nat 1) (ep1961 (@Eq.refl (Option Real) (@Option.some Real qz9)) (@Eq.refl (Option Real) (@Option.some Real qz61))))

theorem solution : Zeta.Certificates.BatchSpec 1 93095 1000 95415 1000 := EMRow27.d185
#print axioms solution
#check solution
