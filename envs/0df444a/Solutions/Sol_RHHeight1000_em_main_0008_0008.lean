-- Prove2me | solution 1 for RHHeight1000.em_main_0008_0008
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:51:44.831301+00:00
-- url     : https://prove2.me/submissions/236a1872-ba41-44da-83d3-32a0e21dfd95

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow08.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow08.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow08.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow08.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow08.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz254 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz254

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz255 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz255 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138516661214455 2251799813685248 250000000030969 15484500000000000000 4138516661214455 2251799813685248 250000000030969 15484500000000000000 120446 65536

noncomputable abbrev qz256 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 65536 qz256 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 779317518150410741488063439345657628452599855445271348474342368876423347582876053728679783827237610085654588674605917415063316248867402488514697634436426745

noncomputable def ep10 := nat_lit 13198325246229587668616048586507268161410801335203869857947191811663857046415771104290097871102374067703089877156867761119753226876438075596795543285583799

noncomputable def ep11 := nat_lit 13338205139369261376383149914767634013226508915861991492218067381232119098362059104733250767410551174650894954010182016771344050520336484956804919489535

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 4 3 ep9 131072 61938 ep10 ep11 59189 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 3 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz257 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz257

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138516661214455 2251799813685248 250000000030969 15484500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000123876 61938000000000000000 4138516661214455 2251799813685248 250000000030969 15484500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 59189 131072 24973259072661432 36028797018963968 61938 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 779317518150412560342812906055656980396982394702499187106382620393032652998517540933158707129341055012778793601285942846917973645097155238594697634436426745

noncomputable def ep18 := nat_lit 13198325246229655554962711811363413523213721429909419700721697472804734044169853548961061453892255410264786862895235075217650796661500958924795543285583799

noncomputable def ep19 := nat_lit 13338205139369401582665284895604560799810298653799657073142644093199656832454717421805370366589019475922075211274104314270069372987910244956804919489535

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 4 3 ep17 131072 61938 ep18 ep19 59189 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 3 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138516661214455 2251799813685248 250000000030969 15484500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000123876 61938000000000000000 4138516661214455 2251799813685248 250000000030969 15484500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 59189 131072 24973259072661432 36028797018963968 61938 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz258 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz3 := (Real.log qz258)

theorem EMRow08.d4 : Enclosure.Real.IsNear qz3 Bool.false 60223 32768 1 32768 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz255) Bool.false 60223 32768 1 32768 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz255) Bool.false 120446 65536 2 65536 60223 32768 1 32768 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 150042 131072 1 61938 150042 131072 1 61938 75021 65536 2 65536 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 5456220599384213465248909714772227496572670538165976141063262914812807742611017753801422503639530882087556452122005170047444298375835020188444492540969863625638808382453421118235702266947370928498132967594635949979551089348001357731941995137847266570621617494261809398531128871567535833923098076891483476912075228072418610430965163137427706923427310178652894498746239459018086669257415154730407592571637957767157504839263249849478535520334507104454135585522664276476675

noncomputable def ep28 := nat_lit 583201912334273870627228188254822588827079241605343036411752047433839590517388190714780374919746279700129906501257101384229175562492847525225536391462542197025353003914524118772974087630067522636400444148635637549655768907025719966434833632093412247469427754039812435067522613541620617101084764807513402584784781490076808276521160080078978009740617112077674385114356333461540984478969922738031393369686631450339262287925718320742111081121726382582016608811398564907105

noncomputable def ep29 := nat_lit 2006268627360805445673839316848610509641534779303135707206598861506426804997221642604762844037348942607248852390277353874343091902420975230792155995982437872051629609224882022549487822374001366578458875613104959699164386313425243185530298109514065278868815165519648262204211929774735225023360668387821809970420335957473972782118680523137645713941929429588852958886338507735711181009301082096313539911189247153419366938656533848809858580689548163599238034961919825

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 10 9 ep27 131072 61938 ep28 ep29 150042 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 9 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 5456220599384260892400251500854699790811159195150212163211869656216336849990273498858157048596616978904240776489460003685239051624059887013466241201881443704542959173524008982544253046253151867013374679201187657749749224297051088632484873343955402287279851789208893474071824987110190207053471018354491495133306616646837230249901879422821128116650397962087630806812522581253210958036113071268120219429850657911869289056672761916619783759890108169949892385522664276476675

noncomputable def ep34 := nat_lit 583201912334279575053067226115417021307550325332234501953544426829928714668898700518418107620762577859683234776628347658361181262145210140271013263714562720079188253110303208819702903278206870150494721073991877864419341163488949363940583288588224434829960190109694548513088121652843287215458036179968684293644459891198769761601084092249455692877745995219003758983943549453190712470220270279351626860119698313725888367584660500821040083453648022042061408811398564907105

noncomputable def ep35 := nat_lit 2006268627360839170887858856494478835319319717359667041823756329478526322484078784125879825811686186445537802910004300367040714583746383402724632880452479311196631191501299191497899488881639138562974769996989848045902383299749709271247360054208480548633525642122514778503225872819822968825602771791453574137145372948950799520945900351638147820910599315255916738483881817718250085827996954508077874524152655659774549924038927632065100609588052048399238034961919825

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 10 9 ep33 131072 61938 ep34 ep35 150042 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 9 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 75021 65536 2 65536 75021 65536 1 32768 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 150042 131072 1 61938 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 150042 131072 61938 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 150042 131072 1 61938 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 150042 131072 61938 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow08.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 32768 := ep37

noncomputable abbrev qz442 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 42364 1000)))

noncomputable abbrev qz419 := qz442

noncomputable abbrev qz259 := qz419

noncomputable abbrev qz4 := (BSN.headSumC qz259 9)

noncomputable abbrev qz443 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz420 := qz443

noncomputable abbrev qz260 := qz420

noncomputable abbrev qz5 := qz260

noncomputable abbrev qz6 := (BSN.headSumC qz259 8)

noncomputable abbrev qz421 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz261 := qz421

noncomputable abbrev qz422 := (@Neg.neg Complex Complex.instNeg qz442)

noncomputable abbrev qz262 := qz422

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 8) qz262)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz4 (@HAdd.hAdd Complex Complex Complex qz5 qz6 qz7) Bool.false 2477989359 2147483648 1274405083999 266021684379648 Bool.true 4195027995 17179869184 2546116886975 532043368759296

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP qz6 qz7 Bool.false 13800279987 17179869184 253375639141 59115929862144 Bool.true 853626633 4294967296 63366426829 14778982465536 Bool.false

noncomputable abbrev qz8 := (BSN.headSumC qz259 7)

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 7) qz262)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq qz6 (@HAdd.hAdd Complex Complex Complex qz5 qz8 qz9) Bool.false 13800279987 17179869184 253375639141 59115929862144 Bool.true 853626633 4294967296 63366426829 14778982465536

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP qz8 qz9 Bool.false 4534532473 8589934592 332204571823 88673894793216 Bool.false 1032937661 17179869184 664738478315 177347789586432 Bool.false

noncomputable abbrev qz10 := (BSN.headSumC qz259 6)

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 6) qz262)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq qz8 (@HAdd.hAdd Complex Complex Complex qz5 qz10 qz11) Bool.false 4534532473 8589934592 332204571823 88673894793216 Bool.false 1032937661 17179869184 664738478315 177347789586432

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP qz10 qz11 Bool.false 367430117 2147483648 420205020799 133010842189824 Bool.false 4441578171 17179869184 1684957634503 532043368759296 Bool.false

noncomputable abbrev qz12 := (BSN.headSumC qz259 5)

noncomputable abbrev qz13 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 5) qz262)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq qz10 (@HAdd.hAdd Complex Complex Complex qz5 qz12 qz13) Bool.false 367430117 2147483648 420205020799 133010842189824 Bool.false 4441578171 17179869184 1684957634503 532043368759296

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP qz12 qz13 Bool.true 817925191 8589934592 671979149407 266021684379648 Bool.true 1730557461 17179869184 1347252192623 532043368759296 Bool.false

noncomputable abbrev qz14 := (BSN.headSumC qz259 4)

noncomputable abbrev qz15 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 4) qz262)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq qz12 (@HAdd.hAdd Complex Complex Complex qz5 qz14 qz15) Bool.true 817925191 8589934592 671979149407 266021684379648 Bool.true 1730557461 17179869184 1347252192623 532043368759296

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP qz14 qz15 Bool.false 3280650853 17179869184 322573283251 177347789586432 Bool.false 5313013269 17179869184 323336194243 177347789586432 Bool.true

noncomputable abbrev qz16 := (BSN.headSumC qz259 3)

noncomputable abbrev qz423 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz263 := qz423

noncomputable abbrev qz17 := (@HPow.hPow Complex Complex Complex qz261 qz263 qz262)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq qz14 (@HAdd.hAdd Complex Complex Complex qz5 qz16 qz17) Bool.false 3280650853 17179869184 322573283251 177347789586432 Bool.false 5313013269 17179869184 323336194243 177347789586432

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP qz16 qz17 Bool.false 90332801 134217728 33285109927 33252710547456 Bool.false 5385611997 8589934592 268003034537 266021684379648 Bool.true

noncomputable abbrev qz18 := (BSN.headSumC qz259 2)

noncomputable abbrev qz424 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz264 := qz424

noncomputable abbrev qz19 := (@HPow.hPow Complex Complex Complex qz261 qz264 qz262)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq qz16 (@HAdd.hAdd Complex Complex Complex qz5 qz18 qz19) Bool.false 90332801 134217728 33285109927 33252710547456 Bool.false 5385611997 8589934592 268003034537 266021684379648

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP qz18 qz19 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz265 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz20 := qz265

noncomputable abbrev qz21 := qz259

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq qz18 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz20) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz21)

noncomputable abbrev qz266 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz22 := (@Inv.inv Real Real.instInv (Real.sqrt qz266))

noncomputable abbrev qz444 := (Enclosure.sfrac Bool.false 42364 1000)

noncomputable abbrev qz425 := qz444

noncomputable abbrev qz267 := qz425

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz24 := qz267

noncomputable abbrev qz268 := (@Eq.refl Real qz425)

noncomputable abbrev qz25 := qz268

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz19 (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.true 43884927 134217728 33285109927 33252710547456 Bool.false 5385611997 8589934592 268003034537 266021684379648 (BSN.cpow_neg_s_mk qz24 42364 1000 2 qz25 rfl)

noncomputable abbrev qz26 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz266) 185363 131072 1 131072 46340 46342 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz266) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz266 qz26)) Bool.false 185363 131072 1 131072 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz266 qz26)) Bool.false 185363 131072 1 131072 185363 131072 1 131072 (BSN.sqrt_enclosure 2 1 92681 92682 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 65536 30969 24381081 945 45426 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 64009648012689812602488500043232866481433181890992843176289422854585121

noncomputable def ep57 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120

noncomputable def ep58 := nat_lit 53755577844178251781043289469037330837128222620949898533706052926241

noncomputable def ep59 := nat_lit 191921432882381081303903413550760524782625289227736629731800856457902881

noncomputable def ep60 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400

noncomputable abbrev qz269 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz270 := (BSN.cosOddQ 268435456)

noncomputable def ep61 := BSN.cos_dyadic_bound_f 292619283 268435456 3 2 131072 61999 ep56 ep57 ep58 ep59 ep60 ep58 60608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 292619283) qz269 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 292619283) qz270 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz27 := (@Nat.cast Real Real.instNatCast 65536)

noncomputable abbrev qz28 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz271 := (Enclosure.Real.IsNear.const Bool.false 42364 1000)

noncomputable abbrev qz29 := qz271

noncomputable abbrev qz30 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable abbrev qz272 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1924427) qz27)

noncomputable abbrev qz273 := (BSN.isNear_log_sfrac 2 1 45426 65536 1 30969 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 45426 65536 30969 rfl rfl rfl (ep55 rfl)))

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz23 qz272 Bool.false 1924427 65536 45 32768 Bool.true 60608 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 240553383 8192000 10591 7742250 1924427 65536 45 32768 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz28 42364 1000 0 1 45426 65536 1 30969 240553383 8192000 10591 7742250 qz29 qz273 rfl) rfl) (Enclosure.sfrac_false_div 1924427 65536) (BSN.cos_reduce2 qz272 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10295625740700042133504) qz30) 226375608064910080 72057594037927936 Bool.false 60608 131072 4 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q2 1924427 65536 226375608064910080 72057594037927936 4 10295625740700042133504 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 60608 131072 10295625740700042133504 9444732965739290427392 292619283 268435456 61999 61938 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 115174361960566320083054465446243929801910024825690357798493996295912225

noncomputable def ep64 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080

noncomputable def ep65 := nat_lit 301560105627830740190830482271498517612218524087802732493667799546460961

noncomputable def ep66 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800

noncomputable abbrev qz274 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz275 := (BSN.sinOddQ 268435456)

noncomputable def ep67 := BSN.sin_dyadic_bound_f 292619283 268435456 3 2 131072 61999 ep63 ep64 ep58 ep65 ep66 ep58 116217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 292619283) qz274 0 2 ep63 ep64 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 292619283) qz275 0 2 ep65 ep66 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz23 qz272 Bool.false 1924427 65536 45 32768 Bool.true 116217 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 240553383 8192000 10591 7742250 1924427 65536 45 32768 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz28 42364 1000 0 1 45426 65536 1 30969 240553383 8192000 10591 7742250 qz29 qz273 rfl) rfl) (Enclosure.sfrac_false_div 1924427 65536) (BSN.sin_reduce2 qz272 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10295625740700042133504) qz30) 226375608064910080 72057594037927936 Bool.false 116217 131072 4 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q2 1924427 65536 226375608064910080 72057594037927936 4 10295625740700042133504 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 116217 131072 10295625740700042133504 9444732965739290427392 292619283 268435456 61999 61938 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz276 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 92682 131072 2 131072 46341 65536 1 65536 (ep54 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.true 43884927 134217728 33285109927 33252710547456 Bool.false 5385611997 8589934592 268003034537 266021684379648 (@Enclosure.Real.IsNear.mulLit_ft qz22 (Real.cos qz23) 46341 65536 1 65536 947 2048 1426373 1014792192 43884927 134217728 33285109927 33252710547456 qz276 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.true 60608 131072 1426373 1014792192 947 2048 1426373 1014792192 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 46341 65536 1 65536 116217 131072 1426373 1014792192 5385611997 8589934592 268003034537 266021684379648 qz276 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.true 116217 131072 1426373 1014792192 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.true 116217 131072 1426373 1014792192 116217 131072 1426373 1014792192 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz277 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz31 := qz277

noncomputable def ep70 := @ep51 43884927 134217728 33285109927 33252710547456 Bool.false 5385611997 8589934592 268003034537 266021684379648 Bool.false 90332801 90332801 134217728 33285109927 33252710547456 Bool.false 5385611997 5385611997 8589934592 268003034537 266021684379648 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz20 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz31)) (ep53 ep69) rfl rfl

noncomputable abbrev qz32 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz33 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq qz17 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)))) Bool.true 8281947675 17179869184 435158090921 532043368759296 Bool.true 5458210725 17179869184 434002513655 532043368759296 (BSN.cpow_neg_s_mk qz24 42364 1000 3 qz25 rfl)

noncomputable abbrev qz34 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz34) 227023 131072 1 131072 37837 37838 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz34) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz34 qz26)) Bool.false 227023 131072 1 131072 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz34 qz26)) Bool.false 227023 131072 1 131072 227023 131072 1 131072 (BSN.sqrt_enclosure 3 1 113511 113512 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 9 8 2258332876800 65536 30969 222698787165 2027025 71998 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1) (BSN.artanhQ 2) 0 8 222698787165 2258332876800 2027025 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := nat_lit 4949319829332501983886956340039936

noncomputable def ep75 := nat_lit 623075623024179315423659559506411520

noncomputable def ep76 := nat_lit 4361529361169255207965616916544880640

noncomputable def ep77 := BSN.sin_dyadic_bound_f 265238388 268435456 2 1 131072 61999 ep74 ep75 ep74 ep74 ep76 ep74 109441 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 265238388) qz274 0 1 ep74 ep75 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 265238388) qz275 0 1 ep74 ep76 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz35 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz278 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3050123) qz27)

noncomputable abbrev qz279 := (BSN.isNear_log_sfrac 3 1 71998 65536 1 30969 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 71998 65536 30969 rfl rfl rfl (ep73 rfl)))

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz33 qz278 Bool.false 3050123 65536 45 32768 Bool.true 109441 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 381265409 8192000 10591 7742250 3050123 65536 45 32768 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz35 42364 1000 0 1 71998 65536 1 30969 381265409 8192000 10591 7742250 qz29 qz279 rfl) rfl) (Enclosure.sfrac_false_div 3050123 65536) (BSN.cos_reduce1 qz278 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9332246145377276788736) qz30) 226375608064910080 72057594037927936 Bool.false 109441 131072 7 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q1 3050123 65536 226375608064910080 72057594037927936 7 9332246145377276788736 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 109441 131072 9332246145377276788736 9444732965739290427392 265238388 268435456 61999 61938 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 43197703273674853089196644120014649999387977348436236765317577981362176

noncomputable def ep80 := nat_lit 24495766773023906565177660585722605566963981587523214576790074884096

noncomputable def ep81 := nat_lit 129544118287478511454459577038872504787030004082133663866799153794318336

noncomputable def ep82 := BSN.cos_dyadic_bound_f 265238388 268435456 3 2 131072 61999 ep79 ep57 ep80 ep81 ep60 ep80 72127 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 265238388) qz269 0 2 ep79 ep57 ep80 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 265238388) qz270 0 2 ep81 ep60 ep80 rfl rfl rfl rfl) rfl rfl

noncomputable def ep83 := @Enclosure.Real.IsNear.sin_image qz33 qz278 Bool.false 3050123 65536 45 32768 Bool.false 72127 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 381265409 8192000 10591 7742250 3050123 65536 45 32768 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz35 42364 1000 0 1 71998 65536 1 30969 381265409 8192000 10591 7742250 qz29 qz279 rfl) rfl) (Enclosure.sfrac_false_div 3050123 65536) (BSN.sin_reduce1 qz278 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9332246145377276788736) qz30) 226375608064910080 72057594037927936 Bool.false 72127 131072 7 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q1 3050123 65536 226375608064910080 72057594037927936 7 9332246145377276788736 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 72127 131072 9332246145377276788736 9444732965739290427392 265238388 268435456 61999 61938 (ep82 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz280 := (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 75675 131072 1 131072 75675 131072 1 131072 (ep72 rfl rfl) rfl)

noncomputable def ep84 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33))) Bool.true 8281947675 17179869184 435158090921 532043368759296 Bool.true 5458210725 17179869184 434002513655 532043368759296 (@Enclosure.Real.IsNear.mulLit_ft qz32 (Real.cos qz33) 75675 131072 1 131072 109441 131072 1426373 1014792192 8281947675 17179869184 435158090921 532043368759296 qz280 (@Enclosure.Real.IsNear.recentre' (Real.cos qz33) Bool.true 109441 131072 1426373 1014792192 109441 131072 1426373 1014792192 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)) 75675 131072 1 131072 72127 131072 1426373 1014792192 5458210725 17179869184 434002513655 532043368759296 qz280 (@Enclosure.Real.IsNear.neg (Real.sin qz33) Bool.false 72127 131072 1426373 1014792192 (@Enclosure.Real.IsNear.recentre' (Real.sin qz33) Bool.false 72127 131072 1426373 1014792192 72127 131072 1426373 1014792192 (ep83 rfl rfl) rfl)) rfl)

noncomputable def ep85 := @ep49 8281947675 17179869184 435158090921 532043368759296 Bool.true 5458210725 17179869184 434002513655 532043368759296 Bool.false 440321503850921984 3280650853 17179869184 322573283251 177347789586432 Bool.false 45638436467138101248 5313013269 17179869184 323336194243 177347789586432 (ep50 (BSN.head_sum_c_succ qz21 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep84) rfl rfl

noncomputable abbrev qz281 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz281))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep86 := @Enclosure.Complex.IsNear.of_eq qz15 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.true 4916501235 17179869184 376238449061 532043368759296 Bool.true 3521785365 8589934592 188621804947 266021684379648 (BSN.cpow_neg_s_mk qz24 42364 1000 4 qz25 rfl)

noncomputable def ep87 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz281) 262145 131072 1 131072 32767 32768 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz281) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz281 qz26)) Bool.false 262145 131072 1 131072 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz281 qz26)) Bool.false 262145 131072 1 131072 262145 131072 1 131072 (BSN.sqrt_enclosure 4 1 131072 131073 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep88 := nat_lit 753960950911045074462890625

noncomputable def ep89 := nat_lit 117048680082474133384580175

noncomputable def ep90 := BSN.log_dyadic_bound 3 5 12 11 ep88 65536 30969 ep89 431467934736729065175 90852 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 3) (BSN.artanhQ 5) 0 11 ep89 ep88 431467934736729065175 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep91 := nat_lit 716032773192977332986297050001936

noncomputable def ep92 := BSN.sin_dyadic_bound_f 163581138 268435456 2 1 131072 61999 ep91 ep75 ep91 ep91 ep76 ep91 75021 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 163581138) qz274 0 1 ep91 ep75 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 163581138) qz275 0 1 ep91 ep76 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz38 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz282 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1924427) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz283 := (BSN.isNear_log_sfrac 4 1 90852 65536 1 30969 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 90852 65536 30969 rfl rfl rfl (ep90 rfl)))

noncomputable abbrev qz284 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep93 := @Enclosure.Real.IsNear.cos_image qz37 qz282 Bool.false 1924427 32768 45 32768 Bool.true 75021 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 240553383 4096000 10591 7742250 1924427 32768 45 32768 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz38 42364 1000 0 1 90852 65536 1 30969 240553383 4096000 10591 7742250 qz29 qz283 rfl) rfl) (Enclosure.sfrac_false_div 1924427 32768) (BSN.cos_reduce1 qz282 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2877749815629068632064) qz284) 226375608064910080 72057594037927936 Bool.false 75021 131072 9 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q1 1924427 32768 226375608064910080 72057594037927936 9 2877749815629068632064 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 75021 131072 2877749815629068632064 4722366482869645213696 163581138 268435456 61999 61938 (ep92 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep94 := nat_lit 124615124604835863084731911901282304

noncomputable def ep95 := nat_lit 1869226869072537946270978678519234560

noncomputable def ep96 := BSN.cos_dyadic_bound_f 163581138 268435456 2 1 131072 61999 ep91 ep94 ep91 ep91 ep95 ep91 107478 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 163581138) qz269 0 1 ep91 ep94 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 163581138) qz270 0 1 ep91 ep95 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable def ep97 := @Enclosure.Real.IsNear.sin_image qz37 qz282 Bool.false 1924427 32768 45 32768 Bool.false 107478 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 240553383 4096000 10591 7742250 1924427 32768 45 32768 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz38 42364 1000 0 1 90852 65536 1 30969 240553383 4096000 10591 7742250 qz29 qz283 rfl) rfl) (Enclosure.sfrac_false_div 1924427 32768) (BSN.sin_reduce1 qz282 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2877749815629068632064) qz284) 226375608064910080 72057594037927936 Bool.false 107478 131072 9 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q1 1924427 32768 226375608064910080 72057594037927936 9 2877749815629068632064 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 107478 131072 2877749815629068632064 4722366482869645213696 163581138 268435456 61999 61938 (ep96 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz285 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 65535 131072 1 131072 65535 131072 1 131072 (ep87 rfl rfl) rfl)

noncomputable def ep98 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.true 4916501235 17179869184 376238449061 532043368759296 Bool.true 3521785365 8589934592 188621804947 266021684379648 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz37) 65535 131072 1 131072 75021 131072 1426373 1014792192 4916501235 17179869184 376238449061 532043368759296 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.true 75021 131072 1426373 1014792192 75021 131072 1426373 1014792192 (ep93 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 65535 131072 1 131072 53739 65536 1426373 1014792192 3521785365 8589934592 188621804947 266021684379648 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.false 53739 65536 1426373 1014792192 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.false 107478 131072 1426373 1014792192 53739 65536 1426373 1014792192 (ep97 rfl rfl) rfl)) rfl)

noncomputable def ep99 := @ep47 4916501235 17179869184 376238449061 532043368759296 Bool.true 3521785365 8589934592 188621804947 266021684379648 Bool.true 28103695567356428288 817925191 8589934592 671979149407 266021684379648 Bool.true 14865375397687590912 1730557461 17179869184 1347252192623 532043368759296 (ep48 (BSN.head_sum_c_succ qz21 3 4 rfl rfl) (ep85 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep86 ep98) rfl rfl

noncomputable abbrev qz286 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz39 := (@Inv.inv Real Real.instInv (Real.sqrt qz286))

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep100 := @Enclosure.Complex.IsNear.of_eq qz13 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)))) Bool.false 2287645659 8589934592 168430892191 266021684379648 Bool.false 385758477 1073741824 42213180235 66505421094912 (BSN.cpow_neg_s_mk qz24 42364 1000 5 qz25 rfl)

noncomputable def ep101 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz286) 293085 131072 1 131072 29308 29309 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz286) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz286 qz26)) Bool.false 293085 131072 1 131072 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz286 qz26)) Bool.false 293085 131072 1 131072 293085 131072 1 131072 (BSN.sqrt_enclosure 5 1 146542 146543 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep102 := nat_lit 141613827518379161815574079375

noncomputable def ep103 := nat_lit 29325128709309236875766211300

noncomputable def ep104 := BSN.log_dyadic_bound 2 3 15 14 ep102 65536 30969 ep103 57299708096576225280000 105476 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP 2) (BSN.artanhQ 3) 0 14 ep103 ep102 57299708096576225280000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep105 := nat_lit 859756902656174527321332867076096

noncomputable def ep106 := BSN.sin_dyadic_bound_f 171235544 268435456 2 1 131072 61999 ep105 ep75 ep105 ep105 ep76 ep105 78054 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 171235544) qz274 0 1 ep105 ep75 ep105 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 171235544) qz275 0 1 ep105 ep76 ep105 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz41 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz287 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4468385) qz27)

noncomputable abbrev qz288 := (BSN.isNear_log_sfrac 5 1 105476 65536 1 30969 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 105476 65536 30969 rfl rfl rfl (ep104 rfl)))

noncomputable def ep107 := @Enclosure.Real.IsNear.cos_image qz40 qz287 Bool.false 4468385 65536 45 32768 Bool.false 78054 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 279274079 4096000 10591 7742250 4468385 65536 45 32768 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz41 42364 1000 0 1 105476 65536 1 30969 279274079 4096000 10591 7742250 qz29 qz288 rfl) rfl) (Enclosure.sfrac_false_div 4468385 65536) (BSN.cos_reduce3 qz287 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6024815114229519482880) qz30) 226375608064910080 72057594037927936 Bool.false 78054 131072 10 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q3 4468385 65536 226375608064910080 72057594037927936 10 6024815114229519482880 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 78054 131072 6024815114229519482880 9444732965739290427392 171235544 268435456 61999 61938 (ep106 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep108 := BSN.cos_dyadic_bound_f 171235544 268435456 2 1 131072 61999 ep105 ep94 ep105 ep105 ep95 ep105 105296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 171235544) qz269 0 1 ep105 ep94 ep105 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 171235544) qz270 0 1 ep105 ep95 ep105 rfl rfl rfl rfl) rfl rfl

noncomputable def ep109 := @Enclosure.Real.IsNear.sin_image qz40 qz287 Bool.false 4468385 65536 45 32768 Bool.true 105296 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 279274079 4096000 10591 7742250 4468385 65536 45 32768 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz41 42364 1000 0 1 105476 65536 1 30969 279274079 4096000 10591 7742250 qz29 qz288 rfl) rfl) (Enclosure.sfrac_false_div 4468385 65536) (BSN.sin_reduce3 qz287 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6024815114229519482880) qz30) 226375608064910080 72057594037927936 Bool.false 105296 131072 10 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q3 4468385 65536 226375608064910080 72057594037927936 10 6024815114229519482880 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 105296 131072 6024815114229519482880 9444732965739290427392 171235544 268435456 61999 61938 (ep108 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz289 := (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 58617 131072 1 131072 58617 131072 1 131072 (ep101 rfl rfl) rfl)

noncomputable def ep110 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40))) Bool.false 2287645659 8589934592 168430892191 266021684379648 Bool.false 385758477 1073741824 42213180235 66505421094912 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz40) 58617 131072 1 131072 39027 65536 1426373 1014792192 2287645659 8589934592 168430892191 266021684379648 qz289 (@Enclosure.Real.IsNear.recentre' (Real.cos qz40) Bool.false 78054 131072 1426373 1014792192 39027 65536 1426373 1014792192 (ep107 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)) 58617 131072 1 131072 6581 8192 1426373 1014792192 385758477 1073741824 42213180235 66505421094912 qz289 (@Enclosure.Real.IsNear.neg (Real.sin qz40) Bool.true 6581 8192 1426373 1014792192 (@Enclosure.Real.IsNear.recentre' (Real.sin qz40) Bool.true 105296 131072 1426373 1014792192 6581 8192 1426373 1014792192 (ep109 rfl rfl) rfl)) rfl)

noncomputable def ep111 := @ep45 2287645659 8589934592 168430892191 266021684379648 Bool.false 385758477 1073741824 42213180235 66505421094912 Bool.false 12624802688643629056 367430117 2147483648 420205020799 133010842189824 Bool.false 4769108246768123904 4441578171 17179869184 1684957634503 532043368759296 (ep46 (BSN.head_sum_c_succ qz21 4 5 rfl rfl) (ep99 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep100 ep110) rfl rfl

noncomputable abbrev qz290 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt qz290))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep112 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.false 3064812005 8589934592 156203673871 266021684379648 Bool.true 1704320255 8589934592 154628900221 266021684379648 (BSN.cpow_neg_s_mk qz24 42364 1000 6 qz25 rfl)

noncomputable abbrev qz291 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz26)

noncomputable def ep113 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz290) 321059 131072 1 131072 26754 26756 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz290) (Real.sqrt qz291) Bool.false 321059 131072 1 131072 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz291) Bool.false 321059 131072 1 131072 321059 131072 1 131072 (BSN.sqrt_enclosure 6 1 160529 160530 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep114 := BSN.log_dyadic_bound 2 10 4 3 105000000 65536 30969 1434560 960 26572 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz44 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep115 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz44 42364 1000 0 1 4034664351997175 2251799813685248 500000000030969 15484500000000000000 1709245206080083217 22517998136852480 5295500000327992679 3871125000000000000000 qz29 (BSN.isNear_log_sfrac 6 1 4034664351997175 2251799813685248 500000000030969 15484500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz291) Bool.false 4230652207559789772800 2361183241434822606848 1000000000061938 30969000000000000000 4034664351997175 2251799813685248 500000000030969 15484500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 26572 65536 24973259072661432 36028797018963968 30969 1000000000000000 rfl rfl rfl rfl (ep114 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep116 := nat_lit 344452563902166226366943118506641

noncomputable def ep117 := BSN.cos_dyadic_bound_f 136233011 268435456 2 1 131072 61999 ep116 ep94 ep116 ep116 ep95 ep116 114551 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 136233011) qz269 0 1 ep116 ep94 ep116 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 136233011) qz270 0 1 ep116 ep95 ep116 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz292 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2487279) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep118 := @Enclosure.Real.IsNear.cos_image qz43 qz292 Bool.false 2487279 32768 45 32768 Bool.false 114551 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 1709245206080083217 22517998136852480 5295500000327992679 3871125000000000000000 2487279 32768 45 32768 (ep115 rfl) rfl) (Enclosure.sfrac_false_div 2487279 32768) (BSN.cos_reduce0 qz292 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2396636478719989383168) qz284) 226375608064910080 72057594037927936 Bool.false 114551 131072 12 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 2487279 32768 226375608064910080 72057594037927936 12 2396636478719989383168 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 114551 131072 2396636478719989383168 4722366482869645213696 136233011 268435456 61999 61938 (ep117 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep119 := BSN.sin_dyadic_bound_f 136233011 268435456 2 1 131072 61999 ep116 ep75 ep116 ep116 ep76 ep116 63701 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 136233011) qz274 0 1 ep116 ep75 ep116 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 136233011) qz275 0 1 ep116 ep76 ep116 rfl rfl rfl rfl) rfl rfl

noncomputable def ep120 := @Enclosure.Real.IsNear.sin_image qz43 qz292 Bool.false 2487279 32768 45 32768 Bool.false 63701 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 1709245206080083217 22517998136852480 5295500000327992679 3871125000000000000000 2487279 32768 45 32768 (ep115 rfl) rfl) (Enclosure.sfrac_false_div 2487279 32768) (BSN.sin_reduce0 qz292 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2396636478719989383168) qz284) 226375608064910080 72057594037927936 Bool.false 63701 131072 12 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 2487279 32768 226375608064910080 72057594037927936 12 2396636478719989383168 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 63701 131072 2396636478719989383168 4722366482869645213696 136233011 268435456 61999 61938 (ep119 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz293 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 53510 131072 2 131072 26755 65536 1 65536 (ep113 rfl rfl) rfl)

noncomputable def ep121 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.false 3064812005 8589934592 156203673871 266021684379648 Bool.true 1704320255 8589934592 154628900221 266021684379648 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz43) 26755 65536 1 65536 114551 131072 1426373 1014792192 3064812005 8589934592 156203673871 266021684379648 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.false 114551 131072 1426373 1014792192 114551 131072 1426373 1014792192 (ep118 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 26755 65536 1 65536 63701 131072 1426373 1014792192 1704320255 8589934592 154628900221 266021684379648 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.false 63701 131072 1426373 1014792192 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.false 63701 131072 1426373 1014792192 63701 131072 1426373 1014792192 (ep120 rfl rfl) rfl)) rfl)

noncomputable def ep122 := @ep43 3064812005 8589934592 156203673871 266021684379648 Bool.true 1704320255 8589934592 154628900221 266021684379648 Bool.false 9737834337092501504 4534532473 8589934592 332204571823 88673894793216 Bool.false 8872866945603469312 1032937661 17179869184 664738478315 177347789586432 (ep44 (BSN.head_sum_c_succ qz21 5 6 rfl rfl) (ep111 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep112 ep121) rfl rfl

noncomputable abbrev qz294 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv (Real.sqrt qz294))

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep123 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)))) Bool.false 4731215041 17179869184 95717773777 177347789586432 Bool.true 4447444193 17179869184 95658643633 177347789586432 (BSN.cpow_neg_s_mk qz24 42364 1000 7 qz25 rfl)

noncomputable abbrev qz295 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) qz26)

noncomputable def ep124 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz294) 346783 131072 1 131072 24770 24771 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz294) (Real.sqrt qz295) Bool.false 346783 131072 1 131072 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz295) Bool.false 346783 131072 1 131072 346783 131072 1 131072 (BSN.sqrt_enclosure 7 1 173391 173392 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep125 := BSN.log_dyadic_bound 3 11 5 4 202569142545 65536 30969 5259111624 688905 36674 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz47 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep126 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz47 42364 1000 0 1 4381766428990711 2251799813685248 500000000030969 15484500000000000000 46407288249440620201 562949953421312000 5295500000327992679 3871125000000000000000 qz29 (BSN.isNear_log_sfrac 7 1 4381766428990711 2251799813685248 500000000030969 15484500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz295) Bool.false 4594615115045363777536 2361183241434822606848 1000000000061938 30969000000000000000 4381766428990711 2251799813685248 500000000030969 15484500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 36674 65536 24973259072661432 36028797018963968 30969 1000000000000000 rfl rfl rfl rfl (ep125 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep127 := nat_lit 1682560852138520071806477594967056

noncomputable def ep128 := BSN.cos_dyadic_bound_f 202531554 268435456 2 1 131072 61999 ep127 ep94 ep127 ep127 ep95 ep127 95501 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 202531554) qz269 0 1 ep127 ep94 ep127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 202531554) qz270 0 1 ep127 ep95 ep127 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz296 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5402519) qz27)

noncomputable def ep129 := @Enclosure.Real.IsNear.cos_image qz46 qz296 Bool.false 5402519 65536 181 131072 Bool.false 95501 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 46407288249440620201 562949953421312000 5295500000327992679 3871125000000000000000 5402519 65536 181 131072 (ep126 rfl) rfl) (Enclosure.sfrac_false_div 5402519 65536) (BSN.cos_reduce0 qz296 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7125945561003545591808) qz30) 226375608064910080 72057594037927936 Bool.false 95501 131072 13 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 5402519 65536 226375608064910080 72057594037927936 13 7125945561003545591808 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 95501 131072 7125945561003545591808 9444732965739290427392 202531554 268435456 61999 61938 (ep128 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep130 := BSN.sin_dyadic_bound_f 202531554 268435456 2 1 131072 61999 ep127 ep75 ep127 ep127 ep76 ep127 89773 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 202531554) qz274 0 1 ep127 ep75 ep127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 202531554) qz275 0 1 ep127 ep76 ep127 rfl rfl rfl rfl) rfl rfl

noncomputable def ep131 := @Enclosure.Real.IsNear.sin_image qz46 qz296 Bool.false 5402519 65536 181 131072 Bool.false 89773 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 46407288249440620201 562949953421312000 5295500000327992679 3871125000000000000000 5402519 65536 181 131072 (ep126 rfl) rfl) (Enclosure.sfrac_false_div 5402519 65536) (BSN.sin_reduce0 qz296 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7125945561003545591808) qz30) 226375608064910080 72057594037927936 Bool.false 89773 131072 13 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 5402519 65536 226375608064910080 72057594037927936 13 7125945561003545591808 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 89773 131072 7125945561003545591808 9444732965739290427392 202531554 268435456 61999 61938 (ep130 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz297 := (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 49541 131072 1 131072 49541 131072 1 131072 (ep124 rfl rfl) rfl)

noncomputable def ep132 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46))) Bool.false 4731215041 17179869184 95717773777 177347789586432 Bool.true 4447444193 17179869184 95658643633 177347789586432 (@Enclosure.Real.IsNear.mulLit_ff qz45 (Real.cos qz46) 49541 131072 1 131072 95501 131072 5736461 4059168768 4731215041 17179869184 95717773777 177347789586432 qz297 (@Enclosure.Real.IsNear.recentre' (Real.cos qz46) Bool.false 95501 131072 5736461 4059168768 95501 131072 5736461 4059168768 (ep129 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)) 49541 131072 1 131072 89773 131072 5736461 4059168768 4447444193 17179869184 95658643633 177347789586432 qz297 (@Enclosure.Real.IsNear.neg (Real.sin qz46) Bool.false 89773 131072 5736461 4059168768 (@Enclosure.Real.IsNear.recentre' (Real.sin qz46) Bool.false 89773 131072 5736461 4059168768 89773 131072 5736461 4059168768 (ep131 rfl rfl) rfl)) rfl)

noncomputable def ep133 := @ep41 4731215041 17179869184 95717773777 177347789586432 Bool.true 4447444193 17179869184 95658643633 177347789586432 Bool.false 118543502439616610304 13800279987 17179869184 253375639141 59115929862144 Bool.true 58660775547673509888 853626633 4294967296 63366426829 14778982465536 (ep42 (BSN.head_sum_c_succ qz21 6 7 rfl rfl) (ep122 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep123 ep132) rfl rfl

noncomputable abbrev qz298 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz48 := (@Inv.inv Real Real.instInv (Real.sqrt qz298))

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep134 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)))) Bool.false 6023634885 17179869184 268429415729 532043368759296 Bool.true 780521463 17179869184 264925521131 532043368759296 (BSN.cpow_neg_s_mk qz24 42364 1000 8 qz25 rfl)

noncomputable abbrev qz299 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz26)

noncomputable def ep135 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz298) 370727 131072 1 131072 23170 23171 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz298) (Real.sqrt qz299) Bool.false 370727 131072 1 131072 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz299) Bool.false 370727 131072 1 131072 370727 131072 1 131072 (BSN.sqrt_enclosure 8 1 185363 185364 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep136 := BSN.log_dyadic_bound 0 16 1 0 1 65536 30969 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz50 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep137 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz50 42364 1000 0 1 9364972152248037 4503599627370496 1000000000092907 30969000000000000000 99184420064458959867 1125899906842624000 10591000000983978037 7742250000000000000000 qz29 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000092907 30969000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz299) Bool.false 4909942519757818822656 2361183241434822606848 1000000000092907 30969000000000000000 9364972152248037 4503599627370496 1000000000092907 30969000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 65536 24973259072661432 36028797018963968 30969 1000000000000000 rfl rfl rfl rfl (ep136 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep138 := nat_lit 1431891037783801182306186050625

noncomputable def ep139 := BSN.cos_dyadic_bound_f 34592145 268435456 2 1 131072 61999 ep138 ep94 ep138 ep138 ep95 ep138 129985 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 34592145) qz269 0 1 ep138 ep94 ep138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 34592145) qz270 0 1 ep138 ep95 ep138 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz300 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5773293) qz27)

noncomputable def ep140 := @Enclosure.Real.IsNear.cos_image qz49 qz300 Bool.false 5773293 65536 45 32768 Bool.false 129985 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 99184420064458959867 1125899906842624000 10591000000983978037 7742250000000000000000 5773293 65536 45 32768 (ep137 rfl) rfl) (Enclosure.sfrac_false_div 5773293 65536) (BSN.cos_reduce0 qz300 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1217102904073142665216) qz30) 226375608064910080 72057594037927936 Bool.false 129985 131072 14 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 5773293 65536 226375608064910080 72057594037927936 14 1217102904073142665216 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 129985 131072 1217102904073142665216 9444732965739290427392 34592145 268435456 61999 61938 (ep139 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep141 := BSN.sin_dyadic_bound_f 34592145 268435456 1 0 131072 61999 0 1 1 0 1 1 16843 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 34592145) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 34592145) qz275 0 0 rfl) rfl rfl

noncomputable def ep142 := @Enclosure.Real.IsNear.sin_image qz49 qz300 Bool.false 5773293 65536 45 32768 Bool.false 16843 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 99184420064458959867 1125899906842624000 10591000000983978037 7742250000000000000000 5773293 65536 45 32768 (ep137 rfl) rfl) (Enclosure.sfrac_false_div 5773293 65536) (BSN.sin_reduce0 qz300 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1217102904073142665216) qz30) 226375608064910080 72057594037927936 Bool.false 16843 131072 14 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 5773293 65536 226375608064910080 72057594037927936 14 1217102904073142665216 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16843 131072 1217102904073142665216 9444732965739290427392 34592145 268435456 61999 61938 (ep141 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz301 := (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 46341 131072 1 131072 46341 131072 1 131072 (ep135 rfl rfl) rfl)

noncomputable def ep143 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49))) Bool.false 6023634885 17179869184 268429415729 532043368759296 Bool.true 780521463 17179869184 264925521131 532043368759296 (@Enclosure.Real.IsNear.mulLit_ff qz48 (Real.cos qz49) 46341 131072 1 131072 129985 131072 1426373 1014792192 6023634885 17179869184 268429415729 532043368759296 qz301 (@Enclosure.Real.IsNear.recentre' (Real.cos qz49) Bool.false 129985 131072 1426373 1014792192 129985 131072 1426373 1014792192 (ep140 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)) 46341 131072 1 131072 16843 131072 1426373 1014792192 780521463 17179869184 264925521131 532043368759296 qz301 (@Enclosure.Real.IsNear.neg (Real.sin qz49) Bool.false 16843 131072 1426373 1014792192 (@Enclosure.Real.IsNear.recentre' (Real.sin qz49) Bool.false 16843 131072 1426373 1014792192 16843 131072 1426373 1014792192 (ep142 rfl rfl) rfl)) rfl)

noncomputable def ep144 := @ep39 6023634885 17179869184 268429415729 532043368759296 Bool.true 780521463 17179869184 264925521131 532043368759296 Bool.false 340572264215712104448 2477989359 2147483648 1274405083999 266021684379648 Bool.true 18017508044329451520 4195027995 17179869184 2546116886975 532043368759296 (ep40 (BSN.head_sum_c_succ qz21 7 8 rfl rfl) (ep133 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep134 ep143) rfl rfl

theorem EMRow08.d6 : Enclosure.Complex.IsNear qz4 Bool.false 2477989359 2147483648 1274405083999 266021684379648 Bool.true 4195027995 17179869184 2546116886975 532043368759296 := ep38 (BSN.head_sum_c_succ qz21 8 9 rfl rfl) (ep144 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow08.d7 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow08.d8 : @Eq Nat (Nat.pow 9 1) 9 := @Eq.refl Nat 9

noncomputable def ep145 := nat_lit 33108349066634544534330973

noncomputable def ep146 := nat_lit 28419519423273419302502400

noncomputable def ep147 := nat_lit 1136425146235616985666822598509349

noncomputable def ep148 := nat_lit 181710421070615934690408976613376000

noncomputable abbrev qz445 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz426 := qz445

noncomputable abbrev qz302 := qz426

noncomputable abbrev qz51 := qz302

noncomputable abbrev qz52 := (@instHSub Real Real.instSub)

noncomputable abbrev qz427 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz303 := qz427

noncomputable abbrev qz53 := qz303

noncomputable abbrev qz446 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz447 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz428 := (@HAdd.hAdd Complex Complex Complex qz443 (@HAdd.hAdd Complex Complex Complex qz443 qz446 (@HMul.hMul Complex Complex Complex qz445 Complex.I (@HDiv.hDiv Complex Complex Complex qz447 (↑qz444) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz304 := qz428

noncomputable abbrev qz54 := (Complex.Stirling.logGammaStirling 1 qz304)

noncomputable abbrev qz429 := (@HAdd.hAdd Complex Complex Complex qz443 qz446 (@HMul.hMul Complex Complex Complex qz445 Complex.I (@HDiv.hDiv Complex Complex Complex qz447 (↑qz444) (2 : Complex))))

noncomputable abbrev qz305 := qz429

noncomputable abbrev qz55 := qz305

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz254 (@HDiv.hDiv Real Real Real qz257 qz267 (2 : Real)) (Real.log Real.pi))

noncomputable def ep149 := Complex.re (@HMul.hMul Complex Complex Complex qz51 (Complex.exp (@HMul.hMul Complex Complex Complex qz51 Complex.I ↑(@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56))) (zetaApproximant qz21 1 9))

noncomputable def ep150 := @Enclosure.Real.IsNear.of_eq ep149 (@HSub.hSub Real Real Real qz52 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) (Complex.re (zetaApproximant qz21 1 9))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) (Complex.im (zetaApproximant qz21 1 9))))

noncomputable def ep151 := nat_lit 198645753086845046889313183

noncomputable def ep152 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) (Complex.re (zetaApproximant qz21 1 9))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) (Complex.im (zetaApproximant qz21 1 9))) ep151

noncomputable def ep153 := nat_lit 170517116539640515815014400

noncomputable def ep154 := nat_lit 224818958483568943768397648693731

noncomputable def ep155 := nat_lit 36342084214123186938081795322675200

noncomputable def ep156 := nat_lit 34103423307928103163002880

noncomputable def ep157 := nat_lit 6165176908886133412417177520347

noncomputable def ep158 := nat_lit 90855210535307967345204488306688000

noncomputable def ep159 := nat_lit 6774648259476505113683876021117259339710558833213440

noncomputable def ep160 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) (Complex.re (zetaApproximant qz21 1 9)) 131071 131072 930869

noncomputable def ep161 := nat_lit 44765426484138718789632000

noncomputable def ep162 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) Bool.false 131071 131072 930869

noncomputable abbrev qz57 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz306 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2470699) qz57)

noncomputable def ep163 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56) qz306 Bool.false 2470699 131072 29

noncomputable def ep164 := nat_lit 126849024000000000000000000

noncomputable def ep165 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56) Bool.false 31834723939600066673 1688849860263936000 111371874275054109541097 ep164

noncomputable def ep166 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56 14557077136799542909 337769972052787200 29373704525054109541097 ep164 794547411 32768000

noncomputable def ep167 := nat_lit 208632046810562996948172800

noncomputable def ep168 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 3728650674983200849 112589990684262400 49156652915325050795059 ep164 Bool.false 14557077136799542909 337769972052787200

noncomputable def ep169 := @Enclosure.Complex.IsNear.subLitP qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 3040938795276322649 112589990684262400 47108652914310258603059 ep164 Bool.false 15594321614523079309 337769972052787200 25277704524927260517097

noncomputable def ep170 := nat_lit 2099043723806136466912632413093888

noncomputable def ep171 := nat_lit 4097452948055874266851161149538304

noncomputable abbrev qz448 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz430 := qz448

noncomputable abbrev qz307 := (@HSub.hSub Complex Complex Complex qz427 qz428 qz430)

noncomputable abbrev qz308 := (Complex.log qz428)

noncomputable abbrev qz58 := (@HSub.hSub Complex Complex Complex qz303 (@HMul.hMul Complex Complex Complex qz302 qz307 qz308) qz304)

noncomputable abbrev qz309 := qz430

noncomputable abbrev qz59 := (@HMul.hMul Complex Complex Complex qz302 qz309 ↑(Real.log qz258))

noncomputable abbrev qz431 := qz447

noncomputable abbrev qz310 := qz431

noncomputable abbrev qz60 := qz310

noncomputable abbrev qz61 := (@instHMul Nat instMulNat)

noncomputable abbrev qz432 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz311 := qz432

noncomputable abbrev qz62 := qz311

noncomputable abbrev qz63 := qz304

noncomputable abbrev qz312 := (@instHSub Int Int.instSub)

noncomputable abbrev qz64 := qz312

noncomputable abbrev qz313 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz65 := qz313

noncomputable abbrev qz314 := (@instHMul Int Int.instMul)

noncomputable abbrev qz66 := qz314

noncomputable abbrev qz315 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz67 := qz315

noncomputable def ep172 := @Enclosure.Complex.IsNear.of_eq qz54 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz58 qz59) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz63 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k)))))) Bool.true 3040938795276322649

noncomputable def ep173 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz58 qz59) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz63 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) Bool.true 3040985320908015449 112589990684262400

noncomputable def ep174 := nat_lit 3265183168712361265149771776

noncomputable def ep175 := nat_lit 10465172084012897542088949760000

noncomputable def ep176 := @ep173 11501049439021338179 30969000000000000000000 Bool.false 25992726037384058603 562949953421312000 6170500002651039307 30969000000000000000000 Bool.false 443703 1073741824 3 1073741824 Bool.true 1566419491 402653184000 10591 402653184000 Bool.true ep174 3040938795276322649 112589990684262400 47108652914310258603059 ep164 Bool.false ep175

noncomputable def ep177 := @Enclosure.Complex.IsNear.addLitP qz58 qz59 Bool.true 3144447647094818649 112589990684262400 11028500000544775679 30969000000000000000000

noncomputable def ep178 := @ep177 Bool.false 25992726037384058603 562949953421312000 6170500002651039307 30969000000000000000000 Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 Bool.true 199294013991027700465664 3040985320908015449 112589990684262400 11501049439021338179 30969000000000000000000 Bool.false 25992726037384058603 25992726037384058603 562949953421312000

noncomputable abbrev qz68 := (@HMul.hMul Complex Complex Complex qz302 qz307 qz308)

noncomputable def ep179 := @Enclosure.Complex.IsNear.subLitP qz68 qz63 Bool.true 2891120168055228249 112589990684262400 11028500000544775679 30969000000000000000000 Bool.false 37917131950754289387

noncomputable def ep180 := @ep179 562949953421312000 6170500002651039307 30969000000000000000000 Bool.false 9000 4000 0 1 Bool.false 84728 4000 0 1 Bool.true 12577790588379274596000 3144447647094818649 112589990684262400 11028500000544775679 30969000000000000000000 Bool.false 103970904149536234412000 25992726037384058603 562949953421312000 6170500002651039307 30969000000000000000000

noncomputable abbrev qz69 := qz307

noncomputable abbrev qz70 := qz308

noncomputable def ep181 := @Enclosure.Complex.IsNear.mul qz69 qz70 Bool.true 2891120168055228249 112589990684262400 11028500000544775679 30969000000000000000000 Bool.false 37917131950754289387 562949953421312000 6170500002651039307

noncomputable abbrev qz71 := (Complex.re qz307)

noncomputable abbrev qz72 := (Complex.re qz308)

noncomputable abbrev qz73 := (Complex.im qz307)

noncomputable abbrev qz74 := (Complex.im qz308)

noncomputable def ep182 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz71 qz72) (@HMul.hMul Real Real Real qz0 qz73 qz74) 24107000684858049 4503599627370496 437500000216783 30969000000000000000 1746897592588339737 56294995342131200

noncomputable def ep183 := nat_lit 6510223855768425857690026484170752

noncomputable def ep184 := @Enclosure.Real.IsNear.mulLit_ff qz71 qz72 7000 4000 0 1 3443857240694007 1125899906842624 62500000030969 7742250000000000000

noncomputable def ep185 := @Enclosure.Complex.IsNear.re_isNear qz69 Bool.false 7000 4000 0 1 Bool.false 84728 4000 0 1

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 84728 4000)

noncomputable abbrev qz75 := qz316

noncomputable def ep186 := @Enclosure.Complex.IsNear.of_eq qz69 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz75) Bool.false 7000 4000 0 1 Bool.false 84728 4000 0

noncomputable abbrev qz317 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz76 := (Complex.mk qz317 qz316)

noncomputable def ep187 := @Enclosure.Complex.IsNear.of_eq qz70 (Complex.log qz76) Bool.false 3443857240694007 1125899906842624 62500000030969 7742250000000000000 Bool.false 824708522608035 562949953421312 1000000000030969 61938000000000000000

noncomputable def ep188 := nat_lit 261326881887144183905238995727357943659094244072940270346332304910771839178605854720

noncomputable def ep189 := nat_lit 7095070473772550117181594399526083230623007732717838192220462290013951087790260224

noncomputable def ep190 := nat_lit 1054141211707796139799495513550978666147807612062904945621291440146554636206080

noncomputable def ep191 := BSN.log_dyadic_bound 3163833984 11355833984 5 4 ep188 131072 61938 ep189 ep190 75018 14519667968 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3163833984) (BSN.artanhQ 11355833984) 0 4 ep189 ep188 ep190 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz77 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz318 := (Real.log (Enclosure.sfrac Bool.false 7259833984 16000000))

noncomputable abbrev qz319 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz320 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep192 := @Enclosure.Real.IsNear.mulLit_ff qz77 qz318 1 2 0 1 3443857240694007 562949953421312 62500000030969 3871125000000000000 3443857240694007 1125899906842624 62500000030969 7742250000000000000 qz319 (BSN.isNear_log_sfrac 7259833984 16000000 3443857240694007 562949953421312 62500000030969 3871125000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7259833984) qz320)) Bool.false 28889168400143672672256 4722366482869645213696 1000000000495504 61938000000000000000 3443857240694007 562949953421312 62500000030969 3871125000000000000 (BSN.log_rat_reduce_isNear 7259833984 16000000 8 14519667968 8192000000 75018 131072 24973259072661432 36028797018963968 61938 1000000000000000 rfl rfl rfl rfl (ep191 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep193 := BSN.arctan_dyadic_bound_f 9000 84728 1 0 131072 61938 0 1 1 0 1 1 13870 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 84728) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 84728) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz78 := (@HMul.hMul Real Real Real qz254 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz79 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz319 BSN.pi_near_15 rfl)

noncomputable abbrev qz321 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 84728)))

noncomputable def ep194 := @Enclosure.Real.IsNear.subLit_ff_p qz78 qz321 884279719003555 562949953421312 1 2000000000000000 13870 131072 1 61938 108096195475280363520 824708522608035 562949953421312 1000000000030969 61938000000000000000 qz79 (ep193 rfl) rfl rfl

noncomputable abbrev qz322 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 84728) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep195 := @Enclosure.Complex.IsNear.re_isNear qz70 Bool.false 3443857240694007 1125899906842624 62500000030969 7742250000000000000 Bool.false 824708522608035 562949953421312 1000000000030969 61938000000000000000 (ep187 (@congrArg Complex Complex qz63 qz76 Complex.log (BSN.w_shift_mk qz24 Bool.false 42364 1000 2 qz25 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz76) Bool.false 3443857240694007 1125899906842624 62500000030969 7742250000000000000 Bool.false 824708522608035 562949953421312 1000000000030969 61938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz76)) (@HMul.hMul Real Real Real qz0 qz77 qz318) Bool.false 3443857240694007 1125899906842624 62500000030969 7742250000000000000 (Enclosure.clog_re_eq 9000 84728 4000 7259833984 16000000 rfl rfl rfl) (ep192 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz76)) qz322 Bool.false 824708522608035 562949953421312 1000000000030969 61938000000000000000 (Enclosure.clog_im_eq 9000 84728 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz322 (@HSub.hSub Real Real Real qz52 qz78 qz321) Bool.false 824708522608035 562949953421312 1000000000030969 61938000000000000000 (BSN.arctan_recip 84728 9000 rfl rfl) ep194))))

noncomputable def ep196 := @Enclosure.Real.IsNear.mulLit_ff qz73 qz74 84728 4000 0 1 824708522608035 562949953421312 1000000000030969 61938000000000000000

noncomputable def ep197 := @Enclosure.Complex.IsNear.im_isNear qz69 Bool.false 7000 4000 0 1 Bool.false 84728 4000 0 1

noncomputable def ep198 := @Enclosure.Complex.IsNear.im_isNear qz70 Bool.false 3443857240694007 1125899906842624 62500000030969 7742250000000000000 Bool.false 824708522608035 562949953421312 1000000000030969 61938000000000000000 (ep187 (@congrArg Complex Complex qz63 qz76 Complex.log (BSN.w_shift_mk qz24 Bool.false 42364 1000 2 qz25 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz76) Bool.false 3443857240694007 1125899906842624 62500000030969 7742250000000000000 Bool.false 824708522608035 562949953421312 1000000000030969 61938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz76)) (@HMul.hMul Real Real Real qz0 qz77 qz318) Bool.false 3443857240694007 1125899906842624 62500000030969 7742250000000000000 (Enclosure.clog_re_eq 9000 84728 4000 7259833984 16000000 rfl rfl rfl) (ep192 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz76)) qz322 Bool.false 824708522608035 562949953421312 1000000000030969 61938000000000000000 (Enclosure.clog_im_eq 9000 84728 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz322 (@HSub.hSub Real Real Real qz52 qz78 qz321) Bool.false 824708522608035 562949953421312 1000000000030969 61938000000000000000 (BSN.arctan_recip 84728 9000 rfl rfl) ep194))))

noncomputable abbrev qz323 := (Enclosure.Real.IsNear.const Bool.false 84728 4000)

noncomputable abbrev qz80 := (@ep186 1 (BSN.w_sub_half_mk qz267 Bool.false 42364 1000 2 qz268 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz316 Bool.false 7000 4000 0 1 Bool.false 84728 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz323))

noncomputable def ep199 := @ep182 10591000000327992679 30969000000000000000000 ep183 2891120168055228249 112589990684262400 11028500000544775679 30969000000000000000000 (@ep184 24107000684858049 4503599627370496 437500000216783 30969000000000000000 (ep185 qz80) ep195 rfl) (@ep196 1746897592588339737 56294995342131200 10591000000327992679 30969000000000000000000 (ep197 qz80) ep198 rfl) rfl

noncomputable def ep200 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz71 qz74) (@HMul.hMul Real Real Real qz0 qz73 qz72) 5772959658256245 2251799813685248 7000000000216783 247752000000000000000 36473892036190228137 562949953421312000

noncomputable def ep201 := nat_lit 85381790662187472885584959924862976

noncomputable def ep202 := @Enclosure.Real.IsNear.mulLit_ff qz71 qz74 7000 4000 0 1 824708522608035 562949953421312 1000000000030969 61938000000000000000

noncomputable def ep203 := @Enclosure.Real.IsNear.mulLit_ff qz73 qz72 84728 4000 0 1 3443857240694007 1125899906842624 62500000030969 7742250000000000000

noncomputable def ep204 := @ep200 661937500327992679 3871125000000000000000 ep201 37917131950754289387 562949953421312000 6170500002651039307 30969000000000000000000 (@ep202 5772959658256245 2251799813685248 7000000000216783 247752000000000000000 (ep185 qz80) ep198 rfl) (@ep203 36473892036190228137 562949953421312000 661937500327992679 3871125000000000000000 (ep197 qz80) ep195 rfl) rfl

noncomputable def ep205 := @Enclosure.Complex.IsNear.of_eq qz63 qz76 Bool.false 9000 4000 0 1 Bool.false 84728 4000 0 1 (BSN.w_shift_mk qz24 Bool.false 42364 1000 2 qz25 rfl)

noncomputable abbrev qz324 := (ep205 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 84728 4000) Bool.false 9000 4000 0 1 Bool.false 84728 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 84728 4000)))

noncomputable abbrev qz81 := qz324

noncomputable def ep206 := ep180 (@ep181 30969000000000000000000 (ep199 rfl) (ep204 rfl)) qz81 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz82 := qz309

noncomputable def ep207 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz82) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz82) (Complex.im ↑qz3)) 60223 65536 1 65536 0 1 0 1 60223 60223

noncomputable def ep208 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz82) (Complex.re ↑qz3) 1 2 0 1 60223 32768 1 32768 60223 65536 1 65536

noncomputable abbrev qz83 := (@Enclosure.Complex.IsNear.of_eq qz309 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz265) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz265 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz319 qz277))

noncomputable def ep209 := ep208 (@Enclosure.Complex.IsNear.re_isNear qz82 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz83) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 60223 32768 1 32768 (Complex.ofReal_re qz3) EMRow08.d4)

noncomputable def ep210 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz82) (Complex.im ↑qz3) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep211 := ep210 (@Enclosure.Complex.IsNear.im_isNear qz82 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz83) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz20 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz20 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz31)

noncomputable def ep212 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz82) (Complex.im ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz82) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep213 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz82) (Complex.im ↑qz3) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep214 := ep213 (@Enclosure.Complex.IsNear.re_isNear qz82 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz83) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz20 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz20 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz31)

noncomputable def ep215 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz82) (Complex.re ↑qz3) 0 1 0 1 60223 32768 1 32768 0 1 0 1

noncomputable def ep216 := ep215 (@Enclosure.Complex.IsNear.im_isNear qz82 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz83) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 60223 32768 1 32768 (Complex.ofReal_re qz3) EMRow08.d4)

noncomputable def ep217 := @ep178 6170500002651039307 30969000000000000000000 (ep206 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz82 (↑qz3) Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 (@ep207 65536 1 65536 (ep209 rfl) (ep211 rfl) rfl rfl) (@ep212 1 0 1 (ep214 rfl) (ep216 rfl) rfl rfl))

noncomputable abbrev qz84 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz325 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz85 := (@HMul.hMul Complex Complex Complex qz302 (@HMul.hMul Complex Complex Complex qz302 (2 : Complex) qz325) (@HSub.hSub Complex Complex Complex qz303 (@HMul.hMul Complex Complex Complex qz302 (2 : Complex) qz325) (1 : Complex)))

noncomputable abbrev qz326 := (@HPow.hPow Complex Int Complex qz432 qz428 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz86 := qz326

noncomputable def ep218 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz63 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz63 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) qz86)) Bool.false 443703 1073741824 3 1073741824

noncomputable def ep219 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz63 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) qz86) Bool.false 0 1 0 1 Bool.false

noncomputable def ep220 := @ep219 0 1 0 1 Bool.false 443703 1073741824 3 1073741824 Bool.true 1566419491 402653184000 10591 402653184000 Bool.false 443703 443703 1073741824 3 1073741824 Bool.true 1566419491 1566419491 402653184000 10591

noncomputable def ep221 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz63 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false

noncomputable def ep222 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) qz86 Bool.false 443703 1073741824 3 1073741824 Bool.true 1566419491 402653184000 10591 402653184000

noncomputable abbrev qz87 := (Complex.re qz326)

noncomputable abbrev qz88 := (Complex.im qz326)

noncomputable def ep223 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz87) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz88) 443703 1073741824 3 1073741824 0 1 0

noncomputable def ep224 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz87 1 12 0 1 1331109 268435456 9 268435456 443703

noncomputable def ep225 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz20) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz327 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz20 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz31)

noncomputable def ep226 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep225 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz327)

noncomputable def ep227 := @Enclosure.Complex.IsNear.re_isNear qz86 Bool.false 1331109 268435456 9 268435456 Bool.true 1566419491 33554432000 10591 33554432000

noncomputable abbrev qz433 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz328 := (@HPow.hPow Complex Nat Complex qz433 qz428 1)

noncomputable abbrev qz89 := (@Inv.inv Complex Complex.instInv qz328)

noncomputable def ep228 := @Enclosure.Complex.IsNear.of_eq qz86 qz89 Bool.false 1331109 268435456 9 268435456 Bool.true 1566419491 33554432000 10591

noncomputable def ep229 := @Enclosure.Complex.IsNear.of_parts qz89 Bool.false 1331109 268435456 9 268435456 Bool.true 1566419491 33554432000 10591

noncomputable abbrev qz90 := (Complex.re qz328)

noncomputable abbrev qz91 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz92 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz93 := qz328

noncomputable def ep230 := @Enclosure.Real.IsNear.mulLit_ff qz90 (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz93)) 9000 4000 0 1 147901 67108864 1 67108864

noncomputable def ep231 := @Enclosure.Complex.IsNear.re_isNear qz93 Bool.false 9000 4000 0 1 Bool.false 84728 4000 0 1

noncomputable def ep232 := @Enclosure.Complex.IsNear.of_eq qz93 qz63 Bool.false 9000 4000 0 1 Bool.false 84728 4000 0

noncomputable def ep233 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz93)) Bool.false 147901 67108864 1 67108864 147901 67108864 1

noncomputable abbrev qz94 := (@instHAdd Real Real.instAdd)

noncomputable abbrev qz95 := (Complex.im qz328)

noncomputable def ep234 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz93) (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 qz90 qz90) (@HMul.hMul Real Real Real qz0 qz95 qz95)) Bool.false 56717453 125000 0 1

noncomputable def ep235 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz90 qz90) (@HMul.hMul Real Real Real qz0 qz95 qz95) 81 16 0 1 112169281 250000

noncomputable def ep236 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz90 9000 4000 0 1 9000 4000 0 1

noncomputable def ep237 := @Enclosure.Real.IsNear.mulLit_ff qz95 qz95 84728 4000 0 1 84728 4000 0 1

noncomputable def ep238 := @Enclosure.Complex.IsNear.im_isNear qz93 Bool.false 9000 4000 0 1 Bool.false 84728 4000 0 1

noncomputable abbrev qz96 := (ep231 (@ep232 1 (BSN.pow_one_c qz304) qz324))

noncomputable abbrev qz97 := (ep238 (@ep232 1 (BSN.pow_one_c qz304) qz324))

noncomputable def ep239 := @ep235 0 1 1814958496 56717453 125000 0 1 (@ep236 81 16 0 1 qz96 qz96 rfl) (@ep237 112169281 250000 0 1 qz97 qz97 rfl)

noncomputable def ep240 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz93) 56717453 125000 0 1 73950 73951 33554432 (ep234 (Enclosure.Complex.normSq_eq_mul_add_mul qz93) (ep239 rfl rfl)) rfl

noncomputable def ep241 := @Enclosure.Real.IsNear.of_eq (Complex.re qz89) (@HMul.hMul Real Real Real qz0 qz90 (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz93))) Bool.false 1331109 268435456 9 268435456 (Enclosure.Complex.inv_re_eq_mul qz93) (@ep230 1331109 268435456 9 268435456 qz96 (@ep233 67108864 (ep240 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep242 := @Enclosure.Real.IsNear.of_eq (Complex.im qz89) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz95) (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz93))) Bool.true 1566419491 33554432000 10591 33554432000 (Enclosure.Complex.inv_im_eq_mul qz93)

noncomputable def ep243 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz95) (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz93)) 84728 4000 0 1 147901 67108864 1

noncomputable def ep244 := @ep243 67108864 1566419491 33554432000 10591 33554432000 (@Enclosure.Real.IsNear.neg qz95 Bool.false 84728 4000 0 1 qz97) (@ep233 67108864 (ep240 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep245 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz88 0 1 0 1 1566419491 33554432000 10591 33554432000 0

noncomputable def ep246 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep225 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz327)

noncomputable def ep247 := @Enclosure.Complex.IsNear.im_isNear qz86 Bool.false 1331109 268435456 9 268435456 Bool.true 1566419491 33554432000 10591 33554432000

noncomputable abbrev qz98 := (@ep228 33554432000 (BSN.zpow_one_sub_two_mul qz304 1 1 rfl rfl) (@ep229 33554432000 ep241 (ep242 ep244)))

noncomputable def ep248 := @ep223 1 443703 443703 1073741824 3 1073741824 (@ep224 1073741824 3 1073741824 ep226 (ep227 qz98) rfl) (@ep245 1 0 1 ep246 (ep247 qz98) rfl) rfl

noncomputable def ep249 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz88) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz87) 1566419491 402653184000 10591 402653184000 0 1 0

noncomputable def ep250 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz88 1 12 0 1 1566419491 33554432000 10591 33554432000 1566419491

noncomputable def ep251 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz87 0 1 0 1 1331109 268435456 9 268435456 0

noncomputable def ep252 := @ep249 1 1566419491 1566419491 402653184000 10591 402653184000 (@ep250 402653184000 10591 402653184000 ep226 (ep247 qz98) rfl) (@ep251 1 0 1 ep246 (ep227 qz98) rfl) rfl

noncomputable abbrev qz99 := (@Enclosure.Complex.IsNear.mk qz265 qz265 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz277 qz277)

noncomputable def ep253 := @ep220 402653184000 (@ep221 0 1 0 1 (BSN.stirling_sum_base qz63) qz99) (ep222 (ep248 rfl) (ep252 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep254 := @ep176 15594321614523079309 337769972052787200 25277704524927260517097 ep164 (ep217 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep218 Bool.true 1566419491 402653184000 10591 402653184000 (BSN.stirling_sum_succ qz63 0 1 rfl) (ep253 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep255 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz24 2) Bool.false 3438559398534391 562949953421312 62500000030969 3871125000000000000 Bool.false 864370398102947 281474976710656

noncomputable abbrev qz100 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz260 qz305 qz325))

noncomputable def ep256 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz24 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz24 1) qz100) Bool.false 3438559398534391 562949953421312 62500000030969 3871125000000000000 Bool.false 864370398102947 281474976710656 1000000000030969 30969000000000000000

noncomputable def ep257 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz24 1) qz100 Bool.false 3437620948180215 1125899906842624 62500000030969 7742250000000000000 Bool.false 877639699563939 562949953421312 1000000000030969 61938000000000000000 Bool.false

noncomputable def ep258 := nat_lit 7742947412965400078595777363968

noncomputable def ep259 := nat_lit 973194550701629847954079612928

noncomputable abbrev qz101 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz260 qz305 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep260 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz24 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz24 0) qz101) Bool.false 3437620948180215 1125899906842624 62500000030969 7742250000000000000 Bool.false 877639699563939 562949953421312 1000000000030969 61938000000000000000

noncomputable def ep261 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz24 0) qz101 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz329 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz75))

noncomputable def ep262 := @Enclosure.Complex.IsNear.of_eq qz101 qz329 Bool.false 3437620948180215 1125899906842624 62500000030969 7742250000000000000 Bool.false 877639699563939 562949953421312 1000000000030969 61938000000000000000

noncomputable def ep263 := nat_lit 246956915955630476583557192976445607905819096881074061237529856305119964567405854720

noncomputable def ep264 := nat_lit 6449165704279988339122118574509452258462401111517243968091598628941328536750260224

noncomputable def ep265 := nat_lit 858849801611567019908017204161300962106446588678007078615207952071597836206080

noncomputable def ep266 := BSN.log_dyadic_bound 3083833984 11275833984 5 4 ep263 131072 61938 ep264 ep265 73566 14359667968 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3083833984) (BSN.artanhQ 11275833984) 0 4 ep264 ep263 ep265 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep267 := @Enclosure.Real.IsNear.mulLit_ff qz77 (Real.log (Enclosure.sfrac Bool.false 7179833984 16000000)) 1 2 0 1 3437620948180215 562949953421312 62500000030969 3871125000000000000 3437620948180215 1125899906842624 62500000030969 7742250000000000000 qz319 (BSN.isNear_log_sfrac 7179833984 16000000 3437620948180215 562949953421312 62500000030969 3871125000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7179833984) qz320)) Bool.false 28836854586872136990720 4722366482869645213696 1000000000495504 61938000000000000000 3437620948180215 562949953421312 62500000030969 3871125000000000000 (BSN.log_rat_reduce_isNear 7179833984 16000000 8 14359667968 8192000000 73566 131072 24973259072661432 36028797018963968 61938 1000000000000000 rfl rfl rfl rfl (ep266 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep268 := BSN.arctan_dyadic_bound_f 1000 84728 1 0 131072 61938 0 1 1 0 1 1 1546 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 84728) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 84728) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz330 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz331 := (@Nat.cast Real Real.instNatCast 84728)

noncomputable def ep269 := @Enclosure.Real.IsNear.subLit_ff_p qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz331)) 884279719003555 562949953421312 1 2000000000000000 1546 131072 1 61938 115033990701244612608 877639699563939 562949953421312 1000000000030969 61938000000000000000 qz79 (ep268 rfl) rfl rfl

noncomputable abbrev qz102 := (@HAdd.hAdd Complex Complex Complex qz260 qz305 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz332 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz75)

noncomputable def ep270 := @ep261 3437620948180215 1125899906842624 62500000030969 7742250000000000000 Bool.false 877639699563939 562949953421312 1000000000030969 61938000000000000000 Bool.false 3437620948180215 3437620948180215 1125899906842624 62500000030969 7742250000000000000 Bool.false 877639699563939 877639699563939 562949953421312 1000000000030969 61938000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz24 0) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz24) qz99) (ep262 (@congrArg Complex Complex qz102 qz332 Complex.log (BSN.w_shift_mk qz24 Bool.false 42364 1000 0 qz25 rfl)) (@Enclosure.Complex.IsNear.of_parts qz329 Bool.false 3437620948180215 1125899906842624 62500000030969 7742250000000000000 Bool.false 877639699563939 562949953421312 1000000000030969 61938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz329) (@HMul.hMul Real Real Real qz0 qz77 (Real.log (Enclosure.sfrac Bool.false 7179833984 16000000))) Bool.false 3437620948180215 1125899906842624 62500000030969 7742250000000000000 (Enclosure.clog_re_eq 1000 84728 4000 7179833984 16000000 rfl rfl rfl) (ep267 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz329) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz331 qz330)) Bool.false 877639699563939 562949953421312 1000000000030969 61938000000000000000 (Enclosure.clog_im_eq 1000 84728 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz331 qz330)) (@HSub.hSub Real Real Real qz52 qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz331))) Bool.false 877639699563939 562949953421312 1000000000030969 61938000000000000000 (BSN.arctan_recip 84728 1000 rfl rfl) ep269)))) rfl rfl

noncomputable abbrev qz333 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz75))

noncomputable def ep271 := @Enclosure.Complex.IsNear.of_eq qz100 qz333 Bool.false 3439497848888567 1125899906842624 62500000030969 7742250000000000000 Bool.false 851101096641955 562949953421312 1000000000030969 61938000000000000000

noncomputable def ep272 := nat_lit 251193450644473989246245038189525245436474913963861793157460460505851686950765854720

noncomputable def ep273 := nat_lit 6637623810254422292406304414155499224359696342663634428074748047266187302062260224

noncomputable def ep274 := nat_lit 913801338777142461205292694313138057789292755604082358431826224734084876206080

noncomputable def ep275 := BSN.log_dyadic_bound 3107833984 11299833984 5 4 ep272 131072 61938 ep273 ep274 74003 14407667968 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3107833984) (BSN.artanhQ 11299833984) 0 4 ep273 ep272 ep274 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep276 := @Enclosure.Real.IsNear.mulLit_ff qz77 (Real.log (Enclosure.sfrac Bool.false 7203833984 16000000)) 1 2 0 1 3439497848888567 562949953421312 62500000030969 3871125000000000000 3439497848888567 1125899906842624 62500000030969 7742250000000000000 qz319 (BSN.isNear_log_sfrac 7203833984 16000000 3439497848888567 562949953421312 62500000030969 3871125000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7203833984) qz320)) Bool.false 28852599171169424244736 4722366482869645213696 1000000000495504 61938000000000000000 3439497848888567 562949953421312 62500000030969 3871125000000000000 (BSN.log_rat_reduce_isNear 7203833984 16000000 8 14407667968 8192000000 74003 131072 24973259072661432 36028797018963968 61938 1000000000000000 rfl rfl rfl rfl (ep275 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep277 := BSN.arctan_dyadic_bound_f 5000 84728 1 0 131072 61938 0 1 1 0 1 1 7725 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 84728) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 84728) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz334 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep278 := @Enclosure.Real.IsNear.subLit_ff_p qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz334 qz331)) 884279719003555 562949953421312 1 2000000000000000 7725 131072 1 61938 111555522939054325760 851101096641955 562949953421312 1000000000030969 61938000000000000000 qz79 (ep277 rfl) rfl rfl

noncomputable abbrev qz103 := (@HAdd.hAdd Complex Complex Complex qz260 qz305 qz325)

noncomputable abbrev qz335 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz75)

noncomputable def ep279 := @ep257 3439497848888567 1125899906842624 62500000030969 7742250000000000000 Bool.false 851101096641955 562949953421312 1000000000030969 61938000000000000000 Bool.false ep258 3438559398534391 562949953421312 62500000030969 3871125000000000000 Bool.false ep259 864370398102947 281474976710656 1000000000030969 30969000000000000000 (ep260 (BSN.log_sum_c_succ qz24 0 1 rfl) (ep270 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep271 (@congrArg Complex Complex qz103 qz335 Complex.log (BSN.w_shift_mk qz24 Bool.false 42364 1000 1 qz25 rfl)) (@Enclosure.Complex.IsNear.of_parts qz333 Bool.false 3439497848888567 1125899906842624 62500000030969 7742250000000000000 Bool.false 851101096641955 562949953421312 1000000000030969 61938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz333) (@HMul.hMul Real Real Real qz0 qz77 (Real.log (Enclosure.sfrac Bool.false 7203833984 16000000))) Bool.false 3439497848888567 1125899906842624 62500000030969 7742250000000000000 (Enclosure.clog_re_eq 5000 84728 4000 7203833984 16000000 rfl rfl rfl) (ep276 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz333) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz331 qz334)) Bool.false 851101096641955 562949953421312 1000000000030969 61938000000000000000 (Enclosure.clog_im_eq 5000 84728 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz331 qz334)) (@HSub.hSub Real Real Real qz52 qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz334 qz331))) Bool.false 851101096641955 562949953421312 1000000000030969 61938000000000000000 (BSN.arctan_recip 84728 5000 rfl rfl) ep278)))) rfl rfl

noncomputable def ep280 := @ep169 ep164 Bool.false 3438559398534391 562949953421312 62500000030969 3871125000000000000 Bool.false 864370398102947 281474976710656 1000000000030969 30969000000000000000 Bool.true ep170 3728650674983200849 112589990684262400 49156652915325050795059 ep164 Bool.false ep171 14557077136799542909 337769972052787200 29373704525054109541097 ep164 (@ep172 112589990684262400 47108652914310258603059 ep164 Bool.false 15594321614523079309 337769972052787200 25277704524927260517097 ep164 (BSN.logGammaStirling_unfold 1 qz63) (ep254 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep255 1000000000030969 30969000000000000000 (BSN.log_sum_c_eq qz24 2) (ep256 (BSN.log_sum_c_succ qz24 1 2 rfl) (ep279 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz104 := (@HDiv.hDiv Real Real Real qz257 qz267 (2 : Real))

noncomputable def ep281 := @Enclosure.Real.IsNear.mulLit_ff qz104 (Real.log Real.pi) 42364 2000 0 1 75021 65536 1 32768 794547411 32768000 10591 16384000 (@Enclosure.Real.IsNear.of_eq qz104 (Enclosure.sfrac Bool.false 42364 2000) Bool.false 42364 2000 0 1 (BSN.t_half_eq qz24 Bool.false 42364 1000 qz25) (Enclosure.Real.IsNear.const Bool.false 42364 2000)) EMRow08.d5 rfl

noncomputable def ep282 := @ep166 10591 16384000 ep167 31834723939600066673 1688849860263936000 111371874275054109541097 ep164 (@ep168 29373704525054109541097 ep164 (ep280 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep281 rfl rfl

noncomputable def ep283 := BSN.cos_dyadic_bound_f 102412 268435456 1 0 131072 61999 0 1 1 0 1 1 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 102412) qz269 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 102412) qz270 0 0 rfl) rfl rfl

noncomputable abbrev qz336 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep284 := @ep163 32768 Bool.false 131071 131072 1 30969 (@ep165 2470699 131072 29 32768 ep282 rfl) (Enclosure.sfrac_false_div 2470699 131072) (BSN.cos_reduce0 qz306 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7206660422299025408) qz336) 226375608064910080 72057594037927936 Bool.false 131071 131072 3 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 2470699 131072 226375608064910080 72057594037927936 3 7206660422299025408 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 131071 131072 7206660422299025408 18889465931478580854784 102412 268435456 61999 61938 (ep283 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz105 := qz261

noncomputable abbrev qz106 := qz262

noncomputable abbrev qz337 := (@HPow.hPow Complex Complex Complex qz421 (@Nat.cast Complex Complex.instNatCast 9) qz422)

noncomputable abbrev qz107 := qz337

noncomputable abbrev qz338 := (@Nat.cast Complex Complex.instNatCast 9)

noncomputable abbrev qz108 := (@HAdd.hAdd Complex Complex Complex qz260 (@HDiv.hDiv Complex Complex Complex qz310 qz338 (@HSub.hSub Complex Complex Complex qz303 qz259 (1 : Complex))) qz309)

noncomputable abbrev qz109 := (@instHSub Nat instSubNat)

noncomputable abbrev qz339 := qz433

noncomputable abbrev qz110 := qz339

noncomputable abbrev qz111 := qz338

noncomputable def ep285 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz21 1 9) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 9, @HPow.hPow Complex Complex Complex qz105 (@Nat.cast Complex Complex.instNatCast n) qz106) (@HMul.hMul Complex Complex Complex qz51 qz107 (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) Bool.false 1515558385049668095073 1300942356412052275200 228881593689786564774949

noncomputable def ep286 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 9, @HPow.hPow Complex Complex Complex qz105 (@Nat.cast Complex Complex.instNatCast n) qz106) (@HMul.hMul Complex Complex Complex qz51 qz107 (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) Bool.false 2477989359 2147483648 1274405083999 266021684379648

noncomputable def ep287 := nat_lit 3254636849483449901996576866304

noncomputable def ep288 := nat_lit 14916637755549714924653409992704

noncomputable def ep289 := @ep286 Bool.true 4195027995 17179869184 2546116886975 532043368759296 Bool.false 14396167184225723473 1300942356412052275200 14428071858261686133949 ep161 Bool.false 2308414451239430087969 13009423564120522752000 14485690983398282913523 ep161 Bool.false ep287 1515558385049668095073 1300942356412052275200 228881593689786564774949 ep161 Bool.true ep288 868262592444063334531 13009423564120522752000

noncomputable def ep290 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 9, @HPow.hPow Complex Complex Complex qz105 (@Nat.cast Complex Complex.instNatCast n) qz106) qz4 Bool.false 2477989359 2147483648 1274405083999 266021684379648 Bool.true 4195027995 17179869184 2546116886975

noncomputable def ep291 := @Enclosure.Complex.IsNear.mul qz107 (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))) Bool.false 14396167184225723473 1300942356412052275200 14428071858261686133949 ep161 Bool.false

noncomputable abbrev qz112 := (Complex.re qz337)

noncomputable abbrev qz113 := (Complex.im qz337)

noncomputable def ep292 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz112 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz113 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) 13766205273306681037 208150777025928364032 508776525460350502837

noncomputable def ep293 := nat_lit 2148740471238658501902336

noncomputable def ep294 := nat_lit 268592558904832312737792000

noncomputable def ep295 := nat_lit 3995431180789007396946967316355348430848

noncomputable def ep296 := @Enclosure.Real.IsNear.mulLit_ff qz112 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 2262800581 17179869184 83629423981 177347789586432 6083702377

noncomputable abbrev qz340 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz114 := (@Inv.inv Real Real.instInv (Real.sqrt qz340))

noncomputable abbrev qz341 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz425 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable abbrev qz115 := (Real.cos qz341)

noncomputable abbrev qz116 := (@Neg.neg Real Real.instNeg (Real.sin qz341))

noncomputable def ep297 := @Enclosure.Complex.IsNear.of_eq qz107 (Complex.mk (@HMul.hMul Real Real Real qz0 qz114 qz115) (@HMul.hMul Real Real Real qz0 qz114 qz116)) Bool.false 2262800581 17179869184 83629423981 177347789586432 Bool.false 5260614855 17179869184 84337726303 177347789586432 (BSN.cpow_neg_s_mk qz24 42364 1000 9 qz25 rfl)

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9) qz26)

noncomputable def ep298 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz340) 393217 131072 1 131072 21845 21846 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz340) (Real.sqrt qz342) Bool.false 393217 131072 1 131072 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz342) Bool.false 393217 131072 1 131072 393217 131072 1 131072 (BSN.sqrt_enclosure 9 1 196608 196609 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep299 := BSN.log_dyadic_bound 1 17 2 1 867 65536 30969 1 1 7719 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz343 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz117 := qz343

noncomputable abbrev qz344 := (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9) qz26))

noncomputable def ep300 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz117 42364 1000 0 1 9895417793173221 4503599627370496 1000000000092907 30969000000000000000 104802369847497583611 1125899906842624000 10591000000983978037 7742250000000000000000 qz29 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000092907 30969000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz344 Bool.false 5188048803947201691648 2361183241434822606848 1000000000092907 30969000000000000000 9895417793173221 4503599627370496 1000000000092907 30969000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 7719 65536 24973259072661432 36028797018963968 30969 1000000000000000 rfl rfl rfl rfl (ep299 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep301 := nat_lit 141378859618480992072741580960000

noncomputable def ep302 := BSN.sin_dyadic_bound_f 109042580 268435456 2 1 131072 61999 ep301 ep75 ep301 ep301 ep76 ep301 51791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 109042580) qz274 0 1 ep301 ep75 ep301 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 109042580) qz275 0 1 ep301 ep76 ep301 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz118 := qz341

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12200601) qz57)

noncomputable def ep303 := @Enclosure.Real.IsNear.cos_image qz118 qz345 Bool.false 12200601 131072 45 32768 Bool.false 51791 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 104802369847497583611 1125899906842624000 10591000000983978037 7742250000000000000000 12200601 131072 45 32768 (ep300 rfl) rfl) (Enclosure.sfrac_false_div 12200601 131072) (BSN.cos_reduce3 qz345 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7673189436725481439232) qz336) 226375608064910080 72057594037927936 Bool.false 51791 131072 14 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q3 12200601 131072 226375608064910080 72057594037927936 14 7673189436725481439232 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 51791 131072 7673189436725481439232 18889465931478580854784 109042580 268435456 61999 61938 (ep302 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep304 := BSN.cos_dyadic_bound_f 109042580 268435456 2 1 131072 61999 ep301 ep94 ep301 ep301 ep95 ep301 120405 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 109042580) qz269 0 1 ep301 ep94 ep301 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 109042580) qz270 0 1 ep301 ep95 ep301 rfl rfl rfl rfl) rfl rfl

noncomputable def ep305 := @Enclosure.Real.IsNear.sin_image qz118 qz345 Bool.false 12200601 131072 45 32768 Bool.true 120405 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 104802369847497583611 1125899906842624000 10591000000983978037 7742250000000000000000 12200601 131072 45 32768 (ep300 rfl) rfl) (Enclosure.sfrac_false_div 12200601 131072) (BSN.sin_reduce3 qz345 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7673189436725481439232) qz336) 226375608064910080 72057594037927936 Bool.false 120405 131072 14 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q3 12200601 131072 226375608064910080 72057594037927936 14 7673189436725481439232 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 120405 131072 7673189436725481439232 18889465931478580854784 109042580 268435456 61999 61938 (ep304 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz119 := (Real.sin qz341)

noncomputable abbrev qz346 := (@Enclosure.Real.IsNear.recentre' qz114 Bool.false 43691 131072 1 131072 43691 131072 1 131072 (ep298 rfl rfl) rfl)

noncomputable def ep306 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz114 qz115) (@HMul.hMul Real Real Real qz0 qz114 qz116) Bool.false 2262800581 17179869184 83629423981 177347789586432 Bool.false 5260614855 17179869184 84337726303 177347789586432 (@Enclosure.Real.IsNear.mulLit_ff qz114 qz115 43691 131072 1 131072 51791 131072 1426373 1014792192 2262800581 17179869184 83629423981 177347789586432 qz346 (@Enclosure.Real.IsNear.recentre' qz115 Bool.false 51791 131072 1426373 1014792192 51791 131072 1426373 1014792192 (ep303 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz114 qz116 43691 131072 1 131072 120405 131072 1426373 1014792192 5260614855 17179869184 84337726303 177347789586432 qz346 (@Enclosure.Real.IsNear.neg qz119 Bool.true 120405 131072 1426373 1014792192 (@Enclosure.Real.IsNear.recentre' qz119 Bool.true 120405 131072 1426373 1014792192 120405 131072 1426373 1014792192 (ep305 rfl rfl) rfl)) rfl)

noncomputable def ep307 := @ep296 12115969848 0 1 13766205273306681037 208150777025928364032 508776525460350502837 ep293 (@Enclosure.Complex.IsNear.re_isNear qz107 Bool.false 2262800581 17179869184 83629423981 177347789586432 Bool.false 5260614855 17179869184 84337726303 177347789586432 (ep297 ep306))

noncomputable def ep308 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))) Bool.false 6083702377 12115969848 0 1 Bool.false

noncomputable def ep309 := @Enclosure.Complex.IsNear.addLitP qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) Bool.false 55811203 112184906 0 1 Bool.true 11914875

noncomputable def ep310 := @ep309 56092453 0 1 Bool.false 1 216 0 1 Bool.false 10591 27000 0 1 Bool.false 12167404754 6083702377 12115969848 0 1 Bool.false 272373544723 272373544723 1514496231000 0 1

noncomputable abbrev qz120 := (@HDiv.hDiv Complex Complex Complex qz310 qz338 (@HSub.hSub Complex Complex Complex qz303 qz259 (1 : Complex)))

noncomputable def ep311 := @Enclosure.Complex.IsNear.addLitP qz120 qz82 Bool.true 18000000 7179833984 0 1 Bool.true 1525104000 7179833984 0 1

noncomputable def ep312 := @Enclosure.Complex.IsNear.of_eq qz120 (Complex.mk (Enclosure.sfrac Bool.true 18000000 7179833984) (Enclosure.sfrac Bool.true 1525104000 7179833984)) Bool.true 18000000 7179833984 0 1 Bool.true 1525104000 7179833984 0 1

noncomputable def ep313 := @ep311 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 7143833984 55811203 112184906 0 1 Bool.true 1525104000 11914875 56092453 0 1 (ep312 (BSN.N_div_s_sub_one_mk qz24 42364 1000 9 qz25 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 18000000 7179833984) (Enclosure.sfrac Bool.true 1525104000 7179833984) Bool.true 18000000 7179833984 0 1 Bool.true 1525104000 7179833984 0 1 (Enclosure.Real.IsNear.const Bool.true 18000000 7179833984) (Enclosure.Real.IsNear.const Bool.true 1525104000 7179833984))) qz83 rfl

noncomputable abbrev qz121 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz347 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz433 (@Nat.cast Complex Complex.instNatCast 9) 1))

noncomputable abbrev qz122 := qz347

noncomputable def ep314 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz122)) Bool.false 1 216 0 1

noncomputable def ep315 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz122) Bool.false 0 1 0 1 Bool.false

noncomputable def ep316 := @ep315 0 1 0 1 Bool.false 1 216 0 1 Bool.false 10591 27000 0 1 Bool.false 1 1 216 0 1 Bool.false 10591 10591 27000 0

noncomputable def ep317 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false

noncomputable def ep318 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz122 Bool.false 1 216 0 1 Bool.false 10591 27000 0 1

noncomputable abbrev qz123 := (Complex.re qz347)

noncomputable abbrev qz124 := (Complex.im qz347)

noncomputable def ep319 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz123) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz124) 1 216 0 1 0 1 0

noncomputable def ep320 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz123 1 24 0 1 1 9 0 1 1

noncomputable def ep321 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep322 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep323 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz20) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow08.d7 rfl) qz327

noncomputable def ep324 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) qz21 Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 (BSN.ascPochhammer_one_eval qz21)

noncomputable def ep325 := ep324 (@Enclosure.Complex.IsNear.of_eq qz21 (Complex.mk qz77 qz24) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 (BSN.s_crit_mk qz24 Bool.false 42364 1000 qz25) (@Enclosure.Complex.IsNear.mk qz77 qz24 Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 qz319 qz29))

noncomputable def ep326 := @ep322 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep325)

noncomputable def ep327 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 42364 1000 0 1 0 1 0

noncomputable def ep328 := @ep327 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep325)

noncomputable def ep329 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) 10591 3000 0 1 0 1 0 1 10591

noncomputable def ep330 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 42364 1000 0 1 10591 3000 0

noncomputable def ep331 := @ep330 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep325)

noncomputable def ep332 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep333 := @ep332 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep325)

noncomputable def ep334 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 10591 3000 0 1 (@ep321 1 24 0 1 (ep326 rfl) (ep328 rfl) rfl rfl) (@ep329 10591 3000 0 1 (ep331 rfl) (ep333 rfl) rfl rfl)

noncomputable def ep335 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 10591 3000 0 1 ep334

noncomputable abbrev qz125 := (@Enclosure.Complex.IsNear.of_eq qz347 (Complex.mk (Enclosure.sfrac Bool.false 1 9) qz265) Bool.false 1 9 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 9 1 9 EMRow08.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 9) qz265 Bool.false 1 9 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 9) qz277))

noncomputable def ep336 := @ep320 216 0 1 ep335 (@Enclosure.Complex.IsNear.re_isNear qz122 Bool.false 1 9 0 1 Bool.false 0 1 0 1 qz125)

noncomputable def ep337 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz124 10591 3000 0 1 0 1 0 1 0

noncomputable def ep338 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 10591 3000 0 1 ep334

noncomputable def ep339 := @ep337 1 0 1 ep338 (@Enclosure.Complex.IsNear.im_isNear qz122 Bool.false 1 9 0 1 Bool.false 0 1 0 1 qz125)

noncomputable def ep340 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz124) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz123) 0 1 0 1 10591 27000 0

noncomputable def ep341 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz124 1 24 0 1 0 1 0 1 0

noncomputable def ep342 := @ep341 1 0 1 ep335 (@Enclosure.Complex.IsNear.im_isNear qz122 Bool.false 1 9 0 1 Bool.false 0 1 0 1 qz125)

noncomputable def ep343 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz123 10591 3000 0 1 1 9 0 1 10591

noncomputable def ep344 := @ep343 27000 0 1 ep338 (@Enclosure.Complex.IsNear.re_isNear qz122 Bool.false 1 9 0 1 Bool.false 0 1 0 1 qz125)

noncomputable def ep345 := @ep316 1 (@ep317 0 1 0 1 (BSN.bern_sum_base qz21 9) qz99) (ep318 (@ep319 1 1 1 216 0 1 (ep336 rfl) (ep339 rfl) rfl rfl) (@ep340 1 10591 10591 27000 0 1 (ep342 rfl) (ep344 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep346 := ep310 (ep313 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep314 Bool.false 10591 27000 0 1 (BSN.bern_sum_succ qz21 9 0 1 1 rfl rfl) (ep345 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep347 := @Enclosure.Real.IsNear.mulLit_ff qz113 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 5260614855 17179869184 84337726303 177347789586432 272373544723

noncomputable def ep348 := @ep347 1514496231000 0 1 95523487698588044011 1734589808549403033600 22971365467026303949069 ep294 (@Enclosure.Complex.IsNear.im_isNear qz107 Bool.false 2262800581 17179869184 83629423981 177347789586432 Bool.false 5260614855 17179869184 84337726303 177347789586432 (ep297 ep306))

noncomputable def ep349 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))) Bool.false 6083702377 12115969848 0 1 Bool.false

noncomputable def ep350 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz112 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz113 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) 616327015248233884063 26018847128241045504000 22778442652847632202263

noncomputable def ep351 := nat_lit 320332174482246264050927439217382677020672

noncomputable def ep352 := @Enclosure.Real.IsNear.mulLit_ff qz112 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 2262800581 17179869184 83629423981 177347789586432 272373544723

noncomputable def ep353 := @ep352 1514496231000 0 1 616327015248233884063 26018847128241045504000 22778442652847632202263 ep294 (@Enclosure.Complex.IsNear.re_isNear qz107 Bool.false 2262800581 17179869184 83629423981 177347789586432 Bool.false 5260614855 17179869184 84337726303 177347789586432 (ep297 ep306))

noncomputable def ep354 := @Enclosure.Real.IsNear.mulLit_ff qz113 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 5260614855 17179869184 84337726303 177347789586432 6083702377

noncomputable def ep355 := @ep354 12115969848 0 1 10668005032615003445 69383592341976121344 513085625980336522231 ep293 (@Enclosure.Complex.IsNear.im_isNear qz107 Bool.false 2262800581 17179869184 83629423981 177347789586432 Bool.false 5260614855 17179869184 84337726303 177347789586432 (ep297 ep306))

noncomputable abbrev qz348 := (ep346 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep356 := @ep291 2308414451239430087969 13009423564120522752000 14485690983398282913523 ep161 (@ep292 ep293 95523487698588044011 1734589808549403033600 22971365467026303949069 ep294 ep295 14396167184225723473 1300942356412052275200 14428071858261686133949 ep161 (ep307 (@ep308 272373544723 1514496231000 0 1 qz348) rfl) (ep348 (@ep349 272373544723 1514496231000 0 1 qz348) rfl) rfl rfl) (@ep350 ep294 10668005032615003445 69383592341976121344 513085625980336522231 ep293 ep351 2308414451239430087969 13009423564120522752000 14485690983398282913523 ep161 (ep353 (@ep349 272373544723 1514496231000 0 1 qz348) rfl) (ep355 (@ep308 272373544723 1514496231000 0 1 qz348) rfl) rfl rfl)

noncomputable def ep357 := @ep289 228712603706125532426023 ep161 (@ep290 532043368759296 (BSN.head_sum_c_eq qz21 9) EMRow08.d6) ep356 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def ep358 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz21 1 9) Bool.false 1515558385049668095073 1300942356412052275200 228881593689786564774949 ep161 Bool.true 868262592444063334531 13009423564120522752000 228712603706125532426023 ep161 (@ep285 ep161 Bool.true 868262592444063334531 13009423564120522752000 228712603706125532426023 ep161 (BSN.zetaApproximant_eq_folded' qz21 1 9 rfl) (ep357 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep359 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) (Complex.im (zetaApproximant qz21 1 9)) 25 65536 930869

noncomputable def ep360 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) Bool.false 50 131072 930869

noncomputable def ep361 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56) qz306 Bool.false 2470699 131072 29

noncomputable def ep362 := BSN.sin_dyadic_bound_f 102412 268435456 1 0 131072 61999 0 1 1 0 1 1 50 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 102412) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 102412) qz275 0 0 rfl) rfl rfl

noncomputable def ep363 := @ep361 32768 Bool.false 50 131072 1 30969 (@ep165 2470699 131072 29 32768 ep282 rfl) (Enclosure.sfrac_false_div 2470699 131072) (BSN.sin_reduce0 qz306 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7206660422299025408) qz336) 226375608064910080 72057594037927936 Bool.false 50 131072 3 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 2470699 131072 226375608064910080 72057594037927936 3 7206660422299025408 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 50 131072 7206660422299025408 18889465931478580854784 102412 268435456 61999 61938 (ep362 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep364 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz21 1 9) Bool.false 1515558385049668095073 1300942356412052275200 228881593689786564774949 ep161 Bool.true 868262592444063334531 13009423564120522752000 228712603706125532426023 ep161 (@ep285 ep161 Bool.true 868262592444063334531 13009423564120522752000 228712603706125532426023 ep161 (BSN.zetaApproximant_eq_folded' qz21 1 9 rfl) (ep357 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow08.d9 : Enclosure.Real.IsNear (hardyZApproximantEM 1 9 qz24) Bool.false ep145 ep146 ep147 ep148 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 9 qz24) ep149 Bool.false ep145 ep146 ep147 ep148 (@Eq.refl Real ep149) (@ep150 Bool.false ep145 ep146 ep147 ep148 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56) (zetaApproximant qz21 1 9)) (@ep152 ep153 ep154 ep155 868262592444063334531 ep156 ep157 ep158 ep159 ep145 ep146 ep147 ep148 (@ep160 1014792192 1515558385049668095073 1300942356412052275200 228881593689786564774949 ep161 ep151 ep153 ep154 ep155 (@ep162 1014792192 131071 131072 930869 1014792192 (ep284 rfl rfl) rfl) ep358 rfl) (@ep359 1014792192 868262592444063334531 13009423564120522752000 228712603706125532426023 ep161 868262592444063334531 ep156 ep157 ep158 (@ep360 1014792192 25 65536 930869 1014792192 (ep363 rfl rfl) rfl) ep364 rfl) rfl rfl))

noncomputable abbrev qz449 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 45593 1000)))

noncomputable abbrev qz434 := qz449

noncomputable abbrev qz349 := qz434

noncomputable abbrev qz126 := (BSN.headSumC qz349 9)

noncomputable abbrev qz127 := (BSN.headSumC qz349 8)

noncomputable abbrev qz435 := (@Neg.neg Complex Complex.instNeg qz449)

noncomputable abbrev qz350 := qz435

noncomputable abbrev qz128 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 8) qz350)

noncomputable def ep365 := @Enclosure.Complex.IsNear.of_eq qz126 (@HAdd.hAdd Complex Complex Complex qz5 qz127 qz128) Bool.false 60437698919 17179869184 2744937433409 532043368759296 Bool.true 557857645 2147483648 1362643940815 266021684379648

noncomputable def ep366 := @Enclosure.Complex.IsNear.addLitP qz127 qz128 Bool.false 27646066651 8589934592 4265629345 923686404096 Bool.true 1235442215 17179869184 270959424421 59115929862144 Bool.false

noncomputable abbrev qz129 := (BSN.headSumC qz349 7)

noncomputable abbrev qz130 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 7) qz350)

noncomputable def ep367 := @Enclosure.Complex.IsNear.of_eq qz127 (@HAdd.hAdd Complex Complex Complex qz5 qz129 qz130) Bool.false 27646066651 8589934592 4265629345 923686404096 Bool.true 1235442215 17179869184 270959424421 59115929862144

noncomputable def ep368 := @Enclosure.Complex.IsNear.addLitP qz129 qz130 Bool.false 50561413671 17179869184 716634676835 177347789586432 Bool.false 803124347 4294967296 355285519771 88673894793216 Bool.false

noncomputable abbrev qz131 := (BSN.headSumC qz349 6)

noncomputable abbrev qz132 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 6) qz350)

noncomputable def ep369 := @Enclosure.Complex.IsNear.of_eq qz129 (@HAdd.hAdd Complex Complex Complex qz5 qz131 qz132) Bool.false 50561413671 17179869184 716634676835 177347789586432 Bool.false 803124347 4294967296 355285519771 88673894793216

noncomputable def ep370 := @Enclosure.Complex.IsNear.addLitP qz131 qz132 Bool.false 43548125521 17179869184 1813272854839 532043368759296 Bool.false 1640896419 8589934592 450779909305 133010842189824 Bool.false

noncomputable abbrev qz133 := (BSN.headSumC qz349 5)

noncomputable abbrev qz134 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 5) qz350)

noncomputable def ep371 := @Enclosure.Complex.IsNear.of_eq qz131 (@HAdd.hAdd Complex Complex Complex qz5 qz133 qz134) Bool.false 43548125521 17179869184 1813272854839 532043368759296 Bool.false 1640896419 8589934592 450779909305 133010842189824

noncomputable def ep372 := @Enclosure.Complex.IsNear.addLitP qz133 qz134 Bool.false 46878977929 17179869184 1451653770539 532043368759296 Bool.true 3641636883 17179869184 1439602493879 532043368759296 Bool.true

noncomputable abbrev qz135 := (BSN.headSumC qz349 4)

noncomputable abbrev qz136 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 4) qz350)

noncomputable def ep373 := @Enclosure.Complex.IsNear.of_eq qz133 (@HAdd.hAdd Complex Complex Complex qz5 qz135 qz136) Bool.false 46878977929 17179869184 1451653770539 532043368759296 Bool.true 3641636883 17179869184 1439602493879 532043368759296

noncomputable def ep374 := @Enclosure.Complex.IsNear.addLitP qz135 qz136 Bool.false 9720222481 4294967296 43564371491 22168473698304 Bool.true 508801743 17179869184 345264248905 177347789586432 Bool.false

noncomputable abbrev qz137 := (BSN.headSumC qz349 3)

noncomputable abbrev qz138 := (@HPow.hPow Complex Complex Complex qz261 qz263 qz350)

noncomputable def ep375 := @Enclosure.Complex.IsNear.of_eq qz135 (@HAdd.hAdd Complex Complex Complex qz5 qz137 qz138) Bool.false 9720222481 4294967296 43564371491 22168473698304 Bool.true 508801743 17179869184 345264248905 177347789586432

noncomputable def ep376 := @Enclosure.Complex.IsNear.addLitP qz137 qz138 Bool.false 14558423687 8589934592 288484878191 266021684379648 Bool.true 281799621 2147483648 17828094737 16626355273728 Bool.false

noncomputable abbrev qz139 := (BSN.headSumC qz349 2)

noncomputable abbrev qz140 := (@HPow.hPow Complex Complex Complex qz261 qz264 qz350)

noncomputable def ep377 := @Enclosure.Complex.IsNear.of_eq qz137 (@HAdd.hAdd Complex Complex Complex qz5 qz139 qz140) Bool.false 14558423687 8589934592 288484878191 266021684379648 Bool.true 281799621 2147483648 17828094737 16626355273728

noncomputable def ep378 := @Enclosure.Complex.IsNear.addLitP qz139 qz140 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz141 := qz349

noncomputable def ep379 := @Enclosure.Complex.IsNear.of_eq qz139 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz20) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz141)

noncomputable abbrev qz450 := (Enclosure.sfrac Bool.false 45593 1000)

noncomputable abbrev qz436 := qz450

noncomputable abbrev qz351 := qz436

noncomputable abbrev qz142 := (@HMul.hMul Real Real Real qz254 qz351 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz143 := qz351

noncomputable abbrev qz352 := (@Eq.refl Real qz436)

noncomputable abbrev qz144 := qz352

noncomputable def ep380 := @Enclosure.Complex.IsNear.of_eq qz140 (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz142)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz142)))) Bool.false 5968489095 8589934592 288484878191 266021684379648 Bool.true 281799621 2147483648 17828094737 16626355273728 (BSN.cpow_neg_s_mk qz143 45593 1000 2 qz144 rfl)

noncomputable def ep381 := nat_lit 6304051414227265627529049834256

noncomputable def ep382 := BSN.cos_dyadic_bound_f 50107754 268435456 2 1 131072 61999 ep381 ep94 ep381 ep381 ep95 ep381 128795 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 50107754) qz269 0 1 ep381 ep94 ep381 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 50107754) qz270 0 1 ep381 ep95 ep381 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz353 := (Enclosure.Real.IsNear.const Bool.false 45593 1000)

noncomputable abbrev qz145 := qz353

noncomputable abbrev qz354 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4142215) qz57)

noncomputable abbrev qz355 := (@Nat.cast Real Real.instNatCast 3526019769953450721280)

noncomputable def ep383 := @Enclosure.Real.IsNear.cos_image qz142 qz354 Bool.false 4142215 131072 97 65536 Bool.false 128795 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 1035553809 32768000 45593 30969000 4142215 131072 97 65536 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz28 45593 1000 0 1 45426 65536 1 30969 1035553809 32768000 45593 30969000 qz145 qz273 rfl) rfl) (Enclosure.sfrac_false_div 4142215 131072) (BSN.cos_reduce0 qz354 (@HDiv.hDiv Real Real Real qz2 qz355 qz336) 226375608064910080 72057594037927936 Bool.false 128795 131072 5 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 4142215 131072 226375608064910080 72057594037927936 5 3526019769953450721280 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 128795 131072 3526019769953450721280 18889465931478580854784 50107754 268435456 61999 61938 (ep382 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep384 := BSN.sin_dyadic_bound_f 50107754 268435456 1 0 131072 61999 0 1 1 0 1 1 24324 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 50107754) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 50107754) qz275 0 0 rfl) rfl rfl

noncomputable def ep385 := @Enclosure.Real.IsNear.sin_image qz142 qz354 Bool.false 4142215 131072 97 65536 Bool.false 24324 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 1035553809 32768000 45593 30969000 4142215 131072 97 65536 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz28 45593 1000 0 1 45426 65536 1 30969 1035553809 32768000 45593 30969000 qz145 qz273 rfl) rfl) (Enclosure.sfrac_false_div 4142215 131072) (BSN.sin_reduce0 qz354 (@HDiv.hDiv Real Real Real qz2 qz355 qz336) 226375608064910080 72057594037927936 Bool.false 24324 131072 5 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 4142215 131072 226375608064910080 72057594037927936 5 3526019769953450721280 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 24324 131072 3526019769953450721280 18889465931478580854784 50107754 268435456 61999 61938 (ep384 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep386 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz142)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz142))) Bool.false 5968489095 8589934592 288484878191 266021684379648 Bool.true 281799621 2147483648 17828094737 16626355273728 (@Enclosure.Real.IsNear.mulLit_ff qz22 (Real.cos qz142) 46341 65536 1 65536 128795 131072 3069529 2029584384 5968489095 8589934592 288484878191 266021684379648 qz276 (@Enclosure.Real.IsNear.recentre' (Real.cos qz142) Bool.false 128795 131072 3069529 2029584384 128795 131072 3069529 2029584384 (ep383 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz22 (@Neg.neg Real Real.instNeg (Real.sin qz142)) 46341 65536 1 65536 6081 32768 3069529 2029584384 281799621 2147483648 17828094737 16626355273728 qz276 (@Enclosure.Real.IsNear.neg (Real.sin qz142) Bool.false 6081 32768 3069529 2029584384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz142) Bool.false 24324 131072 3069529 2029584384 6081 32768 3069529 2029584384 (ep385 rfl rfl) rfl)) rfl)

noncomputable def ep387 := @ep378 5968489095 8589934592 288484878191 266021684379648 Bool.true 281799621 2147483648 17828094737 16626355273728 Bool.false 14558423687 14558423687 8589934592 288484878191 266021684379648 Bool.true 281799621 281799621 2147483648 17828094737 16626355273728 (ep379 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz20 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz31)) (ep380 ep386) rfl rfl

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz254 qz351 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep388 := @Enclosure.Complex.IsNear.of_eq qz138 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz146)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz146)))) Bool.false 4882021275 8589934592 234287579701 266021684379648 Bool.false 1745595225 17179869184 465293715131 532043368759296 (BSN.cpow_neg_s_mk qz143 45593 1000 3 qz144 rfl)

noncomputable def ep389 := nat_lit 308140322001872111587472245023610708164829343752914341352174417579830625

noncomputable def ep390 := nat_lit 384176561753723192970134606055932232872282766425839952058608750390625

noncomputable def ep391 := nat_lit 806412176523968549940475661890127964435616966302467153142838108065590625

noncomputable def ep392 := BSN.sin_dyadic_bound_f 374167755 268435456 3 2 131072 61999 ep389 ep64 ep390 ep391 ep66 ep390 129026 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 374167755) qz274 0 2 ep389 ep64 ep390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 374167755) qz275 0 2 ep391 ep66 ep390 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz356 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6565209) qz57)

noncomputable def ep393 := @Enclosure.Real.IsNear.cos_image qz146 qz356 Bool.false 6565209 131072 97 65536 Bool.false 129026 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 1641302407 32768000 45593 30969000 6565209 131072 97 65536 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz35 45593 1000 0 1 71998 65536 1 30969 1641302407 32768000 45593 30969000 qz145 qz279 rfl) rfl) (Enclosure.sfrac_false_div 6565209 131072) (BSN.cos_reduce3 qz356 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 26329715083500939378688) qz336) 226375608064910080 72057594037927936 Bool.false 129026 131072 7 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q3 6565209 131072 226375608064910080 72057594037927936 7 26329715083500939378688 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 129026 131072 26329715083500939378688 18889465931478580854784 374167755 268435456 61999 61938 (ep392 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep394 := nat_lit 171359812917375050078804640393586363306181761092252785174345169211190625

noncomputable def ep395 := nat_lit 513311085628617703850473651968647225452800717743906675618918290132790625

noncomputable def ep396 := BSN.cos_dyadic_bound_f 374167755 268435456 3 2 131072 61999 ep394 ep57 ep390 ep395 ep60 ep390 23067 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 374167755) qz269 0 2 ep394 ep57 ep390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 374167755) qz270 0 2 ep395 ep60 ep390 rfl rfl rfl rfl) rfl rfl

noncomputable def ep397 := @Enclosure.Real.IsNear.sin_image qz146 qz356 Bool.false 6565209 131072 97 65536 Bool.true 23067 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 1641302407 32768000 45593 30969000 6565209 131072 97 65536 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz35 45593 1000 0 1 71998 65536 1 30969 1641302407 32768000 45593 30969000 qz145 qz279 rfl) rfl) (Enclosure.sfrac_false_div 6565209 131072) (BSN.sin_reduce3 qz356 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 26329715083500939378688) qz336) 226375608064910080 72057594037927936 Bool.false 23067 131072 7 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q3 6565209 131072 226375608064910080 72057594037927936 7 26329715083500939378688 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 23067 131072 26329715083500939378688 18889465931478580854784 374167755 268435456 61999 61938 (ep396 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep398 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz146)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz146))) Bool.false 4882021275 8589934592 234287579701 266021684379648 Bool.false 1745595225 17179869184 465293715131 532043368759296 (@Enclosure.Real.IsNear.mulLit_ff qz32 (Real.cos qz146) 75675 131072 1 131072 64513 65536 3069529 2029584384 4882021275 8589934592 234287579701 266021684379648 qz280 (@Enclosure.Real.IsNear.recentre' (Real.cos qz146) Bool.false 129026 131072 3069529 2029584384 64513 65536 3069529 2029584384 (ep393 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz32 (@Neg.neg Real Real.instNeg (Real.sin qz146)) 75675 131072 1 131072 23067 131072 3069529 2029584384 1745595225 17179869184 465293715131 532043368759296 qz280 (@Enclosure.Real.IsNear.neg (Real.sin qz146) Bool.true 23067 131072 3069529 2029584384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz146) Bool.true 23067 131072 3069529 2029584384 23067 131072 3069529 2029584384 (ep397 rfl rfl) rfl)) rfl)

noncomputable def ep399 := @ep376 4882021275 8589934592 234287579701 266021684379648 Bool.false 1745595225 17179869184 465293715131 532043368759296 Bool.false 166992150662955925504 9720222481 4294967296 43564371491 22168473698304 Bool.true 1092643423166398464 508801743 17179869184 345264248905 177347789586432 (ep377 (BSN.head_sum_c_succ qz141 2 3 rfl rfl) (ep387 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep388 ep398) rfl rfl

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz254 qz351 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep400 := @Enclosure.Complex.IsNear.of_eq qz136 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz147)))) Bool.false 7998088005 17179869184 406108854755 532043368759296 Bool.true 783208785 4294967296 100952436791 133010842189824 (BSN.cpow_neg_s_mk qz143 45593 1000 4 qz144 rfl)

noncomputable def ep401 := nat_lit 100864826653553042772984189904561

noncomputable def ep402 := BSN.cos_dyadic_bound_f 100215509 268435456 2 1 131072 61999 ep401 ep94 ep401 ep401 ep95 ep401 122043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 100215509) qz269 0 1 ep401 ep94 ep401 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 100215509) qz270 0 1 ep401 ep95 ep401 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4142215) qz27)

noncomputable def ep403 := @Enclosure.Real.IsNear.cos_image qz147 qz357 Bool.false 4142215 65536 97 65536 Bool.false 122043 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 1035553809 16384000 45593 30969000 4142215 65536 97 65536 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz38 45593 1000 0 1 90852 65536 1 30969 1035553809 16384000 45593 30969000 qz145 qz283 rfl) rfl) (Enclosure.sfrac_false_div 4142215 65536) (BSN.cos_reduce0 qz357 (@HDiv.hDiv Real Real Real qz2 qz355 qz30) 226375608064910080 72057594037927936 Bool.false 122043 131072 10 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 4142215 65536 226375608064910080 72057594037927936 10 3526019769953450721280 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 122043 131072 3526019769953450721280 9444732965739290427392 100215509 268435456 61999 61938 (ep402 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep404 := BSN.sin_dyadic_bound_f 100215509 268435456 2 1 131072 61999 ep401 ep75 ep401 ep401 ep76 ep401 47804 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 100215509) qz274 0 1 ep401 ep75 ep401 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 100215509) qz275 0 1 ep401 ep76 ep401 rfl rfl rfl rfl) rfl rfl

noncomputable def ep405 := @Enclosure.Real.IsNear.sin_image qz147 qz357 Bool.false 4142215 65536 97 65536 Bool.false 47804 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 1035553809 16384000 45593 30969000 4142215 65536 97 65536 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz38 45593 1000 0 1 90852 65536 1 30969 1035553809 16384000 45593 30969000 qz145 qz283 rfl) rfl) (Enclosure.sfrac_false_div 4142215 65536) (BSN.sin_reduce0 qz357 (@HDiv.hDiv Real Real Real qz2 qz355 qz30) 226375608064910080 72057594037927936 Bool.false 47804 131072 10 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 4142215 65536 226375608064910080 72057594037927936 10 3526019769953450721280 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 47804 131072 3526019769953450721280 9444732965739290427392 100215509 268435456 61999 61938 (ep404 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep406 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz147))) Bool.false 7998088005 17179869184 406108854755 532043368759296 Bool.true 783208785 4294967296 100952436791 133010842189824 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz147) 65535 131072 1 131072 122043 131072 3069529 2029584384 7998088005 17179869184 406108854755 532043368759296 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz147) Bool.false 122043 131072 3069529 2029584384 122043 131072 3069529 2029584384 (ep403 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz147)) 65535 131072 1 131072 11951 32768 3069529 2029584384 783208785 4294967296 100952436791 133010842189824 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz147) Bool.false 11951 32768 3069529 2029584384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz147) Bool.false 47804 131072 3069529 2029584384 11951 32768 3069529 2029584384 (ep405 rfl rfl) rfl)) rfl)

noncomputable def ep407 := @ep374 7998088005 17179869184 406108854755 532043368759296 Bool.true 783208785 4294967296 100952436791 133010842189824 Bool.false 201343677074960809984 46878977929 17179869184 1451653770539 532043368759296 Bool.true 15640711316392378368 3641636883 17179869184 1439602493879 532043368759296 (ep375 (BSN.head_sum_c_succ qz141 3 4 rfl rfl) (ep399 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep400 ep406) rfl rfl

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz254 qz351 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep408 := @Enclosure.Complex.IsNear.of_eq qz134 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz148)))) Bool.true 416356551 2147483648 90404771075 133010842189824 Bool.false 6923429721 17179869184 363517143341 532043368759296 (BSN.cpow_neg_s_mk qz143 45593 1000 5 qz144 rfl)

noncomputable def ep409 := nat_lit 71945091587556131876572711151977323976755748215687126489993756338961121

noncomputable def ep410 := nat_lit 67896072823075474655928167747242296866316649210041114862727911062241

noncomputable def ep411 := nat_lit 215699482617022244680406277120437487336534611348641297240255813194758881

noncomputable def ep412 := BSN.cos_dyadic_bound_f 301287131 268435456 3 2 131072 61999 ep409 ep57 ep410 ep411 ep60 ep410 56824 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 301287131) qz269 0 2 ep409 ep57 ep410 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 301287131) qz270 0 2 ep411 ep60 ep410 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4808967) qz27)

noncomputable def ep413 := @Enclosure.Real.IsNear.cos_image qz148 qz358 Bool.false 4808967 65536 97 65536 Bool.true 56824 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 1202241817 16384000 45593 30969000 4808967 65536 97 65536 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz41 45593 1000 0 1 105476 65536 1 30969 1202241817 16384000 45593 30969000 qz145 qz288 rfl) rfl) (Enclosure.sfrac_false_div 4808967 65536) (BSN.cos_reduce2 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10600598549054823071744) qz30) 226375608064910080 72057594037927936 Bool.false 56824 131072 11 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q2 4808967 65536 226375608064910080 72057594037927936 11 10600598549054823071744 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 56824 131072 10600598549054823071744 9444732965739290427392 301287131 268435456 61999 61938 (ep412 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep414 := nat_lit 129446847999342576998106137539361389320667293468868794790098579081280225

noncomputable def ep415 := nat_lit 338917532070850341369406476521974770216345065462602015026194719071156961

noncomputable def ep416 := BSN.sin_dyadic_bound_f 301287131 268435456 3 2 131072 61999 ep414 ep64 ep410 ep415 ep66 ep410 118113 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 301287131) qz274 0 2 ep414 ep64 ep410 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 301287131) qz275 0 2 ep415 ep66 ep410 rfl rfl rfl rfl) rfl rfl

noncomputable def ep417 := @Enclosure.Real.IsNear.sin_image qz148 qz358 Bool.false 4808967 65536 97 65536 Bool.true 118113 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 1202241817 16384000 45593 30969000 4808967 65536 97 65536 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz41 45593 1000 0 1 105476 65536 1 30969 1202241817 16384000 45593 30969000 qz145 qz288 rfl) rfl) (Enclosure.sfrac_false_div 4808967 65536) (BSN.sin_reduce2 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10600598549054823071744) qz30) 226375608064910080 72057594037927936 Bool.false 118113 131072 11 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q2 4808967 65536 226375608064910080 72057594037927936 11 10600598549054823071744 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 118113 131072 10600598549054823071744 9444732965739290427392 301287131 268435456 61999 61938 (ep416 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep418 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz148))) Bool.true 416356551 2147483648 90404771075 133010842189824 Bool.false 6923429721 17179869184 363517143341 532043368759296 (@Enclosure.Real.IsNear.mulLit_ft qz39 (Real.cos qz148) 58617 131072 1 131072 7103 16384 3069529 2029584384 416356551 2147483648 90404771075 133010842189824 qz289 (@Enclosure.Real.IsNear.recentre' (Real.cos qz148) Bool.true 56824 131072 3069529 2029584384 7103 16384 3069529 2029584384 (ep413 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz39 (@Neg.neg Real Real.instNeg (Real.sin qz148)) 58617 131072 1 131072 118113 131072 3069529 2029584384 6923429721 17179869184 363517143341 532043368759296 qz289 (@Enclosure.Real.IsNear.neg (Real.sin qz148) Bool.true 118113 131072 3069529 2029584384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz148) Bool.true 118113 131072 3069529 2029584384 118113 131072 3069529 2029584384 (ep417 rfl rfl) rfl)) rfl)

noncomputable def ep419 := @ep372 416356551 2147483648 90404771075 133010842189824 Bool.false 6923429721 17179869184 363517143341 532043368759296 Bool.false 93518887457398980608 43548125521 17179869184 1813272854839 532043368759296 Bool.false 56380771645828104192 1640896419 8589934592 450779909305 133010842189824 (ep373 (BSN.head_sum_c_succ qz141 4 5 rfl rfl) (ep407 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep408 ep418) rfl rfl

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz254 qz351 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep420 := @Enclosure.Complex.IsNear.of_eq qz132 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.false 3506644075 8589934592 168315587833 266021684379648 Bool.true 34647725 8589934592 164296740703 266021684379648 (BSN.cpow_neg_s_mk qz143 45593 1000 6 qz144 rfl)

noncomputable def ep421 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz44 45593 1000 0 1 4034664351997175 2251799813685248 500000000030969 15484500000000000000 7358098072024287991 90071992547409920 22796500001411969617 15484500000000000000000 qz145 (BSN.isNear_log_sfrac 6 1 4034664351997175 2251799813685248 500000000030969 15484500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz291) Bool.false 4230652207559789772800 2361183241434822606848 1000000000061938 30969000000000000000 4034664351997175 2251799813685248 500000000030969 15484500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 26572 65536 24973259072661432 36028797018963968 30969 1000000000000000 rfl rfl rfl rfl (ep114 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep422 := BSN.cos_dyadic_bound_f 2652898 268435456 1 0 131072 61999 0 1 1 0 1 1 131065 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 2652898) qz269 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 2652898) qz270 0 0 rfl) rfl rfl

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10707441) qz57)

noncomputable def ep423 := @Enclosure.Real.IsNear.cos_image qz149 qz359 Bool.false 10707441 131072 97 65536 Bool.false 131065 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 7358098072024287991 90071992547409920 22796500001411969617 15484500000000000000000 10707441 131072 97 65536 (ep421 rfl) rfl) (Enclosure.sfrac_false_div 10707441 131072) (BSN.cos_reduce0 qz359 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 186681111367785644032) qz336) 226375608064910080 72057594037927936 Bool.false 131065 131072 13 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 10707441 131072 226375608064910080 72057594037927936 13 186681111367785644032 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 131065 131072 186681111367785644032 18889465931478580854784 2652898 268435456 61999 61938 (ep422 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep424 := BSN.sin_dyadic_bound_f 2652898 268435456 1 0 131072 61999 0 1 1 0 1 1 1295 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2652898) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2652898) qz275 0 0 rfl) rfl rfl

noncomputable def ep425 := @Enclosure.Real.IsNear.sin_image qz149 qz359 Bool.false 10707441 131072 97 65536 Bool.false 1295 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 7358098072024287991 90071992547409920 22796500001411969617 15484500000000000000000 10707441 131072 97 65536 (ep421 rfl) rfl) (Enclosure.sfrac_false_div 10707441 131072) (BSN.sin_reduce0 qz359 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 186681111367785644032) qz336) 226375608064910080 72057594037927936 Bool.false 1295 131072 13 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 10707441 131072 226375608064910080 72057594037927936 13 186681111367785644032 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1295 131072 186681111367785644032 18889465931478580854784 2652898 268435456 61999 61938 (ep424 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep426 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.false 3506644075 8589934592 168315587833 266021684379648 Bool.true 34647725 8589934592 164296740703 266021684379648 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz149) 26755 65536 1 65536 131065 131072 3069529 2029584384 3506644075 8589934592 168315587833 266021684379648 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.false 131065 131072 3069529 2029584384 131065 131072 3069529 2029584384 (ep423 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 26755 65536 1 65536 1295 131072 3069529 2029584384 34647725 8589934592 164296740703 266021684379648 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.false 1295 131072 3069529 2029584384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.false 1295 131072 3069529 2029584384 1295 131072 3069529 2029584384 (ep425 rfl rfl) rfl)) rfl)

noncomputable def ep427 := @ep370 3506644075 8589934592 168315587833 266021684379648 Bool.true 34647725 8589934592 164296740703 266021684379648 Bool.false 434319236312944607232 50561413671 17179869184 716634676835 177347789586432 Bool.false 13797571219945422848 803124347 4294967296 355285519771 88673894793216 (ep371 (BSN.head_sum_c_succ qz141 5 6 rfl rfl) (ep419 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep420 ep426) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz254 qz351 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep428 := @Enclosure.Complex.IsNear.of_eq qz130 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.false 4730719631 17179869184 102366157405 177347789586432 Bool.true 4447939603 17179869184 102307233721 177347789586432 (BSN.cpow_neg_s_mk qz143 45593 1000 7 qz144 rfl)

noncomputable def ep429 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz47 45593 1000 0 1 4381766428990711 2251799813685248 500000000030969 15484500000000000000 199777876796973486623 2251799813685248000 22796500001411969617 15484500000000000000000 qz145 (BSN.isNear_log_sfrac 7 1 4381766428990711 2251799813685248 500000000030969 15484500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz295) Bool.false 4594615115045363777536 2361183241434822606848 1000000000061938 30969000000000000000 4381766428990711 2251799813685248 500000000030969 15484500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 36674 65536 24973259072661432 36028797018963968 30969 1000000000000000 rfl rfl rfl rfl (ep125 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep430 := nat_lit 1683536681243603074667419446557761

noncomputable def ep431 := BSN.cos_dyadic_bound_f 202560913 268435456 2 1 131072 61999 ep430 ep94 ep430 ep430 ep95 ep430 95491 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 202560913) qz269 0 1 ep430 ep94 ep430 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 202560913) qz270 0 1 ep430 ep95 ep430 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz360 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5814301) qz27)

noncomputable def ep432 := @Enclosure.Real.IsNear.cos_image qz150 qz360 Bool.false 5814301 65536 97 65536 Bool.false 95491 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 199777876796973486623 2251799813685248000 22796500001411969617 15484500000000000000000 5814301 65536 97 65536 (ep429 rfl) rfl) (Enclosure.sfrac_false_div 5814301 65536) (BSN.cos_reduce0 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7126978536687840264192) qz30) 226375608064910080 72057594037927936 Bool.false 95491 131072 14 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 5814301 65536 226375608064910080 72057594037927936 14 7126978536687840264192 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 95491 131072 7126978536687840264192 9444732965739290427392 202560913 268435456 61999 61938 (ep431 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep433 := BSN.sin_dyadic_bound_f 202560913 268435456 2 1 131072 61999 ep430 ep75 ep430 ep430 ep76 ep430 89783 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 202560913) qz274 0 1 ep430 ep75 ep430 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 202560913) qz275 0 1 ep430 ep76 ep430 rfl rfl rfl rfl) rfl rfl

noncomputable def ep434 := @Enclosure.Real.IsNear.sin_image qz150 qz360 Bool.false 5814301 65536 97 65536 Bool.false 89783 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 199777876796973486623 2251799813685248000 22796500001411969617 15484500000000000000000 5814301 65536 97 65536 (ep429 rfl) rfl) (Enclosure.sfrac_false_div 5814301 65536) (BSN.sin_reduce0 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7126978536687840264192) qz30) 226375608064910080 72057594037927936 Bool.false 89783 131072 14 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 5814301 65536 226375608064910080 72057594037927936 14 7126978536687840264192 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 89783 131072 7126978536687840264192 9444732965739290427392 202560913 268435456 61999 61938 (ep433 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep435 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.false 4730719631 17179869184 102366157405 177347789586432 Bool.true 4447939603 17179869184 102307233721 177347789586432 (@Enclosure.Real.IsNear.mulLit_ff qz45 (Real.cos qz150) 49541 131072 1 131072 95491 131072 3069529 2029584384 4730719631 17179869184 102366157405 177347789586432 qz297 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.false 95491 131072 3069529 2029584384 95491 131072 3069529 2029584384 (ep432 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 49541 131072 1 131072 89783 131072 3069529 2029584384 4447939603 17179869184 102307233721 177347789586432 qz297 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.false 89783 131072 3069529 2029584384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.false 89783 131072 3069529 2029584384 89783 131072 3069529 2029584384 (ep434 rfl rfl) rfl)) rfl)

noncomputable def ep436 := @ep368 4730719631 17179869184 102366157405 177347789586432 Bool.true 4447939603 17179869184 102307233721 177347789586432 Bool.false 949911617032649965568 27646066651 8589934592 4265629345 923686404096 Bool.true 5306183909522800640 1235442215 17179869184 270959424421 59115929862144 (ep369 (BSN.head_sum_c_succ qz141 6 7 rfl rfl) (ep427 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep428 ep435) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz254 qz351 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep437 := @Enclosure.Complex.IsNear.of_eq qz128 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.false 5145565617 17179869184 287934930689 532043368759296 Bool.true 3227418945 17179869184 286653061841 532043368759296 (BSN.cpow_neg_s_mk qz143 45593 1000 8 qz144 rfl)

noncomputable def ep438 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz50 45593 1000 0 1 9364972152248037 4503599627370496 1000000000092907 30969000000000000000 426977175337444750941 4503599627370496000 45593000004235908851 30969000000000000000000 qz145 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000092907 30969000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz299) Bool.false 4909942519757818822656 2361183241434822606848 1000000000092907 30969000000000000000 9364972152248037 4503599627370496 1000000000092907 30969000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 65536 24973259072661432 36028797018963968 30969 1000000000000000 rfl rfl rfl rfl (ep136 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep439 := nat_lit 511352081818620923439037846388736

noncomputable def ep440 := BSN.cos_dyadic_bound_f 150376512 268435456 2 1 131072 61999 ep439 ep94 ep439 ep439 ep95 ep439 111037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 150376512) qz269 0 1 ep439 ep94 ep439 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 150376512) qz270 0 1 ep439 ep95 ep439 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz361 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12426671) qz57)

noncomputable def ep441 := @Enclosure.Real.IsNear.cos_image qz151 qz361 Bool.false 12426671 131072 97 65536 Bool.false 111037 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 426977175337444750941 4503599627370496000 45593000004235908851 30969000000000000000000 12426671 131072 97 65536 (ep438 rfl) rfl) (Enclosure.sfrac_false_div 12426671 131072) (BSN.cos_reduce0 qz361 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10581806304750324416512) qz336) 226375608064910080 72057594037927936 Bool.false 111037 131072 15 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 12426671 131072 226375608064910080 72057594037927936 15 10581806304750324416512 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 111037 131072 10581806304750324416512 18889465931478580854784 150376512 268435456 61999 61938 (ep440 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep442 := BSN.sin_dyadic_bound_f 150376512 268435456 2 1 131072 61999 ep439 ep75 ep439 ep439 ep76 ep439 69645 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 150376512) qz274 0 1 ep439 ep75 ep439 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 150376512) qz275 0 1 ep439 ep76 ep439 rfl rfl rfl rfl) rfl rfl

noncomputable def ep443 := @Enclosure.Real.IsNear.sin_image qz151 qz361 Bool.false 12426671 131072 97 65536 Bool.false 69645 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 426977175337444750941 4503599627370496000 45593000004235908851 30969000000000000000000 12426671 131072 97 65536 (ep438 rfl) rfl) (Enclosure.sfrac_false_div 12426671 131072) (BSN.sin_reduce0 qz361 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10581806304750324416512) qz336) 226375608064910080 72057594037927936 Bool.false 69645 131072 15 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q0 12426671 131072 226375608064910080 72057594037927936 15 10581806304750324416512 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 69645 131072 10581806304750324416512 18889465931478580854784 150376512 268435456 61999 61938 (ep442 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep444 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.false 5145565617 17179869184 287934930689 532043368759296 Bool.true 3227418945 17179869184 286653061841 532043368759296 (@Enclosure.Real.IsNear.mulLit_ff qz48 (Real.cos qz151) 46341 131072 1 131072 111037 131072 3069529 2029584384 5145565617 17179869184 287934930689 532043368759296 qz301 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.false 111037 131072 3069529 2029584384 111037 131072 3069529 2029584384 (ep441 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 46341 131072 1 131072 69645 131072 3069529 2029584384 3227418945 17179869184 286653061841 532043368759296 qz301 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.false 69645 131072 3069529 2029584384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.false 69645 131072 3069529 2029584384 69645 131072 3069529 2029584384 (ep443 rfl rfl) rfl)) rfl)

noncomputable def ep445 := @ep366 5145565617 17179869184 287934930689 532043368759296 Bool.true 3227418945 17179869184 286653061841 532043368759296 Bool.false 519155880605199106048 60437698919 17179869184 2744937433409 532043368759296 Bool.true 76671370915154493440 557857645 2147483648 1362643940815 266021684379648 (ep367 (BSN.head_sum_c_succ qz141 7 8 rfl rfl) (ep436 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep437 ep444) rfl rfl

theorem EMRow08.d10 : Enclosure.Complex.IsNear qz126 Bool.false 60437698919 17179869184 2744937433409 532043368759296 Bool.true 557857645 2147483648 1362643940815 266021684379648 := ep365 (BSN.head_sum_c_succ qz141 8 9 rfl rfl) (ep445 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow08.d11 : @Eq Nat (Nat.pow 10 1) 10 := @Eq.refl Nat 10

noncomputable def ep446 := nat_lit 210130674456698629577212433753

noncomputable def ep447 := nat_lit 56177135662501353618407424000

noncomputable def ep448 := nat_lit 104149631991461085848765243517125683

noncomputable def ep449 := nat_lit 10775661780629568977887156536921292800

noncomputable abbrev qz437 := (@HAdd.hAdd Complex Complex Complex qz443 (@HAdd.hAdd Complex Complex Complex qz443 qz446 (@HMul.hMul Complex Complex Complex qz445 Complex.I (@HDiv.hDiv Complex Complex Complex qz447 (↑qz450) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz362 := qz437

noncomputable abbrev qz152 := (Complex.Stirling.logGammaStirling 1 qz362)

noncomputable abbrev qz438 := (@HAdd.hAdd Complex Complex Complex qz443 qz446 (@HMul.hMul Complex Complex Complex qz445 Complex.I (@HDiv.hDiv Complex Complex Complex qz447 (↑qz450) (2 : Complex))))

noncomputable abbrev qz363 := qz438

noncomputable abbrev qz153 := qz363

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz254 (@HDiv.hDiv Real Real Real qz257 qz351 (2 : Real)) (Real.log Real.pi))

noncomputable def ep450 := Complex.re (@HMul.hMul Complex Complex Complex qz51 (Complex.exp (@HMul.hMul Complex Complex Complex qz51 Complex.I ↑(@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154))) (zetaApproximant qz141 1 10))

noncomputable def ep451 := @Enclosure.Real.IsNear.of_eq ep450 (@HSub.hSub Real Real Real qz52 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) (Complex.re (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) (Complex.im (zetaApproximant qz141 1 10))))

noncomputable def ep452 := nat_lit 210130684058077105472061009323

noncomputable def ep453 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) (Complex.re (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) (Complex.im (zetaApproximant qz141 1 10))) ep452

noncomputable def ep454 := nat_lit 20807445600354736294743342839524051

noncomputable def ep455 := nat_lit 2155132356125913795577431307384258560

noncomputable def ep456 := nat_lit 1872571188750045120613580800

noncomputable def ep457 := nat_lit 28100997421851093762132329876357

noncomputable def ep458 := nat_lit 2693915445157392244471789134230323200

noncomputable def ep459 := nat_lit 393484646860228894412860230563983068198650602232112742400

noncomputable def ep460 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) (Complex.re (zetaApproximant qz141 1 10)) 131071 131072 992807

noncomputable def ep461 := nat_lit 1603182123109437674787413

noncomputable def ep462 := nat_lit 79500414261109987114259717

noncomputable def ep463 := nat_lit 13273236956268344270389248000

noncomputable def ep464 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) Bool.true 131071 131072 992807

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1441209) qz27)

noncomputable def ep465 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154) qz364 Bool.false 1441209 65536 31

noncomputable def ep466 := nat_lit 507396096000000000000000000

noncomputable def ep467 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154) Bool.false 1188469738560294483973 54043195528445952000 477101231600701190250463 ep466

noncomputable def ep468 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154 2598771708846251964421 54043195528445952000 124108827350701190250463 ep466 3420432453 131072000

noncomputable def ep469 := nat_lit 155775105572574918603309056000

noncomputable def ep470 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 160650298056860882207 4503599627370496000 52463148915665291589683 ep164 Bool.false 2598771708846251964421 54043195528445952000

noncomputable def ep471 := nat_lit 42283008000000000000000000

noncomputable def ep472 := @Enclosure.Complex.IsNear.subLitP qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 132481302004195363207 4503599627370496000 16805049638174550124561 ep471 Bool.false 2765000892825590268421 54043195528445952000 35908275783397931384821

noncomputable def ep473 := nat_lit 169132032000000000000000000

noncomputable def ep474 := nat_lit 723504622465837786727210866203164672

noncomputable def ep475 := nat_lit 731489206223810466897195864923570176

noncomputable abbrev qz365 := (@HSub.hSub Complex Complex Complex qz427 qz437 qz430)

noncomputable abbrev qz366 := (Complex.log qz437)

noncomputable abbrev qz155 := (@HSub.hSub Complex Complex Complex qz303 (@HMul.hMul Complex Complex Complex qz302 qz365 qz366) qz362)

noncomputable abbrev qz156 := qz362

noncomputable def ep476 := @Enclosure.Complex.IsNear.of_eq qz152 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz155 qz59) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz156 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k)))))) Bool.true 132481302004195363207

noncomputable def ep477 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz155 qz59) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz156 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) Bool.true 132482911220228131207 4503599627370496000

noncomputable def ep478 := nat_lit 142250714859879584942226669568

noncomputable def ep479 := nat_lit 296889710202417780869101413990400

noncomputable def ep480 := @ep477 16411065918764581039 41292000000000000000000 Bool.false 184346436230431705259 3602879701896396800 8765500004272039351 41292000000000000000000 Bool.false 383667 1073741824 3 1073741824 Bool.true 5830843177 1610612736000 45593 1610612736000 Bool.true ep478 132481302004195363207 4503599627370496000 16805049638174550124561 ep471 Bool.false ep479

noncomputable def ep481 := @Enclosure.Complex.IsNear.addLitP qz155 qz59 Bool.true 136621404267700259207 4503599627370496000 15781000000795831039 41292000000000000000000

noncomputable def ep482 := nat_lit 8682400069728870806781952

noncomputable def ep483 := @ep481 Bool.false 184346436230431705259 3602879701896396800 8765500004272039351 41292000000000000000000 Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 Bool.true ep482 132482911220228131207 4503599627370496000 16411065918764581039 41292000000000000000000 Bool.false 184346436230431705259 184346436230431705259 3602879701896396800

noncomputable abbrev qz157 := (@HMul.hMul Complex Complex Complex qz302 qz365 qz366)

noncomputable def ep484 := @Enclosure.Complex.IsNear.subLitP qz157 qz156 Bool.true 126488305106116643207 4503599627370496000 15781000000795831039 41292000000000000000000 Bool.false 1332397416773564574551

noncomputable def ep485 := nat_lit 3686928724608634105180000

noncomputable def ep486 := @ep484 18014398509481984000 8765500004272039351 41292000000000000000000 Bool.false 9000 4000 0 1 Bool.false 91186 4000 0 1 Bool.true 546485617070801036828000 136621404267700259207 4503599627370496000 15781000000795831039 41292000000000000000000 Bool.false ep485 184346436230431705259 3602879701896396800 8765500004272039351 41292000000000000000000

noncomputable abbrev qz158 := qz365

noncomputable abbrev qz159 := qz366

noncomputable def ep487 := @Enclosure.Complex.IsNear.mul qz158 qz159 Bool.true 126488305106116643207 4503599627370496000 15781000000795831039 41292000000000000000000 Bool.false 1332397416773564574551 18014398509481984000 8765500004272039351

noncomputable abbrev qz160 := (Complex.re qz365)

noncomputable abbrev qz161 := (Complex.re qz366)

noncomputable abbrev qz162 := (Complex.im qz365)

noncomputable abbrev qz163 := (Complex.im qz366)

noncomputable def ep488 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz160 qz161) (@HMul.hMul Real Real Real qz0 qz162 qz163) 197439364736360649 36028797018963968 3500000001951047 247752000000000000000 37792056424540431083 1125899906842624000

noncomputable def ep489 := nat_lit 1139305367485265041708266151261241344

noncomputable def ep490 := @Enclosure.Real.IsNear.mulLit_ff qz160 qz161 7000 4000 0 1 28205623533765807 9007199254740992 500000000278721 61938000000000000000

noncomputable def ep491 := @Enclosure.Complex.IsNear.re_isNear qz158 Bool.false 7000 4000 0 1 Bool.false 91186 4000 0 1

noncomputable abbrev qz367 := (Enclosure.sfrac Bool.false 91186 4000)

noncomputable abbrev qz164 := qz367

noncomputable def ep492 := @Enclosure.Complex.IsNear.of_eq qz158 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz164) Bool.false 7000 4000 0 1 Bool.false 91186 4000 0

noncomputable abbrev qz165 := (Complex.mk qz317 qz367)

noncomputable def ep493 := @Enclosure.Complex.IsNear.of_eq qz159 (Complex.log qz165) Bool.false 28205623533765807 9007199254740992 500000000278721 61938000000000000000 Bool.false 828900410688931 562949953421312 1000000000030969 61938000000000000000

noncomputable def ep494 := BSN.log_dyadic_bound 203886596 16587886596 1 0 1 131072 61938 0 1 3222 16791773192 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 203886596) (BSN.artanhQ 16587886596) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz368 := (Real.log (Enclosure.sfrac Bool.false 8395886596 16000000))

noncomputable def ep495 := @Enclosure.Real.IsNear.mulLit_ff qz77 qz368 1 2 0 1 28205623533765807 4503599627370496 500000000278721 30969000000000000000 28205623533765807 9007199254740992 500000000278721 61938000000000000000 qz319 (BSN.isNear_log_sfrac 8395886596 16000000 28205623533765807 4503599627370496 500000000278721 30969000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8395886596) qz320)) Bool.false 29575739902542014840832 4722366482869645213696 1000000000557442 61938000000000000000 28205623533765807 4503599627370496 500000000278721 30969000000000000000 (BSN.log_rat_reduce_isNear 8395886596 16000000 9 16791773192 16384000000 3222 131072 24973259072661432 36028797018963968 61938 1000000000000000 rfl rfl rfl rfl (ep494 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep496 := BSN.arctan_dyadic_bound_f 9000 91186 1 0 131072 61938 0 1 1 0 1 1 12894 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 91186) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 91186) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz369 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 91186)))

noncomputable def ep497 := @Enclosure.Real.IsNear.subLit_ff_p qz78 qz369 884279719003555 562949953421312 1 2000000000000000 12894 131072 1 61938 108645634629819564032 828900410688931 562949953421312 1000000000030969 61938000000000000000 qz79 (ep496 rfl) rfl rfl

noncomputable abbrev qz370 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 91186) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep498 := @Enclosure.Complex.IsNear.re_isNear qz159 Bool.false 28205623533765807 9007199254740992 500000000278721 61938000000000000000 Bool.false 828900410688931 562949953421312 1000000000030969 61938000000000000000 (ep493 (@congrArg Complex Complex qz156 qz165 Complex.log (BSN.w_shift_mk qz143 Bool.false 45593 1000 2 qz144 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz165) Bool.false 28205623533765807 9007199254740992 500000000278721 61938000000000000000 Bool.false 828900410688931 562949953421312 1000000000030969 61938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz165)) (@HMul.hMul Real Real Real qz0 qz77 qz368) Bool.false 28205623533765807 9007199254740992 500000000278721 61938000000000000000 (Enclosure.clog_re_eq 9000 91186 4000 8395886596 16000000 rfl rfl rfl) (ep495 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz165)) qz370 Bool.false 828900410688931 562949953421312 1000000000030969 61938000000000000000 (Enclosure.clog_im_eq 9000 91186 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz370 (@HSub.hSub Real Real Real qz52 qz78 qz369) Bool.false 828900410688931 562949953421312 1000000000030969 61938000000000000000 (BSN.arctan_recip 91186 9000 rfl rfl) ep497))))

noncomputable def ep499 := @Enclosure.Real.IsNear.mulLit_ff qz162 qz163 91186 4000 0 1 828900410688931 562949953421312 1000000000030969 61938000000000000000

noncomputable def ep500 := @Enclosure.Complex.IsNear.im_isNear qz158 Bool.false 7000 4000 0 1 Bool.false 91186 4000 0 1

noncomputable def ep501 := @Enclosure.Complex.IsNear.im_isNear qz159 Bool.false 28205623533765807 9007199254740992 500000000278721 61938000000000000000 Bool.false 828900410688931 562949953421312 1000000000030969 61938000000000000000 (ep493 (@congrArg Complex Complex qz156 qz165 Complex.log (BSN.w_shift_mk qz143 Bool.false 45593 1000 2 qz144 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz165) Bool.false 28205623533765807 9007199254740992 500000000278721 61938000000000000000 Bool.false 828900410688931 562949953421312 1000000000030969 61938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz165)) (@HMul.hMul Real Real Real qz0 qz77 qz368) Bool.false 28205623533765807 9007199254740992 500000000278721 61938000000000000000 (Enclosure.clog_re_eq 9000 91186 4000 8395886596 16000000 rfl rfl rfl) (ep495 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz165)) qz370 Bool.false 828900410688931 562949953421312 1000000000030969 61938000000000000000 (Enclosure.clog_im_eq 9000 91186 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz370 (@HSub.hSub Real Real Real qz52 qz78 qz369) Bool.false 828900410688931 562949953421312 1000000000030969 61938000000000000000 (BSN.arctan_recip 91186 9000 rfl rfl) ep497))))

noncomputable abbrev qz371 := (Enclosure.Real.IsNear.const Bool.false 91186 4000)

noncomputable abbrev qz166 := (@ep492 1 (BSN.w_sub_half_mk qz351 Bool.false 45593 1000 2 qz352 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz367 Bool.false 7000 4000 0 1 Bool.false 91186 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz371))

noncomputable def ep502 := @ep488 45593000001411969617 123876000000000000000000 ep489 126488305106116643207 4503599627370496000 15781000000795831039 41292000000000000000000 (@ep490 197439364736360649 36028797018963968 3500000001951047 247752000000000000000 (ep491 qz166) ep498 rfl) (@ep499 37792056424540431083 1125899906842624000 45593000001411969617 123876000000000000000000 (ep500 qz166) ep501 rfl) rfl

noncomputable def ep503 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz160 qz163) (@HMul.hMul Real Real Real qz0 qz162 qz161) 5802302874822517 2251799813685248 7000000000216783 247752000000000000000 1285978993774984438551 18014398509481984000

noncomputable def ep504 := nat_lit 3000292254845418437366617936544923648

noncomputable def ep505 := @Enclosure.Real.IsNear.mulLit_ff qz160 qz163 7000 4000 0 1 828900410688931 562949953421312 1000000000030969 61938000000000000000

noncomputable def ep506 := @Enclosure.Real.IsNear.mulLit_ff qz162 qz161 91186 4000 0 1 28205623533765807 9007199254740992 500000000278721 61938000000000000000

noncomputable def ep507 := @ep503 22796500012707726553 123876000000000000000000 ep504 1332397416773564574551 18014398509481984000 8765500004272039351 41292000000000000000000 (@ep505 5802302874822517 2251799813685248 7000000000216783 247752000000000000000 (ep491 qz166) ep501 rfl) (@ep506 1285978993774984438551 18014398509481984000 22796500012707726553 123876000000000000000000 (ep500 qz166) ep498 rfl) rfl

noncomputable def ep508 := @Enclosure.Complex.IsNear.of_eq qz156 qz165 Bool.false 9000 4000 0 1 Bool.false 91186 4000 0 1 (BSN.w_shift_mk qz143 Bool.false 45593 1000 2 qz144 rfl)

noncomputable abbrev qz372 := (ep508 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 91186 4000) Bool.false 9000 4000 0 1 Bool.false 91186 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 91186 4000)))

noncomputable abbrev qz167 := qz372

noncomputable def ep509 := ep486 (@ep487 41292000000000000000000 (ep502 rfl) (ep507 rfl)) qz167 rfl rfl rfl rfl rfl rfl

noncomputable def ep510 := @ep483 8765500004272039351 41292000000000000000000 (ep509 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz82 (↑qz3) Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 (@ep207 65536 1 65536 (ep209 rfl) (ep211 rfl) rfl rfl) (@ep212 1 0 1 (ep214 rfl) (ep216 rfl) rfl rfl))

noncomputable abbrev qz373 := (@HPow.hPow Complex Int Complex qz432 qz437 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz168 := qz373

noncomputable def ep511 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz156 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz156 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) qz168)) Bool.false 383667 1073741824 3 1073741824

noncomputable def ep512 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz156 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) qz168) Bool.false 0 1 0 1 Bool.false

noncomputable def ep513 := @ep512 0 1 0 1 Bool.false 383667 1073741824 3 1073741824 Bool.true 5830843177 1610612736000 45593 1610612736000 Bool.false 383667 383667 1073741824 3 1073741824 Bool.true 5830843177 5830843177 1610612736000 45593

noncomputable def ep514 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz156 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false

noncomputable def ep515 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) qz168 Bool.false 383667 1073741824 3 1073741824 Bool.true 5830843177 1610612736000 45593 1610612736000

noncomputable abbrev qz169 := (Complex.re qz373)

noncomputable abbrev qz170 := (Complex.im qz373)

noncomputable def ep516 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz169) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz170) 383667 1073741824 3 1073741824 0 1 0

noncomputable def ep517 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz169 1 12 0 1 1151001 268435456 9 268435456 383667

noncomputable def ep518 := @Enclosure.Complex.IsNear.re_isNear qz168 Bool.false 1151001 268435456 9 268435456 Bool.true 5830843177 134217728000 45593 134217728000

noncomputable abbrev qz374 := (@HPow.hPow Complex Nat Complex qz433 qz437 1)

noncomputable abbrev qz171 := (@Inv.inv Complex Complex.instInv qz374)

noncomputable def ep519 := @Enclosure.Complex.IsNear.of_eq qz168 qz171 Bool.false 1151001 268435456 9 268435456 Bool.true 5830843177 134217728000 45593

noncomputable def ep520 := @Enclosure.Complex.IsNear.of_parts qz171 Bool.false 1151001 268435456 9 268435456 Bool.true 5830843177 134217728000 45593

noncomputable abbrev qz172 := (Complex.re qz374)

noncomputable abbrev qz173 := qz374

noncomputable def ep521 := @Enclosure.Real.IsNear.mulLit_ff qz172 (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz173)) 9000 4000 0 1 127889 67108864 1 67108864

noncomputable def ep522 := @Enclosure.Complex.IsNear.re_isNear qz173 Bool.false 9000 4000 0 1 Bool.false 91186 4000 0 1

noncomputable def ep523 := @Enclosure.Complex.IsNear.of_eq qz173 qz156 Bool.false 9000 4000 0 1 Bool.false 91186 4000 0

noncomputable def ep524 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz173)) Bool.false 127889 67108864 1 67108864 127889 67108864 1

noncomputable abbrev qz174 := (Complex.im qz374)

noncomputable def ep525 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz173) (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 qz172 qz172) (@HMul.hMul Real Real Real qz0 qz174 qz174)) Bool.false 2098971649 4000000 0 1

noncomputable def ep526 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz172 qz172) (@HMul.hMul Real Real Real qz0 qz174 qz174) 81 16 0 1 2078721649 4000000

noncomputable def ep527 := @Enclosure.Real.IsNear.mulLit_ff qz172 qz172 9000 4000 0 1 9000 4000 0 1

noncomputable def ep528 := @Enclosure.Real.IsNear.mulLit_ff qz174 qz174 91186 4000 0 1 91186 4000 0 1

noncomputable def ep529 := @Enclosure.Complex.IsNear.im_isNear qz173 Bool.false 9000 4000 0 1 Bool.false 91186 4000 0 1

noncomputable abbrev qz175 := (ep522 (@ep523 1 (BSN.pow_one_c qz362) qz372))

noncomputable abbrev qz176 := (ep529 (@ep523 1 (BSN.pow_one_c qz362) qz372))

noncomputable def ep530 := @ep526 0 1 33583546384 2098971649 4000000 0 1 (@ep527 81 16 0 1 qz175 qz175 rfl) (@ep528 2078721649 4000000 0 1 qz176 qz176 rfl)

noncomputable def ep531 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz173) 2098971649 4000000 0 1 63944 63945 33554432 (ep525 (Enclosure.Complex.normSq_eq_mul_add_mul qz173) (ep530 rfl rfl)) rfl

noncomputable def ep532 := @Enclosure.Real.IsNear.of_eq (Complex.re qz171) (@HMul.hMul Real Real Real qz0 qz172 (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz173))) Bool.false 1151001 268435456 9 268435456 (Enclosure.Complex.inv_re_eq_mul qz173) (@ep521 1151001 268435456 9 268435456 qz175 (@ep524 67108864 (ep531 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep533 := @Enclosure.Real.IsNear.of_eq (Complex.im qz171) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz174) (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz173))) Bool.true 5830843177 134217728000 45593 134217728000 (Enclosure.Complex.inv_im_eq_mul qz173)

noncomputable def ep534 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz174) (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz173)) 91186 4000 0 1 127889 67108864 1

noncomputable def ep535 := @ep534 67108864 5830843177 134217728000 45593 134217728000 (@Enclosure.Real.IsNear.neg qz174 Bool.false 91186 4000 0 1 qz176) (@ep524 67108864 (ep531 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep536 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz170 0 1 0 1 5830843177 134217728000 45593 134217728000 0

noncomputable def ep537 := @Enclosure.Complex.IsNear.im_isNear qz168 Bool.false 1151001 268435456 9 268435456 Bool.true 5830843177 134217728000 45593 134217728000

noncomputable abbrev qz177 := (@ep519 134217728000 (BSN.zpow_one_sub_two_mul qz362 1 1 rfl rfl) (@ep520 134217728000 ep532 (ep533 ep535)))

noncomputable def ep538 := @ep516 1 383667 383667 1073741824 3 1073741824 (@ep517 1073741824 3 1073741824 ep226 (ep518 qz177) rfl) (@ep536 1 0 1 ep246 (ep537 qz177) rfl) rfl

noncomputable def ep539 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz170) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz169) 5830843177 1610612736000 45593 1610612736000 0 1 0

noncomputable def ep540 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz170 1 12 0 1 5830843177 134217728000 45593 134217728000 5830843177

noncomputable def ep541 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz169 0 1 0 1 1151001 268435456 9 268435456 0

noncomputable def ep542 := @ep539 1 5830843177 5830843177 1610612736000 45593 1610612736000 (@ep540 1610612736000 45593 1610612736000 ep226 (ep537 qz177) rfl) (@ep541 1 0 1 ep246 (ep518 qz177) rfl) rfl

noncomputable def ep543 := @ep513 1610612736000 (@ep514 0 1 0 1 (BSN.stirling_sum_base qz156) qz99) (ep515 (ep538 rfl) (ep542 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep544 := @ep480 2765000892825590268421 54043195528445952000 35908275783397931384821 ep473 (ep510 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep511 Bool.true 5830843177 1610612736000 45593 1610612736000 (BSN.stirling_sum_succ qz156 0 1 rfl) (ep543 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep545 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz143 2) Bool.false 28168996052665519 4503599627370496 500000000278721 30969000000000000000 Bool.false 865776999892387 281474976710656

noncomputable abbrev qz178 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz260 qz363 qz325))

noncomputable def ep546 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz143 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz143 1) qz178) Bool.false 28168996052665519 4503599627370496 500000000278721 30969000000000000000 Bool.false 865776999892387 281474976710656 1000000000030969 30969000000000000000

noncomputable def ep547 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz143 1) qz178 Bool.false 28162502062113967 9007199254740992 500000000278721 61938000000000000000 Bool.false 878107850999203 562949953421312 1000000000030969 61938000000000000000 Bool.false

noncomputable def ep548 := nat_lit 507447520504741616342759108509696

noncomputable def ep549 := nat_lit 974778243525325012172944703488

noncomputable abbrev qz179 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz260 qz363 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep550 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz143 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz143 0) qz179) Bool.false 28162502062113967 9007199254740992 500000000278721 61938000000000000000 Bool.false 878107850999203 562949953421312 1000000000030969 61938000000000000000

noncomputable def ep551 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz143 0) qz179 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz375 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz164))

noncomputable def ep552 := @Enclosure.Complex.IsNear.of_eq qz179 qz375 Bool.false 28162502062113967 9007199254740992 500000000278721 61938000000000000000 Bool.false 878107850999203 562949953421312 1000000000030969 61938000000000000000

noncomputable def ep553 := BSN.log_dyadic_bound 123886596 16507886596 1 0 1 131072 61938 0 1 1967 16631773192 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 123886596) (BSN.artanhQ 16507886596) 0 0 rfl) rfl rfl rfl

noncomputable def ep554 := @Enclosure.Real.IsNear.mulLit_ff qz77 (Real.log (Enclosure.sfrac Bool.false 8315886596 16000000)) 1 2 0 1 28162502062113967 4503599627370496 500000000278721 30969000000000000000 28162502062113967 9007199254740992 500000000278721 61938000000000000000 qz319 (BSN.isNear_log_sfrac 8315886596 16000000 28162502062113967 4503599627370496 500000000278721 30969000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8315886596) qz320)) Bool.false 29530523762283215060992 4722366482869645213696 1000000000557442 61938000000000000000 28162502062113967 4503599627370496 500000000278721 30969000000000000000 (BSN.log_rat_reduce_isNear 8315886596 16000000 9 16631773192 16384000000 1967 131072 24973259072661432 36028797018963968 61938 1000000000000000 rfl rfl rfl rfl (ep553 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep555 := BSN.arctan_dyadic_bound_f 1000 91186 1 0 131072 61938 0 1 1 0 1 1 1437 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 91186) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 91186) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz376 := (@Nat.cast Real Real.instNatCast 91186)

noncomputable def ep556 := @Enclosure.Real.IsNear.subLit_ff_p qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz376)) 884279719003555 562949953421312 1 2000000000000000 1437 131072 1 61938 115095352246167535616 878107850999203 562949953421312 1000000000030969 61938000000000000000 qz79 (ep555 rfl) rfl rfl

noncomputable abbrev qz180 := (@HAdd.hAdd Complex Complex Complex qz260 qz363 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz377 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz164)

noncomputable def ep557 := @ep551 28162502062113967 9007199254740992 500000000278721 61938000000000000000 Bool.false 878107850999203 562949953421312 1000000000030969 61938000000000000000 Bool.false 28162502062113967 28162502062113967 9007199254740992 500000000278721 61938000000000000000 Bool.false 878107850999203 878107850999203 562949953421312 1000000000030969 61938000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz143 0) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz143) qz99) (ep552 (@congrArg Complex Complex qz180 qz377 Complex.log (BSN.w_shift_mk qz143 Bool.false 45593 1000 0 qz144 rfl)) (@Enclosure.Complex.IsNear.of_parts qz375 Bool.false 28162502062113967 9007199254740992 500000000278721 61938000000000000000 Bool.false 878107850999203 562949953421312 1000000000030969 61938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz375) (@HMul.hMul Real Real Real qz0 qz77 (Real.log (Enclosure.sfrac Bool.false 8315886596 16000000))) Bool.false 28162502062113967 9007199254740992 500000000278721 61938000000000000000 (Enclosure.clog_re_eq 1000 91186 4000 8315886596 16000000 rfl rfl rfl) (ep554 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz375) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz376 qz330)) Bool.false 878107850999203 562949953421312 1000000000030969 61938000000000000000 (Enclosure.clog_im_eq 1000 91186 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz376 qz330)) (@HSub.hSub Real Real Real qz52 qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz376))) Bool.false 878107850999203 562949953421312 1000000000030969 61938000000000000000 (BSN.arctan_recip 91186 1000 rfl rfl) ep556)))) rfl rfl

noncomputable abbrev qz378 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz164))

noncomputable def ep558 := @Enclosure.Complex.IsNear.of_eq qz178 qz378 Bool.false 28175490043217071 9007199254740992 500000000278721 61938000000000000000 Bool.false 853446148785571 562949953421312 1000000000030969 61938000000000000000

noncomputable def ep559 := BSN.log_dyadic_bound 147886596 16531886596 1 0 1 131072 61938 0 1 2345 16679773192 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 147886596) (BSN.artanhQ 16531886596) 0 0 rfl) rfl rfl rfl

noncomputable def ep560 := @Enclosure.Real.IsNear.mulLit_ff qz77 (Real.log (Enclosure.sfrac Bool.false 8339886596 16000000)) 1 2 0 1 28175490043217071 4503599627370496 500000000278721 30969000000000000000 28175490043217071 9007199254740992 500000000278721 61938000000000000000 qz319 (BSN.isNear_log_sfrac 8339886596 16000000 28175490043217071 4503599627370496 500000000278721 30969000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8339886596) qz320)) Bool.false 29544142647556383440896 4722366482869645213696 1000000000557442 61938000000000000000 28175490043217071 4503599627370496 500000000278721 30969000000000000000 (BSN.log_rat_reduce_isNear 8339886596 16000000 9 16679773192 16384000000 2345 131072 24973259072661432 36028797018963968 61938 1000000000000000 rfl rfl rfl rfl (ep559 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep561 := BSN.arctan_dyadic_bound_f 5000 91186 1 0 131072 61938 0 1 1 0 1 1 7179 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 91186) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 91186) 0 0 rfl) rfl rfl rfl

noncomputable def ep562 := @Enclosure.Real.IsNear.subLit_ff_p qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz334 qz376)) 884279719003555 562949953421312 1 2000000000000000 7179 131072 1 61938 111862893613622362112 853446148785571 562949953421312 1000000000030969 61938000000000000000 qz79 (ep561 rfl) rfl rfl

noncomputable abbrev qz181 := (@HAdd.hAdd Complex Complex Complex qz260 qz363 qz325)

noncomputable abbrev qz379 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz164)

noncomputable def ep563 := @ep547 28175490043217071 9007199254740992 500000000278721 61938000000000000000 Bool.false 853446148785571 562949953421312 1000000000030969 61938000000000000000 Bool.false ep548 28168996052665519 4503599627370496 500000000278721 30969000000000000000 Bool.false ep549 865776999892387 281474976710656 1000000000030969 30969000000000000000 (ep550 (BSN.log_sum_c_succ qz143 0 1 rfl) (ep557 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep558 (@congrArg Complex Complex qz181 qz379 Complex.log (BSN.w_shift_mk qz143 Bool.false 45593 1000 1 qz144 rfl)) (@Enclosure.Complex.IsNear.of_parts qz378 Bool.false 28175490043217071 9007199254740992 500000000278721 61938000000000000000 Bool.false 853446148785571 562949953421312 1000000000030969 61938000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz378) (@HMul.hMul Real Real Real qz0 qz77 (Real.log (Enclosure.sfrac Bool.false 8339886596 16000000))) Bool.false 28175490043217071 9007199254740992 500000000278721 61938000000000000000 (Enclosure.clog_re_eq 5000 91186 4000 8339886596 16000000 rfl rfl rfl) (ep560 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz378) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz376 qz334)) Bool.false 853446148785571 562949953421312 1000000000030969 61938000000000000000 (Enclosure.clog_im_eq 5000 91186 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz376 qz334)) (@HSub.hSub Real Real Real qz52 qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz334 qz376))) Bool.false 853446148785571 562949953421312 1000000000030969 61938000000000000000 (BSN.arctan_recip 91186 5000 rfl rfl) ep562)))) rfl rfl

noncomputable def ep564 := @ep472 ep473 Bool.false 28168996052665519 4503599627370496 500000000278721 30969000000000000000 Bool.false 865776999892387 281474976710656 1000000000030969 30969000000000000000 Bool.true ep474 160650298056860882207 4503599627370496000 52463148915665291589683 ep164 Bool.false ep475 2598771708846251964421 54043195528445952000 124108827350701190250463 ep466 (@ep476 4503599627370496000 16805049638174550124561 ep471 Bool.false 2765000892825590268421 54043195528445952000 35908275783397931384821 ep473 (BSN.logGammaStirling_unfold 1 qz156) (ep544 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep545 1000000000030969 30969000000000000000 (BSN.log_sum_c_eq qz143 2) (ep546 (BSN.log_sum_c_succ qz143 1 2 rfl) (ep563 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz182 := (@HDiv.hDiv Real Real Real qz257 qz351 (2 : Real))

noncomputable def ep565 := @Enclosure.Real.IsNear.mulLit_ff qz182 (Real.log Real.pi) 45593 2000 0 1 75021 65536 1 32768 3420432453 131072000 45593 65536000 (@Enclosure.Real.IsNear.of_eq qz182 (Enclosure.sfrac Bool.false 45593 2000) Bool.false 45593 2000 0 1 (BSN.t_half_eq qz143 Bool.false 45593 1000 qz144) (Enclosure.Real.IsNear.const Bool.false 45593 2000)) EMRow08.d5 rfl

noncomputable def ep566 := @ep468 45593 65536000 ep469 1188469738560294483973 54043195528445952000 477101231600701190250463 ep466 (@ep470 124108827350701190250463 ep466 (ep564 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep565 rfl rfl

noncomputable def ep567 := nat_lit 497284049261305279478661945134151539676167164562272288713375726551695360

noncomputable def ep568 := nat_lit 999032748162700272532440617973666461683616587070757448135651713089536

noncomputable def ep569 := nat_lit 1300793123615917074383824000065106191547235766045931910761859657242771456

noncomputable def ep570 := BSN.sin_dyadic_bound_f 421645496 268435456 3 2 131072 61999 ep567 ep64 ep568 ep569 ep66 ep568 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 421645496) qz274 0 2 ep567 ep64 ep568 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 421645496) qz275 0 2 ep569 ep66 ep568 rfl rfl rfl rfl) rfl rfl

noncomputable def ep571 := @ep465 32768 Bool.true 131071 131072 1 30969 (@ep467 1441209 65536 31 32768 ep566 rfl) (Enclosure.sfrac_false_div 1441209 65536) (BSN.cos_reduce1 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14835332039770854391808) qz30) 226375608064910080 72057594037927936 Bool.false 131071 131072 3 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q1 1441209 65536 226375608064910080 72057594037927936 3 14835332039770854391808 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131071 131072 14835332039770854391808 9444732965739290427392 421645496 268435456 61999 61938 (ep570 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep572 := nat_lit 19743647228674991890613051

noncomputable def ep573 := nat_lit 3318309239067086067597312000

noncomputable abbrev qz183 := qz350

noncomputable abbrev qz439 := (@Nat.cast Complex Complex.instNatCast 10)

noncomputable abbrev qz380 := (@HPow.hPow Complex Complex Complex qz421 qz439 qz435)

noncomputable abbrev qz184 := qz380

noncomputable abbrev qz381 := qz439

noncomputable abbrev qz185 := (@HAdd.hAdd Complex Complex Complex qz260 (@HDiv.hDiv Complex Complex Complex qz310 qz381 (@HSub.hSub Complex Complex Complex qz303 qz349 (1 : Complex))) qz309)

noncomputable abbrev qz186 := qz381

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz141 1 10) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 10, @HPow.hPow Complex Complex Complex qz105 (@Nat.cast Complex Complex.instNatCast n) qz183) (@HMul.hMul Complex Complex Complex qz51 qz184 (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) Bool.false ep461 428597531604777172992000 ep462

noncomputable def ep575 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 10, @HPow.hPow Complex Complex Complex qz105 (@Nat.cast Complex Complex.instNatCast n) qz183) (@HMul.hMul Complex Complex Complex qz51 qz184 (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) Bool.false 32905693041 8589934592 1508487062881 266021684379648

noncomputable def ep576 := nat_lit 4233970182400884855803717

noncomputable def ep577 := nat_lit 13771229576573761284324445174890496

noncomputable def ep578 := nat_lit 85911680313513956181136113664

noncomputable def ep579 := @ep575 Bool.true 38804439 268435456 1497459311671 266021684379648 Bool.true 38657947041016595828587 428597531604777172992000 ep576 ep463 Bool.false 10006140103456293655481 71432921934129528832000 1064594501704608997739051 ep573 Bool.false ep577 ep461 428597531604777172992000 ep462 ep463 Bool.true ep578 320045949196494952519 71432921934129528832000

noncomputable def ep580 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 10, @HPow.hPow Complex Complex Complex qz105 (@Nat.cast Complex Complex.instNatCast n) qz183) (BSN.headSumC qz141 10) Bool.false 32905693041 8589934592 1508487062881 266021684379648 Bool.true 38804439 268435456 1497459311671

noncomputable abbrev qz187 := (@HPow.hPow Complex Complex Complex qz261 qz338 qz350)

noncomputable def ep581 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 10) (@HAdd.hAdd Complex Complex Complex qz5 qz126 qz187) Bool.false 32905693041 8589934592 1508487062881 266021684379648 Bool.true 38804439 268435456 1497459311671 266021684379648

noncomputable def ep582 := @Enclosure.Complex.IsNear.addLitP qz126 qz187 Bool.false 60437698919 17179869184 2744937433409 532043368759296 Bool.true 557857645 2147483648 1362643940815 266021684379648 Bool.false

noncomputable abbrev qz188 := (@HMul.hMul Real Real Real qz254 qz351 qz343)

noncomputable def ep583 := @Enclosure.Complex.IsNear.of_eq qz187 (Complex.mk (@HMul.hMul Real Real Real qz0 qz114 (Real.cos qz188)) (@HMul.hMul Real Real Real qz0 qz114 (@Neg.neg Real Real.instNeg (Real.sin qz188)))) Bool.false 5373687163 17179869184 90678897451 177347789586432 Bool.false 247422133 2147483648 5617307119 11084236849152 (BSN.cpow_neg_s_mk qz143 45593 1000 9 qz144 rfl)

noncomputable def ep584 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz117 45593 1000 0 1 9895417793173221 4503599627370496 1000000000092907 30969000000000000000 451161783444146665053 4503599627370496000 45593000004235908851 30969000000000000000000 qz145 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000092907 30969000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz344 Bool.false 5188048803947201691648 2361183241434822606848 1000000000092907 30969000000000000000 9895417793173221 4503599627370496 1000000000092907 30969000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 7719 65536 24973259072661432 36028797018963968 30969 1000000000000000 rfl rfl rfl rfl (ep299 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep585 := nat_lit 179482349139087305015644748618341571093773575789797975518370499394273185

noncomputable def ep586 := nat_lit 130475579133053774917415337471771645994939053142504459568726330310561

noncomputable def ep587 := nat_lit 469861572998060854643489002501654579723510416220573500089763846259736481

noncomputable def ep588 := BSN.sin_dyadic_bound_f 326919747 268435456 3 2 131072 61999 ep585 ep64 ep586 ep587 ep66 ep586 122993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 326919747) qz274 0 2 ep585 ep64 ep586 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 326919747) qz275 0 2 ep587 ep66 ep586 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz382 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1641317) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep589 := @Enclosure.Real.IsNear.cos_image qz188 qz382 Bool.false 1641317 16384 97 65536 Bool.false 122993 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz188 Bool.false 451161783444146665053 4503599627370496000 45593000004235908851 30969000000000000000000 1641317 16384 97 65536 (ep584 rfl) rfl) (Enclosure.sfrac_false_div 1641317 16384) (BSN.cos_reduce3 qz382 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2875616507363866968064) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 122993 131072 15 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q3 1641317 16384 226375608064910080 72057594037927936 15 2875616507363866968064 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 122993 131072 2875616507363866968064 2361183241434822606848 326919747 268435456 61999 61938 (ep588 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep590 := nat_lit 99770405334663193353099267160177215783649737240173321714458600254734241

noncomputable def ep591 := nat_lit 299050264845723472509462970805588104058959333614234956224238348103581601

noncomputable def ep592 := BSN.cos_dyadic_bound_f 326919747 268435456 3 2 131072 61999 ep590 ep57 ep586 ep591 ep60 ep586 45304 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 326919747) qz269 0 2 ep590 ep57 ep586 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 326919747) qz270 0 2 ep591 ep60 ep586 rfl rfl rfl rfl) rfl rfl

noncomputable def ep593 := @Enclosure.Real.IsNear.sin_image qz188 qz382 Bool.false 1641317 16384 97 65536 Bool.true 45304 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz188 Bool.false 451161783444146665053 4503599627370496000 45593000004235908851 30969000000000000000000 1641317 16384 97 65536 (ep584 rfl) rfl) (Enclosure.sfrac_false_div 1641317 16384) (BSN.sin_reduce3 qz382 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2875616507363866968064) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 45304 131072 15 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q3 1641317 16384 226375608064910080 72057594037927936 15 2875616507363866968064 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 45304 131072 2875616507363866968064 2361183241434822606848 326919747 268435456 61999 61938 (ep592 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep594 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz114 (Real.cos qz188)) (@HMul.hMul Real Real Real qz0 qz114 (@Neg.neg Real Real.instNeg (Real.sin qz188))) Bool.false 5373687163 17179869184 90678897451 177347789586432 Bool.false 247422133 2147483648 5617307119 11084236849152 (@Enclosure.Real.IsNear.mulLit_ff qz114 (Real.cos qz188) 43691 131072 1 131072 122993 131072 3069529 2029584384 5373687163 17179869184 90678897451 177347789586432 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz188) Bool.false 122993 131072 3069529 2029584384 122993 131072 3069529 2029584384 (ep589 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz114 (@Neg.neg Real Real.instNeg (Real.sin qz188)) 43691 131072 1 131072 5663 16384 3069529 2029584384 247422133 2147483648 5617307119 11084236849152 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz188) Bool.true 5663 16384 3069529 2029584384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz188) Bool.true 45304 131072 3069529 2029584384 5663 16384 3069529 2029584384 (ep593 rfl rfl) rfl)) rfl)

noncomputable def ep595 := @ep582 5373687163 17179869184 90678897451 177347789586432 Bool.false 247422133 2147483648 5617307119 11084236849152 Bool.false 1130631003706478297088 32905693041 8589934592 1508487062881 266021684379648 Bool.true 666655185778507776 38804439 268435456 1497459311671 266021684379648 EMRow08.d10 (ep583 ep594) rfl rfl

noncomputable def ep596 := @Enclosure.Complex.IsNear.mul qz184 (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))) Bool.true 38657947041016595828587 428597531604777172992000 ep576 ep463 Bool.false

noncomputable abbrev qz189 := (Complex.re qz380)

noncomputable abbrev qz190 := (Complex.im qz380)

noncomputable def ep597 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz189 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz190 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) 17630502614391378179 428597531604777172992 799624049794843027261

noncomputable def ep598 := nat_lit 3318309239067086067597312

noncomputable def ep599 := nat_lit 16568700678687912627297755713665305677922304

noncomputable def ep600 := @Enclosure.Real.IsNear.mulLit_tf qz189 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 352109255 4294967296 15969767545 33252710547456 250355569529

noncomputable abbrev qz383 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz436 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz191 := (Real.cos qz383)

noncomputable abbrev qz192 := (@Neg.neg Real Real.instNeg (Real.sin qz383))

noncomputable abbrev qz384 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

noncomputable def ep601 := @Enclosure.Complex.IsNear.of_eq qz184 (Complex.mk (@HMul.hMul Real Real Real qz0 qz384 qz191) (@HMul.hMul Real Real Real qz0 qz384 qz192)) Bool.true 352109255 4294967296 15969767545 33252710547456 Bool.false 2623514455 8589934592 129192159905 266021684379648 (BSN.cpow_neg_s_mk qz143 45593 1000 10 qz144 rfl)

noncomputable abbrev qz385 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable abbrev qz386 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10) qz26)

noncomputable def ep602 := @Enclosure.Real.IsNear.inv_image qz385 414487 131072 1 131072 20724 20725 65536 (@Enclosure.Real.IsNear.of_eq qz385 (Real.sqrt qz386) Bool.false 414487 131072 1 131072 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz386) Bool.false 414487 131072 1 131072 414487 131072 1 131072 (BSN.sqrt_enclosure 10 1 207243 207244 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep603 := BSN.log_dyadic_bound 2 18 3 2 1574640 65536 30969 6528 48 14623 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz387 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz193 := qz387

noncomputable def ep604 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz193 45593 1000 0 1 10369857060558565 4503599627370496 1000000000092907 30969000000000000000 94558578592409330809 900719925474099200 45593000004235908851 30969000000000000000000 qz145 (BSN.isNear_log_sfrac 10 1 10369857060558565 4503599627370496 1000000000092907 30969000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz386) Bool.false 5436791618566128926720 2361183241434822606848 1000000000092907 30969000000000000000 10369857060558565 4503599627370496 1000000000092907 30969000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 14623 65536 24973259072661432 36028797018963968 30969 1000000000000000 rfl rfl rfl rfl (ep603 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep605 := nat_lit 133030004146520952154789144536361104571241070083802008395264868290437376

noncomputable def ep606 := nat_lit 231764568825553612794967898511977390009906423401733711057205839831296

noncomputable def ep607 := nat_lit 398626483301911749238777497812059358933703397404602557763680193191649536

noncomputable def ep608 := BSN.cos_dyadic_bound_f 351261766 268435456 3 2 131072 61999 ep605 ep57 ep606 ep607 ep60 ep606 33980 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 351261766) qz269 0 2 ep605 ep57 ep606 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 351261766) qz270 0 2 ep607 ep60 ep606 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz194 := qz383

noncomputable abbrev qz388 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3440021) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep609 := @Enclosure.Real.IsNear.cos_image qz194 qz388 Bool.false 3440021 32768 97 65536 Bool.true 33980 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 94558578592409330809 900719925474099200 45593000004235908851 30969000000000000000000 3440021 32768 97 65536 (ep604 rfl) rfl) (Enclosure.sfrac_false_div 3440021 32768) (BSN.cos_reduce2 qz388 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6179462345209541558272) qz284) 226375608064910080 72057594037927936 Bool.false 33980 131072 16 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q2 3440021 32768 226375608064910080 72057594037927936 16 6179462345209541558272 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33980 131072 6179462345209541558272 4722366482869645213696 351261766 268435456 61999 61938 (ep608 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep610 := nat_lit 239268595808677270988384485846640406316226001012122228142630998250922240

noncomputable def ep611 := nat_lit 626280608292246718167910372048372148387242535108145885793750471678402816

noncomputable def ep612 := BSN.sin_dyadic_bound_f 351261766 268435456 3 2 131072 61999 ep610 ep64 ep606 ep611 ep66 ep606 126590 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 351261766) qz274 0 2 ep610 ep64 ep606 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 351261766) qz275 0 2 ep611 ep66 ep606 rfl rfl rfl rfl) rfl rfl

noncomputable def ep613 := @Enclosure.Real.IsNear.sin_image qz194 qz388 Bool.false 3440021 32768 97 65536 Bool.true 126590 131072 1 30969 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 94558578592409330809 900719925474099200 45593000004235908851 30969000000000000000000 3440021 32768 97 65536 (ep604 rfl) rfl) (Enclosure.sfrac_false_div 3440021 32768) (BSN.sin_reduce2 qz388 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6179462345209541558272) qz284) 226375608064910080 72057594037927936 Bool.false 126590 131072 16 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q2 3440021 32768 226375608064910080 72057594037927936 16 6179462345209541558272 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 126590 131072 6179462345209541558272 4722366482869645213696 351261766 268435456 61999 61938 (ep612 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz195 := (Real.sin qz383)

noncomputable def ep614 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz384 qz191) (@HMul.hMul Real Real Real qz0 qz384 qz192) Bool.true 352109255 4294967296 15969767545 33252710547456 Bool.false 2623514455 8589934592 129192159905 266021684379648 (@Enclosure.Real.IsNear.mulLit_ft qz384 qz191 41449 131072 1 131072 8495 32768 3069529 2029584384 352109255 4294967296 15969767545 33252710547456 (@Enclosure.Real.IsNear.recentre' qz384 Bool.false 41449 131072 1 131072 41449 131072 1 131072 (ep602 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz191 Bool.true 33980 131072 3069529 2029584384 8495 32768 3069529 2029584384 (ep609 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz384 qz192 41449 131072 1 131072 63295 65536 3069529 2029584384 2623514455 8589934592 129192159905 266021684379648 (@Enclosure.Real.IsNear.recentre' qz384 Bool.false 41449 131072 1 131072 41449 131072 1 131072 (ep602 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz195 Bool.true 63295 65536 3069529 2029584384 (@Enclosure.Real.IsNear.recentre' qz195 Bool.true 126590 131072 3069529 2029584384 63295 65536 3069529 2029584384 (ep613 rfl rfl) rfl)) rfl)

noncomputable def ep615 := @ep600 498953195760 0 1 17630502614391378179 428597531604777172992 799624049794843027261 ep598 (@Enclosure.Complex.IsNear.re_isNear qz184 Bool.true 352109255 4294967296 15969767545 33252710547456 Bool.false 2623514455 8589934592 129192159905 266021684379648 (ep601 ep614))

noncomputable def ep616 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))) Bool.false 250355569529 498953195760 0 1 Bool.false

noncomputable def ep617 := @Enclosure.Complex.IsNear.addLitP qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) Bool.false 2068971649 4157943298 0 1 Bool.true 455930000

noncomputable def ep618 := @ep617 2078971649 0 1 Bool.false 1 240 0 1 Bool.false 45593 120000 0 1 Bool.false 500711139058 250355569529 498953195760 0 1 Bool.false 40074954392857 40074954392857 249476597880000 0 1

noncomputable abbrev qz196 := (@HDiv.hDiv Complex Complex Complex qz310 qz381 (@HSub.hSub Complex Complex Complex qz303 qz349 (1 : Complex)))

noncomputable def ep619 := @Enclosure.Complex.IsNear.addLitP qz196 qz82 Bool.true 20000000 8315886596 0 1 Bool.true 1823720000 8315886596 0 1

noncomputable def ep620 := @Enclosure.Complex.IsNear.of_eq qz196 (Complex.mk (Enclosure.sfrac Bool.true 20000000 8315886596) (Enclosure.sfrac Bool.true 1823720000 8315886596)) Bool.true 20000000 8315886596 0 1 Bool.true 1823720000 8315886596 0 1

noncomputable def ep621 := @ep619 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 8275886596 2068971649 4157943298 0 1 Bool.true 1823720000 455930000 2078971649 0 1 (ep620 (BSN.N_div_s_sub_one_mk qz143 45593 1000 10 qz144 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 20000000 8315886596) (Enclosure.sfrac Bool.true 1823720000 8315886596) Bool.true 20000000 8315886596 0 1 Bool.true 1823720000 8315886596 0 1 (Enclosure.Real.IsNear.const Bool.true 20000000 8315886596) (Enclosure.Real.IsNear.const Bool.true 1823720000 8315886596))) qz83 rfl

noncomputable abbrev qz389 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz433 qz439 1))

noncomputable abbrev qz197 := qz389

noncomputable def ep622 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz197)) Bool.false 1 240 0 1

noncomputable def ep623 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz197) Bool.false 0 1 0 1 Bool.false

noncomputable def ep624 := @ep623 0 1 0 1 Bool.false 1 240 0 1 Bool.false 45593 120000 0 1 Bool.false 1 1 240 0 1 Bool.false 45593 45593 120000 0

noncomputable def ep625 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false

noncomputable def ep626 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz197 Bool.false 1 240 0 1 Bool.false 45593 120000 0 1

noncomputable abbrev qz198 := (Complex.re qz389)

noncomputable abbrev qz199 := (Complex.im qz389)

noncomputable def ep627 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199) 1 240 0 1 0 1 0

noncomputable def ep628 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198 1 24 0 1 1 10 0 1 1

noncomputable def ep629 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep630 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep631 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) qz141 Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 (BSN.ascPochhammer_one_eval qz141)

noncomputable def ep632 := ep631 (@Enclosure.Complex.IsNear.of_eq qz141 (Complex.mk qz77 qz143) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 (BSN.s_crit_mk qz143 Bool.false 45593 1000 qz144) (@Enclosure.Complex.IsNear.mk qz77 qz143 Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 qz319 qz145))

noncomputable def ep633 := @ep630 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep632)

noncomputable def ep634 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 45593 1000 0 1 0 1 0

noncomputable def ep635 := @ep634 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep632)

noncomputable def ep636 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) 45593 12000 0 1 0 1 0 1 45593

noncomputable def ep637 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 45593 1000 0 1 45593 12000 0

noncomputable def ep638 := @ep637 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep632)

noncomputable def ep639 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep640 := @ep639 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep632)

noncomputable def ep641 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 45593 12000 0 1 (@ep629 1 24 0 1 (ep633 rfl) (ep635 rfl) rfl rfl) (@ep636 45593 12000 0 1 (ep638 rfl) (ep640 rfl) rfl rfl)

noncomputable def ep642 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 45593 12000 0 1 ep641

noncomputable abbrev qz200 := (@Enclosure.Complex.IsNear.of_eq qz389 (Complex.mk (Enclosure.sfrac Bool.false 1 10) qz265) Bool.false 1 10 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 10 1 10 EMRow08.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 10) qz265 Bool.false 1 10 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 10) qz277))

noncomputable def ep643 := @ep628 240 0 1 ep642 (@Enclosure.Complex.IsNear.re_isNear qz197 Bool.false 1 10 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199 45593 12000 0 1 0 1 0 1 0

noncomputable def ep645 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 45593 12000 0 1 ep641

noncomputable def ep646 := @ep644 1 0 1 ep645 (@Enclosure.Complex.IsNear.im_isNear qz197 Bool.false 1 10 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep647 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198) 0 1 0 1 45593 120000 0

noncomputable def ep648 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199 1 24 0 1 0 1 0 1 0

noncomputable def ep649 := @ep648 1 0 1 ep642 (@Enclosure.Complex.IsNear.im_isNear qz197 Bool.false 1 10 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep650 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz121) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198 45593 12000 0 1 1 10 0 1 45593

noncomputable def ep651 := @ep650 120000 0 1 ep645 (@Enclosure.Complex.IsNear.re_isNear qz197 Bool.false 1 10 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep652 := @ep624 1 (@ep625 0 1 0 1 (BSN.bern_sum_base qz141 10) qz99) (ep626 (@ep627 1 1 1 240 0 1 (ep643 rfl) (ep646 rfl) rfl rfl) (@ep647 1 45593 45593 120000 0 1 (ep649 rfl) (ep651 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep653 := ep618 (ep621 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep622 Bool.false 45593 120000 0 1 (BSN.bern_sum_succ qz141 10 0 1 1 rfl rfl) (ep652 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep654 := @Enclosure.Real.IsNear.mulLit_ff qz190 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 2623514455 8589934592 129192159905 266021684379648 40074954392857

noncomputable def ep655 := @ep654 249476597880000 0 1 21027444426625217649587 428597531604777172992000 1035473983221512746759717 ep463 (@Enclosure.Complex.IsNear.im_isNear qz184 Bool.true 352109255 4294967296 15969767545 33252710547456 Bool.false 2623514455 8589934592 129192159905 266021684379648 (ep601 ep614))

noncomputable def ep656 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))) Bool.false 250355569529 498953195760 0 1 Bool.false

noncomputable def ep657 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz189 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz190 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) 2822152467085571118307 214298765802388586496000 127997541206080579685213

noncomputable def ep658 := nat_lit 1659154619533543033798656000

noncomputable def ep659 := nat_lit 26546473912536688540778496

noncomputable def ep660 := nat_lit 25731641695397622908881781415617908715814912

noncomputable def ep661 := @Enclosure.Real.IsNear.mulLit_tf qz189 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 352109255 4294967296 15969767545 33252710547456 40074954392857

noncomputable def ep662 := @ep661 249476597880000 0 1 2822152467085571118307 214298765802388586496000 127997541206080579685213 ep658 (@Enclosure.Complex.IsNear.re_isNear qz184 Bool.true 352109255 4294967296 15969767545 33252710547456 Bool.false 2623514455 8589934592 129192159905 266021684379648 (ep601 ep614))

noncomputable def ep663 := @Enclosure.Real.IsNear.mulLit_ff qz190 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz186 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 2623514455 8589934592 129192159905 266021684379648 250355569529

noncomputable def ep664 := @ep663 498953195760 0 1 131362291109817808339 857195063209554345984 6468795354339582706949 ep659 (@Enclosure.Complex.IsNear.im_isNear qz184 Bool.true 352109255 4294967296 15969767545 33252710547456 Bool.false 2623514455 8589934592 129192159905 266021684379648 (ep601 ep614))

noncomputable abbrev qz390 := (ep653 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep665 := @ep596 10006140103456293655481 71432921934129528832000 1064594501704608997739051 ep573 (@ep597 ep598 21027444426625217649587 428597531604777172992000 1035473983221512746759717 ep463 ep599 38657947041016595828587 428597531604777172992000 ep576 ep463 (ep615 (@ep616 40074954392857 249476597880000 0 1 qz390) rfl) (ep655 (@ep656 40074954392857 249476597880000 0 1 qz390) rfl) rfl rfl) (@ep657 ep658 131362291109817808339 857195063209554345984 6468795354339582706949 ep659 ep660 10006140103456293655481 71432921934129528832000 1064594501704608997739051 ep573 (ep662 (@ep656 40074954392857 249476597880000 0 1 qz390) rfl) (ep664 (@ep616 40074954392857 249476597880000 0 1 qz390) rfl) rfl rfl)

noncomputable def ep666 := @ep579 ep572 ep573 (@ep580 266021684379648 (BSN.head_sum_c_eq qz141 10) (ep581 (BSN.head_sum_c_succ qz141 9 10 rfl rfl) (ep595 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep665 rfl rfl rfl

noncomputable def ep667 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz141 1 10) Bool.false ep461 428597531604777172992000 ep462 ep463 Bool.true 320045949196494952519 71432921934129528832000 ep572 ep573 (@ep574 ep463 Bool.true 320045949196494952519 71432921934129528832000 ep572 ep573 (BSN.zetaApproximant_eq_folded' qz141 1 10 rfl) (ep666 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep668 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) (Complex.im (zetaApproximant qz141 1 10)) 5 131072 992807

noncomputable def ep669 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) Bool.false 5 131072 992807

noncomputable def ep670 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154) qz364 Bool.false 1441209 65536 31

noncomputable def ep671 := nat_lit 276712930811019688720382165349183596025285587684404941484380137734537216

noncomputable def ep672 := nat_lit 828140726936733665616081614811603455152489529879073309556869109777432576

noncomputable def ep673 := BSN.cos_dyadic_bound_f 421645496 268435456 3 2 131072 61999 ep671 ep57 ep568 ep672 ep60 ep568 5 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 421645496) qz269 0 2 ep671 ep57 ep568 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 421645496) qz270 0 2 ep672 ep60 ep568 rfl rfl rfl rfl) rfl rfl

noncomputable def ep674 := @ep670 32768 Bool.false 5 131072 1 30969 (@ep467 1441209 65536 31 32768 ep566 rfl) (Enclosure.sfrac_false_div 1441209 65536) (BSN.sin_reduce1 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14835332039770854391808) qz30) 226375608064910080 72057594037927936 Bool.false 5 131072 3 1000000000000000 61938 30969 (BSN.sin_reduce_arg_pos_rat_q1 1441209 65536 226375608064910080 72057594037927936 3 14835332039770854391808 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 5 131072 14835332039770854391808 9444732965739290427392 421645496 268435456 61999 61938 (ep673 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep675 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz141 1 10) Bool.false ep461 428597531604777172992000 ep462 ep463 Bool.true 320045949196494952519 71432921934129528832000 ep572 ep573 (@ep574 ep463 Bool.true 320045949196494952519 71432921934129528832000 ep572 ep573 (BSN.zetaApproximant_eq_folded' qz141 1 10 rfl) (ep666 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow08.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 10 qz143) Bool.true ep446 ep447 ep448 ep449 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 10 qz143) ep450 Bool.true ep446 ep447 ep448 ep449 (@Eq.refl Real ep450) (@ep451 Bool.true ep446 ep447 ep448 ep449 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154) (zetaApproximant qz141 1 10)) (@ep453 ep447 ep454 ep455 320045949196494952519 ep456 ep457 ep458 ep459 ep446 ep447 ep448 ep449 (@ep460 1014792192 ep461 428597531604777172992000 ep462 ep463 ep452 ep447 ep454 ep455 (@ep464 1014792192 131071 131072 992807 1014792192 (ep571 rfl rfl) rfl) ep667 rfl) (@ep668 1014792192 320045949196494952519 71432921934129528832000 ep572 ep573 320045949196494952519 ep456 ep457 ep458 (@ep669 1014792192 5 131072 992807 1014792192 (ep674 rfl rfl) rfl) ep675 rfl) rfl rfl))

theorem EMRow08.d13 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow08.d14 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow08.d15 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow08.d16 : @Eq Nat (Nat.pow 9 (Nat.succ (Nat.mul 2 3))) 4782969 := @Eq.refl Nat 4782969

noncomputable abbrev qz440 := (@HAdd.hAdd Complex Complex Complex qz443 qz442 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz391 := qz440

noncomputable abbrev qz201 := (@HDiv.hDiv Real Real Real qz257 (@Norm.norm Complex Complex.instNorm qz391) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz259) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz202 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz203 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz392 := (@HPow.hPow Complex Complex Complex qz421 (@Nat.cast Complex Complex.instNatCast 9) (@HSub.hSub Complex Complex Complex qz427 qz422 qz423))

noncomputable abbrev qz204 := qz392

noncomputable def ep676 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 9))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) 18811989 1073741824 838295 9663676416 289567737769759 492581209243648 781858277

noncomputable def ep677 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 9)) 123 8192 1 221184 152943 131072 711 131072 18811989 1073741824

noncomputable abbrev qz393 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz205 := (@HPow.hPow Real Nat Real qz393 qz258 2)

noncomputable def ep678 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz205) 96 162 0 1 3321 131072 1 131072 123 8192 1 221184

noncomputable def ep679 := nat_lit 781950621441006189802102638025

noncomputable def ep680 := nat_lit 19807040628566084398385987584

noncomputable def ep681 := nat_lit 26986075409044041160201671

noncomputable def ep682 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz206 := qz258

noncomputable abbrev qz394 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz206 1)

noncomputable def ep683 := @Enclosure.Real.IsNear.mulLit_ff qz394 qz206 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep679 ep680 ep681 ep682

noncomputable def ep684 := ep683 (@Enclosure.Real.IsNear.of_eq qz394 qz206 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz206) (@Enclosure.Real.IsNear.of_eq qz206 qz255 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz256)) (@Enclosure.Real.IsNear.of_eq qz206 qz255 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz256) rfl

noncomputable def ep685 := @Enclosure.Real.IsNear.inv_image qz205 ep679 ep680 ep681 ep682 1660 1661 65536 (@Enclosure.Real.IsNear.of_eq qz205 (@HMul.hMul Real Real Real qz0 qz394 qz206) Bool.false ep679 ep680 ep681 ep682 (BSN.pow_succ_r qz206 1 2 rfl) ep684) rfl rfl rfl

noncomputable def ep686 := ep678 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz205) Bool.false 3321 131072 1 131072 3321 131072 1 131072 (ep685 rfl rfl rfl) rfl)

noncomputable def ep687 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 9)) (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz21 1 9)) (Complex.re (zetaApproximant qz21 1 9))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz21 1 9)) (Complex.im (zetaApproximant qz21 1 9))))) Bool.false 152943 131072 711 131072

noncomputable def ep688 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz21 1 9)) (Complex.re (zetaApproximant qz21 1 9))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz21 1 9)) (Complex.im (zetaApproximant qz21 1 9))))) Bool.false 152943 131072 711 131072

noncomputable def ep689 := nat_lit 4108317419793951384495886638468045737

noncomputable def ep690 := nat_lit 3017252632376307828002251603968000000

noncomputable def ep691 := nat_lit 3167982317642477022956754293529222939007089899767

noncomputable def ep692 := nat_lit 250492926038353526726807594716296620883836928000000

noncomputable def ep693 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz21 1 9)) (Complex.re (zetaApproximant qz21 1 9))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz21 1 9)) (Complex.im (zetaApproximant qz21 1 9)))) ep689 ep690 ep691 ep692 76116 76827

noncomputable def ep694 := nat_lit 2296917218494358020912191593878180566875329

noncomputable def ep695 := nat_lit 1692451014706943251557483819897496535040000

noncomputable def ep696 := nat_lit 23924903645105979704051819361147997114280600335741

noncomputable def ep697 := nat_lit 2003943408306828213814460757730372967070695424000000

noncomputable def ep698 := nat_lit 753879929437685627901290573778790816989961

noncomputable def ep699 := nat_lit 169245101470694325155748381989749653504000000

noncomputable def ep700 := nat_lit 283790979206767295920442997417157279555223772479

noncomputable def ep701 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz21 1 9)) (Complex.re (zetaApproximant qz21 1 9))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz21 1 9)) (Complex.im (zetaApproximant qz21 1 9))) ep694 ep695 ep696 ep697 ep698 ep699 ep700

noncomputable def ep702 := nat_lit 400788681661365642762892151546074593414139084800000

noncomputable def ep703 := nat_lit 390017892565406601096619853609768145937918669479849693041282007023782697475967549440000

noncomputable def ep704 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz21 1 9)) (Complex.re (zetaApproximant qz21 1 9)) 1515558385049668095073 1300942356412052275200 228881593689786564774949 ep161 1515558385049668095073 1300942356412052275200 228881593689786564774949 ep161 ep694

noncomputable def ep705 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz21 1 9)) (Complex.im (zetaApproximant qz21 1 9)) 868262592444063334531 13009423564120522752000 228712603706125532426023 ep161 868262592444063334531 13009423564120522752000 228712603706125532426023 ep161 ep698

noncomputable def ep706 := @ep676 492581209243648 320187423214352925196288 298197775347487 492581209243648 391606232333 4433230883192832 (@ep677 838295 9663676416 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz205)) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow08.d13 EMRow08.d14 rfl) (ep686 rfl)) (ep687 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz21 1 9)) (@ep688 152943 131072 711 131072 (@ep693 65536 (@ep701 ep702 ep703 ep689 ep690 ep691 ep692 (@ep704 ep695 ep696 ep697 ep358 ep358 rfl) (@ep705 ep699 ep700 ep702 ep364 ep364 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz207 := (@Norm.norm Complex Complex.instNorm qz391)

noncomputable abbrev qz395 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep707 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz207 qz395) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) Bool.false 289567737769759 492581209243648 781858277 492581209243648 (BSN.zrb_shape_eq qz207 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) qz24 3)

noncomputable def ep708 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz207 qz395) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) 5571653 458752 1 458752 51971603 1073741824 131 1073741824

noncomputable def ep709 := @Enclosure.Real.IsNear.mulLit_ff qz207 qz395 5571653 131072 1 131072 2 7 0 1 5571653 458752

noncomputable abbrev qz396 := (Complex.re qz440)

noncomputable abbrev qz397 := (Complex.im qz440)

noncomputable abbrev qz208 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz254 qz396 qz396) (@HMul.hMul Real Real Real qz254 qz397 qz397))

noncomputable abbrev qz209 := qz391

noncomputable def ep710 := @Enclosure.Real.IsNear.of_eq qz207 (Real.sqrt qz208) Bool.false 5571653 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz209)

noncomputable def ep711 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz208) Bool.false 5571653 131072 1 131072 5571653

noncomputable def ep712 := @Enclosure.Real.IsNear.sqrt_image qz208 56467453 31250 0 1 2785826 2785827 65536

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz254 qz396 qz396)

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz254 qz397 qz397)

noncomputable def ep713 := @Enclosure.Real.IsNear.addLit_ff qz210 qz211 49 4 0 1 112169281 62500 0 1

noncomputable abbrev qz212 := qz396

noncomputable def ep714 := @Enclosure.Real.IsNear.mulLit_ff qz212 qz212 7 2 0 1 7 2 0 1 49 4

noncomputable def ep715 := @Enclosure.Complex.IsNear.of_eq qz209 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz24) Bool.false 7 2 0 1 Bool.false 42364 1000 0 1 (BSN.s_add_nat_mk qz24 Bool.false 42364 1000 3 qz25)

noncomputable abbrev qz213 := (ep715 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz267 Bool.false 7 2 0 1 Bool.false 42364 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz271))

noncomputable def ep716 := @ep714 0 1 (@Enclosure.Complex.IsNear.re_isNear qz209 Bool.false 7 2 0 1 Bool.false 42364 1000 0 1 qz213)

noncomputable def ep717 := ep716 (@Enclosure.Complex.IsNear.re_isNear qz209 Bool.false 7 2 0 1 Bool.false 42364 1000 0 1 qz213)

noncomputable abbrev qz214 := qz397

noncomputable def ep718 := @Enclosure.Real.IsNear.mulLit_ff qz214 qz214 42364 1000 0 1 42364 1000 0 1 112169281 62500

noncomputable def ep719 := @ep718 0 1 (@Enclosure.Complex.IsNear.im_isNear qz209 Bool.false 7 2 0 1 Bool.false 42364 1000 0 1 qz213)

noncomputable def ep720 := ep719 (@Enclosure.Complex.IsNear.im_isNear qz209 Bool.false 7 2 0 1 Bool.false 42364 1000 0 1 qz213)

noncomputable def ep721 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))))) Bool.false 51971603 1073741824

noncomputable def ep722 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))))) Bool.false 51971603 1073741824

noncomputable def ep723 := nat_lit 218959863835878311247205302408090266700117213455677

noncomputable def ep724 := nat_lit 93461343453626897313548933925961728000000000000000000

noncomputable def ep725 := nat_lit 2039496774966309711817392956138417501646661021520343766591068731

noncomputable def ep726 := nat_lit 173635680274240948884716683178591816800768690288066560000000000000000000

noncomputable def ep727 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))) ep723 ep724 ep725 ep726

noncomputable def ep728 := nat_lit 13306705489469432172085375785052240639732148976601

noncomputable def ep729 := nat_lit 7476907476290151785083914714076938240000000000000000

noncomputable def ep730 := nat_lit 15470932314925360979967972422004023027664065941524397427529033379

noncomputable def ep731 := nat_lit 1736356802742409488847166831785918168007686902880665600000000000000000000

noncomputable def ep732 := nat_lit 105252090435020818192276210189874517406930702496329

noncomputable def ep733 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) ep728 ep729 ep730 ep731 ep732

noncomputable def ep734 := nat_lit 186922686907253794627097867851923456000000000000000000

noncomputable def ep735 := nat_lit 4924035434737736138205957139380151988802544273679040238381653931

noncomputable def ep736 := nat_lit 3274285285843904355488390406202332341418793550119189624073825973096185426656724212776960000000000000000

noncomputable def ep737 := nat_lit 3647835726765863037043301

noncomputable def ep738 := nat_lit 86469112845513523200000000

noncomputable def ep739 := nat_lit 139152877426204791094289792827

noncomputable def ep740 := nat_lit 1317708921857330936713052160000000000

noncomputable def ep741 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) ep737 ep738 ep739 ep740 ep737 ep738 ep739

noncomputable def ep742 := nat_lit 10259244145404709988852323

noncomputable def ep743 := nat_lit 432345564227567616000000000

noncomputable def ep744 := nat_lit 78738435832200270937968603529

noncomputable def ep745 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204) Bool.true ep737 ep738 ep739 ep740 Bool.false ep742 ep743 ep744

noncomputable def ep746 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204 Bool.true ep737 ep738 ep739 ep740 Bool.false ep742 ep743 ep744 ep740

noncomputable def ep747 := nat_lit 9183232512517843487678041

noncomputable def ep748 := nat_lit 1756945229143107915617402880000000

noncomputable def ep749 := nat_lit 3823043890731082118202101

noncomputable def ep750 := nat_lit 132265453041816408478531262077

noncomputable abbrev qz215 := (Complex.re qz392)

noncomputable abbrev qz216 := (Complex.im qz392)

noncomputable def ep751 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216) 146006803304349234299 72057594037927936000000 ep747 ep748 ep749 ep738 ep750

noncomputable def ep752 := nat_lit 262854265916344371766162284131537949556736000000

noncomputable def ep753 := nat_lit 117129681942873861041160192

noncomputable def ep754 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215 168214859 15000000 0 1 13019670572415 72057594037927936 54592278988373099 ep753 146006803304349234299

noncomputable def ep755 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) 168214859 15000000 0 1 0 1 0 1 168214859

noncomputable def ep756 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 504644577 62500 0 1 168214859 15000000 0

noncomputable def ep757 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz20) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow08.d15 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz20 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz31)

noncomputable abbrev qz398 := (@HAdd.hAdd Complex Complex Complex qz420 qz419 qz424)

noncomputable abbrev qz217 := qz398

noncomputable def ep758 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz51 (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) qz217) Bool.true 504644577 62500 0 1 Bool.true 592089357223 7812500 0 1

noncomputable abbrev qz218 := (Complex.re qz398)

noncomputable abbrev qz219 := (Complex.im qz398)

noncomputable def ep759 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz218) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz219) 56061203 12500 0 1 112169281 31250 0 1

noncomputable def ep760 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz218 56061203 31250 0 1 5 2 0 1 56061203 12500

noncomputable abbrev qz399 := (@HAdd.hAdd Complex Complex Complex qz420 qz419 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz220 := qz399

noncomputable def ep761 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz51 (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) qz220) Bool.true 56061203 31250 0 1 Bool.false 10591 125 0 1

noncomputable abbrev qz221 := (Complex.re qz399)

noncomputable abbrev qz222 := (Complex.im qz399)

noncomputable def ep762 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz221) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz222) 3 4 0 1 112169281 62500 0 1

noncomputable def ep763 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz221 1 2 0 1 3 2 0 1 3 4

noncomputable def ep764 := @ep763 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep325)

noncomputable def ep765 := @Enclosure.Complex.IsNear.of_eq qz220 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz24) Bool.false 3 2 0 1 Bool.false 42364 1000 0 1 (BSN.s_add_nat_mk qz24 Bool.false 42364 1000 1 qz25)

noncomputable abbrev qz223 := (ep765 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz267 Bool.false 3 2 0 1 Bool.false 42364 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz271))

noncomputable def ep766 := ep764 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 3 2 0 1 Bool.false 42364 1000 0 1 qz223)

noncomputable def ep767 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz222 42364 1000 0 1 42364 1000 0 1 112169281 62500

noncomputable def ep768 := @ep767 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep325)

noncomputable def ep769 := ep768 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 3 2 0 1 Bool.false 42364 1000 0 1 qz223)

noncomputable def ep770 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) qz220 Bool.true 56061203 31250 0 1 Bool.false 10591 125 0 1 (@ep762 448489624 56061203 31250 0 1 (ep766 rfl) (ep769 rfl) rfl rfl)

noncomputable def ep771 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz222) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz221) 10591 500 0 1 31773 500 0 1

noncomputable def ep772 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz222 1 2 0 1 42364 1000 0 1 10591 500

noncomputable def ep773 := @ep772 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep325)

noncomputable def ep774 := ep773 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 3 2 0 1 Bool.false 42364 1000 0 1 qz223)

noncomputable def ep775 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz221 42364 1000 0 1 3 2 0 1 31773 500

noncomputable def ep776 := @ep775 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep325)

noncomputable def ep777 := ep776 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 3 2 0 1 Bool.false 42364 1000 0 1 qz223)

noncomputable abbrev qz224 := (ep761 (BSN.ascPochhammer_succ_eval_c 1 2 qz259 rfl) (ep770 (@ep771 21182000 10591 125 0 1 (ep774 rfl) (ep777 rfl) rfl rfl)))

noncomputable def ep778 := @ep760 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 56061203 31250 0 1 Bool.false 10591 125 0 1 qz224)

noncomputable def ep779 := @Enclosure.Complex.IsNear.of_eq qz217 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz24) Bool.false 5 2 0 1 Bool.false 42364 1000 0 1 (BSN.s_add_nat_mk qz24 Bool.false 42364 1000 2 qz25)

noncomputable abbrev qz225 := (ep779 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz267 Bool.false 5 2 0 1 Bool.false 42364 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz271))

noncomputable def ep780 := ep778 (@Enclosure.Complex.IsNear.re_isNear qz217 Bool.false 5 2 0 1 Bool.false 42364 1000 0 1 qz225)

noncomputable def ep781 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz219 10591 125 0 1 42364 1000 0 1 112169281 31250

noncomputable def ep782 := @ep781 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 56061203 31250 0 1 Bool.false 10591 125 0 1 qz224)

noncomputable def ep783 := ep782 (@Enclosure.Complex.IsNear.im_isNear qz217 Bool.false 5 2 0 1 Bool.false 42364 1000 0 1 qz225)

noncomputable def ep784 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) qz217 Bool.true 504644577 62500 0 1 Bool.true 592089357223 7812500 0 1 (@ep759 3154028606250 504644577 62500 0 1 (ep780 rfl) (ep783 rfl) rfl rfl)

noncomputable def ep785 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz219) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz218) 593744200973 7812500 0 1 10591 50 0 1

noncomputable def ep786 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz219 56061203 31250 0 1 42364 1000 0 1 593744200973 7812500

noncomputable def ep787 := @ep786 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 56061203 31250 0 1 Bool.false 10591 125 0 1 qz224)

noncomputable def ep788 := ep787 (@Enclosure.Complex.IsNear.im_isNear qz217 Bool.false 5 2 0 1 Bool.false 42364 1000 0 1 qz225)

noncomputable def ep789 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz218 10591 125 0 1 5 2 0 1 10591 50

noncomputable def ep790 := @ep789 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 56061203 31250 0 1 Bool.false 10591 125 0 1 qz224)

noncomputable def ep791 := ep790 (@Enclosure.Complex.IsNear.re_isNear qz217 Bool.false 5 2 0 1 Bool.false 42364 1000 0 1 qz225)

noncomputable abbrev qz226 := (ep758 (BSN.ascPochhammer_succ_eval_c 2 3 qz259 rfl) (ep784 (@ep785 29604467861150 592089357223 7812500 0 1 (ep788 rfl) (ep791 rfl) rfl rfl)))

noncomputable def ep792 := @ep756 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep757) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 504644577 62500 0 1 Bool.true 592089357223 7812500 0 1 qz226)

noncomputable def ep793 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 592089357223 7812500 0 1 0 1 0

noncomputable def ep794 := @ep793 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep757) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 504644577 62500 0 1 Bool.true 592089357223 7812500 0 1 qz226)

noncomputable def ep795 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) 592089357223 5625000000 0 1 0 1 0 1 592089357223

noncomputable def ep796 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 592089357223 7812500 0 1 592089357223 5625000000 0

noncomputable def ep797 := @ep796 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep757) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 504644577 62500 0 1 Bool.true 592089357223 7812500 0 1 qz226)

noncomputable def ep798 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 504644577 62500 0 1 0 1 0

noncomputable def ep799 := @ep798 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep757) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 504644577 62500 0 1 Bool.true 592089357223 7812500 0 1 qz226)

noncomputable def ep800 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 168214859 15000000 0 1 Bool.false 592089357223 5625000000 0 1 (@ep755 168214859 15000000 0 1 (ep792 rfl) (ep794 rfl) rfl rfl) (@ep795 592089357223 5625000000 0 1 (ep797 rfl) (ep799 rfl) rfl rfl)

noncomputable def ep801 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 168214859 15000000 0 1 Bool.false 592089357223 5625000000 0 1 ep800

noncomputable def ep802 := nat_lit 234259363885747722082320384

noncomputable def ep803 := @Enclosure.Complex.IsNear.re_isNear qz204 Bool.false 13019670572415 72057594037927936 54592278988373099 ep753 Bool.false 484265235149025 1152921504606846976 223387654968439099 ep802

noncomputable abbrev qz400 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4782969)))

noncomputable def ep804 := @Enclosure.Complex.IsNear.of_eq qz204 (Complex.mk (@HMul.hMul Real Real Real qz0 qz400 qz115) (@HMul.hMul Real Real Real qz0 qz400 qz116)) Bool.false 13019670572415 72057594037927936 54592278988373099 ep753 Bool.false 484265235149025 1152921504606846976 223387654968439099

noncomputable abbrev qz401 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4782969))

noncomputable abbrev qz402 := (@Nat.cast Real Real.instNatCast 4782969)

noncomputable def ep805 := @Enclosure.Real.IsNear.inv_image qz401 2348273369089 1073741824 1 1073741824 245482 245483 536870912 (@Enclosure.Real.IsNear.of_eq qz401 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz402 qz26)) Bool.false 2348273369089 1073741824 1 1073741824 (BSN.sqrt_natCast_div_one 4782969) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz402 qz26)) Bool.false 2348273369089 1073741824 1 1073741824 2348273369089 1073741824 1 1073741824 (BSN.sqrt_enclosure 4782969 1 1174136684544 1174136684545 536870912 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep806 := nat_lit 50796902250000000000000000

noncomputable def ep807 := nat_lit 42500504340760369752440832

noncomputable def ep808 := nat_lit 19342813113834066795298816

noncomputable def ep809 := BSN.log_dyadic_bound 1 17 4 3 2534444745 536870912 203187609 2929319 15 63234285 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 1) (BSN.artanhQ 17) 0 3 2929319 2534444745 15 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep810 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz117 42364 1000 0 1 9895419781273317 4503599627370496 1000000609562827 203187609000000000000000 104802390903465700347 1125899906842624000 10591006455879900757 ep806 qz29 (BSN.isNear_log_sfrac 9 1 9895419781273317 4503599627370496 1000000609562827 203187609000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz344 Bool.false ep807 ep808 1000000609562827 203187609000000000000000 9895419781273317 4503599627370496 1000000609562827 203187609000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 63234285 536870912 24973259072661432 36028797018963968 203187609 1000000000000000 rfl rfl rfl rfl (ep809 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep811 := nat_lit 31431193299013864345567232

noncomputable def ep812 := nat_lit 77371252455336267181195264

noncomputable def ep813 := nat_lit 45034904444160016490646325882806751794902513141218183930183153504499285850839678818420872891363630625

noncomputable def ep814 := nat_lit 198427385752314841779073402044110610264839530770632232232545909413510936087367383754837115419531442913280

noncomputable def ep815 := nat_lit 405591193827292363357418367385919948569579573024281584793190665641474126880354018528785625390625

noncomputable def ep816 := nat_lit 117947902587057656145009227206184772735304136050548442408866213060229948175041352522691334776844590625

noncomputable def ep817 := nat_lit 3637835405459105432616345704142027854855391397461590924263341672581033828268402035505347116024743120076800

noncomputable def ep818 := BSN.sin_dyadic_bound_f 893328242995 2199023255552 3 2 1073741824 406772069 ep813 ep814 ep815 ep816 ep817 ep815 424296496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 893328242995) (BSN.sinEvenQ 2199023255552) 0 2 ep813 ep814 ep815 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 893328242995) (BSN.sinOddQ 2199023255552) 0 2 ep816 ep817 ep815 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz403 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 49973674251) (@Nat.cast Real Real.instNatCast 536870912))

noncomputable def ep819 := @Enclosure.Real.IsNear.cos_image qz118 qz403 Bool.false 49973674251 536870912 225 1073741824 Bool.false 424296496 1073741824 1 203187609 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 104802390903465700347 1125899906842624000 10591006455879900757 ep806 49973674251 536870912 225 1073741824 (ep810 rfl) rfl) (Enclosure.sfrac_false_div 49973674251 536870912) (BSN.cos_reduce3 qz403 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep811) (@Nat.cast Real Real.instNatCast ep812)) 226375608064910080 72057594037927936 Bool.false 424296496 1073741824 14 1000000000000000 406375218 203187609 (BSN.sin_reduce_arg_pos_rat_q3 49973674251 536870912 226375608064910080 72057594037927936 14 ep811 ep812 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 424296496 1073741824 ep811 ep812 893328242995 2199023255552 406772069 406375218 (ep818 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep820 := nat_lit 25019571620619487958076117676389255850478538224931446308583882253906555016745101723130942177702190625

noncomputable def ep821 := nat_lit 22047487305812760197674822449345623362759947863403581359171767712612326231929709306093012824392382545920

noncomputable def ep822 := nat_lit 75057903679470809289501638192432995711538475515648290362582060380388382101981544461355768961855790625

noncomputable def ep823 := nat_lit 992136928761574208895367010220553051324197653853161161162729547067554680436836918774185577097657214566400

noncomputable def ep824 := BSN.cos_dyadic_bound_f 893328242995 2199023255552 3 2 1073741824 406772069 ep820 ep821 ep815 ep822 ep823 ep815 986353885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 893328242995) (BSN.cosEvenQ 2199023255552) 0 2 ep820 ep821 ep815 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 893328242995) (BSN.cosOddQ 2199023255552) 0 2 ep822 ep823 ep815 rfl rfl rfl rfl) rfl rfl

noncomputable def ep825 := @Enclosure.Real.IsNear.sin_image qz118 qz403 Bool.false 49973674251 536870912 225 1073741824 Bool.true 986353885 1073741824 1 203187609 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 104802390903465700347 1125899906842624000 10591006455879900757 ep806 49973674251 536870912 225 1073741824 (ep810 rfl) rfl) (Enclosure.sfrac_false_div 49973674251 536870912) (BSN.sin_reduce3 qz403 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep811) (@Nat.cast Real Real.instNatCast ep812)) 226375608064910080 72057594037927936 Bool.false 986353885 1073741824 14 1000000000000000 406375218 203187609 (BSN.sin_reduce_arg_pos_rat_q3 49973674251 536870912 226375608064910080 72057594037927936 14 ep811 ep812 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 986353885 1073741824 ep811 ep812 893328242995 2199023255552 406772069 406375218 (ep824 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep826 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz400 qz115) (@HMul.hMul Real Real Real qz0 qz400 qz116) Bool.false 13019670572415 72057594037927936 54592278988373099 ep753 Bool.false 484265235149025 1152921504606846976 223387654968439099 ep802 (@Enclosure.Real.IsNear.mulLit_ff qz400 qz115 490965 1073741824 1 1073741824 26518531 67108864 46790953849 218171033901858816 13019670572415 72057594037927936 54592278988373099 ep753 (@Enclosure.Real.IsNear.recentre' qz400 Bool.false 490965 1073741824 1 1073741824 490965 1073741824 1 1073741824 (ep805 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz115 Bool.false 424296496 1073741824 46790953849 218171033901858816 26518531 67108864 46790953849 218171033901858816 (ep819 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz400 qz116 490965 1073741824 1 1073741824 986353885 1073741824 46790953849 218171033901858816 484265235149025 1152921504606846976 223387654968439099 ep802 (@Enclosure.Real.IsNear.recentre' qz400 Bool.false 490965 1073741824 1 1073741824 490965 1073741824 1 1073741824 (ep805 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz119 Bool.true 986353885 1073741824 46790953849 218171033901858816 (@Enclosure.Real.IsNear.recentre' qz119 Bool.true 986353885 1073741824 46790953849 218171033901858816 986353885 1073741824 46790953849 218171033901858816 (ep825 rfl rfl) rfl)) rfl)

noncomputable def ep827 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216 592089357223 5625000000 0 1 484265235149025 1152921504606846976 223387654968439099 ep802 ep749

noncomputable def ep828 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 168214859 15000000 0 1 Bool.false 592089357223 5625000000 0 1 ep800

noncomputable def ep829 := @Enclosure.Complex.IsNear.im_isNear qz204 Bool.false 13019670572415 72057594037927936 54592278988373099 ep753 Bool.false 484265235149025 1152921504606846976 223387654968439099 ep802

noncomputable def ep830 := nat_lit 37577122882856632488372041

noncomputable def ep831 := nat_lit 3513890458286215831234805760000000

noncomputable def ep832 := nat_lit 27021597764222976000000000

noncomputable def ep833 := nat_lit 32323507375564516877414544077

noncomputable def ep834 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215) 1086141443322601124833 230584300921369395200000 ep830 ep831 513920558698427054986903 ep832 ep833

noncomputable def ep835 := nat_lit 658854460928665468356526080000000000

noncomputable def ep836 := nat_lit 147851289953112302683949950249322724039065600000

noncomputable def ep837 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216 168214859 15000000 0 1 484265235149025 1152921504606846976 223387654968439099 ep802 1086141443322601124833

noncomputable def ep838 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215 592089357223 5625000000 0 1 13019670572415 72057594037927936 54592278988373099 ep753 513920558698427054986903

noncomputable abbrev qz404 := (@ep804 ep802 (BSN.cpow_neg_s_sub_mk qz24 42364 1000 9 3 4782969 qz25 rfl EMRow08.d16) ep826)

noncomputable def ep839 := ep746 (@ep751 ep740 ep752 ep737 ep738 ep739 ep740 (@ep754 72057594037927936000000 ep747 ep748 ep801 (ep803 qz404) rfl) (@ep827 ep738 ep750 ep740 ep828 (ep829 qz404) rfl) rfl rfl) (@ep834 ep835 ep836 ep742 ep743 ep744 ep740 (@ep837 230584300921369395200000 ep830 ep831 ep801 (ep829 qz404) rfl) (@ep838 ep832 ep833 ep835 ep828 (ep803 qz404) rfl) rfl rfl)

noncomputable def ep840 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) ep742 ep743 ep744 ep740 ep742 ep743 ep744

noncomputable def ep841 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204) Bool.true ep737 ep738 ep739 ep740 Bool.false ep742 ep743 ep744

noncomputable def ep842 := @ep708 289567737769759 492581209243648 781858277 492581209243648 (@ep709 1 458752 (ep710 (@ep711 131072 1 131072 (ep712 (@ep713 451739624 56467453 31250 0 1 (ep717 rfl) (ep720 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep721 131 1073741824 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (@ep722 131 1073741824 51971603 1073741824 131 1073741824 (@ep727 25985736 25985867 536870912 (@ep733 ep734 ep735 ep731 ep736 ep723 ep724 ep725 ep726 (@ep741 ep740 ep728 ep729 ep730 ep731 (@ep745 ep740 ep839) (@ep745 ep740 ep839) rfl) (@ep840 ep740 ep732 ep734 ep735 ep731 (@ep841 ep740 ep839) (@ep841 ep740 ep839) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow08.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 9))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))) Bool.false 298197775347487 492581209243648 391606232333 4433230883192832 := ep706 (ep707 ep842) rfl rfl

theorem EMRow08.d18 : @Eq Nat (Nat.pow 10 (Nat.succ (Nat.mul 2 3))) 10000000 := @Eq.refl Nat 10000000

noncomputable abbrev qz441 := (@HAdd.hAdd Complex Complex Complex qz443 qz449 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz405 := qz441

noncomputable abbrev qz227 := (@HDiv.hDiv Real Real Real qz257 (@Norm.norm Complex Complex.instNorm qz405) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz349) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz406 := (@HPow.hPow Complex Complex Complex qz421 qz439 (@HSub.hSub Complex Complex Complex qz427 qz435 qz423))

noncomputable abbrev qz228 := qz406

noncomputable def ep843 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) 30152097 536870912 1554007 14495514624 268446822270857 492581209243648 506292643

noncomputable def ep844 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 10)) 123 8192 1 221184 245139 65536 197 32768 30152097 536870912

noncomputable def ep845 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 10)) (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 10)) (Complex.re (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 10)) (Complex.im (zetaApproximant qz141 1 10))))) Bool.false 245139 65536 197 32768

noncomputable def ep846 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 10)) (Complex.re (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 10)) (Complex.im (zetaApproximant qz141 1 10))))) Bool.false 490278 131072 788 131072

noncomputable def ep847 := nat_lit 247256532675922957878789859313309082937

noncomputable def ep848 := nat_lit 17671798861332905811532554908467200000

noncomputable def ep849 := nat_lit 7916174119439528170491354421258844671716103765933642331

noncomputable def ep850 := nat_lit 176178819297247740109394854764748913840969434005504000000

noncomputable def ep851 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 10)) (Complex.re (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 10)) (Complex.im (zetaApproximant qz141 1 10)))) ep847 ep848 ep849 ep850 244745 245533

noncomputable def ep852 := nat_lit 2570192919857684176615713298698473571014743232569

noncomputable def ep853 := nat_lit 183695844097707967664817594476195494232064000000

noncomputable def ep854 := nat_lit 7900544051245229129911149938846446954994204314178810587

noncomputable def ep855 := nat_lit 102429409597085428143916857427444064445361

noncomputable def ep856 := nat_lit 5102662336047443546244933179894319284224000000

noncomputable def ep857 := nat_lit 122109907767961254532847518846857161889839466834623

noncomputable def ep858 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 10)) (Complex.re (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 10)) (Complex.im (zetaApproximant qz141 1 10))) ep852 ep853 ep854 ep850 ep855 ep856 ep857

noncomputable def ep859 := nat_lit 1376397025759747969604647302849600889382573703168000000

noncomputable def ep860 := nat_lit 13114845424390466961328943909072958715051980619613094012238115772388657310850030826946560000000

noncomputable def ep861 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz141 1 10)) (Complex.re (zetaApproximant qz141 1 10)) ep461 428597531604777172992000 ep462 ep463 ep461 428597531604777172992000 ep462 ep463 ep852

noncomputable def ep862 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz141 1 10)) (Complex.im (zetaApproximant qz141 1 10)) 320045949196494952519 71432921934129528832000 ep572 ep573 320045949196494952519 71432921934129528832000 ep572 ep573 ep855

noncomputable def ep863 := @ep843 492581209243648 158973646697548679741440 296111491876745 492581209243648 1439477539889 13299692649578496 (@ep844 1554007 14495514624 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz205)) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow08.d13 EMRow08.d14 rfl) (ep686 rfl)) (ep845 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz141 1 10)) (@ep846 245139 65536 197 32768 (@ep851 65536 (@ep858 ep859 ep860 ep847 ep848 ep849 ep850 (@ep861 ep853 ep854 ep850 ep667 ep667 rfl) (@ep862 ep856 ep857 ep859 ep675 ep675 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz229 := (@Norm.norm Complex Complex.instNorm qz405)

noncomputable def ep864 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz229 qz395) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) Bool.false 268446822270857 492581209243648 506292643 492581209243648 (BSN.zrb_shape_eq qz229 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) qz143 3)

noncomputable def ep865 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz229 qz395) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) 5993549 458752 1 458752 44789293 1073741824 77 1073741824

noncomputable def ep866 := @Enclosure.Real.IsNear.mulLit_ff qz229 qz395 5993549 131072 1 131072 2 7 0 1 5993549 458752

noncomputable abbrev qz407 := (Complex.re qz441)

noncomputable abbrev qz408 := (Complex.im qz441)

noncomputable abbrev qz230 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz254 qz407 qz407) (@HMul.hMul Real Real Real qz254 qz408 qz408))

noncomputable abbrev qz231 := qz405

noncomputable def ep867 := @Enclosure.Real.IsNear.of_eq qz229 (Real.sqrt qz230) Bool.false 5993549 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz231)

noncomputable def ep868 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz230) Bool.false 5993549 131072 1 131072 5993549

noncomputable def ep869 := @Enclosure.Real.IsNear.sqrt_image qz230 2090971649 1000000 0 1 2996774 2996775 65536

noncomputable abbrev qz232 := (@HMul.hMul Real Real Real qz254 qz407 qz407)

noncomputable abbrev qz233 := (@HMul.hMul Real Real Real qz254 qz408 qz408)

noncomputable def ep870 := @Enclosure.Real.IsNear.addLit_ff qz232 qz233 49 4 0 1 2078721649 1000000 0 1

noncomputable abbrev qz234 := qz407

noncomputable def ep871 := @Enclosure.Real.IsNear.mulLit_ff qz234 qz234 7 2 0 1 7 2 0 1 49 4

noncomputable def ep872 := @Enclosure.Complex.IsNear.of_eq qz231 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz143) Bool.false 7 2 0 1 Bool.false 45593 1000 0 1 (BSN.s_add_nat_mk qz143 Bool.false 45593 1000 3 qz144)

noncomputable abbrev qz235 := (ep872 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz351 Bool.false 7 2 0 1 Bool.false 45593 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz353))

noncomputable def ep873 := @ep871 0 1 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 7 2 0 1 Bool.false 45593 1000 0 1 qz235)

noncomputable def ep874 := ep873 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 7 2 0 1 Bool.false 45593 1000 0 1 qz235)

noncomputable abbrev qz236 := qz408

noncomputable def ep875 := @Enclosure.Real.IsNear.mulLit_ff qz236 qz236 45593 1000 0 1 45593 1000 0 1 2078721649 1000000

noncomputable def ep876 := @ep875 0 1 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 7 2 0 1 Bool.false 45593 1000 0 1 qz235)

noncomputable def ep877 := ep876 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 7 2 0 1 Bool.false 45593 1000 0 1 qz235)

noncomputable def ep878 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))))) Bool.false 44789293 1073741824

noncomputable def ep879 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))))) Bool.false 89578586 2147483648

noncomputable def ep880 := nat_lit 19183733071824860758406337605227748104146822860424930899441

noncomputable def ep881 := nat_lit 11025148688238406216213337280789290051174400000000000000000000

noncomputable def ep882 := nat_lit 24544278786377632973538542087182008362700556605253248912984480858227

noncomputable def ep883 := nat_lit 4130464120619610763336651903750764672737492336640000000000000000000000000000

noncomputable def ep884 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))) ep880 ep881 ep882 ep883

noncomputable def ep885 := nat_lit 2918560439339174921619525328672692055892089490101373209

noncomputable def ep886 := nat_lit 1722679482537250971283333950123326570496000000000000000000

noncomputable def ep887 := nat_lit 5737283157578759024542292146024294635146841111910923928914418050169

noncomputable def ep888 := nat_lit 1032616030154902690834162975937691168184373084160000000000000000000000000000

noncomputable def ep889 := nat_lit 504946260054141260041375501722518946437450123776142361841

noncomputable def ep890 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) ep885 ep886 ep887 ep888 ep889

noncomputable def ep891 := nat_lit 1595146156062596875369373503084829822113192157609553197326808657551

noncomputable def ep892 := nat_lit 33047423361303999151691678865036094402978671862648569709300333963590468456857290931035839173492736000000000000000000

noncomputable def ep893 := nat_lit 1708379477557364864758577797

noncomputable def ep894 := nat_lit 41505174165846491136000000000

noncomputable def ep895 := nat_lit 2168824429232316005419947749987

noncomputable def ep896 := nat_lit 32134343468552499599769600000000000000

noncomputable def ep897 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) ep893 ep894 ep895 ep896 ep893 ep894 ep895

noncomputable def ep898 := nat_lit 22471009324330343930065701721

noncomputable def ep899 := nat_lit 3320413933267719290880000000000

noncomputable def ep900 := nat_lit 1833748582497802511521309258099

noncomputable def ep901 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228) Bool.true ep893 ep894 ep895 ep896 Bool.true ep898 ep899 ep900

noncomputable def ep902 := nat_lit 64268686937104999199539200000000000000

noncomputable def ep903 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228 Bool.true ep893 ep894 ep895 ep896 Bool.true ep898 ep899 ep900 ep902

noncomputable def ep904 := nat_lit 2351523146262456487073491

noncomputable def ep905 := nat_lit 2213609288845146193920000000

noncomputable def ep906 := nat_lit 93571072572522506169658729

noncomputable def ep907 := nat_lit 42845791291403332799692800000000000

noncomputable def ep908 := nat_lit 6657153674259775222503799363

noncomputable def ep909 := nat_lit 166020696663385964544000000000

noncomputable def ep910 := nat_lit 2098646124802924125792703703237

noncomputable abbrev qz237 := (Complex.re qz406)

noncomputable abbrev qz238 := (Complex.im qz406)

noncomputable def ep911 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238) ep904 ep905 ep906 ep907 ep908 ep909 ep910

noncomputable def ep912 := nat_lit 15126738721573603322652386652100904403227073576960000000

noncomputable def ep913 := nat_lit 89262065190423609999360000

noncomputable def ep914 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237 6234914947 480000000 0 1 377154005507953 4611686018427387904 15007594067910307 ep913 ep904

noncomputable def ep915 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) 6234914947 480000000 0 1 0 1 0 1 6234914947

noncomputable def ep916 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 18704744841 2000000 0 1 6234914947 480000000 0

noncomputable abbrev qz409 := (@HAdd.hAdd Complex Complex Complex qz420 qz434 qz424)

noncomputable abbrev qz239 := qz409

noncomputable def ep917 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz51 (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) qz239) Bool.true 18704744841 2000000 0 1 Bool.true 94512996392857 1000000000 0 1

noncomputable abbrev qz240 := (Complex.re qz409)

noncomputable abbrev qz241 := (Complex.im qz409)

noncomputable def ep918 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz240) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz241) 2077971649 400000 0 1 2078721649 500000 0 1

noncomputable def ep919 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz240 2077971649 1000000 0 1 5 2 0 1 2077971649 400000

noncomputable abbrev qz410 := (@HAdd.hAdd Complex Complex Complex qz420 qz434 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz242 := qz410

noncomputable def ep920 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz51 (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) qz242) Bool.true 2077971649 1000000 0 1 Bool.false 45593 500 0 1

noncomputable abbrev qz243 := (Complex.re qz410)

noncomputable abbrev qz244 := (Complex.im qz410)

noncomputable def ep921 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz243) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz244) 3 4 0 1 2078721649 1000000 0 1

noncomputable def ep922 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz243 1 2 0 1 3 2 0 1 3 4

noncomputable def ep923 := @ep922 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep632)

noncomputable def ep924 := @Enclosure.Complex.IsNear.of_eq qz242 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz143) Bool.false 3 2 0 1 Bool.false 45593 1000 0 1 (BSN.s_add_nat_mk qz143 Bool.false 45593 1000 1 qz144)

noncomputable abbrev qz245 := (ep924 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz351 Bool.false 3 2 0 1 Bool.false 45593 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz353))

noncomputable def ep925 := ep923 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 3 2 0 1 Bool.false 45593 1000 0 1 qz245)

noncomputable def ep926 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz244 45593 1000 0 1 45593 1000 0 1 2078721649 1000000

noncomputable def ep927 := @ep926 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep632)

noncomputable def ep928 := ep927 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 3 2 0 1 Bool.false 45593 1000 0 1 qz245)

noncomputable def ep929 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) qz242 Bool.true 2077971649 1000000 0 1 Bool.false 45593 500 0 1 (@ep921 8311886596 2077971649 1000000 0 1 (ep925 rfl) (ep928 rfl) rfl rfl)

noncomputable def ep930 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz244) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz243) 45593 2000 0 1 136779 2000 0 1

noncomputable def ep931 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz244 1 2 0 1 45593 1000 0 1 45593 2000

noncomputable def ep932 := @ep931 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep632)

noncomputable def ep933 := ep932 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 3 2 0 1 Bool.false 45593 1000 0 1 qz245)

noncomputable def ep934 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz243 45593 1000 0 1 3 2 0 1 136779 2000

noncomputable def ep935 := @ep934 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep632)

noncomputable def ep936 := ep935 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 3 2 0 1 Bool.false 45593 1000 0 1 qz245)

noncomputable abbrev qz246 := (ep920 (BSN.ascPochhammer_succ_eval_c 1 2 qz349 rfl) (ep929 (@ep930 364744000 45593 500 0 1 (ep933 rfl) (ep936 rfl) rfl rfl)))

noncomputable def ep937 := @ep919 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2077971649 1000000 0 1 Bool.false 45593 500 0 1 qz246)

noncomputable def ep938 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz143) Bool.false 5 2 0 1 Bool.false 45593 1000 0 1 (BSN.s_add_nat_mk qz143 Bool.false 45593 1000 2 qz144)

noncomputable abbrev qz247 := (ep938 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz351 Bool.false 5 2 0 1 Bool.false 45593 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz353))

noncomputable def ep939 := ep937 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 5 2 0 1 Bool.false 45593 1000 0 1 qz247)

noncomputable def ep940 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz241 45593 500 0 1 45593 1000 0 1 2078721649 500000

noncomputable def ep941 := @ep940 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2077971649 1000000 0 1 Bool.false 45593 500 0 1 qz246)

noncomputable def ep942 := ep941 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 5 2 0 1 Bool.false 45593 1000 0 1 qz247)

noncomputable def ep943 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) qz239 Bool.true 18704744841 2000000 0 1 Bool.true 94512996392857 1000000000 0 1 (@ep918 1870474484100000 18704744841 2000000 0 1 (ep939 rfl) (ep942 rfl) rfl rfl)

noncomputable def ep944 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz240) 94740961392857 1000000000 0 1 45593 200 0 1

noncomputable def ep945 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz241 2077971649 1000000 0 1 45593 1000 0 1 94740961392857 1000000000

noncomputable def ep946 := @ep945 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2077971649 1000000 0 1 Bool.false 45593 500 0 1 qz246)

noncomputable def ep947 := ep946 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 5 2 0 1 Bool.false 45593 1000 0 1 qz247)

noncomputable def ep948 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz240 45593 500 0 1 5 2 0 1 45593 200

noncomputable def ep949 := @ep948 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2077971649 1000000 0 1 Bool.false 45593 500 0 1 qz246)

noncomputable def ep950 := ep949 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 5 2 0 1 Bool.false 45593 1000 0 1 qz247)

noncomputable abbrev qz248 := (ep917 (BSN.ascPochhammer_succ_eval_c 2 3 qz349 rfl) (ep943 (@ep944 18902599278571400 94512996392857 1000000000 0 1 (ep947 rfl) (ep950 rfl) rfl rfl)))

noncomputable def ep951 := @ep916 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep757) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 18704744841 2000000 0 1 Bool.true 94512996392857 1000000000 0 1 qz248)

noncomputable def ep952 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 94512996392857 1000000000 0 1 0 1 0

noncomputable def ep953 := @ep952 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep757) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 18704744841 2000000 0 1 Bool.true 94512996392857 1000000000 0 1 qz248)

noncomputable def ep954 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) 94512996392857 720000000000 0 1 0 1 0 1 94512996392857

noncomputable def ep955 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 94512996392857 1000000000 0 1 94512996392857 720000000000 0

noncomputable def ep956 := @ep955 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep757) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 18704744841 2000000 0 1 Bool.true 94512996392857 1000000000 0 1 qz248)

noncomputable def ep957 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 18704744841 2000000 0 1 0 1 0

noncomputable def ep958 := @ep957 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep757) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 18704744841 2000000 0 1 Bool.true 94512996392857 1000000000 0 1 qz248)

noncomputable def ep959 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 6234914947 480000000 0 1 Bool.false 94512996392857 720000000000 0 1 (@ep915 6234914947 480000000 0 1 (ep951 rfl) (ep953 rfl) rfl rfl) (@ep954 94512996392857 720000000000 0 1 (ep956 rfl) (ep958 rfl) rfl rfl)

noncomputable def ep960 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 6234914947 480000000 0 1 Bool.false 94512996392857 720000000000 0 1 ep959

noncomputable def ep961 := nat_lit 44631032595211804999680000

noncomputable def ep962 := @Enclosure.Complex.IsNear.re_isNear qz228 Bool.true 377154005507953 4611686018427387904 15007594067910307 ep913 Bool.false 352181918272295 1152921504606846976 22204841713827341 ep961

noncomputable abbrev qz411 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10000000)))

noncomputable def ep963 := @Enclosure.Complex.IsNear.of_eq qz228 (Complex.mk (@HMul.hMul Real Real Real qz0 qz411 qz191) (@HMul.hMul Real Real Real qz0 qz411 qz192)) Bool.true 377154005507953 4611686018427387904 15007594067910307 ep913 Bool.false 352181918272295 1152921504606846976 22204841713827341

noncomputable abbrev qz412 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10000000))

noncomputable abbrev qz413 := (@Nat.cast Real Real.instNatCast 10000000)

noncomputable def ep964 := @Enclosure.Real.IsNear.inv_image qz412 6790939565647 2147483648 1 2147483648 339546 339547 1073741824 (@Enclosure.Real.IsNear.of_eq qz412 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz413 qz26)) Bool.false 6790939565647 2147483648 1 2147483648 (BSN.sqrt_natCast_div_one 10000000) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz413 qz26)) Bool.false 6790939565647 2147483648 1 2147483648 6790939565647 2147483648 1 2147483648 (BSN.sqrt_enclosure 10000000 1 3395469782823 3395469782824 1073741824 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep965 := nat_lit 89076946236074554071973888

noncomputable def ep966 := nat_lit 38685626227668133590597632

noncomputable def ep967 := BSN.log_dyadic_bound 2 18 5 4 10413862744320 1073741824 309690000 43175675904 26880 239598563 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 18) 0 4 43175675904 10413862744320 26880 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep968 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz193 45593 1000 0 1 10369921363433189 4503599627370496 100000092907 30969000000000000000 472795824723009386077 4503599627370496000 4559304235908851 30969000000000000000000 qz145 (BSN.isNear_log_sfrac 10 1 10369921363433189 4503599627370496 100000092907 30969000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz386) Bool.false ep965 ep966 1000000929070000 309690000000000000000000 10369921363433189 4503599627370496 100000092907 30969000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 239598563 1073741824 24973259072661432 36028797018963968 309690000 1000000000000000 rfl rfl rfl rfl (ep967 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep969 := nat_lit 405179180618912225948598272

noncomputable def ep970 := nat_lit 309485009821345068724781056

noncomputable def ep971 := nat_lit 3076327268869164504033066547719080536010798031469910807115772959410230666914684011807105160106275194238542828407932797391691862736964302700844298105718287062881

noncomputable def ep972 := nat_lit 25087349417715593433012958174142958689126641386910427249058555817347792676670613748293986999300093003550818609852734049752458890129433227026772000655283952025600

noncomputable def ep973 := nat_lit 1328029907734088302198831062731064843191428285445214817021316561139973897243061058903172888647087789590683063517894931952356482444584804849412168010127201

noncomputable def ep974 := nat_lit 18641325702404866548841656641088826685642747430440909267606269433606788268702708309711546022368272907838664826684972032484108850735896369422352784665401416177505

noncomputable def ep975 := nat_lit 2282948797012119002404179193847009240710524366208848879664328579378649133577025851094752816936308463323124493496598798527473759001778423659436252059630839634329600

noncomputable def ep976 := BSN.cos_dyadic_bound_f 5757942469399 4398046511104 4 3 2147483648 619984864 ep971 ep972 ep973 ep974 ep975 ep973 555379021 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 5757942469399) (BSN.cosEvenQ 4398046511104) 0 3 ep971 ep972 ep973 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 5757942469399) (BSN.cosOddQ 4398046511104) 0 3 ep974 ep975 ep973 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz414 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 225446617471) (@Nat.cast Real Real.instNatCast 2147483648))

noncomputable def ep977 := @Enclosure.Real.IsNear.cos_image qz194 qz414 Bool.false 225446617471 2147483648 317 2147483648 Bool.true 555379021 2147483648 1 309690000 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 472795824723009386077 4503599627370496000 4559304235908851 30969000000000000000000 225446617471 2147483648 317 2147483648 (ep968 rfl) rfl) (Enclosure.sfrac_false_div 225446617471 2147483648) (BSN.cos_reduce2 qz414 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep969) (@Nat.cast Real Real.instNatCast ep970)) 226375608064910080 72057594037927936 Bool.false 555379021 2147483648 16 1000000000000000 619380000 309690000 (BSN.sin_reduce_arg_pos_rat_q2 225446617471 2147483648 226375608064910080 72057594037927936 16 ep969 ep970 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 555379021 2147483648 ep969 ep970 5757942469399 4398046511104 619984864 619380000 (ep976 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep978 := nat_lit 7992243155150108977017580189464801196659310025848919946212250952128282481054620366445866740856695348166311511759447897627126798032732604905624162637978270914401

noncomputable def ep979 := nat_lit 326135542430302714629168456263858462958646338029835554237761225625521304796717978727821830990901209046160641928085542646781965571682631951348036008518691376332800

noncomputable def ep980 := nat_lit 39937234208164612107425406156527747544604161967011218295868833120843138233466039659750209156175792273905758184896647303303752621119313836353670663855731176068961

noncomputable def ep981 := nat_lit 11414743985060595012020895969235046203552621831044244398321642896893245667885129255473764084681542316615622467482993992637368795008892118297181260298154198171648000

noncomputable def ep982 := BSN.sin_dyadic_bound_f 5757942469399 4398046511104 4 3 2147483648 619984864 ep978 ep979 ep973 ep980 ep981 ep973 2074425260 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 5757942469399) (BSN.sinEvenQ 4398046511104) 0 3 ep978 ep979 ep973 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 5757942469399) (BSN.sinOddQ 4398046511104) 0 3 ep980 ep981 ep973 rfl rfl rfl rfl) rfl rfl

noncomputable def ep983 := @Enclosure.Real.IsNear.sin_image qz194 qz414 Bool.false 225446617471 2147483648 317 2147483648 Bool.true 2074425260 2147483648 1 309690000 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 472795824723009386077 4503599627370496000 4559304235908851 30969000000000000000000 225446617471 2147483648 317 2147483648 (ep968 rfl) rfl) (Enclosure.sfrac_false_div 225446617471 2147483648) (BSN.sin_reduce2 qz414 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep969) (@Nat.cast Real Real.instNatCast ep970)) 226375608064910080 72057594037927936 Bool.false 2074425260 2147483648 16 1000000000000000 619380000 309690000 (BSN.sin_reduce_arg_pos_rat_q2 225446617471 2147483648 226375608064910080 72057594037927936 16 ep969 ep970 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2074425260 2147483648 ep969 ep970 5757942469399 4398046511104 619984864 619380000 (ep982 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep984 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz411 qz191) (@HMul.hMul Real Real Real qz0 qz411 qz192) Bool.true 377154005507953 4611686018427387904 15007594067910307 ep913 Bool.false 352181918272295 1152921504606846976 22204841713827341 ep961 (@Enclosure.Real.IsNear.mulLit_ft qz411 qz191 679093 2147483648 1 2147483648 555379021 2147483648 6269950853 41565888184320000 377154005507953 4611686018427387904 15007594067910307 ep913 (@Enclosure.Real.IsNear.recentre' qz411 Bool.false 679093 2147483648 1 2147483648 679093 2147483648 1 2147483648 (ep964 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz191 Bool.true 555379021 2147483648 100319213648 665054210949120000 555379021 2147483648 6269950853 41565888184320000 (ep977 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz411 qz192 679093 2147483648 1 2147483648 518606315 536870912 6269950853 41565888184320000 352181918272295 1152921504606846976 22204841713827341 ep961 (@Enclosure.Real.IsNear.recentre' qz411 Bool.false 679093 2147483648 1 2147483648 679093 2147483648 1 2147483648 (ep964 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz195 Bool.true 518606315 536870912 6269950853 41565888184320000 (@Enclosure.Real.IsNear.recentre' qz195 Bool.true 2074425260 2147483648 100319213648 665054210949120000 518606315 536870912 6269950853 41565888184320000 (ep983 rfl rfl) rfl)) rfl)

noncomputable def ep985 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238 94512996392857 720000000000 0 1 352181918272295 1152921504606846976 22204841713827341 ep961 ep908

noncomputable def ep986 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 6234914947 480000000 0 1 Bool.false 94512996392857 720000000000 0 1 ep959

noncomputable def ep987 := @Enclosure.Complex.IsNear.im_isNear qz228 Bool.true 377154005507953 4611686018427387904 15007594067910307 ep913 Bool.false 352181918272295 1152921504606846976 22204841713827341 ep961

noncomputable def ep988 := nat_lit 110680464442257309696000000

noncomputable def ep989 := nat_lit 138445299497311184978165927

noncomputable def ep990 := nat_lit 21422895645701666399846400000000000

noncomputable def ep991 := nat_lit 35645955162124730999025891721

noncomputable def ep992 := nat_lit 1418412684005868956586811477099

noncomputable def ep993 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237) 439164861259812902298673 ep988 ep989 ep990 ep991 ep899 ep992

noncomputable def ep994 := nat_lit 2487101748503177085391324040255139355651857186816000000

noncomputable def ep995 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238 6234914947 480000000 0 1 352181918272295 1152921504606846976 22204841713827341 ep961 439164861259812902298673

noncomputable def ep996 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237 94512996392857 720000000000 0 1 377154005507953 4611686018427387904 15007594067910307 ep913 ep991

noncomputable abbrev qz415 := (@ep963 ep961 (BSN.cpow_neg_s_sub_mk qz143 45593 1000 10 3 10000000 qz144 rfl EMRow08.d18) ep984)

noncomputable def ep997 := ep903 (@ep911 ep896 ep912 ep893 ep894 ep895 ep896 (@ep914 ep905 ep906 ep907 ep960 (ep962 qz415) rfl) (@ep985 ep909 ep910 ep896 ep986 (ep987 qz415) rfl) rfl rfl) (@ep993 ep902 ep994 ep898 ep899 ep900 ep902 (@ep995 ep988 ep989 ep990 ep960 (ep987 qz415) rfl) (@ep996 ep899 ep992 ep902 ep986 (ep962 qz415) rfl) rfl rfl)

noncomputable def ep998 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) ep898 ep899 ep900 ep902 ep898 ep899 ep900

noncomputable def ep999 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228) Bool.true ep893 ep894 ep895 ep896 Bool.true ep898 ep899 ep900

noncomputable def ep1000 := @ep865 268446822270857 492581209243648 506292643 492581209243648 (@ep866 1 458752 (ep867 (@ep868 131072 1 131072 (ep869 (@ep870 8363886596 2090971649 1000000 0 1 (ep874 rfl) (ep877 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep878 77 1073741824 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (@ep879 154 2147483648 44789293 1073741824 77 1073741824 (@ep884 44789216 44789370 1073741824 (@ep890 ep881 ep891 ep883 ep892 ep880 ep881 ep882 ep883 (@ep897 ep896 ep885 ep886 ep887 ep888 (@ep901 ep902 ep997) (@ep901 ep902 ep997) rfl) (@ep998 ep902 ep889 ep881 ep891 ep883 (@ep999 ep902 ep997) (@ep999 ep902 ep997) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow08.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))) Bool.false 296111491876745 492581209243648 1439477539889 13299692649578496 := ep863 (ep864 ep1000) rfl rfl

noncomputable def EMRow08.d20 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz416 := (EMRow08.d3 qz425 qz436 (@Enclosure.dec_le_dec qz425 qz436 42364 1000 45593 1000 (@Eq.refl Real qz425) (@Eq.refl Real qz436) rfl rfl rfl) 9 10 1 1)

noncomputable abbrev qz249 := qz416

noncomputable def ep1001 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz249 (@Enclosure.dec_nonneg qz24 42364 1000 qz25) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 9 rfl)

noncomputable abbrev qz250 := (Zeta.Certificates.ZIntervalEM.fstVal qz416)

noncomputable def ep1002 := @Enclosure.Real.IsNear.pos_val qz250 ep145 ep146

noncomputable def ep1003 := @Enclosure.Real.IsNear.of_eq qz250 (hardyZApproximantEM 1 9 qz24) Bool.false

noncomputable abbrev qz251 := (Zeta.Certificates.ZIntervalEM.sndVal qz416)

noncomputable def ep1004 := BSN.mul_neg_of_pos_neg_r qz250 qz251 (@ep1002 ep147 ep148 (@ep1003 ep145 ep146 ep147 ep148 (@Eq.refl Real (hardyZApproximantEM 1 9 qz24)) EMRow08.d9) rfl rfl rfl)

noncomputable def ep1005 := @Enclosure.Real.IsNear.neg_val qz251 ep446 ep447

noncomputable def ep1006 := @Enclosure.Real.IsNear.of_eq qz251 (hardyZApproximantEM 1 10 qz143) Bool.true

noncomputable def ep1007 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz250) (BSN.hardyZErrorBoundStrong 1 9 qz24)

noncomputable def ep1008 := @Enclosure.norm_gt_of_isNear qz250 (BSN.hardyZErrorBoundStrong 1 9 qz24) Bool.false

noncomputable def ep1009 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 9 qz24) (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 9))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))) Bool.false 298197775347487 492581209243648 391606232333 4433230883192832 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 9))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))))

noncomputable def ep1010 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz251) (BSN.hardyZErrorBoundStrong 1 10 qz143)

noncomputable def ep1011 := @Enclosure.norm_gt_of_isNear qz251 (BSN.hardyZErrorBoundStrong 1 10 qz143) Bool.true

noncomputable def ep1012 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 10 qz143) (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))) Bool.false 296111491876745 492581209243648 1439477539889 13299692649578496 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))))

noncomputable def ep1013 := @List.cons EMRow08.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz249 (ep1001 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 10 rfl) (ep1004 (@ep1005 ep448 ep449 (@ep1006 ep446 ep447 ep448 ep449 (@Eq.refl Real (hardyZApproximantEM 1 10 qz143)) EMRow08.d12) rfl rfl rfl)) (ep1007 (hardyZErrorBoundEM 1 9 qz24) (BSN.hardyZErrorBoundEM_le_strong 1 9 qz24 rfl) (@ep1008 Bool.false ep145 ep146 ep147 ep148 298197775347487 492581209243648 391606232333 4433230883192832 (@ep1003 ep145 ep146 ep147 ep148 (@Eq.refl Real (hardyZApproximantEM 1 9 qz24)) EMRow08.d9) (ep1009 EMRow08.d17) rfl rfl rfl rfl rfl)) (ep1010 (hardyZErrorBoundEM 1 10 qz143) (BSN.hardyZErrorBoundEM_le_strong 1 10 qz143 rfl) (@ep1011 Bool.false ep446 ep447 ep448 ep449 296111491876745 492581209243648 1439477539889 13299692649578496 (@ep1006 ep446 ep447 ep448 ep449 (@Eq.refl Real (hardyZApproximantEM 1 10 qz143)) EMRow08.d12) (ep1012 EMRow08.d19) rfl rfl rfl rfl rfl)))) (@List.nil EMRow08.d0)

noncomputable abbrev qz417 := (@Enclosure.dec_le_dec qz425 qz436 42364 1000 45593 1000 (@Eq.refl Real qz425) (@Eq.refl Real qz436) rfl rfl rfl)

noncomputable abbrev qz252 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1013 (@List.IsChain.singleton EMRow08.d1 EMRow08.d20 (EMRow08.d2 qz267 qz351 qz417))))

noncomputable abbrev qz418 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1014 := And (@Eq (Option Real) (@Option.map qz418 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz418 qz252)) (@Option.some Real qz24))

noncomputable def ep1015 := ep1014 (@Eq (Option Real) (@Option.map qz418 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz418 qz252)) (@Option.some Real qz143))

noncomputable def ep1016 := @And.intro (@Eq Nat (@List.length qz418 qz252) 1) ep1015

noncomputable def ep1017 := @And.intro (@Eq (Option Real) (@Option.map qz418 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz418 qz252)) (@Option.some Real qz24))

noncomputable def ep1018 := @ep1017 (@Eq (Option Real) (@Option.map qz418 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz418 qz252)) (@Option.some Real qz143))

noncomputable abbrev qz253 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1013 (@List.IsChain.singleton EMRow08.d1 EMRow08.d20 (EMRow08.d2 qz267 qz351 qz417)))

theorem EMRow08.d21 : Zeta.Certificates.BatchSpec 1 42364 1000 45593 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz418 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz418 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz418 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz24)) (@Eq (Option Real) (@Option.map qz418 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz418 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz143)))) qz253 (ep1016 (@Eq.refl Nat 1) (ep1018 (@Eq.refl (Option Real) (@Option.some Real qz24)) (@Eq.refl (Option Real) (@Option.some Real qz143))))

theorem solution : Zeta.Certificates.BatchSpec 1 42364 1000 45593 1000 := EMRow08.d21
#print axioms solution
#check solution
