-- Prove2me | solution 1 for RHHeight1000.em_main_0007_0007
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:49:25.212948+00:00
-- url     : https://prove2.me/submissions/164c01f3-3644-4f7f-8d88-ea5a911e2665

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow07.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow07.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow07.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow07.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow07.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz254 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz254

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz255 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz255 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138516661214455 2251799813685248 250000000029717 14858500000000000000 4138516661214455 2251799813685248 250000000029717 14858500000000000000 120446 65536

noncomputable abbrev qz256 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 65536 qz256 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 779317518150410741488063439345657628452599855445271348474342368876423347582876053728679783827237610085654588674605917415063316248867402488514697634436426745

noncomputable def ep10 := nat_lit 13198325246229587668616048586507268161410801335203869857947191811663857046415771104290097871102374067703089877156867761119753226876438075596795543285583799

noncomputable def ep11 := nat_lit 13338205139369261376383149914767634013226508915861991492218067381232119098362059104733250767410551174650894954010182016771344050520336484956804919489535

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 4 3 ep9 131072 59434 ep10 ep11 59189 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 3 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz257 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz257

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138516661214455 2251799813685248 250000000029717 14858500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000118868 59434000000000000000 4138516661214455 2251799813685248 250000000029717 14858500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 59189 131072 24973259072661432 36028797018963968 59434 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 779317518150412560342812906055656980396982394702499187106382620393032652998517540933158707129341055012778793601285942846917973645097155238594697634436426745

noncomputable def ep18 := nat_lit 13198325246229655554962711811363413523213721429909419700721697472804734044169853548961061453892255410264786862895235075217650796661500958924795543285583799

noncomputable def ep19 := nat_lit 13338205139369401582665284895604560799810298653799657073142644093199656832454717421805370366589019475922075211274104314270069372987910244956804919489535

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 4 3 ep17 131072 59434 ep18 ep19 59189 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 3 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138516661214455 2251799813685248 250000000029717 14858500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000118868 59434000000000000000 4138516661214455 2251799813685248 250000000029717 14858500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 59189 131072 24973259072661432 36028797018963968 59434 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz258 := (Real.log (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz3 := qz258

theorem EMRow07.d4 : Enclosure.Real.IsNear qz3 Bool.false 60223 32768 1 32768 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz255) Bool.false 60223 32768 1 32768 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz255) Bool.false 120446 65536 2 65536 60223 32768 1 32768 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 150042 131072 1 59434 150042 131072 1 59434 75021 65536 2 65536 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 5456220599384213465248909714772227496572670538165976141063262914812807742611017753801422503639530882087556452122005170047444298375835020188444492540969863625638808382453421118235702266947370928498132967594635949979551089348001357731941995137847266570621617494261809398531128871567535833923098076891483476912075228072418610430965163137427706923427310178652894498746239459018086669257415154730407592571637957767157504839263249849478535520334507104454135585522664276476675

noncomputable def ep28 := nat_lit 583201912334273870627228188254822588827079241605343036411752047433839590517388190714780374919746279700129906501257101384229175562492847525225536391462542197025353003914524118772974087630067522636400444148635637549655768907025719966434833632093412247469427754039812435067522613541620617101084764807513402584784781490076808276521160080078978009740617112077674385114356333461540984478969922738031393369686631450339262287925718320742111081121726382582016608811398564907105

noncomputable def ep29 := nat_lit 2006268627360805445673839316848610509641534779303135707206598861506426804997221642604762844037348942607248852390277353874343091902420975230792155995982437872051629609224882022549487822374001366578458875613104959699164386313425243185530298109514065278868815165519648262204211929774735225023360668387821809970420335957473972782118680523137645713941929429588852958886338507735711181009301082096313539911189247153419366938656533848809858580689548163599238034961919825

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 10 9 ep27 131072 59434 ep28 ep29 150042 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 9 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 5456220599384260892400251500854699790811159195150212163211869656216336849990273498858157048596616978904240776489460003685239051624059887013466241201881443704542959173524008982544253046253151867013374679201187657749749224297051088632484873343955402287279851789208893474071824987110190207053471018354491495133306616646837230249901879422821128116650397962087630806812522581253210958036113071268120219429850657911869289056672761916619783759890108169949892385522664276476675

noncomputable def ep34 := nat_lit 583201912334279575053067226115417021307550325332234501953544426829928714668898700518418107620762577859683234776628347658361181262145210140271013263714562720079188253110303208819702903278206870150494721073991877864419341163488949363940583288588224434829960190109694548513088121652843287215458036179968684293644459891198769761601084092249455692877745995219003758983943549453190712470220270279351626860119698313725888367584660500821040083453648022042061408811398564907105

noncomputable def ep35 := nat_lit 2006268627360839170887858856494478835319319717359667041823756329478526322484078784125879825811686186445537802910004300367040714583746383402724632880452479311196631191501299191497899488881639138562974769996989848045902383299749709271247360054208480548633525642122514778503225872819822968825602771791453574137145372948950799520945900351638147820910599315255916738483881817718250085827996954508077874524152655659774549924038927632065100609588052048399238034961919825

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 10 9 ep33 131072 59434 ep34 ep35 150042 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 9 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 75021 65536 2 65536 75021 65536 1 32768 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 150042 131072 1 59434 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 150042 131072 59434 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 150042 131072 1 59434 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 150042 131072 59434 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow07.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 32768 := ep37

theorem EMRow07.d6 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow07.d7 : @Eq Nat (Nat.pow 8 1) 8 := @Eq.refl Nat 8

noncomputable def ep38 := nat_lit 197548421233170458301982433999

noncomputable def ep39 := nat_lit 109611994509920508298919936000

noncomputable def ep40 := nat_lit 592040909147485783722115852206302683

noncomputable def ep41 := nat_lit 96798362107178312261701434085474304000

noncomputable abbrev qz435 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz413 := qz435

noncomputable abbrev qz259 := qz413

noncomputable abbrev qz4 := qz259

noncomputable abbrev qz5 := (@instHSub Real Real.instSub)

noncomputable abbrev qz414 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz260 := qz414

noncomputable abbrev qz6 := qz260

noncomputable abbrev qz436 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz437 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz438 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz439 := (Enclosure.sfrac Bool.false 38999 1000)

noncomputable abbrev qz415 := (@HAdd.hAdd Complex Complex Complex qz436 (@HAdd.hAdd Complex Complex Complex qz436 qz437 (@HMul.hMul Complex Complex Complex qz435 Complex.I (@HDiv.hDiv Complex Complex Complex qz438 (↑qz439) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz261 := qz415

noncomputable abbrev qz7 := (Complex.Stirling.logGammaStirling 1 qz261)

noncomputable abbrev qz416 := qz436

noncomputable abbrev qz262 := qz416

noncomputable abbrev qz8 := qz262

noncomputable abbrev qz417 := (@HAdd.hAdd Complex Complex Complex qz436 qz437 (@HMul.hMul Complex Complex Complex qz435 Complex.I (@HDiv.hDiv Complex Complex Complex qz438 (↑qz439) (2 : Complex))))

noncomputable abbrev qz263 := qz417

noncomputable abbrev qz9 := qz263

noncomputable abbrev qz418 := qz439

noncomputable abbrev qz264 := qz418

noncomputable abbrev qz10 := (@HMul.hMul Real Real Real qz254 (@HDiv.hDiv Real Real Real qz257 qz264 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz440 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 38999 1000)))

noncomputable abbrev qz419 := qz440

noncomputable abbrev qz265 := qz419

noncomputable abbrev qz11 := qz265

noncomputable def ep42 := Complex.re (@HMul.hMul Complex Complex Complex qz4 (Complex.exp (@HMul.hMul Complex Complex Complex qz4 Complex.I ↑(@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10))) (zetaApproximant qz11 1 8))

noncomputable def ep43 := @Enclosure.Real.IsNear.of_eq ep42 (@HSub.hSub Real Real Real qz5 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 8))))

noncomputable def ep44 := nat_lit 197551247816788960192113381959

noncomputable def ep45 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 8))) ep44

noncomputable def ep46 := nat_lit 1746654263091963293164795743040672757

noncomputable def ep47 := nat_lit 290395086321534936785104302256422912000

noncomputable def ep48 := nat_lit 2740299862748012707472998400

noncomputable def ep49 := nat_lit 7367116087623514500387953394558823

noncomputable def ep50 := nat_lit 72598771580383734196276075564105728000

noncomputable def ep51 := nat_lit 541341911591343606131039418086595965764145233402632601600

noncomputable def ep52 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 8)) 131071 131072 835127

noncomputable def ep53 := nat_lit 1507207908818800193727929

noncomputable def ep54 := nat_lit 66581200187918454202343707

noncomputable def ep55 := nat_lit 14910917545400883843013017600

noncomputable def ep56 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) Bool.true 131071 131072 835127

noncomputable abbrev qz266 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 514711) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep57 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) qz266 Bool.false 514711 32768 27

noncomputable def ep58 := nat_lit 1460649984000000000000000000

noncomputable def ep59 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) Bool.false 7074134682170366117 450359962737049600 1201005186203672111406407 ep58

noncomputable def ep60 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10 85634572235947473721 2251799813685248000 331805223953672111406407 ep58 2925743979 131072000

noncomputable def ep61 := nat_lit 4636104905307171138437120000

noncomputable def ep62 := nat_lit 121720832000000000000000000

noncomputable def ep63 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 34287718001537743771 1125899906842624000 45632628587088487896167 ep62 Bool.false 85634572235947473721 2251799813685248000

noncomputable def ep64 := @Enclosure.Complex.IsNear.subLitP qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 27596601353156833771 1125899906842624000 43584628586114721240167 ep62 Bool.false 92535808705293033721 2251799813685248000 282653223952211461422407

noncomputable def ep65 := nat_lit 19302269251888753830274362666647552

noncomputable def ep66 := nat_lit 24103989225740304069788593580670976

noncomputable abbrev qz441 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz420 := qz441

noncomputable abbrev qz267 := (@HSub.hSub Complex Complex Complex qz414 qz415 qz420)

noncomputable abbrev qz268 := (Complex.log qz415)

noncomputable abbrev qz12 := (@HSub.hSub Complex Complex Complex qz260 (@HMul.hMul Complex Complex Complex qz259 qz267 qz268) qz261)

noncomputable abbrev qz269 := qz420

noncomputable abbrev qz13 := (@HMul.hMul Complex Complex Complex qz259 qz269 ↑qz258)

noncomputable abbrev qz421 := qz438

noncomputable abbrev qz270 := qz421

noncomputable abbrev qz14 := qz270

noncomputable abbrev qz15 := (@instHMul Nat instMulNat)

noncomputable abbrev qz422 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz271 := qz422

noncomputable abbrev qz16 := qz271

noncomputable abbrev qz17 := qz261

noncomputable abbrev qz272 := (@instHSub Int Int.instSub)

noncomputable abbrev qz18 := qz272

noncomputable abbrev qz273 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz19 := qz273

noncomputable abbrev qz274 := (@instHMul Int Int.instMul)

noncomputable abbrev qz20 := qz274

noncomputable abbrev qz275 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz21 := qz275

noncomputable def ep67 := @Enclosure.Complex.IsNear.of_eq qz7 (@HAdd.hAdd Complex Complex Complex qz8 (@HAdd.hAdd Complex Complex Complex qz8 qz12 qz13) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz16 qz17 (@HSub.hSub Int Int Int qz18 qz19 (@HMul.hMul Int Int Int qz20 qz21 (@Nat.cast Int instNatCastInt k)))))) Bool.true 27596601353156833771

noncomputable def ep68 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz8 qz12 qz13) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz16 qz17 (@HSub.hSub Int Int Int qz18 qz19 (@HMul.hMul Int Int Int qz20 qz21 (@Nat.cast Int instNatCastInt k))))) Bool.true 27597149266622689771 1125899906842624000

noncomputable def ep69 := nat_lit 29631625073139486851338338304

noncomputable def ep70 := nat_lit 9935956802453642048208004710400

noncomputable def ep71 := @ep68 42562781740272259283 118868000000000000000000 Bool.false 18509061125703488357 450359962737049600 5749875002343868941 29717000000000000000000 Bool.false 522531 1073741824 3 1073741824 Bool.true 2264242941 536870912000 38999 1610612736000 Bool.true ep69 27596601353156833771 1125899906842624000 43584628586114721240167 ep62 Bool.false ep70

noncomputable def ep72 := @Enclosure.Complex.IsNear.addLitP qz12 qz13 Bool.true 28631772528490721771 1125899906842624000 40749000001991009283 118868000000000000000000

noncomputable def ep73 := nat_lit 1808606774337384596832256

noncomputable def ep74 := @ep72 Bool.false 18509061125703488357 450359962737049600 5749875002343868941 29717000000000000000000 Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 Bool.true ep73 27597149266622689771 1125899906842624000 42562781740272259283 118868000000000000000000 Bool.false 18509061125703488357 18509061125703488357 450359962737049600

noncomputable abbrev qz22 := (@HMul.hMul Complex Complex Complex qz259 qz267 qz268)

noncomputable def ep75 := @Enclosure.Complex.IsNear.subLitP qz22 qz17 Bool.true 26098497738094817771 1125899906842624000 40749000001991009283 118868000000000000000000 Bool.false 136454276095472935161

noncomputable def ep76 := @ep75 2251799813685248000 5749875002343868941 29717000000000000000000 Bool.false 9000 4000 0 1 Bool.false 77998 4000 0 1 Bool.true 114527090113962887084000 28631772528490721771 1125899906842624000 40749000001991009283 118868000000000000000000 Bool.false 370181222514069767140000 18509061125703488357 450359962737049600 5749875002343868941 29717000000000000000000

noncomputable abbrev qz23 := qz267

noncomputable abbrev qz24 := qz268

noncomputable def ep77 := @Enclosure.Complex.IsNear.mul qz23 qz24 Bool.true 26098497738094817771 1125899906842624000 40749000001991009283 118868000000000000000000 Bool.false 136454276095472935161 2251799813685248000 5749875002343868941

noncomputable abbrev qz25 := (Complex.re qz267)

noncomputable abbrev qz26 := (Complex.re qz268)

noncomputable abbrev qz27 := (Complex.im qz267)

noncomputable abbrev qz28 := (Complex.im qz268)

noncomputable def ep78 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz25 qz26) (@HMul.hMul Real Real Real qz0 qz27 qz28) 23462622446471873 4503599627370496 437500000208019 29717000000000000000 31964153349712786021 1125899906842624000

noncomputable def ep79 := nat_lit 117537184688213554022081749021884416

noncomputable def ep80 := @Enclosure.Real.IsNear.mulLit_ff qz25 qz26 7000 4000 0 1 3351803206638839 1125899906842624 62500000029717 7429250000000000000

noncomputable def ep81 := @Enclosure.Complex.IsNear.re_isNear qz23 Bool.false 7000 4000 0 1 Bool.false 77998 4000 0 1

noncomputable abbrev qz276 := (Enclosure.sfrac Bool.false 77998 4000)

noncomputable abbrev qz29 := qz276

noncomputable def ep82 := @Enclosure.Complex.IsNear.of_eq qz23 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz29) Bool.false 7000 4000 0 1 Bool.false 77998 4000 0

noncomputable abbrev qz277 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz30 := (Complex.mk qz277 qz276)

noncomputable def ep83 := @Enclosure.Complex.IsNear.of_eq qz24 (Complex.log qz30) Bool.false 3351803206638839 1125899906842624 62500000029717 7429250000000000000 Bool.false 819614691394979 562949953421312 1000000000029717 59434000000000000000

noncomputable def ep84 := nat_lit 122531624846649601414448192969443059096501150027820475842990080

noncomputable def ep85 := nat_lit 1701879614403922283536153327373275574474609943920686170402816

noncomputable def ep86 := nat_lit 1175604487970525294547554566600419363059228274464686141440

noncomputable def ep87 := BSN.log_dyadic_bound 2068688004 10260688004 4 3 ep84 131072 59434 ep85 ep86 53585 12329376008 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2068688004) (BSN.artanhQ 10260688004) 0 3 ep85 ep84 ep86 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz31 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz32 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz278 := (Real.log (Enclosure.sfrac Bool.false 6164688004 16000000))

noncomputable abbrev qz279 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep88 := @Enclosure.Real.IsNear.mulLit_ff qz31 qz278 1 2 0 1 3351803206638839 562949953421312 62500000029717 3714625000000000000 3351803206638839 1125899906842624 62500000029717 7429250000000000000 qz32 (BSN.isNear_log_sfrac 6164688004 16000000 3351803206638839 562949953421312 62500000029717 3714625000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6164688004) qz279)) Bool.false 28116963193636217946112 4722366482869645213696 1000000000475472 59434000000000000000 3351803206638839 562949953421312 62500000029717 3714625000000000000 (BSN.log_rat_reduce_isNear 6164688004 16000000 8 12329376008 8192000000 53585 131072 24973259072661432 36028797018963968 59434 1000000000000000 rfl rfl rfl rfl (ep87 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep89 := BSN.arctan_dyadic_bound_f 9000 77998 1 0 131072 59434 0 1 1 0 1 1 15056 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 77998) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 77998) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz33 := (@HMul.hMul Real Real Real qz254 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz34 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz280 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 77998)))

noncomputable def ep90 := @Enclosure.Real.IsNear.subLit_ff_p qz33 qz280 884279719003555 562949953421312 1 2000000000000000 15056 131072 1 59434 107428536830522687488 819614691394979 562949953421312 1000000000029717 59434000000000000000 qz34 (ep89 rfl) rfl rfl

noncomputable abbrev qz35 := qz264

noncomputable abbrev qz281 := (@Eq.refl Real qz418)

noncomputable abbrev qz36 := qz281

noncomputable abbrev qz282 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 77998) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep91 := @Enclosure.Complex.IsNear.re_isNear qz24 Bool.false 3351803206638839 1125899906842624 62500000029717 7429250000000000000 Bool.false 819614691394979 562949953421312 1000000000029717 59434000000000000000 (ep83 (@congrArg Complex Complex qz17 qz30 Complex.log (BSN.w_shift_mk qz35 Bool.false 38999 1000 2 qz36 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz30) Bool.false 3351803206638839 1125899906842624 62500000029717 7429250000000000000 Bool.false 819614691394979 562949953421312 1000000000029717 59434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz30)) (@HMul.hMul Real Real Real qz0 qz31 qz278) Bool.false 3351803206638839 1125899906842624 62500000029717 7429250000000000000 (Enclosure.clog_re_eq 9000 77998 4000 6164688004 16000000 rfl rfl rfl) (ep88 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz30)) qz282 Bool.false 819614691394979 562949953421312 1000000000029717 59434000000000000000 (Enclosure.clog_im_eq 9000 77998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz282 (@HSub.hSub Real Real Real qz5 qz33 qz280) Bool.false 819614691394979 562949953421312 1000000000029717 59434000000000000000 (BSN.arctan_recip 77998 9000 rfl rfl) ep90))))

noncomputable def ep92 := @Enclosure.Real.IsNear.mulLit_ff qz27 qz28 77998 4000 0 1 819614691394979 562949953421312 1000000000029717 59434000000000000000

noncomputable def ep93 := @Enclosure.Complex.IsNear.im_isNear qz23 Bool.false 7000 4000 0 1 Bool.false 77998 4000 0 1

noncomputable def ep94 := @Enclosure.Complex.IsNear.im_isNear qz24 Bool.false 3351803206638839 1125899906842624 62500000029717 7429250000000000000 Bool.false 819614691394979 562949953421312 1000000000029717 59434000000000000000 (ep83 (@congrArg Complex Complex qz17 qz30 Complex.log (BSN.w_shift_mk qz35 Bool.false 38999 1000 2 qz36 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz30) Bool.false 3351803206638839 1125899906842624 62500000029717 7429250000000000000 Bool.false 819614691394979 562949953421312 1000000000029717 59434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz30)) (@HMul.hMul Real Real Real qz0 qz31 qz278) Bool.false 3351803206638839 1125899906842624 62500000029717 7429250000000000000 (Enclosure.clog_re_eq 9000 77998 4000 6164688004 16000000 rfl rfl rfl) (ep88 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz30)) qz282 Bool.false 819614691394979 562949953421312 1000000000029717 59434000000000000000 (Enclosure.clog_im_eq 9000 77998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz282 (@HSub.hSub Real Real Real qz5 qz33 qz280) Bool.false 819614691394979 562949953421312 1000000000029717 59434000000000000000 (BSN.arctan_recip 77998 9000 rfl rfl) ep90))))

noncomputable abbrev qz283 := (Enclosure.Real.IsNear.const Bool.false 77998 4000)

noncomputable abbrev qz37 := (@ep82 1 (BSN.w_sub_half_mk qz264 Bool.false 38999 1000 2 qz281 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz276 Bool.false 7000 4000 0 1 Bool.false 77998 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz283))

noncomputable def ep95 := @ep78 38999000001158933283 118868000000000000000000 ep79 26098497738094817771 1125899906842624000 40749000001991009283 118868000000000000000000 (@ep80 23462622446471873 4503599627370496 437500000208019 29717000000000000000 (ep81 qz37) ep91 rfl) (@ep92 31964153349712786021 1125899906842624000 38999000001158933283 118868000000000000000000 (ep93 qz37) ep94 rfl) rfl

noncomputable def ep96 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz25 qz28) (@HMul.hMul Real Real Real qz0 qz27 qz26) 5737302839764853 2251799813685248 7000000000208019 237736000000000000000 130716973255708082161 2251799813685248000

noncomputable def ep97 := nat_lit 307267713488341345327971562766204928

noncomputable def ep98 := @Enclosure.Real.IsNear.mulLit_ff qz25 qz28 7000 4000 0 1 819614691394979 562949953421312 1000000000029717 59434000000000000000

noncomputable def ep99 := @Enclosure.Real.IsNear.mulLit_ff qz27 qz26 77998 4000 0 1 3351803206638839 1125899906842624 62500000029717 7429250000000000000

noncomputable def ep100 := @ep96 2437437501158933283 14858500000000000000000 ep97 136454276095472935161 2251799813685248000 5749875002343868941 29717000000000000000000 (@ep98 5737302839764853 2251799813685248 7000000000208019 237736000000000000000 (ep81 qz37) ep94 rfl) (@ep99 130716973255708082161 2251799813685248000 2437437501158933283 14858500000000000000000 (ep93 qz37) ep91 rfl) rfl

noncomputable def ep101 := @Enclosure.Complex.IsNear.of_eq qz17 qz30 Bool.false 9000 4000 0 1 Bool.false 77998 4000 0 1 (BSN.w_shift_mk qz35 Bool.false 38999 1000 2 qz36 rfl)

noncomputable abbrev qz284 := (ep101 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 77998 4000) Bool.false 9000 4000 0 1 Bool.false 77998 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 77998 4000)))

noncomputable abbrev qz38 := qz284

noncomputable def ep102 := ep76 (@ep77 29717000000000000000000 (ep95 rfl) (ep100 rfl)) qz38 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz39 := qz269

noncomputable abbrev qz40 := (Complex.im ↑qz258)

noncomputable def ep103 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz39) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz39) qz40) 60223 65536 1 65536 0 1 0 1 60223 60223

noncomputable def ep104 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz39) (Complex.re ↑qz3) 1 2 0 1 60223 32768 1 32768 60223 65536 1 65536

noncomputable abbrev qz285 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz286 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz41 := (@Enclosure.Complex.IsNear.of_eq qz269 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz285) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz285 Bool.false 1 2 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 2) qz286))

noncomputable def ep105 := ep104 (@Enclosure.Complex.IsNear.re_isNear qz39 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz41) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 60223 32768 1 32768 (Complex.ofReal_re qz3) EMRow07.d4)

noncomputable def ep106 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz39) qz40 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable abbrev qz42 := qz285

noncomputable abbrev qz43 := qz286

noncomputable def ep107 := ep106 (@Enclosure.Complex.IsNear.im_isNear qz39 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz41) (@Enclosure.Real.IsNear.of_eq qz40 qz42 Bool.false 0 1 0 1 (@Eq.trans Real qz40 (0 : Real) qz42 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz43)

noncomputable def ep108 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz39) qz40) (@HMul.hMul Real Real Real qz0 (Complex.im qz39) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep109 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz39) qz40 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep110 := ep109 (@Enclosure.Complex.IsNear.re_isNear qz39 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz41) (@Enclosure.Real.IsNear.of_eq qz40 qz42 Bool.false 0 1 0 1 (@Eq.trans Real qz40 (0 : Real) qz42 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz43)

noncomputable def ep111 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz39) (Complex.re ↑qz3) 0 1 0 1 60223 32768 1 32768 0 1 0 1

noncomputable def ep112 := ep111 (@Enclosure.Complex.IsNear.im_isNear qz39 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz41) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 60223 32768 1 32768 (Complex.ofReal_re qz3) EMRow07.d4)

noncomputable def ep113 := @ep74 5749875002343868941 29717000000000000000000 (ep102 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz39 (↑qz3) Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 (@ep103 65536 1 65536 (ep105 rfl) (ep107 rfl) rfl rfl) (@ep108 1 0 1 (ep110 rfl) (ep112 rfl) rfl rfl))

noncomputable abbrev qz44 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz287 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz45 := (@HMul.hMul Complex Complex Complex qz259 (@HMul.hMul Complex Complex Complex qz259 (2 : Complex) qz287) (@HSub.hSub Complex Complex Complex qz260 (@HMul.hMul Complex Complex Complex qz259 (2 : Complex) qz287) (1 : Complex)))

noncomputable abbrev qz288 := (@HPow.hPow Complex Int Complex qz422 qz415 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz46 := qz288

noncomputable def ep114 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz16 qz17 (@HSub.hSub Int Int Int qz18 qz19 (@HMul.hMul Int Int Int qz20 qz21 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz16 qz17 (@HSub.hSub Int Int Int qz18 qz19 (@HMul.hMul Int Int Int qz20 qz21 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45) qz46)) Bool.false 522531 1073741824 3 1073741824

noncomputable def ep115 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz16 qz17 (@HSub.hSub Int Int Int qz18 qz19 (@HMul.hMul Int Int Int qz20 qz21 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45) qz46) Bool.false 0 1 0 1 Bool.false

noncomputable def ep116 := @ep115 0 1 0 1 Bool.false 522531 1073741824 3 1073741824 Bool.true 2264242941 536870912000 38999 1610612736000 Bool.false 522531 522531 1073741824 3 1073741824 Bool.true 2264242941 2264242941 536870912000 38999

noncomputable def ep117 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz16 qz17 (@HSub.hSub Int Int Int qz18 qz19 (@HMul.hMul Int Int Int qz20 qz21 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz42 qz42) Bool.false 0 1 0 1 Bool.false

noncomputable def ep118 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45) qz46 Bool.false 522531 1073741824 3 1073741824 Bool.true 2264242941 536870912000 38999 1610612736000

noncomputable abbrev qz47 := (Complex.re qz288)

noncomputable abbrev qz48 := (Complex.im qz288)

noncomputable def ep119 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz47) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz48) 522531 1073741824 3 1073741824 0 1 0

noncomputable def ep120 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz47 1 12 0 1 1567593 268435456 9 268435456 522531

noncomputable def ep121 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz42) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz289 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz42 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz43)

noncomputable def ep122 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep121 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz289)

noncomputable def ep123 := @Enclosure.Complex.IsNear.re_isNear qz46 Bool.false 1567593 268435456 9 268435456 Bool.true 6792728823 134217728000 38999 134217728000

noncomputable abbrev qz423 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz290 := (@HPow.hPow Complex Nat Complex qz423 qz415 1)

noncomputable abbrev qz49 := (@Inv.inv Complex Complex.instInv qz290)

noncomputable def ep124 := @Enclosure.Complex.IsNear.of_eq qz46 qz49 Bool.false 1567593 268435456 9 268435456 Bool.true 6792728823 134217728000 38999

noncomputable def ep125 := @Enclosure.Complex.IsNear.of_parts qz49 Bool.false 1567593 268435456 9 268435456 Bool.true 6792728823 134217728000 38999

noncomputable abbrev qz50 := (Complex.re qz290)

noncomputable abbrev qz51 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz52 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz53 := qz290

noncomputable def ep126 := @Enclosure.Real.IsNear.mulLit_ff qz50 (@Inv.inv Real Real.instInv (@DFunLike.coe qz51 Complex (fun (x : Complex) => Real) qz52 Complex.normSq qz53)) 9000 4000 0 1 174177 67108864 1 67108864

noncomputable def ep127 := @Enclosure.Complex.IsNear.re_isNear qz53 Bool.false 9000 4000 0 1 Bool.false 77998 4000 0 1

noncomputable def ep128 := @Enclosure.Complex.IsNear.of_eq qz53 qz17 Bool.false 9000 4000 0 1 Bool.false 77998 4000 0

noncomputable def ep129 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz51 Complex (fun (x : Complex) => Real) qz52 Complex.normSq qz53)) Bool.false 174177 67108864 1 67108864 174177 67108864 1

noncomputable abbrev qz54 := (@instHAdd Real Real.instAdd)

noncomputable abbrev qz55 := (Complex.im qz290)

noncomputable def ep130 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz51 Complex (fun (x : Complex) => Real) qz52 Complex.normSq qz53) (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 qz50 qz50) (@HMul.hMul Real Real Real qz0 qz55 qz55)) Bool.false 1541172001 4000000 0 1

noncomputable def ep131 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz50 qz50) (@HMul.hMul Real Real Real qz0 qz55 qz55) 81 16 0 1 1520922001 4000000

noncomputable def ep132 := @Enclosure.Real.IsNear.mulLit_ff qz50 qz50 9000 4000 0 1 9000 4000 0 1

noncomputable def ep133 := @Enclosure.Real.IsNear.mulLit_ff qz55 qz55 77998 4000 0 1 77998 4000 0 1

noncomputable def ep134 := @Enclosure.Complex.IsNear.im_isNear qz53 Bool.false 9000 4000 0 1 Bool.false 77998 4000 0 1

noncomputable abbrev qz56 := (ep127 (@ep128 1 (BSN.pow_one_c qz261) qz284))

noncomputable abbrev qz57 := (ep134 (@ep128 1 (BSN.pow_one_c qz261) qz284))

noncomputable def ep135 := @ep131 0 1 24658752016 1541172001 4000000 0 1 (@ep132 81 16 0 1 qz56 qz56 rfl) (@ep133 1520922001 4000000 0 1 qz57 qz57 rfl)

noncomputable def ep136 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz51 Complex (fun (x : Complex) => Real) qz52 Complex.normSq qz53) 1541172001 4000000 0 1 87088 87089 33554432 (ep130 (Enclosure.Complex.normSq_eq_mul_add_mul qz53) (ep135 rfl rfl)) rfl

noncomputable def ep137 := @Enclosure.Real.IsNear.of_eq (Complex.re qz49) (@HMul.hMul Real Real Real qz0 qz50 (@Inv.inv Real Real.instInv (@DFunLike.coe qz51 Complex (fun (x : Complex) => Real) qz52 Complex.normSq qz53))) Bool.false 1567593 268435456 9 268435456 (Enclosure.Complex.inv_re_eq_mul qz53) (@ep126 1567593 268435456 9 268435456 qz56 (@ep129 67108864 (ep136 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep138 := @Enclosure.Real.IsNear.of_eq (Complex.im qz49) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz55) (@Inv.inv Real Real.instInv (@DFunLike.coe qz51 Complex (fun (x : Complex) => Real) qz52 Complex.normSq qz53))) Bool.true 6792728823 134217728000 38999 134217728000 (Enclosure.Complex.inv_im_eq_mul qz53)

noncomputable def ep139 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz55) (@Inv.inv Real Real.instInv (@DFunLike.coe qz51 Complex (fun (x : Complex) => Real) qz52 Complex.normSq qz53)) 77998 4000 0 1 174177 67108864 1

noncomputable def ep140 := @ep139 67108864 6792728823 134217728000 38999 134217728000 (@Enclosure.Real.IsNear.neg qz55 Bool.false 77998 4000 0 1 qz57) (@ep129 67108864 (ep136 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep141 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz48 0 1 0 1 6792728823 134217728000 38999 134217728000 0

noncomputable def ep142 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep121 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz289)

noncomputable def ep143 := @Enclosure.Complex.IsNear.im_isNear qz46 Bool.false 1567593 268435456 9 268435456 Bool.true 6792728823 134217728000 38999 134217728000

noncomputable abbrev qz58 := (@ep124 134217728000 (BSN.zpow_one_sub_two_mul qz261 1 1 rfl rfl) (@ep125 134217728000 ep137 (ep138 ep140)))

noncomputable def ep144 := @ep119 1 522531 522531 1073741824 3 1073741824 (@ep120 1073741824 3 1073741824 ep122 (ep123 qz58) rfl) (@ep141 1 0 1 ep142 (ep143 qz58) rfl) rfl

noncomputable def ep145 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz48) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz47) 2264242941 536870912000 38999 1610612736000 0 1 0

noncomputable def ep146 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz48 1 12 0 1 6792728823 134217728000 38999 134217728000 2264242941

noncomputable def ep147 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz47 0 1 0 1 1567593 268435456 9 268435456 0

noncomputable def ep148 := @ep145 1 2264242941 2264242941 536870912000 38999 1610612736000 (@ep146 536870912000 38999 1610612736000 ep122 (ep143 qz58) rfl) (@ep147 1 0 1 ep142 (ep123 qz58) rfl) rfl

noncomputable abbrev qz59 := (@Enclosure.Complex.IsNear.mk qz285 qz285 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz286 qz286)

noncomputable def ep149 := @ep116 1610612736000 (@ep117 0 1 0 1 (BSN.stirling_sum_base qz17) qz59) (ep118 (ep144 rfl) (ep148 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep150 := @ep71 92535808705293033721 2251799813685248000 282653223952211461422407 ep58 (ep113 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep114 Bool.true 2264242941 536870912000 38999 1610612736000 (BSN.stirling_sum_succ qz17 0 1 rfl) (ep149 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep151 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz35 2) Bool.false 3345558324190455 562949953421312 62500000029717 3714625000000000000 Bool.false 862654558668195 281474976710656

noncomputable abbrev qz60 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz262 qz263 qz287))

noncomputable def ep152 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz35 2) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz35 1) qz60) Bool.false 3345558324190455 562949953421312 62500000029717 3714625000000000000 Bool.false 862654558668195 281474976710656 1000000000029717 29717000000000000000

noncomputable def ep153 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz35 1) qz60 Bool.false 3344450222628087 1125899906842624 62500000029717 7429250000000000000 Bool.false 877064173946275 562949953421312 1000000000029717 59434000000000000000 Bool.false

noncomputable def ep154 := nat_lit 7533527611085197095919775907840

noncomputable def ep155 := nat_lit 971262687241885670532899143680

noncomputable abbrev qz61 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz262 qz263 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep156 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz35 1) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz35 0) qz61) Bool.false 3344450222628087 1125899906842624 62500000029717 7429250000000000000 Bool.false 877064173946275 562949953421312 1000000000029717 59434000000000000000

noncomputable def ep157 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz35 0) qz61 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz291 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz29))

noncomputable def ep158 := @Enclosure.Complex.IsNear.of_eq qz61 qz291 Bool.false 3344450222628087 1125899906842624 62500000029717 7429250000000000000 Bool.false 877064173946275 562949953421312 1000000000029717 59434000000000000000

noncomputable def ep159 := nat_lit 116910109959347088000397231372500787279770280939512866242990080

noncomputable def ep160 := nat_lit 1521968070132942208514166151547368728911992386074588250402816

noncomputable def ep161 := nat_lit 927878652742729103186008108135876868025687659091886141440

noncomputable def ep162 := BSN.log_dyadic_bound 1988688004 10180688004 4 3 ep159 131072 59434 ep160 ep161 51873 12169376008 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 1988688004) (BSN.artanhQ 10180688004) 0 3 ep160 ep159 ep161 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep163 := @Enclosure.Real.IsNear.mulLit_ff qz31 (Real.log (Enclosure.sfrac Bool.false 6084688004 16000000)) 1 2 0 1 3344450222628087 562949953421312 62500000029717 3714625000000000000 3344450222628087 1125899906842624 62500000029717 7429250000000000000 qz32 (BSN.isNear_log_sfrac 6084688004 16000000 3344450222628087 562949953421312 62500000029717 3714625000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6084688004) qz279)) Bool.false 28055281893139751632896 4722366482869645213696 1000000000475472 59434000000000000000 3344450222628087 562949953421312 62500000029717 3714625000000000000 (BSN.log_rat_reduce_isNear 6084688004 16000000 8 12169376008 8192000000 51873 131072 24973259072661432 36028797018963968 59434 1000000000000000 rfl rfl rfl rfl (ep162 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep164 := BSN.arctan_dyadic_bound_f 1000 77998 1 0 131072 59434 0 1 1 0 1 1 1680 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 77998) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 77998) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz292 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz293 := (@Nat.cast Real Real.instNatCast 77998)

noncomputable def ep165 := @Enclosure.Real.IsNear.subLit_ff_p qz33 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz292 qz293)) 884279719003555 562949953421312 1 2000000000000000 1680 131072 1 59434 114958555407486156800 877064173946275 562949953421312 1000000000029717 59434000000000000000 qz34 (ep164 rfl) rfl rfl

noncomputable abbrev qz62 := (@HAdd.hAdd Complex Complex Complex qz262 qz263 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz294 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz29)

noncomputable def ep166 := @ep157 3344450222628087 1125899906842624 62500000029717 7429250000000000000 Bool.false 877064173946275 562949953421312 1000000000029717 59434000000000000000 Bool.false 3344450222628087 3344450222628087 1125899906842624 62500000029717 7429250000000000000 Bool.false 877064173946275 877064173946275 562949953421312 1000000000029717 59434000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz35 0) (Complex.mk qz42 qz42) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz35) qz59) (ep158 (@congrArg Complex Complex qz62 qz294 Complex.log (BSN.w_shift_mk qz35 Bool.false 38999 1000 0 qz36 rfl)) (@Enclosure.Complex.IsNear.of_parts qz291 Bool.false 3344450222628087 1125899906842624 62500000029717 7429250000000000000 Bool.false 877064173946275 562949953421312 1000000000029717 59434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz291) (@HMul.hMul Real Real Real qz0 qz31 (Real.log (Enclosure.sfrac Bool.false 6084688004 16000000))) Bool.false 3344450222628087 1125899906842624 62500000029717 7429250000000000000 (Enclosure.clog_re_eq 1000 77998 4000 6084688004 16000000 rfl rfl rfl) (ep163 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz291) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz293 qz292)) Bool.false 877064173946275 562949953421312 1000000000029717 59434000000000000000 (Enclosure.clog_im_eq 1000 77998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz293 qz292)) (@HSub.hSub Real Real Real qz5 qz33 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz292 qz293))) Bool.false 877064173946275 562949953421312 1000000000029717 59434000000000000000 (BSN.arctan_recip 77998 1000 rfl rfl) ep165)))) rfl rfl

noncomputable abbrev qz295 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz29))

noncomputable def ep167 := @Enclosure.Complex.IsNear.of_eq qz60 qz295 Bool.false 3346666425752823 1125899906842624 62500000029717 7429250000000000000 Bool.false 848244943390115 562949953421312 1000000000029717 59434000000000000000

noncomputable def ep168 := nat_lit 118573512848510475178707129295089549508319649365205149122990080

noncomputable def ep169 := nat_lit 1574399942973563597891125368131165879229197145268417626402816

noncomputable def ep170 := nat_lit 997125924709291662180652701531809971351135443703726141440

noncomputable def ep171 := BSN.log_dyadic_bound 2012688004 10204688004 4 3 ep168 131072 59434 ep169 ep170 52389 12217376008 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2012688004) (BSN.artanhQ 10204688004) 0 3 ep169 ep168 ep170 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep172 := @Enclosure.Real.IsNear.mulLit_ff qz31 (Real.log (Enclosure.sfrac Bool.false 6108688004 16000000)) 1 2 0 1 3346666425752823 562949953421312 62500000029717 3714625000000000000 3346666425752823 1125899906842624 62500000029717 7429250000000000000 qz32 (BSN.isNear_log_sfrac 6108688004 16000000 3346666425752823 562949953421312 62500000029717 3714625000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6108688004) qz279)) Bool.false 28073872752401537040384 4722366482869645213696 1000000000475472 59434000000000000000 3346666425752823 562949953421312 62500000029717 3714625000000000000 (BSN.log_rat_reduce_isNear 6108688004 16000000 8 12217376008 8192000000 52389 131072 24973259072661432 36028797018963968 59434 1000000000000000 rfl rfl rfl rfl (ep171 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep173 := BSN.arctan_dyadic_bound_f 5000 77998 1 0 131072 59434 0 1 1 0 1 1 8390 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 77998) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 77998) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz296 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep174 := @Enclosure.Real.IsNear.subLit_ff_p qz33 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz296 qz293)) 884279719003555 562949953421312 1 2000000000000000 8390 131072 1 59434 111181161220029153280 848244943390115 562949953421312 1000000000029717 59434000000000000000 qz34 (ep173 rfl) rfl rfl

noncomputable abbrev qz63 := (@HAdd.hAdd Complex Complex Complex qz262 qz263 qz287)

noncomputable abbrev qz297 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz29)

noncomputable def ep175 := @ep153 3346666425752823 1125899906842624 62500000029717 7429250000000000000 Bool.false 848244943390115 562949953421312 1000000000029717 59434000000000000000 Bool.false ep154 3345558324190455 562949953421312 62500000029717 3714625000000000000 Bool.false ep155 862654558668195 281474976710656 1000000000029717 29717000000000000000 (ep156 (BSN.log_sum_c_succ qz35 0 1 rfl) (ep166 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep167 (@congrArg Complex Complex qz63 qz297 Complex.log (BSN.w_shift_mk qz35 Bool.false 38999 1000 1 qz36 rfl)) (@Enclosure.Complex.IsNear.of_parts qz295 Bool.false 3346666425752823 1125899906842624 62500000029717 7429250000000000000 Bool.false 848244943390115 562949953421312 1000000000029717 59434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz295) (@HMul.hMul Real Real Real qz0 qz31 (Real.log (Enclosure.sfrac Bool.false 6108688004 16000000))) Bool.false 3346666425752823 1125899906842624 62500000029717 7429250000000000000 (Enclosure.clog_re_eq 5000 77998 4000 6108688004 16000000 rfl rfl rfl) (ep172 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz295) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz293 qz296)) Bool.false 848244943390115 562949953421312 1000000000029717 59434000000000000000 (Enclosure.clog_im_eq 5000 77998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz293 qz296)) (@HSub.hSub Real Real Real qz5 qz33 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz296 qz293))) Bool.false 848244943390115 562949953421312 1000000000029717 59434000000000000000 (BSN.arctan_recip 77998 5000 rfl rfl) ep174)))) rfl rfl

noncomputable def ep176 := @ep64 ep58 Bool.false 3345558324190455 562949953421312 62500000029717 3714625000000000000 Bool.false 862654558668195 281474976710656 1000000000029717 29717000000000000000 Bool.true ep65 34287718001537743771 1125899906842624000 45632628587088487896167 ep62 Bool.false ep66 85634572235947473721 2251799813685248000 331805223953672111406407 ep58 (@ep67 1125899906842624000 43584628586114721240167 ep62 Bool.false 92535808705293033721 2251799813685248000 282653223952211461422407 ep58 (BSN.logGammaStirling_unfold 1 qz17) (ep150 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep151 1000000000029717 29717000000000000000 (BSN.log_sum_c_eq qz35 2) (ep152 (BSN.log_sum_c_succ qz35 1 2 rfl) (ep175 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz64 := (@HDiv.hDiv Real Real Real qz257 qz264 (2 : Real))

noncomputable def ep177 := @Enclosure.Real.IsNear.mulLit_ff qz64 (Real.log Real.pi) 38999 2000 0 1 75021 65536 1 32768 2925743979 131072000 38999 65536000 (@Enclosure.Real.IsNear.of_eq qz64 (Enclosure.sfrac Bool.false 38999 2000) Bool.false 38999 2000 0 1 (BSN.t_half_eq qz35 Bool.false 38999 1000 qz36) (Enclosure.Real.IsNear.const Bool.false 38999 2000)) EMRow07.d5 rfl

noncomputable def ep178 := @ep60 38999 65536000 ep61 7074134682170366117 450359962737049600 1201005186203672111406407 ep58 (@ep63 331805223953672111406407 ep58 (ep176 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep177 rfl rfl

noncomputable def ep179 := nat_lit 497048500635992941278709264631778202067139925682697725399381553195165505

noncomputable def ep180 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080

noncomputable def ep181 := nat_lit 998088444005431997316880136454194539381330553241187008232418397038401

noncomputable def ep182 := nat_lit 1300177739423020337258106458576588499969225270178008311366003961915942721

noncomputable def ep183 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800

noncomputable abbrev qz298 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz299 := (BSN.sinOddQ 268435456)

noncomputable def ep184 := BSN.sin_dyadic_bound_f 421595657 268435456 3 2 131072 59493 ep179 ep180 ep181 ep182 ep183 ep181 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 421595657) qz298 0 2 ep179 ep180 ep181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 421595657) qz299 0 2 ep182 ep183 ep181 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz300 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep185 := @ep57 32768 Bool.true 131071 131072 1 29717 (@ep59 514711 32768 27 32768 ep178 rfl) (Enclosure.sfrac_false_div 514711 32768) (BSN.cos_reduce1 qz266 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7416789244073090220032) qz300) 226375608064910080 72057594037927936 Bool.false 131071 131072 2 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q1 514711 32768 226375608064910080 72057594037927936 2 7416789244073090220032 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131071 131072 7416789244073090220032 4722366482869645213696 421595657 268435456 59493 59434 (ep184 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep186 := nat_lit 166469489562106151063680651

noncomputable def ep187 := nat_lit 37277293863502209607532544000

noncomputable abbrev qz424 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz301 := qz424

noncomputable abbrev qz65 := qz301

noncomputable abbrev qz425 := (@Neg.neg Complex Complex.instNeg qz440)

noncomputable abbrev qz302 := qz425

noncomputable abbrev qz66 := qz302

noncomputable abbrev qz303 := (@HPow.hPow Complex Complex Complex qz424 (@Nat.cast Complex Complex.instNatCast 8) qz425)

noncomputable abbrev qz67 := qz303

noncomputable abbrev qz304 := (@Nat.cast Complex Complex.instNatCast 8)

noncomputable abbrev qz68 := (@HAdd.hAdd Complex Complex Complex qz262 (@HDiv.hDiv Complex Complex Complex qz270 qz304 (@HSub.hSub Complex Complex Complex qz260 qz265 (1 : Complex))) qz269)

noncomputable abbrev qz69 := (@instHSub Nat instSubNat)

noncomputable abbrev qz305 := qz423

noncomputable abbrev qz70 := qz305

noncomputable abbrev qz71 := qz304

noncomputable def ep188 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz11 1 8) (@HAdd.hAdd Complex Complex Complex qz8 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 8, @HPow.hPow Complex Complex Complex qz65 (@Nat.cast Complex Complex.instNatCast n) qz66) (@HMul.hMul Complex Complex Complex qz4 qz67 (@HAdd.hAdd Complex Complex Complex qz8 qz68 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))))) Bool.false ep53 836273151473392549888000 ep54

noncomputable def ep189 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 8, @HPow.hPow Complex Complex Complex qz65 (@Nat.cast Complex Complex.instNatCast n) qz66) (@HMul.hMul Complex Complex Complex qz4 qz67 (@HAdd.hAdd Complex Complex Complex qz8 qz68 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))))) Bool.false 29093465039 17179869184 2105673174515 510534172540928

noncomputable def ep190 := nat_lit 5081851522401562915655707

noncomputable def ep191 := nat_lit 12680526999231059618848651

noncomputable def ep192 := nat_lit 25893634706597187288079677507239936

noncomputable def ep193 := nat_lit 101167368340624655221722047315968

noncomputable def ep194 := @ep189 Bool.true 1160080471 4294967296 1053114545217 255267086270464 Bool.false 91010647078026656479929 836273151473392549888000 ep190 ep55 Bool.false 32914958317031207980767 209068287868348137472000 ep191 ep187 Bool.false ep192 ep53 836273151473392549888000 ep54 ep55 Bool.true ep193 23554863487515751091233 209068287868348137472000

noncomputable def ep195 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 8, @HPow.hPow Complex Complex Complex qz65 (@Nat.cast Complex Complex.instNatCast n) qz66) (BSN.headSumC qz11 8) Bool.false 29093465039 17179869184 2105673174515 510534172540928 Bool.true 1160080471 4294967296 1053114545217

noncomputable abbrev qz72 := (BSN.headSumC qz265 7)

noncomputable abbrev qz73 := (@HPow.hPow Complex Complex Complex qz301 (@Nat.cast Complex Complex.instNatCast 7) qz302)

noncomputable def ep196 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz11 8) (@HAdd.hAdd Complex Complex Complex qz8 qz72 qz73) Bool.false 29093465039 17179869184 2105673174515 510534172540928 Bool.true 1160080471 4294967296 1053114545217 255267086270464

noncomputable def ep197 := @Enclosure.Complex.IsNear.addLitP qz72 qz73 Bool.false 11681652637 8589934592 230130616933 63816771567616 Bool.true 1585871529 17179869184 1843205866553 510534172540928 Bool.false

noncomputable abbrev qz74 := (BSN.headSumC qz265 6)

noncomputable abbrev qz75 := (@HPow.hPow Complex Complex Complex qz301 (@Nat.cast Complex Complex.instNatCast 6) qz302)

noncomputable def ep198 := @Enclosure.Complex.IsNear.of_eq qz72 (@HAdd.hAdd Complex Complex Complex qz8 qz74 qz75) Bool.false 11681652637 8589934592 230130616933 63816771567616 Bool.true 1585871529 17179869184 1843205866553 510534172540928

noncomputable def ep199 := @Enclosure.Complex.IsNear.addLitP qz74 qz75 Bool.false 9143298767 8589934592 388321220823 127633543135232 Bool.false 3253305321 17179869184 1555709641907 510534172540928 Bool.false

noncomputable abbrev qz76 := (BSN.headSumC qz265 5)

noncomputable abbrev qz77 := (@HPow.hPow Complex Complex Complex qz301 (@Nat.cast Complex Complex.instNatCast 5) qz302)

noncomputable def ep200 := @Enclosure.Complex.IsNear.of_eq qz74 (@HAdd.hAdd Complex Complex Complex qz8 qz76 qz77) Bool.false 9143298767 8589934592 388321220823 127633543135232 Bool.false 3253305321 17179869184 1555709641907 510534172540928

noncomputable def ep201 := @Enclosure.Complex.IsNear.addLitP qz76 qz77 Bool.false 10620021487 17179869184 1240357447311 510534172540928 Bool.false 687695445 4294967296 155801769779 63816771567616 Bool.false

noncomputable abbrev qz78 := (BSN.headSumC qz265 4)

noncomputable abbrev qz79 := (@HPow.hPow Complex Complex Complex qz301 (@Nat.cast Complex Complex.instNatCast 4) qz302)

noncomputable def ep202 := @Enclosure.Complex.IsNear.of_eq qz76 (@HAdd.hAdd Complex Complex Complex qz8 qz78 qz79) Bool.false 10620021487 17179869184 1240357447311 510534172540928 Bool.false 687695445 4294967296 155801769779 63816771567616

noncomputable def ep203 := @Enclosure.Complex.IsNear.addLitP qz78 qz79 Bool.false 8711047871 8589934592 445879916581 255267086270464 Bool.true 2494705155 17179869184 898522382267 510534172540928 Bool.true

noncomputable abbrev qz80 := (BSN.headSumC qz265 3)

noncomputable abbrev qz426 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz306 := qz426

noncomputable abbrev qz81 := (@HPow.hPow Complex Complex Complex qz301 qz306 qz302)

noncomputable def ep204 := @Enclosure.Complex.IsNear.of_eq qz78 (@HAdd.hAdd Complex Complex Complex qz8 qz80 qz81) Bool.false 8711047871 8589934592 445879916581 255267086270464 Bool.true 2494705155 17179869184 898522382267 510534172540928

noncomputable def ep205 := @Enclosure.Complex.IsNear.addLitP qz80 qz81 Bool.false 6630590771 8589934592 245576725123 255267086270464 Bool.true 5749296165 8589934592 248007100251 255267086270464 Bool.false

noncomputable abbrev qz82 := (BSN.headSumC qz265 2)

noncomputable abbrev qz427 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz307 := qz427

noncomputable abbrev qz83 := (@HPow.hPow Complex Complex Complex qz301 qz307 qz302)

noncomputable def ep206 := @Enclosure.Complex.IsNear.of_eq qz80 (@HAdd.hAdd Complex Complex Complex qz8 qz82 qz83) Bool.false 6630590771 8589934592 245576725123 255267086270464 Bool.true 5749296165 8589934592 248007100251 255267086270464

noncomputable def ep207 := @Enclosure.Complex.IsNear.addLitP qz82 qz83 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep208 := @Enclosure.Complex.IsNear.of_eq qz82 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz42) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz11)

noncomputable abbrev qz84 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable abbrev qz85 := (@HMul.hMul Real Real Real qz254 qz264 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable def ep209 := @Enclosure.Complex.IsNear.of_eq qz83 (Complex.mk (@HMul.hMul Real Real Real qz0 qz84 (Real.cos qz85)) (@HMul.hMul Real Real Real qz0 qz84 (@Neg.neg Real Real.instNeg (Real.sin qz85)))) Bool.true 1959343821 8589934592 245576725123 255267086270464 Bool.true 5749296165 8589934592 248007100251 255267086270464 (BSN.cpow_neg_s_mk qz35 38999 1000 2 qz36 rfl)

noncomputable abbrev qz86 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz87 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep210 := @Enclosure.Real.IsNear.inv_image qz86 185363 131072 1 131072 46340 46342 65536 (@Enclosure.Real.IsNear.of_eq qz86 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2) qz87)) Bool.false 185363 131072 1 131072 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2) qz87)) Bool.false 185363 131072 1 131072 185363 131072 1 131072 (BSN.sqrt_enclosure 2 1 92681 92682 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep211 := BSN.log_dyadic_bound 1 3 6 5 613814355 65536 29717 24381081 945 45426 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep212 := nat_lit 60429607009115666104057009350625

noncomputable def ep213 := nat_lit 623075623024179315423659559506411520

noncomputable def ep214 := nat_lit 4361529361169255207965616916544880640

noncomputable def ep215 := BSN.sin_dyadic_bound_f 88168295 268435456 2 1 131072 59493 ep212 ep213 ep212 ep212 ep214 ep212 42281 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 88168295) qz298 0 1 ep212 ep213 ep212 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 88168295) qz299 0 1 ep212 ep214 ep212 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz88 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz89 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz308 := (Enclosure.Real.IsNear.const Bool.false 38999 1000)

noncomputable abbrev qz90 := qz308

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3543137) qz88)

noncomputable abbrev qz310 := (BSN.isNear_log_sfrac 2 1 45426 65536 1 29717 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 45426 65536 29717 rfl rfl rfl (ep211 rfl)))

noncomputable abbrev qz311 := (@Nat.cast Real Real.instNatCast 6204292228697548652544)

noncomputable abbrev qz312 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep216 := @Enclosure.Real.IsNear.cos_image qz85 qz309 Bool.false 3543137 131072 173 131072 Bool.true 42281 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz85 Bool.false 885784287 32768000 38999 29717000 3543137 131072 173 131072 (@Enclosure.Real.IsNear.mulLit_ff qz35 qz89 38999 1000 0 1 45426 65536 1 29717 885784287 32768000 38999 29717000 qz90 qz310 rfl) rfl) (Enclosure.sfrac_false_div 3543137 131072) (BSN.cos_reduce1 qz309 (@HDiv.hDiv Real Real Real qz2 qz311 qz312) 226375608064910080 72057594037927936 Bool.false 42281 131072 4 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q1 3543137 131072 226375608064910080 72057594037927936 4 6204292228697548652544 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 42281 131072 6204292228697548652544 18889465931478580854784 88168295 268435456 59493 59434 (ep215 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep217 := nat_lit 124615124604835863084731911901282304

noncomputable def ep218 := nat_lit 1869226869072537946270978678519234560

noncomputable abbrev qz313 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz314 := (BSN.cosOddQ 268435456)

noncomputable def ep219 := BSN.cos_dyadic_bound_f 88168295 268435456 2 1 131072 59493 ep212 ep217 ep212 ep212 ep218 ep212 124065 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 88168295) qz313 0 1 ep212 ep217 ep212 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 88168295) qz314 0 1 ep212 ep218 ep212 rfl rfl rfl rfl) rfl rfl

noncomputable def ep220 := @Enclosure.Real.IsNear.sin_image qz85 qz309 Bool.false 3543137 131072 173 131072 Bool.false 124065 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz85 Bool.false 885784287 32768000 38999 29717000 3543137 131072 173 131072 (@Enclosure.Real.IsNear.mulLit_ff qz35 qz89 38999 1000 0 1 45426 65536 1 29717 885784287 32768000 38999 29717000 qz90 qz310 rfl) rfl) (Enclosure.sfrac_false_div 3543137 131072) (BSN.sin_reduce1 qz309 (@HDiv.hDiv Real Real Real qz2 qz311 qz312) 226375608064910080 72057594037927936 Bool.false 124065 131072 4 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q1 3543137 131072 226375608064910080 72057594037927936 4 6204292228697548652544 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 124065 131072 6204292228697548652544 18889465931478580854784 88168295 268435456 59493 59434 (ep219 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz315 := (@Enclosure.Real.IsNear.recentre' qz84 Bool.false 92682 131072 2 131072 46341 65536 1 65536 (ep210 rfl rfl) rfl)

noncomputable def ep221 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz84 (Real.cos qz85)) (@HMul.hMul Real Real Real qz0 qz84 (@Neg.neg Real Real.instNeg (Real.sin qz85))) Bool.true 1959343821 8589934592 245576725123 255267086270464 Bool.true 5749296165 8589934592 248007100251 255267086270464 (@Enclosure.Real.IsNear.mulLit_ft qz84 (Real.cos qz85) 46341 65536 1 65536 42281 131072 5272113 3895066624 1959343821 8589934592 245576725123 255267086270464 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz85) Bool.true 42281 131072 5272113 3895066624 42281 131072 5272113 3895066624 (ep216 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz84 (@Neg.neg Real Real.instNeg (Real.sin qz85)) 46341 65536 1 65536 124065 131072 5272113 3895066624 5749296165 8589934592 248007100251 255267086270464 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz85) Bool.false 124065 131072 5272113 3895066624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz85) Bool.false 124065 131072 5272113 3895066624 124065 131072 5272113 3895066624 (ep220 rfl rfl) rfl)) rfl)

noncomputable def ep222 := @ep207 1959343821 8589934592 245576725123 255267086270464 Bool.true 5749296165 8589934592 248007100251 255267086270464 Bool.false 6630590771 6630590771 8589934592 245576725123 255267086270464 Bool.true 5749296165 5749296165 8589934592 248007100251 255267086270464 (ep208 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz42 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz43)) (ep209 ep221) rfl rfl

noncomputable abbrev qz316 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz91 := (@Inv.inv Real Real.instInv (Real.sqrt qz316))

noncomputable abbrev qz92 := (@HMul.hMul Real Real Real qz254 qz264 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep223 := @Enclosure.Complex.IsNear.of_eq qz81 (Complex.mk (@HMul.hMul Real Real Real qz0 qz91 (Real.cos qz92)) (@HMul.hMul Real Real Real qz0 qz91 (@Neg.neg Real Real.instNeg (Real.sin qz92)))) Bool.false 520114275 2147483648 100151595729 127633543135232 Bool.false 9003887175 17179869184 402508181765 510534172540928 (BSN.cpow_neg_s_mk qz35 38999 1000 3 qz36 rfl)

noncomputable abbrev qz93 := (Real.sqrt qz316)

noncomputable abbrev qz94 := qz316

noncomputable def ep224 := @Enclosure.Real.IsNear.inv_image qz93 227023 131072 1 131072 37837 37838 65536 (@Enclosure.Real.IsNear.of_eq qz93 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz94 qz87)) Bool.false 227023 131072 1 131072 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz94 qz87)) Bool.false 227023 131072 1 131072 227023 131072 1 131072 (BSN.sqrt_enclosure 3 1 113511 113512 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep225 := BSN.log_dyadic_bound 1 2 9 8 2258332876800 65536 29717 222698787165 2027025 71998 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1) (BSN.artanhQ 2) 0 8 222698787165 2258332876800 2027025 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep226 := nat_lit 182334940436312956127111454351616

noncomputable def ep227 := BSN.sin_dyadic_bound_f 116203036 268435456 2 1 131072 59493 ep226 ep213 ep226 ep226 ep214 ep226 54984 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 116203036) qz298 0 1 ep226 ep213 ep226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 116203036) qz299 0 1 ep226 ep214 ep226 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz95 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz317 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1403925) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz318 := (BSN.isNear_log_sfrac 3 1 71998 65536 1 29717 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 71998 65536 29717 rfl rfl rfl (ep225 rfl)))

noncomputable def ep228 := @Enclosure.Real.IsNear.cos_image qz92 qz317 Bool.false 1403925 32768 173 131072 Bool.false 54984 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz92 Bool.false 1403925001 32768000 38999 29717000 1403925 32768 173 131072 (@Enclosure.Real.IsNear.mulLit_ff qz35 qz95 38999 1000 0 1 71998 65536 1 29717 1403925001 32768000 38999 29717000 qz90 qz318 rfl) rfl) (Enclosure.sfrac_false_div 1403925 32768) (BSN.cos_reduce3 qz317 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2044265442479670558720) qz300) 226375608064910080 72057594037927936 Bool.false 54984 131072 6 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q3 1403925 32768 226375608064910080 72057594037927936 6 2044265442479670558720 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 54984 131072 2044265442479670558720 4722366482869645213696 116203036 268435456 59493 59434 (ep227 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep229 := BSN.cos_dyadic_bound_f 116203036 268435456 2 1 131072 59493 ep226 ep217 ep226 ep226 ep218 ep226 118981 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 116203036) qz313 0 1 ep226 ep217 ep226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 116203036) qz314 0 1 ep226 ep218 ep226 rfl rfl rfl rfl) rfl rfl

noncomputable def ep230 := @Enclosure.Real.IsNear.sin_image qz92 qz317 Bool.false 1403925 32768 173 131072 Bool.true 118981 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz92 Bool.false 1403925001 32768000 38999 29717000 1403925 32768 173 131072 (@Enclosure.Real.IsNear.mulLit_ff qz35 qz95 38999 1000 0 1 71998 65536 1 29717 1403925001 32768000 38999 29717000 qz90 qz318 rfl) rfl) (Enclosure.sfrac_false_div 1403925 32768) (BSN.sin_reduce3 qz317 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2044265442479670558720) qz300) 226375608064910080 72057594037927936 Bool.false 118981 131072 6 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q3 1403925 32768 226375608064910080 72057594037927936 6 2044265442479670558720 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 118981 131072 2044265442479670558720 4722366482869645213696 116203036 268435456 59493 59434 (ep229 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz319 := (@Enclosure.Real.IsNear.recentre' qz91 Bool.false 75675 131072 1 131072 75675 131072 1 131072 (ep224 rfl rfl) rfl)

noncomputable def ep231 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz91 (Real.cos qz92)) (@HMul.hMul Real Real Real qz0 qz91 (@Neg.neg Real Real.instNeg (Real.sin qz92))) Bool.false 520114275 2147483648 100151595729 127633543135232 Bool.false 9003887175 17179869184 402508181765 510534172540928 (@Enclosure.Real.IsNear.mulLit_ff qz91 (Real.cos qz92) 75675 131072 1 131072 6873 16384 5272113 3895066624 520114275 2147483648 100151595729 127633543135232 qz319 (@Enclosure.Real.IsNear.recentre' (Real.cos qz92) Bool.false 54984 131072 5272113 3895066624 6873 16384 5272113 3895066624 (ep228 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz91 (@Neg.neg Real Real.instNeg (Real.sin qz92)) 75675 131072 1 131072 118981 131072 5272113 3895066624 9003887175 17179869184 402508181765 510534172540928 qz319 (@Enclosure.Real.IsNear.neg (Real.sin qz92) Bool.true 118981 131072 5272113 3895066624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz92) Bool.true 118981 131072 5272113 3895066624 118981 131072 5272113 3895066624 (ep230 rfl rfl) rfl)) rfl)

noncomputable def ep232 := @ep205 520114275 2147483648 100151595729 127633543135232 Bool.false 9003887175 17179869184 402508181765 510534172540928 Bool.false 18706832859917713408 8711047871 8589934592 445879916581 255267086270464 Bool.true 21429354107775221760 2494705155 17179869184 898522382267 510534172540928 (ep206 (BSN.head_sum_c_succ qz11 2 3 rfl rfl) (ep222 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep223 ep231) rfl rfl

noncomputable abbrev qz96 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable abbrev qz97 := (@HMul.hMul Real Real Real qz254 qz264 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep233 := @Enclosure.Complex.IsNear.of_eq qz79 (Complex.mk (@HMul.hMul Real Real Real qz0 qz96 (Real.cos qz97)) (@HMul.hMul Real Real Real qz0 qz96 (@Neg.neg Real Real.instNeg (Real.sin qz97)))) Bool.true 6802074255 17179869184 348597614149 510534172540928 Bool.false 5245486935 17179869184 347891775965 510534172540928 (BSN.cpow_neg_s_mk qz35 38999 1000 4 qz36 rfl)

noncomputable abbrev qz98 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable def ep234 := @Enclosure.Real.IsNear.inv_image qz98 262145 131072 1 131072 32767 32768 65536 (@Enclosure.Real.IsNear.of_eq qz98 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4) qz87)) Bool.false 262145 131072 1 131072 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4) qz87)) Bool.false 262145 131072 1 131072 262145 131072 1 131072 (BSN.sqrt_enclosure 4 1 131072 131073 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep235 := nat_lit 753960950911045074462890625

noncomputable def ep236 := nat_lit 117048680082474133384580175

noncomputable def ep237 := BSN.log_dyadic_bound 3 5 12 11 ep235 65536 29717 ep236 431467934736729065175 90852 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 3) (BSN.artanhQ 5) 0 11 ep236 ep235 431467934736729065175 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep238 := nat_lit 966873712145850657664912149610000

noncomputable def ep239 := BSN.cos_dyadic_bound_f 176336590 268435456 2 1 131072 59493 ep238 ep217 ep238 ep238 ep218 ep238 103793 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 176336590) qz313 0 1 ep238 ep217 ep238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 176336590) qz314 0 1 ep238 ep218 ep238 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz99 := (@Nat.cast Real Real.instNatCast 65536)

noncomputable abbrev qz100 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz320 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3543137) qz99)

noncomputable abbrev qz321 := (BSN.isNear_log_sfrac 4 1 90852 65536 1 29717 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 90852 65536 29717 rfl rfl rfl (ep237 rfl)))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep240 := @Enclosure.Real.IsNear.cos_image qz97 qz320 Bool.false 3543137 65536 173 131072 Bool.true 103793 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz97 Bool.false 885784287 16384000 38999 29717000 3543137 65536 173 131072 (@Enclosure.Real.IsNear.mulLit_ff qz35 qz100 38999 1000 0 1 90852 65536 1 29717 885784287 16384000 38999 29717000 qz90 qz321 rfl) rfl) (Enclosure.sfrac_false_div 3543137 65536) (BSN.cos_reduce2 qz320 (@HDiv.hDiv Real Real Real qz2 qz311 qz322) 226375608064910080 72057594037927936 Bool.false 103793 131072 8 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q2 3543137 65536 226375608064910080 72057594037927936 8 6204292228697548652544 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 103793 131072 6204292228697548652544 9444732965739290427392 176336590 268435456 59493 59434 (ep239 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep241 := BSN.sin_dyadic_bound_f 176336590 268435456 2 1 131072 59493 ep238 ep213 ep238 ep238 ep214 ep238 80041 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 176336590) qz298 0 1 ep238 ep213 ep238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 176336590) qz299 0 1 ep238 ep214 ep238 rfl rfl rfl rfl) rfl rfl

noncomputable def ep242 := @Enclosure.Real.IsNear.sin_image qz97 qz320 Bool.false 3543137 65536 173 131072 Bool.true 80041 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz97 Bool.false 885784287 16384000 38999 29717000 3543137 65536 173 131072 (@Enclosure.Real.IsNear.mulLit_ff qz35 qz100 38999 1000 0 1 90852 65536 1 29717 885784287 16384000 38999 29717000 qz90 qz321 rfl) rfl) (Enclosure.sfrac_false_div 3543137 65536) (BSN.sin_reduce2 qz320 (@HDiv.hDiv Real Real Real qz2 qz311 qz322) 226375608064910080 72057594037927936 Bool.false 80041 131072 8 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q2 3543137 65536 226375608064910080 72057594037927936 8 6204292228697548652544 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 80041 131072 6204292228697548652544 9444732965739290427392 176336590 268435456 59493 59434 (ep241 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz323 := (@Enclosure.Real.IsNear.recentre' qz96 Bool.false 65535 131072 1 131072 65535 131072 1 131072 (ep234 rfl rfl) rfl)

noncomputable def ep243 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz96 (Real.cos qz97)) (@HMul.hMul Real Real Real qz0 qz96 (@Neg.neg Real Real.instNeg (Real.sin qz97))) Bool.true 6802074255 17179869184 348597614149 510534172540928 Bool.false 5245486935 17179869184 347891775965 510534172540928 (@Enclosure.Real.IsNear.mulLit_ft qz96 (Real.cos qz97) 65535 131072 1 131072 103793 131072 5272113 3895066624 6802074255 17179869184 348597614149 510534172540928 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz97) Bool.true 103793 131072 5272113 3895066624 103793 131072 5272113 3895066624 (ep240 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz96 (@Neg.neg Real Real.instNeg (Real.sin qz97)) 65535 131072 1 131072 80041 131072 5272113 3895066624 5245486935 17179869184 347891775965 510534172540928 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz97) Bool.true 80041 131072 5272113 3895066624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz97) Bool.true 80041 131072 5272113 3895066624 80041 131072 5272113 3895066624 (ep242 rfl rfl) rfl)) rfl)

noncomputable def ep244 := @ep203 6802074255 17179869184 348597614149 510534172540928 Bool.false 5245486935 17179869184 347891775965 510534172540928 Bool.false 91225289938964578304 10620021487 17179869184 1240357447311 510534172540928 Bool.false 47258071134130667520 687695445 4294967296 155801769779 63816771567616 (ep204 (BSN.head_sum_c_succ qz11 3 4 rfl rfl) (ep232 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep233 ep243) rfl rfl

noncomputable abbrev qz101 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable abbrev qz102 := (@HMul.hMul Real Real Real qz254 qz264 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep245 := @Enclosure.Complex.IsNear.of_eq qz77 (Complex.mk (@HMul.hMul Real Real Real qz0 qz101 (Real.cos qz102)) (@HMul.hMul Real Real Real qz0 qz101 (@Neg.neg Real Real.instNeg (Real.sin qz102)))) Bool.false 7666576047 17179869184 312927435981 510534172540928 Bool.false 502523541 17179869184 309295483675 510534172540928 (BSN.cpow_neg_s_mk qz35 38999 1000 5 qz36 rfl)

noncomputable abbrev qz103 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def ep246 := @Enclosure.Real.IsNear.inv_image qz103 293085 131072 1 131072 29308 29309 65536 (@Enclosure.Real.IsNear.of_eq qz103 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5) qz87)) Bool.false 293085 131072 1 131072 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5) qz87)) Bool.false 293085 131072 1 131072 293085 131072 1 131072 (BSN.sqrt_enclosure 5 1 146542 146543 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep247 := nat_lit 141613827518379161815574079375

noncomputable def ep248 := nat_lit 29325128709309236875766211300

noncomputable def ep249 := BSN.log_dyadic_bound 2 3 15 14 ep247 65536 29717 ep248 57299708096576225280000 105476 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP 2) (BSN.artanhQ 3) 0 14 ep248 ep247 57299708096576225280000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep250 := nat_lit 419348119305180556739738439399216917771589466812400066450614144890777665

noncomputable def ep251 := nat_lit 710874808016663285741062232492244022546351657067729969412124505747521

noncomputable def ep252 := nat_lit 1097141753252969717570019907192961627650992605635319087420179320752255041

noncomputable def ep253 := BSN.sin_dyadic_bound_f 404086313 268435456 3 2 131072 59493 ep250 ep180 ep251 ep252 ep183 ep251 130791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 404086313) qz298 0 2 ep250 ep180 ep251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 404086313) qz299 0 2 ep252 ep183 ep251 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz104 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz324 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8226917) qz88)

noncomputable abbrev qz325 := (BSN.isNear_log_sfrac 5 1 105476 65536 1 29717 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 105476 65536 29717 rfl rfl rfl (ep249 rfl)))

noncomputable def ep254 := @Enclosure.Real.IsNear.cos_image qz102 qz324 Bool.false 8226917 131072 173 131072 Bool.false 130791 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz102 Bool.false 1028364631 16384000 38999 29717000 8226917 131072 173 131072 (@Enclosure.Real.IsNear.mulLit_ff qz35 qz104 38999 1000 0 1 105476 65536 1 29717 1028364631 16384000 38999 29717000 qz90 qz325 rfl) rfl) (Enclosure.sfrac_false_div 8226917 131072) (BSN.cos_reduce3 qz324 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28435046428384096681984) qz312) 226375608064910080 72057594037927936 Bool.false 130791 131072 9 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q3 8226917 131072 226375608064910080 72057594037927936 9 28435046428384096681984 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 130791 131072 28435046428384096681984 18889465931478580854784 404086313 268435456 59493 59434 (ep253 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep255 := nat_lit 233287121750885492982406271769561507216459193410030139125635469164097601

noncomputable def ep256 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120

noncomputable def ep257 := nat_lit 698439615636623152375736690843700033604284876915954957438082158480797761

noncomputable def ep258 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400

noncomputable def ep259 := BSN.cos_dyadic_bound_f 404086313 268435456 3 2 131072 59493 ep255 ep256 ep251 ep257 ep258 ep251 8573 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 404086313) qz313 0 2 ep255 ep256 ep251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 404086313) qz314 0 2 ep257 ep258 ep251 rfl rfl rfl rfl) rfl rfl

noncomputable def ep260 := @Enclosure.Real.IsNear.sin_image qz102 qz324 Bool.false 8226917 131072 173 131072 Bool.true 8573 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz102 Bool.false 1028364631 16384000 38999 29717000 8226917 131072 173 131072 (@Enclosure.Real.IsNear.mulLit_ff qz35 qz104 38999 1000 0 1 105476 65536 1 29717 1028364631 16384000 38999 29717000 qz90 qz325 rfl) rfl) (Enclosure.sfrac_false_div 8226917 131072) (BSN.sin_reduce3 qz324 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28435046428384096681984) qz312) 226375608064910080 72057594037927936 Bool.false 8573 131072 9 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q3 8226917 131072 226375608064910080 72057594037927936 9 28435046428384096681984 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8573 131072 28435046428384096681984 18889465931478580854784 404086313 268435456 59493 59434 (ep259 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz326 := (@Enclosure.Real.IsNear.recentre' qz101 Bool.false 58617 131072 1 131072 58617 131072 1 131072 (ep246 rfl rfl) rfl)

noncomputable def ep261 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz101 (Real.cos qz102)) (@HMul.hMul Real Real Real qz0 qz101 (@Neg.neg Real Real.instNeg (Real.sin qz102))) Bool.false 7666576047 17179869184 312927435981 510534172540928 Bool.false 502523541 17179869184 309295483675 510534172540928 (@Enclosure.Real.IsNear.mulLit_ff qz101 (Real.cos qz102) 58617 131072 1 131072 130791 131072 5272113 3895066624 7666576047 17179869184 312927435981 510534172540928 qz326 (@Enclosure.Real.IsNear.recentre' (Real.cos qz102) Bool.false 130791 131072 5272113 3895066624 130791 131072 5272113 3895066624 (ep254 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz101 (@Neg.neg Real Real.instNeg (Real.sin qz102)) 58617 131072 1 131072 8573 131072 5272113 3895066624 502523541 17179869184 309295483675 510534172540928 qz326 (@Enclosure.Real.IsNear.neg (Real.sin qz102) Bool.true 8573 131072 5272113 3895066624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz102) Bool.true 8573 131072 5272113 3895066624 8573 131072 5272113 3895066624 (ep260 rfl rfl) rfl)) rfl)

noncomputable def ep262 := @ep201 7666576047 17179869184 312927435981 510534172540928 Bool.false 502523541 17179869184 309295483675 510534172540928 Bool.false 314161353454576992256 9143298767 8589934592 388321220823 127633543135232 Bool.false 13972839957597782016 3253305321 17179869184 1555709641907 510534172540928 (ep202 (BSN.head_sum_c_succ qz11 4 5 rfl rfl) (ep244 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep245 ep261) rfl rfl

noncomputable abbrev qz327 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz105 := (@Inv.inv Real Real.instInv (Real.sqrt qz327))

noncomputable abbrev qz106 := (@HMul.hMul Real Real Real qz254 qz264 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep263 := @Enclosure.Complex.IsNear.of_eq qz75 (Complex.mk (@HMul.hMul Real Real Real qz0 qz105 (Real.cos qz106)) (@HMul.hMul Real Real Real qz0 qz105 (@Neg.neg Real Real.instNeg (Real.sin qz106)))) Bool.false 1269176935 4294967296 71940013043 127633543135232 Bool.true 2419588425 8589934592 143748112323 255267086270464 (BSN.cpow_neg_s_mk qz35 38999 1000 6 qz36 rfl)

noncomputable abbrev qz107 := (Real.sqrt qz327)

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz87)

noncomputable def ep264 := @Enclosure.Real.IsNear.inv_image qz107 321059 131072 1 131072 26754 26756 65536 (@Enclosure.Real.IsNear.of_eq qz107 (Real.sqrt qz328) Bool.false 321059 131072 1 131072 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz328) Bool.false 321059 131072 1 131072 321059 131072 1 131072 (BSN.sqrt_enclosure 6 1 160529 160530 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep265 := BSN.log_dyadic_bound 2 10 4 3 105000000 65536 29717 1434560 960 26572 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz108 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep266 := @Enclosure.Real.IsNear.mulLit_ff qz35 qz108 38999 1000 0 1 4034664351997175 2251799813685248 500000000029717 14858500000000000000 6293915002541513113 90071992547409920 19499500001158933283 14858500000000000000000 qz90 (BSN.isNear_log_sfrac 6 1 4034664351997175 2251799813685248 500000000029717 14858500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz328) Bool.false 4230652207559789772800 2361183241434822606848 1000000000059434 29717000000000000000 4034664351997175 2251799813685248 500000000029717 14858500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 26572 65536 24973259072661432 36028797018963968 29717 1000000000000000 rfl rfl rfl rfl (ep265 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep267 := nat_lit 1745515058644822954818612326400256

noncomputable def ep268 := BSN.cos_dyadic_bound_f 204400004 268435456 2 1 131072 59493 ep267 ep217 ep267 ep267 ep218 ep267 94874 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 204400004) qz313 0 1 ep267 ep217 ep267 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 204400004) qz314 0 1 ep267 ep218 ep267 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9158851) qz88)

noncomputable def ep269 := @Enclosure.Real.IsNear.cos_image qz106 qz329 Bool.false 9158851 131072 173 131072 Bool.false 94874 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 6293915002541513113 90071992547409920 19499500001158933283 14858500000000000000000 9158851 131072 173 131072 (ep266 rfl) rfl) (Enclosure.sfrac_false_div 9158851 131072) (BSN.cos_reduce0 qz329 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14383371611249292869632) qz312) 226375608064910080 72057594037927936 Bool.false 94874 131072 11 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q0 9158851 131072 226375608064910080 72057594037927936 11 14383371611249292869632 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 94874 131072 14383371611249292869632 18889465931478580854784 204400004 268435456 59493 59434 (ep268 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep270 := BSN.sin_dyadic_bound_f 204400004 268435456 2 1 131072 59493 ep267 ep213 ep267 ep267 ep214 ep267 90435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 204400004) qz298 0 1 ep267 ep213 ep267 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 204400004) qz299 0 1 ep267 ep214 ep267 rfl rfl rfl rfl) rfl rfl

noncomputable def ep271 := @Enclosure.Real.IsNear.sin_image qz106 qz329 Bool.false 9158851 131072 173 131072 Bool.false 90435 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 6293915002541513113 90071992547409920 19499500001158933283 14858500000000000000000 9158851 131072 173 131072 (ep266 rfl) rfl) (Enclosure.sfrac_false_div 9158851 131072) (BSN.sin_reduce0 qz329 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14383371611249292869632) qz312) 226375608064910080 72057594037927936 Bool.false 90435 131072 11 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q0 9158851 131072 226375608064910080 72057594037927936 11 14383371611249292869632 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 90435 131072 14383371611249292869632 18889465931478580854784 204400004 268435456 59493 59434 (ep270 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz330 := (@Enclosure.Real.IsNear.recentre' qz105 Bool.false 53510 131072 2 131072 26755 65536 1 65536 (ep264 rfl rfl) rfl)

noncomputable def ep272 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz105 (Real.cos qz106)) (@HMul.hMul Real Real Real qz0 qz105 (@Neg.neg Real Real.instNeg (Real.sin qz106))) Bool.false 1269176935 4294967296 71940013043 127633543135232 Bool.true 2419588425 8589934592 143748112323 255267086270464 (@Enclosure.Real.IsNear.mulLit_ff qz105 (Real.cos qz106) 26755 65536 1 65536 47437 65536 5272113 3895066624 1269176935 4294967296 71940013043 127633543135232 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz106) Bool.false 94874 131072 5272113 3895066624 47437 65536 5272113 3895066624 (ep269 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz105 (@Neg.neg Real Real.instNeg (Real.sin qz106)) 26755 65536 1 65536 90435 131072 5272113 3895066624 2419588425 8589934592 143748112323 255267086270464 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz106) Bool.false 90435 131072 5272113 3895066624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz106) Bool.false 90435 131072 5272113 3895066624 90435 131072 5272113 3895066624 (ep271 rfl rfl) rfl)) rfl)

noncomputable def ep273 := @ep199 1269176935 4294967296 71940013043 127633543135232 Bool.true 2419588425 8589934592 143748112323 255267086270464 Bool.false 50172316039147159552 11681652637 8589934592 230130616933 63816771567616 Bool.true 13622532705425031168 1585871529 17179869184 1843205866553 510534172540928 (ep200 (BSN.head_sum_c_succ qz11 5 6 rfl rfl) (ep262 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep263 ep272) rfl rfl

noncomputable abbrev qz331 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz109 := (@Inv.inv Real Real.instInv (Real.sqrt qz331))

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz254 qz264 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep274 := @Enclosure.Complex.IsNear.of_eq qz73 (Complex.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz110)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110)))) Bool.false 5730159765 17179869184 264628239051 510534172540928 Bool.true 3054450355 17179869184 263023223881 510534172540928 (BSN.cpow_neg_s_mk qz35 38999 1000 7 qz36 rfl)

noncomputable abbrev qz111 := (Real.sqrt qz331)

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) qz87)

noncomputable def ep275 := @Enclosure.Real.IsNear.inv_image qz111 346783 131072 1 131072 24770 24771 65536 (@Enclosure.Real.IsNear.of_eq qz111 (Real.sqrt qz332) Bool.false 346783 131072 1 131072 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz332) Bool.false 346783 131072 1 131072 346783 131072 1 131072 (BSN.sqrt_enclosure 7 1 173391 173392 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep276 := BSN.log_dyadic_bound 3 11 5 4 202569142545 65536 29717 5259111624 688905 36674 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz112 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep277 := @Enclosure.Real.IsNear.mulLit_ff qz35 qz112 38999 1000 0 1 4381766428990711 2251799813685248 500000000029717 14858500000000000000 170884508964208738289 2251799813685248000 19499500001158933283 14858500000000000000000 qz90 (BSN.isNear_log_sfrac 7 1 4381766428990711 2251799813685248 500000000029717 14858500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz332) Bool.false 4594615115045363777536 2361183241434822606848 1000000000059434 29717000000000000000 4381766428990711 2251799813685248 500000000029717 14858500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 36674 65536 24973259072661432 36028797018963968 29717 1000000000000000 rfl rfl rfl rfl (ep276 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep278 := nat_lit 298687500592363559826744876325521

noncomputable def ep279 := BSN.cos_dyadic_bound_f 131463219 268435456 2 1 131072 59493 ep278 ep217 ep278 ep278 ep218 ep278 115665 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 131463219) qz313 0 1 ep278 ep217 ep278 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 131463219) qz314 0 1 ep278 ep218 ep278 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9946787) qz88)

noncomputable def ep280 := @Enclosure.Real.IsNear.cos_image qz110 qz333 Bool.false 9946787 131072 173 131072 Bool.false 115665 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz110 Bool.false 170884508964208738289 2251799813685248000 19499500001158933283 14858500000000000000000 9946787 131072 173 131072 (ep277 rfl) rfl) (Enclosure.sfrac_false_div 9946787 131072) (BSN.cos_reduce0 qz333 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9250901641851289206784) qz312) 226375608064910080 72057594037927936 Bool.false 115665 131072 12 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q0 9946787 131072 226375608064910080 72057594037927936 12 9250901641851289206784 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 115665 131072 9250901641851289206784 18889465931478580854784 131463219 268435456 59493 59434 (ep279 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep281 := BSN.sin_dyadic_bound_f 131463219 268435456 2 1 131072 59493 ep278 ep213 ep278 ep278 ep214 ep278 61655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 131463219) qz298 0 1 ep278 ep213 ep278 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 131463219) qz299 0 1 ep278 ep214 ep278 rfl rfl rfl rfl) rfl rfl

noncomputable def ep282 := @Enclosure.Real.IsNear.sin_image qz110 qz333 Bool.false 9946787 131072 173 131072 Bool.false 61655 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz110 Bool.false 170884508964208738289 2251799813685248000 19499500001158933283 14858500000000000000000 9946787 131072 173 131072 (ep277 rfl) rfl) (Enclosure.sfrac_false_div 9946787 131072) (BSN.sin_reduce0 qz333 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9250901641851289206784) qz312) 226375608064910080 72057594037927936 Bool.false 61655 131072 12 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q0 9946787 131072 226375608064910080 72057594037927936 12 9250901641851289206784 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 61655 131072 9250901641851289206784 18889465931478580854784 131463219 268435456 59493 59434 (ep281 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz334 := (@Enclosure.Real.IsNear.recentre' qz109 Bool.false 49541 131072 1 131072 49541 131072 1 131072 (ep275 rfl rfl) rfl)

noncomputable def ep283 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz110)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110))) Bool.false 5730159765 17179869184 264628239051 510534172540928 Bool.true 3054450355 17179869184 263023223881 510534172540928 (@Enclosure.Real.IsNear.mulLit_ff qz109 (Real.cos qz110) 49541 131072 1 131072 115665 131072 5272113 3895066624 5730159765 17179869184 264628239051 510534172540928 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz110) Bool.false 115665 131072 5272113 3895066624 115665 131072 5272113 3895066624 (ep280 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110)) 49541 131072 1 131072 61655 131072 5272113 3895066624 3054450355 17179869184 263023223881 510534172540928 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz110) Bool.false 61655 131072 5272113 3895066624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz110) Bool.false 61655 131072 5272113 3895066624 61655 131072 5272113 3895066624 (ep282 rfl rfl) rfl)) rfl)

noncomputable def ep284 := @ep197 5730159765 17179869184 264628239051 510534172540928 Bool.true 3054450355 17179869184 263023223881 510534172540928 Bool.false 249910961739648729088 29093465039 17179869184 2105673174515 510534172540928 Bool.true 79720122938772422656 1160080471 4294967296 1053114545217 255267086270464 (ep198 (BSN.head_sum_c_succ qz11 6 7 rfl rfl) (ep273 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep274 ep283) rfl rfl

noncomputable def ep285 := @Enclosure.Complex.IsNear.mul qz67 (@HAdd.hAdd Complex Complex Complex qz8 qz68 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))) Bool.false 91010647078026656479929 836273151473392549888000 ep190 ep55 Bool.false

noncomputable abbrev qz113 := (Complex.re qz303)

noncomputable abbrev qz114 := (Complex.im qz303)

noncomputable def ep286 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz113 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz68 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz114 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz68 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))))) 30965860798898524863 209068287868348137472 18169647283202465244103

noncomputable def ep287 := nat_lit 74554587727004419215065088

noncomputable def ep288 := nat_lit 1447922065761069866835107

noncomputable def ep289 := nat_lit 19027440162393514290922172123136906900799488

noncomputable def ep290 := @Enclosure.Real.IsNear.mulLit_ff qz113 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz68 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))))) 632879037 2147483648 123783510599 255267086270464 146785684097

noncomputable abbrev qz335 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz115 := (@Inv.inv Real Real.instInv (Real.sqrt qz335))

noncomputable abbrev qz336 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz418 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable abbrev qz116 := (Real.cos qz336)

noncomputable abbrev qz117 := (@Neg.neg Real Real.instNeg (Real.sin qz336))

noncomputable def ep291 := @Enclosure.Complex.IsNear.of_eq qz67 (Complex.mk (@HMul.hMul Real Real Real qz0 qz115 qz116) (@HMul.hMul Real Real Real qz0 qz115 qz117)) Bool.false 632879037 2147483648 123783510599 255267086270464 Bool.false 3355412787 17179869184 246471979465 510534172540928 (BSN.cpow_neg_s_mk qz35 38999 1000 8 qz36 rfl)

noncomputable abbrev qz118 := (Real.sqrt qz335)

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz87)

noncomputable def ep292 := @Enclosure.Real.IsNear.inv_image qz118 370727 131072 1 131072 23170 23171 65536 (@Enclosure.Real.IsNear.of_eq qz118 (Real.sqrt qz337) Bool.false 370727 131072 1 131072 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz337) Bool.false 370727 131072 1 131072 370727 131072 1 131072 (BSN.sqrt_enclosure 8 1 185363 185364 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep293 := BSN.log_dyadic_bound 0 16 1 0 1 65536 29717 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz338 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz119 := qz338

noncomputable abbrev qz339 := (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz87))

noncomputable def ep294 := @Enclosure.Real.IsNear.mulLit_ff qz35 qz119 38999 1000 0 1 9364972152248037 4503599627370496 1000000000089151 29717000000000000000 365224548965521194963 4503599627370496000 38999000003476799849 29717000000000000000000 qz90 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000089151 29717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz339 Bool.false 4909942519757818822656 2361183241434822606848 1000000000089151 29717000000000000000 9364972152248037 4503599627370496 1000000000089151 29717000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 65536 24973259072661432 36028797018963968 29717 1000000000000000 rfl rfl rfl rfl (ep293 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep295 := nat_lit 4898134231349060902396792492916496

noncomputable def ep296 := BSN.sin_dyadic_bound_f 264549942 268435456 2 1 131072 59493 ep295 ep213 ep295 ep295 ep214 ep295 109256 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 264549942) qz298 0 1 ep295 ep213 ep295 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 264549942) qz299 0 1 ep295 ep214 ep295 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz120 := qz336

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10629433) qz88)

noncomputable def ep297 := @Enclosure.Real.IsNear.cos_image qz120 qz340 Bool.false 10629433 131072 173 131072 Bool.false 109256 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 365224548965521194963 4503599627370496000 38999000003476799849 29717000000000000000000 10629433 131072 173 131072 (ep294 rfl) rfl) (Enclosure.sfrac_false_div 10629433 131072) (BSN.cos_reduce3 qz340 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18616047220230314786816) qz312) 226375608064910080 72057594037927936 Bool.false 109256 131072 12 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q3 10629433 131072 226375608064910080 72057594037927936 12 18616047220230314786816 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 109256 131072 18616047220230314786816 18889465931478580854784 264549942 268435456 59493 59434 (ep296 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep298 := nat_lit 42750704248902574442773105193359232206490746532478498752596079642992896

noncomputable def ep299 := nat_lit 23991718948313455670588802021898291259475117691313671528336028918016

noncomputable def ep300 := nat_lit 128204129308811096416978137976033900036953289362052868914731566871142656

noncomputable def ep301 := BSN.cos_dyadic_bound_f 264549942 268435456 3 2 131072 59493 ep298 ep256 ep299 ep300 ep258 ep299 72407 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 264549942) qz313 0 2 ep298 ep256 ep299 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 264549942) qz314 0 2 ep300 ep258 ep299 rfl rfl rfl rfl) rfl rfl

noncomputable def ep302 := @Enclosure.Real.IsNear.sin_image qz120 qz340 Bool.false 10629433 131072 173 131072 Bool.true 72407 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 365224548965521194963 4503599627370496000 38999000003476799849 29717000000000000000000 10629433 131072 173 131072 (ep294 rfl) rfl) (Enclosure.sfrac_false_div 10629433 131072) (BSN.sin_reduce3 qz340 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18616047220230314786816) qz312) 226375608064910080 72057594037927936 Bool.false 72407 131072 12 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q3 10629433 131072 226375608064910080 72057594037927936 12 18616047220230314786816 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 72407 131072 18616047220230314786816 18889465931478580854784 264549942 268435456 59493 59434 (ep301 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz121 := (Real.sin qz336)

noncomputable abbrev qz341 := (@Enclosure.Real.IsNear.recentre' qz115 Bool.false 46341 131072 1 131072 46341 131072 1 131072 (ep292 rfl rfl) rfl)

noncomputable def ep303 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz115 qz116) (@HMul.hMul Real Real Real qz0 qz115 qz117) Bool.false 632879037 2147483648 123783510599 255267086270464 Bool.false 3355412787 17179869184 246471979465 510534172540928 (@Enclosure.Real.IsNear.mulLit_ff qz115 qz116 46341 131072 1 131072 13657 16384 5272113 3895066624 632879037 2147483648 123783510599 255267086270464 qz341 (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 109256 131072 5272113 3895066624 13657 16384 5272113 3895066624 (ep297 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz115 qz117 46341 131072 1 131072 72407 131072 5272113 3895066624 3355412787 17179869184 246471979465 510534172540928 qz341 (@Enclosure.Real.IsNear.neg qz121 Bool.true 72407 131072 5272113 3895066624 (@Enclosure.Real.IsNear.recentre' qz121 Bool.true 72407 131072 5272113 3895066624 72407 131072 5272113 3895066624 (ep302 rfl rfl) rfl)) rfl)

noncomputable def ep304 := @ep290 292065024192 0 1 30965860798898524863 209068287868348137472 18169647283202465244103 ep287 (@Enclosure.Complex.IsNear.re_isNear qz67 Bool.false 632879037 2147483648 123783510599 255267086270464 Bool.false 3355412787 17179869184 246471979465 510534172540928 (ep291 ep303))

noncomputable def ep305 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz68 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))) Bool.false 146785684097 292065024192 0 1 Bool.false

noncomputable def ep306 := @Enclosure.Complex.IsNear.addLitP qz68 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) Bool.false 1513172001 3042344002 0 1 Bool.true 311992000

noncomputable def ep307 := @ep306 1521172001 0 1 Bool.false 1 192 0 1 Bool.false 38999 96000 0 1 Bool.false 293571368194 146785684097 292065024192 0 1 Bool.false 29372954866999 29372954866999 146032512096000 0 1

noncomputable abbrev qz122 := (@HDiv.hDiv Complex Complex Complex qz270 qz304 (@HSub.hSub Complex Complex Complex qz260 qz265 (1 : Complex)))

noncomputable def ep308 := @Enclosure.Complex.IsNear.addLitP qz122 qz39 Bool.true 16000000 6084688004 0 1 Bool.true 1247968000 6084688004 0 1

noncomputable def ep309 := @Enclosure.Complex.IsNear.of_eq qz122 (Complex.mk (Enclosure.sfrac Bool.true 16000000 6084688004) (Enclosure.sfrac Bool.true 1247968000 6084688004)) Bool.true 16000000 6084688004 0 1 Bool.true 1247968000 6084688004 0 1

noncomputable def ep310 := @ep308 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 6052688004 1513172001 3042344002 0 1 Bool.true 1247968000 311992000 1521172001 0 1 (ep309 (BSN.N_div_s_sub_one_mk qz35 38999 1000 8 qz36 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 16000000 6084688004) (Enclosure.sfrac Bool.true 1247968000 6084688004) Bool.true 16000000 6084688004 0 1 Bool.true 1247968000 6084688004 0 1 (Enclosure.Real.IsNear.const Bool.true 16000000 6084688004) (Enclosure.Real.IsNear.const Bool.true 1247968000 6084688004))) qz41 rfl

noncomputable abbrev qz123 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz342 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz423 (@Nat.cast Complex Complex.instNatCast 8) 1))

noncomputable abbrev qz124 := qz342

noncomputable def ep311 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz124)) Bool.false 1 192 0 1

noncomputable def ep312 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz124) Bool.false 0 1 0 1 Bool.false

noncomputable def ep313 := @ep312 0 1 0 1 Bool.false 1 192 0 1 Bool.false 38999 96000 0 1 Bool.false 1 1 192 0 1 Bool.false 38999 38999 96000 0

noncomputable def ep314 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (Complex.mk qz42 qz42) Bool.false 0 1 0 1 Bool.false

noncomputable def ep315 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz124 Bool.false 1 192 0 1 Bool.false 38999 96000 0 1

noncomputable abbrev qz125 := (Complex.re qz342)

noncomputable abbrev qz126 := (Complex.im qz342)

noncomputable def ep316 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz125) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126) 1 192 0 1 0 1 0

noncomputable def ep317 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz125 1 24 0 1 1 8 0 1 1

noncomputable def ep318 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep319 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep320 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz42) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow07.d6 rfl) qz289

noncomputable def ep321 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz11 Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 (BSN.ascPochhammer_one_eval qz11)

noncomputable def ep322 := ep321 (@Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk qz31 qz35) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 (BSN.s_crit_mk qz35 Bool.false 38999 1000 qz36) (@Enclosure.Complex.IsNear.mk qz31 qz35 Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 qz32 qz90))

noncomputable def ep323 := @ep319 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep320) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep322)

noncomputable def ep324 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 38999 1000 0 1 0 1 0

noncomputable def ep325 := @ep324 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep320) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep322)

noncomputable def ep326 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) 38999 12000 0 1 0 1 0 1 38999

noncomputable def ep327 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 38999 1000 0 1 38999 12000 0

noncomputable def ep328 := @ep327 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep320) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep322)

noncomputable def ep329 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep330 := @ep329 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep320) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep322)

noncomputable def ep331 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 38999 12000 0 1 (@ep318 1 24 0 1 (ep323 rfl) (ep325 rfl) rfl rfl) (@ep326 38999 12000 0 1 (ep328 rfl) (ep330 rfl) rfl rfl)

noncomputable def ep332 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 38999 12000 0 1 ep331

noncomputable abbrev qz127 := (@Enclosure.Complex.IsNear.of_eq qz342 (Complex.mk (Enclosure.sfrac Bool.false 1 8) qz285) Bool.false 1 8 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 8 1 8 EMRow07.d7 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 8) qz285 Bool.false 1 8 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 8) qz286))

noncomputable def ep333 := @ep317 192 0 1 ep332 (@Enclosure.Complex.IsNear.re_isNear qz124 Bool.false 1 8 0 1 Bool.false 0 1 0 1 qz127)

noncomputable def ep334 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126 38999 12000 0 1 0 1 0 1 0

noncomputable def ep335 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 38999 12000 0 1 ep331

noncomputable def ep336 := @ep334 1 0 1 ep335 (@Enclosure.Complex.IsNear.im_isNear qz124 Bool.false 1 8 0 1 Bool.false 0 1 0 1 qz127)

noncomputable def ep337 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz125) 0 1 0 1 38999 96000 0

noncomputable def ep338 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126 1 24 0 1 0 1 0 1 0

noncomputable def ep339 := @ep338 1 0 1 ep332 (@Enclosure.Complex.IsNear.im_isNear qz124 Bool.false 1 8 0 1 Bool.false 0 1 0 1 qz127)

noncomputable def ep340 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz125 38999 12000 0 1 1 8 0 1 38999

noncomputable def ep341 := @ep340 96000 0 1 ep335 (@Enclosure.Complex.IsNear.re_isNear qz124 Bool.false 1 8 0 1 Bool.false 0 1 0 1 qz127)

noncomputable def ep342 := @ep313 1 (@ep314 0 1 0 1 (BSN.bern_sum_base qz11 8) qz59) (ep315 (@ep316 1 1 1 192 0 1 (ep333 rfl) (ep336 rfl) rfl rfl) (@ep337 1 38999 38999 96000 0 1 (ep339 rfl) (ep341 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep343 := ep307 (ep310 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep311 Bool.false 38999 96000 0 1 (BSN.bern_sum_succ qz11 8 0 1 1 rfl rfl) (ep342 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep344 := @Enclosure.Real.IsNear.mulLit_ff qz114 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz68 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))))) 3355412787 17179869184 246471979465 510534172540928 29372954866999

noncomputable def ep345 := @ep344 146032512096000 0 1 32852796117567442972071 836273151473392549888000 ep288 ep55 (@Enclosure.Complex.IsNear.im_isNear qz67 Bool.false 632879037 2147483648 123783510599 255267086270464 Bool.false 3355412787 17179869184 246471979465 510534172540928 (ep291 ep303))

noncomputable def ep346 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz68 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))) Bool.false 146785684097 292065024192 0 1 Bool.false

noncomputable def ep347 := nat_lit 3635887470103119351822401

noncomputable def ep348 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz113 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz68 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz114 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz68 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))))) 6196509130023596733321 104534143934174068736000 ep347

noncomputable def ep349 := nat_lit 149109175454008838430130176

noncomputable def ep350 := nat_lit 27525895922399041310569003130905145792004096

noncomputable def ep351 := @Enclosure.Real.IsNear.mulLit_ff qz113 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz68 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))))) 632879037 2147483648 123783510599 255267086270464 29372954866999

noncomputable def ep352 := @ep351 146032512096000 0 1 6196509130023596733321 104534143934174068736000 ep347 ep187 (@Enclosure.Complex.IsNear.re_isNear qz67 Bool.false 632879037 2147483648 123783510599 255267086270464 Bool.false 3355412787 17179869184 246471979465 510534172540928 (ep291 ep303))

noncomputable def ep353 := @Enclosure.Real.IsNear.mulLit_ff qz114 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz68 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz71 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))))) 3355412787 17179869184 246471979465 510534172540928 146785684097

noncomputable def ep354 := @ep353 292065024192 0 1 164175520455872116113 1672546302946785099776 36178558116511761068105 ep349 (@Enclosure.Complex.IsNear.im_isNear qz67 Bool.false 632879037 2147483648 123783510599 255267086270464 Bool.false 3355412787 17179869184 246471979465 510534172540928 (ep291 ep303))

noncomputable abbrev qz343 := (ep343 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep355 := @ep285 32914958317031207980767 209068287868348137472000 ep191 ep187 (@ep286 ep287 32852796117567442972071 836273151473392549888000 ep288 ep55 ep289 91010647078026656479929 836273151473392549888000 ep190 ep55 (ep304 (@ep305 29372954866999 146032512096000 0 1 qz343) rfl) (ep345 (@ep346 29372954866999 146032512096000 0 1 qz343) rfl) rfl rfl) (@ep348 ep187 164175520455872116113 1672546302946785099776 36178558116511761068105 ep349 ep350 32914958317031207980767 209068287868348137472000 ep191 ep187 (ep352 (@ep346 29372954866999 146032512096000 0 1 qz343) rfl) (ep354 (@ep305 29372954866999 146032512096000 0 1 qz343) rfl) rfl rfl)

noncomputable def ep356 := @ep194 ep186 ep187 (@ep195 255267086270464 (BSN.head_sum_c_eq qz11 8) (ep196 (BSN.head_sum_c_succ qz11 7 8 rfl rfl) (ep284 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep355 rfl rfl rfl

noncomputable def ep357 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz11 1 8) Bool.false ep53 836273151473392549888000 ep54 ep55 Bool.true 23554863487515751091233 209068287868348137472000 ep186 ep187 (@ep188 ep55 Bool.true 23554863487515751091233 209068287868348137472000 ep186 ep187 (BSN.zetaApproximant_eq_folded' qz11 1 8 rfl) (ep356 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep358 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 8)) 15 65536 835127

noncomputable def ep359 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) Bool.false 30 131072 835127

noncomputable def ep360 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) qz266 Bool.false 514711 32768 27

noncomputable def ep361 := nat_lit 276581650772887381598090427078300865388136105625161486114426382173775681

noncomputable def ep362 := nat_lit 827748775430651280799637520961994207085645655769002084326814309727250241

noncomputable def ep363 := BSN.cos_dyadic_bound_f 421595657 268435456 3 2 131072 59493 ep361 ep256 ep181 ep362 ep258 ep181 30 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 421595657) qz313 0 2 ep361 ep256 ep181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 421595657) qz314 0 2 ep362 ep258 ep181 rfl rfl rfl rfl) rfl rfl

noncomputable def ep364 := @ep360 32768 Bool.false 30 131072 1 29717 (@ep59 514711 32768 27 32768 ep178 rfl) (Enclosure.sfrac_false_div 514711 32768) (BSN.sin_reduce1 qz266 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7416789244073090220032) qz300) 226375608064910080 72057594037927936 Bool.false 30 131072 2 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q1 514711 32768 226375608064910080 72057594037927936 2 7416789244073090220032 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 30 131072 7416789244073090220032 4722366482869645213696 421595657 268435456 59493 59434 (ep363 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep365 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz11 1 8) Bool.false ep53 836273151473392549888000 ep54 ep55 Bool.true 23554863487515751091233 209068287868348137472000 ep186 ep187 (@ep188 ep55 Bool.true 23554863487515751091233 209068287868348137472000 ep186 ep187 (BSN.zetaApproximant_eq_folded' qz11 1 8 rfl) (ep356 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow07.d8 : Enclosure.Real.IsNear (hardyZApproximantEM 1 8 qz35) Bool.true ep38 ep39 ep40 ep41 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 8 qz35) ep42 Bool.true ep38 ep39 ep40 ep41 (@Eq.refl Real ep42) (@ep43 Bool.true ep38 ep39 ep40 ep41 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) (zetaApproximant qz11 1 8)) (@ep45 ep39 ep46 ep47 70664590462547253273699 ep48 ep49 ep50 ep51 ep38 ep39 ep40 ep41 (@ep52 973766656 ep53 836273151473392549888000 ep54 ep55 ep44 ep39 ep46 ep47 (@ep56 973766656 131071 131072 835127 973766656 (ep185 rfl rfl) rfl) ep357 rfl) (@ep358 973766656 23554863487515751091233 209068287868348137472000 ep186 ep187 70664590462547253273699 ep48 ep49 ep50 (@ep359 973766656 15 65536 835127 973766656 (ep364 rfl rfl) rfl) ep365 rfl) rfl rfl))

noncomputable abbrev qz442 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 42364 1000)))

noncomputable abbrev qz428 := qz442

noncomputable abbrev qz344 := qz428

noncomputable abbrev qz128 := (BSN.headSumC qz344 9)

noncomputable abbrev qz129 := (BSN.headSumC qz344 8)

noncomputable abbrev qz429 := (@Neg.neg Complex Complex.instNeg qz442)

noncomputable abbrev qz345 := qz429

noncomputable abbrev qz130 := (@HPow.hPow Complex Complex Complex qz301 qz304 qz345)

noncomputable def ep366 := @Enclosure.Complex.IsNear.of_eq qz128 (@HAdd.hAdd Complex Complex Complex qz8 qz129 qz130) Bool.false 2477989359 2147483648 637235278223 127633543135232 Bool.true 4195027995 17179869184 2546356714553 510534172540928

noncomputable def ep367 := @Enclosure.Complex.IsNear.addLitP qz129 qz130 Bool.false 13800279987 17179869184 2280100909791 510534172540928 Bool.true 853626633 4294967296 1140439376133 255267086270464 Bool.false

noncomputable abbrev qz131 := (BSN.headSumC qz344 7)

noncomputable abbrev qz132 := (@HPow.hPow Complex Complex Complex qz301 (@Nat.cast Complex Complex.instNatCast 7) qz345)

noncomputable def ep368 := @Enclosure.Complex.IsNear.of_eq qz129 (@HAdd.hAdd Complex Complex Complex qz8 qz131 qz132) Bool.false 13800279987 17179869184 2280100909791 510534172540928 Bool.true 853626633 4294967296 1140439376133 255267086270464

noncomputable def ep369 := @Enclosure.Complex.IsNear.addLitP qz131 qz132 Bool.false 4534532473 8589934592 996994145059 255267086270464 Bool.false 1032937661 17179869184 1994936351569 510534172540928 Bool.false

noncomputable abbrev qz133 := (BSN.headSumC qz344 6)

noncomputable abbrev qz134 := (@HPow.hPow Complex Complex Complex qz301 (@Nat.cast Complex Complex.instNatCast 6) qz345)

noncomputable def ep370 := @Enclosure.Complex.IsNear.of_eq qz131 (@HAdd.hAdd Complex Complex Complex qz8 qz133 qz134) Bool.false 4534532473 8589934592 996994145059 255267086270464 Bool.false 1032937661 17179869184 1994936351569 510534172540928

noncomputable def ep371 := @Enclosure.Complex.IsNear.addLitP qz133 qz134 Bool.false 367430117 2147483648 52537672299 15954192891904 Bool.false 4441578171 17179869184 1685175793919 510534172540928 Bool.false

noncomputable abbrev qz135 := (BSN.headSumC qz344 5)

noncomputable abbrev qz136 := (@HPow.hPow Complex Complex Complex qz301 (@Nat.cast Complex Complex.instNatCast 5) qz345)

noncomputable def ep372 := @Enclosure.Complex.IsNear.of_eq qz133 (@HAdd.hAdd Complex Complex Complex qz8 qz135 qz136) Bool.false 367430117 2147483648 52537672299 15954192891904 Bool.false 4441578171 17179869184 1685175793919 510534172540928

noncomputable def ep373 := @Enclosure.Complex.IsNear.addLitP qz135 qz136 Bool.true 817925191 8589934592 671857998213 255267086270464 Bool.true 1730557461 17179869184 1346876726263 510534172540928 Bool.false

noncomputable abbrev qz137 := (BSN.headSumC qz344 4)

noncomputable abbrev qz138 := (@HPow.hPow Complex Complex Complex qz301 (@Nat.cast Complex Complex.instNatCast 4) qz345)

noncomputable def ep374 := @Enclosure.Complex.IsNear.of_eq qz135 (@HAdd.hAdd Complex Complex Complex qz8 qz137 qz138) Bool.true 817925191 8589934592 671857998213 255267086270464 Bool.true 1730557461 17179869184 1346876726263 510534172540928

noncomputable def ep375 := @Enclosure.Complex.IsNear.addLitP qz137 qz138 Bool.false 3280650853 17179869184 966760400121 510534172540928 Bool.false 5313013269 17179869184 968956605289 510534172540928 Bool.true

noncomputable abbrev qz139 := (BSN.headSumC qz344 3)

noncomputable abbrev qz140 := (@HPow.hPow Complex Complex Complex qz301 qz306 qz345)

noncomputable def ep376 := @Enclosure.Complex.IsNear.of_eq qz137 (@HAdd.hAdd Complex Complex Complex qz8 qz139 qz140) Bool.false 3280650853 17179869184 966760400121 510534172540928 Bool.false 5313013269 17179869184 968956605289 510534172540928

noncomputable def ep377 := @Enclosure.Complex.IsNear.addLitP qz139 qz140 Bool.false 90332801 134217728 132700690789 127633543135232 Bool.false 5385611997 8589934592 267053914231 255267086270464 Bool.true

noncomputable abbrev qz141 := (BSN.headSumC qz344 2)

noncomputable abbrev qz142 := (@HPow.hPow Complex Complex Complex qz301 qz307 qz345)

noncomputable def ep378 := @Enclosure.Complex.IsNear.of_eq qz139 (@HAdd.hAdd Complex Complex Complex qz8 qz141 qz142) Bool.false 90332801 134217728 132700690789 127633543135232 Bool.false 5385611997 8589934592 267053914231 255267086270464

noncomputable def ep379 := @Enclosure.Complex.IsNear.addLitP qz141 qz142 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz143 := qz344

noncomputable def ep380 := @Enclosure.Complex.IsNear.of_eq qz141 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz42) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz143)

noncomputable abbrev qz443 := (Enclosure.sfrac Bool.false 42364 1000)

noncomputable abbrev qz430 := qz443

noncomputable abbrev qz346 := qz430

noncomputable abbrev qz144 := (@HMul.hMul Real Real Real qz254 qz346 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz145 := qz346

noncomputable abbrev qz347 := (@Eq.refl Real qz430)

noncomputable abbrev qz146 := qz347

noncomputable def ep381 := @Enclosure.Complex.IsNear.of_eq qz142 (Complex.mk (@HMul.hMul Real Real Real qz0 qz84 (Real.cos qz144)) (@HMul.hMul Real Real Real qz0 qz84 (@Neg.neg Real Real.instNeg (Real.sin qz144)))) Bool.true 43884927 134217728 132700690789 127633543135232 Bool.false 5385611997 8589934592 267053914231 255267086270464 (BSN.cpow_neg_s_mk qz145 42364 1000 2 qz146 rfl)

noncomputable def ep382 := nat_lit 64009648012689812602488500043232866481433181890992843176289422854585121

noncomputable def ep383 := nat_lit 53755577844178251781043289469037330837128222620949898533706052926241

noncomputable def ep384 := nat_lit 191921432882381081303903413550760524782625289227736629731800856457902881

noncomputable def ep385 := BSN.cos_dyadic_bound_f 292619283 268435456 3 2 131072 59493 ep382 ep256 ep383 ep384 ep258 ep383 60608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 292619283) qz313 0 2 ep382 ep256 ep383 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 292619283) qz314 0 2 ep384 ep258 ep383 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz348 := (Enclosure.Real.IsNear.const Bool.false 42364 1000)

noncomputable abbrev qz147 := qz348

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1924427) qz99)

noncomputable def ep386 := @Enclosure.Real.IsNear.cos_image qz144 qz349 Bool.false 1924427 65536 187 131072 Bool.true 60608 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 240553383 8192000 10591 7429250 1924427 65536 187 131072 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz89 42364 1000 0 1 45426 65536 1 29717 240553383 8192000 10591 7429250 qz147 qz310 rfl) rfl) (Enclosure.sfrac_false_div 1924427 65536) (BSN.cos_reduce2 qz349 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10295625740700042133504) qz322) 226375608064910080 72057594037927936 Bool.false 60608 131072 4 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q2 1924427 65536 226375608064910080 72057594037927936 4 10295625740700042133504 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 60608 131072 10295625740700042133504 9444732965739290427392 292619283 268435456 59493 59434 (ep385 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep387 := nat_lit 115174361960566320083054465446243929801910024825690357798493996295912225

noncomputable def ep388 := nat_lit 301560105627830740190830482271498517612218524087802732493667799546460961

noncomputable def ep389 := BSN.sin_dyadic_bound_f 292619283 268435456 3 2 131072 59493 ep387 ep180 ep383 ep388 ep183 ep383 116217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 292619283) qz298 0 2 ep387 ep180 ep383 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 292619283) qz299 0 2 ep388 ep183 ep383 rfl rfl rfl rfl) rfl rfl

noncomputable def ep390 := @Enclosure.Real.IsNear.sin_image qz144 qz349 Bool.false 1924427 65536 187 131072 Bool.true 116217 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 240553383 8192000 10591 7429250 1924427 65536 187 131072 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz89 42364 1000 0 1 45426 65536 1 29717 240553383 8192000 10591 7429250 qz147 qz310 rfl) rfl) (Enclosure.sfrac_false_div 1924427 65536) (BSN.sin_reduce2 qz349 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10295625740700042133504) qz322) 226375608064910080 72057594037927936 Bool.false 116217 131072 4 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q2 1924427 65536 226375608064910080 72057594037927936 4 10295625740700042133504 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 116217 131072 10295625740700042133504 9444732965739290427392 292619283 268435456 59493 59434 (ep389 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep391 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz84 (Real.cos qz144)) (@HMul.hMul Real Real Real qz0 qz84 (@Neg.neg Real Real.instNeg (Real.sin qz144))) Bool.true 43884927 134217728 132700690789 127633543135232 Bool.false 5385611997 8589934592 267053914231 255267086270464 (@Enclosure.Real.IsNear.mulLit_ft qz84 (Real.cos qz144) 46341 65536 1 65536 947 2048 5688151 3895066624 43884927 134217728 132700690789 127633543135232 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz144) Bool.true 60608 131072 5688151 3895066624 947 2048 5688151 3895066624 (ep386 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz84 (@Neg.neg Real Real.instNeg (Real.sin qz144)) 46341 65536 1 65536 116217 131072 5688151 3895066624 5385611997 8589934592 267053914231 255267086270464 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz144) Bool.true 116217 131072 5688151 3895066624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz144) Bool.true 116217 131072 5688151 3895066624 116217 131072 5688151 3895066624 (ep390 rfl rfl) rfl)) rfl)

noncomputable def ep392 := @ep379 43884927 134217728 132700690789 127633543135232 Bool.false 5385611997 8589934592 267053914231 255267086270464 Bool.false 90332801 90332801 134217728 132700690789 127633543135232 Bool.false 5385611997 5385611997 8589934592 267053914231 255267086270464 (ep380 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz42 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz43)) (ep381 ep391) rfl rfl

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz254 qz346 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep393 := @Enclosure.Complex.IsNear.of_eq qz140 (Complex.mk (@HMul.hMul Real Real Real qz0 qz91 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz91 (@Neg.neg Real Real.instNeg (Real.sin qz148)))) Bool.true 8281947675 17179869184 435957636965 510534172540928 Bool.true 5458210725 17179869184 434848776827 510534172540928 (BSN.cpow_neg_s_mk qz145 42364 1000 3 qz146 rfl)

noncomputable def ep394 := nat_lit 4949319829332501983886956340039936

noncomputable def ep395 := BSN.sin_dyadic_bound_f 265238388 268435456 2 1 131072 59493 ep394 ep213 ep394 ep394 ep214 ep394 109441 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 265238388) qz298 0 1 ep394 ep213 ep394 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 265238388) qz299 0 1 ep394 ep214 ep394 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz350 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3050123) qz99)

noncomputable def ep396 := @Enclosure.Real.IsNear.cos_image qz148 qz350 Bool.false 3050123 65536 47 32768 Bool.true 109441 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 381265409 8192000 10591 7429250 3050123 65536 47 32768 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz95 42364 1000 0 1 71998 65536 1 29717 381265409 8192000 10591 7429250 qz147 qz318 rfl) rfl) (Enclosure.sfrac_false_div 3050123 65536) (BSN.cos_reduce1 qz350 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9332246145377276788736) qz322) 226375608064910080 72057594037927936 Bool.false 109441 131072 7 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q1 3050123 65536 226375608064910080 72057594037927936 7 9332246145377276788736 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 109441 131072 9332246145377276788736 9444732965739290427392 265238388 268435456 59493 59434 (ep395 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep397 := nat_lit 43197703273674853089196644120014649999387977348436236765317577981362176

noncomputable def ep398 := nat_lit 24495766773023906565177660585722605566963981587523214576790074884096

noncomputable def ep399 := nat_lit 129544118287478511454459577038872504787030004082133663866799153794318336

noncomputable def ep400 := BSN.cos_dyadic_bound_f 265238388 268435456 3 2 131072 59493 ep397 ep256 ep398 ep399 ep258 ep398 72127 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 265238388) qz313 0 2 ep397 ep256 ep398 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 265238388) qz314 0 2 ep399 ep258 ep398 rfl rfl rfl rfl) rfl rfl

noncomputable def ep401 := @Enclosure.Real.IsNear.sin_image qz148 qz350 Bool.false 3050123 65536 47 32768 Bool.false 72127 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 381265409 8192000 10591 7429250 3050123 65536 47 32768 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz95 42364 1000 0 1 71998 65536 1 29717 381265409 8192000 10591 7429250 qz147 qz318 rfl) rfl) (Enclosure.sfrac_false_div 3050123 65536) (BSN.sin_reduce1 qz350 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9332246145377276788736) qz322) 226375608064910080 72057594037927936 Bool.false 72127 131072 7 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q1 3050123 65536 226375608064910080 72057594037927936 7 9332246145377276788736 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 72127 131072 9332246145377276788736 9444732965739290427392 265238388 268435456 59493 59434 (ep400 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep402 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz91 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz91 (@Neg.neg Real Real.instNeg (Real.sin qz148))) Bool.true 8281947675 17179869184 435957636965 510534172540928 Bool.true 5458210725 17179869184 434848776827 510534172540928 (@Enclosure.Real.IsNear.mulLit_ft qz91 (Real.cos qz148) 75675 131072 1 131072 109441 131072 1429467 973766656 8281947675 17179869184 435957636965 510534172540928 qz319 (@Enclosure.Real.IsNear.recentre' (Real.cos qz148) Bool.true 109441 131072 1429467 973766656 109441 131072 1429467 973766656 (ep396 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz91 (@Neg.neg Real Real.instNeg (Real.sin qz148)) 75675 131072 1 131072 72127 131072 1429467 973766656 5458210725 17179869184 434848776827 510534172540928 qz319 (@Enclosure.Real.IsNear.neg (Real.sin qz148) Bool.false 72127 131072 1429467 973766656 (@Enclosure.Real.IsNear.recentre' (Real.sin qz148) Bool.false 72127 131072 1429467 973766656 72127 131072 1429467 973766656 (ep401 rfl rfl) rfl)) rfl)

noncomputable def ep403 := @ep377 8281947675 17179869184 435957636965 510534172540928 Bool.true 5458210725 17179869184 434848776827 510534172540928 Bool.false 440321503850921984 3280650853 17179869184 966760400121 510534172540928 Bool.false 45638436467138101248 5313013269 17179869184 968956605289 510534172540928 (ep378 (BSN.head_sum_c_succ qz143 2 3 rfl rfl) (ep392 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep393 ep402) rfl rfl

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz254 qz346 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep404 := @Enclosure.Complex.IsNear.of_eq qz138 (Complex.mk (@HMul.hMul Real Real Real qz0 qz96 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz96 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.true 4916501235 17179869184 376955596305 510534172540928 Bool.true 3521785365 8589934592 188960060487 255267086270464 (BSN.cpow_neg_s_mk qz145 42364 1000 4 qz146 rfl)

noncomputable def ep405 := nat_lit 716032773192977332986297050001936

noncomputable def ep406 := BSN.sin_dyadic_bound_f 163581138 268435456 2 1 131072 59493 ep405 ep213 ep405 ep405 ep214 ep405 75021 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 163581138) qz298 0 1 ep405 ep213 ep405 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 163581138) qz299 0 1 ep405 ep214 ep405 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1924427) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep407 := @Enclosure.Real.IsNear.cos_image qz149 qz351 Bool.false 1924427 32768 47 32768 Bool.true 75021 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 240553383 4096000 10591 7429250 1924427 32768 47 32768 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz100 42364 1000 0 1 90852 65536 1 29717 240553383 4096000 10591 7429250 qz147 qz321 rfl) rfl) (Enclosure.sfrac_false_div 1924427 32768) (BSN.cos_reduce1 qz351 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2877749815629068632064) qz300) 226375608064910080 72057594037927936 Bool.false 75021 131072 9 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q1 1924427 32768 226375608064910080 72057594037927936 9 2877749815629068632064 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 75021 131072 2877749815629068632064 4722366482869645213696 163581138 268435456 59493 59434 (ep406 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep408 := BSN.cos_dyadic_bound_f 163581138 268435456 2 1 131072 59493 ep405 ep217 ep405 ep405 ep218 ep405 107478 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 163581138) qz313 0 1 ep405 ep217 ep405 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 163581138) qz314 0 1 ep405 ep218 ep405 rfl rfl rfl rfl) rfl rfl

noncomputable def ep409 := @Enclosure.Real.IsNear.sin_image qz149 qz351 Bool.false 1924427 32768 47 32768 Bool.false 107478 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 240553383 4096000 10591 7429250 1924427 32768 47 32768 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz100 42364 1000 0 1 90852 65536 1 29717 240553383 4096000 10591 7429250 qz147 qz321 rfl) rfl) (Enclosure.sfrac_false_div 1924427 32768) (BSN.sin_reduce1 qz351 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2877749815629068632064) qz300) 226375608064910080 72057594037927936 Bool.false 107478 131072 9 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q1 1924427 32768 226375608064910080 72057594037927936 9 2877749815629068632064 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 107478 131072 2877749815629068632064 4722366482869645213696 163581138 268435456 59493 59434 (ep408 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep410 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz96 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz96 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.true 4916501235 17179869184 376955596305 510534172540928 Bool.true 3521785365 8589934592 188960060487 255267086270464 (@Enclosure.Real.IsNear.mulLit_ft qz96 (Real.cos qz149) 65535 131072 1 131072 75021 131072 1429467 973766656 4916501235 17179869184 376955596305 510534172540928 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.true 75021 131072 1429467 973766656 75021 131072 1429467 973766656 (ep407 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz96 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 65535 131072 1 131072 53739 65536 1429467 973766656 3521785365 8589934592 188960060487 255267086270464 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.false 53739 65536 1429467 973766656 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.false 107478 131072 1429467 973766656 53739 65536 1429467 973766656 (ep409 rfl rfl) rfl)) rfl)

noncomputable def ep411 := @ep375 4916501235 17179869184 376955596305 510534172540928 Bool.true 3521785365 8589934592 188960060487 255267086270464 Bool.true 28103695567356428288 817925191 8589934592 671857998213 255267086270464 Bool.true 14865375397687590912 1730557461 17179869184 1346876726263 510534172540928 (ep376 (BSN.head_sum_c_succ qz143 3 4 rfl rfl) (ep403 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep404 ep410) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz254 qz346 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep412 := @Enclosure.Complex.IsNear.of_eq qz136 (Complex.mk (@HMul.hMul Real Real Real qz0 qz101 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz101 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.false 2287645659 8589934592 168744758571 255267086270464 Bool.false 385758477 1073741824 42287383457 63816771567616 (BSN.cpow_neg_s_mk qz145 42364 1000 5 qz146 rfl)

noncomputable def ep413 := nat_lit 859756902656174527321332867076096

noncomputable def ep414 := BSN.sin_dyadic_bound_f 171235544 268435456 2 1 131072 59493 ep413 ep213 ep413 ep413 ep214 ep413 78054 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 171235544) qz298 0 1 ep413 ep213 ep413 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 171235544) qz299 0 1 ep413 ep214 ep413 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4468385) qz99)

noncomputable def ep415 := @Enclosure.Real.IsNear.cos_image qz150 qz352 Bool.false 4468385 65536 47 32768 Bool.false 78054 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 279274079 4096000 10591 7429250 4468385 65536 47 32768 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz104 42364 1000 0 1 105476 65536 1 29717 279274079 4096000 10591 7429250 qz147 qz325 rfl) rfl) (Enclosure.sfrac_false_div 4468385 65536) (BSN.cos_reduce3 qz352 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6024815114229519482880) qz322) 226375608064910080 72057594037927936 Bool.false 78054 131072 10 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q3 4468385 65536 226375608064910080 72057594037927936 10 6024815114229519482880 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 78054 131072 6024815114229519482880 9444732965739290427392 171235544 268435456 59493 59434 (ep414 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep416 := BSN.cos_dyadic_bound_f 171235544 268435456 2 1 131072 59493 ep413 ep217 ep413 ep413 ep218 ep413 105296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 171235544) qz313 0 1 ep413 ep217 ep413 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 171235544) qz314 0 1 ep413 ep218 ep413 rfl rfl rfl rfl) rfl rfl

noncomputable def ep417 := @Enclosure.Real.IsNear.sin_image qz150 qz352 Bool.false 4468385 65536 47 32768 Bool.true 105296 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 279274079 4096000 10591 7429250 4468385 65536 47 32768 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz104 42364 1000 0 1 105476 65536 1 29717 279274079 4096000 10591 7429250 qz147 qz325 rfl) rfl) (Enclosure.sfrac_false_div 4468385 65536) (BSN.sin_reduce3 qz352 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6024815114229519482880) qz322) 226375608064910080 72057594037927936 Bool.false 105296 131072 10 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q3 4468385 65536 226375608064910080 72057594037927936 10 6024815114229519482880 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 105296 131072 6024815114229519482880 9444732965739290427392 171235544 268435456 59493 59434 (ep416 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep418 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz101 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz101 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.false 2287645659 8589934592 168744758571 255267086270464 Bool.false 385758477 1073741824 42287383457 63816771567616 (@Enclosure.Real.IsNear.mulLit_ff qz101 (Real.cos qz150) 58617 131072 1 131072 39027 65536 1429467 973766656 2287645659 8589934592 168744758571 255267086270464 qz326 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.false 78054 131072 1429467 973766656 39027 65536 1429467 973766656 (ep415 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz101 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 58617 131072 1 131072 6581 8192 1429467 973766656 385758477 1073741824 42287383457 63816771567616 qz326 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.true 6581 8192 1429467 973766656 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.true 105296 131072 1429467 973766656 6581 8192 1429467 973766656 (ep417 rfl rfl) rfl)) rfl)

noncomputable def ep419 := @ep373 2287645659 8589934592 168744758571 255267086270464 Bool.false 385758477 1073741824 42287383457 63816771567616 Bool.false 12624802688643629056 367430117 2147483648 52537672299 15954192891904 Bool.false 4769108246768123904 4441578171 17179869184 1685175793919 510534172540928 (ep374 (BSN.head_sum_c_succ qz143 4 5 rfl rfl) (ep411 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep412 ep418) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz254 qz346 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep420 := @Enclosure.Complex.IsNear.of_eq qz134 (Complex.mk (@HMul.hMul Real Real Real qz0 qz105 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz105 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.false 3064812005 8589934592 156391388275 255267086270464 Bool.true 1704320255 8589934592 154880278825 255267086270464 (BSN.cpow_neg_s_mk qz145 42364 1000 6 qz146 rfl)

noncomputable def ep421 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz108 42364 1000 0 1 4034664351997175 2251799813685248 500000000029717 14858500000000000000 1709245206080083217 22517998136852480 5295500000314732747 3714625000000000000000 qz147 (BSN.isNear_log_sfrac 6 1 4034664351997175 2251799813685248 500000000029717 14858500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz328) Bool.false 4230652207559789772800 2361183241434822606848 1000000000059434 29717000000000000000 4034664351997175 2251799813685248 500000000029717 14858500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 26572 65536 24973259072661432 36028797018963968 29717 1000000000000000 rfl rfl rfl rfl (ep265 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep422 := nat_lit 344452563902166226366943118506641

noncomputable def ep423 := BSN.cos_dyadic_bound_f 136233011 268435456 2 1 131072 59493 ep422 ep217 ep422 ep422 ep218 ep422 114551 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 136233011) qz313 0 1 ep422 ep217 ep422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 136233011) qz314 0 1 ep422 ep218 ep422 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz353 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2487279) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep424 := @Enclosure.Real.IsNear.cos_image qz151 qz353 Bool.false 2487279 32768 47 32768 Bool.false 114551 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 1709245206080083217 22517998136852480 5295500000314732747 3714625000000000000000 2487279 32768 47 32768 (ep421 rfl) rfl) (Enclosure.sfrac_false_div 2487279 32768) (BSN.cos_reduce0 qz353 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2396636478719989383168) qz300) 226375608064910080 72057594037927936 Bool.false 114551 131072 12 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q0 2487279 32768 226375608064910080 72057594037927936 12 2396636478719989383168 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 114551 131072 2396636478719989383168 4722366482869645213696 136233011 268435456 59493 59434 (ep423 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep425 := BSN.sin_dyadic_bound_f 136233011 268435456 2 1 131072 59493 ep422 ep213 ep422 ep422 ep214 ep422 63701 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 136233011) qz298 0 1 ep422 ep213 ep422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 136233011) qz299 0 1 ep422 ep214 ep422 rfl rfl rfl rfl) rfl rfl

noncomputable def ep426 := @Enclosure.Real.IsNear.sin_image qz151 qz353 Bool.false 2487279 32768 47 32768 Bool.false 63701 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 1709245206080083217 22517998136852480 5295500000314732747 3714625000000000000000 2487279 32768 47 32768 (ep421 rfl) rfl) (Enclosure.sfrac_false_div 2487279 32768) (BSN.sin_reduce0 qz353 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2396636478719989383168) qz300) 226375608064910080 72057594037927936 Bool.false 63701 131072 12 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q0 2487279 32768 226375608064910080 72057594037927936 12 2396636478719989383168 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 63701 131072 2396636478719989383168 4722366482869645213696 136233011 268435456 59493 59434 (ep425 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep427 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz105 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz105 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.false 3064812005 8589934592 156391388275 255267086270464 Bool.true 1704320255 8589934592 154880278825 255267086270464 (@Enclosure.Real.IsNear.mulLit_ff qz105 (Real.cos qz151) 26755 65536 1 65536 114551 131072 1429467 973766656 3064812005 8589934592 156391388275 255267086270464 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.false 114551 131072 1429467 973766656 114551 131072 1429467 973766656 (ep424 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz105 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 26755 65536 1 65536 63701 131072 1429467 973766656 1704320255 8589934592 154880278825 255267086270464 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.false 63701 131072 1429467 973766656 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.false 63701 131072 1429467 973766656 63701 131072 1429467 973766656 (ep426 rfl rfl) rfl)) rfl)

noncomputable def ep428 := @ep371 3064812005 8589934592 156391388275 255267086270464 Bool.true 1704320255 8589934592 154880278825 255267086270464 Bool.false 9737834337092501504 4534532473 8589934592 996994145059 255267086270464 Bool.false 8872866945603469312 1032937661 17179869184 1994936351569 510534172540928 (ep372 (BSN.head_sum_c_succ qz143 5 6 rfl rfl) (ep419 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep420 ep427) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz254 qz346 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep429 := @Enclosure.Complex.IsNear.of_eq qz132 (Complex.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.false 4731215041 17179869184 286112619673 510534172540928 Bool.true 4447444193 17179869184 285942400697 510534172540928 (BSN.cpow_neg_s_mk qz145 42364 1000 7 qz146 rfl)

noncomputable def ep430 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz112 42364 1000 0 1 4381766428990711 2251799813685248 500000000029717 14858500000000000000 46407288249440620201 562949953421312000 5295500000314732747 3714625000000000000000 qz147 (BSN.isNear_log_sfrac 7 1 4381766428990711 2251799813685248 500000000029717 14858500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz332) Bool.false 4594615115045363777536 2361183241434822606848 1000000000059434 29717000000000000000 4381766428990711 2251799813685248 500000000029717 14858500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 36674 65536 24973259072661432 36028797018963968 29717 1000000000000000 rfl rfl rfl rfl (ep276 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep431 := nat_lit 1682560852138520071806477594967056

noncomputable def ep432 := BSN.cos_dyadic_bound_f 202531554 268435456 2 1 131072 59493 ep431 ep217 ep431 ep431 ep218 ep431 95501 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 202531554) qz313 0 1 ep431 ep217 ep431 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 202531554) qz314 0 1 ep431 ep218 ep431 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz354 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5402519) qz99)

noncomputable def ep433 := @Enclosure.Real.IsNear.cos_image qz152 qz354 Bool.false 5402519 65536 47 32768 Bool.false 95501 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 46407288249440620201 562949953421312000 5295500000314732747 3714625000000000000000 5402519 65536 47 32768 (ep430 rfl) rfl) (Enclosure.sfrac_false_div 5402519 65536) (BSN.cos_reduce0 qz354 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7125945561003545591808) qz322) 226375608064910080 72057594037927936 Bool.false 95501 131072 13 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q0 5402519 65536 226375608064910080 72057594037927936 13 7125945561003545591808 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 95501 131072 7125945561003545591808 9444732965739290427392 202531554 268435456 59493 59434 (ep432 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep434 := BSN.sin_dyadic_bound_f 202531554 268435456 2 1 131072 59493 ep431 ep213 ep431 ep431 ep214 ep431 89773 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 202531554) qz298 0 1 ep431 ep213 ep431 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 202531554) qz299 0 1 ep431 ep214 ep431 rfl rfl rfl rfl) rfl rfl

noncomputable def ep435 := @Enclosure.Real.IsNear.sin_image qz152 qz354 Bool.false 5402519 65536 47 32768 Bool.false 89773 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 46407288249440620201 562949953421312000 5295500000314732747 3714625000000000000000 5402519 65536 47 32768 (ep430 rfl) rfl) (Enclosure.sfrac_false_div 5402519 65536) (BSN.sin_reduce0 qz354 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7125945561003545591808) qz322) 226375608064910080 72057594037927936 Bool.false 89773 131072 13 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q0 5402519 65536 226375608064910080 72057594037927936 13 7125945561003545591808 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 89773 131072 7125945561003545591808 9444732965739290427392 202531554 268435456 59493 59434 (ep434 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep436 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.false 4731215041 17179869184 286112619673 510534172540928 Bool.true 4447444193 17179869184 285942400697 510534172540928 (@Enclosure.Real.IsNear.mulLit_ff qz109 (Real.cos qz152) 49541 131072 1 131072 95501 131072 1429467 973766656 4731215041 17179869184 286112619673 510534172540928 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.false 95501 131072 1429467 973766656 95501 131072 1429467 973766656 (ep433 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz109 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 49541 131072 1 131072 89773 131072 1429467 973766656 4447444193 17179869184 285942400697 510534172540928 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.false 89773 131072 1429467 973766656 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.false 89773 131072 1429467 973766656 89773 131072 1429467 973766656 (ep435 rfl rfl) rfl)) rfl)

noncomputable def ep437 := @ep369 4731215041 17179869184 286112619673 510534172540928 Bool.true 4447444193 17179869184 285942400697 510534172540928 Bool.false 118543502439616610304 13800279987 17179869184 2280100909791 510534172540928 Bool.true 58660775547673509888 853626633 4294967296 1140439376133 255267086270464 (ep370 (BSN.head_sum_c_succ qz143 6 7 rfl rfl) (ep428 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep429 ep436) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz254 qz346 qz338)

noncomputable def ep438 := @Enclosure.Complex.IsNear.of_eq qz130 (Complex.mk (@HMul.hMul Real Real Real qz0 qz115 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz115 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.false 6023634885 17179869184 268840203101 510534172540928 Bool.true 780521463 17179869184 265477962287 510534172540928 (BSN.cpow_neg_s_mk qz145 42364 1000 8 qz146 rfl)

noncomputable def ep439 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz119 42364 1000 0 1 9364972152248037 4503599627370496 1000000000089151 29717000000000000000 99184420064458959867 1125899906842624000 10591000000944198241 7429250000000000000000 qz147 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000089151 29717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz339 Bool.false 4909942519757818822656 2361183241434822606848 1000000000089151 29717000000000000000 9364972152248037 4503599627370496 1000000000089151 29717000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 65536 24973259072661432 36028797018963968 29717 1000000000000000 rfl rfl rfl rfl (ep293 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep440 := nat_lit 1431891037783801182306186050625

noncomputable def ep441 := BSN.cos_dyadic_bound_f 34592145 268435456 2 1 131072 59493 ep440 ep217 ep440 ep440 ep218 ep440 129985 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 34592145) qz313 0 1 ep440 ep217 ep440 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 34592145) qz314 0 1 ep440 ep218 ep440 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5773293) qz99)

noncomputable def ep442 := @Enclosure.Real.IsNear.cos_image qz153 qz355 Bool.false 5773293 65536 47 32768 Bool.false 129985 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 99184420064458959867 1125899906842624000 10591000000944198241 7429250000000000000000 5773293 65536 47 32768 (ep439 rfl) rfl) (Enclosure.sfrac_false_div 5773293 65536) (BSN.cos_reduce0 qz355 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1217102904073142665216) qz322) 226375608064910080 72057594037927936 Bool.false 129985 131072 14 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q0 5773293 65536 226375608064910080 72057594037927936 14 1217102904073142665216 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 129985 131072 1217102904073142665216 9444732965739290427392 34592145 268435456 59493 59434 (ep441 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep443 := BSN.sin_dyadic_bound_f 34592145 268435456 1 0 131072 59493 0 1 1 0 1 1 16843 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 34592145) qz298 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 34592145) qz299 0 0 rfl) rfl rfl

noncomputable def ep444 := @Enclosure.Real.IsNear.sin_image qz153 qz355 Bool.false 5773293 65536 47 32768 Bool.false 16843 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 99184420064458959867 1125899906842624000 10591000000944198241 7429250000000000000000 5773293 65536 47 32768 (ep439 rfl) rfl) (Enclosure.sfrac_false_div 5773293 65536) (BSN.sin_reduce0 qz355 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1217102904073142665216) qz322) 226375608064910080 72057594037927936 Bool.false 16843 131072 14 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q0 5773293 65536 226375608064910080 72057594037927936 14 1217102904073142665216 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16843 131072 1217102904073142665216 9444732965739290427392 34592145 268435456 59493 59434 (ep443 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep445 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz115 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz115 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.false 6023634885 17179869184 268840203101 510534172540928 Bool.true 780521463 17179869184 265477962287 510534172540928 (@Enclosure.Real.IsNear.mulLit_ff qz115 (Real.cos qz153) 46341 131072 1 131072 129985 131072 1429467 973766656 6023634885 17179869184 268840203101 510534172540928 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.false 129985 131072 1429467 973766656 129985 131072 1429467 973766656 (ep442 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz115 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 46341 131072 1 131072 16843 131072 1429467 973766656 780521463 17179869184 265477962287 510534172540928 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.false 16843 131072 1429467 973766656 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.false 16843 131072 1429467 973766656 16843 131072 1429467 973766656 (ep444 rfl rfl) rfl)) rfl)

noncomputable def ep446 := @ep367 6023634885 17179869184 268840203101 510534172540928 Bool.true 780521463 17179869184 265477962287 510534172540928 Bool.false 340572264215712104448 2477989359 2147483648 637235278223 127633543135232 Bool.true 18017508044329451520 4195027995 17179869184 2546356714553 510534172540928 (ep368 (BSN.head_sum_c_succ qz143 7 8 rfl rfl) (ep437 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep438 ep445) rfl rfl

theorem EMRow07.d9 : Enclosure.Complex.IsNear qz128 Bool.false 2477989359 2147483648 637235278223 127633543135232 Bool.true 4195027995 17179869184 2546356714553 510534172540928 := ep366 (BSN.head_sum_c_succ qz143 8 9 rfl rfl) (ep446 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow07.d10 : @Eq Nat (Nat.pow 9 1) 9 := @Eq.refl Nat 9

noncomputable def ep447 := nat_lit 33108349066634544534330973

noncomputable def ep448 := nat_lit 28419519423273419302502400

noncomputable def ep449 := nat_lit 9775052991278105714528805058030367

noncomputable def ep450 := nat_lit 1505836807921799115442451241762816000

noncomputable abbrev qz431 := (@HAdd.hAdd Complex Complex Complex qz436 (@HAdd.hAdd Complex Complex Complex qz436 qz437 (@HMul.hMul Complex Complex Complex qz435 Complex.I (@HDiv.hDiv Complex Complex Complex qz438 (↑qz443) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz356 := qz431

noncomputable abbrev qz154 := (Complex.Stirling.logGammaStirling 1 qz356)

noncomputable abbrev qz432 := (@HAdd.hAdd Complex Complex Complex qz436 qz437 (@HMul.hMul Complex Complex Complex qz435 Complex.I (@HDiv.hDiv Complex Complex Complex qz438 (↑qz443) (2 : Complex))))

noncomputable abbrev qz357 := qz432

noncomputable abbrev qz155 := qz357

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz254 (@HDiv.hDiv Real Real Real qz257 qz346 (2 : Real)) (Real.log Real.pi))

noncomputable def ep451 := Complex.re (@HMul.hMul Complex Complex Complex qz4 (Complex.exp (@HMul.hMul Complex Complex Complex qz4 Complex.I ↑(@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156))) (zetaApproximant qz143 1 9))

noncomputable def ep452 := @Enclosure.Real.IsNear.of_eq ep451 (@HSub.hSub Real Real Real qz5 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) (Complex.re (zetaApproximant qz143 1 9))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) (Complex.im (zetaApproximant qz143 1 9))))

noncomputable def ep453 := nat_lit 198645753086845046889313183

noncomputable def ep454 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) (Complex.re (zetaApproximant qz143 1 9))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) (Complex.im (zetaApproximant qz143 1 9))) ep453

noncomputable def ep455 := nat_lit 170517116539640515815014400

noncomputable def ep456 := nat_lit 1934128936464703417866740505393649

noncomputable def ep457 := nat_lit 301167361584359823088490248352563200

noncomputable def ep458 := nat_lit 34103423307928103163002880

noncomputable def ep459 := nat_lit 17401384825764770865850421843687

noncomputable def ep460 := nat_lit 250972801320299852573741873627136000

noncomputable def ep461 := nat_lit 6774648259476505113683876021117259339710558833213440

noncomputable def ep462 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) (Complex.re (zetaApproximant qz143 1 9)) 131071 131072 1818839

noncomputable def ep463 := nat_lit 2060267560065720496087009

noncomputable def ep464 := nat_lit 386601040054969574621184000

noncomputable def ep465 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) Bool.false 131071 131072 1818839

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2470699) qz88)

noncomputable def ep466 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156) qz358 Bool.false 2470699 131072 59

noncomputable def ep467 := nat_lit 365162496000000000000000000

noncomputable def ep468 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156) Bool.false 31834723939600066673 1688849860263936000 324170269162819236000463 ep467

noncomputable def ep469 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156 14557077136799542909 337769972052787200 88120708912819236000463 ep467 794547411 32768000

noncomputable def ep470 := nat_lit 208632046810562996948172800

noncomputable def ep471 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 3728650674983200849 112589990684262400 49078388587190885546087 ep62 Bool.false 14557077136799542909 337769972052787200

noncomputable def ep472 := @Enclosure.Complex.IsNear.subLitP qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 3040938795276322649 112589990684262400 47030388586217118890087 ep62 Bool.false 15594321614523079309 337769972052787200 75832708912454073504463

noncomputable def ep473 := nat_lit 2099043723806136466912632413093888

noncomputable def ep474 := nat_lit 4097452948055874266851161149538304

noncomputable abbrev qz359 := (@HSub.hSub Complex Complex Complex qz414 qz431 qz420)

noncomputable abbrev qz360 := (Complex.log qz431)

noncomputable abbrev qz157 := (@HSub.hSub Complex Complex Complex qz260 (@HMul.hMul Complex Complex Complex qz259 qz359 qz360) qz356)

noncomputable abbrev qz158 := qz356

noncomputable def ep475 := @Enclosure.Complex.IsNear.of_eq qz154 (@HAdd.hAdd Complex Complex Complex qz8 (@HAdd.hAdd Complex Complex Complex qz8 qz157 qz13) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz16 qz158 (@HSub.hSub Int Int Int qz18 qz19 (@HMul.hMul Int Int Int qz20 qz21 (@Nat.cast Int instNatCastInt k)))))) Bool.true 3040938795276322649

noncomputable def ep476 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz8 qz157 qz13) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz16 qz158 (@HSub.hSub Int Int Int qz18 qz19 (@HMul.hMul Int Int Int qz20 qz21 (@Nat.cast Int instNatCastInt k))))) Bool.true 3040985320908015449 112589990684262400

noncomputable def ep477 := nat_lit 3265183168712361265149771776

noncomputable def ep478 := nat_lit 10465172084012897542088949760000

noncomputable def ep479 := @ep476 11481945435093064247 29717000000000000000000 Bool.false 25992726037384058603 562949953421312000 6170500002543864351 29717000000000000000000 Bool.false 443703 1073741824 3 1073741824 Bool.true 1566419491 402653184000 10591 402653184000 Bool.true ep477 3040938795276322649 112589990684262400 47030388586217118890087 ep62 Bool.false ep478

noncomputable def ep480 := @Enclosure.Complex.IsNear.addLitP qz157 qz13 Bool.true 3144447647094818649 112589990684262400 11028500000522751747 29717000000000000000000

noncomputable def ep481 := @ep480 Bool.false 25992726037384058603 562949953421312000 6170500002543864351 29717000000000000000000 Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 Bool.true 199294013991027700465664 3040985320908015449 112589990684262400 11481945435093064247 29717000000000000000000 Bool.false 25992726037384058603 25992726037384058603 562949953421312000

noncomputable abbrev qz159 := (@HMul.hMul Complex Complex Complex qz259 qz359 qz360)

noncomputable def ep482 := @Enclosure.Complex.IsNear.subLitP qz159 qz158 Bool.true 2891120168055228249 112589990684262400 11028500000522751747 29717000000000000000000 Bool.false 37917131950754289387

noncomputable def ep483 := @ep482 562949953421312000 6170500002543864351 29717000000000000000000 Bool.false 9000 4000 0 1 Bool.false 84728 4000 0 1 Bool.true 12577790588379274596000 3144447647094818649 112589990684262400 11028500000522751747 29717000000000000000000 Bool.false 103970904149536234412000 25992726037384058603 562949953421312000 6170500002543864351 29717000000000000000000

noncomputable abbrev qz160 := qz359

noncomputable abbrev qz161 := qz360

noncomputable def ep484 := @Enclosure.Complex.IsNear.mul qz160 qz161 Bool.true 2891120168055228249 112589990684262400 11028500000522751747 29717000000000000000000 Bool.false 37917131950754289387 562949953421312000 6170500002543864351

noncomputable abbrev qz162 := (Complex.re qz359)

noncomputable abbrev qz163 := (Complex.re qz360)

noncomputable abbrev qz164 := (Complex.im qz359)

noncomputable abbrev qz165 := (Complex.im qz360)

noncomputable def ep485 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz162 qz163) (@HMul.hMul Real Real Real qz0 qz164 qz165) 24107000684858049 4503599627370496 437500000208019 29717000000000000000 1746897592588339737 56294995342131200

noncomputable def ep486 := nat_lit 6510223855768425857690026484170752

noncomputable def ep487 := @Enclosure.Real.IsNear.mulLit_ff qz162 qz163 7000 4000 0 1 3443857240694007 1125899906842624 62500000029717 7429250000000000000

noncomputable def ep488 := @Enclosure.Complex.IsNear.re_isNear qz160 Bool.false 7000 4000 0 1 Bool.false 84728 4000 0 1

noncomputable abbrev qz361 := (Enclosure.sfrac Bool.false 84728 4000)

noncomputable abbrev qz166 := qz361

noncomputable def ep489 := @Enclosure.Complex.IsNear.of_eq qz160 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz166) Bool.false 7000 4000 0 1 Bool.false 84728 4000 0

noncomputable abbrev qz167 := (Complex.mk qz277 qz361)

noncomputable def ep490 := @Enclosure.Complex.IsNear.of_eq qz161 (Complex.log qz167) Bool.false 3443857240694007 1125899906842624 62500000029717 7429250000000000000 Bool.false 824708522608035 562949953421312 1000000000029717 59434000000000000000

noncomputable def ep491 := nat_lit 261326881887144183905238995727357943659094244072940270346332304910771839178605854720

noncomputable def ep492 := nat_lit 7095070473772550117181594399526083230623007732717838192220462290013951087790260224

noncomputable def ep493 := nat_lit 1054141211707796139799495513550978666147807612062904945621291440146554636206080

noncomputable def ep494 := BSN.log_dyadic_bound 3163833984 11355833984 5 4 ep491 131072 59434 ep492 ep493 75018 14519667968 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3163833984) (BSN.artanhQ 11355833984) 0 4 ep492 ep491 ep493 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz362 := (Real.log (Enclosure.sfrac Bool.false 7259833984 16000000))

noncomputable def ep495 := @Enclosure.Real.IsNear.mulLit_ff qz31 qz362 1 2 0 1 3443857240694007 562949953421312 62500000029717 3714625000000000000 3443857240694007 1125899906842624 62500000029717 7429250000000000000 qz32 (BSN.isNear_log_sfrac 7259833984 16000000 3443857240694007 562949953421312 62500000029717 3714625000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7259833984) qz279)) Bool.false 28889168400143672672256 4722366482869645213696 1000000000475472 59434000000000000000 3443857240694007 562949953421312 62500000029717 3714625000000000000 (BSN.log_rat_reduce_isNear 7259833984 16000000 8 14519667968 8192000000 75018 131072 24973259072661432 36028797018963968 59434 1000000000000000 rfl rfl rfl rfl (ep494 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep496 := BSN.arctan_dyadic_bound_f 9000 84728 1 0 131072 59434 0 1 1 0 1 1 13870 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 84728) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 84728) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz363 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 84728)))

noncomputable def ep497 := @Enclosure.Real.IsNear.subLit_ff_p qz33 qz363 884279719003555 562949953421312 1 2000000000000000 13870 131072 1 59434 108096195475280363520 824708522608035 562949953421312 1000000000029717 59434000000000000000 qz34 (ep496 rfl) rfl rfl

noncomputable abbrev qz364 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 84728) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep498 := @Enclosure.Complex.IsNear.re_isNear qz161 Bool.false 3443857240694007 1125899906842624 62500000029717 7429250000000000000 Bool.false 824708522608035 562949953421312 1000000000029717 59434000000000000000 (ep490 (@congrArg Complex Complex qz158 qz167 Complex.log (BSN.w_shift_mk qz145 Bool.false 42364 1000 2 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz167) Bool.false 3443857240694007 1125899906842624 62500000029717 7429250000000000000 Bool.false 824708522608035 562949953421312 1000000000029717 59434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz167)) (@HMul.hMul Real Real Real qz0 qz31 qz362) Bool.false 3443857240694007 1125899906842624 62500000029717 7429250000000000000 (Enclosure.clog_re_eq 9000 84728 4000 7259833984 16000000 rfl rfl rfl) (ep495 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz167)) qz364 Bool.false 824708522608035 562949953421312 1000000000029717 59434000000000000000 (Enclosure.clog_im_eq 9000 84728 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz364 (@HSub.hSub Real Real Real qz5 qz33 qz363) Bool.false 824708522608035 562949953421312 1000000000029717 59434000000000000000 (BSN.arctan_recip 84728 9000 rfl rfl) ep497))))

noncomputable def ep499 := @Enclosure.Real.IsNear.mulLit_ff qz164 qz165 84728 4000 0 1 824708522608035 562949953421312 1000000000029717 59434000000000000000

noncomputable def ep500 := @Enclosure.Complex.IsNear.im_isNear qz160 Bool.false 7000 4000 0 1 Bool.false 84728 4000 0 1

noncomputable def ep501 := @Enclosure.Complex.IsNear.im_isNear qz161 Bool.false 3443857240694007 1125899906842624 62500000029717 7429250000000000000 Bool.false 824708522608035 562949953421312 1000000000029717 59434000000000000000 (ep490 (@congrArg Complex Complex qz158 qz167 Complex.log (BSN.w_shift_mk qz145 Bool.false 42364 1000 2 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz167) Bool.false 3443857240694007 1125899906842624 62500000029717 7429250000000000000 Bool.false 824708522608035 562949953421312 1000000000029717 59434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz167)) (@HMul.hMul Real Real Real qz0 qz31 qz362) Bool.false 3443857240694007 1125899906842624 62500000029717 7429250000000000000 (Enclosure.clog_re_eq 9000 84728 4000 7259833984 16000000 rfl rfl rfl) (ep495 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz167)) qz364 Bool.false 824708522608035 562949953421312 1000000000029717 59434000000000000000 (Enclosure.clog_im_eq 9000 84728 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz364 (@HSub.hSub Real Real Real qz5 qz33 qz363) Bool.false 824708522608035 562949953421312 1000000000029717 59434000000000000000 (BSN.arctan_recip 84728 9000 rfl rfl) ep497))))

noncomputable abbrev qz365 := (Enclosure.Real.IsNear.const Bool.false 84728 4000)

noncomputable abbrev qz168 := (@ep489 1 (BSN.w_sub_half_mk qz346 Bool.false 42364 1000 2 qz347 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz361 Bool.false 7000 4000 0 1 Bool.false 84728 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz365))

noncomputable def ep502 := @ep485 10591000000314732747 29717000000000000000000 ep486 2891120168055228249 112589990684262400 11028500000522751747 29717000000000000000000 (@ep487 24107000684858049 4503599627370496 437500000208019 29717000000000000000 (ep488 qz168) ep498 rfl) (@ep499 1746897592588339737 56294995342131200 10591000000314732747 29717000000000000000000 (ep500 qz168) ep501 rfl) rfl

noncomputable def ep503 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz162 qz165) (@HMul.hMul Real Real Real qz0 qz164 qz163) 5772959658256245 2251799813685248 7000000000208019 237736000000000000000 36473892036190228137 562949953421312000

noncomputable def ep504 := nat_lit 85381790662187472885584959924862976

noncomputable def ep505 := @Enclosure.Real.IsNear.mulLit_ff qz162 qz165 7000 4000 0 1 824708522608035 562949953421312 1000000000029717 59434000000000000000

noncomputable def ep506 := @Enclosure.Real.IsNear.mulLit_ff qz164 qz163 84728 4000 0 1 3443857240694007 1125899906842624 62500000029717 7429250000000000000

noncomputable def ep507 := @ep503 661937500314732747 3714625000000000000000 ep504 37917131950754289387 562949953421312000 6170500002543864351 29717000000000000000000 (@ep505 5772959658256245 2251799813685248 7000000000208019 237736000000000000000 (ep488 qz168) ep501 rfl) (@ep506 36473892036190228137 562949953421312000 661937500314732747 3714625000000000000000 (ep500 qz168) ep498 rfl) rfl

noncomputable def ep508 := @Enclosure.Complex.IsNear.of_eq qz158 qz167 Bool.false 9000 4000 0 1 Bool.false 84728 4000 0 1 (BSN.w_shift_mk qz145 Bool.false 42364 1000 2 qz146 rfl)

noncomputable abbrev qz366 := (ep508 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 84728 4000) Bool.false 9000 4000 0 1 Bool.false 84728 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 84728 4000)))

noncomputable abbrev qz169 := qz366

noncomputable def ep509 := ep483 (@ep484 29717000000000000000000 (ep502 rfl) (ep507 rfl)) qz169 rfl rfl rfl rfl rfl rfl

noncomputable def ep510 := @ep481 6170500002543864351 29717000000000000000000 (ep509 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz39 (↑qz3) Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 (@ep103 65536 1 65536 (ep105 rfl) (ep107 rfl) rfl rfl) (@ep108 1 0 1 (ep110 rfl) (ep112 rfl) rfl rfl))

noncomputable abbrev qz367 := (@HPow.hPow Complex Int Complex qz422 qz431 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz170 := qz367

noncomputable def ep511 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz16 qz158 (@HSub.hSub Int Int Int qz18 qz19 (@HMul.hMul Int Int Int qz20 qz21 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz16 qz158 (@HSub.hSub Int Int Int qz18 qz19 (@HMul.hMul Int Int Int qz20 qz21 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45) qz170)) Bool.false 443703 1073741824 3 1073741824

noncomputable def ep512 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz16 qz158 (@HSub.hSub Int Int Int qz18 qz19 (@HMul.hMul Int Int Int qz20 qz21 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45) qz170) Bool.false 0 1 0 1 Bool.false

noncomputable def ep513 := @ep512 0 1 0 1 Bool.false 443703 1073741824 3 1073741824 Bool.true 1566419491 402653184000 10591 402653184000 Bool.false 443703 443703 1073741824 3 1073741824 Bool.true 1566419491 1566419491 402653184000 10591

noncomputable def ep514 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz16 qz158 (@HSub.hSub Int Int Int qz18 qz19 (@HMul.hMul Int Int Int qz20 qz21 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz42 qz42) Bool.false 0 1 0 1 Bool.false

noncomputable def ep515 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45) qz170 Bool.false 443703 1073741824 3 1073741824 Bool.true 1566419491 402653184000 10591 402653184000

noncomputable abbrev qz171 := (Complex.re qz367)

noncomputable abbrev qz172 := (Complex.im qz367)

noncomputable def ep516 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz171) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz172) 443703 1073741824 3 1073741824 0 1 0

noncomputable def ep517 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz171 1 12 0 1 1331109 268435456 9 268435456 443703

noncomputable def ep518 := @Enclosure.Complex.IsNear.re_isNear qz170 Bool.false 1331109 268435456 9 268435456 Bool.true 1566419491 33554432000 10591 33554432000

noncomputable abbrev qz368 := (@HPow.hPow Complex Nat Complex qz423 qz431 1)

noncomputable abbrev qz173 := (@Inv.inv Complex Complex.instInv qz368)

noncomputable def ep519 := @Enclosure.Complex.IsNear.of_eq qz170 qz173 Bool.false 1331109 268435456 9 268435456 Bool.true 1566419491 33554432000 10591

noncomputable def ep520 := @Enclosure.Complex.IsNear.of_parts qz173 Bool.false 1331109 268435456 9 268435456 Bool.true 1566419491 33554432000 10591

noncomputable abbrev qz174 := (Complex.re qz368)

noncomputable abbrev qz175 := qz368

noncomputable def ep521 := @Enclosure.Real.IsNear.mulLit_ff qz174 (@Inv.inv Real Real.instInv (@DFunLike.coe qz51 Complex (fun (x : Complex) => Real) qz52 Complex.normSq qz175)) 9000 4000 0 1 147901 67108864 1 67108864

noncomputable def ep522 := @Enclosure.Complex.IsNear.re_isNear qz175 Bool.false 9000 4000 0 1 Bool.false 84728 4000 0 1

noncomputable def ep523 := @Enclosure.Complex.IsNear.of_eq qz175 qz158 Bool.false 9000 4000 0 1 Bool.false 84728 4000 0

noncomputable def ep524 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz51 Complex (fun (x : Complex) => Real) qz52 Complex.normSq qz175)) Bool.false 147901 67108864 1 67108864 147901 67108864 1

noncomputable abbrev qz176 := (Complex.im qz368)

noncomputable def ep525 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz51 Complex (fun (x : Complex) => Real) qz52 Complex.normSq qz175) (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 qz174 qz174) (@HMul.hMul Real Real Real qz0 qz176 qz176)) Bool.false 56717453 125000 0 1

noncomputable def ep526 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz174 qz174) (@HMul.hMul Real Real Real qz0 qz176 qz176) 81 16 0 1 112169281 250000

noncomputable def ep527 := @Enclosure.Real.IsNear.mulLit_ff qz174 qz174 9000 4000 0 1 9000 4000 0 1

noncomputable def ep528 := @Enclosure.Real.IsNear.mulLit_ff qz176 qz176 84728 4000 0 1 84728 4000 0 1

noncomputable def ep529 := @Enclosure.Complex.IsNear.im_isNear qz175 Bool.false 9000 4000 0 1 Bool.false 84728 4000 0 1

noncomputable abbrev qz177 := (ep522 (@ep523 1 (BSN.pow_one_c qz356) qz366))

noncomputable abbrev qz178 := (ep529 (@ep523 1 (BSN.pow_one_c qz356) qz366))

noncomputable def ep530 := @ep526 0 1 1814958496 56717453 125000 0 1 (@ep527 81 16 0 1 qz177 qz177 rfl) (@ep528 112169281 250000 0 1 qz178 qz178 rfl)

noncomputable def ep531 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz51 Complex (fun (x : Complex) => Real) qz52 Complex.normSq qz175) 56717453 125000 0 1 73950 73951 33554432 (ep525 (Enclosure.Complex.normSq_eq_mul_add_mul qz175) (ep530 rfl rfl)) rfl

noncomputable def ep532 := @Enclosure.Real.IsNear.of_eq (Complex.re qz173) (@HMul.hMul Real Real Real qz0 qz174 (@Inv.inv Real Real.instInv (@DFunLike.coe qz51 Complex (fun (x : Complex) => Real) qz52 Complex.normSq qz175))) Bool.false 1331109 268435456 9 268435456 (Enclosure.Complex.inv_re_eq_mul qz175) (@ep521 1331109 268435456 9 268435456 qz177 (@ep524 67108864 (ep531 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep533 := @Enclosure.Real.IsNear.of_eq (Complex.im qz173) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz176) (@Inv.inv Real Real.instInv (@DFunLike.coe qz51 Complex (fun (x : Complex) => Real) qz52 Complex.normSq qz175))) Bool.true 1566419491 33554432000 10591 33554432000 (Enclosure.Complex.inv_im_eq_mul qz175)

noncomputable def ep534 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz176) (@Inv.inv Real Real.instInv (@DFunLike.coe qz51 Complex (fun (x : Complex) => Real) qz52 Complex.normSq qz175)) 84728 4000 0 1 147901 67108864 1

noncomputable def ep535 := @ep534 67108864 1566419491 33554432000 10591 33554432000 (@Enclosure.Real.IsNear.neg qz176 Bool.false 84728 4000 0 1 qz178) (@ep524 67108864 (ep531 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep536 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz172 0 1 0 1 1566419491 33554432000 10591 33554432000 0

noncomputable def ep537 := @Enclosure.Complex.IsNear.im_isNear qz170 Bool.false 1331109 268435456 9 268435456 Bool.true 1566419491 33554432000 10591 33554432000

noncomputable abbrev qz179 := (@ep519 33554432000 (BSN.zpow_one_sub_two_mul qz356 1 1 rfl rfl) (@ep520 33554432000 ep532 (ep533 ep535)))

noncomputable def ep538 := @ep516 1 443703 443703 1073741824 3 1073741824 (@ep517 1073741824 3 1073741824 ep122 (ep518 qz179) rfl) (@ep536 1 0 1 ep142 (ep537 qz179) rfl) rfl

noncomputable def ep539 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz172) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz171) 1566419491 402653184000 10591 402653184000 0 1 0

noncomputable def ep540 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz172 1 12 0 1 1566419491 33554432000 10591 33554432000 1566419491

noncomputable def ep541 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 (@Rat.cast Complex Complex.instRatCast (bernoulli qz44)) qz45)) qz171 0 1 0 1 1331109 268435456 9 268435456 0

noncomputable def ep542 := @ep539 1 1566419491 1566419491 402653184000 10591 402653184000 (@ep540 402653184000 10591 402653184000 ep122 (ep537 qz179) rfl) (@ep541 1 0 1 ep142 (ep518 qz179) rfl) rfl

noncomputable def ep543 := @ep513 402653184000 (@ep514 0 1 0 1 (BSN.stirling_sum_base qz158) qz59) (ep515 (ep538 rfl) (ep542 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep544 := @ep479 15594321614523079309 337769972052787200 75832708912454073504463 ep467 (ep510 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep511 Bool.true 1566419491 402653184000 10591 402653184000 (BSN.stirling_sum_succ qz158 0 1 rfl) (ep543 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep545 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz145 2) Bool.false 3438559398534391 562949953421312 62500000029717 3714625000000000000 Bool.false 864370398102947 281474976710656

noncomputable abbrev qz180 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz262 qz357 qz287))

noncomputable def ep546 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 2) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz145 1) qz180) Bool.false 3438559398534391 562949953421312 62500000029717 3714625000000000000 Bool.false 864370398102947 281474976710656 1000000000029717 29717000000000000000

noncomputable def ep547 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz145 1) qz180 Bool.false 3437620948180215 1125899906842624 62500000029717 7429250000000000000 Bool.false 877639699563939 562949953421312 1000000000029717 59434000000000000000 Bool.false

noncomputable def ep548 := nat_lit 7742947412965400078595777363968

noncomputable def ep549 := nat_lit 973194550701629847954079612928

noncomputable abbrev qz181 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz262 qz357 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep550 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 1) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz145 0) qz181) Bool.false 3437620948180215 1125899906842624 62500000029717 7429250000000000000 Bool.false 877639699563939 562949953421312 1000000000029717 59434000000000000000

noncomputable def ep551 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz145 0) qz181 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz369 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz166))

noncomputable def ep552 := @Enclosure.Complex.IsNear.of_eq qz181 qz369 Bool.false 3437620948180215 1125899906842624 62500000029717 7429250000000000000 Bool.false 877639699563939 562949953421312 1000000000029717 59434000000000000000

noncomputable def ep553 := nat_lit 246956915955630476583557192976445607905819096881074061237529856305119964567405854720

noncomputable def ep554 := nat_lit 6449165704279988339122118574509452258462401111517243968091598628941328536750260224

noncomputable def ep555 := nat_lit 858849801611567019908017204161300962106446588678007078615207952071597836206080

noncomputable def ep556 := BSN.log_dyadic_bound 3083833984 11275833984 5 4 ep553 131072 59434 ep554 ep555 73566 14359667968 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3083833984) (BSN.artanhQ 11275833984) 0 4 ep554 ep553 ep555 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep557 := @Enclosure.Real.IsNear.mulLit_ff qz31 (Real.log (Enclosure.sfrac Bool.false 7179833984 16000000)) 1 2 0 1 3437620948180215 562949953421312 62500000029717 3714625000000000000 3437620948180215 1125899906842624 62500000029717 7429250000000000000 qz32 (BSN.isNear_log_sfrac 7179833984 16000000 3437620948180215 562949953421312 62500000029717 3714625000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7179833984) qz279)) Bool.false 28836854586872136990720 4722366482869645213696 1000000000475472 59434000000000000000 3437620948180215 562949953421312 62500000029717 3714625000000000000 (BSN.log_rat_reduce_isNear 7179833984 16000000 8 14359667968 8192000000 73566 131072 24973259072661432 36028797018963968 59434 1000000000000000 rfl rfl rfl rfl (ep556 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep558 := BSN.arctan_dyadic_bound_f 1000 84728 1 0 131072 59434 0 1 1 0 1 1 1546 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 84728) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 84728) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz370 := (@Nat.cast Real Real.instNatCast 84728)

noncomputable def ep559 := @Enclosure.Real.IsNear.subLit_ff_p qz33 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz292 qz370)) 884279719003555 562949953421312 1 2000000000000000 1546 131072 1 59434 115033990701244612608 877639699563939 562949953421312 1000000000029717 59434000000000000000 qz34 (ep558 rfl) rfl rfl

noncomputable abbrev qz182 := (@HAdd.hAdd Complex Complex Complex qz262 qz357 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz371 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz166)

noncomputable def ep560 := @ep551 3437620948180215 1125899906842624 62500000029717 7429250000000000000 Bool.false 877639699563939 562949953421312 1000000000029717 59434000000000000000 Bool.false 3437620948180215 3437620948180215 1125899906842624 62500000029717 7429250000000000000 Bool.false 877639699563939 877639699563939 562949953421312 1000000000029717 59434000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 0) (Complex.mk qz42 qz42) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz145) qz59) (ep552 (@congrArg Complex Complex qz182 qz371 Complex.log (BSN.w_shift_mk qz145 Bool.false 42364 1000 0 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts qz369 Bool.false 3437620948180215 1125899906842624 62500000029717 7429250000000000000 Bool.false 877639699563939 562949953421312 1000000000029717 59434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz369) (@HMul.hMul Real Real Real qz0 qz31 (Real.log (Enclosure.sfrac Bool.false 7179833984 16000000))) Bool.false 3437620948180215 1125899906842624 62500000029717 7429250000000000000 (Enclosure.clog_re_eq 1000 84728 4000 7179833984 16000000 rfl rfl rfl) (ep557 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz369) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz370 qz292)) Bool.false 877639699563939 562949953421312 1000000000029717 59434000000000000000 (Enclosure.clog_im_eq 1000 84728 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz370 qz292)) (@HSub.hSub Real Real Real qz5 qz33 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz292 qz370))) Bool.false 877639699563939 562949953421312 1000000000029717 59434000000000000000 (BSN.arctan_recip 84728 1000 rfl rfl) ep559)))) rfl rfl

noncomputable abbrev qz372 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz166))

noncomputable def ep561 := @Enclosure.Complex.IsNear.of_eq qz180 qz372 Bool.false 3439497848888567 1125899906842624 62500000029717 7429250000000000000 Bool.false 851101096641955 562949953421312 1000000000029717 59434000000000000000

noncomputable def ep562 := nat_lit 251193450644473989246245038189525245436474913963861793157460460505851686950765854720

noncomputable def ep563 := nat_lit 6637623810254422292406304414155499224359696342663634428074748047266187302062260224

noncomputable def ep564 := nat_lit 913801338777142461205292694313138057789292755604082358431826224734084876206080

noncomputable def ep565 := BSN.log_dyadic_bound 3107833984 11299833984 5 4 ep562 131072 59434 ep563 ep564 74003 14407667968 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3107833984) (BSN.artanhQ 11299833984) 0 4 ep563 ep562 ep564 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep566 := @Enclosure.Real.IsNear.mulLit_ff qz31 (Real.log (Enclosure.sfrac Bool.false 7203833984 16000000)) 1 2 0 1 3439497848888567 562949953421312 62500000029717 3714625000000000000 3439497848888567 1125899906842624 62500000029717 7429250000000000000 qz32 (BSN.isNear_log_sfrac 7203833984 16000000 3439497848888567 562949953421312 62500000029717 3714625000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7203833984) qz279)) Bool.false 28852599171169424244736 4722366482869645213696 1000000000475472 59434000000000000000 3439497848888567 562949953421312 62500000029717 3714625000000000000 (BSN.log_rat_reduce_isNear 7203833984 16000000 8 14407667968 8192000000 74003 131072 24973259072661432 36028797018963968 59434 1000000000000000 rfl rfl rfl rfl (ep565 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep567 := BSN.arctan_dyadic_bound_f 5000 84728 1 0 131072 59434 0 1 1 0 1 1 7725 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 84728) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 84728) 0 0 rfl) rfl rfl rfl

noncomputable def ep568 := @Enclosure.Real.IsNear.subLit_ff_p qz33 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz296 qz370)) 884279719003555 562949953421312 1 2000000000000000 7725 131072 1 59434 111555522939054325760 851101096641955 562949953421312 1000000000029717 59434000000000000000 qz34 (ep567 rfl) rfl rfl

noncomputable abbrev qz183 := (@HAdd.hAdd Complex Complex Complex qz262 qz357 qz287)

noncomputable abbrev qz373 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz166)

noncomputable def ep569 := @ep547 3439497848888567 1125899906842624 62500000029717 7429250000000000000 Bool.false 851101096641955 562949953421312 1000000000029717 59434000000000000000 Bool.false ep548 3438559398534391 562949953421312 62500000029717 3714625000000000000 Bool.false ep549 864370398102947 281474976710656 1000000000029717 29717000000000000000 (ep550 (BSN.log_sum_c_succ qz145 0 1 rfl) (ep560 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep561 (@congrArg Complex Complex qz183 qz373 Complex.log (BSN.w_shift_mk qz145 Bool.false 42364 1000 1 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts qz372 Bool.false 3439497848888567 1125899906842624 62500000029717 7429250000000000000 Bool.false 851101096641955 562949953421312 1000000000029717 59434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz372) (@HMul.hMul Real Real Real qz0 qz31 (Real.log (Enclosure.sfrac Bool.false 7203833984 16000000))) Bool.false 3439497848888567 1125899906842624 62500000029717 7429250000000000000 (Enclosure.clog_re_eq 5000 84728 4000 7203833984 16000000 rfl rfl rfl) (ep566 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz372) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz370 qz296)) Bool.false 851101096641955 562949953421312 1000000000029717 59434000000000000000 (Enclosure.clog_im_eq 5000 84728 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz370 qz296)) (@HSub.hSub Real Real Real qz5 qz33 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz296 qz370))) Bool.false 851101096641955 562949953421312 1000000000029717 59434000000000000000 (BSN.arctan_recip 84728 5000 rfl rfl) ep568)))) rfl rfl

noncomputable def ep570 := @ep472 ep467 Bool.false 3438559398534391 562949953421312 62500000029717 3714625000000000000 Bool.false 864370398102947 281474976710656 1000000000029717 29717000000000000000 Bool.true ep473 3728650674983200849 112589990684262400 49078388587190885546087 ep62 Bool.false ep474 14557077136799542909 337769972052787200 88120708912819236000463 ep467 (@ep475 112589990684262400 47030388586217118890087 ep62 Bool.false 15594321614523079309 337769972052787200 75832708912454073504463 ep467 (BSN.logGammaStirling_unfold 1 qz158) (ep544 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep545 1000000000029717 29717000000000000000 (BSN.log_sum_c_eq qz145 2) (ep546 (BSN.log_sum_c_succ qz145 1 2 rfl) (ep569 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz184 := (@HDiv.hDiv Real Real Real qz257 qz346 (2 : Real))

noncomputable def ep571 := @Enclosure.Real.IsNear.mulLit_ff qz184 (Real.log Real.pi) 42364 2000 0 1 75021 65536 1 32768 794547411 32768000 10591 16384000 (@Enclosure.Real.IsNear.of_eq qz184 (Enclosure.sfrac Bool.false 42364 2000) Bool.false 42364 2000 0 1 (BSN.t_half_eq qz145 Bool.false 42364 1000 qz146) (Enclosure.Real.IsNear.const Bool.false 42364 2000)) EMRow07.d5 rfl

noncomputable def ep572 := @ep469 10591 16384000 ep470 31834723939600066673 1688849860263936000 324170269162819236000463 ep467 (@ep471 88120708912819236000463 ep467 (ep570 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep571 rfl rfl

noncomputable def ep573 := BSN.cos_dyadic_bound_f 102412 268435456 1 0 131072 59493 0 1 1 0 1 1 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 102412) qz313 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 102412) qz314 0 0 rfl) rfl rfl

noncomputable def ep574 := @ep466 65536 Bool.false 131071 131072 1 29717 (@ep468 2470699 131072 59 65536 ep572 rfl) (Enclosure.sfrac_false_div 2470699 131072) (BSN.cos_reduce0 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7206660422299025408) qz312) 226375608064910080 72057594037927936 Bool.false 131071 131072 3 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q0 2470699 131072 226375608064910080 72057594037927936 3 7206660422299025408 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 131071 131072 7206660422299025408 18889465931478580854784 102412 268435456 59493 59434 (ep573 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep575 := nat_lit 2058808136832807128370347

noncomputable abbrev qz185 := qz345

noncomputable abbrev qz374 := (@HPow.hPow Complex Complex Complex qz424 (@Nat.cast Complex Complex.instNatCast 9) qz429)

noncomputable abbrev qz186 := qz374

noncomputable abbrev qz375 := (@Nat.cast Complex Complex.instNatCast 9)

noncomputable abbrev qz187 := (@HAdd.hAdd Complex Complex Complex qz262 (@HDiv.hDiv Complex Complex Complex qz270 qz375 (@HSub.hSub Complex Complex Complex qz260 qz344 (1 : Complex))) qz269)

noncomputable abbrev qz188 := qz375

noncomputable def ep576 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz143 1 9) (@HAdd.hAdd Complex Complex Complex qz8 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 9, @HPow.hPow Complex Complex Complex qz65 (@Nat.cast Complex Complex.instNatCast n) qz185) (@HMul.hMul Complex Complex Complex qz4 qz186 (@HAdd.hAdd Complex Complex Complex qz8 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))))) Bool.false 1515558385049668095073 1300942356412052275200 ep463

noncomputable def ep577 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 9, @HPow.hPow Complex Complex Complex qz65 (@Nat.cast Complex Complex.instNatCast n) qz185) (@HMul.hMul Complex Complex Complex qz4 qz186 (@HAdd.hAdd Complex Complex Complex qz8 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))))) Bool.false 2477989359 2147483648 637235278223 127633543135232

noncomputable def ep578 := nat_lit 3254636849483449901996576866304

noncomputable def ep579 := nat_lit 14916637755549714924653409992704

noncomputable def ep580 := @ep577 Bool.true 4195027995 17179869184 2546356714553 510534172540928 Bool.false 14396167184225723473 1300942356412052275200 130086705807780741061009 ep464 Bool.false 2308414451239430087969 13009423564120522752000 130584313346776453498847 ep464 Bool.false ep578 1515558385049668095073 1300942356412052275200 ep463 ep464 Bool.true ep579 868262592444063334531 13009423564120522752000

noncomputable def ep581 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 9, @HPow.hPow Complex Complex Complex qz65 (@Nat.cast Complex Complex.instNatCast n) qz185) qz128 Bool.false 2477989359 2147483648 637235278223 127633543135232 Bool.true 4195027995 17179869184 2546356714553

noncomputable def ep582 := @Enclosure.Complex.IsNear.mul qz186 (@HAdd.hAdd Complex Complex Complex qz8 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))) Bool.false 14396167184225723473 1300942356412052275200 130086705807780741061009 ep464 Bool.false

noncomputable abbrev qz189 := (Complex.re qz374)

noncomputable abbrev qz190 := (Complex.im qz374)

noncomputable def ep583 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz189 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz190 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))))) 13766205273306681037 208150777025928364032 1529224748653523705731

noncomputable def ep584 := nat_lit 6185616640879513193938944

noncomputable def ep585 := nat_lit 257734026703313049747456000

noncomputable def ep586 := nat_lit 3995431180789007396946967316355348430848

noncomputable def ep587 := @Enclosure.Real.IsNear.mulLit_ff qz189 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))))) 2262800581 17179869184 251364161803 510534172540928 6083702377

noncomputable abbrev qz376 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz430 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable abbrev qz191 := (Real.cos qz376)

noncomputable abbrev qz192 := (@Neg.neg Real Real.instNeg (Real.sin qz376))

noncomputable abbrev qz377 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable def ep588 := @Enclosure.Complex.IsNear.of_eq qz186 (Complex.mk (@HMul.hMul Real Real Real qz0 qz377 qz191) (@HMul.hMul Real Real Real qz0 qz377 qz192)) Bool.false 2262800581 17179869184 251364161803 510534172540928 Bool.false 5260614855 17179869184 253403164041 510534172540928 (BSN.cpow_neg_s_mk qz145 42364 1000 9 qz146 rfl)

noncomputable abbrev qz378 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable abbrev qz379 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9) qz87)

noncomputable def ep589 := @Enclosure.Real.IsNear.inv_image qz378 393217 131072 1 131072 21845 21846 65536 (@Enclosure.Real.IsNear.of_eq qz378 (Real.sqrt qz379) Bool.false 393217 131072 1 131072 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz379) Bool.false 393217 131072 1 131072 393217 131072 1 131072 (BSN.sqrt_enclosure 9 1 196608 196609 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep590 := BSN.log_dyadic_bound 1 17 2 1 867 65536 29717 1 1 7719 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz380 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz193 := qz380

noncomputable def ep591 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz193 42364 1000 0 1 9895417793173221 4503599627370496 1000000000089151 29717000000000000000 104802369847497583611 1125899906842624000 10591000000944198241 7429250000000000000000 qz147 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000089151 29717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz379) Bool.false 5188048803947201691648 2361183241434822606848 1000000000089151 29717000000000000000 9895417793173221 4503599627370496 1000000000089151 29717000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 7719 65536 24973259072661432 36028797018963968 29717 1000000000000000 rfl rfl rfl rfl (ep590 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep592 := nat_lit 141378859618480992072741580960000

noncomputable def ep593 := BSN.sin_dyadic_bound_f 109042580 268435456 2 1 131072 59493 ep592 ep213 ep592 ep592 ep214 ep592 51791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 109042580) qz298 0 1 ep592 ep213 ep592 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 109042580) qz299 0 1 ep592 ep214 ep592 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz194 := qz376

noncomputable abbrev qz381 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12200601) qz88)

noncomputable def ep594 := @Enclosure.Real.IsNear.cos_image qz194 qz381 Bool.false 12200601 131072 47 32768 Bool.false 51791 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 104802369847497583611 1125899906842624000 10591000000944198241 7429250000000000000000 12200601 131072 47 32768 (ep591 rfl) rfl) (Enclosure.sfrac_false_div 12200601 131072) (BSN.cos_reduce3 qz381 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7673189436725481439232) qz312) 226375608064910080 72057594037927936 Bool.false 51791 131072 14 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q3 12200601 131072 226375608064910080 72057594037927936 14 7673189436725481439232 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 51791 131072 7673189436725481439232 18889465931478580854784 109042580 268435456 59493 59434 (ep593 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep595 := BSN.cos_dyadic_bound_f 109042580 268435456 2 1 131072 59493 ep592 ep217 ep592 ep592 ep218 ep592 120405 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 109042580) qz313 0 1 ep592 ep217 ep592 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 109042580) qz314 0 1 ep592 ep218 ep592 rfl rfl rfl rfl) rfl rfl

noncomputable def ep596 := @Enclosure.Real.IsNear.sin_image qz194 qz381 Bool.false 12200601 131072 47 32768 Bool.true 120405 131072 1 29717 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 104802369847497583611 1125899906842624000 10591000000944198241 7429250000000000000000 12200601 131072 47 32768 (ep591 rfl) rfl) (Enclosure.sfrac_false_div 12200601 131072) (BSN.sin_reduce3 qz381 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7673189436725481439232) qz312) 226375608064910080 72057594037927936 Bool.false 120405 131072 14 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q3 12200601 131072 226375608064910080 72057594037927936 14 7673189436725481439232 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 120405 131072 7673189436725481439232 18889465931478580854784 109042580 268435456 59493 59434 (ep595 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz195 := (Real.sin qz376)

noncomputable def ep597 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz377 qz191) (@HMul.hMul Real Real Real qz0 qz377 qz192) Bool.false 2262800581 17179869184 251364161803 510534172540928 Bool.false 5260614855 17179869184 253403164041 510534172540928 (@Enclosure.Real.IsNear.mulLit_ff qz377 qz191 43691 131072 1 131072 51791 131072 1429467 973766656 2262800581 17179869184 251364161803 510534172540928 (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 43691 131072 1 131072 43691 131072 1 131072 (ep589 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz191 Bool.false 51791 131072 1429467 973766656 51791 131072 1429467 973766656 (ep594 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz377 qz192 43691 131072 1 131072 120405 131072 1429467 973766656 5260614855 17179869184 253403164041 510534172540928 (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 43691 131072 1 131072 43691 131072 1 131072 (ep589 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz195 Bool.true 120405 131072 1429467 973766656 (@Enclosure.Real.IsNear.recentre' qz195 Bool.true 120405 131072 1429467 973766656 120405 131072 1429467 973766656 (ep596 rfl rfl) rfl)) rfl)

noncomputable def ep598 := @ep587 12115969848 0 1 13766205273306681037 208150777025928364032 1529224748653523705731 ep584 (@Enclosure.Complex.IsNear.re_isNear qz186 Bool.false 2262800581 17179869184 251364161803 510534172540928 Bool.false 5260614855 17179869184 253403164041 510534172540928 (ep588 ep597))

noncomputable def ep599 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))) Bool.false 6083702377 12115969848 0 1 Bool.false

noncomputable def ep600 := @Enclosure.Complex.IsNear.addLitP qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) Bool.false 55811203 112184906 0 1 Bool.true 11914875

noncomputable def ep601 := @ep600 56092453 0 1 Bool.false 1 216 0 1 Bool.false 10591 27000 0 1 Bool.false 12167404754 6083702377 12115969848 0 1 Bool.false 272373544723 272373544723 1514496231000 0 1

noncomputable abbrev qz196 := (@HDiv.hDiv Complex Complex Complex qz270 qz375 (@HSub.hSub Complex Complex Complex qz260 qz344 (1 : Complex)))

noncomputable def ep602 := @Enclosure.Complex.IsNear.addLitP qz196 qz39 Bool.true 18000000 7179833984 0 1 Bool.true 1525104000 7179833984 0 1

noncomputable def ep603 := @Enclosure.Complex.IsNear.of_eq qz196 (Complex.mk (Enclosure.sfrac Bool.true 18000000 7179833984) (Enclosure.sfrac Bool.true 1525104000 7179833984)) Bool.true 18000000 7179833984 0 1 Bool.true 1525104000 7179833984 0 1

noncomputable def ep604 := @ep602 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 7143833984 55811203 112184906 0 1 Bool.true 1525104000 11914875 56092453 0 1 (ep603 (BSN.N_div_s_sub_one_mk qz145 42364 1000 9 qz146 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 18000000 7179833984) (Enclosure.sfrac Bool.true 1525104000 7179833984) Bool.true 18000000 7179833984 0 1 Bool.true 1525104000 7179833984 0 1 (Enclosure.Real.IsNear.const Bool.true 18000000 7179833984) (Enclosure.Real.IsNear.const Bool.true 1525104000 7179833984))) qz41 rfl

noncomputable abbrev qz382 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz423 (@Nat.cast Complex Complex.instNatCast 9) 1))

noncomputable abbrev qz197 := qz382

noncomputable def ep605 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz197)) Bool.false 1 216 0 1

noncomputable def ep606 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz197) Bool.false 0 1 0 1 Bool.false

noncomputable def ep607 := @ep606 0 1 0 1 Bool.false 1 216 0 1 Bool.false 10591 27000 0 1 Bool.false 1 1 216 0 1 Bool.false 10591 10591 27000 0

noncomputable def ep608 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (Complex.mk qz42 qz42) Bool.false 0 1 0 1 Bool.false

noncomputable def ep609 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz197 Bool.false 1 216 0 1 Bool.false 10591 27000 0 1

noncomputable abbrev qz198 := (Complex.re qz382)

noncomputable abbrev qz199 := (Complex.im qz382)

noncomputable def ep610 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199) 1 216 0 1 0 1 0

noncomputable def ep611 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198 1 24 0 1 1 9 0 1 1

noncomputable def ep612 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep613 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep614 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz143 Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 (BSN.ascPochhammer_one_eval qz143)

noncomputable def ep615 := ep614 (@Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk qz31 qz145) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 (BSN.s_crit_mk qz145 Bool.false 42364 1000 qz146) (@Enclosure.Complex.IsNear.mk qz31 qz145 Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 qz32 qz147))

noncomputable def ep616 := @ep613 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep320) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep615)

noncomputable def ep617 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 42364 1000 0 1 0 1 0

noncomputable def ep618 := @ep617 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep320) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep615)

noncomputable def ep619 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) 10591 3000 0 1 0 1 0 1 10591

noncomputable def ep620 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 42364 1000 0 1 10591 3000 0

noncomputable def ep621 := @ep620 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep320) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep615)

noncomputable def ep622 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep623 := @ep622 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep320) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep615)

noncomputable def ep624 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 10591 3000 0 1 (@ep612 1 24 0 1 (ep616 rfl) (ep618 rfl) rfl rfl) (@ep619 10591 3000 0 1 (ep621 rfl) (ep623 rfl) rfl rfl)

noncomputable def ep625 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 10591 3000 0 1 ep624

noncomputable abbrev qz200 := (@Enclosure.Complex.IsNear.of_eq qz382 (Complex.mk (Enclosure.sfrac Bool.false 1 9) qz285) Bool.false 1 9 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 9 1 9 EMRow07.d10 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 9) qz285 Bool.false 1 9 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 9) qz286))

noncomputable def ep626 := @ep611 216 0 1 ep625 (@Enclosure.Complex.IsNear.re_isNear qz197 Bool.false 1 9 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep627 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199 10591 3000 0 1 0 1 0 1 0

noncomputable def ep628 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 10591 3000 0 1 ep624

noncomputable def ep629 := @ep627 1 0 1 ep628 (@Enclosure.Complex.IsNear.im_isNear qz197 Bool.false 1 9 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep630 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198) 0 1 0 1 10591 27000 0

noncomputable def ep631 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199 1 24 0 1 0 1 0 1 0

noncomputable def ep632 := @ep631 1 0 1 ep625 (@Enclosure.Complex.IsNear.im_isNear qz197 Bool.false 1 9 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep633 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz44)) ↑qz123) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198 10591 3000 0 1 1 9 0 1 10591

noncomputable def ep634 := @ep633 27000 0 1 ep628 (@Enclosure.Complex.IsNear.re_isNear qz197 Bool.false 1 9 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep635 := @ep607 1 (@ep608 0 1 0 1 (BSN.bern_sum_base qz143 9) qz59) (ep609 (@ep610 1 1 1 216 0 1 (ep626 rfl) (ep629 rfl) rfl rfl) (@ep630 1 10591 10591 27000 0 1 (ep632 rfl) (ep634 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep636 := ep601 (ep604 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep605 Bool.false 10591 27000 0 1 (BSN.bern_sum_succ qz143 9 0 1 1 rfl rfl) (ep635 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep637 := @Enclosure.Real.IsNear.mulLit_ff qz190 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))))) 5260614855 17179869184 253403164041 510534172540928 272373544723

noncomputable def ep638 := @ep637 1514496231000 0 1 95523487698588044011 1734589808549403033600 23006772677957006301881 ep585 (@Enclosure.Complex.IsNear.im_isNear qz186 Bool.false 2262800581 17179869184 251364161803 510534172540928 Bool.false 5260614855 17179869184 253403164041 510534172540928 (ep588 ep597))

noncomputable def ep639 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))) Bool.false 6083702377 12115969848 0 1 Bool.false

noncomputable def ep640 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz189 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz190 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1))))))) 616327015248233884063 26018847128241045504000 68464947766608828815569

noncomputable def ep641 := nat_lit 773202080109939149242368000

noncomputable def ep642 := nat_lit 2061872213626504397979648

noncomputable def ep643 := nat_lit 320332174482246264050927439217382677020672

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_ff qz189 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))))) 2262800581 17179869184 251364161803 510534172540928 272373544723

noncomputable def ep645 := @ep644 1514496231000 0 1 616327015248233884063 26018847128241045504000 68464947766608828815569 ep641 (@Enclosure.Complex.IsNear.re_isNear qz186 Bool.false 2262800581 17179869184 251364161803 510534172540928 Bool.false 5260614855 17179869184 253403164041 510534172540928 (ep588 ep597))

noncomputable def ep646 := @Enclosure.Real.IsNear.mulLit_ff qz190 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz187 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz15 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz15 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz70 qz188 (@HSub.hSub Nat Nat Nat qz69 (@HMul.hMul Nat Nat Nat qz15 2 k) 1)))))) 5260614855 17179869184 253403164041 510534172540928 6083702377

noncomputable def ep647 := @ep646 12115969848 0 1 10668005032615003445 69383592341976121344 513876477138517541819 ep642 (@Enclosure.Complex.IsNear.im_isNear qz186 Bool.false 2262800581 17179869184 251364161803 510534172540928 Bool.false 5260614855 17179869184 253403164041 510534172540928 (ep588 ep597))

noncomputable abbrev qz383 := (ep636 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep648 := @ep582 2308414451239430087969 13009423564120522752000 130584313346776453498847 ep464 (@ep583 ep584 95523487698588044011 1734589808549403033600 23006772677957006301881 ep585 ep586 14396167184225723473 1300942356412052275200 130086705807780741061009 ep464 (ep598 (@ep599 272373544723 1514496231000 0 1 qz383) rfl) (ep638 (@ep639 272373544723 1514496231000 0 1 qz383) rfl) rfl rfl) (@ep640 ep641 10668005032615003445 69383592341976121344 513876477138517541819 ep642 ep643 2308414451239430087969 13009423564120522752000 130584313346776453498847 ep464 (ep645 (@ep639 272373544723 1514496231000 0 1 qz383) rfl) (ep647 (@ep599 272373544723 1514496231000 0 1 qz383) rfl) rfl rfl)

noncomputable def ep649 := @ep580 ep575 ep464 (@ep581 510534172540928 (BSN.head_sum_c_eq qz143 9) EMRow07.d9) ep648 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def ep650 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz143 1 9) Bool.false 1515558385049668095073 1300942356412052275200 ep463 ep464 Bool.true 868262592444063334531 13009423564120522752000 ep575 ep464 (@ep576 ep464 Bool.true 868262592444063334531 13009423564120522752000 ep575 ep464 (BSN.zetaApproximant_eq_folded' qz143 1 9 rfl) (ep649 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep651 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) (Complex.im (zetaApproximant qz143 1 9)) 25 65536 1818839

noncomputable def ep652 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156)) Bool.false 50 131072 1818839

noncomputable def ep653 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156) qz358 Bool.false 2470699 131072 59

noncomputable def ep654 := BSN.sin_dyadic_bound_f 102412 268435456 1 0 131072 59493 0 1 1 0 1 1 50 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 102412) qz298 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 102412) qz299 0 0 rfl) rfl rfl

noncomputable def ep655 := @ep653 65536 Bool.false 50 131072 1 29717 (@ep468 2470699 131072 59 65536 ep572 rfl) (Enclosure.sfrac_false_div 2470699 131072) (BSN.sin_reduce0 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7206660422299025408) qz312) 226375608064910080 72057594037927936 Bool.false 50 131072 3 1000000000000000 59434 29717 (BSN.sin_reduce_arg_pos_rat_q0 2470699 131072 226375608064910080 72057594037927936 3 7206660422299025408 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 50 131072 7206660422299025408 18889465931478580854784 102412 268435456 59493 59434 (ep654 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep656 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz143 1 9) Bool.false 1515558385049668095073 1300942356412052275200 ep463 ep464 Bool.true 868262592444063334531 13009423564120522752000 ep575 ep464 (@ep576 ep464 Bool.true 868262592444063334531 13009423564120522752000 ep575 ep464 (BSN.zetaApproximant_eq_folded' qz143 1 9 rfl) (ep649 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow07.d11 : Enclosure.Real.IsNear (hardyZApproximantEM 1 9 qz145) Bool.false ep447 ep448 ep449 ep450 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 9 qz145) ep451 Bool.false ep447 ep448 ep449 ep450 (@Eq.refl Real ep451) (@ep452 Bool.false ep447 ep448 ep449 ep450 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz154 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz155 (@Nat.cast Complex Complex.instNatCast j))))) qz156) (zetaApproximant qz143 1 9)) (@ep454 ep455 ep456 ep457 868262592444063334531 ep458 ep459 ep460 ep461 ep447 ep448 ep449 ep450 (@ep462 1947533312 1515558385049668095073 1300942356412052275200 ep463 ep464 ep453 ep455 ep456 ep457 (@ep465 1947533312 131071 131072 1818839 1947533312 (ep574 rfl rfl) rfl) ep650 rfl) (@ep651 1947533312 868262592444063334531 13009423564120522752000 ep575 ep464 868262592444063334531 ep458 ep459 ep460 (@ep652 1947533312 25 65536 1818839 1947533312 (ep655 rfl rfl) rfl) ep656 rfl) rfl rfl))

theorem EMRow07.d12 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow07.d13 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow07.d14 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow07.d15 : @Eq Nat (Nat.pow 8 (Nat.succ (Nat.mul 2 3))) 2097152 := @Eq.refl Nat 2097152

noncomputable abbrev qz433 := (@HAdd.hAdd Complex Complex Complex qz436 qz440 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz384 := qz433

noncomputable abbrev qz201 := (@HDiv.hDiv Real Real Real qz257 (@Norm.norm Complex Complex.instNorm qz384) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz265) qz316))

noncomputable abbrev qz202 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz203 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz385 := (@HPow.hPow Complex Complex Complex qz424 (@Nat.cast Complex Complex.instNatCast 8) (@HSub.hSub Complex Complex Complex qz414 qz425 qz426))

noncomputable abbrev qz204 := qz385

noncomputable def ep657 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) 29112993 1073741824 2306297 28991029248 78596767241317 123145302310912 287322143

noncomputable def ep658 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 8)) 123 8192 1 221184 236691 131072 623 131072 29112993 1073741824

noncomputable abbrev qz386 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz387 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz205 := (@HPow.hPow Real Nat Real qz386 qz387 2)

noncomputable def ep659 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz205) 96 162 0 1 3321 131072 1 131072 123 8192 1 221184

noncomputable def ep660 := nat_lit 781950621441006189802102638025

noncomputable def ep661 := nat_lit 19807040628566084398385987584

noncomputable def ep662 := nat_lit 26986075409044041160201671

noncomputable def ep663 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz206 := qz387

noncomputable abbrev qz388 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz206 1)

noncomputable def ep664 := @Enclosure.Real.IsNear.mulLit_ff qz388 qz206 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep660 ep661 ep662 ep663

noncomputable def ep665 := ep664 (@Enclosure.Real.IsNear.of_eq qz388 qz206 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz206) (@Enclosure.Real.IsNear.of_eq qz206 qz255 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz256)) (@Enclosure.Real.IsNear.of_eq qz206 qz255 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz256) rfl

noncomputable def ep666 := @Enclosure.Real.IsNear.inv_image qz205 ep660 ep661 ep662 ep663 1660 1661 65536 (@Enclosure.Real.IsNear.of_eq qz205 (@HMul.hMul Real Real Real qz0 qz388 qz206) Bool.false ep660 ep661 ep662 ep663 (BSN.pow_succ_r qz206 1 2 rfl) ep665) rfl rfl rfl

noncomputable def ep667 := ep659 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz205) Bool.false 3321 131072 1 131072 3321 131072 1 131072 (ep666 rfl rfl rfl) rfl)

noncomputable def ep668 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 8)) (Real.sqrt (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 8)) (Complex.re (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 8)) (Complex.im (zetaApproximant qz11 1 8))))) Bool.false 236691 131072 623 131072

noncomputable def ep669 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 8)) (Complex.re (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 8)) (Complex.im (zetaApproximant qz11 1 8))))) Bool.false 236691 131072 623 131072

noncomputable def ep670 := nat_lit 299841567476837717822810184485018122733

noncomputable def ep671 := nat_lit 91949205404187525528038616648908800000

noncomputable def ep672 := nat_lit 95279443156118602205415857458501062814552014509260838087

noncomputable def ep673 := nat_lit 5558386551143597972043509186151411743500736076447744000000

noncomputable def ep674 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 8)) (Complex.re (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 8)) (Complex.im (zetaApproximant qz11 1 8)))) ep670 ep671 ep672 ep673 118034 118657

noncomputable def ep675 := nat_lit 2271675680405940718787766935773958060910474629041

noncomputable def ep676 := nat_lit 699352783875239759933625420465462568812544000000

noncomputable def ep677 := nat_lit 17915076145300255075402930424344070910229696622525869751

noncomputable def ep678 := nat_lit 1111677310228719594408701837230282348700147215289548800000

noncomputable def ep679 := nat_lit 554831593915502692263795194207050030289460289

noncomputable def ep680 := nat_lit 43709548992202484995851588779091410550784000000

noncomputable def ep681 := nat_lit 1426015607404331707100301334195177065850882849157872333

noncomputable def ep682 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 8)) (Complex.re (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 8)) (Complex.im (zetaApproximant qz11 1 8))) ep675 ep676 ep677 ep678 ep679 ep680 ep681

noncomputable def ep683 := nat_lit 1389596637785899493010877296537852935875184019111936000000

noncomputable def ep684 := nat_lit 99681942466885123882165618815180544273022937638992302551048379785097775846557977264783360000000

noncomputable def ep685 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz11 1 8)) (Complex.re (zetaApproximant qz11 1 8)) ep53 836273151473392549888000 ep54 ep55 ep53 836273151473392549888000 ep54 ep55 ep675

noncomputable def ep686 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz11 1 8)) (Complex.im (zetaApproximant qz11 1 8)) 23554863487515751091233 209068287868348137472000 ep186 ep187 23554863487515751091233 209068287868348137472000 ep186 ep187 ep679

noncomputable def ep687 := @ep657 123145302310912 87977764542355628621824 81935678182501 123145302310912 272262288197 3324923162394624 (@ep658 2306297 28991029248 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz205)) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow07.d12 EMRow07.d13 rfl) (ep667 rfl)) (ep668 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz11 1 8)) (@ep669 236691 131072 623 131072 (@ep674 65536 (@ep682 ep683 ep684 ep670 ep671 ep672 ep673 (@ep685 ep676 ep677 ep678 ep357 ep357 rfl) (@ep686 ep680 ep681 ep683 ep365 ep365 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz207 := (@Norm.norm Complex Complex.instNorm qz384)

noncomputable abbrev qz389 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep688 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz207 qz389) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) Bool.false 78596767241317 123145302310912 287322143 123145302310912 (BSN.zrb_shape_eq qz207 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) qz35 3)

noncomputable def ep689 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz207 qz389) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) 5132221 458752 1 458752 15314377 268435456 53 268435456

noncomputable def ep690 := @Enclosure.Real.IsNear.mulLit_ff qz207 qz389 5132221 131072 1 131072 2 7 0 1 5132221 458752

noncomputable abbrev qz390 := (Complex.re qz433)

noncomputable abbrev qz391 := (Complex.im qz433)

noncomputable abbrev qz208 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz254 qz390 qz390) (@HMul.hMul Real Real Real qz254 qz391 qz391))

noncomputable abbrev qz209 := qz384

noncomputable def ep691 := @Enclosure.Real.IsNear.of_eq qz207 (Real.sqrt qz208) Bool.false 5132221 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz209)

noncomputable def ep692 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz208) Bool.false 5132221 131072 1 131072 5132221

noncomputable def ep693 := @Enclosure.Real.IsNear.sqrt_image qz208 1533172001 1000000 0 1 2566110 2566111 65536

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz254 qz390 qz390)

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz254 qz391 qz391)

noncomputable def ep694 := @Enclosure.Real.IsNear.addLit_ff qz210 qz211 49 4 0 1 1520922001 1000000 0 1

noncomputable abbrev qz212 := qz390

noncomputable def ep695 := @Enclosure.Real.IsNear.mulLit_ff qz212 qz212 7 2 0 1 7 2 0 1 49 4

noncomputable def ep696 := @Enclosure.Complex.IsNear.of_eq qz209 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz35) Bool.false 7 2 0 1 Bool.false 38999 1000 0 1 (BSN.s_add_nat_mk qz35 Bool.false 38999 1000 3 qz36)

noncomputable abbrev qz213 := (ep696 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz264 Bool.false 7 2 0 1 Bool.false 38999 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz308))

noncomputable def ep697 := @ep695 0 1 (@Enclosure.Complex.IsNear.re_isNear qz209 Bool.false 7 2 0 1 Bool.false 38999 1000 0 1 qz213)

noncomputable def ep698 := ep697 (@Enclosure.Complex.IsNear.re_isNear qz209 Bool.false 7 2 0 1 Bool.false 38999 1000 0 1 qz213)

noncomputable abbrev qz214 := qz391

noncomputable def ep699 := @Enclosure.Real.IsNear.mulLit_ff qz214 qz214 38999 1000 0 1 38999 1000 0 1 1520922001 1000000

noncomputable def ep700 := @ep699 0 1 (@Enclosure.Complex.IsNear.im_isNear qz209 Bool.false 7 2 0 1 Bool.false 38999 1000 0 1 qz213)

noncomputable def ep701 := ep700 (@Enclosure.Complex.IsNear.im_isNear qz209 Bool.false 7 2 0 1 Bool.false 38999 1000 0 1 qz213)

noncomputable def ep702 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Real.sqrt (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))))) Bool.false 15314377 268435456

noncomputable def ep703 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))))) Bool.false 30628754 536870912

noncomputable def ep704 := nat_lit 35043172321384640846114227452865589250424395423954264689

noncomputable def ep705 := nat_lit 10766746765857818570520837188270791065600000000000000000000

noncomputable def ep706 := nat_lit 211928420131507282627307523064885115087079596035586133586039

noncomputable def ep707 := nat_lit 9508115027169501740972804097316445346131764838400000000000000000000

noncomputable def ep708 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))) ep704 ep705 ep706 ep707

noncomputable def ep709 := nat_lit 287488974946707921970807043773319402662547857458741001

noncomputable def ep710 := nat_lit 430669870634312742820833487530831642624000000000000000000

noncomputable def ep711 := nat_lit 59006458334477377398257803152228756484034416773472818923639

noncomputable def ep712 := nat_lit 1740996746732308924802753209908287761491293686717858729

noncomputable def ep713 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) ep709 ep710 ep711 ep707 ep712

noncomputable def ep714 := nat_lit 672921672866113660657552324266924441600000000000000000000

noncomputable def ep715 := nat_lit 2986757066348240336504877342044069503965726157463150677

noncomputable def ep716 := nat_lit 185705371624404330878375080025711823166636032000000000000000000

noncomputable def ep717 := nat_lit 943252405641665765344581904047877140679224459991205707355929471929565522700786984081996906496000000000000000000

noncomputable def ep718 := nat_lit 536179983724409393371589251

noncomputable def ep719 := nat_lit 20752587082923245568000000000

noncomputable def ep720 := nat_lit 370324953962751823721106473

noncomputable def ep721 := nat_lit 3083523151716150442721280000000000

noncomputable def ep722 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) ep718 ep719 ep720 ep721 ep718 ep719 ep720

noncomputable def ep723 := nat_lit 1319468357609347494731716723

noncomputable def ep724 := nat_lit 25940733853654056960000000000

noncomputable def ep725 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204) Bool.true ep718 ep719 ep720 ep721 Bool.false ep723 ep724 76171986340792048597147

noncomputable def ep726 := nat_lit 481800492455648506675200000000

noncomputable def ep727 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204 Bool.true ep718 ep719 ep720 ep721 Bool.false ep723 ep724 76171986340792048597147 ep726

noncomputable def ep728 := nat_lit 8646911284551352320000000

noncomputable def ep729 := nat_lit 20556821011441002951475200000

noncomputable def ep730 := nat_lit 649697648311425698249436451

noncomputable def ep731 := nat_lit 318141122869190954032956473

noncomputable abbrev qz215 := (Complex.re qz385)

noncomputable abbrev qz216 := (Complex.im qz385)

noncomputable def ep732 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216) 47299026911256793699103 ep728 347892207290405797921 ep729 ep730 ep719 ep731

noncomputable def ep733 := nat_lit 4636300751817156007744405259150226639625912320000000

noncomputable def ep734 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215 4561516003 480000000 0 1 10369146327701 18014398509481984 1906669882675 1070667761012552237056 47299026911256793699103

noncomputable def ep735 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) 4561516003 480000000 0 1 0 1 0 1 4561516003

noncomputable def ep736 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 13684548009 2000000 0 1 4561516003 480000000 0

noncomputable def ep737 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz42) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow07.d14 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz42 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz43)

noncomputable abbrev qz392 := (@HAdd.hAdd Complex Complex Complex qz416 qz419 qz427)

noncomputable abbrev qz217 := qz392

noncomputable def ep738 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) qz217) Bool.true 13684548009 2000000 0 1 Bool.true 59090192866999 1000000000 0 1

noncomputable abbrev qz218 := (Complex.re qz392)

noncomputable abbrev qz219 := (Complex.im qz392)

noncomputable def ep739 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz218) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz219) 1520172001 400000 0 1 1520922001 500000 0 1

noncomputable def ep740 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz218 1520172001 1000000 0 1 5 2 0 1 1520172001 400000

noncomputable abbrev qz393 := (@HAdd.hAdd Complex Complex Complex qz416 qz419 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz220 := qz393

noncomputable def ep741 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz220) Bool.true 1520172001 1000000 0 1 Bool.false 38999 500 0 1

noncomputable abbrev qz221 := (Complex.re qz393)

noncomputable abbrev qz222 := (Complex.im qz393)

noncomputable def ep742 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz221) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz222) 3 4 0 1 1520922001 1000000 0 1

noncomputable def ep743 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz221 1 2 0 1 3 2 0 1 3 4

noncomputable def ep744 := @ep743 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep322)

noncomputable def ep745 := @Enclosure.Complex.IsNear.of_eq qz220 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz35) Bool.false 3 2 0 1 Bool.false 38999 1000 0 1 (BSN.s_add_nat_mk qz35 Bool.false 38999 1000 1 qz36)

noncomputable abbrev qz223 := (ep745 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz264 Bool.false 3 2 0 1 Bool.false 38999 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz308))

noncomputable def ep746 := ep744 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 3 2 0 1 Bool.false 38999 1000 0 1 qz223)

noncomputable def ep747 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz222 38999 1000 0 1 38999 1000 0 1 1520922001 1000000

noncomputable def ep748 := @ep747 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep322)

noncomputable def ep749 := ep748 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 3 2 0 1 Bool.false 38999 1000 0 1 qz223)

noncomputable def ep750 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz220 Bool.true 1520172001 1000000 0 1 Bool.false 38999 500 0 1 (@ep742 6080688004 1520172001 1000000 0 1 (ep746 rfl) (ep749 rfl) rfl rfl)

noncomputable def ep751 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz222) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz221) 38999 2000 0 1 116997 2000 0 1

noncomputable def ep752 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz222 1 2 0 1 38999 1000 0 1 38999 2000

noncomputable def ep753 := @ep752 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep322)

noncomputable def ep754 := ep753 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 3 2 0 1 Bool.false 38999 1000 0 1 qz223)

noncomputable def ep755 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz221 38999 1000 0 1 3 2 0 1 116997 2000

noncomputable def ep756 := @ep755 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep322)

noncomputable def ep757 := ep756 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 3 2 0 1 Bool.false 38999 1000 0 1 qz223)

noncomputable abbrev qz224 := (ep741 (BSN.ascPochhammer_succ_eval_c 1 2 qz265 rfl) (ep750 (@ep751 311992000 38999 500 0 1 (ep754 rfl) (ep757 rfl) rfl rfl)))

noncomputable def ep758 := @ep740 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1520172001 1000000 0 1 Bool.false 38999 500 0 1 qz224)

noncomputable def ep759 := @Enclosure.Complex.IsNear.of_eq qz217 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz35) Bool.false 5 2 0 1 Bool.false 38999 1000 0 1 (BSN.s_add_nat_mk qz35 Bool.false 38999 1000 2 qz36)

noncomputable abbrev qz225 := (ep759 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz264 Bool.false 5 2 0 1 Bool.false 38999 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz308))

noncomputable def ep760 := ep758 (@Enclosure.Complex.IsNear.re_isNear qz217 Bool.false 5 2 0 1 Bool.false 38999 1000 0 1 qz225)

noncomputable def ep761 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz219 38999 500 0 1 38999 1000 0 1 1520922001 500000

noncomputable def ep762 := @ep761 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1520172001 1000000 0 1 Bool.false 38999 500 0 1 qz224)

noncomputable def ep763 := ep762 (@Enclosure.Complex.IsNear.im_isNear qz217 Bool.false 5 2 0 1 Bool.false 38999 1000 0 1 qz225)

noncomputable def ep764 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) qz217 Bool.true 13684548009 2000000 0 1 Bool.true 59090192866999 1000000000 0 1 (@ep739 1368454800900000 13684548009 2000000 0 1 (ep760 rfl) (ep763 rfl) rfl rfl)

noncomputable def ep765 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz219) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz218) 59285187866999 1000000000 0 1 38999 200 0 1

noncomputable def ep766 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz219 1520172001 1000000 0 1 38999 1000 0 1 59285187866999 1000000000

noncomputable def ep767 := @ep766 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1520172001 1000000 0 1 Bool.false 38999 500 0 1 qz224)

noncomputable def ep768 := ep767 (@Enclosure.Complex.IsNear.im_isNear qz217 Bool.false 5 2 0 1 Bool.false 38999 1000 0 1 qz225)

noncomputable def ep769 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz218 38999 500 0 1 5 2 0 1 38999 200

noncomputable def ep770 := @ep769 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1520172001 1000000 0 1 Bool.false 38999 500 0 1 qz224)

noncomputable def ep771 := ep770 (@Enclosure.Complex.IsNear.re_isNear qz217 Bool.false 5 2 0 1 Bool.false 38999 1000 0 1 qz225)

noncomputable abbrev qz226 := (ep738 (BSN.ascPochhammer_succ_eval_c 2 3 qz265 rfl) (ep764 (@ep765 11818038573399800 59090192866999 1000000000 0 1 (ep768 rfl) (ep771 rfl) rfl rfl)))

noncomputable def ep772 := @ep736 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep737) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 13684548009 2000000 0 1 Bool.true 59090192866999 1000000000 0 1 qz226)

noncomputable def ep773 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 59090192866999 1000000000 0 1 0 1 0

noncomputable def ep774 := @ep773 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep737) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 13684548009 2000000 0 1 Bool.true 59090192866999 1000000000 0 1 qz226)

noncomputable def ep775 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) 59090192866999 720000000000 0 1 0 1 0 1 59090192866999

noncomputable def ep776 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 59090192866999 1000000000 0 1 59090192866999 720000000000 0

noncomputable def ep777 := @ep776 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep737) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 13684548009 2000000 0 1 Bool.true 59090192866999 1000000000 0 1 qz226)

noncomputable def ep778 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 13684548009 2000000 0 1 0 1 0

noncomputable def ep779 := @ep778 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep737) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 13684548009 2000000 0 1 Bool.true 59090192866999 1000000000 0 1 qz226)

noncomputable def ep780 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 4561516003 480000000 0 1 Bool.false 59090192866999 720000000000 0 1 (@ep735 4561516003 480000000 0 1 (ep772 rfl) (ep774 rfl) rfl rfl) (@ep775 59090192866999 720000000000 0 1 (ep777 rfl) (ep779 rfl) rfl rfl)

noncomputable def ep781 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 4561516003 480000000 0 1 Bool.false 59090192866999 720000000000 0 1 ep780

noncomputable def ep782 := @Enclosure.Complex.IsNear.re_isNear qz204 Bool.false 10369146327701 18014398509481984 1906669882675 1070667761012552237056 Bool.false 54975082732745 144115188075855872 5383991952527 4282671044050208948224

noncomputable abbrev qz394 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2097152)))

noncomputable def ep783 := @Enclosure.Complex.IsNear.of_eq qz204 (Complex.mk (@HMul.hMul Real Real Real qz0 qz394 qz116) (@HMul.hMul Real Real Real qz0 qz394 qz117)) Bool.false 10369146327701 18014398509481984 1906669882675 1070667761012552237056 Bool.false 54975082732745 144115188075855872 5383991952527

noncomputable abbrev qz395 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2097152))

noncomputable abbrev qz396 := (@Nat.cast Real Real.instNatCast 2097152)

noncomputable def ep784 := @Enclosure.Real.IsNear.inv_image qz395 777472127993 536870912 1 536870912 185363 185364 268435456 (@Enclosure.Real.IsNear.of_eq qz395 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz396 qz87)) Bool.false 777472127993 536870912 1 536870912 (BSN.sqrt_natCast_div_one 2097152) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz396 qz87)) Bool.false 777472127993 536870912 1 536870912 777472127993 536870912 1 536870912 (BSN.sqrt_enclosure 2097152 1 388736063996 388736063997 268435456 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep785 := nat_lit 20111124560928025897598976

noncomputable def ep786 := nat_lit 9671406556917033397649408

noncomputable def ep787 := BSN.log_dyadic_bound 0 16 1 0 1 268435456 121720832 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep788 := @Enclosure.Real.IsNear.mulLit_ff qz35 qz119 38999 1000 0 1 9364972152248037 4503599627370496 244140714151 29717000000000000000 365224548965521194963 4503599627370496000 9521243711174849 29717000000000000000000 qz90 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 244140714151 29717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz339 Bool.false ep785 ep786 1000000365162496 121720832000000000000000 9364972152248037 4503599627370496 244140714151 29717000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 268435456 24973259072661432 36028797018963968 121720832 1000000000000000 rfl rfl rfl rfl (ep787 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep789 := nat_lit 2382860529372943706226688

noncomputable def ep790 := nat_lit 2417851639229258349412352

noncomputable def ep791 := nat_lit 6095253297269824472276868938451785229672730396396642962210348737213518815802343625716933187799613440

noncomputable def ep792 := nat_lit 775106975594979850699505476734807071347029417072782157158382458646527094091278842792332482107544698880

noncomputable def ep793 := nat_lit 1900861218473397978867123540414839348058312884295819245857735696040894125354480874927536583213056

noncomputable def ep794 := nat_lit 15960681050876773830664109972117813480674580436369014527010000834908483069946040336413513765959499776

noncomputable def ep795 := nat_lit 14210294552574630596157600406804796308028872646334339547903678408519663391673445451192762171971652812800

noncomputable def ep796 := BSN.sin_dyadic_bound_f 1083599513264 1099511627776 3 2 536870912 243679401 ep791 ep792 ep793 ep794 ep795 ep793 447516208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1083599513264) (BSN.sinEvenQ 1099511627776) 0 2 ep791 ep792 ep793 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1083599513264) (BSN.sinOddQ 1099511627776) 0 2 ep794 ep795 ep793 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz397 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1360567469) (@Nat.cast Real Real.instNatCast 16777216))

noncomputable def ep797 := @Enclosure.Real.IsNear.cos_image qz120 qz397 Bool.false 1360567469 16777216 173 536870912 Bool.false 447516208 536870912 1 121720832 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 365224548965521194963 4503599627370496000 9521243711174849 29717000000000000000000 1360567469 16777216 173 536870912 (ep788 rfl) rfl) (Enclosure.sfrac_false_div 1360567469 16777216) (BSN.cos_reduce3 qz397 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep789) (@Nat.cast Real Real.instNatCast ep790)) 226375608064910080 72057594037927936 Bool.false 447516208 536870912 12 1000000000000000 243441664 121720832 (BSN.sin_reduce_arg_pos_rat_q3 1360567469 16777216 226375608064910080 72057594037927936 12 ep789 ep790 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 447516208 536870912 ep789 ep790 1083599513264 1099511627776 243679401 243441664 (ep796 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep798 := nat_lit 58808940698747552381828242286265992888375658468664297581503221808489370958714499158248585423674436045693318089843421280791611998335404962130134067838976

noncomputable def ep799 := nat_lit 1495322550399040784419355283626494329519667708093549445215377558311688463489449843662618815857177555772710955730243566617516213067140175522969484368281600

noncomputable def ep800 := nat_lit 2620750126276833616604463316160531307428294024857155261293814900449318461638152473497381574523645453135883096245565927272125336036501029488951296

noncomputable def ep801 := nat_lit 356640744245644978428579460907299633045751706797604211411639440151600130028470638417549674125410984301468919297906137090598799639760627150861850011238400

noncomputable def ep802 := nat_lit 136074352086312711382161330810010983986289761436512999514599357806363650177539935773298312243003157575316696971452164562193975389109755972590223077513625600

noncomputable def ep803 := BSN.cos_dyadic_bound_f 1083599513264 1099511627776 4 3 536870912 243679401 ep798 ep799 ep800 ep801 ep802 ep800 296579870 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1083599513264) (BSN.cosEvenQ 1099511627776) 0 3 ep798 ep799 ep800 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1083599513264) (BSN.cosOddQ 1099511627776) 0 3 ep801 ep802 ep800 rfl rfl rfl rfl) rfl rfl

noncomputable def ep804 := @Enclosure.Real.IsNear.sin_image qz120 qz397 Bool.false 1360567469 16777216 173 536870912 Bool.true 296579870 536870912 1 121720832 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 365224548965521194963 4503599627370496000 9521243711174849 29717000000000000000000 1360567469 16777216 173 536870912 (ep788 rfl) rfl) (Enclosure.sfrac_false_div 1360567469 16777216) (BSN.sin_reduce3 qz397 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep789) (@Nat.cast Real Real.instNatCast ep790)) 226375608064910080 72057594037927936 Bool.false 296579870 536870912 12 1000000000000000 243441664 121720832 (BSN.sin_reduce_arg_pos_rat_q3 1360567469 16777216 226375608064910080 72057594037927936 12 ep789 ep790 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 296579870 536870912 ep789 ep790 1083599513264 1099511627776 243679401 243441664 (ep803 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep805 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz394 qz116) (@HMul.hMul Real Real Real qz0 qz394 qz117) Bool.false 10369146327701 18014398509481984 1906669882675 1070667761012552237056 Bool.false 54975082732745 144115188075855872 5383991952527 4282671044050208948224 (@Enclosure.Real.IsNear.mulLit_ff qz394 qz116 370727 536870912 1 536870912 27969763 33554432 5272113 15954192891904 10369146327701 18014398509481984 1906669882675 1070667761012552237056 (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 370727 536870912 1 536870912 370727 536870912 1 536870912 (ep784 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 447516208 536870912 21594574848 65348374085238784 27969763 33554432 5272113 15954192891904 (ep797 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz394 qz117 370727 536870912 1 536870912 148289935 268435456 5272113 15954192891904 54975082732745 144115188075855872 5383991952527 4282671044050208948224 (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 370727 536870912 1 536870912 370727 536870912 1 536870912 (ep784 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz121 Bool.true 148289935 268435456 5272113 15954192891904 (@Enclosure.Real.IsNear.recentre' qz121 Bool.true 296579870 536870912 21594574848 65348374085238784 148289935 268435456 5272113 15954192891904 (ep804 rfl rfl) rfl)) rfl)

noncomputable def ep806 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216 59090192866999 720000000000 0 1 54975082732745 144115188075855872 5383991952527 4282671044050208948224 ep730

noncomputable def ep807 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 4561516003 480000000 0 1 Bool.false 59090192866999 720000000000 0 1 ep780

noncomputable def ep808 := @Enclosure.Complex.IsNear.im_isNear qz204 Bool.false 10369146327701 18014398509481984 1906669882675 1070667761012552237056 Bool.false 54975082732745 144115188075855872 5383991952527 4282671044050208948224

noncomputable def ep809 := nat_lit 13835058055282163712000000

noncomputable def ep810 := nat_lit 2055682101144100295147520000000

noncomputable def ep811 := nat_lit 612714856369986505562439299

noncomputable def ep812 := nat_lit 12970366926827028480000000000

noncomputable def ep813 := nat_lit 4506619644038564208373693

noncomputable def ep814 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215) 50153943930333057923647 ep809 24559165451475126789581 ep810 ep811 ep812 ep813

noncomputable def ep815 := nat_lit 30835231517161504427212800000000

noncomputable def ep816 := nat_lit 9127460664816564844965852223765377699847077888000000

noncomputable def ep817 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216 4561516003 480000000 0 1 54975082732745 144115188075855872 5383991952527 4282671044050208948224 50153943930333057923647

noncomputable def ep818 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215 59090192866999 720000000000 0 1 10369146327701 18014398509481984 1906669882675 1070667761012552237056 ep811

noncomputable abbrev qz398 := (@ep783 4282671044050208948224 (BSN.cpow_neg_s_sub_mk qz35 38999 1000 8 3 2097152 qz36 rfl EMRow07.d15) ep805)

noncomputable def ep819 := ep727 (@ep732 ep721 ep733 ep718 ep719 ep720 ep721 (@ep734 ep728 347892207290405797921 ep729 ep781 (ep782 qz398) rfl) (@ep806 ep719 ep731 ep721 ep807 (ep808 qz398) rfl) rfl rfl) (@ep814 ep815 ep816 ep723 ep724 76171986340792048597147 ep726 (@ep817 ep809 24559165451475126789581 ep810 ep781 (ep808 qz398) rfl) (@ep818 ep812 ep813 ep815 ep807 (ep782 qz398) rfl) rfl rfl)

noncomputable def ep820 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) ep723 ep724 76171986340792048597147 ep726 ep723 ep724 76171986340792048597147

noncomputable def ep821 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204) Bool.true ep718 ep719 ep720 ep721 Bool.false ep723 ep724 76171986340792048597147

noncomputable def ep822 := @ep689 78596767241317 123145302310912 287322143 123145302310912 (@ep690 1 458752 (ep691 (@ep692 131072 1 131072 (ep693 (@ep694 6132688004 1533172001 1000000 0 1 (ep698 rfl) (ep701 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep702 53 268435456 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (@ep703 106 536870912 15314377 268435456 53 268435456 (@ep708 15314324 15314430 268435456 (@ep713 ep714 ep715 ep716 ep717 ep704 ep705 ep706 ep707 (@ep722 ep721 ep709 ep710 ep711 ep707 (@ep725 ep726 ep819) (@ep725 ep726 ep819) rfl) (@ep820 ep726 ep712 ep714 ep715 ep716 (@ep821 ep726 ep819) (@ep821 ep726 ep819) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow07.d16 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))) Bool.false 81935678182501 123145302310912 272262288197 3324923162394624 := ep687 (ep688 ep822) rfl rfl

theorem EMRow07.d17 : @Eq Nat (Nat.pow 9 (Nat.succ (Nat.mul 2 3))) 4782969 := @Eq.refl Nat 4782969

noncomputable abbrev qz434 := (@HAdd.hAdd Complex Complex Complex qz436 qz442 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz399 := qz434

noncomputable abbrev qz227 := (@HDiv.hDiv Real Real Real qz257 (@Norm.norm Complex Complex.instNorm qz399) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz344) qz316))

noncomputable abbrev qz400 := (@HPow.hPow Complex Complex Complex qz424 (@Nat.cast Complex Complex.instNatCast 9) (@HSub.hSub Complex Complex Complex qz414 qz429 qz426))

noncomputable abbrev qz228 := qz400

noncomputable def ep823 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 9))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) 18811989 1073741824 96835 1073741824 72391935835353 123145302310912 196857483

noncomputable def ep824 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 9)) 123 8192 1 221184 152943 131072 741 131072 18811989 1073741824

noncomputable def ep825 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 9)) (Real.sqrt (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 9)) (Complex.re (zetaApproximant qz143 1 9))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 9)) (Complex.im (zetaApproximant qz143 1 9))))) Bool.false 152943 131072 741 131072

noncomputable def ep826 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 9)) (Complex.re (zetaApproximant qz143 1 9))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 9)) (Complex.im (zetaApproximant qz143 1 9))))) Bool.false 152943 131072 741 131072

noncomputable def ep827 := nat_lit 4108317419793951384495886638468045737

noncomputable def ep828 := nat_lit 3017252632376307828002251603968000000

noncomputable def ep829 := nat_lit 246315893877433617437180677140100872255065916103801

noncomputable def ep830 := nat_lit 18682545521448023679604541874594239512137695232000000

noncomputable def ep831 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 9)) (Complex.re (zetaApproximant qz143 1 9))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 9)) (Complex.im (zetaApproximant qz143 1 9)))) ep827 ep828 ep829 ep830 76101 76842

noncomputable def ep832 := nat_lit 2296917218494358020912191593878180566875329

noncomputable def ep833 := nat_lit 1692451014706943251557483819897496535040000

noncomputable def ep834 := nat_lit 1860045068388367829065332871515291861493398603087461

noncomputable def ep835 := nat_lit 149460364171584189436836334996753916097101561856000000

noncomputable def ep836 := nat_lit 753879929437685627901290573778790816989961

noncomputable def ep837 := nat_lit 169245101470694325155748381989749653504000000

noncomputable def ep838 := nat_lit 12275786959011234492456949511723901838569858415883

noncomputable def ep839 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 9)) (Complex.re (zetaApproximant qz143 1 9))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 9)) (Complex.im (zetaApproximant qz143 1 9))) ep832 ep833 ep834 ep835 ep836 ep837 ep838

noncomputable def ep840 := nat_lit 16606707130176021048537370555194879566344617984000000

noncomputable def ep841 := nat_lit 390017892565406601096619853609768145937918669479849693041282007023782697475967549440000

noncomputable def ep842 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz143 1 9)) (Complex.re (zetaApproximant qz143 1 9)) 1515558385049668095073 1300942356412052275200 ep463 ep464 1515558385049668095073 1300942356412052275200 ep463 ep464 ep832

noncomputable def ep843 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz143 1 9)) (Complex.im (zetaApproximant qz143 1 9)) 868262592444063334531 13009423564120522752000 ep575 ep464 868262592444063334531 13009423564120522752000 ep575 ep464 ep836

noncomputable def ep844 := @ep823 123145302310912 80046857299217445027840 74549445229785 123145302310912 11302669963 123145302310912 (@ep824 96835 1073741824 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz205)) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow07.d12 EMRow07.d13 rfl) (ep667 rfl)) (ep825 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz143 1 9)) (@ep826 152943 131072 741 131072 (@ep831 65536 (@ep839 ep840 ep841 ep827 ep828 ep829 ep830 (@ep842 ep833 ep834 ep835 ep650 ep650 rfl) (@ep843 ep837 ep838 ep840 ep656 ep656 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz229 := (@Norm.norm Complex Complex.instNorm qz399)

noncomputable def ep845 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz229 qz389) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) Bool.false 72391935835353 123145302310912 196857483 123145302310912 (BSN.zrb_shape_eq qz229 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) qz145 3)

noncomputable def ep846 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz229 qz389) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) 5571653 458752 1 458752 12992901 268435456 33 268435456

noncomputable def ep847 := @Enclosure.Real.IsNear.mulLit_ff qz229 qz389 5571653 131072 1 131072 2 7 0 1 5571653 458752

noncomputable abbrev qz401 := (Complex.re qz434)

noncomputable abbrev qz402 := (Complex.im qz434)

noncomputable abbrev qz230 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz254 qz401 qz401) (@HMul.hMul Real Real Real qz254 qz402 qz402))

noncomputable abbrev qz231 := qz399

noncomputable def ep848 := @Enclosure.Real.IsNear.of_eq qz229 (Real.sqrt qz230) Bool.false 5571653 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz231)

noncomputable def ep849 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz230) Bool.false 5571653 131072 1 131072 5571653

noncomputable def ep850 := @Enclosure.Real.IsNear.sqrt_image qz230 56467453 31250 0 1 2785826 2785827 65536

noncomputable abbrev qz232 := (@HMul.hMul Real Real Real qz254 qz401 qz401)

noncomputable abbrev qz233 := (@HMul.hMul Real Real Real qz254 qz402 qz402)

noncomputable def ep851 := @Enclosure.Real.IsNear.addLit_ff qz232 qz233 49 4 0 1 112169281 62500 0 1

noncomputable abbrev qz234 := qz401

noncomputable def ep852 := @Enclosure.Real.IsNear.mulLit_ff qz234 qz234 7 2 0 1 7 2 0 1 49 4

noncomputable def ep853 := @Enclosure.Complex.IsNear.of_eq qz231 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz145) Bool.false 7 2 0 1 Bool.false 42364 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 42364 1000 3 qz146)

noncomputable abbrev qz235 := (ep853 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz346 Bool.false 7 2 0 1 Bool.false 42364 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz348))

noncomputable def ep854 := @ep852 0 1 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 7 2 0 1 Bool.false 42364 1000 0 1 qz235)

noncomputable def ep855 := ep854 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 7 2 0 1 Bool.false 42364 1000 0 1 qz235)

noncomputable abbrev qz236 := qz402

noncomputable def ep856 := @Enclosure.Real.IsNear.mulLit_ff qz236 qz236 42364 1000 0 1 42364 1000 0 1 112169281 62500

noncomputable def ep857 := @ep856 0 1 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 7 2 0 1 Bool.false 42364 1000 0 1 qz235)

noncomputable def ep858 := ep857 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 7 2 0 1 Bool.false 42364 1000 0 1 qz235)

noncomputable def ep859 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Real.sqrt (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))))) Bool.false 12992901 268435456

noncomputable def ep860 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))))) Bool.false 51971604 1073741824

noncomputable def ep861 := nat_lit 218959863835878311247205302408090266700117213455677

noncomputable def ep862 := nat_lit 93461343453626897313548933925961728000000000000000000

noncomputable def ep863 := nat_lit 1887568190119976796675169958149805444334253454753515185851457299

noncomputable def ep864 := nat_lit 159880146410341000450261940064389793565110355561021440000000000000000000

noncomputable def ep865 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))) ep861 ep862 ep863 ep864

noncomputable def ep866 := nat_lit 13306705489469432172085375785052240639732148976601

noncomputable def ep867 := nat_lit 7476907476290151785083914714076938240000000000000000

noncomputable def ep868 := nat_lit 14307022325258889897046215559725955764838642379170179545247358171

noncomputable def ep869 := nat_lit 1598801464103410004502619400643897935651103555610214400000000000000000000

noncomputable def ep870 := nat_lit 105252090435020818192276210189874517406930702496329

noncomputable def ep871 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) ep866 ep867 ep868 ep869 ep870

noncomputable def ep872 := nat_lit 186922686907253794627097867851923456000000000000000000

noncomputable def ep873 := nat_lit 4568659575940878069705484021772098678503892168364972313267214819

noncomputable def ep874 := nat_lit 3274285285843904355488390406202332341418793550119189624073825973096185426656724212776960000000000000000

noncomputable def ep875 := nat_lit 3647835726765863037043301

noncomputable def ep876 := nat_lit 86469112845513523200000000

noncomputable def ep877 := nat_lit 134105680841504463162754653511

noncomputable def ep878 := nat_lit 1264437212400603940918394880000000000

noncomputable def ep879 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) ep875 ep876 ep877 ep878 ep875 ep876 ep877

noncomputable def ep880 := nat_lit 10259244145404709988852323

noncomputable def ep881 := nat_lit 432345564227567616000000000

noncomputable def ep882 := nat_lit 76133645553021388943845525597

noncomputable def ep883 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228) Bool.true ep875 ep876 ep877 ep878 Bool.false ep880 ep881 ep882

noncomputable def ep884 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228 Bool.true ep875 ep876 ep877 ep878 Bool.false ep880 ep881 ep882 ep878

noncomputable def ep885 := nat_lit 4443115249737631368015269

noncomputable def ep886 := nat_lit 842958141600402627278929920000000

noncomputable def ep887 := nat_lit 3823043890731082118202101

noncomputable def ep888 := nat_lit 127441007966898016110731750011

noncomputable abbrev qz237 := (Complex.re qz400)

noncomputable abbrev qz238 := (Complex.im qz400)

noncomputable def ep889 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238) 146006803304349234299 72057594037927936000000 ep885 ep886 ep887 ep876 ep888

noncomputable def ep890 := nat_lit 262854265916344371766162284131537949556736000000

noncomputable def ep891 := nat_lit 56197209440026841818595328

noncomputable def ep892 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237 168214859 15000000 0 1 13019670572415 72057594037927936 26413333971510991 ep891 146006803304349234299

noncomputable def ep893 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) 168214859 15000000 0 1 0 1 0 1 168214859

noncomputable def ep894 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 504644577 62500 0 1 168214859 15000000 0

noncomputable abbrev qz403 := (@HAdd.hAdd Complex Complex Complex qz416 qz428 qz427)

noncomputable abbrev qz239 := qz403

noncomputable def ep895 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) qz239) Bool.true 504644577 62500 0 1 Bool.true 592089357223 7812500 0 1

noncomputable abbrev qz240 := (Complex.re qz403)

noncomputable abbrev qz241 := (Complex.im qz403)

noncomputable def ep896 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz240) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz241) 56061203 12500 0 1 112169281 31250 0 1

noncomputable def ep897 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz240 56061203 31250 0 1 5 2 0 1 56061203 12500

noncomputable abbrev qz404 := (@HAdd.hAdd Complex Complex Complex qz416 qz428 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz242 := qz404

noncomputable def ep898 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz242) Bool.true 56061203 31250 0 1 Bool.false 10591 125 0 1

noncomputable abbrev qz243 := (Complex.re qz404)

noncomputable abbrev qz244 := (Complex.im qz404)

noncomputable def ep899 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz243) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz244) 3 4 0 1 112169281 62500 0 1

noncomputable def ep900 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz243 1 2 0 1 3 2 0 1 3 4

noncomputable def ep901 := @ep900 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep615)

noncomputable def ep902 := @Enclosure.Complex.IsNear.of_eq qz242 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz145) Bool.false 3 2 0 1 Bool.false 42364 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 42364 1000 1 qz146)

noncomputable abbrev qz245 := (ep902 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz346 Bool.false 3 2 0 1 Bool.false 42364 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz348))

noncomputable def ep903 := ep901 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 3 2 0 1 Bool.false 42364 1000 0 1 qz245)

noncomputable def ep904 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz244 42364 1000 0 1 42364 1000 0 1 112169281 62500

noncomputable def ep905 := @ep904 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep615)

noncomputable def ep906 := ep905 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 3 2 0 1 Bool.false 42364 1000 0 1 qz245)

noncomputable def ep907 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz242 Bool.true 56061203 31250 0 1 Bool.false 10591 125 0 1 (@ep899 448489624 56061203 31250 0 1 (ep903 rfl) (ep906 rfl) rfl rfl)

noncomputable def ep908 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz244) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz243) 10591 500 0 1 31773 500 0 1

noncomputable def ep909 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz244 1 2 0 1 42364 1000 0 1 10591 500

noncomputable def ep910 := @ep909 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep615)

noncomputable def ep911 := ep910 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 3 2 0 1 Bool.false 42364 1000 0 1 qz245)

noncomputable def ep912 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz243 42364 1000 0 1 3 2 0 1 31773 500

noncomputable def ep913 := @ep912 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 42364 1000 0 1 ep615)

noncomputable def ep914 := ep913 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 3 2 0 1 Bool.false 42364 1000 0 1 qz245)

noncomputable abbrev qz246 := (ep898 (BSN.ascPochhammer_succ_eval_c 1 2 qz344 rfl) (ep907 (@ep908 21182000 10591 125 0 1 (ep911 rfl) (ep914 rfl) rfl rfl)))

noncomputable def ep915 := @ep897 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 56061203 31250 0 1 Bool.false 10591 125 0 1 qz246)

noncomputable def ep916 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz145) Bool.false 5 2 0 1 Bool.false 42364 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 42364 1000 2 qz146)

noncomputable abbrev qz247 := (ep916 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz346 Bool.false 5 2 0 1 Bool.false 42364 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz348))

noncomputable def ep917 := ep915 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 5 2 0 1 Bool.false 42364 1000 0 1 qz247)

noncomputable def ep918 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz241 10591 125 0 1 42364 1000 0 1 112169281 31250

noncomputable def ep919 := @ep918 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 56061203 31250 0 1 Bool.false 10591 125 0 1 qz246)

noncomputable def ep920 := ep919 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 5 2 0 1 Bool.false 42364 1000 0 1 qz247)

noncomputable def ep921 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) qz239 Bool.true 504644577 62500 0 1 Bool.true 592089357223 7812500 0 1 (@ep896 3154028606250 504644577 62500 0 1 (ep917 rfl) (ep920 rfl) rfl rfl)

noncomputable def ep922 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz240) 593744200973 7812500 0 1 10591 50 0 1

noncomputable def ep923 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz241 56061203 31250 0 1 42364 1000 0 1 593744200973 7812500

noncomputable def ep924 := @ep923 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 56061203 31250 0 1 Bool.false 10591 125 0 1 qz246)

noncomputable def ep925 := ep924 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 5 2 0 1 Bool.false 42364 1000 0 1 qz247)

noncomputable def ep926 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz240 10591 125 0 1 5 2 0 1 10591 50

noncomputable def ep927 := @ep926 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 56061203 31250 0 1 Bool.false 10591 125 0 1 qz246)

noncomputable def ep928 := ep927 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 5 2 0 1 Bool.false 42364 1000 0 1 qz247)

noncomputable abbrev qz248 := (ep895 (BSN.ascPochhammer_succ_eval_c 2 3 qz344 rfl) (ep921 (@ep922 29604467861150 592089357223 7812500 0 1 (ep925 rfl) (ep928 rfl) rfl rfl)))

noncomputable def ep929 := @ep894 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep737) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 504644577 62500 0 1 Bool.true 592089357223 7812500 0 1 qz248)

noncomputable def ep930 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 592089357223 7812500 0 1 0 1 0

noncomputable def ep931 := @ep930 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep737) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 504644577 62500 0 1 Bool.true 592089357223 7812500 0 1 qz248)

noncomputable def ep932 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) 592089357223 5625000000 0 1 0 1 0 1 592089357223

noncomputable def ep933 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 592089357223 7812500 0 1 592089357223 5625000000 0

noncomputable def ep934 := @ep933 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep737) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 504644577 62500 0 1 Bool.true 592089357223 7812500 0 1 qz248)

noncomputable def ep935 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 504644577 62500 0 1 0 1 0

noncomputable def ep936 := @ep935 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep737) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 504644577 62500 0 1 Bool.true 592089357223 7812500 0 1 qz248)

noncomputable def ep937 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 168214859 15000000 0 1 Bool.false 592089357223 5625000000 0 1 (@ep893 168214859 15000000 0 1 (ep929 rfl) (ep931 rfl) rfl rfl) (@ep932 592089357223 5625000000 0 1 (ep934 rfl) (ep936 rfl) rfl rfl)

noncomputable def ep938 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 168214859 15000000 0 1 Bool.false 592089357223 5625000000 0 1 ep937

noncomputable def ep939 := nat_lit 224788837760107367274381312

noncomputable def ep940 := @Enclosure.Complex.IsNear.re_isNear qz228 Bool.false 13019670572415 72057594037927936 26413333971510991 ep891 Bool.false 484265235149025 1152921504606846976 215239484399142157 ep939

noncomputable abbrev qz405 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4782969)))

noncomputable def ep941 := @Enclosure.Complex.IsNear.of_eq qz228 (Complex.mk (@HMul.hMul Real Real Real qz0 qz405 qz191) (@HMul.hMul Real Real Real qz0 qz405 qz192)) Bool.false 13019670572415 72057594037927936 26413333971510991 ep891 Bool.false 484265235149025 1152921504606846976 215239484399142157

noncomputable abbrev qz406 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4782969))

noncomputable abbrev qz407 := (@Nat.cast Real Real.instNatCast 4782969)

noncomputable def ep942 := @Enclosure.Real.IsNear.inv_image qz406 2348273369089 1073741824 1 1073741824 245482 245483 536870912 (@Enclosure.Real.IsNear.of_eq qz406 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz407 qz87)) Bool.false 2348273369089 1073741824 1 1073741824 (BSN.sqrt_natCast_div_one 4782969) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz407 qz87)) Bool.false 2348273369089 1073741824 1 1073741824 2348273369089 1073741824 1 1073741824 (BSN.sqrt_enclosure 4782969 1 1174136684544 1174136684545 536870912 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep943 := nat_lit 48743309250000000000000000

noncomputable def ep944 := nat_lit 42500504340760369752440832

noncomputable def ep945 := nat_lit 19342813113834066795298816

noncomputable def ep946 := BSN.log_dyadic_bound 1 17 4 3 2534444745 536870912 194973237 2929319 15 63234285 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 1) (BSN.artanhQ 17) 0 3 2929319 2534444745 15 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep947 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz193 42364 1000 0 1 9895419781273317 4503599627370496 1000000584919711 194973237000000000000000 104802390903465700347 1125899906842624000 10591006194884659201 ep943 qz147 (BSN.isNear_log_sfrac 9 1 9895419781273317 4503599627370496 1000000584919711 194973237000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz379) Bool.false ep944 ep945 1000000584919711 194973237000000000000000 9895419781273317 4503599627370496 1000000584919711 194973237000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 63234285 536870912 24973259072661432 36028797018963968 194973237 1000000000000000 rfl rfl rfl rfl (ep946 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep948 := nat_lit 31431193299013864345567232

noncomputable def ep949 := nat_lit 77371252455336267181195264

noncomputable def ep950 := nat_lit 45034904444160016490646325882806751794902513141218183930183153504499285850839678818420872891363630625

noncomputable def ep951 := nat_lit 198427385752314841779073402044110610264839530770632232232545909413510936087367383754837115419531442913280

noncomputable def ep952 := nat_lit 405591193827292363357418367385919948569579573024281584793190665641474126880354018528785625390625

noncomputable def ep953 := nat_lit 117947902587057656145009227206184772735304136050548442408866213060229948175041352522691334776844590625

noncomputable def ep954 := nat_lit 3637835405459105432616345704142027854855391397461590924263341672581033828268402035505347116024743120076800

noncomputable def ep955 := BSN.sin_dyadic_bound_f 893328242995 2199023255552 3 2 1073741824 390327282 ep950 ep951 ep952 ep953 ep954 ep952 424296496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 893328242995) (BSN.sinEvenQ 2199023255552) 0 2 ep950 ep951 ep952 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 893328242995) (BSN.sinOddQ 2199023255552) 0 2 ep953 ep954 ep952 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz408 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 49973674251) (@Nat.cast Real Real.instNatCast 536870912))

noncomputable def ep956 := @Enclosure.Real.IsNear.cos_image qz194 qz408 Bool.false 49973674251 536870912 117 536870912 Bool.false 424296496 1073741824 1 194973237 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 104802390903465700347 1125899906842624000 10591006194884659201 ep943 49973674251 536870912 117 536870912 (ep947 rfl) rfl) (Enclosure.sfrac_false_div 49973674251 536870912) (BSN.cos_reduce3 qz408 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep948) (@Nat.cast Real Real.instNatCast ep949)) 226375608064910080 72057594037927936 Bool.false 424296496 1073741824 14 1000000000000000 389946474 194973237 (BSN.sin_reduce_arg_pos_rat_q3 49973674251 536870912 226375608064910080 72057594037927936 14 ep948 ep949 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 424296496 1073741824 ep948 ep949 893328242995 2199023255552 390327282 389946474 (ep955 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep957 := nat_lit 25019571620619487958076117676389255850478538224931446308583882253906555016745101723130942177702190625

noncomputable def ep958 := nat_lit 22047487305812760197674822449345623362759947863403581359171767712612326231929709306093012824392382545920

noncomputable def ep959 := nat_lit 75057903679470809289501638192432995711538475515648290362582060380388382101981544461355768961855790625

noncomputable def ep960 := nat_lit 992136928761574208895367010220553051324197653853161161162729547067554680436836918774185577097657214566400

noncomputable def ep961 := BSN.cos_dyadic_bound_f 893328242995 2199023255552 3 2 1073741824 390327282 ep957 ep958 ep952 ep959 ep960 ep952 986353885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 893328242995) (BSN.cosEvenQ 2199023255552) 0 2 ep957 ep958 ep952 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 893328242995) (BSN.cosOddQ 2199023255552) 0 2 ep959 ep960 ep952 rfl rfl rfl rfl) rfl rfl

noncomputable def ep962 := @Enclosure.Real.IsNear.sin_image qz194 qz408 Bool.false 49973674251 536870912 117 536870912 Bool.true 986353885 1073741824 1 194973237 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 104802390903465700347 1125899906842624000 10591006194884659201 ep943 49973674251 536870912 117 536870912 (ep947 rfl) rfl) (Enclosure.sfrac_false_div 49973674251 536870912) (BSN.sin_reduce3 qz408 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep948) (@Nat.cast Real Real.instNatCast ep949)) 226375608064910080 72057594037927936 Bool.false 986353885 1073741824 14 1000000000000000 389946474 194973237 (BSN.sin_reduce_arg_pos_rat_q3 49973674251 536870912 226375608064910080 72057594037927936 14 ep948 ep949 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 986353885 1073741824 ep948 ep949 893328242995 2199023255552 390327282 389946474 (ep961 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep963 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz405 qz191) (@HMul.hMul Real Real Real qz0 qz405 qz192) Bool.false 13019670572415 72057594037927936 26413333971510991 ep891 Bool.false 484265235149025 1152921504606846976 215239484399142157 ep939 (@Enclosure.Real.IsNear.mulLit_ff qz405 qz191 490965 1073741824 1 1073741824 26518531 67108864 23348739641 104675459563782144 13019670572415 72057594037927936 26413333971510991 ep891 (@Enclosure.Real.IsNear.recentre' qz405 Bool.false 490965 1073741824 1 1073741824 490965 1073741824 1 1073741824 (ep942 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz191 Bool.false 424296496 1073741824 23348739641 104675459563782144 26518531 67108864 23348739641 104675459563782144 (ep956 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz405 qz192 490965 1073741824 1 1073741824 986353885 1073741824 23348739641 104675459563782144 484265235149025 1152921504606846976 215239484399142157 ep939 (@Enclosure.Real.IsNear.recentre' qz405 Bool.false 490965 1073741824 1 1073741824 490965 1073741824 1 1073741824 (ep942 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz195 Bool.true 986353885 1073741824 23348739641 104675459563782144 (@Enclosure.Real.IsNear.recentre' qz195 Bool.true 986353885 1073741824 23348739641 104675459563782144 986353885 1073741824 23348739641 104675459563782144 (ep962 rfl rfl) rfl)) rfl)

noncomputable def ep964 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238 592089357223 5625000000 0 1 484265235149025 1152921504606846976 215239484399142157 ep939 ep887

noncomputable def ep965 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 168214859 15000000 0 1 Bool.false 592089357223 5625000000 0 1 ep937

noncomputable def ep966 := @Enclosure.Complex.IsNear.im_isNear qz228 Bool.false 13019670572415 72057594037927936 26413333971510991 ep891 Bool.false 484265235149025 1152921504606846976 215239484399142157 ep939

noncomputable def ep967 := nat_lit 36206479519434397660710863

noncomputable def ep968 := nat_lit 3371832566401610509115719680000000

noncomputable def ep969 := nat_lit 27021597764222976000000000

noncomputable def ep970 := nat_lit 15639053933308372455269737993

noncomputable def ep971 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237) 1086141443322601124833 230584300921369395200000 ep967 ep968 513920558698427054986903 ep969 ep970

noncomputable def ep972 := nat_lit 316109303100150985229598720000000000

noncomputable def ep973 := nat_lit 147851289953112302683949950249322724039065600000

noncomputable def ep974 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238 168214859 15000000 0 1 484265235149025 1152921504606846976 215239484399142157 ep939 1086141443322601124833

noncomputable def ep975 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237 592089357223 5625000000 0 1 13019670572415 72057594037927936 26413333971510991 ep891 513920558698427054986903

noncomputable abbrev qz409 := (@ep941 ep939 (BSN.cpow_neg_s_sub_mk qz145 42364 1000 9 3 4782969 qz146 rfl EMRow07.d17) ep963)

noncomputable def ep976 := ep884 (@ep889 ep878 ep890 ep875 ep876 ep877 ep878 (@ep892 72057594037927936000000 ep885 ep886 ep938 (ep940 qz409) rfl) (@ep964 ep876 ep888 ep878 ep965 (ep966 qz409) rfl) rfl rfl) (@ep971 ep972 ep973 ep880 ep881 ep882 ep878 (@ep974 230584300921369395200000 ep967 ep968 ep938 (ep966 qz409) rfl) (@ep975 ep969 ep970 ep972 ep965 (ep940 qz409) rfl) rfl rfl)

noncomputable def ep977 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) ep880 ep881 ep882 ep878 ep880 ep881 ep882

noncomputable def ep978 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228) Bool.true ep875 ep876 ep877 ep878 Bool.false ep880 ep881 ep882

noncomputable def ep979 := @ep846 72391935835353 123145302310912 196857483 123145302310912 (@ep847 1 458752 (ep848 (@ep849 131072 1 131072 (ep850 (@ep851 451739624 56467453 31250 0 1 (ep855 rfl) (ep858 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep859 33 268435456 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (@ep860 132 1073741824 12992901 268435456 33 268435456 (@ep865 25985736 25985868 536870912 (@ep871 ep872 ep873 ep869 ep874 ep861 ep862 ep863 ep864 (@ep879 ep878 ep866 ep867 ep868 ep869 (@ep883 ep878 ep976) (@ep883 ep878 ep976) rfl) (@ep977 ep878 ep870 ep872 ep873 ep869 (@ep978 ep878 ep976) (@ep978 ep878 ep976) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow07.d18 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 9))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))) Bool.false 74549445229785 123145302310912 11302669963 123145302310912 := ep844 (ep845 ep979) rfl rfl

noncomputable def EMRow07.d19 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz410 := (EMRow07.d3 qz418 qz430 (@Enclosure.dec_le_dec qz418 qz430 38999 1000 42364 1000 (@Eq.refl Real qz418) (@Eq.refl Real qz430) rfl rfl rfl) 8 9 1 1)

noncomputable abbrev qz249 := qz410

noncomputable def ep980 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz249 (@Enclosure.dec_nonneg qz35 38999 1000 qz36) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 8 rfl)

noncomputable abbrev qz250 := (Zeta.Certificates.ZIntervalEM.fstVal qz410)

noncomputable def ep981 := @Enclosure.Real.IsNear.neg_val qz250 ep38 ep39

noncomputable def ep982 := @Enclosure.Real.IsNear.of_eq qz250 (hardyZApproximantEM 1 8 qz35) Bool.true

noncomputable abbrev qz251 := (Zeta.Certificates.ZIntervalEM.sndVal qz410)

noncomputable def ep983 := BSN.mul_neg_of_neg_pos_r qz250 qz251 (@ep981 ep40 ep41 (@ep982 ep38 ep39 ep40 ep41 (@Eq.refl Real (hardyZApproximantEM 1 8 qz35)) EMRow07.d8) rfl rfl rfl)

noncomputable def ep984 := @Enclosure.Real.IsNear.pos_val qz251 ep447 ep448

noncomputable def ep985 := @Enclosure.Real.IsNear.of_eq qz251 (hardyZApproximantEM 1 9 qz145) Bool.false

noncomputable def ep986 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz250) (BSN.hardyZErrorBoundStrong 1 8 qz35)

noncomputable def ep987 := @Enclosure.norm_gt_of_isNear qz250 (BSN.hardyZErrorBoundStrong 1 8 qz35) Bool.true

noncomputable def ep988 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 8 qz35) (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))) Bool.false 81935678182501 123145302310912 272262288197 3324923162394624 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))))

noncomputable def ep989 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz251) (BSN.hardyZErrorBoundStrong 1 9 qz145)

noncomputable def ep990 := @Enclosure.norm_gt_of_isNear qz251 (BSN.hardyZErrorBoundStrong 1 9 qz145) Bool.false

noncomputable def ep991 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 9 qz145) (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 9))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))) Bool.false 74549445229785 123145302310912 11302669963 123145302310912 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz54 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 9))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz14 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))))

noncomputable def ep992 := @List.cons EMRow07.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz249 (ep980 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 9 rfl) (ep983 (@ep984 ep449 ep450 (@ep985 ep447 ep448 ep449 ep450 (@Eq.refl Real (hardyZApproximantEM 1 9 qz145)) EMRow07.d11) rfl rfl rfl)) (ep986 (hardyZErrorBoundEM 1 8 qz35) (BSN.hardyZErrorBoundEM_le_strong 1 8 qz35 rfl) (@ep987 Bool.false ep38 ep39 ep40 ep41 81935678182501 123145302310912 272262288197 3324923162394624 (@ep982 ep38 ep39 ep40 ep41 (@Eq.refl Real (hardyZApproximantEM 1 8 qz35)) EMRow07.d8) (ep988 EMRow07.d16) rfl rfl rfl rfl rfl)) (ep989 (hardyZErrorBoundEM 1 9 qz145) (BSN.hardyZErrorBoundEM_le_strong 1 9 qz145 rfl) (@ep990 Bool.false ep447 ep448 ep449 ep450 74549445229785 123145302310912 11302669963 123145302310912 (@ep985 ep447 ep448 ep449 ep450 (@Eq.refl Real (hardyZApproximantEM 1 9 qz145)) EMRow07.d11) (ep991 EMRow07.d18) rfl rfl rfl rfl rfl)))) (@List.nil EMRow07.d0)

noncomputable abbrev qz411 := (@Enclosure.dec_le_dec qz418 qz430 38999 1000 42364 1000 (@Eq.refl Real qz418) (@Eq.refl Real qz430) rfl rfl rfl)

noncomputable abbrev qz252 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep992 (@List.IsChain.singleton EMRow07.d1 EMRow07.d19 (EMRow07.d2 qz264 qz346 qz411))))

noncomputable abbrev qz412 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep993 := And (@Eq (Option Real) (@Option.map qz412 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz412 qz252)) (@Option.some Real qz35))

noncomputable def ep994 := ep993 (@Eq (Option Real) (@Option.map qz412 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz412 qz252)) (@Option.some Real qz145))

noncomputable def ep995 := @And.intro (@Eq Nat (@List.length qz412 qz252) 1) ep994

noncomputable def ep996 := @And.intro (@Eq (Option Real) (@Option.map qz412 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz412 qz252)) (@Option.some Real qz35))

noncomputable def ep997 := @ep996 (@Eq (Option Real) (@Option.map qz412 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz412 qz252)) (@Option.some Real qz145))

noncomputable abbrev qz253 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep992 (@List.IsChain.singleton EMRow07.d1 EMRow07.d19 (EMRow07.d2 qz264 qz346 qz411)))

theorem EMRow07.d20 : Zeta.Certificates.BatchSpec 1 38999 1000 42364 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz412 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz412 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz412 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz35)) (@Eq (Option Real) (@Option.map qz412 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz412 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz145)))) qz253 (ep995 (@Eq.refl Nat 1) (ep997 (@Eq.refl (Option Real) (@Option.some Real qz35)) (@Eq.refl (Option Real) (@Option.some Real qz145))))

theorem solution : Zeta.Certificates.BatchSpec 1 38999 1000 42364 1000 := EMRow07.d20
#print axioms solution
#check solution
