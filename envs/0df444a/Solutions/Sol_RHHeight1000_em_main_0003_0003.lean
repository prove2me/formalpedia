-- Prove2me | solution 1 for RHHeight1000.em_main_0003_0003
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:42:50.327278+00:00
-- url     : https://prove2.me/submissions/60a4f35f-6ff1-40d3-baef-9e1ab749a2d2

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow03.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow03.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow03.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow03.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow03.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz250 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz250

noncomputable abbrev qz251 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz1 := qz251

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz252 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138516661214455 2251799813685248 125000000011111 5555500000000000000 4138516661214455 2251799813685248 125000000011111 5555500000000000000 120446 65536

noncomputable abbrev qz253 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 65536 qz253 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 779317518150410741488063439345657628452599855445271348474342368876423347582876053728679783827237610085654588674605917415063316248867402488514697634436426745

noncomputable def ep10 := nat_lit 13198325246229587668616048586507268161410801335203869857947191811663857046415771104290097871102374067703089877156867761119753226876438075596795543285583799

noncomputable def ep11 := nat_lit 13338205139369261376383149914767634013226508915861991492218067381232119098362059104733250767410551174650894954010182016771344050520336484956804919489535

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 4 3 ep9 131072 44444 ep10 ep11 59189 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 3 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz254 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz254

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138516661214455 2251799813685248 125000000011111 5555500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000088888 44444000000000000000 4138516661214455 2251799813685248 125000000011111 5555500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 59189 131072 24973259072661432 36028797018963968 44444 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 779317518150412560342812906055656980396982394702499187106382620393032652998517540933158707129341055012778793601285942846917973645097155238594697634436426745

noncomputable def ep18 := nat_lit 13198325246229655554962711811363413523213721429909419700721697472804734044169853548961061453892255410264786862895235075217650796661500958924795543285583799

noncomputable def ep19 := nat_lit 13338205139369401582665284895604560799810298653799657073142644093199656832454717421805370366589019475922075211274104314270069372987910244956804919489535

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 4 3 ep17 131072 44444 ep18 ep19 59189 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 3 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138516661214455 2251799813685248 125000000011111 5555500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000088888 44444000000000000000 4138516661214455 2251799813685248 125000000011111 5555500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 59189 131072 24973259072661432 36028797018963968 44444 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz255 := (Real.log (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz3 := qz255

theorem EMRow03.d4 : Enclosure.Real.IsNear qz3 Bool.false 60223 32768 3 65536 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz252) Bool.false 60223 32768 3 65536 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz252) Bool.false 120446 65536 3 65536 60223 32768 3 65536 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 150042 131072 1 44444 150042 131072 1 44444 75021 65536 2 65536 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 5456220599384213465248909714772227496572670538165976141063262914812807742611017753801422503639530882087556452122005170047444298375835020188444492540969863625638808382453421118235702266947370928498132967594635949979551089348001357731941995137847266570621617494261809398531128871567535833923098076891483476912075228072418610430965163137427706923427310178652894498746239459018086669257415154730407592571637957767157504839263249849478535520334507104454135585522664276476675

noncomputable def ep28 := nat_lit 583201912334273870627228188254822588827079241605343036411752047433839590517388190714780374919746279700129906501257101384229175562492847525225536391462542197025353003914524118772974087630067522636400444148635637549655768907025719966434833632093412247469427754039812435067522613541620617101084764807513402584784781490076808276521160080078978009740617112077674385114356333461540984478969922738031393369686631450339262287925718320742111081121726382582016608811398564907105

noncomputable def ep29 := nat_lit 2006268627360805445673839316848610509641534779303135707206598861506426804997221642604762844037348942607248852390277353874343091902420975230792155995982437872051629609224882022549487822374001366578458875613104959699164386313425243185530298109514065278868815165519648262204211929774735225023360668387821809970420335957473972782118680523137645713941929429588852958886338507735711181009301082096313539911189247153419366938656533848809858580689548163599238034961919825

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 10 9 ep27 131072 44444 ep28 ep29 150042 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 9 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 5456220599384260892400251500854699790811159195150212163211869656216336849990273498858157048596616978904240776489460003685239051624059887013466241201881443704542959173524008982544253046253151867013374679201187657749749224297051088632484873343955402287279851789208893474071824987110190207053471018354491495133306616646837230249901879422821128116650397962087630806812522581253210958036113071268120219429850657911869289056672761916619783759890108169949892385522664276476675

noncomputable def ep34 := nat_lit 583201912334279575053067226115417021307550325332234501953544426829928714668898700518418107620762577859683234776628347658361181262145210140271013263714562720079188253110303208819702903278206870150494721073991877864419341163488949363940583288588224434829960190109694548513088121652843287215458036179968684293644459891198769761601084092249455692877745995219003758983943549453190712470220270279351626860119698313725888367584660500821040083453648022042061408811398564907105

noncomputable def ep35 := nat_lit 2006268627360839170887858856494478835319319717359667041823756329478526322484078784125879825811686186445537802910004300367040714583746383402724632880452479311196631191501299191497899488881639138562974769996989848045902383299749709271247360054208480548633525642122514778503225872819822968825602771791453574137145372948950799520945900351638147820910599315255916738483881817718250085827996954508077874524152655659774549924038927632065100609588052048399238034961919825

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 10 9 ep33 131072 44444 ep34 ep35 150042 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 9 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 75021 65536 2 65536 75021 65536 1 32768 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 150042 131072 1 44444 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 150042 131072 44444 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 150042 131072 1 44444 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 150042 131072 44444 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow03.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 32768 := ep37

theorem EMRow03.d6 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow03.d7 : @Eq Nat (Nat.pow 5 1) 5 := @Eq.refl Nat 5

noncomputable def ep38 := nat_lit 2681950784884925507682931

noncomputable def ep39 := nat_lit 1860675696847002533888000

noncomputable def ep40 := nat_lit 9811309162488914102711563696863

noncomputable def ep41 := nat_lit 2986209911820831003183492890624000

noncomputable abbrev qz405 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz383 := qz405

noncomputable abbrev qz256 := qz383

noncomputable abbrev qz4 := qz256

noncomputable abbrev qz5 := (@instHSub Real Real.instSub)

noncomputable abbrev qz384 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz257 := qz384

noncomputable abbrev qz6 := qz257

noncomputable abbrev qz406 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz407 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz408 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz409 := (Enclosure.sfrac Bool.false 23170 1000)

noncomputable abbrev qz385 := (@HAdd.hAdd Complex Complex Complex qz406 (@HAdd.hAdd Complex Complex Complex qz406 qz407 (@HMul.hMul Complex Complex Complex qz405 Complex.I (@HDiv.hDiv Complex Complex Complex qz408 (↑qz409) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz258 := qz385

noncomputable abbrev qz7 := (Complex.Stirling.logGammaStirling 1 qz258)

noncomputable abbrev qz386 := qz406

noncomputable abbrev qz259 := qz386

noncomputable abbrev qz8 := qz259

noncomputable abbrev qz387 := (@HAdd.hAdd Complex Complex Complex qz406 qz407 (@HMul.hMul Complex Complex Complex qz405 Complex.I (@HDiv.hDiv Complex Complex Complex qz408 (↑qz409) (2 : Complex))))

noncomputable abbrev qz260 := qz387

noncomputable abbrev qz9 := qz260

noncomputable abbrev qz388 := qz409

noncomputable abbrev qz261 := qz388

noncomputable abbrev qz10 := (@HMul.hMul Real Real Real qz250 (@HDiv.hDiv Real Real Real qz254 qz261 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz410 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 23170 1000)))

noncomputable abbrev qz389 := qz410

noncomputable abbrev qz262 := qz389

noncomputable abbrev qz11 := qz262

noncomputable def ep42 := Complex.re (@HMul.hMul Complex Complex Complex qz4 (Complex.exp (@HMul.hMul Complex Complex Complex qz4 Complex.I ↑(@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10))) (zetaApproximant qz11 1 5))

noncomputable def ep43 := @Enclosure.Real.IsNear.of_eq ep42 (@HSub.hSub Real Real Real qz5 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 5))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 5))))

noncomputable def ep44 := nat_lit 1340996606858407861993367

noncomputable def ep45 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 5))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 5))) ep44

noncomputable def ep46 := nat_lit 4806595844755801205550063910561

noncomputable def ep47 := nat_lit 1493104955910415501591746445312000

noncomputable def ep48 := nat_lit 15239805613639360893187375057

noncomputable def ep49 := nat_lit 229708454755448538706422530048000

noncomputable def ep50 := nat_lit 2495120322787562079738266650623271684343332864000

noncomputable def ep51 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 5)) 131071 131072 227493

noncomputable def ep52 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) Bool.true 131071 131072 454986

noncomputable abbrev qz12 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz263 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 411745) qz12)

noncomputable def ep53 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) qz263 Bool.false 411745 131072 19

noncomputable def ep54 := nat_lit 13653196800000000000000000

noncomputable def ep55 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) Bool.false 3395395810672474843 1080863910568919040 7759276713317239850623 ep54

noncomputable def ep56 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10 88647403573630035527 5404319552844595200 2932241650817239850623 ep54 173823657 13107200

noncomputable def ep57 := nat_lit 222520659848231311310848000

noncomputable def ep58 := nat_lit 2275532800000000000000000

noncomputable def ep59 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 16114911553204186897 900719925474099200 741260243603838407369 ep58 Bool.false 88647403573630035527 5404319552844595200

noncomputable def ep60 := @Enclosure.Complex.IsNear.subLitP qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 11696487581773236297 900719925474099200 690060243587909677769 ep58 Bool.false 104928140209104627527 5404319552844595200 2317841650803586653823

noncomputable def ep61 := nat_lit 72575109666118877034983425847590912

noncomputable def ep62 := nat_lit 24952025856347637716863098879475712

noncomputable abbrev qz411 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz390 := qz411

noncomputable abbrev qz264 := (@HSub.hSub Complex Complex Complex qz384 qz385 qz390)

noncomputable abbrev qz265 := (Complex.log qz385)

noncomputable abbrev qz13 := (@HSub.hSub Complex Complex Complex qz257 (@HMul.hMul Complex Complex Complex qz256 qz264 qz265) qz258)

noncomputable abbrev qz266 := qz390

noncomputable abbrev qz14 := (@HMul.hMul Complex Complex Complex qz256 qz266 ↑qz255)

noncomputable abbrev qz391 := qz408

noncomputable abbrev qz267 := qz391

noncomputable abbrev qz15 := qz267

noncomputable abbrev qz16 := (@instHMul Nat instMulNat)

noncomputable abbrev qz392 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz268 := qz392

noncomputable abbrev qz17 := qz268

noncomputable abbrev qz18 := qz258

noncomputable abbrev qz269 := (@instHSub Int Int.instSub)

noncomputable abbrev qz19 := qz269

noncomputable abbrev qz270 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz20 := qz270

noncomputable abbrev qz271 := (@instHMul Int Int.instMul)

noncomputable abbrev qz21 := qz271

noncomputable abbrev qz272 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz22 := qz272

noncomputable def ep63 := @Enclosure.Complex.IsNear.of_eq qz7 (@HAdd.hAdd Complex Complex Complex qz8 (@HAdd.hAdd Complex Complex Complex qz8 qz13 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k)))))) Bool.true 11696487581773236297

noncomputable def ep64 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz8 qz13 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) Bool.true 11697700181903181897 900719925474099200

noncomputable def ep65 := nat_lit 3139751977611635973980946432

noncomputable def ep66 := nat_lit 1408321658213146802096019865600

noncomputable def ep67 := @ep64 1347724243217028637 4444400000000000000000 Bool.false 34988533823039693421 1801439850948198400 754250000184098159 4444400000000000000000 Bool.false 361383 268435456 3 268435456 Bool.true 279108137 40265318400 2317 40265318400 Bool.true ep65 11696487581773236297 900719925474099200 690060243587909677769 ep58 Bool.false ep66

noncomputable def ep68 := @Enclosure.Complex.IsNear.addLitP qz13 qz14 Bool.true 12525398791397607497 900719925474099200 1246000000052966137 4444400000000000000000

noncomputable def ep69 := @ep68 Bool.false 34988533823039693421 1801439850948198400 754250000184098159 4444400000000000000000 Bool.false 60223 65536 3 131072 Bool.false 0 1 0 1 Bool.true 766620479121206928801792 11697700181903181897 900719925474099200 1347724243217028637 4444400000000000000000 Bool.false 34988533823039693421 34988533823039693421 1801439850948198400

noncomputable abbrev qz23 := (@HMul.hMul Complex Complex Complex qz256 qz264 qz265)

noncomputable def ep70 := @Enclosure.Complex.IsNear.subLitP qz23 qz18 Bool.true 10498778959080884297 900719925474099200 1246000000052966137 4444400000000000000000 Bool.false 11171642899254914377

noncomputable def ep71 := @ep70 360287970189639680 754250000184098159 4444400000000000000000 Bool.false 9000 4000 0 1 Bool.false 46340 4000 0 1 Bool.true 50101595165590429988000 12525398791397607497 900719925474099200 1246000000052966137 4444400000000000000000 Bool.false 27990827058431754736800 34988533823039693421 1801439850948198400 754250000184098159 4444400000000000000000

noncomputable abbrev qz24 := qz264

noncomputable abbrev qz25 := qz265

noncomputable def ep72 := @Enclosure.Complex.IsNear.mul qz24 qz25 Bool.true 10498778959080884297 900719925474099200 1246000000052966137 4444400000000000000000 Bool.false 11171642899254914377 360287970189639680 754250000184098159

noncomputable abbrev qz26 := (Complex.re qz264)

noncomputable abbrev qz27 := (Complex.re qz265)

noncomputable abbrev qz28 := (Complex.im qz264)

noncomputable abbrev qz29 := (Complex.im qz265)

noncomputable def ep73 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz26 qz27) (@HMul.hMul Real Real Real qz0 qz28 qz29) 155622304837176135 36028797018963968 1750000000544439 88888000000000000000 1798667072501285959 112589990684262400

noncomputable def ep74 := nat_lit 47282297007961874392022988527501312

noncomputable def ep75 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz27 7000 4000 0 1 22231757833882305 9007199254740992 250000000077777 22222000000000000000

noncomputable def ep76 := @Enclosure.Complex.IsNear.re_isNear qz24 Bool.false 7000 4000 0 1 Bool.false 46340 4000 0 1

noncomputable abbrev qz273 := (Enclosure.sfrac Bool.false 46340 4000)

noncomputable abbrev qz30 := qz273

noncomputable def ep77 := @Enclosure.Complex.IsNear.of_eq qz24 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz30) Bool.false 7000 4000 0 1 Bool.false 46340 4000 0

noncomputable abbrev qz274 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz31 := (Complex.log (Complex.mk qz274 qz273))

noncomputable def ep78 := @Enclosure.Complex.IsNear.of_eq qz25 qz31 Bool.false 22231757833882305 9007199254740992 250000000077777 22222000000000000000 Bool.false 776291356280227 562949953421312 500000000011111 22222000000000000000

noncomputable def ep79 := BSN.log_dyadic_bound 180395600 4276395600 2 1 54862677983098080000 131072 44444 32542572499360000 32542572499360000 11064 4456791200 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 180395600) (BSN.artanhQ 4276395600) 0 1 32542572499360000 54862677983098080000 32542572499360000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz32 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz33 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz275 := (Real.log (Enclosure.sfrac Bool.false 2228395600 16000000))

noncomputable abbrev qz276 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep80 := @Enclosure.Real.IsNear.mulLit_ff qz32 qz275 1 2 0 1 22231757833882305 4503599627370496 250000000077777 11111000000000000000 22231757833882305 9007199254740992 250000000077777 22222000000000000000 qz33 (BSN.isNear_log_sfrac 2228395600 16000000 22231757833882305 4503599627370496 250000000077777 11111000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2228395600) qz276)) Bool.false 23311687702420971847680 4722366482869645213696 1000000000311108 44444000000000000000 22231757833882305 4503599627370496 250000000077777 11111000000000000000 (BSN.log_rat_reduce_isNear 2228395600 16000000 7 4456791200 4096000000 11064 131072 24973259072661432 36028797018963968 44444 1000000000000000 rfl rfl rfl rfl (ep79 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep81 := BSN.arctan_dyadic_bound_f 9000 46340 2 1 131072 44444 6561000000000000 23056539314496800000 6561000000000000 19683000000000000 32279155040295520000 19683000000000000 25143 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 46340) 0 1 6561000000000000 23056539314496800000 6561000000000000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.arctanOddP 9000) (BSN.arctanOddQ 46340) 0 1 19683000000000000 32279155040295520000 19683000000000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz250 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz35 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz277 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 46340)))

noncomputable def ep82 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz277 884279719003555 562949953421312 1 2000000000000000 25143 131072 1 44444 101750060650361913344 776291356280227 562949953421312 500000000011111 22222000000000000000 qz35 (ep81 rfl) rfl rfl

noncomputable abbrev qz36 := (Complex.mk qz274 qz273)

noncomputable abbrev qz37 := qz261

noncomputable abbrev qz278 := (@Eq.refl Real qz388)

noncomputable abbrev qz38 := qz278

noncomputable abbrev qz279 := (@Nat.cast Real Real.instNatCast 46340)

noncomputable abbrev qz280 := (@Nat.cast Real Real.instNatCast 9000)

noncomputable abbrev qz39 := (Real.arctan (@HDiv.hDiv Real Real Real qz254 qz279 qz280))

noncomputable def ep83 := @Enclosure.Complex.IsNear.re_isNear qz25 Bool.false 22231757833882305 9007199254740992 250000000077777 22222000000000000000 Bool.false 776291356280227 562949953421312 500000000011111 22222000000000000000 (ep78 (@congrArg Complex Complex qz18 qz36 Complex.log (BSN.w_shift_mk qz37 Bool.false 23170 1000 2 qz38 rfl)) (@Enclosure.Complex.IsNear.of_parts qz31 Bool.false 22231757833882305 9007199254740992 250000000077777 22222000000000000000 Bool.false 776291356280227 562949953421312 500000000011111 22222000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz31) (@HMul.hMul Real Real Real qz0 qz32 qz275) Bool.false 22231757833882305 9007199254740992 250000000077777 22222000000000000000 (Enclosure.clog_re_eq 9000 46340 4000 2228395600 16000000 rfl rfl rfl) (ep80 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz31) qz39 Bool.false 776291356280227 562949953421312 500000000011111 22222000000000000000 (Enclosure.clog_im_eq 9000 46340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz39 (@HSub.hSub Real Real Real qz5 qz34 qz277) Bool.false 776291356280227 562949953421312 500000000011111 22222000000000000000 (BSN.arctan_recip 46340 9000 rfl rfl) ep82))))

noncomputable def ep84 := @Enclosure.Real.IsNear.mulLit_ff qz28 qz29 46340 4000 0 1 776291356280227 562949953421312 500000000011111 22222000000000000000

noncomputable def ep85 := @Enclosure.Complex.IsNear.im_isNear qz24 Bool.false 7000 4000 0 1 Bool.false 46340 4000 0 1

noncomputable def ep86 := @Enclosure.Complex.IsNear.im_isNear qz25 Bool.false 22231757833882305 9007199254740992 250000000077777 22222000000000000000 Bool.false 776291356280227 562949953421312 500000000011111 22222000000000000000 (ep78 (@congrArg Complex Complex qz18 qz36 Complex.log (BSN.w_shift_mk qz37 Bool.false 23170 1000 2 qz38 rfl)) (@Enclosure.Complex.IsNear.of_parts qz31 Bool.false 22231757833882305 9007199254740992 250000000077777 22222000000000000000 Bool.false 776291356280227 562949953421312 500000000011111 22222000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz31) (@HMul.hMul Real Real Real qz0 qz32 qz275) Bool.false 22231757833882305 9007199254740992 250000000077777 22222000000000000000 (Enclosure.clog_re_eq 9000 46340 4000 2228395600 16000000 rfl rfl rfl) (ep80 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz31) qz39 Bool.false 776291356280227 562949953421312 500000000011111 22222000000000000000 (Enclosure.clog_im_eq 9000 46340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz39 (@HSub.hSub Real Real Real qz5 qz34 qz277) Bool.false 776291356280227 562949953421312 500000000011111 22222000000000000000 (BSN.arctan_recip 46340 9000 rfl rfl) ep82))))

noncomputable abbrev qz281 := (Enclosure.Real.IsNear.const Bool.false 46340 4000)

noncomputable abbrev qz40 := (@ep77 1 (BSN.w_sub_half_mk qz261 Bool.false 23170 1000 2 qz278 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz273 Bool.false 7000 4000 0 1 Bool.false 46340 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz281))

noncomputable def ep87 := @ep73 1158500000025744187 4444400000000000000000 ep74 10498778959080884297 900719925474099200 1246000000052966137 4444400000000000000000 (@ep75 155622304837176135 36028797018963968 1750000000544439 88888000000000000000 (ep76 qz40) ep83 rfl) (@ep84 1798667072501285959 112589990684262400 1158500000025744187 4444400000000000000000 (ep85 qz40) ep86 rfl) rfl

noncomputable def ep88 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz26 qz29) (@HMul.hMul Real Real Real qz0 qz28 qz27) 5434039493961589 2251799813685248 3500000000077777 88888000000000000000 10302196580221060137 360287970189639680

noncomputable def ep89 := nat_lit 25156303399100339986888243068010496

noncomputable def ep90 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz29 7000 4000 0 1 776291356280227 562949953421312 500000000011111 22222000000000000000

noncomputable def ep91 := @Enclosure.Real.IsNear.mulLit_ff qz28 qz27 46340 4000 0 1 22231757833882305 9007199254740992 250000000077777 22222000000000000000

noncomputable def ep92 := @ep88 579250000180209309 4444400000000000000000 ep89 11171642899254914377 360287970189639680 754250000184098159 4444400000000000000000 (@ep90 5434039493961589 2251799813685248 3500000000077777 88888000000000000000 (ep76 qz40) ep86 rfl) (@ep91 10302196580221060137 360287970189639680 579250000180209309 4444400000000000000000 (ep85 qz40) ep83 rfl) rfl

noncomputable def ep93 := @Enclosure.Complex.IsNear.of_eq qz18 qz36 Bool.false 9000 4000 0 1 Bool.false 46340 4000 0 1 (BSN.w_shift_mk qz37 Bool.false 23170 1000 2 qz38 rfl)

noncomputable abbrev qz282 := (ep93 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 46340 4000) Bool.false 9000 4000 0 1 Bool.false 46340 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 46340 4000)))

noncomputable abbrev qz41 := qz282

noncomputable def ep94 := ep71 (@ep72 4444400000000000000000 (ep87 rfl) (ep92 rfl)) qz41 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz42 := qz266

noncomputable abbrev qz43 := (Complex.im ↑qz255)

noncomputable def ep95 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz42) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz42) qz43) 60223 65536 3 131072 0 1 0 1 60223 60223

noncomputable def ep96 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz42) (Complex.re ↑qz3) 1 2 0 1 60223 32768 3 65536 60223 65536 3 131072

noncomputable abbrev qz283 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz284 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz44 := (@Enclosure.Complex.IsNear.of_eq qz266 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz283) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz283 Bool.false 1 2 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 2) qz284))

noncomputable def ep97 := ep96 (@Enclosure.Complex.IsNear.re_isNear qz42 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz44) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 60223 32768 3 65536 (Complex.ofReal_re qz3) EMRow03.d4)

noncomputable def ep98 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz42) qz43 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable abbrev qz45 := qz283

noncomputable abbrev qz46 := qz284

noncomputable def ep99 := ep98 (@Enclosure.Complex.IsNear.im_isNear qz42 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz44) (@Enclosure.Real.IsNear.of_eq qz43 qz45 Bool.false 0 1 0 1 (@Eq.trans Real qz43 (0 : Real) qz45 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz46)

noncomputable def ep100 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz42) qz43) (@HMul.hMul Real Real Real qz0 (Complex.im qz42) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep101 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz42) qz43 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep102 := ep101 (@Enclosure.Complex.IsNear.re_isNear qz42 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz44) (@Enclosure.Real.IsNear.of_eq qz43 qz45 Bool.false 0 1 0 1 (@Eq.trans Real qz43 (0 : Real) qz45 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz46)

noncomputable def ep103 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz42) (Complex.re ↑qz3) 0 1 0 1 60223 32768 3 65536 0 1 0 1

noncomputable def ep104 := ep103 (@Enclosure.Complex.IsNear.im_isNear qz42 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz44) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 60223 32768 3 65536 (Complex.ofReal_re qz3) EMRow03.d4)

noncomputable def ep105 := @ep69 754250000184098159 4444400000000000000000 (ep94 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz42 (↑qz3) Bool.false 60223 65536 3 131072 Bool.false 0 1 0 1 (@ep95 65536 3 131072 (ep97 rfl) (ep99 rfl) rfl rfl) (@ep100 1 0 1 (ep102 rfl) (ep104 rfl) rfl rfl))

noncomputable abbrev qz47 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz285 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz48 := (@HMul.hMul Complex Complex Complex qz256 (@HMul.hMul Complex Complex Complex qz256 (2 : Complex) qz285) (@HSub.hSub Complex Complex Complex qz257 (@HMul.hMul Complex Complex Complex qz256 (2 : Complex) qz285) (1 : Complex)))

noncomputable abbrev qz286 := (@HPow.hPow Complex Int Complex qz392 qz385 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz49 := qz286

noncomputable def ep106 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48) qz49)) Bool.false 361383 268435456 3 268435456

noncomputable def ep107 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48) qz49) Bool.false 0 1 0 1 Bool.false

noncomputable def ep108 := @ep107 0 1 0 1 Bool.false 361383 268435456 3 268435456 Bool.true 279108137 40265318400 2317 40265318400 Bool.false 361383 361383 268435456 3 268435456 Bool.true 279108137 279108137 40265318400 2317

noncomputable def ep109 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz45 qz45) Bool.false 0 1 0 1 Bool.false

noncomputable def ep110 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48) qz49 Bool.false 361383 268435456 3 268435456 Bool.true 279108137 40265318400 2317 40265318400

noncomputable abbrev qz50 := (Complex.re qz286)

noncomputable abbrev qz51 := (Complex.im qz286)

noncomputable def ep111 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz50) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz51) 361383 268435456 3 268435456 0 1 0

noncomputable def ep112 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz50 1 12 0 1 1084149 67108864 9 67108864 361383

noncomputable def ep113 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz45) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz287 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz45 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz46)

noncomputable def ep114 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep113 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz287)

noncomputable def ep115 := @Enclosure.Complex.IsNear.re_isNear qz49 Bool.false 1084149 67108864 9 67108864 Bool.true 279108137 3355443200 2317 3355443200

noncomputable abbrev qz393 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz288 := (@HPow.hPow Complex Nat Complex qz393 qz385 1)

noncomputable abbrev qz52 := (@Inv.inv Complex Complex.instInv qz288)

noncomputable def ep116 := @Enclosure.Complex.IsNear.of_eq qz49 qz52 Bool.false 1084149 67108864 9 67108864 Bool.true 279108137 3355443200 2317

noncomputable def ep117 := @Enclosure.Complex.IsNear.of_parts qz52 Bool.false 1084149 67108864 9 67108864 Bool.true 279108137 3355443200 2317

noncomputable abbrev qz53 := (Complex.re qz288)

noncomputable abbrev qz54 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz55 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz56 := qz288

noncomputable def ep118 := @Enclosure.Real.IsNear.mulLit_ff qz53 (@Inv.inv Real Real.instInv (@DFunLike.coe qz54 Complex (fun (x : Complex) => Real) qz55 Complex.normSq qz56)) 9000 4000 0 1 120461 16777216 1 16777216

noncomputable def ep119 := @Enclosure.Complex.IsNear.re_isNear qz56 Bool.false 9000 4000 0 1 Bool.false 46340 4000 0 1

noncomputable def ep120 := @Enclosure.Complex.IsNear.of_eq qz56 qz18 Bool.false 9000 4000 0 1 Bool.false 46340 4000 0

noncomputable def ep121 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz54 Complex (fun (x : Complex) => Real) qz55 Complex.normSq qz56)) Bool.false 120461 16777216 1 16777216 120461 16777216 1

noncomputable abbrev qz57 := (@instHAdd Real Real.instAdd)

noncomputable abbrev qz58 := (Complex.im qz288)

noncomputable def ep122 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz54 Complex (fun (x : Complex) => Real) qz55 Complex.normSq qz56) (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 qz53 qz53) (@HMul.hMul Real Real Real qz0 qz58 qz58)) Bool.false 5570989 40000 0 1

noncomputable def ep123 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz53 qz53) (@HMul.hMul Real Real Real qz0 qz58 qz58) 81 16 0 1 5368489 40000

noncomputable def ep124 := @Enclosure.Real.IsNear.mulLit_ff qz53 qz53 9000 4000 0 1 9000 4000 0 1

noncomputable def ep125 := @Enclosure.Real.IsNear.mulLit_ff qz58 qz58 46340 4000 0 1 46340 4000 0 1

noncomputable def ep126 := @Enclosure.Complex.IsNear.im_isNear qz56 Bool.false 9000 4000 0 1 Bool.false 46340 4000 0 1

noncomputable abbrev qz59 := (ep119 (@ep120 1 (BSN.pow_one_c qz258) qz282))

noncomputable abbrev qz60 := (ep126 (@ep120 1 (BSN.pow_one_c qz258) qz282))

noncomputable def ep127 := @ep123 0 1 89135824 5570989 40000 0 1 (@ep124 81 16 0 1 qz59 qz59 rfl) (@ep125 5368489 40000 0 1 qz60 qz60 rfl)

noncomputable def ep128 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz54 Complex (fun (x : Complex) => Real) qz55 Complex.normSq qz56) 5570989 40000 0 1 60230 60231 8388608 (ep122 (Enclosure.Complex.normSq_eq_mul_add_mul qz56) (ep127 rfl rfl)) rfl

noncomputable def ep129 := @Enclosure.Real.IsNear.of_eq (Complex.re qz52) (@HMul.hMul Real Real Real qz0 qz53 (@Inv.inv Real Real.instInv (@DFunLike.coe qz54 Complex (fun (x : Complex) => Real) qz55 Complex.normSq qz56))) Bool.false 1084149 67108864 9 67108864 (Enclosure.Complex.inv_re_eq_mul qz56) (@ep118 1084149 67108864 9 67108864 qz59 (@ep121 16777216 (ep128 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep130 := @Enclosure.Real.IsNear.of_eq (Complex.im qz52) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz58) (@Inv.inv Real Real.instInv (@DFunLike.coe qz54 Complex (fun (x : Complex) => Real) qz55 Complex.normSq qz56))) Bool.true 279108137 3355443200 2317 3355443200 (Enclosure.Complex.inv_im_eq_mul qz56)

noncomputable def ep131 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz58) (@Inv.inv Real Real.instInv (@DFunLike.coe qz54 Complex (fun (x : Complex) => Real) qz55 Complex.normSq qz56)) 46340 4000 0 1 120461 16777216 1

noncomputable def ep132 := @ep131 16777216 279108137 3355443200 2317 3355443200 (@Enclosure.Real.IsNear.neg qz58 Bool.false 46340 4000 0 1 qz60) (@ep121 16777216 (ep128 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep133 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz51 0 1 0 1 279108137 3355443200 2317 3355443200 0

noncomputable def ep134 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep113 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz287)

noncomputable def ep135 := @Enclosure.Complex.IsNear.im_isNear qz49 Bool.false 1084149 67108864 9 67108864 Bool.true 279108137 3355443200 2317 3355443200

noncomputable abbrev qz61 := (@ep116 3355443200 (BSN.zpow_one_sub_two_mul qz258 1 1 rfl rfl) (@ep117 3355443200 ep129 (ep130 ep132)))

noncomputable def ep136 := @ep111 1 361383 361383 268435456 3 268435456 (@ep112 268435456 3 268435456 ep114 (ep115 qz61) rfl) (@ep133 1 0 1 ep134 (ep135 qz61) rfl) rfl

noncomputable def ep137 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz51) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz50) 279108137 40265318400 2317 40265318400 0 1 0

noncomputable def ep138 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz51 1 12 0 1 279108137 3355443200 2317 3355443200 279108137

noncomputable def ep139 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz50 0 1 0 1 1084149 67108864 9 67108864 0

noncomputable def ep140 := @ep137 1 279108137 279108137 40265318400 2317 40265318400 (@ep138 40265318400 2317 40265318400 ep114 (ep135 qz61) rfl) (@ep139 1 0 1 ep134 (ep115 qz61) rfl) rfl

noncomputable abbrev qz62 := (@Enclosure.Complex.IsNear.mk qz283 qz283 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz284 qz284)

noncomputable def ep141 := @ep108 40265318400 (@ep109 0 1 0 1 (BSN.stirling_sum_base qz18) qz62) (ep110 (ep136 rfl) (ep140 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep142 := @ep67 104928140209104627527 5404319552844595200 2317841650803586653823 ep54 (ep105 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep106 Bool.true 279108137 40265318400 2317 40265318400 (BSN.stirling_sum_succ qz18 0 1 rfl) (ep141 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep143 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz37 2) Bool.false 22092119857154753 4503599627370496 250000000077777 11111000000000000000 Bool.false 847955033097635 281474976710656

noncomputable abbrev qz63 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz259 qz260 qz285))

noncomputable def ep144 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz37 2) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz37 1) qz63) Bool.false 22092119857154753 4503599627370496 250000000077777 11111000000000000000 Bool.false 847955033097635 281474976710656 500000000011111 11111000000000000000

noncomputable def ep145 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz37 1) qz63 Bool.false 22067105967622849 9007199254740992 250000000077777 22222000000000000000 Bool.false 872133551490467 562949953421312 500000000011111 22222000000000000000 Bool.false

noncomputable def ep146 := nat_lit 397976251026025923722694153469952

noncomputable def ep147 := nat_lit 954712492771361397131171594240

noncomputable abbrev qz64 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz259 qz260 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep148 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz37 1) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz37 0) qz64) Bool.false 22067105967622849 9007199254740992 250000000077777 22222000000000000000 Bool.false 872133551490467 562949953421312 500000000011111 22222000000000000000

noncomputable def ep149 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz37 0) qz64 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz289 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz30))

noncomputable def ep150 := @Enclosure.Complex.IsNear.of_eq qz64 qz289 Bool.false 22067105967622849 9007199254740992 250000000077777 22222000000000000000 Bool.false 872133551490467 562949953421312 500000000011111 22222000000000000000

noncomputable def ep151 := BSN.log_dyadic_bound 100395600 4196395600 2 1 52829208095098080000 131072 44444 10079276499360000 10079276499360000 6272 4296791200 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 100395600) (BSN.artanhQ 4196395600) 0 1 10079276499360000 52829208095098080000 10079276499360000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep152 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 2148395600 16000000)) 1 2 0 1 22067105967622849 4503599627370496 250000000077777 11111000000000000000 22067105967622849 9007199254740992 250000000077777 22222000000000000000 qz33 (BSN.isNear_log_sfrac 2148395600 16000000 22067105967622849 4503599627370496 250000000077777 11111000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2148395600) qz276)) Bool.false 23139037707106096513024 4722366482869645213696 1000000000311108 44444000000000000000 22067105967622849 4503599627370496 250000000077777 11111000000000000000 (BSN.log_rat_reduce_isNear 2148395600 16000000 7 4296791200 4096000000 6272 131072 24973259072661432 36028797018963968 44444 1000000000000000 rfl rfl rfl rfl (ep151 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep153 := BSN.arctan_dyadic_bound_f 1000 46340 1 0 131072 44444 0 1 1 0 1 1 2828 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 46340) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 46340) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz290 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable def ep154 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz290 qz279)) 884279719003555 562949953421312 1 2000000000000000 2828 131072 1 44444 114312288860958490624 872133551490467 562949953421312 500000000011111 22222000000000000000 qz35 (ep153 rfl) rfl rfl

noncomputable abbrev qz65 := (@HAdd.hAdd Complex Complex Complex qz259 qz260 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz291 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz30)

noncomputable def ep155 := @ep149 22067105967622849 9007199254740992 250000000077777 22222000000000000000 Bool.false 872133551490467 562949953421312 500000000011111 22222000000000000000 Bool.false 22067105967622849 22067105967622849 9007199254740992 250000000077777 22222000000000000000 Bool.false 872133551490467 872133551490467 562949953421312 500000000011111 22222000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz37 0) (Complex.mk qz45 qz45) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz37) qz62) (ep150 (@congrArg Complex Complex qz65 qz291 Complex.log (BSN.w_shift_mk qz37 Bool.false 23170 1000 0 qz38 rfl)) (@Enclosure.Complex.IsNear.of_parts qz289 Bool.false 22067105967622849 9007199254740992 250000000077777 22222000000000000000 Bool.false 872133551490467 562949953421312 500000000011111 22222000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz289) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 2148395600 16000000))) Bool.false 22067105967622849 9007199254740992 250000000077777 22222000000000000000 (Enclosure.clog_re_eq 1000 46340 4000 2148395600 16000000 rfl rfl rfl) (ep152 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz289) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz279 qz290)) Bool.false 872133551490467 562949953421312 500000000011111 22222000000000000000 (Enclosure.clog_im_eq 1000 46340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz279 qz290)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz290 qz279))) Bool.false 872133551490467 562949953421312 500000000011111 22222000000000000000 (BSN.arctan_recip 46340 1000 rfl rfl) ep154)))) rfl rfl

noncomputable abbrev qz292 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz30))

noncomputable def ep156 := @Enclosure.Complex.IsNear.of_eq qz63 qz292 Bool.false 22117133746686657 9007199254740992 250000000077777 22222000000000000000 Bool.false 823776514704803 562949953421312 500000000011111 22222000000000000000

noncomputable def ep157 := BSN.log_dyadic_bound 124395600 4220395600 2 1 53435217061498080000 131072 44444 15474265299360000 15474265299360000 7728 4344791200 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 124395600) (BSN.artanhQ 4220395600) 0 1 15474265299360000 53435217061498080000 15474265299360000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep158 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 2172395600 16000000)) 1 2 0 1 22117133746686657 4503599627370496 250000000077777 11111000000000000000 22117133746686657 9007199254740992 250000000077777 22222000000000000000 qz33 (BSN.isNear_log_sfrac 2172395600 16000000 22117133746686657 4503599627370496 250000000077777 11111000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2172395600) qz276)) Bool.false 23191495635565708050432 4722366482869645213696 1000000000311108 44444000000000000000 22117133746686657 4503599627370496 250000000077777 11111000000000000000 (BSN.log_rat_reduce_isNear 2172395600 16000000 7 4344791200 4096000000 7728 131072 24973259072661432 36028797018963968 44444 1000000000000000 rfl rfl rfl rfl (ep157 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep159 := BSN.arctan_dyadic_bound_f 5000 46340 1 0 131072 44444 0 1 1 0 1 1 14087 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 46340) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 46340) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz293 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep160 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz293 qz279)) 884279719003555 562949953421312 1 2000000000000000 14087 131072 1 44444 107974035335387938816 823776514704803 562949953421312 500000000011111 22222000000000000000 qz35 (ep159 rfl) rfl rfl

noncomputable abbrev qz66 := (@HAdd.hAdd Complex Complex Complex qz259 qz260 qz285)

noncomputable abbrev qz294 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz30)

noncomputable def ep161 := @ep145 22117133746686657 9007199254740992 250000000077777 22222000000000000000 Bool.false 823776514704803 562949953421312 500000000011111 22222000000000000000 Bool.false ep146 22092119857154753 4503599627370496 250000000077777 11111000000000000000 Bool.false ep147 847955033097635 281474976710656 500000000011111 11111000000000000000 (ep148 (BSN.log_sum_c_succ qz37 0 1 rfl) (ep155 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep156 (@congrArg Complex Complex qz66 qz294 Complex.log (BSN.w_shift_mk qz37 Bool.false 23170 1000 1 qz38 rfl)) (@Enclosure.Complex.IsNear.of_parts qz292 Bool.false 22117133746686657 9007199254740992 250000000077777 22222000000000000000 Bool.false 823776514704803 562949953421312 500000000011111 22222000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz292) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 2172395600 16000000))) Bool.false 22117133746686657 9007199254740992 250000000077777 22222000000000000000 (Enclosure.clog_re_eq 5000 46340 4000 2172395600 16000000 rfl rfl rfl) (ep158 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz292) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz279 qz293)) Bool.false 823776514704803 562949953421312 500000000011111 22222000000000000000 (Enclosure.clog_im_eq 5000 46340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz279 qz293)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz293 qz279))) Bool.false 823776514704803 562949953421312 500000000011111 22222000000000000000 (BSN.arctan_recip 46340 5000 rfl rfl) ep160)))) rfl rfl

noncomputable def ep162 := @ep60 ep54 Bool.false 22092119857154753 4503599627370496 250000000077777 11111000000000000000 Bool.false 847955033097635 281474976710656 500000000011111 11111000000000000000 Bool.true ep61 16114911553204186897 900719925474099200 741260243603838407369 ep58 Bool.false ep62 88647403573630035527 5404319552844595200 2932241650817239850623 ep54 (@ep63 900719925474099200 690060243587909677769 ep58 Bool.false 104928140209104627527 5404319552844595200 2317841650803586653823 ep54 (BSN.logGammaStirling_unfold 1 qz18) (ep142 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep143 500000000011111 11111000000000000000 (BSN.log_sum_c_eq qz37 2) (ep144 (BSN.log_sum_c_succ qz37 1 2 rfl) (ep161 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz67 := (@HDiv.hDiv Real Real Real qz254 qz261 (2 : Real))

noncomputable def ep163 := @Enclosure.Real.IsNear.mulLit_ff qz67 (Real.log Real.pi) 23170 2000 0 1 75021 65536 1 32768 173823657 13107200 2317 6553600 (@Enclosure.Real.IsNear.of_eq qz67 (Enclosure.sfrac Bool.false 23170 2000) Bool.false 23170 2000 0 1 (BSN.t_half_eq qz37 Bool.false 23170 1000 qz38) (Enclosure.Real.IsNear.const Bool.false 23170 2000)) EMRow03.d5 rfl

noncomputable def ep164 := @ep56 2317 6553600 ep57 3395395810672474843 1080863910568919040 7759276713317239850623 ep54 (@ep59 2932241650817239850623 ep54 (ep162 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep163 rfl rfl

noncomputable def ep165 := nat_lit 497051685528481738977894509570103180122032396889556143609829398013885025

noncomputable def ep166 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080

noncomputable def ep167 := nat_lit 998101209134563639911411158943643136761662872727595209826600207071841

noncomputable def ep168 := nat_lit 1300186060140758118096533811759599573336280251964421412447929165891582561

noncomputable def ep169 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800

noncomputable abbrev qz295 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz296 := (BSN.sinOddQ 268435456)

noncomputable def ep170 := BSN.sin_dyadic_bound_f 421596331 268435456 3 2 131072 44488 ep165 ep166 ep167 ep168 ep169 ep167 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 421596331) qz295 0 2 ep165 ep166 ep167 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 421596331) qz296 0 2 ep168 ep169 ep167 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz68 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep171 := @ep53 32768 Bool.true 131071 131072 1 22222 (@ep55 411745 131072 19 32768 ep164 rfl) (Enclosure.sfrac_false_div 411745 131072) (BSN.cos_reduce1 qz263 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29667204414009382010880) qz68) 226375608064910080 72057594037927936 Bool.false 131071 131072 0 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q1 411745 131072 226375608064910080 72057594037927936 0 29667204414009382010880 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131071 131072 29667204414009382010880 18889465931478580854784 421596331 268435456 44488 44444 (ep170 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz394 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz297 := qz394

noncomputable abbrev qz69 := qz297

noncomputable abbrev qz395 := (@Neg.neg Complex Complex.instNeg qz410)

noncomputable abbrev qz298 := qz395

noncomputable abbrev qz70 := qz298

noncomputable abbrev qz299 := (@HPow.hPow Complex Complex Complex qz394 (@Nat.cast Complex Complex.instNatCast 5) qz395)

noncomputable abbrev qz71 := qz299

noncomputable abbrev qz300 := (@Nat.cast Complex Complex.instNatCast 5)

noncomputable abbrev qz72 := (@HAdd.hAdd Complex Complex Complex qz259 (@HDiv.hDiv Complex Complex Complex qz267 qz300 (@HSub.hSub Complex Complex Complex qz257 qz262 (1 : Complex))) qz266)

noncomputable abbrev qz73 := (@instHSub Nat instSubNat)

noncomputable abbrev qz301 := qz393

noncomputable abbrev qz74 := qz301

noncomputable abbrev qz75 := qz300

noncomputable def ep172 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz11 1 5) (@HAdd.hAdd Complex Complex Complex qz8 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 5, @HPow.hPow Complex Complex Complex qz69 (@Nat.cast Complex Complex.instNatCast n) qz70) (@HMul.hMul Complex Complex Complex qz4 qz71 (@HAdd.hAdd Complex Complex Complex qz8 qz72 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) Bool.false 10231070235661647977 7097914492977152000 2375609836078221754073

noncomputable def ep173 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 5, @HPow.hPow Complex Complex Complex qz69 (@Nat.cast Complex Complex.instNatCast n) qz70) (@HMul.hMul Complex Complex Complex qz4 qz71 (@HAdd.hAdd Complex Complex Complex qz8 qz72 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) Bool.false 21732272689 17179869184 378349811341 190885526503424

noncomputable def ep174 := nat_lit 175768448260983163930718240768

noncomputable def ep175 := nat_lit 1570952115310007648274874368

noncomputable def ep176 := @ep173 Bool.true 281857371 1073741824 5867708777 2982586351616 Bool.false 1252316577383230977 7097914492977152000 343497161213635505073 1025244063109098766336000 Bool.false 2263343820196267593 14195828985954304000 52637008617064835843 157729855862938271744000 Bool.false ep174 10231070235661647977 7097914492977152000 2375609836078221754073 1025244063109098766336000 Bool.true ep175 1463063168628148407 14195828985954304000

noncomputable def ep177 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 5, @HPow.hPow Complex Complex Complex qz69 (@Nat.cast Complex Complex.instNatCast n) qz70) (BSN.headSumC qz11 5) Bool.false 21732272689 17179869184 378349811341 190885526503424 Bool.true 281857371 1073741824 5867708777

noncomputable abbrev qz76 := (BSN.headSumC qz262 4)

noncomputable abbrev qz77 := (@HPow.hPow Complex Complex Complex qz297 (@Nat.cast Complex Complex.instNatCast 4) qz298)

noncomputable def ep178 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz11 5) (@HAdd.hAdd Complex Complex Complex qz8 qz76 qz77) Bool.false 21732272689 17179869184 378349811341 190885526503424 Bool.true 281857371 1073741824 5867708777 2982586351616

noncomputable def ep179 := @Enclosure.Complex.IsNear.addLitP qz76 qz77 Bool.false 7593547817 8589934592 136228813347 95442763251712 Bool.false 1053089469 17179869184 269807730971 190885526503424 Bool.false

noncomputable abbrev qz78 := (BSN.headSumC qz262 3)

noncomputable abbrev qz396 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz302 := qz396

noncomputable abbrev qz79 := (@HPow.hPow Complex Complex Complex qz297 qz302 qz298)

noncomputable def ep180 := @Enclosure.Complex.IsNear.of_eq qz76 (@HAdd.hAdd Complex Complex Complex qz8 qz78 qz79) Bool.false 7593547817 8589934592 136228813347 95442763251712 Bool.false 1053089469 17179869184 269807730971 190885526503424

noncomputable def ep181 := @Enclosure.Complex.IsNear.addLitP qz78 qz79 Bool.false 2888833067 8589934592 75461022843 95442763251712 Bool.false 2095400997 8589934592 74596498155 95442763251712 Bool.false

noncomputable abbrev qz80 := (BSN.headSumC qz262 2)

noncomputable abbrev qz397 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz303 := qz397

noncomputable abbrev qz81 := (@HPow.hPow Complex Complex Complex qz297 qz303 qz298)

noncomputable def ep182 := @Enclosure.Complex.IsNear.of_eq qz78 (@HAdd.hAdd Complex Complex Complex qz8 qz80 qz81) Bool.false 2888833067 8589934592 75461022843 95442763251712 Bool.false 2095400997 8589934592 74596498155 95442763251712

noncomputable def ep183 := @Enclosure.Complex.IsNear.addLitP qz80 qz81 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep184 := @Enclosure.Complex.IsNear.of_eq qz80 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz45) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz11)

noncomputable abbrev qz82 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable abbrev qz304 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz83 := (@HMul.hMul Real Real Real qz250 qz261 qz304)

noncomputable abbrev qz84 := (Real.sin (@HMul.hMul Real Real Real qz250 qz261 qz304))

noncomputable def ep185 := @Enclosure.Complex.IsNear.of_eq qz81 (Complex.mk (@HMul.hMul Real Real Real qz0 qz82 (Real.cos qz83)) (@HMul.hMul Real Real Real qz0 qz82 (@Neg.neg Real Real.instNeg qz84))) Bool.true 5701101525 8589934592 75461022843 95442763251712 Bool.false 2095400997 8589934592 74596498155 95442763251712 (BSN.cpow_neg_s_mk qz37 23170 1000 2 qz38 rfl)

noncomputable abbrev qz85 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz86 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz305 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep186 := @Enclosure.Real.IsNear.inv_image qz85 185363 131072 1 131072 46340 46342 65536 (@Enclosure.Real.IsNear.of_eq qz85 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz86 qz305)) Bool.false 185363 131072 1 131072 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz86 qz305)) Bool.false 185363 131072 1 131072 185363 131072 1 131072 (BSN.sqrt_enclosure 2 1 92681 92682 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep187 := BSN.log_dyadic_bound 1 3 6 5 613814355 65536 22222 24381081 945 45426 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep188 := nat_lit 79910291795672425523980680845361

noncomputable def ep189 := nat_lit 124615124604835863084731911901282304

noncomputable def ep190 := nat_lit 1869226869072537946270978678519234560

noncomputable abbrev qz306 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz307 := (BSN.cosOddQ 268435456)

noncomputable def ep191 := BSN.cos_dyadic_bound_f 94547637 268435456 2 1 131072 44488 ep188 ep189 ep188 ep188 ep190 ep188 123025 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 94547637) qz306 0 1 ep188 ep189 ep188 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 94547637) qz307 0 1 ep188 ep190 ep188 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz87 := qz304

noncomputable abbrev qz308 := (Enclosure.Real.IsNear.const Bool.false 23170 1000)

noncomputable abbrev qz88 := qz308

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 131565) (@Nat.cast Real Real.instNatCast 8192))

noncomputable abbrev qz310 := (BSN.isNear_log_sfrac 2 1 45426 65536 1 22222 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 45426 65536 22222 rfl rfl rfl (ep187 rfl)))

noncomputable def ep192 := @Enclosure.Real.IsNear.cos_image qz83 qz309 Bool.false 131565 8192 69 65536 Bool.true 123025 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz83 Bool.false 52626021 3276800 2317 2222200 131565 8192 69 65536 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz87 23170 1000 0 1 45426 65536 1 22222 52626021 3276800 2317 2222200 qz88 qz310 rfl) rfl) (Enclosure.sfrac_false_div 131565 8192) (BSN.cos_reduce2 qz309 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 415824906522544046080) (@Nat.cast Real Real.instNatCast 1180591620717411303424)) 226375608064910080 72057594037927936 Bool.false 123025 131072 2 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q2 131565 8192 226375608064910080 72057594037927936 2 415824906522544046080 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 123025 131072 415824906522544046080 1180591620717411303424 94547637 268435456 44488 44444 (ep191 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep193 := nat_lit 623075623024179315423659559506411520

noncomputable def ep194 := nat_lit 4361529361169255207965616916544880640

noncomputable def ep195 := BSN.sin_dyadic_bound_f 94547637 268435456 2 1 131072 44488 ep188 ep193 ep188 ep188 ep194 ep188 45217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 94547637) qz295 0 1 ep188 ep193 ep188 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 94547637) qz296 0 1 ep188 ep194 ep188 rfl rfl rfl rfl) rfl rfl

noncomputable def ep196 := @Enclosure.Real.IsNear.sin_image qz83 qz309 Bool.false 131565 8192 69 65536 Bool.true 45217 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz83 Bool.false 52626021 3276800 2317 2222200 131565 8192 69 65536 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz87 23170 1000 0 1 45426 65536 1 22222 52626021 3276800 2317 2222200 qz88 qz310 rfl) rfl) (Enclosure.sfrac_false_div 131565 8192) (BSN.sin_reduce2 qz309 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 415824906522544046080) (@Nat.cast Real Real.instNatCast 1180591620717411303424)) 226375608064910080 72057594037927936 Bool.false 45217 131072 2 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q2 131565 8192 226375608064910080 72057594037927936 2 415824906522544046080 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 45217 131072 415824906522544046080 1180591620717411303424 94547637 268435456 44488 44444 (ep195 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz89 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) Bool.false 92682 131072 2 131072 46341 65536 1 65536 (ep186 rfl rfl) rfl)

noncomputable def ep197 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz82 (Real.cos qz83)) (@HMul.hMul Real Real Real qz0 qz82 (@Neg.neg Real Real.instNeg qz84)) Bool.true 5701101525 8589934592 75461022843 95442763251712 Bool.false 2095400997 8589934592 74596498155 95442763251712 (@Enclosure.Real.IsNear.mulLit_ft qz82 (Real.cos qz83) 46341 65536 1 65536 123025 131072 799427 728170496 5701101525 8589934592 75461022843 95442763251712 qz89 (@Enclosure.Real.IsNear.recentre' (Real.cos qz83) Bool.true 123025 131072 1598854 1456340992 123025 131072 799427 728170496 (ep192 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz82 (@Neg.neg Real Real.instNeg qz84) 46341 65536 1 65536 45217 131072 799427 728170496 2095400997 8589934592 74596498155 95442763251712 qz89 (@Enclosure.Real.IsNear.neg qz84 Bool.true 45217 131072 799427 728170496 (@Enclosure.Real.IsNear.recentre' qz84 Bool.true 45217 131072 1598854 1456340992 45217 131072 799427 728170496 (ep196 rfl rfl) rfl)) rfl)

noncomputable def ep198 := @ep183 5701101525 8589934592 75461022843 95442763251712 Bool.false 2095400997 8589934592 74596498155 95442763251712 Bool.false 2888833067 2888833067 8589934592 75461022843 95442763251712 Bool.false 2095400997 2095400997 8589934592 74596498155 95442763251712 (ep184 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz45 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz46)) (ep185 ep197) rfl rfl

noncomputable abbrev qz311 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz90 := (@Inv.inv Real Real.instInv (Real.sqrt qz311))

noncomputable abbrev qz312 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz91 := (@HMul.hMul Real Real Real qz250 qz261 qz312)

noncomputable abbrev qz92 := (Real.sin (@HMul.hMul Real Real Real qz250 qz261 qz312))

noncomputable def ep199 := @Enclosure.Complex.IsNear.of_eq qz79 (Complex.mk (@HMul.hMul Real Real Real qz0 qz90 (Real.cos qz91)) (@HMul.hMul Real Real Real qz0 qz90 (@Neg.neg Real Real.instNeg qz92))) Bool.false 2352357375 4294967296 7595973813 11930345406464 Bool.true 3137712525 17179869184 120614734661 190885526503424 (BSN.cpow_neg_s_mk qz37 23170 1000 3 qz38 rfl)

noncomputable abbrev qz93 := (Real.sqrt qz311)

noncomputable abbrev qz94 := qz311

noncomputable def ep200 := @Enclosure.Real.IsNear.inv_image qz93 227023 131072 1 131072 37837 37838 65536 (@Enclosure.Real.IsNear.of_eq qz93 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz94 qz305)) Bool.false 227023 131072 1 131072 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz94 qz305)) Bool.false 227023 131072 1 131072 227023 131072 1 131072 (BSN.sqrt_enclosure 3 1 113511 113512 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep201 := BSN.log_dyadic_bound 1 2 9 8 2258332876800 65536 22222 222698787165 2027025 71998 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1) (BSN.artanhQ 2) 0 8 222698787165 2258332876800 2027025 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep202 := nat_lit 55730073085343675209348507075441

noncomputable def ep203 := BSN.cos_dyadic_bound_f 86401723 268435456 2 1 131072 44488 ep202 ep189 ep202 ep202 ep190 ep202 124340 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 86401723) qz306 0 1 ep202 ep189 ep202 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 86401723) qz307 0 1 ep202 ep190 ep202 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz95 := qz312

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3336387) qz12)

noncomputable abbrev qz314 := (BSN.isNear_log_sfrac 3 1 71998 65536 1 22222 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 71998 65536 22222 rfl rfl rfl (ep201 rfl)))

noncomputable def ep204 := @Enclosure.Real.IsNear.cos_image qz91 qz313 Bool.false 3336387 131072 137 131072 Bool.false 124340 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz91 Bool.false 83409683 3276800 2317 2222200 3336387 131072 137 131072 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz95 23170 1000 0 1 71998 65536 1 22222 83409683 3276800 2317 2222200 qz88 qz314 rfl) rfl) (Enclosure.sfrac_false_div 3336387 131072) (BSN.cos_reduce0 qz313 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6079980794298241122304) qz68) 226375608064910080 72057594037927936 Bool.false 124340 131072 4 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q0 3336387 131072 226375608064910080 72057594037927936 4 6079980794298241122304 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 124340 131072 6079980794298241122304 18889465931478580854784 86401723 268435456 44488 44444 (ep203 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep205 := BSN.sin_dyadic_bound_f 86401723 268435456 2 1 131072 44488 ep202 ep193 ep202 ep202 ep194 ep202 41463 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 86401723) qz295 0 1 ep202 ep193 ep202 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 86401723) qz296 0 1 ep202 ep194 ep202 rfl rfl rfl rfl) rfl rfl

noncomputable def ep206 := @Enclosure.Real.IsNear.sin_image qz91 qz313 Bool.false 3336387 131072 137 131072 Bool.false 41463 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz91 Bool.false 83409683 3276800 2317 2222200 3336387 131072 137 131072 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz95 23170 1000 0 1 71998 65536 1 22222 83409683 3276800 2317 2222200 qz88 qz314 rfl) rfl) (Enclosure.sfrac_false_div 3336387 131072) (BSN.sin_reduce0 qz313 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6079980794298241122304) qz68) 226375608064910080 72057594037927936 Bool.false 41463 131072 4 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q0 3336387 131072 226375608064910080 72057594037927936 4 6079980794298241122304 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 41463 131072 6079980794298241122304 18889465931478580854784 86401723 268435456 44488 44444 (ep205 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz96 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz311)) Bool.false 75675 131072 1 131072 75675 131072 1 131072 (ep200 rfl rfl) rfl)

noncomputable def ep207 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz90 (Real.cos qz91)) (@HMul.hMul Real Real Real qz0 qz90 (@Neg.neg Real Real.instNeg qz92)) Bool.false 2352357375 4294967296 7595973813 11930345406464 Bool.true 3137712525 17179869184 120614734661 190885526503424 (@Enclosure.Real.IsNear.mulLit_ff qz90 (Real.cos qz91) 75675 131072 1 131072 31085 32768 1587743 1456340992 2352357375 4294967296 7595973813 11930345406464 qz96 (@Enclosure.Real.IsNear.recentre' (Real.cos qz91) Bool.false 124340 131072 3175486 2912681984 31085 32768 1587743 1456340992 (ep204 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz90 (@Neg.neg Real Real.instNeg qz92) 75675 131072 1 131072 41463 131072 1587743 1456340992 3137712525 17179869184 120614734661 190885526503424 qz96 (@Enclosure.Real.IsNear.neg qz92 Bool.false 41463 131072 1587743 1456340992 (@Enclosure.Real.IsNear.recentre' qz92 Bool.false 41463 131072 3175486 2912681984 41463 131072 1587743 1456340992 (ep206 rfl rfl) rfl)) rfl)

noncomputable def ep208 := @ep181 2352357375 4294967296 7595973813 11930345406464 Bool.true 3137712525 17179869184 120614734661 190885526503424 Bool.false 32614039534627192832 7593547817 8589934592 136228813347 95442763251712 Bool.false 9045969658234011648 1053089469 17179869184 269807730971 190885526503424 (ep182 (BSN.head_sum_c_succ qz11 2 3 rfl rfl) (ep198 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep199 ep207) rfl rfl

noncomputable abbrev qz97 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable abbrev qz315 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz98 := (@HMul.hMul Real Real Real qz250 qz261 qz315)

noncomputable abbrev qz99 := (Real.sin (@HMul.hMul Real Real Real qz250 qz261 qz315))

noncomputable def ep209 := @Enclosure.Complex.IsNear.of_eq qz77 (Complex.mk (@HMul.hMul Real Real Real qz0 qz97 (Real.cos qz98)) (@HMul.hMul Real Real Real qz0 qz97 (@Neg.neg Real Real.instNeg qz99))) Bool.false 6545177055 17179869184 105892184647 190885526503424 Bool.true 5562807405 17179869184 105725630757 190885526503424 (BSN.cpow_neg_s_mk qz37 23170 1000 4 qz38 rfl)

noncomputable abbrev qz100 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz101 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def ep210 := @Enclosure.Real.IsNear.inv_image qz100 262145 131072 1 131072 32767 32768 65536 (@Enclosure.Real.IsNear.of_eq qz100 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz101 qz305)) Bool.false 262145 131072 1 131072 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz101 qz305)) Bool.false 262145 131072 1 131072 262145 131072 1 131072 (BSN.sqrt_enclosure 4 1 131072 131073 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep211 := nat_lit 753960950911045074462890625

noncomputable def ep212 := nat_lit 117048680082474133384580175

noncomputable def ep213 := BSN.log_dyadic_bound 3 5 12 11 ep211 65536 22222 ep212 431467934736729065175 90852 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 3) (BSN.artanhQ 5) 0 11 ep212 ep211 431467934736729065175 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep214 := nat_lit 1278620059707509434023432638595856

noncomputable def ep215 := BSN.cos_dyadic_bound_f 189097322 268435456 2 1 131072 44488 ep214 ep189 ep214 ep214 ep190 ep214 99873 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 189097322) qz306 0 1 ep214 ep189 ep214 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 189097322) qz307 0 1 ep214 ep190 ep214 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz102 := qz315

noncomputable abbrev qz316 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4210081) qz12)

noncomputable abbrev qz317 := (BSN.isNear_log_sfrac 4 1 90852 65536 1 22222 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 90852 65536 22222 rfl rfl rfl (ep213 rfl)))

noncomputable def ep216 := @Enclosure.Real.IsNear.cos_image qz98 qz316 Bool.false 4210081 131072 69 65536 Bool.false 99873 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz98 Bool.false 52626021 1638400 2317 2222200 4210081 131072 69 65536 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz102 23170 1000 0 1 90852 65536 1 22222 52626021 1638400 2317 2222200 qz88 qz317 rfl) rfl) (Enclosure.sfrac_false_div 4210081 131072) (BSN.cos_reduce0 qz316 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13306541123909485330432) qz68) 226375608064910080 72057594037927936 Bool.false 99873 131072 5 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q0 4210081 131072 226375608064910080 72057594037927936 5 13306541123909485330432 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 99873 131072 13306541123909485330432 18889465931478580854784 189097322 268435456 44488 44444 (ep215 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep217 := BSN.sin_dyadic_bound_f 189097322 268435456 2 1 131072 44488 ep214 ep193 ep214 ep214 ep194 ep214 84883 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 189097322) qz295 0 1 ep214 ep193 ep214 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 189097322) qz296 0 1 ep214 ep194 ep214 rfl rfl rfl rfl) rfl rfl

noncomputable def ep218 := @Enclosure.Real.IsNear.sin_image qz98 qz316 Bool.false 4210081 131072 69 65536 Bool.false 84883 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz98 Bool.false 52626021 1638400 2317 2222200 4210081 131072 69 65536 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz102 23170 1000 0 1 90852 65536 1 22222 52626021 1638400 2317 2222200 qz88 qz317 rfl) rfl) (Enclosure.sfrac_false_div 4210081 131072) (BSN.sin_reduce0 qz316 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13306541123909485330432) qz68) 226375608064910080 72057594037927936 Bool.false 84883 131072 5 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q0 4210081 131072 226375608064910080 72057594037927936 5 13306541123909485330432 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 84883 131072 13306541123909485330432 18889465931478580854784 189097322 268435456 44488 44444 (ep217 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz103 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) Bool.false 65535 131072 1 131072 65535 131072 1 131072 (ep210 rfl rfl) rfl)

noncomputable def ep219 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz97 (Real.cos qz98)) (@HMul.hMul Real Real Real qz0 qz97 (@Neg.neg Real Real.instNeg qz99)) Bool.false 6545177055 17179869184 105892184647 190885526503424 Bool.true 5562807405 17179869184 105725630757 190885526503424 (@Enclosure.Real.IsNear.mulLit_ff qz97 (Real.cos qz98) 65535 131072 1 131072 99873 131072 799427 728170496 6545177055 17179869184 105892184647 190885526503424 qz103 (@Enclosure.Real.IsNear.recentre' (Real.cos qz98) Bool.false 99873 131072 1598854 1456340992 99873 131072 799427 728170496 (ep216 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz97 (@Neg.neg Real Real.instNeg qz99) 65535 131072 1 131072 84883 131072 799427 728170496 5562807405 17179869184 105725630757 190885526503424 qz103 (@Enclosure.Real.IsNear.neg qz99 Bool.false 84883 131072 799427 728170496 (@Enclosure.Real.IsNear.recentre' qz99 Bool.false 84883 131072 1598854 1456340992 84883 131072 799427 728170496 (ep218 rfl rfl) rfl)) rfl)

noncomputable def ep220 := @ep179 6545177055 17179869184 105892184647 190885526503424 Bool.true 5562807405 17179869184 105725630757 190885526503424 Bool.false 186678800934017957888 21732272689 17179869184 378349811341 190885526503424 Bool.true 77476364197218484224 281857371 1073741824 5867708777 2982586351616 (ep180 (BSN.head_sum_c_succ qz11 3 4 rfl rfl) (ep208 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep209 ep219) rfl rfl

noncomputable def ep221 := @Enclosure.Complex.IsNear.mul qz71 (@HAdd.hAdd Complex Complex Complex qz8 qz72 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 1252316577383230977 7097914492977152000 343497161213635505073 1025244063109098766336000 Bool.false

noncomputable abbrev qz104 := (Complex.re qz299)

noncomputable abbrev qz105 := (Complex.im qz299)

noncomputable def ep222 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz104 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz72 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz105 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz72 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 58690359001787769 283916579719086080 30858752869477904941

noncomputable def ep223 := nat_lit 22222089961009945594136993999093760

noncomputable def ep224 := @Enclosure.Real.IsNear.mulLit_ff qz104 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz72 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 7050863079 17179869184 95058132629 190885526503424 324630329

noncomputable abbrev qz106 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable abbrev qz318 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz388 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable abbrev qz107 := (Real.cos qz318)

noncomputable abbrev qz108 := (@Neg.neg Real Real.instNeg (Real.sin qz318))

noncomputable def ep225 := @Enclosure.Complex.IsNear.of_eq qz71 (Complex.mk (@HMul.hMul Real Real Real qz0 qz106 qz107) (@HMul.hMul Real Real Real qz0 qz106 qz108)) Bool.false 7050863079 17179869184 95058132629 190885526503424 Bool.false 95369859 536870912 23575026719 47721381625856 (BSN.cpow_neg_s_mk qz37 23170 1000 5 qz38 rfl)

noncomputable abbrev qz109 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable abbrev qz110 := (@Nat.cast Real Real.instNatCast 5)

noncomputable def ep226 := @Enclosure.Real.IsNear.inv_image qz109 293085 131072 1 131072 29308 29309 65536 (@Enclosure.Real.IsNear.of_eq qz109 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz110 qz305)) Bool.false 293085 131072 1 131072 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz110 qz305)) Bool.false 293085 131072 1 131072 293085 131072 1 131072 (BSN.sqrt_enclosure 5 1 146542 146543 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep227 := nat_lit 141613827518379161815574079375

noncomputable def ep228 := nat_lit 29325128709309236875766211300

noncomputable def ep229 := BSN.log_dyadic_bound 2 3 15 14 ep227 65536 22222 ep228 57299708096576225280000 105476 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP 2) (BSN.artanhQ 3) 0 14 ep228 ep227 57299708096576225280000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep230 := nat_lit 148885448241768627457991784429287449628880081184442322042640515150030625

noncomputable def ep231 := nat_lit 89804444587160857714006733498425705917697565638026223062844125390625

noncomputable def ep232 := nat_lit 389792681056252906715584376889136345504152511805363562893385315856590625

noncomputable def ep233 := BSN.sin_dyadic_bound_f 312005485 268435456 3 2 131072 44488 ep230 ep166 ep231 ep232 ep169 ep231 120287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 312005485) qz295 0 2 ep230 ep166 ep231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 312005485) qz296 0 2 ep232 ep169 ep231 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz111 := qz318

noncomputable abbrev qz319 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz112 := qz319

noncomputable abbrev qz320 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4887757) qz12)

noncomputable abbrev qz321 := (BSN.isNear_log_sfrac 5 1 105476 65536 1 22222 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 105476 65536 22222 rfl rfl rfl (ep229 rfl)))

noncomputable def ep234 := @Enclosure.Real.IsNear.cos_image qz111 qz320 Bool.false 4887757 131072 69 65536 Bool.false 120287 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 61096973 1638400 2317 2222200 4887757 131072 69 65536 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz112 23170 1000 0 1 105476 65536 1 22222 61096973 1638400 2317 2222200 qz88 qz321 rfl) rfl) (Enclosure.sfrac_false_div 4887757 131072) (BSN.cos_reduce3 qz320 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21955434217551507226624) qz68) 226375608064910080 72057594037927936 Bool.false 120287 131072 5 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q3 4887757 131072 226375608064910080 72057594037927936 5 21955434217551507226624 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 120287 131072 21955434217551507226624 18889465931478580854784 312005485 268435456 44488 44444 (ep233 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep235 := nat_lit 82754050998576864524534994342270105663119021798307079456161550250190625

noncomputable def ep236 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120

noncomputable def ep237 := nat_lit 248082544106556271858176969559813465577521670263645185922358962499790625

noncomputable def ep238 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400

noncomputable def ep239 := BSN.cos_dyadic_bound_f 312005485 268435456 3 2 131072 44488 ep235 ep236 ep231 ep237 ep238 ep231 52064 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 312005485) qz306 0 2 ep235 ep236 ep231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 312005485) qz307 0 2 ep237 ep238 ep231 rfl rfl rfl rfl) rfl rfl

noncomputable def ep240 := @Enclosure.Real.IsNear.sin_image qz111 qz320 Bool.false 4887757 131072 69 65536 Bool.true 52064 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 61096973 1638400 2317 2222200 4887757 131072 69 65536 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz112 23170 1000 0 1 105476 65536 1 22222 61096973 1638400 2317 2222200 qz88 qz321 rfl) rfl) (Enclosure.sfrac_false_div 4887757 131072) (BSN.sin_reduce3 qz320 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21955434217551507226624) qz68) 226375608064910080 72057594037927936 Bool.false 52064 131072 5 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q3 4887757 131072 226375608064910080 72057594037927936 5 21955434217551507226624 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 52064 131072 21955434217551507226624 18889465931478580854784 312005485 268435456 44488 44444 (ep239 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz113 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) Bool.false 58617 131072 1 131072 58617 131072 1 131072 (ep226 rfl rfl) rfl)

noncomputable abbrev qz114 := (Real.sin qz318)

noncomputable def ep241 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz106 qz107) (@HMul.hMul Real Real Real qz0 qz106 qz108) Bool.false 7050863079 17179869184 95058132629 190885526503424 Bool.false 95369859 536870912 23575026719 47721381625856 (@Enclosure.Real.IsNear.mulLit_ff qz106 qz107 58617 131072 1 131072 120287 131072 799427 728170496 7050863079 17179869184 95058132629 190885526503424 qz113 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 120287 131072 1598854 1456340992 120287 131072 799427 728170496 (ep234 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz106 qz108 58617 131072 1 131072 1627 4096 799427 728170496 95369859 536870912 23575026719 47721381625856 qz113 (@Enclosure.Real.IsNear.neg qz114 Bool.true 1627 4096 799427 728170496 (@Enclosure.Real.IsNear.recentre' qz114 Bool.true 52064 131072 1598854 1456340992 1627 4096 799427 728170496 (ep240 rfl rfl) rfl)) rfl)

noncomputable def ep242 := @ep224 644518680 0 1 58690359001787769 283916579719086080 30858752869477904941 123029287573091851960320 (@Enclosure.Complex.IsNear.re_isNear qz71 Bool.false 7050863079 17179869184 95058132629 190885526503424 Bool.false 95369859 536870912 23575026719 47721381625856 (ep225 ep241))

noncomputable def ep243 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz72 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 324630329 644518680 0 1 Bool.false

noncomputable def ep244 := @Enclosure.Complex.IsNear.addLitP qz72 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) Bool.false 5320989 10741978 0 1 Bool.true 1158500

noncomputable def ep245 := @ep244 5370989 0 1 Bool.false 1 120 0 1 Bool.false 2317 6000 0 1 Bool.false 649260658 324630329 644518680 0 1 Bool.false 5493581513 5493581513 32225934000 0 1

noncomputable abbrev qz115 := (@HDiv.hDiv Complex Complex Complex qz267 qz300 (@HSub.hSub Complex Complex Complex qz257 qz262 (1 : Complex)))

noncomputable def ep246 := @Enclosure.Complex.IsNear.addLitP qz115 qz42 Bool.true 10000000 2148395600 0 1 Bool.true 463400000 2148395600 0 1

noncomputable def ep247 := @Enclosure.Complex.IsNear.of_eq qz115 (Complex.mk (Enclosure.sfrac Bool.true 10000000 2148395600) (Enclosure.sfrac Bool.true 463400000 2148395600)) Bool.true 10000000 2148395600 0 1 Bool.true 463400000 2148395600 0 1

noncomputable def ep248 := @ep246 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 2128395600 5320989 10741978 0 1 Bool.true 463400000 1158500 5370989 0 1 (ep247 (BSN.N_div_s_sub_one_mk qz37 23170 1000 5 qz38 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 10000000 2148395600) (Enclosure.sfrac Bool.true 463400000 2148395600) Bool.true 10000000 2148395600 0 1 Bool.true 463400000 2148395600 0 1 (Enclosure.Real.IsNear.const Bool.true 10000000 2148395600) (Enclosure.Real.IsNear.const Bool.true 463400000 2148395600))) qz44 rfl

noncomputable abbrev qz116 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz322 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz393 (@Nat.cast Complex Complex.instNatCast 5) 1))

noncomputable abbrev qz117 := qz322

noncomputable def ep249 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz117)) Bool.false 1 120 0 1

noncomputable def ep250 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz117) Bool.false 0 1 0 1 Bool.false

noncomputable def ep251 := @ep250 0 1 0 1 Bool.false 1 120 0 1 Bool.false 2317 6000 0 1 Bool.false 1 1 120 0 1 Bool.false 2317 2317 6000 0

noncomputable def ep252 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (Complex.mk qz45 qz45) Bool.false 0 1 0 1 Bool.false

noncomputable def ep253 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz117 Bool.false 1 120 0 1 Bool.false 2317 6000 0 1

noncomputable abbrev qz118 := (Complex.re qz322)

noncomputable abbrev qz119 := (Complex.im qz322)

noncomputable def ep254 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz118) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz119) 1 120 0 1 0 1 0

noncomputable def ep255 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz118 1 24 0 1 1 5 0 1 1

noncomputable def ep256 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep257 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep258 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz45) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow03.d6 rfl) qz287

noncomputable def ep259 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz11 Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 (BSN.ascPochhammer_one_eval qz11)

noncomputable def ep260 := ep259 (@Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk qz32 qz37) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 (BSN.s_crit_mk qz37 Bool.false 23170 1000 qz38) (@Enclosure.Complex.IsNear.mk qz32 qz37 Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 qz33 qz88))

noncomputable def ep261 := @ep257 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep258) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep260)

noncomputable def ep262 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 23170 1000 0 1 0 1 0

noncomputable def ep263 := @ep262 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep258) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep260)

noncomputable def ep264 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) 2317 1200 0 1 0 1 0 1 2317

noncomputable def ep265 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 23170 1000 0 1 2317 1200 0

noncomputable def ep266 := @ep265 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep258) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep260)

noncomputable def ep267 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep268 := @ep267 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep258) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep260)

noncomputable def ep269 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 2317 1200 0 1 (@ep256 1 24 0 1 (ep261 rfl) (ep263 rfl) rfl rfl) (@ep264 2317 1200 0 1 (ep266 rfl) (ep268 rfl) rfl rfl)

noncomputable def ep270 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2317 1200 0 1 ep269

noncomputable abbrev qz120 := (@Enclosure.Complex.IsNear.of_eq qz322 (Complex.mk (Enclosure.sfrac Bool.false 1 5) qz283) Bool.false 1 5 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 5 1 5 EMRow03.d7 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 5) qz283 Bool.false 1 5 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 5) qz284))

noncomputable def ep271 := @ep255 120 0 1 ep270 (@Enclosure.Complex.IsNear.re_isNear qz117 Bool.false 1 5 0 1 Bool.false 0 1 0 1 qz120)

noncomputable def ep272 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz119 2317 1200 0 1 0 1 0 1 0

noncomputable def ep273 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2317 1200 0 1 ep269

noncomputable def ep274 := @ep272 1 0 1 ep273 (@Enclosure.Complex.IsNear.im_isNear qz117 Bool.false 1 5 0 1 Bool.false 0 1 0 1 qz120)

noncomputable def ep275 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz119) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz118) 0 1 0 1 2317 6000 0

noncomputable def ep276 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz119 1 24 0 1 0 1 0 1 0

noncomputable def ep277 := @ep276 1 0 1 ep270 (@Enclosure.Complex.IsNear.im_isNear qz117 Bool.false 1 5 0 1 Bool.false 0 1 0 1 qz120)

noncomputable def ep278 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz118 2317 1200 0 1 1 5 0 1 2317

noncomputable def ep279 := @ep278 6000 0 1 ep273 (@Enclosure.Complex.IsNear.re_isNear qz117 Bool.false 1 5 0 1 Bool.false 0 1 0 1 qz120)

noncomputable def ep280 := @ep251 1 (@ep252 0 1 0 1 (BSN.bern_sum_base qz11 5) qz62) (ep253 (@ep254 1 1 1 120 0 1 (ep271 rfl) (ep274 rfl) rfl rfl) (@ep275 1 2317 2317 6000 0 1 (ep277 rfl) (ep279 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep281 := ep245 (ep248 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep249 Bool.false 2317 6000 0 1 (BSN.bern_sum_succ qz11 5 0 1 1 rfl rfl) (ep280 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep282 := @Enclosure.Real.IsNear.mulLit_ff qz105 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz72 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 95369859 536870912 23575026719 47721381625856 5493581513

noncomputable def ep283 := @ep282 32225934000 0 1 13433899853841453 443619655811072000 3158812950048279167 37508929138137759744000 (@Enclosure.Complex.IsNear.im_isNear qz71 Bool.false 7050863079 17179869184 95058132629 190885526503424 Bool.false 95369859 536870912 23575026719 47721381625856 (ep225 ep241))

noncomputable def ep284 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz72 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 324630329 644518680 0 1 Bool.false

noncomputable def ep285 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz104 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz72 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz105 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz72 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 993192078499709193 14195828985954304000 12736819513926255797

noncomputable def ep286 := nat_lit 20081276129951701216571351283793920

noncomputable def ep287 := @Enclosure.Real.IsNear.mulLit_ff qz104 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz72 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 7050863079 17179869184 95058132629 190885526503424 5493581513

noncomputable def ep288 := @ep287 32225934000 0 1 993192078499709193 14195828985954304000 12736819513926255797 150035716552551038976000 (@Enclosure.Complex.IsNear.re_isNear qz71 Bool.false 7050863079 17179869184 95058132629 190885526503424 Bool.false 95369859 536870912 23575026719 47721381625856 (ep225 ep241))

noncomputable def ep289 := @Enclosure.Real.IsNear.mulLit_ff qz105 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz72 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz75 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 95369859 536870912 23575026719 47721381625856 324630329

noncomputable def ep290 := @ep289 644518680 0 1 793844838560349 8872393116221440 7653168679972760551 30757321893272962990080 (@Enclosure.Complex.IsNear.im_isNear qz71 Bool.false 7050863079 17179869184 95058132629 190885526503424 Bool.false 95369859 536870912 23575026719 47721381625856 (ep225 ep241))

noncomputable abbrev qz323 := (ep281 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep291 := @ep221 2263343820196267593 14195828985954304000 52637008617064835843 157729855862938271744000 (@ep222 123029287573091851960320 13433899853841453 443619655811072000 3158812950048279167 37508929138137759744000 ep223 1252316577383230977 7097914492977152000 343497161213635505073 1025244063109098766336000 (ep242 (@ep243 5493581513 32225934000 0 1 qz323) rfl) (ep283 (@ep284 5493581513 32225934000 0 1 qz323) rfl) rfl rfl) (@ep285 150035716552551038976000 793844838560349 8872393116221440 7653168679972760551 30757321893272962990080 ep286 2263343820196267593 14195828985954304000 52637008617064835843 157729855862938271744000 (ep288 (@ep284 5493581513 32225934000 0 1 qz323) rfl) (ep290 (@ep243 5493581513 32225934000 0 1 qz323) rfl) rfl rfl)

noncomputable def ep292 := @ep176 362942478613081603843 157729855862938271744000 (@ep177 2982586351616 (BSN.head_sum_c_eq qz11 5) (ep178 (BSN.head_sum_c_succ qz11 4 5 rfl rfl) (ep220 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep291 rfl rfl rfl

noncomputable def ep293 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz11 1 5) Bool.false 10231070235661647977 7097914492977152000 2375609836078221754073 1025244063109098766336000 Bool.true 1463063168628148407 14195828985954304000 362942478613081603843 157729855862938271744000 (@ep172 1025244063109098766336000 Bool.true 1463063168628148407 14195828985954304000 362942478613081603843 157729855862938271744000 (BSN.zetaApproximant_eq_folded' qz11 1 5 rfl) (ep292 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep294 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 5)) 29 131072 227493

noncomputable def ep295 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) Bool.false 29 131072 454986

noncomputable def ep296 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) qz263 Bool.false 411745 131072 19

noncomputable def ep297 := nat_lit 276583425830994105494346465831810052573023181770965677654272598988634721

noncomputable def ep298 := nat_lit 827754075074713189203216575177542871445546219567441842543164596551760481

noncomputable def ep299 := BSN.cos_dyadic_bound_f 421596331 268435456 3 2 131072 44488 ep297 ep236 ep167 ep298 ep238 ep167 29 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 421596331) qz306 0 2 ep297 ep236 ep167 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 421596331) qz307 0 2 ep298 ep238 ep167 rfl rfl rfl rfl) rfl rfl

noncomputable def ep300 := @ep296 32768 Bool.false 29 131072 1 22222 (@ep55 411745 131072 19 32768 ep164 rfl) (Enclosure.sfrac_false_div 411745 131072) (BSN.sin_reduce1 qz263 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29667204414009382010880) qz68) 226375608064910080 72057594037927936 Bool.false 29 131072 0 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q1 411745 131072 226375608064910080 72057594037927936 0 29667204414009382010880 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 29 131072 29667204414009382010880 18889465931478580854784 421596331 268435456 44488 44444 (ep299 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep301 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz11 1 5) Bool.false 10231070235661647977 7097914492977152000 2375609836078221754073 1025244063109098766336000 Bool.true 1463063168628148407 14195828985954304000 362942478613081603843 157729855862938271744000 (@ep172 1025244063109098766336000 Bool.true 1463063168628148407 14195828985954304000 362942478613081603843 157729855862938271744000 (BSN.zetaApproximant_eq_folded' qz11 1 5 rfl) (ep292 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow03.d8 : Enclosure.Real.IsNear (hardyZApproximantEM 1 5 qz37) Bool.true ep38 ep39 ep40 ep41 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 5 qz37) ep42 Bool.true ep38 ep39 ep40 ep41 (@Eq.refl Real ep42) (@ep43 Bool.true ep38 ep39 ep40 ep41 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) (zetaApproximant qz11 1 5)) (@ep45 930337848423501266944000 ep46 ep47 42428831890216303803 ep39 ep48 ep49 ep50 ep38 ep39 ep40 ep41 (@ep51 364085248 10231070235661647977 7097914492977152000 2375609836078221754073 1025244063109098766336000 ep44 930337848423501266944000 ep46 ep47 (@ep52 728170496 131071 131072 227493 364085248 (ep171 rfl rfl) rfl) ep293 rfl) (@ep294 364085248 1463063168628148407 14195828985954304000 362942478613081603843 157729855862938271744000 42428831890216303803 ep39 ep48 ep49 (@ep295 728170496 29 131072 227493 364085248 (ep300 rfl rfl) rfl) ep301 rfl) rfl rfl))

theorem EMRow03.d9 : @Eq Nat (Nat.pow 6 1) 6 := @Eq.refl Nat 6

noncomputable def ep302 := nat_lit 11853261393716373176139607

noncomputable def ep303 := nat_lit 4139054314381110442721280

noncomputable def ep304 := nat_lit 41541405323242016753856084639409

noncomputable def ep305 := nat_lit 7664762099460607873982475219763200

noncomputable abbrev qz412 := (Enclosure.sfrac Bool.false 27670 1000)

noncomputable abbrev qz398 := (@HAdd.hAdd Complex Complex Complex qz406 (@HAdd.hAdd Complex Complex Complex qz406 qz407 (@HMul.hMul Complex Complex Complex qz405 Complex.I (@HDiv.hDiv Complex Complex Complex qz408 (↑qz412) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz324 := qz398

noncomputable abbrev qz121 := (Complex.Stirling.logGammaStirling 1 qz324)

noncomputable abbrev qz399 := (@HAdd.hAdd Complex Complex Complex qz406 qz407 (@HMul.hMul Complex Complex Complex qz405 Complex.I (@HDiv.hDiv Complex Complex Complex qz408 (↑qz412) (2 : Complex))))

noncomputable abbrev qz325 := qz399

noncomputable abbrev qz122 := qz325

noncomputable abbrev qz400 := qz412

noncomputable abbrev qz326 := qz400

noncomputable abbrev qz123 := (@HMul.hMul Real Real Real qz250 (@HDiv.hDiv Real Real Real qz254 qz326 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz413 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 27670 1000)))

noncomputable abbrev qz401 := qz413

noncomputable abbrev qz327 := qz401

noncomputable abbrev qz124 := qz327

noncomputable def ep306 := Complex.re (@HMul.hMul Complex Complex Complex qz4 (Complex.exp (@HMul.hMul Complex Complex Complex qz4 Complex.I ↑(@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123))) (zetaApproximant qz124 1 6))

noncomputable def ep307 := @Enclosure.Real.IsNear.of_eq ep306 (@HSub.hSub Real Real Real qz5 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) (Complex.re (zetaApproximant qz124 1 6))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) (Complex.im (zetaApproximant qz124 1 6))))

noncomputable def ep308 := nat_lit 35559964118216062689879401

noncomputable def ep309 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) (Complex.re (zetaApproximant qz124 1 6))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) (Complex.im (zetaApproximant qz124 1 6))) ep308

noncomputable def ep310 := nat_lit 12417162943143331328163840

noncomputable def ep311 := nat_lit 8199614375559641860423538744377

noncomputable def ep312 := nat_lit 1532952419892121574796495043952640

noncomputable def ep313 := nat_lit 135833361360951862934597729381

noncomputable def ep314 := nat_lit 1916190524865151968495618804940800

noncomputable def ep315 := nat_lit 22077581720016963863063171520661433904883021381632

noncomputable def ep316 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) (Complex.re (zetaApproximant qz124 1 6)) 131071 131072 130413

noncomputable def ep317 := nat_lit 5263027094317075896729600

noncomputable def ep318 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) Bool.false 131071 131072 260826

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 823529) qz12)

noncomputable def ep319 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123) qz328 Bool.false 823529 131072 11

noncomputable def ep320 := nat_lit 27306393600000000000000000

noncomputable def ep321 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123) Bool.false 11318500618344259247 1801439850948198400 18084101612976226535221 ep320

noncomputable def ep322 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123 39848505602890456751 1801439850948198400 6555050237976226535221 ep320 207583107 13107200

noncomputable def ep323 := nat_lit 148353851304761874802278400

noncomputable def ep324 := nat_lit 4551065600000000000000000

noncomputable def ep325 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 19338308215257051969 900719925474099200 1712895056152005747913 ep324 Bool.false 39848505602890456751 1801439850948198400

noncomputable def ep326 := @Enclosure.Complex.IsNear.subLitP qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 14601757734198299769 900719925474099200 1610495056120148288713 ep324 Bool.false 45313034856280607151 1801439850948198400 5326250237948920141621

noncomputable def ep327 := nat_lit 87091997672207460797227892289306624

noncomputable def ep328 := nat_lit 11216357186528036442344483408838656

noncomputable abbrev qz329 := (@HSub.hSub Complex Complex Complex qz384 qz398 qz390)

noncomputable abbrev qz330 := (Complex.log qz398)

noncomputable abbrev qz125 := (@HSub.hSub Complex Complex Complex qz257 (@HMul.hMul Complex Complex Complex qz256 qz329 qz330) qz324)

noncomputable abbrev qz126 := qz324

noncomputable def ep329 := @Enclosure.Complex.IsNear.of_eq qz121 (@HAdd.hAdd Complex Complex Complex qz8 (@HAdd.hAdd Complex Complex Complex qz8 qz125 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz126 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k)))))) Bool.true 14601757734198299769

noncomputable def ep330 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz8 qz125 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz126 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) Bool.true 14602617333314997369 900719925474099200

noncomputable def ep331 := nat_lit 7839258991562094785832419328

noncomputable def ep332 := nat_lit 1216362517438957924453554585600

noncomputable def ep333 := @ep330 1572724243222028587 4444400000000000000000 Bool.false 45323606015195728303 1801439850948198400 866750000219097809 4444400000000000000000 Bool.false 512361 536870912 3 536870912 Bool.true 157522543 26843545600 2767 80530636800 Bool.true ep331 14601757734198299769 900719925474099200 1610495056120148288713 ep324 Bool.false ep332

noncomputable def ep334 := @Enclosure.Complex.IsNear.addLitP qz125 qz14 Bool.true 15430315942809422969 900719925474099200 1471000000057966087 4444400000000000000000

noncomputable def ep335 := @ep334 Bool.false 45323606015195728303 1801439850948198400 866750000219097809 4444400000000000000000 Bool.false 60223 65536 3 131072 Bool.false 0 1 0 1 Bool.true 956997129556131667574784 14602617333314997369 900719925474099200 1572724243222028587 4444400000000000000000 Bool.false 45323606015195728303 45323606015195728303 1801439850948198400

noncomputable abbrev qz127 := (@HMul.hMul Complex Complex Complex qz256 qz329 qz330)

noncomputable def ep336 := @Enclosure.Complex.IsNear.subLitP qz127 qz126 Bool.true 13403696110492699769 900719925474099200 1471000000057966087 4444400000000000000000 Bool.false 70246526353064053167

noncomputable def ep337 := @ep336 1801439850948198400 866750000219097809 4444400000000000000000 Bool.false 9000 4000 0 1 Bool.false 55340 4000 0 1 Bool.true 61721263771237691876000 15430315942809422969 900719925474099200 1471000000057966087 4444400000000000000000 Bool.false 181294424060782913212000 45323606015195728303 1801439850948198400 866750000219097809 4444400000000000000000

noncomputable abbrev qz128 := qz329

noncomputable abbrev qz129 := qz330

noncomputable def ep338 := @Enclosure.Complex.IsNear.mul qz128 qz129 Bool.true 13403696110492699769 900719925474099200 1471000000057966087 4444400000000000000000 Bool.false 70246526353064053167 1801439850948198400 866750000219097809

noncomputable abbrev qz130 := (Complex.re qz329)

noncomputable abbrev qz131 := (Complex.re qz330)

noncomputable abbrev qz132 := (Complex.im qz329)

noncomputable abbrev qz133 := (Complex.im qz330)

noncomputable def ep339 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz130 qz131) (@HMul.hMul Real Real Real qz0 qz132 qz133) 166468952685448007 36028797018963968 1750000000544439 88888000000000000000 2195677490953612493 112589990684262400

noncomputable def ep340 := nat_lit 60364880808602289260044489456615424

noncomputable def ep341 := @Enclosure.Real.IsNear.mulLit_ff qz130 qz131 7000 4000 0 1 23781278955064001 9007199254740992 250000000077777 22222000000000000000

noncomputable def ep342 := @Enclosure.Complex.IsNear.re_isNear qz128 Bool.false 7000 4000 0 1 Bool.false 55340 4000 0 1

noncomputable abbrev qz331 := (Enclosure.sfrac Bool.false 55340 4000)

noncomputable abbrev qz134 := qz331

noncomputable def ep343 := @Enclosure.Complex.IsNear.of_eq qz128 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz134) Bool.false 7000 4000 0 1 Bool.false 55340 4000 0

noncomputable abbrev qz135 := (Complex.log (Complex.mk qz274 qz331))

noncomputable def ep344 := @Enclosure.Complex.IsNear.of_eq qz129 qz135 Bool.false 23781278955064001 9007199254740992 250000000077777 22222000000000000000 Bool.false 793522765071779 562949953421312 500000000011111 22222000000000000000

noncomputable def ep345 := nat_lit 2055674171640608507139442628641918122726071930880000000000000

noncomputable def ep346 := nat_lit 31353946953738333341578587171935170706358398976000000000000

noncomputable def ep347 := nat_lit 25930008341728104069528937153096611763875840000000000000

noncomputable def ep348 := BSN.log_dyadic_bound 1095515600 5191515600 4 3 ep345 131072 44444 ep346 ep347 56161 6287031200 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 1095515600) (BSN.artanhQ 5191515600) 0 3 ep346 ep345 ep347 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz332 := (Real.log (Enclosure.sfrac Bool.false 3143515600 16000000))

noncomputable def ep349 := @Enclosure.Real.IsNear.mulLit_ff qz32 qz332 1 2 0 1 23781278955064001 4503599627370496 250000000077777 11111000000000000000 23781278955064001 9007199254740992 250000000077777 22222000000000000000 qz33 (BSN.isNear_log_sfrac 3143515600 16000000 23781278955064001 4503599627370496 250000000077777 11111000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3143515600) qz276)) Bool.false 24936478361585189912576 4722366482869645213696 1000000000311108 44444000000000000000 23781278955064001 4503599627370496 250000000077777 11111000000000000000 (BSN.log_rat_reduce_isNear 3143515600 16000000 7 6287031200 4096000000 56161 131072 24973259072661432 36028797018963968 44444 1000000000000000 rfl rfl rfl rfl (ep348 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep350 := BSN.arctan_dyadic_bound_f 9000 55340 2 1 131072 44444 6561000000000000 46895009001216800000 6561000000000000 19683000000000000 65653012601703520000 19683000000000000 21131 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 55340) 0 1 6561000000000000 46895009001216800000 6561000000000000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.arctanOddP 9000) (BSN.arctanOddQ 55340) 0 1 19683000000000000 65653012601703520000 19683000000000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz333 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 55340)))

noncomputable def ep351 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz333 884279719003555 562949953421312 1 2000000000000000 21131 131072 1 44444 104008615863488217088 793522765071779 562949953421312 500000000011111 22222000000000000000 qz35 (ep350 rfl) rfl rfl

noncomputable abbrev qz136 := (Complex.mk qz274 qz331)

noncomputable abbrev qz137 := qz326

noncomputable abbrev qz334 := (@Eq.refl Real qz400)

noncomputable abbrev qz138 := qz334

noncomputable abbrev qz335 := (@Nat.cast Real Real.instNatCast 55340)

noncomputable abbrev qz139 := (Real.arctan (@HDiv.hDiv Real Real Real qz254 qz335 qz280))

noncomputable def ep352 := @Enclosure.Complex.IsNear.re_isNear qz129 Bool.false 23781278955064001 9007199254740992 250000000077777 22222000000000000000 Bool.false 793522765071779 562949953421312 500000000011111 22222000000000000000 (ep344 (@congrArg Complex Complex qz126 qz136 Complex.log (BSN.w_shift_mk qz137 Bool.false 27670 1000 2 qz138 rfl)) (@Enclosure.Complex.IsNear.of_parts qz135 Bool.false 23781278955064001 9007199254740992 250000000077777 22222000000000000000 Bool.false 793522765071779 562949953421312 500000000011111 22222000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz135) (@HMul.hMul Real Real Real qz0 qz32 qz332) Bool.false 23781278955064001 9007199254740992 250000000077777 22222000000000000000 (Enclosure.clog_re_eq 9000 55340 4000 3143515600 16000000 rfl rfl rfl) (ep349 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz135) qz139 Bool.false 793522765071779 562949953421312 500000000011111 22222000000000000000 (Enclosure.clog_im_eq 9000 55340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz139 (@HSub.hSub Real Real Real qz5 qz34 qz333) Bool.false 793522765071779 562949953421312 500000000011111 22222000000000000000 (BSN.arctan_recip 55340 9000 rfl rfl) ep351))))

noncomputable def ep353 := @Enclosure.Real.IsNear.mulLit_ff qz132 qz133 55340 4000 0 1 793522765071779 562949953421312 500000000011111 22222000000000000000

noncomputable def ep354 := @Enclosure.Complex.IsNear.im_isNear qz128 Bool.false 7000 4000 0 1 Bool.false 55340 4000 0 1

noncomputable def ep355 := @Enclosure.Complex.IsNear.im_isNear qz129 Bool.false 23781278955064001 9007199254740992 250000000077777 22222000000000000000 Bool.false 793522765071779 562949953421312 500000000011111 22222000000000000000 (ep344 (@congrArg Complex Complex qz126 qz136 Complex.log (BSN.w_shift_mk qz137 Bool.false 27670 1000 2 qz138 rfl)) (@Enclosure.Complex.IsNear.of_parts qz135 Bool.false 23781278955064001 9007199254740992 250000000077777 22222000000000000000 Bool.false 793522765071779 562949953421312 500000000011111 22222000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz135) (@HMul.hMul Real Real Real qz0 qz32 qz332) Bool.false 23781278955064001 9007199254740992 250000000077777 22222000000000000000 (Enclosure.clog_re_eq 9000 55340 4000 3143515600 16000000 rfl rfl rfl) (ep349 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz135) qz139 Bool.false 793522765071779 562949953421312 500000000011111 22222000000000000000 (Enclosure.clog_im_eq 9000 55340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz139 (@HSub.hSub Real Real Real qz5 qz34 qz333) Bool.false 793522765071779 562949953421312 500000000011111 22222000000000000000 (BSN.arctan_recip 55340 9000 rfl rfl) ep351))))

noncomputable abbrev qz336 := (Enclosure.Real.IsNear.const Bool.false 55340 4000)

noncomputable abbrev qz140 := (@ep343 1 (BSN.w_sub_half_mk qz326 Bool.false 27670 1000 2 qz334 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz331 Bool.false 7000 4000 0 1 Bool.false 55340 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz336))

noncomputable def ep356 := @ep339 1383500000030744137 4444400000000000000000 ep340 13403696110492699769 900719925474099200 1471000000057966087 4444400000000000000000 (@ep341 166468952685448007 36028797018963968 1750000000544439 88888000000000000000 (ep342 qz140) ep352 rfl) (@ep353 2195677490953612493 112589990684262400 1383500000030744137 4444400000000000000000 (ep354 qz140) ep355 rfl) rfl

noncomputable def ep357 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz130 qz133) (@HMul.hMul Real Real Real qz0 qz132 qz131) 5554659355502453 2251799813685248 3500000000077777 88888000000000000000 65802798868662090767 1801439850948198400

noncomputable def ep358 := nat_lit 158181114953865498588857094075580416

noncomputable def ep359 := @Enclosure.Real.IsNear.mulLit_ff qz130 qz133 7000 4000 0 1 793522765071779 562949953421312 500000000011111 22222000000000000000

noncomputable def ep360 := @Enclosure.Real.IsNear.mulLit_ff qz132 qz131 55340 4000 0 1 23781278955064001 9007199254740992 250000000077777 22222000000000000000

noncomputable def ep361 := @ep357 691750000215208959 4444400000000000000000 ep358 70246526353064053167 1801439850948198400 866750000219097809 4444400000000000000000 (@ep359 5554659355502453 2251799813685248 3500000000077777 88888000000000000000 (ep342 qz140) ep355 rfl) (@ep360 65802798868662090767 1801439850948198400 691750000215208959 4444400000000000000000 (ep354 qz140) ep352 rfl) rfl

noncomputable def ep362 := @Enclosure.Complex.IsNear.of_eq qz126 qz136 Bool.false 9000 4000 0 1 Bool.false 55340 4000 0 1 (BSN.w_shift_mk qz137 Bool.false 27670 1000 2 qz138 rfl)

noncomputable abbrev qz337 := (ep362 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 55340 4000) Bool.false 9000 4000 0 1 Bool.false 55340 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 55340 4000)))

noncomputable abbrev qz141 := qz337

noncomputable def ep363 := ep337 (@ep338 4444400000000000000000 (ep356 rfl) (ep361 rfl)) qz141 rfl rfl rfl rfl rfl rfl

noncomputable def ep364 := @ep335 866750000219097809 4444400000000000000000 (ep363 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz42 (↑qz3) Bool.false 60223 65536 3 131072 Bool.false 0 1 0 1 (@ep95 65536 3 131072 (ep97 rfl) (ep99 rfl) rfl rfl) (@ep100 1 0 1 (ep102 rfl) (ep104 rfl) rfl rfl))

noncomputable abbrev qz338 := (@HPow.hPow Complex Int Complex qz392 qz398 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz142 := qz338

noncomputable def ep365 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz126 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz126 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48) qz142)) Bool.false 512361 536870912 3 536870912

noncomputable def ep366 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz126 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48) qz142) Bool.false 0 1 0 1 Bool.false

noncomputable def ep367 := @ep366 0 1 0 1 Bool.false 512361 536870912 3 536870912 Bool.true 157522543 26843545600 2767 80530636800 Bool.false 512361 512361 536870912 3 536870912 Bool.true 157522543 157522543 26843545600 2767

noncomputable def ep368 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz126 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz45 qz45) Bool.false 0 1 0 1 Bool.false

noncomputable def ep369 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48) qz142 Bool.false 512361 536870912 3 536870912 Bool.true 157522543 26843545600 2767 80530636800

noncomputable abbrev qz143 := (Complex.re qz338)

noncomputable abbrev qz144 := (Complex.im qz338)

noncomputable def ep370 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz143) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz144) 512361 536870912 3 536870912 0 1 0

noncomputable def ep371 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz143 1 12 0 1 1537083 134217728 9 134217728 512361

noncomputable def ep372 := @Enclosure.Complex.IsNear.re_isNear qz142 Bool.false 1537083 134217728 9 134217728 Bool.true 472567629 6710886400 2767 6710886400

noncomputable abbrev qz339 := (@HPow.hPow Complex Nat Complex qz393 qz398 1)

noncomputable abbrev qz145 := (@Inv.inv Complex Complex.instInv qz339)

noncomputable def ep373 := @Enclosure.Complex.IsNear.of_eq qz142 qz145 Bool.false 1537083 134217728 9 134217728 Bool.true 472567629 6710886400 2767

noncomputable def ep374 := @Enclosure.Complex.IsNear.of_parts qz145 Bool.false 1537083 134217728 9 134217728 Bool.true 472567629 6710886400 2767

noncomputable abbrev qz146 := (Complex.re qz339)

noncomputable abbrev qz147 := qz339

noncomputable def ep375 := @Enclosure.Real.IsNear.mulLit_ff qz146 (@Inv.inv Real Real.instInv (@DFunLike.coe qz54 Complex (fun (x : Complex) => Real) qz55 Complex.normSq qz147)) 9000 4000 0 1 170787 33554432 1 33554432

noncomputable def ep376 := @Enclosure.Complex.IsNear.re_isNear qz147 Bool.false 9000 4000 0 1 Bool.false 55340 4000 0 1

noncomputable def ep377 := @Enclosure.Complex.IsNear.of_eq qz147 qz126 Bool.false 9000 4000 0 1 Bool.false 55340 4000 0

noncomputable def ep378 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz54 Complex (fun (x : Complex) => Real) qz55 Complex.normSq qz147)) Bool.false 170787 33554432 1 33554432 170787 33554432 1

noncomputable abbrev qz148 := (Complex.im qz339)

noncomputable def ep379 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz54 Complex (fun (x : Complex) => Real) qz55 Complex.normSq qz147) (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 qz146 qz146) (@HMul.hMul Real Real Real qz0 qz148 qz148)) Bool.false 7858789 40000 0 1

noncomputable def ep380 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz146 qz146) (@HMul.hMul Real Real Real qz0 qz148 qz148) 81 16 0 1 7656289 40000

noncomputable def ep381 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz146 9000 4000 0 1 9000 4000 0 1

noncomputable def ep382 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz148 55340 4000 0 1 55340 4000 0 1

noncomputable def ep383 := @Enclosure.Complex.IsNear.im_isNear qz147 Bool.false 9000 4000 0 1 Bool.false 55340 4000 0 1

noncomputable abbrev qz149 := (ep376 (@ep377 1 (BSN.pow_one_c qz324) qz337))

noncomputable abbrev qz150 := (ep383 (@ep377 1 (BSN.pow_one_c qz324) qz337))

noncomputable def ep384 := @ep380 0 1 125740624 7858789 40000 0 1 (@ep381 81 16 0 1 qz149 qz149 rfl) (@ep382 7656289 40000 0 1 qz150 qz150 rfl)

noncomputable def ep385 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz54 Complex (fun (x : Complex) => Real) qz55 Complex.normSq qz147) 7858789 40000 0 1 85393 85394 16777216 (ep379 (Enclosure.Complex.normSq_eq_mul_add_mul qz147) (ep384 rfl rfl)) rfl

noncomputable def ep386 := @Enclosure.Real.IsNear.of_eq (Complex.re qz145) (@HMul.hMul Real Real Real qz0 qz146 (@Inv.inv Real Real.instInv (@DFunLike.coe qz54 Complex (fun (x : Complex) => Real) qz55 Complex.normSq qz147))) Bool.false 1537083 134217728 9 134217728 (Enclosure.Complex.inv_re_eq_mul qz147) (@ep375 1537083 134217728 9 134217728 qz149 (@ep378 33554432 (ep385 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep387 := @Enclosure.Real.IsNear.of_eq (Complex.im qz145) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz148) (@Inv.inv Real Real.instInv (@DFunLike.coe qz54 Complex (fun (x : Complex) => Real) qz55 Complex.normSq qz147))) Bool.true 472567629 6710886400 2767 6710886400 (Enclosure.Complex.inv_im_eq_mul qz147)

noncomputable def ep388 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz148) (@Inv.inv Real Real.instInv (@DFunLike.coe qz54 Complex (fun (x : Complex) => Real) qz55 Complex.normSq qz147)) 55340 4000 0 1 170787 33554432 1

noncomputable def ep389 := @ep388 33554432 472567629 6710886400 2767 6710886400 (@Enclosure.Real.IsNear.neg qz148 Bool.false 55340 4000 0 1 qz150) (@ep378 33554432 (ep385 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep390 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz144 0 1 0 1 472567629 6710886400 2767 6710886400 0

noncomputable def ep391 := @Enclosure.Complex.IsNear.im_isNear qz142 Bool.false 1537083 134217728 9 134217728 Bool.true 472567629 6710886400 2767 6710886400

noncomputable abbrev qz151 := (@ep373 6710886400 (BSN.zpow_one_sub_two_mul qz324 1 1 rfl rfl) (@ep374 6710886400 ep386 (ep387 ep389)))

noncomputable def ep392 := @ep370 1 512361 512361 536870912 3 536870912 (@ep371 536870912 3 536870912 ep114 (ep372 qz151) rfl) (@ep390 1 0 1 ep134 (ep391 qz151) rfl) rfl

noncomputable def ep393 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz144) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz143) 157522543 26843545600 2767 80530636800 0 1 0

noncomputable def ep394 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz144 1 12 0 1 472567629 6710886400 2767 6710886400 157522543

noncomputable def ep395 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz47)) qz48)) qz143 0 1 0 1 1537083 134217728 9 134217728 0

noncomputable def ep396 := @ep393 1 157522543 157522543 26843545600 2767 80530636800 (@ep394 26843545600 2767 80530636800 ep114 (ep391 qz151) rfl) (@ep395 1 0 1 ep134 (ep372 qz151) rfl) rfl

noncomputable def ep397 := @ep367 80530636800 (@ep368 0 1 0 1 (BSN.stirling_sum_base qz126) qz62) (ep369 (ep392 rfl) (ep396 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep398 := @ep333 45313034856280607151 1801439850948198400 5326250237948920141621 ep320 (ep364 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep365 Bool.true 157522543 26843545600 2767 80530636800 (BSN.stirling_sum_succ qz126 0 1 rfl) (ep397 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep399 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz137 2) Bool.false 23682752405293761 4503599627370496 250000000077777 11111000000000000000 Bool.false 853832695842211 281474976710656

noncomputable abbrev qz152 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz259 qz325 qz285))

noncomputable def ep400 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz137 2) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz137 1) qz152) Bool.false 23682752405293761 4503599627370496 250000000077777 11111000000000000000 Bool.false 853832695842211 281474976710656 500000000011111 11111000000000000000

noncomputable def ep401 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz137 1) qz152 Bool.false 23665177399118529 9007199254740992 250000000077777 22222000000000000000 Bool.false 874109236446627 562949953421312 500000000011111 22222000000000000000 Bool.false

noncomputable def ep402 := nat_lit 426630539630354799600715457101824

noncomputable def ep403 := nat_lit 961330152707931877233513201664

noncomputable abbrev qz153 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz259 qz325 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep404 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz137 1) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz137 0) qz153) Bool.false 23665177399118529 9007199254740992 250000000077777 22222000000000000000 Bool.false 874109236446627 562949953421312 500000000011111 22222000000000000000

noncomputable def ep405 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz137 0) qz153 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz340 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz134))

noncomputable def ep406 := @Enclosure.Complex.IsNear.of_eq qz153 qz340 Bool.false 23665177399118529 9007199254740992 250000000077777 22222000000000000000 Bool.false 874109236446627 562949953421312 500000000011111 22222000000000000000

noncomputable def ep407 := nat_lit 1872782931211029648364340058519821025718967930880000000000000

noncomputable def ep408 := nat_lit 25239944615390075133983859487111560318697598976000000000000

noncomputable def ep409 := nat_lit 16451702774273028581668499496426067891875840000000000000

noncomputable def ep410 := BSN.log_dyadic_bound 1015515600 5111515600 4 3 ep407 131072 44444 ep408 ep409 52782 6127031200 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 1015515600) (BSN.artanhQ 5111515600) 0 3 ep408 ep407 ep409 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep411 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 3063515600 16000000)) 1 2 0 1 23665177399118529 4503599627370496 250000000077777 11111000000000000000 23665177399118529 9007199254740992 250000000077777 22222000000000000000 qz33 (BSN.isNear_log_sfrac 3063515600 16000000 23665177399118529 4503599627370496 250000000077777 11111000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3063515600) qz276)) Bool.false 24814737056458110664704 4722366482869645213696 1000000000311108 44444000000000000000 23665177399118529 4503599627370496 250000000077777 11111000000000000000 (BSN.log_rat_reduce_isNear 3063515600 16000000 7 6127031200 4096000000 52782 131072 24973259072661432 36028797018963968 44444 1000000000000000 rfl rfl rfl rfl (ep410 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep412 := BSN.arctan_dyadic_bound_f 1000 55340 1 0 131072 44444 0 1 1 0 1 1 2368 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 55340) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 55340) 0 0 rfl) rfl rfl rfl

noncomputable def ep413 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz290 qz335)) 884279719003555 562949953421312 1 2000000000000000 2368 131072 1 44444 114571245839532294144 874109236446627 562949953421312 500000000011111 22222000000000000000 qz35 (ep412 rfl) rfl rfl

noncomputable abbrev qz154 := (@HAdd.hAdd Complex Complex Complex qz259 qz325 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz341 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz134)

noncomputable def ep414 := @ep405 23665177399118529 9007199254740992 250000000077777 22222000000000000000 Bool.false 874109236446627 562949953421312 500000000011111 22222000000000000000 Bool.false 23665177399118529 23665177399118529 9007199254740992 250000000077777 22222000000000000000 Bool.false 874109236446627 874109236446627 562949953421312 500000000011111 22222000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz137 0) (Complex.mk qz45 qz45) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz137) qz62) (ep406 (@congrArg Complex Complex qz154 qz341 Complex.log (BSN.w_shift_mk qz137 Bool.false 27670 1000 0 qz138 rfl)) (@Enclosure.Complex.IsNear.of_parts qz340 Bool.false 23665177399118529 9007199254740992 250000000077777 22222000000000000000 Bool.false 874109236446627 562949953421312 500000000011111 22222000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz340) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 3063515600 16000000))) Bool.false 23665177399118529 9007199254740992 250000000077777 22222000000000000000 (Enclosure.clog_re_eq 1000 55340 4000 3063515600 16000000 rfl rfl rfl) (ep411 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz340) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz335 qz290)) Bool.false 874109236446627 562949953421312 500000000011111 22222000000000000000 (Enclosure.clog_im_eq 1000 55340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz335 qz290)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz290 qz335))) Bool.false 874109236446627 562949953421312 500000000011111 22222000000000000000 (BSN.arctan_recip 55340 1000 rfl rfl) ep413)))) rfl rfl

noncomputable abbrev qz342 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz134))

noncomputable def ep415 := @Enclosure.Complex.IsNear.of_eq qz152 qz342 Bool.false 23700327411468993 9007199254740992 250000000077777 22222000000000000000 Bool.false 833556155237795 562949953421312 500000000011111 22222000000000000000

noncomputable def ep416 := nat_lit 1926165571094312575449936751605578889541099130880000000000000

noncomputable def ep417 := nat_lit 26972333878290649150512377853279033578995838976000000000000

noncomputable def ep418 := nat_lit 18926805801561563279149058683132191053475840000000000000

noncomputable def ep419 := BSN.log_dyadic_bound 1039515600 5135515600 4 3 ep416 131072 44444 ep417 ep418 53805 6175031200 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 1039515600) (BSN.artanhQ 5135515600) 0 3 ep417 ep416 ep418 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep420 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 3087515600 16000000)) 1 2 0 1 23700327411468993 4503599627370496 250000000077777 11111000000000000000 23700327411468993 9007199254740992 250000000077777 22222000000000000000 qz33 (BSN.isNear_log_sfrac 3087515600 16000000 23700327411468993 4503599627370496 250000000077777 11111000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3087515600) qz276)) Bool.false 24851594515808510803968 4722366482869645213696 1000000000311108 44444000000000000000 23700327411468993 4503599627370496 250000000077777 11111000000000000000 (BSN.log_rat_reduce_isNear 3087515600 16000000 7 6175031200 4096000000 53805 131072 24973259072661432 36028797018963968 44444 1000000000000000 rfl rfl rfl rfl (ep419 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep421 := BSN.arctan_dyadic_bound_f 5000 55340 1 0 131072 44444 0 1 1 0 1 1 11810 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 55340) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 55340) 0 0 rfl) rfl rfl rfl

noncomputable def ep422 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz293 qz335)) 884279719003555 562949953421312 1 2000000000000000 11810 131072 1 44444 109255872379328266240 833556155237795 562949953421312 500000000011111 22222000000000000000 qz35 (ep421 rfl) rfl rfl

noncomputable abbrev qz155 := (@HAdd.hAdd Complex Complex Complex qz259 qz325 qz285)

noncomputable abbrev qz343 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz134)

noncomputable def ep423 := @ep401 23700327411468993 9007199254740992 250000000077777 22222000000000000000 Bool.false 833556155237795 562949953421312 500000000011111 22222000000000000000 Bool.false ep402 23682752405293761 4503599627370496 250000000077777 11111000000000000000 Bool.false ep403 853832695842211 281474976710656 500000000011111 11111000000000000000 (ep404 (BSN.log_sum_c_succ qz137 0 1 rfl) (ep414 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep415 (@congrArg Complex Complex qz155 qz343 Complex.log (BSN.w_shift_mk qz137 Bool.false 27670 1000 1 qz138 rfl)) (@Enclosure.Complex.IsNear.of_parts qz342 Bool.false 23700327411468993 9007199254740992 250000000077777 22222000000000000000 Bool.false 833556155237795 562949953421312 500000000011111 22222000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz342) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 3087515600 16000000))) Bool.false 23700327411468993 9007199254740992 250000000077777 22222000000000000000 (Enclosure.clog_re_eq 5000 55340 4000 3087515600 16000000 rfl rfl rfl) (ep420 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz342) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz335 qz293)) Bool.false 833556155237795 562949953421312 500000000011111 22222000000000000000 (Enclosure.clog_im_eq 5000 55340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz335 qz293)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz293 qz335))) Bool.false 833556155237795 562949953421312 500000000011111 22222000000000000000 (BSN.arctan_recip 55340 5000 rfl rfl) ep422)))) rfl rfl

noncomputable def ep424 := @ep326 ep320 Bool.false 23682752405293761 4503599627370496 250000000077777 11111000000000000000 Bool.false 853832695842211 281474976710656 500000000011111 11111000000000000000 Bool.true ep327 19338308215257051969 900719925474099200 1712895056152005747913 ep324 Bool.false ep328 39848505602890456751 1801439850948198400 6555050237976226535221 ep320 (@ep329 900719925474099200 1610495056120148288713 ep324 Bool.false 45313034856280607151 1801439850948198400 5326250237948920141621 ep320 (BSN.logGammaStirling_unfold 1 qz126) (ep398 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep399 500000000011111 11111000000000000000 (BSN.log_sum_c_eq qz137 2) (ep400 (BSN.log_sum_c_succ qz137 1 2 rfl) (ep423 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz156 := (@HDiv.hDiv Real Real Real qz254 qz326 (2 : Real))

noncomputable def ep425 := @Enclosure.Real.IsNear.mulLit_ff qz156 (Real.log Real.pi) 27670 2000 0 1 75021 65536 1 32768 207583107 13107200 2767 6553600 (@Enclosure.Real.IsNear.of_eq qz156 (Enclosure.sfrac Bool.false 27670 2000) Bool.false 27670 2000 0 1 (BSN.t_half_eq qz137 Bool.false 27670 1000 qz138) (Enclosure.Real.IsNear.const Bool.false 27670 2000)) EMRow03.d5 rfl

noncomputable def ep426 := @ep322 2767 6553600 ep323 11318500618344259247 1801439850948198400 18084101612976226535221 ep320 (@ep325 6555050237976226535221 ep320 (ep424 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep425 rfl rfl

noncomputable def ep427 := nat_lit 497140415056404234682128590279333722365785711425011746362913801096767905

noncomputable def ep428 := nat_lit 998456871996347343458926812708431666508244176128389756812449109879201

noncomputable def ep429 := nat_lit 1300417871164493195135212807320536573974139706018441942772792180504111521

noncomputable def ep430 := BSN.sin_dyadic_bound_f 421615107 268435456 3 2 131072 44488 ep427 ep166 ep428 ep429 ep169 ep428 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 421615107) qz295 0 2 ep427 ep166 ep428 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 421615107) qz296 0 2 ep429 ep169 ep428 rfl rfl rfl rfl) rfl rfl

noncomputable def ep431 := @ep319 16384 Bool.false 131071 131072 1 22222 (@ep321 823529 131072 11 16384 ep426 rfl) (Enclosure.sfrac_false_div 823529 131072) (BSN.cos_reduce3 qz328 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29668525620069828395008) qz68) 226375608064910080 72057594037927936 Bool.false 131071 131072 0 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q3 823529 131072 226375608064910080 72057594037927936 0 29668525620069828395008 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131071 131072 29668525620069828395008 18889465931478580854784 421615107 268435456 44488 44444 (ep430 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz402 := (@Neg.neg Complex Complex.instNeg qz413)

noncomputable abbrev qz344 := qz402

noncomputable abbrev qz157 := qz344

noncomputable abbrev qz345 := (@HPow.hPow Complex Complex Complex qz394 (@Nat.cast Complex Complex.instNatCast 6) qz402)

noncomputable abbrev qz158 := qz345

noncomputable abbrev qz346 := (@Nat.cast Complex Complex.instNatCast 6)

noncomputable abbrev qz159 := (@HAdd.hAdd Complex Complex Complex qz259 (@HDiv.hDiv Complex Complex Complex qz267 qz346 (@HSub.hSub Complex Complex Complex qz257 qz327 (1 : Complex))) qz266)

noncomputable abbrev qz160 := qz346

noncomputable def ep432 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz124 1 6) (@HAdd.hAdd Complex Complex Complex qz8 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 6, @HPow.hPow Complex Complex Complex qz69 (@Nat.cast Complex Complex.instNatCast n) qz157) (@HMul.hMul Complex Complex Complex qz4 qz158 (@HAdd.hAdd Complex Complex Complex qz8 qz159 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) Bool.false 271303065653089262231 94735435052057886720 17341571785539962172949

noncomputable def ep433 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 6, @HPow.hPow Complex Complex Complex qz69 (@Nat.cast Complex Complex.instNatCast n) qz157) (@HMul.hMul Complex Complex Complex qz4 qz158 (@HAdd.hAdd Complex Complex Complex qz8 qz159 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) Bool.false 47219485369 17179869184 559784202421 190885526503424

noncomputable def ep434 := nat_lit 4660951177138237050603651989504

noncomputable def ep435 := nat_lit 154564763571808232807738638336

noncomputable def ep436 := @ep433 Bool.true 4779043701 17179869184 557708423179 190885526503424 Bool.false 10919331559663400711 94735435052057886720 1907403054787340764549 ep317 Bool.false 17356361528813351051 94735435052057886720 1903687850567345177531 ep317 Bool.false ep434 271303065653089262231 94735435052057886720 17341571785539962172949 ep317 Bool.true ep435 8996853347158073029 94735435052057886720

noncomputable def ep437 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 6, @HPow.hPow Complex Complex Complex qz69 (@Nat.cast Complex Complex.instNatCast n) qz157) (BSN.headSumC qz124 6) Bool.false 47219485369 17179869184 559784202421 190885526503424 Bool.true 4779043701 17179869184 557708423179

noncomputable abbrev qz161 := (BSN.headSumC qz327 5)

noncomputable abbrev qz162 := (@HPow.hPow Complex Complex Complex qz297 qz300 qz344)

noncomputable def ep438 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz124 6) (@HAdd.hAdd Complex Complex Complex qz8 qz161 qz162) Bool.false 47219485369 17179869184 559784202421 190885526503424 Bool.true 4779043701 17179869184 557708423179 190885526503424

noncomputable def ep439 := @Enclosure.Complex.IsNear.addLitP qz161 qz162 Bool.false 20336364245 8589934592 223618200123 95442763251712 Bool.true 758034735 17179869184 445639382883 190885526503424 Bool.false

noncomputable abbrev qz163 := (BSN.headSumC qz327 4)

noncomputable abbrev qz164 := (@HPow.hPow Complex Complex Complex qz297 (@Nat.cast Complex Complex.instNatCast 4) qz344)

noncomputable def ep440 := @Enclosure.Complex.IsNear.of_eq qz161 (@HAdd.hAdd Complex Complex Complex qz8 qz163 qz164) Bool.false 20336364245 8589934592 223618200123 95442763251712 Bool.true 758034735 17179869184 445639382883 190885526503424

noncomputable def ep441 := @Enclosure.Complex.IsNear.addLitP qz163 qz164 Bool.false 16942306595 8589934592 161185297113 95442763251712 Bool.false 1126384965 4294967296 40129006507 23860690812928 Bool.false

noncomputable abbrev qz165 := (BSN.headSumC qz327 3)

noncomputable abbrev qz166 := (@HPow.hPow Complex Complex Complex qz297 qz302 qz344)

noncomputable def ep442 := @Enclosure.Complex.IsNear.of_eq qz163 (@HAdd.hAdd Complex Complex Complex qz8 qz165 qz166) Bool.false 16942306595 8589934592 161185297113 95442763251712 Bool.false 1126384965 4294967296 40129006507 23860690812928

noncomputable def ep443 := @Enclosure.Complex.IsNear.addLitP qz165 qz166 Bool.false 1792073665 1073741824 44687202965 47721381625856 Bool.true 1966943745 8589934592 88468159437 95442763251712 Bool.false

noncomputable abbrev qz167 := (BSN.headSumC qz327 2)

noncomputable abbrev qz168 := (@HPow.hPow Complex Complex Complex qz297 qz303 qz344)

noncomputable def ep444 := @Enclosure.Complex.IsNear.of_eq qz165 (@HAdd.hAdd Complex Complex Complex qz8 qz167 qz168) Bool.false 1792073665 1073741824 44687202965 47721381625856 Bool.true 1966943745 8589934592 88468159437 95442763251712

noncomputable def ep445 := @Enclosure.Complex.IsNear.addLitP qz167 qz168 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep446 := @Enclosure.Complex.IsNear.of_eq qz167 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz45) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz124)

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz250 qz326 qz304)

noncomputable abbrev qz170 := (Real.sin (@HMul.hMul Real Real Real qz250 qz326 qz304))

noncomputable def ep447 := @Enclosure.Complex.IsNear.of_eq qz168 (Complex.mk (@HMul.hMul Real Real Real qz0 qz82 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz82 (@Neg.neg Real Real.instNeg qz170))) Bool.false 718331841 1073741824 44687202965 47721381625856 Bool.true 1966943745 8589934592 88468159437 95442763251712 (BSN.cpow_neg_s_mk qz137 27670 1000 2 qz138 rfl)

noncomputable def ep448 := nat_lit 61412963159365318301862893998336

noncomputable def ep449 := BSN.cos_dyadic_bound_f 88524812 268435456 2 1 131072 44488 ep448 ep189 ep448 ep448 ep190 ep448 124008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 88524812) qz306 0 1 ep448 ep189 ep448 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 88524812) qz307 0 1 ep448 ep190 ep448 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz347 := (Enclosure.Real.IsNear.const Bool.false 27670 1000)

noncomputable abbrev qz171 := qz347

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1256937) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz349 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep450 := @Enclosure.Real.IsNear.cos_image qz169 qz348 Bool.false 1256937 65536 165 131072 Bool.false 124008 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 62846871 3276800 2767 2222200 1256937 65536 165 131072 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz87 27670 1000 0 1 45426 65536 1 22222 62846871 3276800 2767 2222200 qz171 qz310 rfl) rfl) (Enclosure.sfrac_false_div 1256937 65536) (BSN.cos_reduce0 qz348 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3114689952798688149504) qz349) 226375608064910080 72057594037927936 Bool.false 124008 131072 3 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q0 1256937 65536 226375608064910080 72057594037927936 3 3114689952798688149504 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 124008 131072 3114689952798688149504 9444732965739290427392 88524812 268435456 44488 44444 (ep449 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep451 := BSN.sin_dyadic_bound_f 88524812 268435456 2 1 131072 44488 ep448 ep193 ep448 ep448 ep194 ep448 42445 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 88524812) qz295 0 1 ep448 ep193 ep448 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 88524812) qz296 0 1 ep448 ep194 ep448 rfl rfl rfl rfl) rfl rfl

noncomputable def ep452 := @Enclosure.Real.IsNear.sin_image qz169 qz348 Bool.false 1256937 65536 165 131072 Bool.false 42445 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 62846871 3276800 2767 2222200 1256937 65536 165 131072 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz87 27670 1000 0 1 45426 65536 1 22222 62846871 3276800 2767 2222200 qz171 qz310 rfl) rfl) (Enclosure.sfrac_false_div 1256937 65536) (BSN.sin_reduce0 qz348 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3114689952798688149504) qz349) 226375608064910080 72057594037927936 Bool.false 42445 131072 3 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q0 1256937 65536 226375608064910080 72057594037927936 3 3114689952798688149504 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 42445 131072 3114689952798688149504 9444732965739290427392 88524812 268435456 44488 44444 (ep451 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep453 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz82 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz82 (@Neg.neg Real Real.instNeg qz170)) Bool.false 718331841 1073741824 44687202965 47721381625856 Bool.true 1966943745 8589934592 88468159437 95442763251712 (@Enclosure.Real.IsNear.mulLit_ff qz82 (Real.cos qz169) 46341 65536 1 65536 15501 16384 1898851 1456340992 718331841 1073741824 44687202965 47721381625856 qz89 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 124008 131072 3797702 2912681984 15501 16384 1898851 1456340992 (ep450 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz82 (@Neg.neg Real Real.instNeg qz170) 46341 65536 1 65536 42445 131072 1898851 1456340992 1966943745 8589934592 88468159437 95442763251712 qz89 (@Enclosure.Real.IsNear.neg qz170 Bool.false 42445 131072 1898851 1456340992 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 42445 131072 3797702 2912681984 42445 131072 1898851 1456340992 (ep452 rfl rfl) rfl)) rfl)

noncomputable def ep454 := @ep445 718331841 1073741824 44687202965 47721381625856 Bool.true 1966943745 8589934592 88468159437 95442763251712 Bool.false 1792073665 1792073665 1073741824 44687202965 47721381625856 Bool.true 1966943745 1966943745 8589934592 88468159437 95442763251712 (ep446 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz45 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz46)) (ep447 ep453) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz250 qz326 qz312)

noncomputable abbrev qz173 := (Real.sin (@HMul.hMul Real Real Real qz250 qz326 qz312))

noncomputable def ep455 := @Enclosure.Complex.IsNear.of_eq qz166 (Complex.mk (@HMul.hMul Real Real Real qz0 qz90 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz90 (@Neg.neg Real Real.instNeg qz173))) Bool.false 2605717275 8589934592 71810891183 95442763251712 Bool.false 4219713675 8589934592 72047866591 95442763251712 (BSN.cpow_neg_s_mk qz137 27670 1000 3 qz138 rfl)

noncomputable def ep456 := nat_lit 486256854316453644583659398850576

noncomputable def ep457 := BSN.sin_dyadic_bound_f 148496574 268435456 2 1 131072 44488 ep456 ep193 ep456 ep456 ep194 ep456 68866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 148496574) qz295 0 1 ep456 ep193 ep456 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 148496574) qz296 0 1 ep456 ep194 ep456 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz350 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3984369) qz12)

noncomputable def ep458 := @Enclosure.Real.IsNear.cos_image qz172 qz350 Bool.false 3984369 131072 41 32768 Bool.false 68866 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 99609233 3276800 2767 2222200 3984369 131072 41 32768 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz95 27670 1000 0 1 71998 65536 1 22222 99609233 3276800 2767 2222200 qz171 qz314 rfl) rfl) (Enclosure.sfrac_false_div 3984369 131072) (BSN.cos_reduce3 qz350 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10449517493215798755328) qz68) 226375608064910080 72057594037927936 Bool.false 68866 131072 4 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q3 3984369 131072 226375608064910080 72057594037927936 4 10449517493215798755328 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 68866 131072 10449517493215798755328 18889465931478580854784 148496574 268435456 44488 44444 (ep457 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep459 := BSN.cos_dyadic_bound_f 148496574 268435456 2 1 131072 44488 ep456 ep189 ep456 ep456 ep190 ep456 111522 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 148496574) qz306 0 1 ep456 ep189 ep456 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 148496574) qz307 0 1 ep456 ep190 ep456 rfl rfl rfl rfl) rfl rfl

noncomputable def ep460 := @Enclosure.Real.IsNear.sin_image qz172 qz350 Bool.false 3984369 131072 41 32768 Bool.true 111522 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 99609233 3276800 2767 2222200 3984369 131072 41 32768 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz95 27670 1000 0 1 71998 65536 1 22222 99609233 3276800 2767 2222200 qz171 qz314 rfl) rfl) (Enclosure.sfrac_false_div 3984369 131072) (BSN.sin_reduce3 qz350 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10449517493215798755328) qz68) 226375608064910080 72057594037927936 Bool.false 111522 131072 4 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q3 3984369 131072 226375608064910080 72057594037927936 4 10449517493215798755328 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 111522 131072 10449517493215798755328 18889465931478580854784 148496574 268435456 44488 44444 (ep459 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep461 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz90 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz90 (@Neg.neg Real Real.instNeg qz173)) Bool.false 2605717275 8589934592 71810891183 95442763251712 Bool.false 4219713675 8589934592 72047866591 95442763251712 (@Enclosure.Real.IsNear.mulLit_ff qz90 (Real.cos qz172) 75675 131072 1 131072 34433 65536 471935 364085248 2605717275 8589934592 71810891183 95442763251712 qz96 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 68866 131072 943870 728170496 34433 65536 471935 364085248 (ep458 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz90 (@Neg.neg Real Real.instNeg qz173) 75675 131072 1 131072 55761 65536 471935 364085248 4219713675 8589934592 72047866591 95442763251712 qz96 (@Enclosure.Real.IsNear.neg qz173 Bool.true 55761 65536 471935 364085248 (@Enclosure.Real.IsNear.recentre' qz173 Bool.true 111522 131072 943870 728170496 55761 65536 471935 364085248 (ep460 rfl rfl) rfl)) rfl)

noncomputable def ep462 := @ep443 2605717275 8589934592 71810891183 95442763251712 Bool.false 4219713675 8589934592 72047866591 95442763251712 Bool.false 18191663186082529280 16942306595 8589934592 161185297113 95442763251712 Bool.false 19351146349524418560 1126384965 4294967296 40129006507 23860690812928 (ep444 (BSN.head_sum_c_succ qz124 2 3 rfl rfl) (ep454 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep455 ep461) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz250 qz326 qz315)

noncomputable abbrev qz175 := (Real.sin (@HMul.hMul Real Real Real qz250 qz326 qz315))

noncomputable def ep463 := @Enclosure.Complex.IsNear.of_eq qz164 (Complex.mk (@HMul.hMul Real Real Real qz0 qz97 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz97 (@Neg.neg Real Real.instNeg qz175))) Bool.false 1697028825 4294967296 31216451505 47721381625856 Bool.true 5263574595 17179869184 124607330827 190885526503424 (BSN.cpow_neg_s_mk qz137 27670 1000 4 qz138 rfl)

noncomputable def ep464 := nat_lit 982652898306103400820708282947041

noncomputable def ep465 := BSN.cos_dyadic_bound_f 177051673 268435456 2 1 131072 44488 ep464 ep189 ep464 ep464 ep190 ep464 103580 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 177051673) qz306 0 1 ep464 ep189 ep464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 177051673) qz307 0 1 ep464 ep190 ep464 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5027749) qz12)

noncomputable def ep466 := @Enclosure.Real.IsNear.cos_image qz174 qz351 Bool.false 5027749 131072 41 32768 Bool.false 103580 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 62846871 1638400 2767 2222200 5027749 131072 41 32768 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz102 27670 1000 0 1 90852 65536 1 22222 62846871 1638400 2767 2222200 qz171 qz317 rfl) rfl) (Enclosure.sfrac_false_div 5027749 131072) (BSN.cos_reduce0 qz351 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12458903926382828453888) qz68) 226375608064910080 72057594037927936 Bool.false 103580 131072 6 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q0 5027749 131072 226375608064910080 72057594037927936 6 12458903926382828453888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 103580 131072 12458903926382828453888 18889465931478580854784 177051673 268435456 44488 44444 (ep465 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep467 := BSN.sin_dyadic_bound_f 177051673 268435456 2 1 131072 44488 ep464 ep193 ep464 ep464 ep194 ep464 80317 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 177051673) qz295 0 1 ep464 ep193 ep464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 177051673) qz296 0 1 ep464 ep194 ep464 rfl rfl rfl rfl) rfl rfl

noncomputable def ep468 := @Enclosure.Real.IsNear.sin_image qz174 qz351 Bool.false 5027749 131072 41 32768 Bool.false 80317 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 62846871 1638400 2767 2222200 5027749 131072 41 32768 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz102 27670 1000 0 1 90852 65536 1 22222 62846871 1638400 2767 2222200 qz171 qz317 rfl) rfl) (Enclosure.sfrac_false_div 5027749 131072) (BSN.sin_reduce0 qz351 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12458903926382828453888) qz68) 226375608064910080 72057594037927936 Bool.false 80317 131072 6 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q0 5027749 131072 226375608064910080 72057594037927936 6 12458903926382828453888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 80317 131072 12458903926382828453888 18889465931478580854784 177051673 268435456 44488 44444 (ep467 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep469 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz97 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz97 (@Neg.neg Real Real.instNeg qz175)) Bool.false 1697028825 4294967296 31216451505 47721381625856 Bool.true 5263574595 17179869184 124607330827 190885526503424 (@Enclosure.Real.IsNear.mulLit_ff qz97 (Real.cos qz174) 65535 131072 1 131072 25895 32768 471935 364085248 1697028825 4294967296 31216451505 47721381625856 qz103 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 103580 131072 943870 728170496 25895 32768 471935 364085248 (ep466 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz97 (@Neg.neg Real Real.instNeg qz175) 65535 131072 1 131072 80317 131072 471935 364085248 5263574595 17179869184 124607330827 190885526503424 qz103 (@Enclosure.Real.IsNear.neg qz175 Bool.false 80317 131072 471935 364085248 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 80317 131072 943870 728170496 80317 131072 471935 364085248 (ep468 rfl rfl) rfl)) rfl)

noncomputable def ep470 := @ep441 1697028825 4294967296 31216451505 47721381625856 Bool.true 5263574595 17179869184 124607330827 190885526503424 Bool.false 87344019351818731520 20336364245 8589934592 223618200123 95442763251712 Bool.true 3255734396057026560 758034735 17179869184 445639382883 190885526503424 (ep442 (BSN.head_sum_c_succ qz124 3 4 rfl rfl) (ep462 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep463 ep469) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz250 qz326 qz319)

noncomputable abbrev qz177 := (Real.sin (@HMul.hMul Real Real Real qz250 qz326 qz319))

noncomputable def ep471 := @Enclosure.Complex.IsNear.of_eq qz162 (Complex.mk (@HMul.hMul Real Real Real qz0 qz106 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz106 (@Neg.neg Real Real.instNeg qz177))) Bool.false 6546756879 17179869184 112547802175 190885526503424 Bool.true 2010504483 8589934592 14008630037 23860690812928 (BSN.cpow_neg_s_mk qz137 27670 1000 5 qz138 rfl)

noncomputable def ep472 := nat_lit 477868641649381241223108600139776

noncomputable def ep473 := BSN.cos_dyadic_bound_f 147851976 268435456 2 1 131072 44488 ep472 ep189 ep472 ep472 ep190 ep472 111687 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 147851976) qz306 0 1 ep472 ep189 ep472 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 147851976) qz307 0 1 ep472 ep190 ep472 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5837041) qz12)

noncomputable def ep474 := @Enclosure.Real.IsNear.cos_image qz176 qz352 Bool.false 5837041 131072 165 131072 Bool.false 111687 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 72963023 1638400 2767 2222200 5837041 131072 165 131072 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz112 27670 1000 0 1 105476 65536 1 22222 72963023 1638400 2767 2222200 qz171 qz321 rfl) rfl) (Enclosure.sfrac_false_div 5837041 131072) (BSN.cos_reduce0 qz352 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10404157913532802793472) qz68) 226375608064910080 72057594037927936 Bool.false 111687 131072 7 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q0 5837041 131072 226375608064910080 72057594037927936 7 10404157913532802793472 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 111687 131072 10404157913532802793472 18889465931478580854784 147851976 268435456 44488 44444 (ep473 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep475 := BSN.sin_dyadic_bound_f 147851976 268435456 2 1 131072 44488 ep472 ep193 ep472 ep472 ep194 ep472 68598 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 147851976) qz295 0 1 ep472 ep193 ep472 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 147851976) qz296 0 1 ep472 ep194 ep472 rfl rfl rfl rfl) rfl rfl

noncomputable def ep476 := @Enclosure.Real.IsNear.sin_image qz176 qz352 Bool.false 5837041 131072 165 131072 Bool.false 68598 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 72963023 1638400 2767 2222200 5837041 131072 165 131072 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz112 27670 1000 0 1 105476 65536 1 22222 72963023 1638400 2767 2222200 qz171 qz321 rfl) rfl) (Enclosure.sfrac_false_div 5837041 131072) (BSN.sin_reduce0 qz352 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10404157913532802793472) qz68) 226375608064910080 72057594037927936 Bool.false 68598 131072 7 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q0 5837041 131072 226375608064910080 72057594037927936 7 10404157913532802793472 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 68598 131072 10404157913532802793472 18889465931478580854784 147851976 268435456 44488 44444 (ep475 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep477 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz106 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz106 (@Neg.neg Real Real.instNeg qz177)) Bool.false 6546756879 17179869184 112547802175 190885526503424 Bool.true 2010504483 8589934592 14008630037 23860690812928 (@Enclosure.Real.IsNear.mulLit_ff qz106 (Real.cos qz176) 58617 131072 1 131072 111687 131072 1898851 1456340992 6546756879 17179869184 112547802175 190885526503424 qz113 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.false 111687 131072 3797702 2912681984 111687 131072 1898851 1456340992 (ep474 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz106 (@Neg.neg Real Real.instNeg qz177) 58617 131072 1 131072 34299 65536 1898851 1456340992 2010504483 8589934592 14008630037 23860690812928 qz113 (@Enclosure.Real.IsNear.neg qz177 Bool.false 34299 65536 1898851 1456340992 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 68598 131072 3797702 2912681984 34299 65536 1898851 1456340992 (ep476 rfl rfl) rfl)) rfl)

noncomputable def ep478 := @ep439 6546756879 17179869184 112547802175 190885526503424 Bool.true 2010504483 8589934592 14008630037 23860690812928 Bool.false 405612290787610984448 47219485369 17179869184 559784202421 190885526503424 Bool.true 41051672803899604992 4779043701 17179869184 557708423179 190885526503424 (ep440 (BSN.head_sum_c_succ qz124 4 5 rfl rfl) (ep470 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep471 ep477) rfl rfl

noncomputable def ep479 := @Enclosure.Complex.IsNear.mul qz158 (@HAdd.hAdd Complex Complex Complex qz8 qz159 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 10919331559663400711 94735435052057886720 1907403054787340764549 ep317 Bool.false

noncomputable abbrev qz178 := (Complex.re qz345)

noncomputable abbrev qz179 := (Complex.im qz345)

noncomputable def ep480 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz178 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz159 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz179 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz159 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 167027312116751955 1052615945022865408 28644888120897308639

noncomputable def ep481 := nat_lit 11493862508693089392521916894924505088

noncomputable def ep482 := @Enclosure.Real.IsNear.mulLit_ff qz178 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz159 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2709666135 8589934592 51633660187 95442763251712 554771597

noncomputable abbrev qz353 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz400 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable abbrev qz180 := (Real.cos qz353)

noncomputable abbrev qz181 := (@Neg.neg Real Real.instNeg (Real.sin qz353))

noncomputable abbrev qz354 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable def ep483 := @Enclosure.Complex.IsNear.of_eq qz158 (Complex.mk (@HMul.hMul Real Real Real qz0 qz354 qz180) (@HMul.hMul Real Real Real qz0 qz354 qz181)) Bool.false 2709666135 8589934592 51633660187 95442763251712 Bool.false 2226096265 8589934592 51432839973 95442763251712 (BSN.cpow_neg_s_mk qz137 27670 1000 6 qz138 rfl)

noncomputable abbrev qz355 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable abbrev qz356 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1))

noncomputable def ep484 := @Enclosure.Real.IsNear.inv_image qz355 321059 131072 1 131072 26754 26756 65536 (@Enclosure.Real.IsNear.of_eq qz355 (Real.sqrt qz356) Bool.false 321059 131072 1 131072 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz356) Bool.false 321059 131072 1 131072 321059 131072 1 131072 (BSN.sqrt_enclosure 6 1 160529 160530 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep485 := BSN.log_dyadic_bound 2 10 4 3 105000000 65536 22222 1434560 960 26572 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz357 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz182 := qz357

noncomputable def ep486 := @Enclosure.Real.IsNear.mulLit_ff qz137 qz182 27670 1000 0 1 4034664351997175 2251799813685248 250000000011111 5555500000000000000 446556650479047329 9007199254740992 691750000030744137 555550000000000000000 qz171 (BSN.isNear_log_sfrac 6 1 4034664351997175 2251799813685248 250000000011111 5555500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz356) Bool.false 4230652207559789772800 2361183241434822606848 1000000000044444 22222000000000000000 4034664351997175 2251799813685248 250000000011111 5555500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 26572 65536 24973259072661432 36028797018963968 22222 1000000000000000 rfl rfl rfl rfl (ep485 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep487 := nat_lit 3157295606250945252252667066200625

noncomputable def ep488 := BSN.sin_dyadic_bound_f 237043915 268435456 2 1 131072 44488 ep487 ep193 ep487 ep487 ep194 ep487 101277 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 237043915) qz295 0 1 ep487 ep193 ep487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 237043915) qz296 0 1 ep487 ep194 ep487 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz183 := qz353

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3249127) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep489 := @Enclosure.Real.IsNear.cos_image qz183 qz358 Bool.false 3249127 65536 41 32768 Bool.false 101277 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 446556650479047329 9007199254740992 691750000030744137 555550000000000000000 3249127 65536 41 32768 (ep486 rfl) rfl) (Enclosure.sfrac_false_div 3249127 65536) (BSN.cos_reduce3 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8340241332941004734464) qz349) 226375608064910080 72057594037927936 Bool.false 101277 131072 7 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q3 3249127 65536 226375608064910080 72057594037927936 7 8340241332941004734464 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 101277 131072 8340241332941004734464 9444732965739290427392 237043915 268435456 44488 44444 (ep488 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep490 := nat_lit 27551243492653614676217612948851793167180690899285077476037910587190625

noncomputable def ep491 := nat_lit 9968515545251523920630788179420443559170973692707431016272750390625

noncomputable def ep492 := nat_lit 82633793446870340980811577270196538614423730750469817566081186260790625

noncomputable def ep493 := BSN.cos_dyadic_bound_f 237043915 268435456 3 2 131072 44488 ep490 ep236 ep491 ep492 ep238 ep491 83203 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 237043915) qz306 0 2 ep490 ep236 ep491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 237043915) qz307 0 2 ep492 ep238 ep491 rfl rfl rfl rfl) rfl rfl

noncomputable def ep494 := @Enclosure.Real.IsNear.sin_image qz183 qz358 Bool.false 3249127 65536 41 32768 Bool.true 83203 131072 1 22222 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 446556650479047329 9007199254740992 691750000030744137 555550000000000000000 3249127 65536 41 32768 (ep486 rfl) rfl) (Enclosure.sfrac_false_div 3249127 65536) (BSN.sin_reduce3 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8340241332941004734464) qz349) 226375608064910080 72057594037927936 Bool.false 83203 131072 7 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q3 3249127 65536 226375608064910080 72057594037927936 7 8340241332941004734464 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 83203 131072 8340241332941004734464 9444732965739290427392 237043915 268435456 44488 44444 (ep493 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz184 := (Real.sin qz353)

noncomputable def ep495 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz354 qz180) (@HMul.hMul Real Real Real qz0 qz354 qz181) Bool.false 2709666135 8589934592 51633660187 95442763251712 Bool.false 2226096265 8589934592 51432839973 95442763251712 (@Enclosure.Real.IsNear.mulLit_ff qz354 qz180 26755 65536 1 65536 101277 131072 471935 364085248 2709666135 8589934592 51633660187 95442763251712 (@Enclosure.Real.IsNear.recentre' qz354 Bool.false 53510 131072 2 131072 26755 65536 1 65536 (ep484 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 101277 131072 943870 728170496 101277 131072 471935 364085248 (ep489 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz354 qz181 26755 65536 1 65536 83203 131072 471935 364085248 2226096265 8589934592 51432839973 95442763251712 (@Enclosure.Real.IsNear.recentre' qz354 Bool.false 53510 131072 2 131072 26755 65536 1 65536 (ep484 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz184 Bool.true 83203 131072 471935 364085248 (@Enclosure.Real.IsNear.recentre' qz184 Bool.true 83203 131072 943870 728170496 83203 131072 471935 364085248 (ep494 rfl rfl) rfl)) rfl)

noncomputable def ep496 := @ep482 1102865616 0 1 167027312116751955 1052615945022865408 28644888120897308639 105260541886341517934592 (@Enclosure.Complex.IsNear.re_isNear qz158 Bool.false 2709666135 8589934592 51633660187 95442763251712 Bool.false 2226096265 8589934592 51432839973 95442763251712 (ep483 ep495))

noncomputable def ep497 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz159 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 554771597 1102865616 0 1 Bool.false

noncomputable def ep498 := @Enclosure.Complex.IsNear.addLitP qz159 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) Bool.false 7598789 15317578 0 1 Bool.true 1660200

noncomputable def ep499 := @ep498 7658789 0 1 Bool.false 1 144 0 1 Bool.false 2767 7200 0 1 Bool.false 1109543194 554771597 1102865616 0 1 Bool.false 9238429163 9238429163 55143280800 0 1

noncomputable abbrev qz185 := (@HDiv.hDiv Complex Complex Complex qz267 qz346 (@HSub.hSub Complex Complex Complex qz257 qz327 (1 : Complex)))

noncomputable def ep500 := @Enclosure.Complex.IsNear.addLitP qz185 qz42 Bool.true 12000000 3063515600 0 1 Bool.true 664080000 3063515600 0 1

noncomputable def ep501 := @Enclosure.Complex.IsNear.of_eq qz185 (Complex.mk (Enclosure.sfrac Bool.true 12000000 3063515600) (Enclosure.sfrac Bool.true 664080000 3063515600)) Bool.true 12000000 3063515600 0 1 Bool.true 664080000 3063515600 0 1

noncomputable def ep502 := @ep500 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 3039515600 7598789 15317578 0 1 Bool.true 664080000 1660200 7658789 0 1 (ep501 (BSN.N_div_s_sub_one_mk qz137 27670 1000 6 qz138 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 12000000 3063515600) (Enclosure.sfrac Bool.true 664080000 3063515600) Bool.true 12000000 3063515600 0 1 Bool.true 664080000 3063515600 0 1 (Enclosure.Real.IsNear.const Bool.true 12000000 3063515600) (Enclosure.Real.IsNear.const Bool.true 664080000 3063515600))) qz44 rfl

noncomputable abbrev qz359 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz393 (@Nat.cast Complex Complex.instNatCast 6) 1))

noncomputable abbrev qz186 := qz359

noncomputable def ep503 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz186)) Bool.false 1 144 0 1

noncomputable def ep504 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz186) Bool.false 0 1 0 1 Bool.false

noncomputable def ep505 := @ep504 0 1 0 1 Bool.false 1 144 0 1 Bool.false 2767 7200 0 1 Bool.false 1 1 144 0 1 Bool.false 2767 2767 7200 0

noncomputable def ep506 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (Complex.mk qz45 qz45) Bool.false 0 1 0 1 Bool.false

noncomputable def ep507 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz186 Bool.false 1 144 0 1 Bool.false 2767 7200 0 1

noncomputable abbrev qz187 := (Complex.re qz359)

noncomputable abbrev qz188 := (Complex.im qz359)

noncomputable def ep508 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz187) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz188) 1 144 0 1 0 1 0

noncomputable def ep509 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz187 1 24 0 1 1 6 0 1 1

noncomputable def ep510 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep511 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep512 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) qz124 Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 (BSN.ascPochhammer_one_eval qz124)

noncomputable def ep513 := ep512 (@Enclosure.Complex.IsNear.of_eq qz124 (Complex.mk qz32 qz137) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 (BSN.s_crit_mk qz137 Bool.false 27670 1000 qz138) (@Enclosure.Complex.IsNear.mk qz32 qz137 Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 qz33 qz171))

noncomputable def ep514 := @ep511 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep258) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep513)

noncomputable def ep515 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 27670 1000 0 1 0 1 0

noncomputable def ep516 := @ep515 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep258) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep513)

noncomputable def ep517 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) 2767 1200 0 1 0 1 0 1 2767

noncomputable def ep518 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 27670 1000 0 1 2767 1200 0

noncomputable def ep519 := @ep518 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep258) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep513)

noncomputable def ep520 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep521 := @ep520 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep258) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep513)

noncomputable def ep522 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 2767 1200 0 1 (@ep510 1 24 0 1 (ep514 rfl) (ep516 rfl) rfl rfl) (@ep517 2767 1200 0 1 (ep519 rfl) (ep521 rfl) rfl rfl)

noncomputable def ep523 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2767 1200 0 1 ep522

noncomputable abbrev qz189 := (@Enclosure.Complex.IsNear.of_eq qz359 (Complex.mk (Enclosure.sfrac Bool.false 1 6) qz283) Bool.false 1 6 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 6 1 6 EMRow03.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 6) qz283 Bool.false 1 6 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 6) qz284))

noncomputable def ep524 := @ep509 144 0 1 ep523 (@Enclosure.Complex.IsNear.re_isNear qz186 Bool.false 1 6 0 1 Bool.false 0 1 0 1 qz189)

noncomputable def ep525 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz188 2767 1200 0 1 0 1 0 1 0

noncomputable def ep526 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2767 1200 0 1 ep522

noncomputable def ep527 := @ep525 1 0 1 ep526 (@Enclosure.Complex.IsNear.im_isNear qz186 Bool.false 1 6 0 1 Bool.false 0 1 0 1 qz189)

noncomputable def ep528 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz188) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz187) 0 1 0 1 2767 7200 0

noncomputable def ep529 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz188 1 24 0 1 0 1 0 1 0

noncomputable def ep530 := @ep529 1 0 1 ep523 (@Enclosure.Complex.IsNear.im_isNear qz186 Bool.false 1 6 0 1 Bool.false 0 1 0 1 qz189)

noncomputable def ep531 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz47)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz187 2767 1200 0 1 1 6 0 1 2767

noncomputable def ep532 := @ep531 7200 0 1 ep526 (@Enclosure.Complex.IsNear.re_isNear qz186 Bool.false 1 6 0 1 Bool.false 0 1 0 1 qz189)

noncomputable def ep533 := @ep505 1 (@ep506 0 1 0 1 (BSN.bern_sum_base qz124 6) qz62) (ep507 (@ep508 1 1 1 144 0 1 (ep524 rfl) (ep527 rfl) rfl rfl) (@ep528 1 2767 2767 7200 0 1 (ep530 rfl) (ep532 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep534 := ep499 (ep502 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep503 Bool.false 2767 7200 0 1 (BSN.bern_sum_succ qz124 6 0 1 1 rfl rfl) (ep533 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep535 := @Enclosure.Real.IsNear.mulLit_ff qz179 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz159 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2226096265 8589934592 51432839973 95442763251712 9238429163

noncomputable def ep536 := @ep535 55143280800 0 1 4113126530844275239 94735435052057886720 52795405415830592511 584780788257452877414400 (@Enclosure.Complex.IsNear.im_isNear qz158 Bool.false 2709666135 8589934592 51633660187 95442763251712 Bool.false 2226096265 8589934592 51432839973 95442763251712 (ep483 ep495))

noncomputable def ep537 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz159 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 554771597 1102865616 0 1 Bool.false

noncomputable def ep538 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz178 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz159 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz179 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz159 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 556290192079499889 10526159450228654080 477013912064012833481

noncomputable def ep539 := nat_lit 18269582892810370532916929222628343808

noncomputable def ep540 := @Enclosure.Real.IsNear.mulLit_ff qz178 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz159 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2709666135 8589934592 51633660187 95442763251712 9238429163

noncomputable def ep541 := @ep540 55143280800 0 1 556290192079499889 10526159450228654080 477013912064012833481 ep317 (@Enclosure.Complex.IsNear.re_isNear qz158 Bool.false 2709666135 8589934592 51633660187 95442763251712 Bool.false 2226096265 8589934592 51432839973 95442763251712 (ep483 ep495))

noncomputable def ep542 := @Enclosure.Real.IsNear.mulLit_ff qz179 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz159 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz74 qz160 (@HSub.hSub Nat Nat Nat qz73 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2226096265 8589934592 51432839973 95442763251712 554771597

noncomputable def ep543 := @ep542 1102865616 0 1 1234974980009785205 9473543505205788672 3170386530007405209 11695615765149057548288 (@Enclosure.Complex.IsNear.im_isNear qz158 Bool.false 2709666135 8589934592 51633660187 95442763251712 Bool.false 2226096265 8589934592 51432839973 95442763251712 (ep483 ep495))

noncomputable abbrev qz360 := (ep534 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep544 := @ep479 17356361528813351051 94735435052057886720 1903687850567345177531 ep317 (@ep480 105260541886341517934592 4113126530844275239 94735435052057886720 52795405415830592511 584780788257452877414400 ep481 10919331559663400711 94735435052057886720 1907403054787340764549 ep317 (ep496 (@ep497 9238429163 55143280800 0 1 qz360) rfl) (ep536 (@ep537 9238429163 55143280800 0 1 qz360) rfl) rfl rfl) (@ep538 ep317 1234974980009785205 9473543505205788672 3170386530007405209 11695615765149057548288 ep539 17356361528813351051 94735435052057886720 1903687850567345177531 ep317 (ep541 (@ep537 9238429163 55143280800 0 1 qz360) rfl) (ep543 (@ep497 9238429163 55143280800 0 1 qz360) rfl) rfl rfl)

noncomputable def ep545 := @ep436 17280623942509758009131 ep317 (@ep437 190885526503424 (BSN.head_sum_c_eq qz124 6) (ep438 (BSN.head_sum_c_succ qz124 5 6 rfl rfl) (ep478 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep544 rfl rfl rfl

noncomputable def ep546 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz124 1 6) Bool.false 271303065653089262231 94735435052057886720 17341571785539962172949 ep317 Bool.true 8996853347158073029 94735435052057886720 17280623942509758009131 ep317 (@ep432 ep317 Bool.true 8996853347158073029 94735435052057886720 17280623942509758009131 ep317 (BSN.zetaApproximant_eq_folded' qz124 1 6 rfl) (ep545 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep547 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) (Complex.im (zetaApproximant qz124 1 6)) 5 32768 130413

noncomputable def ep548 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) Bool.true 20 131072 260826

noncomputable def ep549 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123) qz328 Bool.false 823529 131072 11

noncomputable def ep550 := nat_lit 276632878085556284753830962071944704277217948203285810093535422435928481

noncomputable def ep551 := nat_lit 827901720512676159574575032590417249498637356257600650766981369088027041

noncomputable def ep552 := BSN.cos_dyadic_bound_f 421615107 268435456 3 2 131072 44488 ep550 ep236 ep428 ep551 ep238 ep428 20 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 421615107) qz306 0 2 ep550 ep236 ep428 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 421615107) qz307 0 2 ep551 ep238 ep428 rfl rfl rfl rfl) rfl rfl

noncomputable def ep553 := @ep549 16384 Bool.true 20 131072 1 22222 (@ep321 823529 131072 11 16384 ep426 rfl) (Enclosure.sfrac_false_div 823529 131072) (BSN.sin_reduce3 qz328 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29668525620069828395008) qz68) 226375608064910080 72057594037927936 Bool.false 20 131072 0 1000000000000000 44444 22222 (BSN.sin_reduce_arg_pos_rat_q3 823529 131072 226375608064910080 72057594037927936 0 29668525620069828395008 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 20 131072 29668525620069828395008 18889465931478580854784 421615107 268435456 44488 44444 (ep552 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep554 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz124 1 6) Bool.false 271303065653089262231 94735435052057886720 17341571785539962172949 ep317 Bool.true 8996853347158073029 94735435052057886720 17280623942509758009131 ep317 (@ep432 ep317 Bool.true 8996853347158073029 94735435052057886720 17280623942509758009131 ep317 (BSN.zetaApproximant_eq_folded' qz124 1 6 rfl) (ep545 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow03.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 6 qz137) Bool.false ep302 ep303 ep304 ep305 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 6 qz137) ep306 Bool.false ep302 ep303 ep304 ep305 (@Eq.refl Real ep306) (@ep307 Bool.false ep302 ep303 ep304 ep305 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123) (zetaApproximant qz124 1 6)) (@ep309 ep310 ep311 ep312 8996853347158073029 620858147157166566408192 ep313 ep314 ep315 ep302 ep303 ep304 ep305 (@ep316 182042624 271303065653089262231 94735435052057886720 17341571785539962172949 ep317 ep308 ep310 ep311 ep312 (@ep318 364085248 131071 131072 130413 182042624 (ep431 rfl rfl) rfl) ep546 rfl) (@ep547 182042624 8996853347158073029 94735435052057886720 17280623942509758009131 ep317 8996853347158073029 620858147157166566408192 ep313 ep314 (@ep548 364085248 5 32768 130413 182042624 (ep553 rfl rfl) rfl) ep554 rfl) rfl rfl))

theorem EMRow03.d11 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow03.d12 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow03.d13 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow03.d14 : @Eq Nat (Nat.pow 5 (Nat.succ (Nat.mul 2 3))) 78125 := @Eq.refl Nat 78125

noncomputable abbrev qz403 := (@HAdd.hAdd Complex Complex Complex qz406 qz410 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz361 := qz403

noncomputable abbrev qz190 := (@HDiv.hDiv Real Real Real qz254 (@Norm.norm Complex Complex.instNorm qz361) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz262) qz311))

noncomputable abbrev qz191 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz192 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz362 := (@HPow.hPow Complex Complex Complex qz394 (@Nat.cast Complex Complex.instNatCast 5) (@HSub.hSub Complex Complex Complex qz384 qz395 qz396))

noncomputable abbrev qz193 := qz362

noncomputable def ep555 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 5))) (@HMul.hMul Real Real Real qz0 qz190 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193))) 5824419 268435456 2209 50331648 6421796372613 15393162788864 48161723

noncomputable def ep556 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 5)) 123 8192 1 221184 47353 32768 163 65536 5824419 268435456

noncomputable abbrev qz363 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz364 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz194 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz363 qz364 2))

noncomputable def ep557 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz194 96 162 0 1 3321 131072 1 131072 123 8192 1 221184

noncomputable def ep558 := nat_lit 781950621441006189802102638025

noncomputable def ep559 := nat_lit 19807040628566084398385987584

noncomputable def ep560 := nat_lit 26986075409044041160201671

noncomputable def ep561 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz195 := qz363

noncomputable abbrev qz196 := qz364

noncomputable def ep562 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz195 qz196 1) qz196 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep558 ep559 ep560 ep561

noncomputable def ep563 := ep562 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz195 qz196 1) qz196 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz196) (@Enclosure.Real.IsNear.of_eq qz196 qz252 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz253)) (@Enclosure.Real.IsNear.of_eq qz196 qz252 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz253) rfl

noncomputable abbrev qz197 := (@HPow.hPow Real Nat Real qz363 qz364 2)

noncomputable def ep564 := @Enclosure.Real.IsNear.inv_image qz197 ep558 ep559 ep560 ep561 1660 1661 65536 (@Enclosure.Real.IsNear.of_eq qz197 (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz195 qz196 1) qz196) Bool.false ep558 ep559 ep560 ep561 (BSN.pow_succ_r qz196 1 2 rfl) ep563) rfl rfl rfl

noncomputable def ep565 := ep557 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 3321 131072 1 131072 3321 131072 1 131072 (ep564 rfl rfl rfl) rfl)

noncomputable def ep566 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 5)) (Real.sqrt (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 5)) (Complex.re (zetaApproximant qz11 1 5))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 5)) (Complex.im (zetaApproximant qz11 1 5))))) Bool.false 47353 32768 163 65536

noncomputable def ep567 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 5)) (Complex.re (zetaApproximant qz11 1 5))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 5)) (Complex.im (zetaApproximant qz11 1 5))))) Bool.false 189412 131072 326 131072

noncomputable def ep568 := nat_lit 203721016913135324739767662882801

noncomputable def ep569 := nat_lit 97552993974852126448707174400000

noncomputable def ep570 := nat_lit 30124578081853137188738701608938408138598639939

noncomputable def ep571 := nat_lit 4204501555761814775780476268608148507459584000000

noncomputable def ep572 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 5)) (Complex.re (zetaApproximant qz11 1 5))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 5)) (Complex.im (zetaApproximant qz11 1 5)))) ep568 ep569 ep570 ep571 94543 94869

noncomputable def ep573 := nat_lit 104674798167041689072503107235468192529

noncomputable def ep574 := nat_lit 50380390149615100748328394031104000000

noncomputable def ep575 := nat_lit 23039431908993832354625055675532618777512727

noncomputable def ep576 := nat_lit 3446312750624438340803669072629629924147200000

noncomputable def ep577 := nat_lit 2140553835396237821033717173216637649

noncomputable def ep578 := nat_lit 201521560598460402993313576124416000000

noncomputable def ep579 := nat_lit 11931781969708057491693098726559841597829071

noncomputable def ep580 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 5)) (Complex.re (zetaApproximant qz11 1 5))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 5)) (Complex.im (zetaApproximant qz11 1 5))) ep573 ep574 ep575 ep576 ep577 ep578 ep579

noncomputable def ep581 := nat_lit 24878707430543282696925895080521588801536000000

noncomputable def ep582 := nat_lit 21202070619314621104913767514966979639890885152725426507957320349122560000000

noncomputable def ep583 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz11 1 5)) (Complex.re (zetaApproximant qz11 1 5)) 10231070235661647977 7097914492977152000 2375609836078221754073 1025244063109098766336000 10231070235661647977 7097914492977152000 2375609836078221754073 1025244063109098766336000 ep573

noncomputable def ep584 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz11 1 5)) (Complex.im (zetaApproximant qz11 1 5)) 1463063168628148407 14195828985954304000 362942478613081603843 157729855862938271744000 1463063168628148407 14195828985954304000 362942478613081603843 157729855862938271744000 ep577

noncomputable def ep585 := @ep555 15393162788864 1813494067439069036544 6755791855749 15393162788864 2171251505 46179488366592 (@ep556 2209 50331648 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz194) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow03.d11 EMRow03.d12 rfl) (ep565 rfl)) (ep566 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz11 1 5)) (@ep567 47353 32768 163 65536 (@ep572 65536 (@ep580 ep581 ep582 ep568 ep569 ep570 ep571 (@ep583 ep574 ep575 ep576 ep293 ep293 rfl) (@ep584 ep578 ep579 ep581 ep301 ep301 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz198 := (@Norm.norm Complex Complex.instNorm qz361)

noncomputable abbrev qz365 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep586 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz190 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz198 qz365) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193))) Bool.false 6421796372613 15393162788864 48161723 15393162788864 (BSN.zrb_shape_eq qz198 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) qz37 3)

noncomputable def ep587 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz198 qz365) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) 3071391 458752 1 458752 2090843 33554432 15 33554432

noncomputable def ep588 := @Enclosure.Real.IsNear.mulLit_ff qz198 qz365 3071391 131072 1 131072 2 7 0 1 3071391 458752

noncomputable abbrev qz366 := (Complex.re qz403)

noncomputable abbrev qz367 := (Complex.im qz403)

noncomputable abbrev qz199 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz250 qz366 qz366) (@HMul.hMul Real Real Real qz250 qz367 qz367))

noncomputable abbrev qz200 := qz361

noncomputable def ep589 := @Enclosure.Real.IsNear.of_eq qz198 (Real.sqrt qz199) Bool.false 3071391 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz200)

noncomputable def ep590 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz199) Bool.false 3071391 131072 1 131072 3071391

noncomputable def ep591 := @Enclosure.Real.IsNear.sqrt_image qz199 5490989 10000 0 1 1535695 1535696 65536

noncomputable abbrev qz201 := (@HMul.hMul Real Real Real qz250 qz366 qz366)

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz250 qz367 qz367)

noncomputable def ep592 := @Enclosure.Real.IsNear.addLit_ff qz201 qz202 49 4 0 1 5368489 10000 0 1

noncomputable abbrev qz203 := qz366

noncomputable def ep593 := @Enclosure.Real.IsNear.mulLit_ff qz203 qz203 7 2 0 1 7 2 0 1 49 4

noncomputable def ep594 := @Enclosure.Complex.IsNear.of_eq qz200 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz37) Bool.false 7 2 0 1 Bool.false 23170 1000 0 1 (BSN.s_add_nat_mk qz37 Bool.false 23170 1000 3 qz38)

noncomputable abbrev qz204 := (ep594 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz261 Bool.false 7 2 0 1 Bool.false 23170 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz308))

noncomputable def ep595 := @ep593 0 1 (@Enclosure.Complex.IsNear.re_isNear qz200 Bool.false 7 2 0 1 Bool.false 23170 1000 0 1 qz204)

noncomputable def ep596 := ep595 (@Enclosure.Complex.IsNear.re_isNear qz200 Bool.false 7 2 0 1 Bool.false 23170 1000 0 1 qz204)

noncomputable abbrev qz205 := qz367

noncomputable def ep597 := @Enclosure.Real.IsNear.mulLit_ff qz205 qz205 23170 1000 0 1 23170 1000 0 1 5368489 10000

noncomputable def ep598 := @ep597 0 1 (@Enclosure.Complex.IsNear.im_isNear qz200 Bool.false 7 2 0 1 Bool.false 23170 1000 0 1 qz204)

noncomputable def ep599 := ep598 (@Enclosure.Complex.IsNear.im_isNear qz200 Bool.false 7 2 0 1 Bool.false 23170 1000 0 1 qz204)

noncomputable def ep600 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) (Real.sqrt (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193))))) Bool.false 2090843 33554432

noncomputable def ep601 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193))))) Bool.false 4181686 67108864

noncomputable def ep602 := nat_lit 816502692427666175353858637460731320434106313

noncomputable def ep603 := nat_lit 210288022770660518955485101333413888000000000000

noncomputable def ep604 := nat_lit 8118022041720580119544426816895524178790991690169191

noncomputable def ep605 := nat_lit 150817994924805460670017395771750481920000000000000000000000

noncomputable def ep606 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)))) ep602 ep603 ep604 ep605

noncomputable def ep607 := nat_lit 74145215981334411929078277448254658181567401

noncomputable def ep608 := nat_lit 420576045541321037910970202666827776000000000000

noncomputable def ep609 := nat_lit 2206180647232181943354739466152542560373953879034191

noncomputable def ep610 := nat_lit 301635989849610921340034791543500963840000000000000000000000

noncomputable def ep611 := nat_lit 6928267417217768616793951099880924367496201

noncomputable def ep612 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193))) ep607 ep608 ep609 ep610 ep611

noncomputable def ep613 := nat_lit 1869226869072537946270978678519234560000000000

noncomputable def ep614 := nat_lit 1558873715134330921748234907515389533023114389033799

noncomputable def ep615 := nat_lit 33515109983290102371114976838166773760000000000000000000000

noncomputable def ep616 := nat_lit 3052457542711727764734651253009239304690479488138031562678407914504032828847554560000000000

noncomputable def ep617 := nat_lit 549213974557831987200000000000

noncomputable def ep618 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) 8610761637702811938701 648518346341351424000000 151267521360299046020021 ep617 8610761637702811938701 648518346341351424000000 151267521360299046020021

noncomputable def ep619 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193) Bool.true 8610761637702811938701 648518346341351424000000 151267521360299046020021 ep617 Bool.false 2632160218759064943101 43234556422756761600000 69932320315533145428757

noncomputable def ep620 := nat_lit 183071324852610662400000000000

noncomputable def ep621 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193 Bool.true 8610761637702811938701 648518346341351424000000 151267521360299046020021 ep617 Bool.false 2632160218759064943101 43234556422756761600000 69932320315533145428757 ep620

noncomputable def ep622 := nat_lit 1220475499017404416000000000

noncomputable abbrev qz206 := (Complex.re qz362)

noncomputable abbrev qz207 := (Complex.im qz362)

noncomputable def ep623 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz206) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz207) 3172918925991671549 288230376151711744000 81663049461015083413 ep622 15749829221184072923951 648518346341351424000000 114519149102842258484171

noncomputable def ep624 := nat_lit 2481883065787810926573267934500349804544000

noncomputable def ep625 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz206 16092967 4800000 0 1 14787137726025 4503599627370496 15223367349417 762797186885877760000 3172918925991671549

noncomputable def ep626 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) 16092967 4800000 0 1 0 1 0 1 16092967

noncomputable def ep627 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 48278901 20000 0 1 16092967 4800000 0

noncomputable def ep628 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz45) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow03.d13 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz45 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz46)

noncomputable abbrev qz368 := (@HAdd.hAdd Complex Complex Complex qz386 qz389 qz397)

noncomputable abbrev qz208 := qz368

noncomputable def ep629 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) qz208) Bool.true 48278901 20000 0 1 Bool.true 12305561513 1000000 0 1

noncomputable abbrev qz209 := (Complex.re qz368)

noncomputable abbrev qz210 := (Complex.im qz368)

noncomputable def ep630 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz209) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz210) 5360989 4000 0 1 5368489 5000 0 1

noncomputable def ep631 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz209 5360989 10000 0 1 5 2 0 1 5360989 4000

noncomputable abbrev qz369 := (@HAdd.hAdd Complex Complex Complex qz386 qz389 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz211 := qz369

noncomputable def ep632 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz211) Bool.true 5360989 10000 0 1 Bool.false 2317 50 0 1

noncomputable abbrev qz212 := (Complex.re qz369)

noncomputable abbrev qz213 := (Complex.im qz369)

noncomputable def ep633 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz212) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz213) 3 4 0 1 5368489 10000 0 1

noncomputable def ep634 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz212 1 2 0 1 3 2 0 1 3 4

noncomputable def ep635 := @ep634 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep260)

noncomputable def ep636 := @Enclosure.Complex.IsNear.of_eq qz211 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz37) Bool.false 3 2 0 1 Bool.false 23170 1000 0 1 (BSN.s_add_nat_mk qz37 Bool.false 23170 1000 1 qz38)

noncomputable abbrev qz214 := (ep636 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz261 Bool.false 3 2 0 1 Bool.false 23170 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz308))

noncomputable def ep637 := ep635 (@Enclosure.Complex.IsNear.re_isNear qz211 Bool.false 3 2 0 1 Bool.false 23170 1000 0 1 qz214)

noncomputable def ep638 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz213 23170 1000 0 1 23170 1000 0 1 5368489 10000

noncomputable def ep639 := @ep638 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep260)

noncomputable def ep640 := ep639 (@Enclosure.Complex.IsNear.im_isNear qz211 Bool.false 3 2 0 1 Bool.false 23170 1000 0 1 qz214)

noncomputable def ep641 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz211 Bool.true 5360989 10000 0 1 Bool.false 2317 50 0 1 (@ep633 21443956 5360989 10000 0 1 (ep637 rfl) (ep640 rfl) rfl rfl)

noncomputable def ep642 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz213) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz212) 2317 200 0 1 6951 200 0 1

noncomputable def ep643 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz213 1 2 0 1 23170 1000 0 1 2317 200

noncomputable def ep644 := @ep643 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep260)

noncomputable def ep645 := ep644 (@Enclosure.Complex.IsNear.im_isNear qz211 Bool.false 3 2 0 1 Bool.false 23170 1000 0 1 qz214)

noncomputable def ep646 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz212 23170 1000 0 1 3 2 0 1 6951 200

noncomputable def ep647 := @ep646 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep260)

noncomputable def ep648 := ep647 (@Enclosure.Complex.IsNear.re_isNear qz211 Bool.false 3 2 0 1 Bool.false 23170 1000 0 1 qz214)

noncomputable abbrev qz215 := (ep632 (BSN.ascPochhammer_succ_eval_c 1 2 qz262 rfl) (ep641 (@ep642 1853600 2317 50 0 1 (ep645 rfl) (ep648 rfl) rfl rfl)))

noncomputable def ep649 := @ep631 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5360989 10000 0 1 Bool.false 2317 50 0 1 qz215)

noncomputable def ep650 := @Enclosure.Complex.IsNear.of_eq qz208 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz37) Bool.false 5 2 0 1 Bool.false 23170 1000 0 1 (BSN.s_add_nat_mk qz37 Bool.false 23170 1000 2 qz38)

noncomputable abbrev qz216 := (ep650 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz261 Bool.false 5 2 0 1 Bool.false 23170 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz308))

noncomputable def ep651 := ep649 (@Enclosure.Complex.IsNear.re_isNear qz208 Bool.false 5 2 0 1 Bool.false 23170 1000 0 1 qz216)

noncomputable def ep652 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz210 2317 50 0 1 23170 1000 0 1 5368489 5000

noncomputable def ep653 := @ep652 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5360989 10000 0 1 Bool.false 2317 50 0 1 qz215)

noncomputable def ep654 := ep653 (@Enclosure.Complex.IsNear.im_isNear qz208 Bool.false 5 2 0 1 Bool.false 23170 1000 0 1 qz216)

noncomputable def ep655 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) qz208 Bool.true 48278901 20000 0 1 Bool.true 12305561513 1000000 0 1 (@ep630 48278901000 48278901 20000 0 1 (ep651 rfl) (ep654 rfl) rfl rfl)

noncomputable def ep656 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz210) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz209) 12421411513 1000000 0 1 2317 20 0 1

noncomputable def ep657 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz210 5360989 10000 0 1 23170 1000 0 1 12421411513 1000000

noncomputable def ep658 := @ep657 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5360989 10000 0 1 Bool.false 2317 50 0 1 qz215)

noncomputable def ep659 := ep658 (@Enclosure.Complex.IsNear.im_isNear qz208 Bool.false 5 2 0 1 Bool.false 23170 1000 0 1 qz216)

noncomputable def ep660 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz209 2317 50 0 1 5 2 0 1 2317 20

noncomputable def ep661 := @ep660 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5360989 10000 0 1 Bool.false 2317 50 0 1 qz215)

noncomputable def ep662 := ep661 (@Enclosure.Complex.IsNear.re_isNear qz208 Bool.false 5 2 0 1 Bool.false 23170 1000 0 1 qz216)

noncomputable abbrev qz217 := (ep629 (BSN.ascPochhammer_succ_eval_c 2 3 qz262 rfl) (ep655 (@ep656 246111230260 12305561513 1000000 0 1 (ep659 rfl) (ep662 rfl) rfl rfl)))

noncomputable def ep663 := @ep627 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep628) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 48278901 20000 0 1 Bool.true 12305561513 1000000 0 1 qz217)

noncomputable def ep664 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 12305561513 1000000 0 1 0 1 0

noncomputable def ep665 := @ep664 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep628) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 48278901 20000 0 1 Bool.true 12305561513 1000000 0 1 qz217)

noncomputable def ep666 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) 12305561513 720000000 0 1 0 1 0 1 12305561513

noncomputable def ep667 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 12305561513 1000000 0 1 12305561513 720000000 0

noncomputable def ep668 := @ep667 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep628) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 48278901 20000 0 1 Bool.true 12305561513 1000000 0 1 qz217)

noncomputable def ep669 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 48278901 20000 0 1 0 1 0

noncomputable def ep670 := @ep669 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep628) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 48278901 20000 0 1 Bool.true 12305561513 1000000 0 1 qz217)

noncomputable def ep671 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 16092967 4800000 0 1 Bool.false 12305561513 720000000 0 1 (@ep626 16092967 4800000 0 1 (ep663 rfl) (ep665 rfl) rfl rfl) (@ep666 12305561513 720000000 0 1 (ep668 rfl) (ep670 rfl) rfl rfl)

noncomputable def ep672 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 16092967 4800000 0 1 Bool.false 12305561513 720000000 0 1 ep671

noncomputable def ep673 := @Enclosure.Complex.IsNear.re_isNear qz193 Bool.false 14787137726025 4503599627370496 15223367349417 762797186885877760000 Bool.false 6399476043635 4503599627370496 9306292035667 762797186885877760000

noncomputable abbrev qz370 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 78125)))

noncomputable def ep674 := @Enclosure.Complex.IsNear.of_eq qz193 (Complex.mk (@HMul.hMul Real Real Real qz0 qz370 qz107) (@HMul.hMul Real Real Real qz0 qz370 qz108)) Bool.false 14787137726025 4503599627370496 15223367349417 762797186885877760000 Bool.false 6399476043635 4503599627370496 9306292035667

noncomputable abbrev qz371 := (Real.sqrt (@Nat.cast Real Real.instNatCast 78125))

noncomputable abbrev qz372 := (@Nat.cast Real Real.instNatCast 78125)

noncomputable def ep675 := @Enclosure.Real.IsNear.inv_image qz371 18757497725 67108864 1 67108864 120047 120048 33554432 (@Enclosure.Real.IsNear.of_eq qz371 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz372 qz305)) Bool.false 18757497725 67108864 1 67108864 (BSN.sqrt_natCast_div_one 78125) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz372 qz305)) Bool.false 18757497725 67108864 1 67108864 18757497725 67108864 1 67108864 (BSN.sqrt_enclosure 78125 1 9378748862 9378748863 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep676 := nat_lit 24987371385403367883999025651388344673404853859375

noncomputable def ep677 := nat_lit 5174345737036840691400486158476888201456094182500

noncomputable def ep678 := nat_lit 9919565729522841605829928920966758400000

noncomputable def ep679 := nat_lit 1753791174206542693625850900

noncomputable def ep680 := nat_lit 2517933232285674949199829375

noncomputable def ep681 := BSN.log_dyadic_bound 2 3 23 22 ep676 33554432 13888750 ep677 ep678 54003774 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 22 11 2054957030503884950940 9923762498944768499025 57668788341964800 ep679 ep680 172009262110757879808000 ep677 ep676 ep678 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 0 11 2054957030503884950940 9923762498944768499025 57668788341964800 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 11 22 ep679 ep680 172009262110757879808000 rfl rfl rfl rfl)) rfl rfl

noncomputable def ep682 := nat_lit 11241658331852586251976704

noncomputable def ep683 := nat_lit 9671406556917033397649408

noncomputable def ep684 := nat_lit 703210828668724568794617206719393346479641008435514138296316724746086960232381605997320937985

noncomputable def ep685 := nat_lit 46199975943266144436568348213124696692647303168343434164427665391357367878632476496239452487680

noncomputable def ep686 := nat_lit 424233195869482767492424655440778944344486248900804980267325626041726782706639749227553281

noncomputable def ep687 := nat_lit 1841055792767632803314723996727697503441549663404316677950872894749969719150902979922805465601

noncomputable def ep688 := nat_lit 846999558959879314670419717240619439365200558086296293014507198841551744441595402431056628940800

noncomputable def ep689 := BSN.sin_dyadic_bound_f 159753573311 137438953472 3 2 67108864 27804627 ep684 ep685 ep686 ep687 ep688 ep686 61588695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 159753573311) (BSN.sinEvenQ 137438953472) 0 2 ep684 ep685 ep686 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 159753573311) (BSN.sinOddQ 137438953472) 0 2 ep687 ep688 ep686 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := (@HDiv.hDiv Real Real Real qz254 (@Nat.cast Real Real.instNatCast 2502534887) (@Nat.cast Real Real.instNatCast 67108864))

noncomputable def ep690 := @Enclosure.Real.IsNear.cos_image qz111 qz218 Bool.false 2502534887 67108864 113 67108864 Bool.false 61588695 67108864 1 13888750 (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 62563372179 1677721600 2317 1388875000 2502534887 67108864 113 67108864 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz112 23170 1000 0 1 54003774 33554432 1 13888750 62563372179 1677721600 2317 1388875000 qz88 (BSN.isNear_log_sfrac 5 1 54003774 33554432 1 13888750 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 54003774 33554432 13888750 rfl rfl rfl (ep681 rfl rfl))) rfl) rfl) (Enclosure.sfrac_false_div 2502534887 67108864) (BSN.cos_reduce3 qz218 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep682) (@Nat.cast Real Real.instNatCast ep683)) 226375608064910080 72057594037927936 Bool.false 61588695 67108864 5 1000000000000000 27777500 13888750 (BSN.sin_reduce_arg_pos_rat_q3 2502534887 67108864 226375608064910080 72057594037927936 5 ep682 ep683 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 61588695 67108864 ep682 ep683 159753573311 137438953472 27804627 27777500 (ep689 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep691 := nat_lit 1656831971598980811749951610671140358810580326409100877610604334443405954966951740848241359607303579611530614659095538243611141722684593222401

noncomputable def ep692 := nat_lit 21759806992472160846509436431027924547665573599712653161483140986990306751823661669370177199848368120331884066839754328502985489716814125465600

noncomputable def ep693 := nat_lit 276316597848078055460700180971917035505259502169107523923016241721339707833818058786110550606801393523865935758562264494870986214552321

noncomputable def ep694 := nat_lit 10044172798333166868460657837529480483613409053561573381748744579169407234896762931247199827592414109649187202490501961700762062940190237209345

noncomputable def ep695 := nat_lit 1980142436314966637032358715223541133837567197573851437694965829816117914415953211912686125186201498950201450082417643893771679564230085417369600

noncomputable def ep696 := BSN.cos_dyadic_bound_f 159753573311 137438953472 4 3 67108864 27804627 ep691 ep692 ep693 ep694 ep695 ep693 26653933 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 159753573311) (BSN.cosEvenQ 137438953472) 0 3 ep691 ep692 ep693 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 159753573311) (BSN.cosOddQ 137438953472) 0 3 ep694 ep695 ep693 rfl rfl rfl rfl) rfl rfl

noncomputable def ep697 := @Enclosure.Real.IsNear.sin_image qz111 qz218 Bool.false 2502534887 67108864 113 67108864 Bool.true 26653933 67108864 1 13888750 (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 62563372179 1677721600 2317 1388875000 2502534887 67108864 113 67108864 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz112 23170 1000 0 1 54003774 33554432 1 13888750 62563372179 1677721600 2317 1388875000 qz88 (BSN.isNear_log_sfrac 5 1 54003774 33554432 1 13888750 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 54003774 33554432 13888750 rfl rfl rfl (ep681 rfl rfl))) rfl) rfl) (Enclosure.sfrac_false_div 2502534887 67108864) (BSN.sin_reduce3 qz218 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep682) (@Nat.cast Real Real.instNatCast ep683)) 226375608064910080 72057594037927936 Bool.false 26653933 67108864 5 1000000000000000 27777500 13888750 (BSN.sin_reduce_arg_pos_rat_q3 2502534887 67108864 226375608064910080 72057594037927936 5 ep682 ep683 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 26653933 67108864 ep682 ep683 159753573311 137438953472 27804627 27777500 (ep696 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep698 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz370 qz107) (@HMul.hMul Real Real Real qz0 qz370 qz108) Bool.false 14787137726025 4503599627370496 15223367349417 762797186885877760000 Bool.false 6399476043635 4503599627370496 9306292035667 762797186885877760000 (@Enclosure.Real.IsNear.mulLit_ff qz370 qz107 240095 67108864 1 67108864 61588695 67108864 818268807 466029117440000 14787137726025 4503599627370496 15223367349417 762797186885877760000 (@Enclosure.Real.IsNear.recentre' qz370 Bool.false 240095 67108864 1 67108864 240095 67108864 1 67108864 (ep675 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 61588695 67108864 1636537614 932058234880000 61588695 67108864 818268807 466029117440000 (ep690 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz370 qz108 240095 67108864 1 67108864 26653933 67108864 818268807 466029117440000 6399476043635 4503599627370496 9306292035667 762797186885877760000 (@Enclosure.Real.IsNear.recentre' qz370 Bool.false 240095 67108864 1 67108864 240095 67108864 1 67108864 (ep675 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz114 Bool.true 26653933 67108864 818268807 466029117440000 (@Enclosure.Real.IsNear.recentre' qz114 Bool.true 26653933 67108864 1636537614 932058234880000 26653933 67108864 818268807 466029117440000 (ep697 rfl rfl) rfl)) rfl)

noncomputable def ep699 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz207 12305561513 720000000 0 1 6399476043635 4503599627370496 9306292035667 762797186885877760000 15749829221184072923951

noncomputable def ep700 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 16092967 4800000 0 1 Bool.false 12305561513 720000000 0 1 ep671

noncomputable def ep701 := @Enclosure.Complex.IsNear.im_isNear qz193 Bool.false 14787137726025 4503599627370496 15223367349417 762797186885877760000 Bool.false 6399476043635 4503599627370496 9306292035667 762797186885877760000

noncomputable def ep702 := nat_lit 3661426497052213248000000000

noncomputable def ep703 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz207) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz206) 20597311357501723009 4323455642275676160000 149765850622351853989 ep702 2426187105184047713011 43234556422756761600000 62444027784415552729307

noncomputable def ep704 := nat_lit 11380027949167457388506686414546702172160000

noncomputable def ep705 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz207 16092967 4800000 0 1 6399476043635 4503599627370496 9306292035667 762797186885877760000 20597311357501723009

noncomputable def ep706 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz206 12305561513 720000000 0 1 14787137726025 4503599627370496 15223367349417 762797186885877760000 2426187105184047713011

noncomputable abbrev qz219 := (@ep674 762797186885877760000 (BSN.cpow_neg_s_sub_mk qz261 23170 1000 5 3 78125 qz278 rfl EMRow03.d14) ep698)

noncomputable def ep707 := ep621 (@ep623 ep617 ep624 8610761637702811938701 648518346341351424000000 151267521360299046020021 ep617 (@ep625 288230376151711744000 81663049461015083413 ep622 ep672 (ep673 qz219) rfl) (@ep699 648518346341351424000000 114519149102842258484171 ep617 ep700 (ep701 qz219) rfl) rfl rfl) (@ep703 ep620 ep704 2632160218759064943101 43234556422756761600000 69932320315533145428757 ep620 (@ep705 4323455642275676160000 149765850622351853989 ep702 ep672 (ep701 qz219) rfl) (@ep706 43234556422756761600000 62444027784415552729307 ep620 ep700 (ep673 qz219) rfl) rfl rfl)

noncomputable def ep708 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) 2632160218759064943101 43234556422756761600000 69932320315533145428757 ep620 2632160218759064943101 43234556422756761600000 69932320315533145428757

noncomputable def ep709 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193) Bool.true 8610761637702811938701 648518346341351424000000 151267521360299046020021 ep617 Bool.false 2632160218759064943101 43234556422756761600000 69932320315533145428757

noncomputable def ep710 := @ep587 6421796372613 15393162788864 48161723 15393162788864 (@ep588 1 458752 (ep589 (@ep590 131072 1 131072 (ep591 (@ep592 21963956 5490989 10000 0 1 (ep596 rfl) (ep599 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep600 15 33554432 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)) (@ep601 30 67108864 2090843 33554432 15 33554432 (@ep606 2090828 2090858 33554432 (@ep612 ep613 ep614 ep615 ep616 ep602 ep603 ep604 ep605 (@ep618 ep617 ep607 ep608 ep609 ep610 (@ep619 ep620 ep707) (@ep619 ep620 ep707) rfl) (@ep708 ep620 ep611 ep613 ep614 ep615 (@ep709 ep620 ep707) (@ep709 ep620 ep707) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow03.d15 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 5))) (@HMul.hMul Real Real Real qz0 qz190 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)))) Bool.false 6755791855749 15393162788864 2171251505 46179488366592 := ep585 (ep586 ep710) rfl rfl

theorem EMRow03.d16 : @Eq Nat (Nat.pow 6 (Nat.succ (Nat.mul 2 3))) 279936 := @Eq.refl Nat 279936

noncomputable abbrev qz404 := (@HAdd.hAdd Complex Complex Complex qz406 qz413 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz373 := qz404

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz254 (@Norm.norm Complex Complex.instNorm qz373) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz327) qz311))

noncomputable abbrev qz374 := (@HPow.hPow Complex Complex Complex qz394 (@Nat.cast Complex Complex.instNatCast 6) (@HSub.hSub Complex Complex Complex qz384 qz402 qz396))

noncomputable abbrev qz221 := qz374

noncomputable def ep711 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz124 1 6))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) 23097555 536870912 931913 14495514624 13720993492655 30786325577728 87833581

noncomputable def ep712 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz124 1 6)) 123 8192 1 221184 187785 65536 7 2048 23097555 536870912

noncomputable def ep713 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz124 1 6)) (Real.sqrt (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz124 1 6)) (Complex.re (zetaApproximant qz124 1 6))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz124 1 6)) (Complex.im (zetaApproximant qz124 1 6))))) Bool.false 187785 65536 7 2048

noncomputable def ep714 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz124 1 6)) (Complex.re (zetaApproximant qz124 1 6))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz124 1 6)) (Complex.im (zetaApproximant qz124 1 6))))) Bool.false 375570 131072 448 131072

noncomputable def ep715 := nat_lit 4810571018663311652297298150833009

noncomputable def ep716 := nat_lit 585915257262125780584232701132800

noncomputable def ep717 := nat_lit 270313243098472039180236611668502707233410800871

noncomputable def ep718 := nat_lit 13849727097757821453392499353925839981987758080000

noncomputable def ep719 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz124 1 6)) (Complex.re (zetaApproximant qz124 1 6))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz124 1 6)) (Complex.im (zetaApproximant qz124 1 6)))) ep715 ep716 ep717 ep718 187561 188009

noncomputable def ep720 := nat_lit 73605353432764462550243660471431883097361

noncomputable def ep721 := nat_lit 8974802654502678089909869969752352358400

noncomputable def ep722 := nat_lit 523053456828017717867562555869050389860105479691

noncomputable def ep723 := nat_lit 27699454195515642906784998707851679963975516160000

noncomputable def ep724 := nat_lit 80943370150269422129083143208497234841

noncomputable def ep725 := nat_lit 17573029368926360492910667467955024606716122051

noncomputable def ep726 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz124 1 6)) (Complex.re (zetaApproximant qz124 1 6))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz124 1 6)) (Complex.im (zetaApproximant qz124 1 6))) ep720 ep721 ep722 ep723 ep724 ep721 ep725

noncomputable def ep727 := nat_lit 661319972147271338370770489810986455687691665754348794623340074352543150165196800

noncomputable def ep728 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz124 1 6)) (Complex.re (zetaApproximant qz124 1 6)) 271303065653089262231 94735435052057886720 17341571785539962172949 ep317 271303065653089262231 94735435052057886720 17341571785539962172949 ep317 ep720

noncomputable def ep729 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz124 1 6)) (Complex.im (zetaApproximant qz124 1 6)) 8996853347158073029 94735435052057886720 17280623942509758009131 ep317 8996853347158073029 94735435052057886720 17280623942509758009131 ep317 ep724

noncomputable def ep730 := @ep711 30786325577728 8077491138227234406400 15045499686575 30786325577728 55811125759 831230790598656 (@ep712 931913 14495514624 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz194) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow03.d11 EMRow03.d12 rfl) (ep565 rfl)) (ep713 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz124 1 6)) (@ep714 187785 65536 7 2048 (@ep719 65536 (@ep726 ep723 ep727 ep715 ep716 ep717 ep718 (@ep728 ep721 ep722 ep723 ep546 ep546 rfl) (@ep729 ep721 ep725 ep723 ep554 ep554 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz222 := (@Norm.norm Complex Complex.instNorm qz373)

noncomputable def ep731 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz222 qz365) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) Bool.false 13720993492655 30786325577728 87833581 30786325577728 (BSN.zrb_shape_eq qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) qz137 3)

noncomputable def ep732 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz222 qz365) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) 3655661 458752 1 458752 3753355 67108864 23 67108864

noncomputable def ep733 := @Enclosure.Real.IsNear.mulLit_ff qz222 qz365 3655661 131072 1 131072 2 7 0 1 3655661 458752

noncomputable abbrev qz375 := (Complex.re qz404)

noncomputable abbrev qz376 := (Complex.im qz404)

noncomputable abbrev qz223 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz250 qz375 qz375) (@HMul.hMul Real Real Real qz250 qz376 qz376))

noncomputable abbrev qz224 := qz373

noncomputable def ep734 := @Enclosure.Real.IsNear.of_eq qz222 (Real.sqrt qz223) Bool.false 3655661 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz224)

noncomputable def ep735 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz223) Bool.false 3655661 131072 1 131072 3655661

noncomputable def ep736 := @Enclosure.Real.IsNear.sqrt_image qz223 7778789 10000 0 1 1827830 1827831 65536

noncomputable abbrev qz225 := (@HMul.hMul Real Real Real qz250 qz375 qz375)

noncomputable abbrev qz226 := (@HMul.hMul Real Real Real qz250 qz376 qz376)

noncomputable def ep737 := @Enclosure.Real.IsNear.addLit_ff qz225 qz226 49 4 0 1 7656289 10000 0 1

noncomputable abbrev qz227 := qz375

noncomputable def ep738 := @Enclosure.Real.IsNear.mulLit_ff qz227 qz227 7 2 0 1 7 2 0 1 49 4

noncomputable def ep739 := @Enclosure.Complex.IsNear.of_eq qz224 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz137) Bool.false 7 2 0 1 Bool.false 27670 1000 0 1 (BSN.s_add_nat_mk qz137 Bool.false 27670 1000 3 qz138)

noncomputable abbrev qz228 := (ep739 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz326 Bool.false 7 2 0 1 Bool.false 27670 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz347))

noncomputable def ep740 := @ep738 0 1 (@Enclosure.Complex.IsNear.re_isNear qz224 Bool.false 7 2 0 1 Bool.false 27670 1000 0 1 qz228)

noncomputable def ep741 := ep740 (@Enclosure.Complex.IsNear.re_isNear qz224 Bool.false 7 2 0 1 Bool.false 27670 1000 0 1 qz228)

noncomputable abbrev qz229 := qz376

noncomputable def ep742 := @Enclosure.Real.IsNear.mulLit_ff qz229 qz229 27670 1000 0 1 27670 1000 0 1 7656289 10000

noncomputable def ep743 := @ep742 0 1 (@Enclosure.Complex.IsNear.im_isNear qz224 Bool.false 7 2 0 1 Bool.false 27670 1000 0 1 qz228)

noncomputable def ep744 := ep743 (@Enclosure.Complex.IsNear.im_isNear qz224 Bool.false 7 2 0 1 Bool.false 27670 1000 0 1 qz228)

noncomputable def ep745 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Real.sqrt (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))))) Bool.false 3753355 67108864

noncomputable def ep746 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))))) Bool.false 7506710 134217728

noncomputable def ep747 := nat_lit 5847112447939226267031601012995890474031012661

noncomputable def ep748 := nat_lit 1869226869072537946270978678519234560000000000000

noncomputable def ep749 := nat_lit 2561924979432085774840720494509512004421695595018279763

noncomputable def ep750 := nat_lit 68131956718119786199183742102727176473208369971200000000000000

noncomputable def ep751 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)))) ep747 ep748 ep749 ep750

noncomputable def ep752 := nat_lit 14697258558477288328156536004926103685051866009

noncomputable def ep753 := nat_lit 18692268690725379462709786785192345600000000000000

noncomputable def ep754 := nat_lit 1758080755975128108509051983511741380511472080376407539

noncomputable def ep755 := nat_lit 136263913436239572398367484205454352946416739942400000000000000

noncomputable def ep756 := nat_lit 4863762880101663815795497125003644561695362289

noncomputable def ep757 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221))) ep752 ep753 ep754 ep755 ep756

noncomputable def ep758 := nat_lit 2076918743413931051412198531688038400000000000000

noncomputable def ep759 := nat_lit 3365769202889043441172389005507282628331919109660151987

noncomputable def ep760 := nat_lit 121439774379738921622166929956835497028594467676391638732145854666341404926541824000000000000000

noncomputable def ep761 := nat_lit 4323455642275676160000000

noncomputable def ep762 := nat_lit 2685526575751453653332579

noncomputable def ep763 := nat_lit 11673213500841984188743680000000

noncomputable def ep764 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) 121232250488379899282747 ep761 ep762 ep763 121232250488379899282747 ep761 ep762

noncomputable def ep765 := nat_lit 1441151880758558720000000

noncomputable def ep766 := nat_lit 2979108485820827700200327

noncomputable def ep767 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221) Bool.true 121232250488379899282747 ep761 ep762 ep763 Bool.false 69740683106072769638233 ep765 ep766

noncomputable def ep768 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221 Bool.true 121232250488379899282747 ep761 ep762 ep763 Bool.false 69740683106072769638233 ep765 ep766 ep763

noncomputable def ep769 := nat_lit 77821423338946561258291200000

noncomputable def ep770 := nat_lit 2258198743365308635278629

noncomputable abbrev qz230 := (Complex.re qz374)

noncomputable abbrev qz231 := (Complex.im qz374)

noncomputable def ep771 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231) 201353992447735218441 28823037615171174400000 2848852215907633453693 ep769 151435349355540182048897 ep761 ep770

noncomputable def ep772 := nat_lit 3494281715998427815174526437760189648076800000

noncomputable def ep773 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230 22956367 4800000 0 1 26313483198069 18014398509481984 124098565592179 16212796528947200262144 201353992447735218441

noncomputable def ep774 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) 22956367 4800000 0 1 0 1 0 1 22956367

noncomputable def ep775 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 68869101 20000 0 1 22956367 4800000 0

noncomputable abbrev qz377 := (@HAdd.hAdd Complex Complex Complex qz386 qz401 qz397)

noncomputable abbrev qz232 := qz377

noncomputable def ep776 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2)) qz232) Bool.true 68869101 20000 0 1 Bool.true 21025849163 1000000 0 1

noncomputable abbrev qz233 := (Complex.re qz377)

noncomputable abbrev qz234 := (Complex.im qz377)

noncomputable def ep777 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz234) 7648789 4000 0 1 7656289 5000 0 1

noncomputable def ep778 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz233 7648789 10000 0 1 5 2 0 1 7648789 4000

noncomputable abbrev qz378 := (@HAdd.hAdd Complex Complex Complex qz386 qz401 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz235 := qz378

noncomputable def ep779 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) qz235) Bool.true 7648789 10000 0 1 Bool.false 2767 50 0 1

noncomputable abbrev qz236 := (Complex.re qz378)

noncomputable abbrev qz237 := (Complex.im qz378)

noncomputable def ep780 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz237) 3 4 0 1 7656289 10000 0 1

noncomputable def ep781 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz236 1 2 0 1 3 2 0 1 3 4

noncomputable def ep782 := @ep781 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep513)

noncomputable def ep783 := @Enclosure.Complex.IsNear.of_eq qz235 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz137) Bool.false 3 2 0 1 Bool.false 27670 1000 0 1 (BSN.s_add_nat_mk qz137 Bool.false 27670 1000 1 qz138)

noncomputable abbrev qz238 := (ep783 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz326 Bool.false 3 2 0 1 Bool.false 27670 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz347))

noncomputable def ep784 := ep782 (@Enclosure.Complex.IsNear.re_isNear qz235 Bool.false 3 2 0 1 Bool.false 27670 1000 0 1 qz238)

noncomputable def ep785 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz237 27670 1000 0 1 27670 1000 0 1 7656289 10000

noncomputable def ep786 := @ep785 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep513)

noncomputable def ep787 := ep786 (@Enclosure.Complex.IsNear.im_isNear qz235 Bool.false 3 2 0 1 Bool.false 27670 1000 0 1 qz238)

noncomputable def ep788 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) qz235 Bool.true 7648789 10000 0 1 Bool.false 2767 50 0 1 (@ep780 30595156 7648789 10000 0 1 (ep784 rfl) (ep787 rfl) rfl rfl)

noncomputable def ep789 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz236) 2767 200 0 1 8301 200 0 1

noncomputable def ep790 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz237 1 2 0 1 27670 1000 0 1 2767 200

noncomputable def ep791 := @ep790 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep513)

noncomputable def ep792 := ep791 (@Enclosure.Complex.IsNear.im_isNear qz235 Bool.false 3 2 0 1 Bool.false 27670 1000 0 1 qz238)

noncomputable def ep793 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz236 27670 1000 0 1 3 2 0 1 8301 200

noncomputable def ep794 := @ep793 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep513)

noncomputable def ep795 := ep794 (@Enclosure.Complex.IsNear.re_isNear qz235 Bool.false 3 2 0 1 Bool.false 27670 1000 0 1 qz238)

noncomputable abbrev qz239 := (ep779 (BSN.ascPochhammer_succ_eval_c 1 2 qz327 rfl) (ep788 (@ep789 2213600 2767 50 0 1 (ep792 rfl) (ep795 rfl) rfl rfl)))

noncomputable def ep796 := @ep778 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7648789 10000 0 1 Bool.false 2767 50 0 1 qz239)

noncomputable def ep797 := @Enclosure.Complex.IsNear.of_eq qz232 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz137) Bool.false 5 2 0 1 Bool.false 27670 1000 0 1 (BSN.s_add_nat_mk qz137 Bool.false 27670 1000 2 qz138)

noncomputable abbrev qz240 := (ep797 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz326 Bool.false 5 2 0 1 Bool.false 27670 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz347))

noncomputable def ep798 := ep796 (@Enclosure.Complex.IsNear.re_isNear qz232 Bool.false 5 2 0 1 Bool.false 27670 1000 0 1 qz240)

noncomputable def ep799 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz234 2767 50 0 1 27670 1000 0 1 7656289 5000

noncomputable def ep800 := @ep799 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7648789 10000 0 1 Bool.false 2767 50 0 1 qz239)

noncomputable def ep801 := ep800 (@Enclosure.Complex.IsNear.im_isNear qz232 Bool.false 5 2 0 1 Bool.false 27670 1000 0 1 qz240)

noncomputable def ep802 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2)) qz232 Bool.true 68869101 20000 0 1 Bool.true 21025849163 1000000 0 1 (@ep777 68869101000 68869101 20000 0 1 (ep798 rfl) (ep801 rfl) rfl rfl)

noncomputable def ep803 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz234) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz233) 21164199163 1000000 0 1 2767 20 0 1

noncomputable def ep804 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz234 7648789 10000 0 1 27670 1000 0 1 21164199163 1000000

noncomputable def ep805 := @ep804 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7648789 10000 0 1 Bool.false 2767 50 0 1 qz239)

noncomputable def ep806 := ep805 (@Enclosure.Complex.IsNear.im_isNear qz232 Bool.false 5 2 0 1 Bool.false 27670 1000 0 1 qz240)

noncomputable def ep807 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz233 2767 50 0 1 5 2 0 1 2767 20

noncomputable def ep808 := @ep807 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7648789 10000 0 1 Bool.false 2767 50 0 1 qz239)

noncomputable def ep809 := ep808 (@Enclosure.Complex.IsNear.re_isNear qz232 Bool.false 5 2 0 1 Bool.false 27670 1000 0 1 qz240)

noncomputable abbrev qz241 := (ep776 (BSN.ascPochhammer_succ_eval_c 2 3 qz327 rfl) (ep802 (@ep803 420516983260 21025849163 1000000 0 1 (ep806 rfl) (ep809 rfl) rfl rfl)))

noncomputable def ep810 := @ep775 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep628) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 68869101 20000 0 1 Bool.true 21025849163 1000000 0 1 qz241)

noncomputable def ep811 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 21025849163 1000000 0 1 0 1 0

noncomputable def ep812 := @ep811 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep628) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 68869101 20000 0 1 Bool.true 21025849163 1000000 0 1 qz241)

noncomputable def ep813 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) 21025849163 720000000 0 1 0 1 0 1 21025849163

noncomputable def ep814 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 21025849163 1000000 0 1 21025849163 720000000 0

noncomputable def ep815 := @ep814 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep628) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 68869101 20000 0 1 Bool.true 21025849163 1000000 0 1 qz241)

noncomputable def ep816 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 68869101 20000 0 1 0 1 0

noncomputable def ep817 := @ep816 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep628) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 68869101 20000 0 1 Bool.true 21025849163 1000000 0 1 qz241)

noncomputable def ep818 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 22956367 4800000 0 1 Bool.false 21025849163 720000000 0 1 (@ep774 22956367 4800000 0 1 (ep810 rfl) (ep812 rfl) rfl rfl) (@ep813 21025849163 720000000 0 1 (ep815 rfl) (ep817 rfl) rfl rfl)

noncomputable def ep819 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 22956367 4800000 0 1 Bool.false 21025849163 720000000 0 1 ep818

noncomputable def ep820 := @Enclosure.Complex.IsNear.re_isNear qz221 Bool.false 26313483198069 18014398509481984 124098565592179 16212796528947200262144 Bool.false 21607024978857 18014398509481984 107401072168783 16212796528947200262144

noncomputable abbrev qz379 := (@Nat.cast Real Real.instNatCast 279936)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz379))

noncomputable def ep821 := @Enclosure.Complex.IsNear.of_eq qz221 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz180) (@HMul.hMul Real Real Real qz0 qz242 qz181)) Bool.false 26313483198069 18014398509481984 124098565592179 16212796528947200262144 Bool.false 21607024978857 18014398509481984 107401072168783

noncomputable def ep822 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz379) 71013228775 134217728 1 134217728 126838 126839 67108864 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz379) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz379 qz305)) Bool.false 71013228775 134217728 1 134217728 (BSN.sqrt_natCast_div_one 279936) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz379 qz305)) Bool.false 71013228775 134217728 1 134217728 71013228775 134217728 1 134217728 (BSN.sqrt_enclosure 279936 1 35506614387 35506614388 67108864 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep823 := nat_lit 4332208541070713612664832

noncomputable def ep824 := nat_lit 2417851639229258349412352

noncomputable def ep825 := BSN.log_dyadic_bound 2 10 6 5 103950000000000 67108864 28799712 1420244935680 967680 27210302 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 2) (BSN.artanhQ 10) 0 5 1420244935680 103950000000000 967680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep826 := @Enclosure.Real.IsNear.mulLit_ff qz137 qz182 27670 1000 0 1 4034683612241143 2251799813685248 15625000899991 449995500000000000000 11163969555071242681 225179981368524800 43234377490275097 44999550000000000000000 qz171 (BSN.isNear_log_sfrac 6 1 4034683612241143 2251799813685248 15625000899991 449995500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz356) Bool.false ep823 ep824 1000000057599424 28799712000000000000000 4034683612241143 2251799813685248 15625000899991 449995500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 27210302 67108864 24973259072661432 36028797018963968 28799712 1000000000000000 rfl rfl rfl rfl (ep825 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep827 := nat_lit 4271367292609506960211968

noncomputable def ep828 := nat_lit 4835703278458516698824704

noncomputable def ep829 := nat_lit 60009081213351719392606546835257411397902560869226954374604658163441749943398876482249387516160

noncomputable def ep830 := nat_lit 11827193841476132975761497142559922353317709611095919146093482340187486176929913983037299836846080

noncomputable def ep831 := nat_lit 12077495060944549418095119006071793917208541636023770542952110501076589163022496900883783936

noncomputable def ep832 := nat_lit 157147087233441545329197373423473865994831226542469413447847420344393316326447401982337441177856

noncomputable def ep833 := nat_lit 216831887093729104555627447613598576477491342870091851011713842903437246577048423022350497008844800

noncomputable def ep834 := BSN.sin_dyadic_bound_f 242799120122 274877906944 3 2 134217728 57655674 ep829 ep830 ep831 ep832 ep833 ep831 103728297 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 242799120122) (BSN.sinEvenQ 274877906944) 0 2 ep829 ep830 ep831 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 242799120122) (BSN.sinOddQ 274877906944) 0 2 ep832 ep833 ep831 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz254 (@Nat.cast Real Real.instNatCast 1663561099) (@Nat.cast Real Real.instNatCast 33554432))

noncomputable def ep835 := @Enclosure.Real.IsNear.cos_image qz183 qz243 Bool.false 1663561099 33554432 65 67108864 Bool.false 103728297 134217728 1 28799712 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 11163969555071242681 225179981368524800 43234377490275097 44999550000000000000000 1663561099 33554432 65 67108864 (ep826 rfl) rfl) (Enclosure.sfrac_false_div 1663561099 33554432) (BSN.cos_reduce3 qz243 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep827) (@Nat.cast Real Real.instNatCast ep828)) 226375608064910080 72057594037927936 Bool.false 103728297 134217728 7 1000000000000000 57599424 28799712 (BSN.sin_reduce_arg_pos_rat_q3 1663561099 33554432 226375608064910080 72057594037927936 7 ep827 ep828 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 103728297 134217728 ep827 ep828 242799120122 274877906944 57655674 57599424 (ep834 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep836 := nat_lit 33343746227444708351189457183590149351686848723630985217243899917690339563738496933205608079616

noncomputable def ep837 := nat_lit 1314132649052903663973499682506658039257523290121768794010386926687498464103323775893033315205120

noncomputable def ep838 := nat_lit 100007083692212235954732181312758304467226129087620908110645795532068865512889445805815056670976

noncomputable def ep839 := nat_lit 59135969207380664878807485712799611766588548055479595730467411700937430884649569915186499184230400

noncomputable def ep840 := BSN.cos_dyadic_bound_f 242799120122 274877906944 3 2 134217728 57655674 ep836 ep837 ep831 ep838 ep839 ep831 85175341 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 242799120122) (BSN.cosEvenQ 274877906944) 0 2 ep836 ep837 ep831 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 242799120122) (BSN.cosOddQ 274877906944) 0 2 ep838 ep839 ep831 rfl rfl rfl rfl) rfl rfl

noncomputable def ep841 := @Enclosure.Real.IsNear.sin_image qz183 qz243 Bool.false 1663561099 33554432 65 67108864 Bool.true 85175341 134217728 1 28799712 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 11163969555071242681 225179981368524800 43234377490275097 44999550000000000000000 1663561099 33554432 65 67108864 (ep826 rfl) rfl) (Enclosure.sfrac_false_div 1663561099 33554432) (BSN.sin_reduce3 qz243 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep827) (@Nat.cast Real Real.instNatCast ep828)) 226375608064910080 72057594037927936 Bool.false 85175341 134217728 7 1000000000000000 57599424 28799712 (BSN.sin_reduce_arg_pos_rat_q3 1663561099 33554432 226375608064910080 72057594037927936 7 ep827 ep828 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 85175341 134217728 ep827 ep828 242799120122 274877906944 57655674 57599424 (ep840 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep842 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz180) (@HMul.hMul Real Real Real qz0 qz242 qz181) Bool.false 26313483198069 18014398509481984 124098565592179 16212796528947200262144 Bool.false 21607024978857 18014398509481984 107401072168783 16212796528947200262144 (@Enclosure.Real.IsNear.mulLit_ff qz242 qz180 253677 134217728 1 134217728 103728297 134217728 60596567 60397373620224 26313483198069 18014398509481984 124098565592179 16212796528947200262144 (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 253677 134217728 1 134217728 253677 134217728 1 134217728 (ep822 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 103728297 134217728 1939090144 1932715955847168 103728297 134217728 60596567 60397373620224 (ep835 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz242 qz181 253677 134217728 1 134217728 85175341 134217728 60596567 60397373620224 21607024978857 18014398509481984 107401072168783 16212796528947200262144 (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 253677 134217728 1 134217728 253677 134217728 1 134217728 (ep822 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz184 Bool.true 85175341 134217728 60596567 60397373620224 (@Enclosure.Real.IsNear.recentre' qz184 Bool.true 85175341 134217728 1939090144 1932715955847168 85175341 134217728 60596567 60397373620224 (ep841 rfl rfl) rfl)) rfl)

noncomputable def ep843 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231 21025849163 720000000 0 1 21607024978857 18014398509481984 107401072168783 16212796528947200262144 151435349355540182048897

noncomputable def ep844 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 22956367 4800000 0 1 Bool.false 21025849163 720000000 0 1 ep818

noncomputable def ep845 := @Enclosure.Complex.IsNear.im_isNear qz221 Bool.false 26313483198069 18014398509481984 124098565592179 16212796528947200262144 Bool.false 21607024978857 18014398509481984 107401072168783 16212796528947200262144

noncomputable def ep846 := nat_lit 2609277721485817426496177

noncomputable def ep847 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230) 165339598397602844173 28823037615171174400000 2465538428900068491361 ep769 61473703186192627429583 ep765 ep846

noncomputable def ep848 := nat_lit 2010138332474068293796291843833457750835200000

noncomputable def ep849 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231 22956367 4800000 0 1 21607024978857 18014398509481984 107401072168783 16212796528947200262144 165339598397602844173

noncomputable def ep850 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230 21025849163 720000000 0 1 26313483198069 18014398509481984 124098565592179 16212796528947200262144 61473703186192627429583

noncomputable abbrev qz244 := (@ep821 16212796528947200262144 (BSN.cpow_neg_s_sub_mk qz326 27670 1000 6 3 279936 qz334 rfl EMRow03.d16) ep842)

noncomputable def ep851 := ep768 (@ep771 ep763 ep772 121232250488379899282747 ep761 ep762 ep763 (@ep773 28823037615171174400000 2848852215907633453693 ep769 ep819 (ep820 qz244) rfl) (@ep843 ep761 ep770 ep763 ep844 (ep845 qz244) rfl) rfl rfl) (@ep847 ep763 ep848 69740683106072769638233 ep765 ep766 ep763 (@ep849 28823037615171174400000 2465538428900068491361 ep769 ep819 (ep845 qz244) rfl) (@ep850 ep765 ep846 ep763 ep844 (ep820 qz244) rfl) rfl rfl)

noncomputable def ep852 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) 69740683106072769638233 ep765 ep766 ep763 69740683106072769638233 ep765 ep766

noncomputable def ep853 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221) Bool.true 121232250488379899282747 ep761 ep762 ep763 Bool.false 69740683106072769638233 ep765 ep766

noncomputable def ep854 := @ep732 13720993492655 30786325577728 87833581 30786325577728 (@ep733 1 458752 (ep734 (@ep735 131072 1 131072 (ep736 (@ep737 31115156 7778789 10000 0 1 (ep741 rfl) (ep744 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep745 23 67108864 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)) (@ep746 46 134217728 3753355 67108864 23 67108864 (@ep751 3753332 3753378 67108864 (@ep757 ep758 ep759 ep755 ep760 ep747 ep748 ep749 ep750 (@ep764 ep763 ep752 ep753 ep754 ep755 (@ep767 ep763 ep851) (@ep767 ep763 ep851) rfl) (@ep852 ep763 ep756 ep758 ep759 ep755 (@ep853 ep763 ep851) (@ep853 ep763 ep851) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow03.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz124 1 6))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)))) Bool.false 15045499686575 30786325577728 55811125759 831230790598656 := ep730 (ep731 ep854) rfl rfl

noncomputable def EMRow03.d18 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz380 := (EMRow03.d3 qz388 qz400 (@Enclosure.dec_le_dec qz388 qz400 23170 1000 27670 1000 (@Eq.refl Real qz388) (@Eq.refl Real qz400) rfl rfl rfl) 5 6 1 1)

noncomputable abbrev qz245 := qz380

noncomputable def ep855 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz245 (@Enclosure.dec_nonneg qz37 23170 1000 qz38) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 5 rfl)

noncomputable abbrev qz246 := (Zeta.Certificates.ZIntervalEM.fstVal qz380)

noncomputable def ep856 := @Enclosure.Real.IsNear.neg_val qz246 ep38 ep39

noncomputable def ep857 := @Enclosure.Real.IsNear.of_eq qz246 (hardyZApproximantEM 1 5 qz37) Bool.true

noncomputable abbrev qz247 := (Zeta.Certificates.ZIntervalEM.sndVal qz380)

noncomputable def ep858 := BSN.mul_neg_of_neg_pos_r qz246 qz247 (@ep856 ep40 ep41 (@ep857 ep38 ep39 ep40 ep41 (@Eq.refl Real (hardyZApproximantEM 1 5 qz37)) EMRow03.d8) rfl rfl rfl)

noncomputable def ep859 := @Enclosure.Real.IsNear.pos_val qz247 ep302 ep303

noncomputable def ep860 := @Enclosure.Real.IsNear.of_eq qz247 (hardyZApproximantEM 1 6 qz137) Bool.false

noncomputable def ep861 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz246) (BSN.hardyZErrorBoundStrong 1 5 qz37)

noncomputable def ep862 := @Enclosure.norm_gt_of_isNear qz246 (BSN.hardyZErrorBoundStrong 1 5 qz37) Bool.true

noncomputable def ep863 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 5 qz37) (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 5))) (@HMul.hMul Real Real Real qz0 qz190 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)))) Bool.false 6755791855749 15393162788864 2171251505 46179488366592 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 5))) (@HMul.hMul Real Real Real qz0 qz190 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz193)))))

noncomputable def ep864 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz247) (BSN.hardyZErrorBoundStrong 1 6 qz137)

noncomputable def ep865 := @Enclosure.norm_gt_of_isNear qz247 (BSN.hardyZErrorBoundStrong 1 6 qz137) Bool.false

noncomputable def ep866 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 6 qz137) (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz124 1 6))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)))) Bool.false 15045499686575 30786325577728 55811125759 831230790598656 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz57 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz124 1 6))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz191)) ↑qz192) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz221)))))

noncomputable def ep867 := @List.cons EMRow03.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz245 (ep855 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 6 rfl) (ep858 (@ep859 ep304 ep305 (@ep860 ep302 ep303 ep304 ep305 (@Eq.refl Real (hardyZApproximantEM 1 6 qz137)) EMRow03.d10) rfl rfl rfl)) (ep861 (hardyZErrorBoundEM 1 5 qz37) (BSN.hardyZErrorBoundEM_le_strong 1 5 qz37 rfl) (@ep862 Bool.false ep38 ep39 ep40 ep41 6755791855749 15393162788864 2171251505 46179488366592 (@ep857 ep38 ep39 ep40 ep41 (@Eq.refl Real (hardyZApproximantEM 1 5 qz37)) EMRow03.d8) (ep863 EMRow03.d15) rfl rfl rfl rfl rfl)) (ep864 (hardyZErrorBoundEM 1 6 qz137) (BSN.hardyZErrorBoundEM_le_strong 1 6 qz137 rfl) (@ep865 Bool.false ep302 ep303 ep304 ep305 15045499686575 30786325577728 55811125759 831230790598656 (@ep860 ep302 ep303 ep304 ep305 (@Eq.refl Real (hardyZApproximantEM 1 6 qz137)) EMRow03.d10) (ep866 EMRow03.d17) rfl rfl rfl rfl rfl)))) (@List.nil EMRow03.d0)

noncomputable abbrev qz381 := (@Enclosure.dec_le_dec qz388 qz400 23170 1000 27670 1000 (@Eq.refl Real qz388) (@Eq.refl Real qz400) rfl rfl rfl)

noncomputable abbrev qz248 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep867 (@List.IsChain.singleton EMRow03.d1 EMRow03.d18 (EMRow03.d2 qz261 qz326 qz381))))

noncomputable abbrev qz382 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep868 := And (@Eq (Option Real) (@Option.map qz382 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz382 qz248)) (@Option.some Real qz37))

noncomputable def ep869 := ep868 (@Eq (Option Real) (@Option.map qz382 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz382 qz248)) (@Option.some Real qz137))

noncomputable def ep870 := @And.intro (@Eq Nat (@List.length qz382 qz248) 1) ep869

noncomputable def ep871 := @And.intro (@Eq (Option Real) (@Option.map qz382 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz382 qz248)) (@Option.some Real qz37))

noncomputable def ep872 := @ep871 (@Eq (Option Real) (@Option.map qz382 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz382 qz248)) (@Option.some Real qz137))

noncomputable abbrev qz249 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep867 (@List.IsChain.singleton EMRow03.d1 EMRow03.d18 (EMRow03.d2 qz261 qz326 qz381)))

theorem EMRow03.d19 : Zeta.Certificates.BatchSpec 1 23170 1000 27670 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz382 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz382 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz382 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz37)) (@Eq (Option Real) (@Option.map qz382 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz382 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz137)))) qz249 (ep870 (@Eq.refl Nat 1) (ep872 (@Eq.refl (Option Real) (@Option.some Real qz37)) (@Eq.refl (Option Real) (@Option.some Real qz137))))

theorem solution : Zeta.Certificates.BatchSpec 1 23170 1000 27670 1000 := EMRow03.d19
#print axioms solution
#check solution
