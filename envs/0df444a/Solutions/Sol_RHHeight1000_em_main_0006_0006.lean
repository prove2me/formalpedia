-- Prove2me | solution 1 for RHHeight1000.em_main_0006_0006
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:46:58.700177+00:00
-- url     : https://prove2.me/submissions/6c1082a9-dec6-436b-85ad-63319c219508

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow06.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow06.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow06.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow06.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow06.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz249 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz249

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz250 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138516661214455 2251799813685248 31250000003539 1769500000000000000 4138516661214455 2251799813685248 31250000003539 1769500000000000000 120446 65536

noncomputable abbrev qz251 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 65536 qz251 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 779317518150410741488063439345657628452599855445271348474342368876423347582876053728679783827237610085654588674605917415063316248867402488514697634436426745

noncomputable def ep10 := nat_lit 13198325246229587668616048586507268161410801335203869857947191811663857046415771104290097871102374067703089877156867761119753226876438075596795543285583799

noncomputable def ep11 := nat_lit 13338205139369261376383149914767634013226508915861991492218067381232119098362059104733250767410551174650894954010182016771344050520336484956804919489535

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 4 3 ep9 131072 56624 ep10 ep11 59189 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 3 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz252 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz252

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138516661214455 2251799813685248 31250000003539 1769500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000113248 56624000000000000000 4138516661214455 2251799813685248 31250000003539 1769500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 59189 131072 24973259072661432 36028797018963968 56624 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 779317518150412560342812906055656980396982394702499187106382620393032652998517540933158707129341055012778793601285942846917973645097155238594697634436426745

noncomputable def ep18 := nat_lit 13198325246229655554962711811363413523213721429909419700721697472804734044169853548961061453892255410264786862895235075217650796661500958924795543285583799

noncomputable def ep19 := nat_lit 13338205139369401582665284895604560799810298653799657073142644093199656832454717421805370366589019475922075211274104314270069372987910244956804919489535

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 4 3 ep17 131072 56624 ep18 ep19 59189 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 3 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138516661214455 2251799813685248 31250000003539 1769500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000113248 56624000000000000000 4138516661214455 2251799813685248 31250000003539 1769500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 59189 131072 24973259072661432 36028797018963968 56624 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz253 := (Real.log (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz3 := qz253

theorem EMRow06.d4 : Enclosure.Real.IsNear qz3 Bool.false 60223 32768 1 32768 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz250) Bool.false 60223 32768 1 32768 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz250) Bool.false 120446 65536 2 65536 60223 32768 1 32768 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 150042 131072 1 56624 150042 131072 1 56624 75021 65536 2 65536 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 5456220599384213465248909714772227496572670538165976141063262914812807742611017753801422503639530882087556452122005170047444298375835020188444492540969863625638808382453421118235702266947370928498132967594635949979551089348001357731941995137847266570621617494261809398531128871567535833923098076891483476912075228072418610430965163137427706923427310178652894498746239459018086669257415154730407592571637957767157504839263249849478535520334507104454135585522664276476675

noncomputable def ep28 := nat_lit 583201912334273870627228188254822588827079241605343036411752047433839590517388190714780374919746279700129906501257101384229175562492847525225536391462542197025353003914524118772974087630067522636400444148635637549655768907025719966434833632093412247469427754039812435067522613541620617101084764807513402584784781490076808276521160080078978009740617112077674385114356333461540984478969922738031393369686631450339262287925718320742111081121726382582016608811398564907105

noncomputable def ep29 := nat_lit 2006268627360805445673839316848610509641534779303135707206598861506426804997221642604762844037348942607248852390277353874343091902420975230792155995982437872051629609224882022549487822374001366578458875613104959699164386313425243185530298109514065278868815165519648262204211929774735225023360668387821809970420335957473972782118680523137645713941929429588852958886338507735711181009301082096313539911189247153419366938656533848809858580689548163599238034961919825

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 10 9 ep27 131072 56624 ep28 ep29 150042 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 9 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 5456220599384260892400251500854699790811159195150212163211869656216336849990273498858157048596616978904240776489460003685239051624059887013466241201881443704542959173524008982544253046253151867013374679201187657749749224297051088632484873343955402287279851789208893474071824987110190207053471018354491495133306616646837230249901879422821128116650397962087630806812522581253210958036113071268120219429850657911869289056672761916619783759890108169949892385522664276476675

noncomputable def ep34 := nat_lit 583201912334279575053067226115417021307550325332234501953544426829928714668898700518418107620762577859683234776628347658361181262145210140271013263714562720079188253110303208819702903278206870150494721073991877864419341163488949363940583288588224434829960190109694548513088121652843287215458036179968684293644459891198769761601084092249455692877745995219003758983943549453190712470220270279351626860119698313725888367584660500821040083453648022042061408811398564907105

noncomputable def ep35 := nat_lit 2006268627360839170887858856494478835319319717359667041823756329478526322484078784125879825811686186445537802910004300367040714583746383402724632880452479311196631191501299191497899488881639138562974769996989848045902383299749709271247360054208480548633525642122514778503225872819822968825602771791453574137145372948950799520945900351638147820910599315255916738483881817718250085827996954508077874524152655659774549924038927632065100609588052048399238034961919825

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 10 9 ep33 131072 56624 ep34 ep35 150042 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 9 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 75021 65536 2 65536 75021 65536 1 32768 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 150042 131072 1 56624 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 150042 131072 56624 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 150042 131072 1 56624 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 150042 131072 56624 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow06.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 32768 := ep37

theorem EMRow06.d6 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow06.d7 : @Eq Nat (Nat.pow 8 1) 8 := @Eq.refl Nat 8

noncomputable def ep38 := nat_lit 136428812447130271690862832843

noncomputable def ep39 := nat_lit 45329922406348602738737152000

noncomputable def ep40 := nat_lit 3805195101417393738812520955622157

noncomputable def ep41 := nat_lit 567735565106683608321970973704192000

noncomputable abbrev qz415 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz392 := qz415

noncomputable abbrev qz254 := qz392

noncomputable abbrev qz4 := qz254

noncomputable abbrev qz5 := (@instHSub Real Real.instSub)

noncomputable abbrev qz393 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz255 := qz393

noncomputable abbrev qz6 := qz255

noncomputable abbrev qz416 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz417 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz418 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz419 := (Enclosure.sfrac Bool.false 35467 1000)

noncomputable abbrev qz394 := (@HAdd.hAdd Complex Complex Complex qz416 (@HAdd.hAdd Complex Complex Complex qz416 qz417 (@HMul.hMul Complex Complex Complex qz415 Complex.I (@HDiv.hDiv Complex Complex Complex qz418 (↑qz419) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz256 := qz394

noncomputable abbrev qz7 := (Complex.Stirling.logGammaStirling 1 qz256)

noncomputable abbrev qz395 := qz416

noncomputable abbrev qz257 := qz395

noncomputable abbrev qz8 := qz257

noncomputable abbrev qz396 := (@HAdd.hAdd Complex Complex Complex qz416 qz417 (@HMul.hMul Complex Complex Complex qz415 Complex.I (@HDiv.hDiv Complex Complex Complex qz418 (↑qz419) (2 : Complex))))

noncomputable abbrev qz258 := qz396

noncomputable abbrev qz9 := qz258

noncomputable abbrev qz397 := qz419

noncomputable abbrev qz259 := qz397

noncomputable abbrev qz10 := (@HMul.hMul Real Real Real qz249 (@HDiv.hDiv Real Real Real qz252 qz259 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz420 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 35467 1000)))

noncomputable abbrev qz398 := qz420

noncomputable abbrev qz260 := qz398

noncomputable abbrev qz11 := qz260

noncomputable def ep42 := Complex.re (@HMul.hMul Complex Complex Complex qz4 (Complex.exp (@HMul.hMul Complex Complex Complex qz4 Complex.I ↑(@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10))) (zetaApproximant qz11 1 8))

noncomputable def ep43 := @Enclosure.Real.IsNear.of_eq ep42 (@HSub.hSub Real Real Real qz5 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 8))))

noncomputable def ep44 := nat_lit 136428957495253353328929073193

noncomputable def ep45 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 8))) ep44

noncomputable def ep46 := nat_lit 151731569934120640928284709262563

noncomputable def ep47 := nat_lit 22709422604267344332878838948167680

noncomputable def ep48 := nat_lit 906598448126972054774743040

noncomputable def ep49 := nat_lit 5952926532188857802701612029041

noncomputable def ep50 := nat_lit 283867782553341804160985486852096000

noncomputable def ep51 := nat_lit 123686149644374033015644749937393680548139380861797662720

noncomputable def ep52 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 8)) 131071 131072 373823

noncomputable def ep53 := nat_lit 152990909000461297123328000

noncomputable def ep54 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) Bool.false 131071 131072 2990584

noncomputable abbrev qz12 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz261 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1647079) qz12)

noncomputable def ep55 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) qz261 Bool.false 1647079 131072 101

noncomputable def ep56 := nat_lit 173948928000000000000000000

noncomputable def ep57 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) Bool.false 84889846038812529199 6755399441055744000 132900771259277596326877 ep56

noncomputable def ep58 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10 222024877677803311663 6755399441055744000 38762486509277596326877 ep56 2660769807 131072000

noncomputable def ep59 := nat_lit 11126681899999235827171328000

noncomputable def ep60 := nat_lit 14495744000000000000000000

noncomputable def ep61 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 6227548056493499531 225179981368524800 5241004000986835438737 ep60 Bool.false 222024877677803311663 6755399441055744000

noncomputable def ep62 := @Enclosure.Complex.IsNear.subLitP qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 4931978906027352731 225179981368524800 4985004000870869486737 ep60 Bool.false 242677047478287991663 6755399441055744000 32618486509103647398877

noncomputable def ep63 := nat_lit 3505797888331997632559361317404672

noncomputable def ep64 := nat_lit 62494447273545934354060435341180928

noncomputable abbrev qz421 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz399 := qz421

noncomputable abbrev qz262 := (@HSub.hSub Complex Complex Complex qz393 qz394 qz399)

noncomputable abbrev qz263 := (Complex.log qz394)

noncomputable abbrev qz13 := (@HSub.hSub Complex Complex Complex qz255 (@HMul.hMul Complex Complex Complex qz254 qz262 qz263) qz256)

noncomputable abbrev qz264 := qz399

noncomputable abbrev qz14 := (@HMul.hMul Complex Complex Complex qz254 qz264 ↑qz253)

noncomputable abbrev qz400 := qz418

noncomputable abbrev qz265 := qz400

noncomputable abbrev qz15 := qz265

noncomputable abbrev qz16 := (@instHMul Nat instMulNat)

noncomputable abbrev qz401 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz266 := qz401

noncomputable abbrev qz17 := qz266

noncomputable abbrev qz18 := qz256

noncomputable abbrev qz267 := (@instHSub Int Int.instSub)

noncomputable abbrev qz19 := qz267

noncomputable abbrev qz268 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz20 := qz268

noncomputable abbrev qz269 := (@instHMul Int Int.instMul)

noncomputable abbrev qz21 := qz269

noncomputable abbrev qz270 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz22 := qz270

noncomputable def ep65 := @Enclosure.Complex.IsNear.of_eq qz7 (@HAdd.hAdd Complex Complex Complex qz8 (@HAdd.hAdd Complex Complex Complex qz8 qz13 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k)))))) Bool.true 4931978906027352731

noncomputable def ep66 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz8 qz13 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) Bool.true 4932111037298827931 225179981368524800

noncomputable def ep67 := nat_lit 5295672026487334315275321344

noncomputable def ep68 := nat_lit 130286247801135774282763206656000

noncomputable def ep69 := @ep66 4868128418193359713 14156000000000000000000 Bool.false 80902763158996910373 2251799813685248000 663546875254132051 3539000000000000000000 Bool.false 630051 1073741824 3 1073741824 Bool.true 7448672939 1610612736000 35467 1610612736000 Bool.true ep67 4931978906027352731 225179981368524800 4985004000870869486737 ep60 Bool.false ep68

noncomputable def ep70 := @Enclosure.Complex.IsNear.addLitP qz13 qz14 Bool.true 5139035689672434331 225179981368524800 4652125000224609713 14156000000000000000000

noncomputable def ep71 := @ep70 Bool.false 80902763158996910373 2251799813685248000 663546875254132051 3539000000000000000000 Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 Bool.true 323230828940415987286016 4932111037298827931 225179981368524800 4868128418193359713 14156000000000000000000 Bool.false 80902763158996910373 80902763158996910373 2251799813685248000

noncomputable abbrev qz23 := (@HMul.hMul Complex Complex Complex qz254 qz262 qz263)

noncomputable def ep72 := @Enclosure.Complex.IsNear.subLitP qz23 qz18 Bool.true 4632380731593253531 225179981368524800 4652125000224609713 14156000000000000000000 Bool.false 120835055154984255781

noncomputable def ep73 := @ep72 2251799813685248000 663546875254132051 3539000000000000000000 Bool.false 9000 4000 0 1 Bool.false 70934 4000 0 1 Bool.true 20556142758689737324000 5139035689672434331 225179981368524800 4652125000224609713 14156000000000000000000 Bool.false 323611052635987641492000 80902763158996910373 2251799813685248000 663546875254132051 3539000000000000000000

noncomputable abbrev qz24 := qz262

noncomputable abbrev qz25 := qz263

noncomputable def ep74 := @Enclosure.Complex.IsNear.mul qz24 qz25 Bool.true 4632380731593253531 225179981368524800 4652125000224609713 14156000000000000000000 Bool.false 120835055154984255781 2251799813685248000 663546875254132051

noncomputable abbrev qz26 := (Complex.re qz262)

noncomputable abbrev qz27 := (Complex.re qz263)

noncomputable abbrev qz28 := (Complex.im qz262)

noncomputable abbrev qz29 := (Complex.im qz263)

noncomputable def ep75 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz26 qz27) (@HMul.hMul Real Real Real qz0 qz28 qz29) 22725253871160001 4503599627370496 54687500024773 3539000000000000000 5768643425151253581 225179981368524800

noncomputable def ep76 := nat_lit 20862388136641642249460406997221376

noncomputable def ep77 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz27 7000 4000 0 1 3246464838737143 1125899906842624 7812500003539 884750000000000000

noncomputable def ep78 := @Enclosure.Complex.IsNear.re_isNear qz24 Bool.false 7000 4000 0 1 Bool.false 70934 4000 0 1

noncomputable abbrev qz271 := (Enclosure.sfrac Bool.false 70934 4000)

noncomputable abbrev qz30 := qz271

noncomputable def ep79 := @Enclosure.Complex.IsNear.of_eq qz24 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz30) Bool.false 7000 4000 0 1 Bool.false 70934 4000 0

noncomputable abbrev qz272 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz31 := (Complex.mk qz272 qz271)

noncomputable def ep80 := @Enclosure.Complex.IsNear.of_eq qz25 (Complex.log qz31) Bool.false 3246464838737143 1125899906842624 7812500003539 884750000000000000 Bool.false 813240959927715 562949953421312 125000000003539 7078000000000000000

noncomputable def ep81 := nat_lit 107862826721941779351241307685961536925440

noncomputable def ep82 := nat_lit 441420520907722545532371005053235693568

noncomputable def ep83 := nat_lit 3204623149525941918432053123443385088

noncomputable def ep84 := BSN.log_dyadic_bound 1016632356 9208632356 3 2 ep81 131072 56624 ep82 ep83 29059 10225264712 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1016632356) (BSN.artanhQ 9208632356) 0 2 ep82 ep81 ep83 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz32 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz33 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz273 := (Real.log (Enclosure.sfrac Bool.false 5112632356 16000000))

noncomputable abbrev qz274 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep85 := @Enclosure.Real.IsNear.mulLit_ff qz32 qz273 1 2 0 1 3246464838737143 562949953421312 7812500003539 442375000000000000 3246464838737143 1125899906842624 7812500003539 884750000000000000 qz33 (BSN.isNear_log_sfrac 5112632356 16000000 3246464838737143 562949953421312 7812500003539 442375000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5112632356) qz274)) Bool.false 27233320917949107666944 4722366482869645213696 1000000000452992 56624000000000000000 3246464838737143 562949953421312 7812500003539 442375000000000000 (BSN.log_rat_reduce_isNear 5112632356 16000000 8 10225264712 8192000000 29059 131072 24973259072661432 36028797018963968 56624 1000000000000000 rfl rfl rfl rfl (ep84 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep86 := BSN.arctan_dyadic_bound_f 9000 70934 1 0 131072 56624 0 1 1 0 1 1 16540 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 70934) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 70934) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz249 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz35 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz275 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 70934)))

noncomputable def ep87 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz275 884279719003555 562949953421312 1 2000000000000000 16540 131072 1 56624 106593119099645460480 813240959927715 562949953421312 125000000003539 7078000000000000000 qz35 (ep86 rfl) rfl rfl

noncomputable abbrev qz36 := qz259

noncomputable abbrev qz276 := (@Eq.refl Real qz397)

noncomputable abbrev qz37 := qz276

noncomputable abbrev qz277 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 70934) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep88 := @Enclosure.Complex.IsNear.re_isNear qz25 Bool.false 3246464838737143 1125899906842624 7812500003539 884750000000000000 Bool.false 813240959927715 562949953421312 125000000003539 7078000000000000000 (ep80 (@congrArg Complex Complex qz18 qz31 Complex.log (BSN.w_shift_mk qz36 Bool.false 35467 1000 2 qz37 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz31) Bool.false 3246464838737143 1125899906842624 7812500003539 884750000000000000 Bool.false 813240959927715 562949953421312 125000000003539 7078000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz31)) (@HMul.hMul Real Real Real qz0 qz32 qz273) Bool.false 3246464838737143 1125899906842624 7812500003539 884750000000000000 (Enclosure.clog_re_eq 9000 70934 4000 5112632356 16000000 rfl rfl rfl) (ep85 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz31)) qz277 Bool.false 813240959927715 562949953421312 125000000003539 7078000000000000000 (Enclosure.clog_im_eq 9000 70934 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz277 (@HSub.hSub Real Real Real qz5 qz34 qz275) Bool.false 813240959927715 562949953421312 125000000003539 7078000000000000000 (BSN.arctan_recip 70934 9000 rfl rfl) ep87))))

noncomputable def ep89 := @Enclosure.Real.IsNear.mulLit_ff qz28 qz29 70934 4000 0 1 813240959927715 562949953421312 125000000003539 7078000000000000000

noncomputable def ep90 := @Enclosure.Complex.IsNear.im_isNear qz24 Bool.false 7000 4000 0 1 Bool.false 70934 4000 0 1

noncomputable def ep91 := @Enclosure.Complex.IsNear.im_isNear qz25 Bool.false 3246464838737143 1125899906842624 7812500003539 884750000000000000 Bool.false 813240959927715 562949953421312 125000000003539 7078000000000000000 (ep80 (@congrArg Complex Complex qz18 qz31 Complex.log (BSN.w_shift_mk qz36 Bool.false 35467 1000 2 qz37 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz31) Bool.false 3246464838737143 1125899906842624 7812500003539 884750000000000000 Bool.false 813240959927715 562949953421312 125000000003539 7078000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz31)) (@HMul.hMul Real Real Real qz0 qz32 qz273) Bool.false 3246464838737143 1125899906842624 7812500003539 884750000000000000 (Enclosure.clog_re_eq 9000 70934 4000 5112632356 16000000 rfl rfl rfl) (ep85 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz31)) qz277 Bool.false 813240959927715 562949953421312 125000000003539 7078000000000000000 (Enclosure.clog_im_eq 9000 70934 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz277 (@HSub.hSub Real Real Real qz5 qz34 qz275) Bool.false 813240959927715 562949953421312 125000000003539 7078000000000000000 (BSN.arctan_recip 70934 9000 rfl rfl) ep87))))

noncomputable abbrev qz278 := (Enclosure.Real.IsNear.const Bool.false 70934 4000)

noncomputable abbrev qz38 := (@ep79 1 (BSN.w_sub_half_mk qz259 Bool.false 35467 1000 2 qz276 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz271 Bool.false 7000 4000 0 1 Bool.false 70934 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz278))

noncomputable def ep92 := @ep75 4433375000125517713 14156000000000000000000 ep76 4632380731593253531 225179981368524800 4652125000224609713 14156000000000000000000 (@ep77 22725253871160001 4503599627370496 54687500024773 3539000000000000000 (ep78 qz38) ep88 rfl) (@ep89 5768643425151253581 225179981368524800 4433375000125517713 14156000000000000000000 (ep90 qz38) ep91 rfl) rfl

noncomputable def ep93 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz26 qz29) (@HMul.hMul Real Real Real qz0 qz28 qz27) 5692686719494005 2251799813685248 875000000024773 28312000000000000000 115142368435490250781 2251799813685248000

noncomputable def ep94 := nat_lit 272096354684640213060442620258418688

noncomputable def ep95 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz29 7000 4000 0 1 813240959927715 562949953421312 125000000003539 7078000000000000000

noncomputable def ep96 := @Enclosure.Real.IsNear.mulLit_ff qz28 qz27 70934 4000 0 1 3246464838737143 1125899906842624 7812500003539 884750000000000000

noncomputable def ep97 := @ep93 277085937625517713 1769500000000000000000 ep94 120835055154984255781 2251799813685248000 663546875254132051 3539000000000000000000 (@ep95 5692686719494005 2251799813685248 875000000024773 28312000000000000000 (ep78 qz38) ep91 rfl) (@ep96 115142368435490250781 2251799813685248000 277085937625517713 1769500000000000000000 (ep90 qz38) ep88 rfl) rfl

noncomputable def ep98 := @Enclosure.Complex.IsNear.of_eq qz18 qz31 Bool.false 9000 4000 0 1 Bool.false 70934 4000 0 1 (BSN.w_shift_mk qz36 Bool.false 35467 1000 2 qz37 rfl)

noncomputable abbrev qz279 := (ep98 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 70934 4000) Bool.false 9000 4000 0 1 Bool.false 70934 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 70934 4000)))

noncomputable abbrev qz39 := qz279

noncomputable def ep99 := ep73 (@ep74 3539000000000000000000 (ep92 rfl) (ep97 rfl)) qz39 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz40 := qz264

noncomputable abbrev qz41 := (Complex.im ↑qz253)

noncomputable def ep100 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz40) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz40) qz41) 60223 65536 1 65536 0 1 0 1 60223 60223

noncomputable def ep101 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz40) (Complex.re ↑qz3) 1 2 0 1 60223 32768 1 32768 60223 65536 1 65536

noncomputable abbrev qz280 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz281 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz42 := (@Enclosure.Complex.IsNear.of_eq qz264 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz280) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz280 Bool.false 1 2 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 2) qz281))

noncomputable def ep102 := ep101 (@Enclosure.Complex.IsNear.re_isNear qz40 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz42) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 60223 32768 1 32768 (Complex.ofReal_re qz3) EMRow06.d4)

noncomputable def ep103 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz40) qz41 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable abbrev qz43 := qz280

noncomputable abbrev qz44 := qz281

noncomputable def ep104 := ep103 (@Enclosure.Complex.IsNear.im_isNear qz40 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz42) (@Enclosure.Real.IsNear.of_eq qz41 qz43 Bool.false 0 1 0 1 (@Eq.trans Real qz41 (0 : Real) qz43 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz44)

noncomputable def ep105 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz40) qz41) (@HMul.hMul Real Real Real qz0 (Complex.im qz40) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep106 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz40) qz41 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep107 := ep106 (@Enclosure.Complex.IsNear.re_isNear qz40 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz42) (@Enclosure.Real.IsNear.of_eq qz41 qz43 Bool.false 0 1 0 1 (@Eq.trans Real qz41 (0 : Real) qz43 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz44)

noncomputable def ep108 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz40) (Complex.re ↑qz3) 0 1 0 1 60223 32768 1 32768 0 1 0 1

noncomputable def ep109 := ep108 (@Enclosure.Complex.IsNear.im_isNear qz40 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz42) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 60223 32768 1 32768 (Complex.ofReal_re qz3) EMRow06.d4)

noncomputable def ep110 := @ep71 663546875254132051 3539000000000000000000 (ep99 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz40 (↑qz3) Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 (@ep100 65536 1 65536 (ep102 rfl) (ep104 rfl) rfl rfl) (@ep105 1 0 1 (ep107 rfl) (ep109 rfl) rfl rfl))

noncomputable abbrev qz45 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz282 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz46 := (@HMul.hMul Complex Complex Complex qz254 (@HMul.hMul Complex Complex Complex qz254 (2 : Complex) qz282) (@HSub.hSub Complex Complex Complex qz255 (@HMul.hMul Complex Complex Complex qz254 (2 : Complex) qz282) (1 : Complex)))

noncomputable abbrev qz283 := (@HPow.hPow Complex Int Complex qz401 qz394 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz47 := qz283

noncomputable def ep111 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46) qz47)) Bool.false 630051 1073741824 3 1073741824

noncomputable def ep112 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46) qz47) Bool.false 0 1 0 1 Bool.false

noncomputable def ep113 := @ep112 0 1 0 1 Bool.false 630051 1073741824 3 1073741824 Bool.true 7448672939 1610612736000 35467 1610612736000 Bool.false 630051 630051 1073741824 3 1073741824 Bool.true 7448672939 7448672939 1610612736000 35467

noncomputable def ep114 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz43 qz43) Bool.false 0 1 0 1 Bool.false

noncomputable def ep115 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46) qz47 Bool.false 630051 1073741824 3 1073741824 Bool.true 7448672939 1610612736000 35467 1610612736000

noncomputable abbrev qz48 := (Complex.re qz283)

noncomputable abbrev qz49 := (Complex.im qz283)

noncomputable def ep116 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz48) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz49) 630051 1073741824 3 1073741824 0 1 0

noncomputable def ep117 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz48 1 12 0 1 1890153 268435456 9 268435456 630051

noncomputable def ep118 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz43) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz284 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz43 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz44)

noncomputable def ep119 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep118 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz284)

noncomputable def ep120 := @Enclosure.Complex.IsNear.re_isNear qz47 Bool.false 1890153 268435456 9 268435456 Bool.true 7448672939 134217728000 35467 134217728000

noncomputable abbrev qz402 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz285 := (@HPow.hPow Complex Nat Complex qz402 qz394 1)

noncomputable abbrev qz50 := (@Inv.inv Complex Complex.instInv qz285)

noncomputable def ep121 := @Enclosure.Complex.IsNear.of_eq qz47 qz50 Bool.false 1890153 268435456 9 268435456 Bool.true 7448672939 134217728000 35467

noncomputable def ep122 := @Enclosure.Complex.IsNear.of_parts qz50 Bool.false 1890153 268435456 9 268435456 Bool.true 7448672939 134217728000 35467

noncomputable abbrev qz51 := (Complex.re qz285)

noncomputable abbrev qz52 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz53 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz54 := qz285

noncomputable def ep123 := @Enclosure.Real.IsNear.mulLit_ff qz51 (@Inv.inv Real Real.instInv (@DFunLike.coe qz52 Complex (fun (x : Complex) => Real) qz53 Complex.normSq qz54)) 9000 4000 0 1 210017 67108864 1 67108864

noncomputable def ep124 := @Enclosure.Complex.IsNear.re_isNear qz54 Bool.false 9000 4000 0 1 Bool.false 70934 4000 0 1

noncomputable def ep125 := @Enclosure.Complex.IsNear.of_eq qz54 qz18 Bool.false 9000 4000 0 1 Bool.false 70934 4000 0

noncomputable def ep126 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz52 Complex (fun (x : Complex) => Real) qz53 Complex.normSq qz54)) Bool.false 210017 67108864 1 67108864 210017 67108864 1

noncomputable abbrev qz55 := (@instHAdd Real Real.instAdd)

noncomputable abbrev qz56 := (Complex.im qz285)

noncomputable def ep127 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz52 Complex (fun (x : Complex) => Real) qz53 Complex.normSq qz54) (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 qz51 qz51) (@HMul.hMul Real Real Real qz0 qz56 qz56)) Bool.false 1278158089 4000000 0 1

noncomputable def ep128 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz51 qz51) (@HMul.hMul Real Real Real qz0 qz56 qz56) 81 16 0 1 1257908089 4000000

noncomputable def ep129 := @Enclosure.Real.IsNear.mulLit_ff qz51 qz51 9000 4000 0 1 9000 4000 0 1

noncomputable def ep130 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 70934 4000 0 1 70934 4000 0 1

noncomputable def ep131 := @Enclosure.Complex.IsNear.im_isNear qz54 Bool.false 9000 4000 0 1 Bool.false 70934 4000 0 1

noncomputable abbrev qz57 := (ep124 (@ep125 1 (BSN.pow_one_c qz256) qz279))

noncomputable abbrev qz58 := (ep131 (@ep125 1 (BSN.pow_one_c qz256) qz279))

noncomputable def ep132 := @ep128 0 1 20450529424 1278158089 4000000 0 1 (@ep129 81 16 0 1 qz57 qz57 rfl) (@ep130 1257908089 4000000 0 1 qz58 qz58 rfl)

noncomputable def ep133 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz52 Complex (fun (x : Complex) => Real) qz53 Complex.normSq qz54) 1278158089 4000000 0 1 105008 105009 33554432 (ep127 (Enclosure.Complex.normSq_eq_mul_add_mul qz54) (ep132 rfl rfl)) rfl

noncomputable def ep134 := @Enclosure.Real.IsNear.of_eq (Complex.re qz50) (@HMul.hMul Real Real Real qz0 qz51 (@Inv.inv Real Real.instInv (@DFunLike.coe qz52 Complex (fun (x : Complex) => Real) qz53 Complex.normSq qz54))) Bool.false 1890153 268435456 9 268435456 (Enclosure.Complex.inv_re_eq_mul qz54) (@ep123 1890153 268435456 9 268435456 qz57 (@ep126 67108864 (ep133 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep135 := @Enclosure.Real.IsNear.of_eq (Complex.im qz50) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz56) (@Inv.inv Real Real.instInv (@DFunLike.coe qz52 Complex (fun (x : Complex) => Real) qz53 Complex.normSq qz54))) Bool.true 7448672939 134217728000 35467 134217728000 (Enclosure.Complex.inv_im_eq_mul qz54)

noncomputable def ep136 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz56) (@Inv.inv Real Real.instInv (@DFunLike.coe qz52 Complex (fun (x : Complex) => Real) qz53 Complex.normSq qz54)) 70934 4000 0 1 210017 67108864 1

noncomputable def ep137 := @ep136 67108864 7448672939 134217728000 35467 134217728000 (@Enclosure.Real.IsNear.neg qz56 Bool.false 70934 4000 0 1 qz58) (@ep126 67108864 (ep133 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep138 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz49 0 1 0 1 7448672939 134217728000 35467 134217728000 0

noncomputable def ep139 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep118 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz284)

noncomputable def ep140 := @Enclosure.Complex.IsNear.im_isNear qz47 Bool.false 1890153 268435456 9 268435456 Bool.true 7448672939 134217728000 35467 134217728000

noncomputable abbrev qz59 := (@ep121 134217728000 (BSN.zpow_one_sub_two_mul qz256 1 1 rfl rfl) (@ep122 134217728000 ep134 (ep135 ep137)))

noncomputable def ep141 := @ep116 1 630051 630051 1073741824 3 1073741824 (@ep117 1073741824 3 1073741824 ep119 (ep120 qz59) rfl) (@ep138 1 0 1 ep139 (ep140 qz59) rfl) rfl

noncomputable def ep142 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz49) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz48) 7448672939 1610612736000 35467 1610612736000 0 1 0

noncomputable def ep143 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz49 1 12 0 1 7448672939 134217728000 35467 134217728000 7448672939

noncomputable def ep144 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz48 0 1 0 1 1890153 268435456 9 268435456 0

noncomputable def ep145 := @ep142 1 7448672939 7448672939 1610612736000 35467 1610612736000 (@ep143 1610612736000 35467 1610612736000 ep119 (ep140 qz59) rfl) (@ep144 1 0 1 ep139 (ep120 qz59) rfl) rfl

noncomputable abbrev qz60 := (@Enclosure.Complex.IsNear.mk qz280 qz280 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz281 qz281)

noncomputable def ep146 := @ep113 1610612736000 (@ep114 0 1 0 1 (BSN.stirling_sum_base qz18) qz60) (ep115 (ep141 rfl) (ep145 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep147 := @ep69 242677047478287991663 6755399441055744000 32618486509103647398877 ep56 (ep110 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep111 Bool.true 7448672939 1610612736000 35467 1610612736000 (BSN.stirling_sum_succ qz18 0 1 rfl) (ep146 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep148 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz36 2) Bool.false 3238922876165367 562949953421312 7812500003539 442375000000000000 Bool.false 860507075020195 281474976710656

noncomputable abbrev qz61 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz257 qz258 qz282))

noncomputable def ep149 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz36 2) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz36 1) qz61) Bool.false 3238922876165367 562949953421312 7812500003539 442375000000000000 Bool.false 860507075020195 281474976710656 125000000003539 3539000000000000000

noncomputable def ep150 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz36 1) qz61 Bool.false 3237582846369015 1125899906842624 7812500003539 884750000000000000 Bool.false 876346914407843 562949953421312 125000000003539 7078000000000000000 Bool.false

noncomputable def ep151 := nat_lit 7293405929090060990722936406016

noncomputable def ep152 := nat_lit 968844835602656412183486791680

noncomputable abbrev qz62 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz257 qz258 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep153 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz36 1) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz36 0) qz62) Bool.false 3237582846369015 1125899906842624 7812500003539 884750000000000000 Bool.false 876346914407843 562949953421312 125000000003539 7078000000000000000

noncomputable def ep154 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz36 0) qz62 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz286 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz30))

noncomputable def ep155 := @Enclosure.Complex.IsNear.of_eq qz62 qz286 Bool.false 3237582846369015 1125899906842624 7812500003539 884750000000000000 Bool.false 876346914407843 562949953421312 125000000003539 7078000000000000000

noncomputable def ep156 := nat_lit 104163155090453911016155967330684736925440

noncomputable def ep157 := nat_lit 367836104461567083181890175572275693568

noncomputable def ep158 := nat_lit 2308861491636955971382542068083385088

noncomputable def ep159 := BSN.log_dyadic_bound 936632356 9128632356 3 2 ep156 131072 56624 ep157 ep158 26991 10065264712 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 936632356) (BSN.artanhQ 9128632356) 0 2 ep157 ep156 ep158 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep160 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 5032632356 16000000)) 1 2 0 1 3237582846369015 562949953421312 7812500003539 442375000000000000 3237582846369015 1125899906842624 7812500003539 884750000000000000 qz33 (BSN.isNear_log_sfrac 5032632356 16000000 3237582846369015 562949953421312 7812500003539 442375000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5032632356) qz274)) Bool.false 27158813365713890181120 4722366482869645213696 1000000000452992 56624000000000000000 3237582846369015 562949953421312 7812500003539 442375000000000000 (BSN.log_rat_reduce_isNear 5032632356 16000000 8 10065264712 8192000000 26991 131072 24973259072661432 36028797018963968 56624 1000000000000000 rfl rfl rfl rfl (ep159 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep161 := BSN.arctan_dyadic_bound_f 1000 70934 1 0 131072 56624 0 1 1 0 1 1 1847 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 70934) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 70934) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz287 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz288 := (@Nat.cast Real Real.instNatCast 70934)

noncomputable def ep162 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz287 qz288)) 884279719003555 562949953421312 1 2000000000000000 1847 131072 1 56624 114864542765264797696 876346914407843 562949953421312 125000000003539 7078000000000000000 qz35 (ep161 rfl) rfl rfl

noncomputable abbrev qz63 := (@HAdd.hAdd Complex Complex Complex qz257 qz258 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz289 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz30)

noncomputable def ep163 := @ep154 3237582846369015 1125899906842624 7812500003539 884750000000000000 Bool.false 876346914407843 562949953421312 125000000003539 7078000000000000000 Bool.false 3237582846369015 3237582846369015 1125899906842624 7812500003539 884750000000000000 Bool.false 876346914407843 876346914407843 562949953421312 125000000003539 7078000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz36 0) (Complex.mk qz43 qz43) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz36) qz60) (ep155 (@congrArg Complex Complex qz63 qz289 Complex.log (BSN.w_shift_mk qz36 Bool.false 35467 1000 0 qz37 rfl)) (@Enclosure.Complex.IsNear.of_parts qz286 Bool.false 3237582846369015 1125899906842624 7812500003539 884750000000000000 Bool.false 876346914407843 562949953421312 125000000003539 7078000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz286) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 5032632356 16000000))) Bool.false 3237582846369015 1125899906842624 7812500003539 884750000000000000 (Enclosure.clog_re_eq 1000 70934 4000 5032632356 16000000 rfl rfl rfl) (ep160 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz286) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz288 qz287)) Bool.false 876346914407843 562949953421312 125000000003539 7078000000000000000 (Enclosure.clog_im_eq 1000 70934 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz288 qz287)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz287 qz288))) Bool.false 876346914407843 562949953421312 125000000003539 7078000000000000000 (BSN.arctan_recip 70934 1000 rfl rfl) ep162)))) rfl rfl

noncomputable abbrev qz290 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz30))

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq qz61 qz290 Bool.false 3240262905961719 1125899906842624 7812500003539 884750000000000000 Bool.false 844667235632547 562949953421312 125000000003539 7078000000000000000

noncomputable def ep165 := nat_lit 105262900012639475398326942877267776925440

noncomputable def ep166 := nat_lit 389078756216163389239233592416563693568

noncomputable def ep167 := nat_lit 2554759933761299252572083384691385088

noncomputable def ep168 := BSN.log_dyadic_bound 960632356 9152632356 3 2 ep165 131072 56624 ep166 ep167 27615 10113264712 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 960632356) (BSN.artanhQ 9152632356) 0 2 ep166 ep165 ep167 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep169 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 5056632356 16000000)) 1 2 0 1 3240262905961719 562949953421312 7812500003539 442375000000000000 3240262905961719 1125899906842624 7812500003539 884750000000000000 qz33 (BSN.isNear_log_sfrac 5056632356 16000000 3240262905961719 562949953421312 7812500003539 442375000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5056632356) qz274)) Bool.false 27181295335053723697152 4722366482869645213696 1000000000452992 56624000000000000000 3240262905961719 562949953421312 7812500003539 442375000000000000 (BSN.log_rat_reduce_isNear 5056632356 16000000 8 10113264712 8192000000 27615 131072 24973259072661432 36028797018963968 56624 1000000000000000 rfl rfl rfl rfl (ep168 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep170 := BSN.arctan_dyadic_bound_f 5000 70934 1 0 131072 56624 0 1 1 0 1 1 9223 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 70934) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 70934) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz291 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep171 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz291 qz288)) 884279719003555 562949953421312 1 2000000000000000 9223 131072 1 56624 110712223908829200384 844667235632547 562949953421312 125000000003539 7078000000000000000 qz35 (ep170 rfl) rfl rfl

noncomputable abbrev qz64 := (@HAdd.hAdd Complex Complex Complex qz257 qz258 qz282)

noncomputable abbrev qz292 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz30)

noncomputable def ep172 := @ep150 3240262905961719 1125899906842624 7812500003539 884750000000000000 Bool.false 844667235632547 562949953421312 125000000003539 7078000000000000000 Bool.false ep151 3238922876165367 562949953421312 7812500003539 442375000000000000 Bool.false ep152 860507075020195 281474976710656 125000000003539 3539000000000000000 (ep153 (BSN.log_sum_c_succ qz36 0 1 rfl) (ep163 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep164 (@congrArg Complex Complex qz64 qz292 Complex.log (BSN.w_shift_mk qz36 Bool.false 35467 1000 1 qz37 rfl)) (@Enclosure.Complex.IsNear.of_parts qz290 Bool.false 3240262905961719 1125899906842624 7812500003539 884750000000000000 Bool.false 844667235632547 562949953421312 125000000003539 7078000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz290) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 5056632356 16000000))) Bool.false 3240262905961719 1125899906842624 7812500003539 884750000000000000 (Enclosure.clog_re_eq 5000 70934 4000 5056632356 16000000 rfl rfl rfl) (ep169 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz290) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz288 qz291)) Bool.false 844667235632547 562949953421312 125000000003539 7078000000000000000 (Enclosure.clog_im_eq 5000 70934 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz288 qz291)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz291 qz288))) Bool.false 844667235632547 562949953421312 125000000003539 7078000000000000000 (BSN.arctan_recip 70934 5000 rfl rfl) ep171)))) rfl rfl

noncomputable def ep173 := @ep62 ep56 Bool.false 3238922876165367 562949953421312 7812500003539 442375000000000000 Bool.false 860507075020195 281474976710656 125000000003539 3539000000000000000 Bool.true ep63 6227548056493499531 225179981368524800 5241004000986835438737 ep60 Bool.false ep64 222024877677803311663 6755399441055744000 38762486509277596326877 ep56 (@ep65 225179981368524800 4985004000870869486737 ep60 Bool.false 242677047478287991663 6755399441055744000 32618486509103647398877 ep56 (BSN.logGammaStirling_unfold 1 qz18) (ep147 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep148 125000000003539 3539000000000000000 (BSN.log_sum_c_eq qz36 2) (ep149 (BSN.log_sum_c_succ qz36 1 2 rfl) (ep172 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz65 := (@HDiv.hDiv Real Real Real qz252 qz259 (2 : Real))

noncomputable def ep174 := @Enclosure.Real.IsNear.mulLit_ff qz65 (Real.log Real.pi) 35467 2000 0 1 75021 65536 1 32768 2660769807 131072000 35467 65536000 (@Enclosure.Real.IsNear.of_eq qz65 (Enclosure.sfrac Bool.false 35467 2000) Bool.false 35467 2000 0 1 (BSN.t_half_eq qz36 Bool.false 35467 1000 qz37) (Enclosure.Real.IsNear.const Bool.false 35467 2000)) EMRow06.d5 rfl

noncomputable def ep175 := @ep58 35467 65536000 ep59 84889846038812529199 6755399441055744000 132900771259277596326877 ep56 (@ep61 38762486509277596326877 ep56 (ep173 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep174 rfl rfl

noncomputable def ep176 := nat_lit 497143661830442952058168913000073723949609606500186728908403708532998400

noncomputable def ep177 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080

noncomputable def ep178 := nat_lit 998469887541030595578313081141409612761803151570226224381333992489216

noncomputable def ep179 := nat_lit 1300426353547522253473791789059297470971172716683661066587297076836679936

noncomputable def ep180 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800

noncomputable abbrev qz293 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz294 := (BSN.sinOddQ 268435456)

noncomputable def ep181 := BSN.sin_dyadic_bound_f 421615794 268435456 3 2 131072 56680 ep176 ep177 ep178 ep179 ep180 ep178 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 421615794) qz293 0 2 ep176 ep177 ep178 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 421615794) qz294 0 2 ep179 ep180 ep178 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz66 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep182 := @ep55 131072 Bool.false 131071 131072 1 28312 (@ep57 1647079 131072 101 131072 ep175 rfl) (Enclosure.sfrac_false_div 1647079 131072) (BSN.cos_reduce3 qz261 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29668573958805355757568) qz66) 226375608064910080 72057594037927936 Bool.false 131071 131072 1 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q3 1647079 131072 226375608064910080 72057594037927936 1 29668573958805355757568 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131071 131072 29668573958805355757568 18889465931478580854784 421615794 268435456 56680 56624 (ep181 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep183 := nat_lit 10396748296764533279098823

noncomputable def ep184 := nat_lit 2447854544007380753973248000

noncomputable abbrev qz403 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz295 := qz403

noncomputable abbrev qz67 := qz295

noncomputable abbrev qz404 := (@Neg.neg Complex Complex.instNeg qz420)

noncomputable abbrev qz296 := qz404

noncomputable abbrev qz68 := qz296

noncomputable abbrev qz405 := (@Nat.cast Complex Complex.instNatCast 8)

noncomputable abbrev qz297 := (@HPow.hPow Complex Complex Complex qz403 qz405 qz404)

noncomputable abbrev qz69 := qz297

noncomputable abbrev qz298 := qz405

noncomputable abbrev qz70 := (@HAdd.hAdd Complex Complex Complex qz257 (@HDiv.hDiv Complex Complex Complex qz265 qz298 (@HSub.hSub Complex Complex Complex qz255 qz260 (1 : Complex))) qz264)

noncomputable abbrev qz71 := (@instHSub Nat instSubNat)

noncomputable abbrev qz299 := qz402

noncomputable abbrev qz72 := qz299

noncomputable abbrev qz73 := qz298

noncomputable def ep185 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz11 1 8) (@HAdd.hAdd Complex Complex Complex qz8 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 8, @HPow.hPow Complex Complex Complex qz67 (@Nat.cast Complex Complex.instNatCast n) qz68) (@HMul.hMul Complex Complex Complex qz4 qz69 (@HAdd.hAdd Complex Complex Complex qz8 qz70 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) Bool.false 1040878283489508383463383 345839862108982870016000 650601004843286115901059

noncomputable def ep186 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 8, @HPow.hPow Complex Complex Complex qz67 (@Nat.cast Complex Complex.instNatCast n) qz68) (@HMul.hMul Complex Complex Complex qz4 qz69 (@HAdd.hAdd Complex Complex Complex qz8 qz70 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) Bool.false 52809303031 17179869184 240498143231 60799557042176

noncomputable def ep187 := nat_lit 17882152746816221064372228794089472

noncomputable def ep188 := nat_lit 49838155598545458608878794047488

noncomputable def ep189 := @ep186 Bool.true 3334537973 17179869184 240025495625 60799557042176 Bool.true 22200945036969500680617 345839862108982870016000 45431636252159624783059 ep53 Bool.false 23949443450735965695993 138335944843593148006400 733067692386041739098823 ep184 Bool.false ep187 1040878283489508383463383 345839862108982870016000 650601004843286115901059 ep53 Bool.true ep188 2900962461632761324807 138335944843593148006400

noncomputable def ep190 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 8, @HPow.hPow Complex Complex Complex qz67 (@Nat.cast Complex Complex.instNatCast n) qz68) (BSN.headSumC qz11 8) Bool.false 52809303031 17179869184 240498143231 60799557042176 Bool.true 3334537973 17179869184 240025495625

noncomputable abbrev qz74 := (BSN.headSumC qz260 7)

noncomputable abbrev qz75 := (@HPow.hPow Complex Complex Complex qz295 (@Nat.cast Complex Complex.instNatCast 7) qz296)

noncomputable def ep191 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz11 8) (@HAdd.hAdd Complex Complex Complex qz8 qz74 qz75) Bool.false 52809303031 17179869184 240498143231 60799557042176 Bool.true 3334537973 17179869184 240025495625 60799557042176

noncomputable def ep192 := @Enclosure.Complex.IsNear.addLitP qz74 qz75 Bool.false 23174157217 8589934592 105147796785 30399778521088 Bool.true 3982633335 17179869184 210238194529 60799557042176 Bool.false

noncomputable abbrev qz76 := (BSN.headSumC qz260 6)

noncomputable abbrev qz77 := (@HPow.hPow Complex Complex Complex qz295 (@Nat.cast Complex Complex.instNatCast 6) qz296)

noncomputable def ep193 := @Enclosure.Complex.IsNear.of_eq qz74 (@HAdd.hAdd Complex Complex Complex qz8 qz76 qz77) Bool.false 23174157217 8589934592 105147796785 30399778521088 Bool.true 3982633335 17179869184 210238194529 60799557042176

noncomputable def ep194 := @Enclosure.Complex.IsNear.addLitP qz76 qz77 Bool.false 20528890367 8589934592 88735760691 30399778521088 Bool.false 621848655 17179869184 177504869379 60799557042176 Bool.false

noncomputable abbrev qz78 := (BSN.headSumC qz260 5)

noncomputable abbrev qz79 := (@HPow.hPow Complex Complex Complex qz295 (@Nat.cast Complex Complex.instNatCast 5) qz296)

noncomputable def ep195 := @Enclosure.Complex.IsNear.of_eq qz76 (@HAdd.hAdd Complex Complex Complex qz8 qz78 qz79) Bool.false 20528890367 8589934592 88735760691 30399778521088 Bool.false 621848655 17179869184 177504869379 60799557042176

noncomputable def ep196 := @Enclosure.Complex.IsNear.addLitP qz78 qz79 Bool.false 34441269625 17179869184 141882550537 60799557042176 Bool.false 4527030429 17179869184 142079594979 60799557042176 Bool.false

noncomputable abbrev qz80 := (BSN.headSumC qz260 4)

noncomputable abbrev qz81 := (@HPow.hPow Complex Complex Complex qz295 (@Nat.cast Complex Complex.instNatCast 4) qz296)

noncomputable def ep197 := @Enclosure.Complex.IsNear.of_eq qz78 (@HAdd.hAdd Complex Complex Complex qz8 qz80 qz81) Bool.false 34441269625 17179869184 141882550537 60799557042176 Bool.false 4527030429 17179869184 142079594979 60799557042176

noncomputable def ep198 := @Enclosure.Complex.IsNear.addLitP qz80 qz81 Bool.false 30528830125 17179869184 102328766253 60799557042176 Bool.true 3119986581 17179869184 102324137241 60799557042176 Bool.false

noncomputable abbrev qz82 := (BSN.headSumC qz260 3)

noncomputable abbrev qz406 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz300 := qz406

noncomputable abbrev qz83 := (@HPow.hPow Complex Complex Complex qz295 qz300 qz296)

noncomputable def ep199 := @Enclosure.Complex.IsNear.of_eq qz80 (@HAdd.hAdd Complex Complex Complex qz8 qz82 qz83) Bool.false 30528830125 17179869184 102328766253 60799557042176 Bool.true 3119986581 17179869184 102324137241 60799557042176

noncomputable def ep200 := @Enclosure.Complex.IsNear.addLitP qz82 qz83 Bool.false 13771460825 8589934592 28379693643 30399778521088 Bool.false 396169209 1073741824 7056506681 7599944630272 Bool.false

noncomputable abbrev qz84 := (BSN.headSumC qz260 2)

noncomputable abbrev qz407 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz301 := qz407

noncomputable abbrev qz85 := (@HPow.hPow Complex Complex Complex qz295 qz301 qz296)

noncomputable def ep201 := @Enclosure.Complex.IsNear.of_eq qz82 (@HAdd.hAdd Complex Complex Complex qz8 qz84 qz85) Bool.false 13771460825 8589934592 28379693643 30399778521088 Bool.false 396169209 1073741824 7056506681 7599944630272

noncomputable def ep202 := @Enclosure.Complex.IsNear.addLitP qz84 qz85 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep203 := @Enclosure.Complex.IsNear.of_eq qz84 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz43) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz11)

noncomputable abbrev qz86 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable abbrev qz87 := (@HMul.hMul Real Real Real qz249 qz259 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable def ep204 := @Enclosure.Complex.IsNear.of_eq qz85 (Complex.mk (@HMul.hMul Real Real Real qz0 qz86 (Real.cos qz87)) (@HMul.hMul Real Real Real qz0 qz86 (@Neg.neg Real Real.instNeg (Real.sin qz87)))) Bool.false 5181526233 8589934592 28379693643 30399778521088 Bool.false 396169209 1073741824 7056506681 7599944630272 (BSN.cpow_neg_s_mk qz36 35467 1000 2 qz37 rfl)

noncomputable abbrev qz88 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz89 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep205 := @Enclosure.Real.IsNear.inv_image qz88 185363 131072 1 131072 46340 46342 65536 (@Enclosure.Real.IsNear.of_eq qz88 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2) qz89)) Bool.false 185363 131072 1 131072 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2) qz89)) Bool.false 185363 131072 1 131072 185363 131072 1 131072 (BSN.sqrt_enclosure 2 1 92681 92682 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep206 := BSN.log_dyadic_bound 1 3 6 5 613814355 65536 28312 24381081 945 45426 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep207 := nat_lit 5661166998794301471692579238117376

noncomputable def ep208 := nat_lit 623075623024179315423659559506411520

noncomputable def ep209 := nat_lit 4361529361169255207965616916544880640

noncomputable def ep210 := BSN.sin_dyadic_bound_f 274300432 268435456 2 1 131072 56680 ep207 ep208 ep207 ep207 ep209 ep207 111813 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 274300432) qz293 0 1 ep207 ep208 ep207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 274300432) qz294 0 1 ep207 ep209 ep207 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz90 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz302 := (Enclosure.Real.IsNear.const Bool.false 35467 1000)

noncomputable abbrev qz91 := qz302

noncomputable abbrev qz303 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3222247) qz12)

noncomputable abbrev qz304 := (BSN.isNear_log_sfrac 2 1 45426 65536 1 28312 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 45426 65536 28312 rfl rfl rfl (ep206 rfl)))

noncomputable def ep211 := @Enclosure.Real.IsNear.cos_image qz87 qz303 Bool.false 3222247 131072 83 65536 Bool.false 111813 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz87 Bool.false 805561971 32768000 35467 28312000 3222247 131072 83 65536 (@Enclosure.Real.IsNear.mulLit_ff qz36 qz90 35467 1000 0 1 45426 65536 1 28312 805561971 32768000 35467 28312000 qz91 qz304 rfl) rfl) (Enclosure.sfrac_false_div 3222247 131072) (BSN.cos_reduce3 qz303 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19302176927603945897984) qz66) 226375608064910080 72057594037927936 Bool.false 111813 131072 3 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q3 3222247 131072 226375608064910080 72057594037927936 3 19302176927603945897984 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 111813 131072 19302176927603945897984 18889465931478580854784 274300432 268435456 56680 56624 (ep210 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep212 := nat_lit 49414740979235796610524071796998727803596160830900304872302341213126656

noncomputable def ep213 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120

noncomputable def ep214 := nat_lit 32048811788237678560648636396593142579835544055991437005292753125376

noncomputable def ep215 := nat_lit 148180125314130914474450918118202997125628811404588931742896438133129216

noncomputable def ep216 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400

noncomputable abbrev qz305 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz306 := (BSN.cosOddQ 268435456)

noncomputable def ep217 := BSN.cos_dyadic_bound_f 274300432 268435456 3 2 131072 56680 ep212 ep213 ep214 ep215 ep216 ep214 68392 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 274300432) qz305 0 2 ep212 ep213 ep214 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 274300432) qz306 0 2 ep215 ep216 ep214 rfl rfl rfl rfl) rfl rfl

noncomputable def ep218 := @Enclosure.Real.IsNear.sin_image qz87 qz303 Bool.false 3222247 131072 83 65536 Bool.true 68392 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz87 Bool.false 805561971 32768000 35467 28312000 3222247 131072 83 65536 (@Enclosure.Real.IsNear.mulLit_ff qz36 qz90 35467 1000 0 1 45426 65536 1 28312 805561971 32768000 35467 28312000 qz91 qz304 rfl) rfl) (Enclosure.sfrac_false_div 3222247 131072) (BSN.sin_reduce3 qz303 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19302176927603945897984) qz66) 226375608064910080 72057594037927936 Bool.false 68392 131072 3 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q3 3222247 131072 226375608064910080 72057594037927936 3 19302176927603945897984 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 68392 131072 19302176927603945897984 18889465931478580854784 274300432 268435456 56680 56624 (ep217 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz307 := (@Enclosure.Real.IsNear.recentre' qz86 Bool.false 92682 131072 2 131072 46341 65536 1 65536 (ep205 rfl rfl) rfl)

noncomputable def ep219 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz86 (Real.cos qz87)) (@HMul.hMul Real Real Real qz0 qz86 (@Neg.neg Real Real.instNeg (Real.sin qz87))) Bool.false 5181526233 8589934592 28379693643 30399778521088 Bool.false 396169209 1073741824 7056506681 7599944630272 (@Enclosure.Real.IsNear.mulLit_ff qz86 (Real.cos qz87) 46341 65536 1 65536 111813 131072 301929 231931904 5181526233 8589934592 28379693643 30399778521088 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz87) Bool.false 111813 131072 2415432 1855455232 111813 131072 301929 231931904 (ep211 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz86 (@Neg.neg Real Real.instNeg (Real.sin qz87)) 46341 65536 1 65536 8549 16384 301929 231931904 396169209 1073741824 7056506681 7599944630272 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz87) Bool.true 8549 16384 301929 231931904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz87) Bool.true 68392 131072 2415432 1855455232 8549 16384 301929 231931904 (ep218 rfl rfl) rfl)) rfl)

noncomputable def ep220 := @ep202 5181526233 8589934592 28379693643 30399778521088 Bool.false 396169209 1073741824 7056506681 7599944630272 Bool.false 13771460825 13771460825 8589934592 28379693643 30399778521088 Bool.false 396169209 396169209 1073741824 7056506681 7599944630272 (ep203 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz43 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz44)) (ep204 ep219) rfl rfl

noncomputable abbrev qz308 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz92 := (@Inv.inv Real Real.instInv (Real.sqrt qz308))

noncomputable abbrev qz93 := (@HMul.hMul Real Real Real qz249 qz259 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep221 := @Enclosure.Complex.IsNear.of_eq qz83 (Complex.mk (@HMul.hMul Real Real Real qz0 qz92 (Real.cos qz93)) (@HMul.hMul Real Real Real qz0 qz92 (@Neg.neg Real Real.instNeg (Real.sin qz93)))) Bool.false 2985908475 17179869184 45569378967 60799557042176 Bool.true 9458693925 17179869184 45872083793 60799557042176 (BSN.cpow_neg_s_mk qz36 35467 1000 3 qz37 rfl)

noncomputable abbrev qz94 := (Real.sqrt qz308)

noncomputable abbrev qz95 := qz308

noncomputable def ep222 := @Enclosure.Real.IsNear.inv_image qz94 227023 131072 1 131072 37837 37838 65536 (@Enclosure.Real.IsNear.of_eq qz94 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz95 qz89)) Bool.false 227023 131072 1 131072 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz95 qz89)) Bool.false 227023 131072 1 131072 227023 131072 1 131072 (BSN.sqrt_enclosure 3 1 113511 113512 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep223 := BSN.log_dyadic_bound 1 2 9 8 2258332876800 65536 28312 222698787165 2027025 71998 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1) (BSN.artanhQ 2) 0 8 222698787165 2258332876800 2027025 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep224 := nat_lit 116164158702571594683947827744869038183147962484027262445095338182078401

noncomputable def ep225 := nat_lit 176800594372274305816923439836603481740468153192125564961143897616321

noncomputable def ep226 := nat_lit 348138874918970235440209636354933907585962951145697536205363726751002561

noncomputable def ep227 := BSN.cos_dyadic_bound_f 339574809 268435456 3 2 131072 56680 ep224 ep213 ep225 ep226 ep216 ep225 39457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 339574809) qz305 0 2 ep224 ep213 ep225 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 339574809) qz306 0 2 ep226 ep216 ep225 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz96 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2553553) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz310 := (BSN.isNear_log_sfrac 3 1 71998 65536 1 28312 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 71998 65536 28312 rfl rfl rfl (ep223 rfl)))

noncomputable abbrev qz311 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep228 := @Enclosure.Real.IsNear.cos_image qz93 qz309 Bool.false 2553553 65536 165 131072 Bool.false 39457 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz93 Bool.false 1276776533 32768000 35467 28312000 2553553 65536 165 131072 (@Enclosure.Real.IsNear.mulLit_ff qz36 qz96 35467 1000 0 1 71998 65536 1 28312 1276776533 32768000 35467 28312000 qz91 qz310 rfl) rfl) (Enclosure.sfrac_false_div 2553553 65536) (BSN.cos_reduce0 qz309 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11947726453259261444096) qz311) 226375608064910080 72057594037927936 Bool.false 39457 131072 6 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q0 2553553 65536 226375608064910080 72057594037927936 6 11947726453259261444096 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 39457 131072 11947726453259261444096 9444732965739290427392 339574809 268435456 56680 56624 (ep227 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep229 := nat_lit 208954045189131050986452551188894985944273957948695371949202693609648065

noncomputable def ep230 := nat_lit 546974345961597641802719758020703795645518655712843485142736631238651841

noncomputable def ep231 := BSN.sin_dyadic_bound_f 339574809 268435456 3 2 131072 56680 ep229 ep177 ep225 ep230 ep180 ep225 124991 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 339574809) qz293 0 2 ep229 ep177 ep225 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 339574809) qz294 0 2 ep230 ep180 ep225 rfl rfl rfl rfl) rfl rfl

noncomputable def ep232 := @Enclosure.Real.IsNear.sin_image qz93 qz309 Bool.false 2553553 65536 165 131072 Bool.false 124991 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz93 Bool.false 1276776533 32768000 35467 28312000 2553553 65536 165 131072 (@Enclosure.Real.IsNear.mulLit_ff qz36 qz96 35467 1000 0 1 71998 65536 1 28312 1276776533 32768000 35467 28312000 qz91 qz310 rfl) rfl) (Enclosure.sfrac_false_div 2553553 65536) (BSN.sin_reduce0 qz309 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11947726453259261444096) qz311) 226375608064910080 72057594037927936 Bool.false 124991 131072 6 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q0 2553553 65536 226375608064910080 72057594037927936 6 11947726453259261444096 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 124991 131072 11947726453259261444096 9444732965739290427392 339574809 268435456 56680 56624 (ep231 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz312 := (@Enclosure.Real.IsNear.recentre' qz92 Bool.false 75675 131072 1 131072 75675 131072 1 131072 (ep222 rfl rfl) rfl)

noncomputable def ep233 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz92 (Real.cos qz93)) (@HMul.hMul Real Real Real qz0 qz92 (@Neg.neg Real Real.instNeg (Real.sin qz93))) Bool.false 2985908475 17179869184 45569378967 60799557042176 Bool.true 9458693925 17179869184 45872083793 60799557042176 (@Enclosure.Real.IsNear.mulLit_ff qz92 (Real.cos qz93) 75675 131072 1 131072 39457 131072 600319 463863808 2985908475 17179869184 45569378967 60799557042176 qz312 (@Enclosure.Real.IsNear.recentre' (Real.cos qz93) Bool.false 39457 131072 4802552 3710910464 39457 131072 600319 463863808 (ep228 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz92 (@Neg.neg Real Real.instNeg (Real.sin qz93)) 75675 131072 1 131072 124991 131072 600319 463863808 9458693925 17179869184 45872083793 60799557042176 qz312 (@Enclosure.Real.IsNear.neg (Real.sin qz93) Bool.false 124991 131072 600319 463863808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz93) Bool.false 124991 131072 4802552 3710910464 124991 131072 600319 463863808 (ep232 rfl rfl) rfl)) rfl)

noncomputable def ep234 := @ep200 2985908475 17179869184 45569378967 60799557042176 Bool.true 9458693925 17179869184 45872083793 60799557042176 Bool.false 262240653944029184000 30528830125 17179869184 102328766253 60799557042176 Bool.true 3350060082338463744 3119986581 17179869184 102324137241 60799557042176 (ep201 (BSN.head_sum_c_succ qz11 2 3 rfl rfl) (ep220 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep221 ep233) rfl rfl

noncomputable abbrev qz97 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable abbrev qz98 := (@HMul.hMul Real Real Real qz249 qz259 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep235 := @Enclosure.Complex.IsNear.of_eq qz81 (Complex.mk (@HMul.hMul Real Real Real qz0 qz97 (Real.cos qz98)) (@HMul.hMul Real Real Real qz0 qz97 (@Neg.neg Real Real.instNeg (Real.sin qz98)))) Bool.false 978109875 4294967296 9888446071 15199889260544 Bool.false 3823508505 8589934592 19877728869 30399778521088 (BSN.cpow_neg_s_mk qz36 35467 1000 4 qz37 rfl)

noncomputable abbrev qz99 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable def ep236 := @Enclosure.Real.IsNear.inv_image qz99 262145 131072 1 131072 32767 32768 65536 (@Enclosure.Real.IsNear.of_eq qz99 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4) qz89)) Bool.false 262145 131072 1 131072 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4) qz89)) Bool.false 262145 131072 1 131072 262145 131072 1 131072 (BSN.sqrt_enclosure 4 1 131072 131073 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep237 := nat_lit 753960950911045074462890625

noncomputable def ep238 := nat_lit 117048680082474133384580175

noncomputable def ep239 := BSN.log_dyadic_bound 3 5 12 11 ep237 65536 28312 ep238 431467934736729065175 90852 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 3) (BSN.artanhQ 5) 0 11 ep238 ep237 431467934736729065175 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep240 := nat_lit 259698241755977204340702680617521

noncomputable def ep241 := BSN.sin_dyadic_bound_f 126945483 268435456 2 1 131072 56680 ep240 ep208 ep240 ep240 ep209 ep240 59700 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 126945483) qz293 0 1 ep240 ep208 ep240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 126945483) qz294 0 1 ep240 ep209 ep240 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz100 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6444495) qz12)

noncomputable abbrev qz314 := (BSN.isNear_log_sfrac 4 1 90852 65536 1 28312 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 90852 65536 28312 rfl rfl rfl (ep239 rfl)))

noncomputable def ep242 := @Enclosure.Real.IsNear.cos_image qz98 qz313 Bool.false 6444495 131072 165 131072 Bool.false 59700 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz98 Bool.false 805561971 16384000 35467 28312000 6444495 131072 165 131072 (@Enclosure.Real.IsNear.mulLit_ff qz36 qz100 35467 1000 0 1 90852 65536 1 28312 805561971 16384000 35467 28312000 qz91 qz314 rfl) rfl) (Enclosure.sfrac_false_div 6444495 131072) (BSN.cos_reduce3 qz313 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8932994270112073646080) qz66) 226375608064910080 72057594037927936 Bool.false 59700 131072 7 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q3 6444495 131072 226375608064910080 72057594037927936 7 8932994270112073646080 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 59700 131072 8932994270112073646080 18889465931478580854784 126945483 268435456 56680 56624 (ep241 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep243 := nat_lit 124615124604835863084731911901282304

noncomputable def ep244 := nat_lit 1869226869072537946270978678519234560

noncomputable def ep245 := BSN.cos_dyadic_bound_f 126945483 268435456 2 1 131072 56680 ep240 ep243 ep240 ep240 ep244 ep240 116686 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 126945483) qz305 0 1 ep240 ep243 ep240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 126945483) qz306 0 1 ep240 ep244 ep240 rfl rfl rfl rfl) rfl rfl

noncomputable def ep246 := @Enclosure.Real.IsNear.sin_image qz98 qz313 Bool.false 6444495 131072 165 131072 Bool.true 116686 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz98 Bool.false 805561971 16384000 35467 28312000 6444495 131072 165 131072 (@Enclosure.Real.IsNear.mulLit_ff qz36 qz100 35467 1000 0 1 90852 65536 1 28312 805561971 16384000 35467 28312000 qz91 qz314 rfl) rfl) (Enclosure.sfrac_false_div 6444495 131072) (BSN.sin_reduce3 qz313 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8932994270112073646080) qz66) 226375608064910080 72057594037927936 Bool.false 116686 131072 7 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q3 6444495 131072 226375608064910080 72057594037927936 7 8932994270112073646080 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 116686 131072 8932994270112073646080 18889465931478580854784 126945483 268435456 56680 56624 (ep245 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz315 := (@Enclosure.Real.IsNear.recentre' qz97 Bool.false 65535 131072 1 131072 65535 131072 1 131072 (ep236 rfl rfl) rfl)

noncomputable def ep247 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz97 (Real.cos qz98)) (@HMul.hMul Real Real Real qz0 qz97 (@Neg.neg Real Real.instNeg (Real.sin qz98))) Bool.false 978109875 4294967296 9888446071 15199889260544 Bool.false 3823508505 8589934592 19877728869 30399778521088 (@Enclosure.Real.IsNear.mulLit_ff qz97 (Real.cos qz98) 65535 131072 1 131072 14925 32768 600319 463863808 978109875 4294967296 9888446071 15199889260544 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz98) Bool.false 59700 131072 4802552 3710910464 14925 32768 600319 463863808 (ep242 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz97 (@Neg.neg Real Real.instNeg (Real.sin qz98)) 65535 131072 1 131072 58343 65536 600319 463863808 3823508505 8589934592 19877728869 30399778521088 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz98) Bool.true 58343 65536 600319 463863808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz98) Bool.true 116686 131072 4802552 3710910464 58343 65536 600319 463863808 (ep246 rfl rfl) rfl)) rfl)

noncomputable def ep248 := @ep198 978109875 4294967296 9888446071 15199889260544 Bool.false 3823508505 8589934592 19877728869 30399778521088 Bool.false 147924126672093184000 34441269625 17179869184 141882550537 60799557042176 Bool.false 38886895281103699968 4527030429 17179869184 142079594979 60799557042176 (ep199 (BSN.head_sum_c_succ qz11 3 4 rfl rfl) (ep234 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep235 ep247) rfl rfl

noncomputable abbrev qz101 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable abbrev qz102 := (@HMul.hMul Real Real Real qz249 qz259 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep249 := @Enclosure.Complex.IsNear.of_eq qz79 (Complex.mk (@HMul.hMul Real Real Real qz0 qz101 (Real.cos qz102)) (@HMul.hMul Real Real Real qz0 qz101 (@Neg.neg Real Real.instNeg (Real.sin qz102)))) Bool.false 6616511109 17179869184 35588970845 60799557042176 Bool.true 1952590887 8589934592 1107039825 1899986157568 (BSN.cpow_neg_s_mk qz36 35467 1000 5 qz37 rfl)

noncomputable abbrev qz103 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def ep250 := @Enclosure.Real.IsNear.inv_image qz103 293085 131072 1 131072 29308 29309 65536 (@Enclosure.Real.IsNear.of_eq qz103 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5) qz89)) Bool.false 293085 131072 1 131072 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5) qz89)) Bool.false 293085 131072 1 131072 293085 131072 1 131072 (BSN.sqrt_enclosure 5 1 146542 146543 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep251 := nat_lit 141613827518379161815574079375

noncomputable def ep252 := nat_lit 29325128709309236875766211300

noncomputable def ep253 := BSN.log_dyadic_bound 2 3 15 14 ep251 65536 28312 ep252 57299708096576225280000 105476 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP 2) (BSN.artanhQ 3) 0 14 ep252 ep251 57299708096576225280000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep254 := nat_lit 419668007603866924901603556512016

noncomputable def ep255 := BSN.cos_dyadic_bound_f 143128614 268435456 2 1 131072 56680 ep254 ep243 ep254 ep254 ep244 ep254 112877 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 143128614) qz305 0 1 ep254 ep243 ep254 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 143128614) qz306 0 1 ep254 ep244 ep254 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz104 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz316 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3740917) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz317 := (BSN.isNear_log_sfrac 5 1 105476 65536 1 28312 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 105476 65536 28312 rfl rfl rfl (ep253 rfl)))

noncomputable def ep256 := @Enclosure.Real.IsNear.cos_image qz102 qz316 Bool.false 3740917 65536 165 131072 Bool.false 112877 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz102 Bool.false 935229323 16384000 35467 28312000 3740917 65536 165 131072 (@Enclosure.Real.IsNear.mulLit_ff qz36 qz104 35467 1000 0 1 105476 65536 1 28312 935229323 16384000 35467 28312000 qz91 qz317 rfl) rfl) (Enclosure.sfrac_false_div 3740917 65536) (BSN.cos_reduce0 qz316 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5035890426056429010944) qz311) 226375608064910080 72057594037927936 Bool.false 112877 131072 9 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q0 3740917 65536 226375608064910080 72057594037927936 9 5035890426056429010944 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 112877 131072 5035890426056429010944 9444732965739290427392 143128614 268435456 56680 56624 (ep255 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep257 := BSN.sin_dyadic_bound_f 143128614 268435456 2 1 131072 56680 ep254 ep208 ep254 ep254 ep209 ep254 66622 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 143128614) qz293 0 1 ep254 ep208 ep254 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 143128614) qz294 0 1 ep254 ep209 ep254 rfl rfl rfl rfl) rfl rfl

noncomputable def ep258 := @Enclosure.Real.IsNear.sin_image qz102 qz316 Bool.false 3740917 65536 165 131072 Bool.false 66622 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz102 Bool.false 935229323 16384000 35467 28312000 3740917 65536 165 131072 (@Enclosure.Real.IsNear.mulLit_ff qz36 qz104 35467 1000 0 1 105476 65536 1 28312 935229323 16384000 35467 28312000 qz91 qz317 rfl) rfl) (Enclosure.sfrac_false_div 3740917 65536) (BSN.sin_reduce0 qz316 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5035890426056429010944) qz311) 226375608064910080 72057594037927936 Bool.false 66622 131072 9 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q0 3740917 65536 226375608064910080 72057594037927936 9 5035890426056429010944 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 66622 131072 5035890426056429010944 9444732965739290427392 143128614 268435456 56680 56624 (ep257 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz318 := (@Enclosure.Real.IsNear.recentre' qz101 Bool.false 58617 131072 1 131072 58617 131072 1 131072 (ep250 rfl rfl) rfl)

noncomputable def ep259 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz101 (Real.cos qz102)) (@HMul.hMul Real Real Real qz0 qz101 (@Neg.neg Real Real.instNeg (Real.sin qz102))) Bool.false 6616511109 17179869184 35588970845 60799557042176 Bool.true 1952590887 8589934592 1107039825 1899986157568 (@Enclosure.Real.IsNear.mulLit_ff qz101 (Real.cos qz102) 58617 131072 1 131072 112877 131072 600319 463863808 6616511109 17179869184 35588970845 60799557042176 qz318 (@Enclosure.Real.IsNear.recentre' (Real.cos qz102) Bool.false 112877 131072 4802552 3710910464 112877 131072 600319 463863808 (ep256 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz101 (@Neg.neg Real Real.instNeg (Real.sin qz102)) 58617 131072 1 131072 33311 65536 600319 463863808 1952590887 8589934592 1107039825 1899986157568 qz318 (@Enclosure.Real.IsNear.neg (Real.sin qz102) Bool.false 33311 65536 600319 463863808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz102) Bool.false 66622 131072 4802552 3710910464 33311 65536 600319 463863808 (ep258 rfl rfl) rfl)) rfl)

noncomputable def ep260 := @ep196 6616511109 17179869184 35588970845 60799557042176 Bool.true 1952590887 8589934592 1107039825 1899986157568 Bool.false 705367301995475501056 20528890367 8589934592 88735760691 30399778521088 Bool.false 5341639272573173760 621848655 17179869184 177504869379 60799557042176 (ep197 (BSN.head_sum_c_succ qz11 4 5 rfl rfl) (ep248 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep249 ep259) rfl rfl

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz105 := (@Inv.inv Real Real.instInv (Real.sqrt qz319))

noncomputable abbrev qz106 := (@HMul.hMul Real Real Real qz249 qz259 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep261 := @Enclosure.Complex.IsNear.of_eq qz77 (Complex.mk (@HMul.hMul Real Real Real qz0 qz105 (Real.cos qz106)) (@HMul.hMul Real Real Real qz0 qz105 (@Neg.neg Real Real.instNeg (Real.sin qz106)))) Bool.false 1322633425 4294967296 8206018047 15199889260544 Bool.true 2302240995 8589934592 16366662575 30399778521088 (BSN.cpow_neg_s_mk qz36 35467 1000 6 qz37 rfl)

noncomputable abbrev qz107 := (Real.sqrt qz319)

noncomputable abbrev qz320 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz89)

noncomputable def ep262 := @Enclosure.Real.IsNear.inv_image qz107 321059 131072 1 131072 26754 26756 65536 (@Enclosure.Real.IsNear.of_eq qz107 (Real.sqrt qz320) Bool.false 321059 131072 1 131072 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz320) Bool.false 321059 131072 1 131072 321059 131072 1 131072 (BSN.sqrt_enclosure 6 1 160529 160530 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep263 := BSN.log_dyadic_bound 2 10 4 3 105000000 65536 28312 1434560 960 26572 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz108 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep264 := @Enclosure.Real.IsNear.mulLit_ff qz36 qz108 35467 1000 0 1 4034664351997175 2251799813685248 62500000003539 1769500000000000000 5723897622891352229 90071992547409920 2216687500125517713 1769500000000000000000 qz91 (BSN.isNear_log_sfrac 6 1 4034664351997175 2251799813685248 62500000003539 1769500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz320) Bool.false 4230652207559789772800 2361183241434822606848 1000000000056624 28312000000000000000 4034664351997175 2251799813685248 62500000003539 1769500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 26572 65536 24973259072661432 36028797018963968 28312 1000000000000000 rfl rfl rfl rfl (ep263 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep265 := nat_lit 1365946318401232495256418709800625

noncomputable def ep266 := BSN.cos_dyadic_bound_f 192246485 268435456 2 1 131072 56680 ep265 ep243 ep265 ep265 ep244 ep265 98870 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 192246485) qz305 0 1 ep265 ep243 ep265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 192246485) qz306 0 1 ep265 ep244 ep265 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz321 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8329367) qz12)

noncomputable def ep267 := @Enclosure.Real.IsNear.cos_image qz106 qz321 Bool.false 8329367 131072 165 131072 Bool.false 98870 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 5723897622891352229 90071992547409920 2216687500125517713 1769500000000000000000 8329367 131072 165 131072 (ep264 rfl) rfl) (Enclosure.sfrac_false_div 8329367 131072) (BSN.cos_reduce0 qz321 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13528143746471636762624) qz66) 226375608064910080 72057594037927936 Bool.false 98870 131072 10 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q0 8329367 131072 226375608064910080 72057594037927936 10 13528143746471636762624 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 98870 131072 13528143746471636762624 18889465931478580854784 192246485 268435456 56680 56624 (ep266 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep268 := BSN.sin_dyadic_bound_f 192246485 268435456 2 1 131072 56680 ep265 ep208 ep265 ep265 ep209 ep265 86049 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 192246485) qz293 0 1 ep265 ep208 ep265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 192246485) qz294 0 1 ep265 ep209 ep265 rfl rfl rfl rfl) rfl rfl

noncomputable def ep269 := @Enclosure.Real.IsNear.sin_image qz106 qz321 Bool.false 8329367 131072 165 131072 Bool.false 86049 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 5723897622891352229 90071992547409920 2216687500125517713 1769500000000000000000 8329367 131072 165 131072 (ep264 rfl) rfl) (Enclosure.sfrac_false_div 8329367 131072) (BSN.sin_reduce0 qz321 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13528143746471636762624) qz66) 226375608064910080 72057594037927936 Bool.false 86049 131072 10 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q0 8329367 131072 226375608064910080 72057594037927936 10 13528143746471636762624 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 86049 131072 13528143746471636762624 18889465931478580854784 192246485 268435456 56680 56624 (ep268 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz322 := (@Enclosure.Real.IsNear.recentre' qz105 Bool.false 53510 131072 2 131072 26755 65536 1 65536 (ep262 rfl rfl) rfl)

noncomputable def ep270 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz105 (Real.cos qz106)) (@HMul.hMul Real Real Real qz0 qz105 (@Neg.neg Real Real.instNeg (Real.sin qz106))) Bool.false 1322633425 4294967296 8206018047 15199889260544 Bool.true 2302240995 8589934592 16366662575 30399778521088 (@Enclosure.Real.IsNear.mulLit_ff qz105 (Real.cos qz106) 26755 65536 1 65536 49435 65536 600319 463863808 1322633425 4294967296 8206018047 15199889260544 qz322 (@Enclosure.Real.IsNear.recentre' (Real.cos qz106) Bool.false 98870 131072 4802552 3710910464 49435 65536 600319 463863808 (ep267 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz105 (@Neg.neg Real Real.instNeg (Real.sin qz106)) 26755 65536 1 65536 86049 131072 600319 463863808 2302240995 8589934592 16366662575 30399778521088 qz322 (@Enclosure.Real.IsNear.neg (Real.sin qz106) Bool.false 86049 131072 600319 463863808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz106) Bool.false 86049 131072 4802552 3710910464 86049 131072 600319 463863808 (ep269 rfl rfl) rfl)) rfl)

noncomputable def ep271 := @ep194 1322633425 4294967296 8206018047 15199889260544 Bool.true 2302240995 8589934592 16366662575 30399778521088 Bool.false 99532247359377375232 23174157217 8589934592 105147796785 30399778521088 Bool.true 34210559851568824320 3982633335 17179869184 210238194529 60799557042176 (ep195 (BSN.head_sum_c_succ qz11 5 6 rfl rfl) (ep260 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep261 ep270) rfl rfl

noncomputable abbrev qz323 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz109 := (@Inv.inv Real Real.instInv (Real.sqrt qz323))

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz249 qz259 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep272 := @Enclosure.Complex.IsNear.of_eq qz75 (Complex.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz110)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110)))) Bool.false 6460988597 17179869184 30202549661 60799557042176 Bool.false 324047681 8589934592 3723412637 7599944630272 (BSN.cpow_neg_s_mk qz36 35467 1000 7 qz37 rfl)

noncomputable abbrev qz111 := (Real.sqrt qz323)

noncomputable abbrev qz324 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) qz89)

noncomputable def ep273 := @Enclosure.Real.IsNear.inv_image qz111 346783 131072 1 131072 24770 24771 65536 (@Enclosure.Real.IsNear.of_eq qz111 (Real.sqrt qz324) Bool.false 346783 131072 1 131072 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz324) Bool.false 346783 131072 1 131072 346783 131072 1 131072 (BSN.sqrt_enclosure 7 1 173391 173392 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep274 := BSN.log_dyadic_bound 3 11 5 4 202569142545 65536 28312 5259111624 688905 36674 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz112 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep275 := @Enclosure.Real.IsNear.mulLit_ff qz36 qz112 35467 1000 0 1 4381766428990711 2251799813685248 62500000003539 1769500000000000000 155408109937013547037 2251799813685248000 2216687500125517713 1769500000000000000000 qz91 (BSN.isNear_log_sfrac 7 1 4381766428990711 2251799813685248 62500000003539 1769500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz324) Bool.false 4594615115045363777536 2361183241434822606848 1000000000056624 28312000000000000000 4381766428990711 2251799813685248 62500000003539 1769500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 36674 65536 24973259072661432 36028797018963968 28312 1000000000000000 rfl rfl rfl rfl (ep274 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep276 := nat_lit 382127757611640206778983580392772926490351149635639196215207526400000000

noncomputable def ep277 := nat_lit 590461238897247749036501370706178418148525544671234560000000000000000

noncomputable def ep278 := nat_lit 999854808881795473779850279761833375750107779116253991276019712000000000

noncomputable def ep279 := BSN.sin_dyadic_bound_f 394819800 268435456 3 2 131072 56680 ep276 ep177 ep277 ep278 ep180 ep277 130417 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 394819800) qz293 0 2 ep276 ep177 ep277 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 394819800) qz294 0 2 ep278 ep180 ep277 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz325 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4522971) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep280 := @Enclosure.Real.IsNear.cos_image qz110 qz325 Bool.false 4522971 65536 165 131072 Bool.false 130417 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz110 Bool.false 155408109937013547037 2251799813685248000 2216687500125517713 1769500000000000000000 4522971 65536 165 131072 (ep275 rfl) rfl) (Enclosure.sfrac_false_div 4522971 65536) (BSN.cos_reduce3 qz325 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13891486770538188111872) qz311) 226375608064910080 72057594037927936 Bool.false 130417 131072 10 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q3 4522971 65536 226375608064910080 72057594037927936 10 13891486770538188111872 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 130417 131072 13891486770538188111872 9444732965739290427392 394819800 268435456 56680 56624 (ep279 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep281 := nat_lit 212555625890421113876784878605187705124927761150764546590670848000000000

noncomputable def ep282 := nat_lit 636485955193468846132281633074150758538486232362951170652012544000000000

noncomputable def ep283 := BSN.cos_dyadic_bound_f 394819800 268435456 3 2 131072 56680 ep281 ep213 ep277 ep282 ep216 ep277 13082 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 394819800) qz305 0 2 ep281 ep213 ep277 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 394819800) qz306 0 2 ep282 ep216 ep277 rfl rfl rfl rfl) rfl rfl

noncomputable def ep284 := @Enclosure.Real.IsNear.sin_image qz110 qz325 Bool.false 4522971 65536 165 131072 Bool.true 13082 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz110 Bool.false 155408109937013547037 2251799813685248000 2216687500125517713 1769500000000000000000 4522971 65536 165 131072 (ep275 rfl) rfl) (Enclosure.sfrac_false_div 4522971 65536) (BSN.sin_reduce3 qz325 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13891486770538188111872) qz311) 226375608064910080 72057594037927936 Bool.false 13082 131072 10 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q3 4522971 65536 226375608064910080 72057594037927936 10 13891486770538188111872 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 13082 131072 13891486770538188111872 9444732965739290427392 394819800 268435456 56680 56624 (ep283 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz326 := (@Enclosure.Real.IsNear.recentre' qz109 Bool.false 49541 131072 1 131072 49541 131072 1 131072 (ep273 rfl rfl) rfl)

noncomputable def ep285 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz110)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110))) Bool.false 6460988597 17179869184 30202549661 60799557042176 Bool.false 324047681 8589934592 3723412637 7599944630272 (@Enclosure.Real.IsNear.mulLit_ff qz109 (Real.cos qz110) 49541 131072 1 131072 130417 131072 600319 463863808 6460988597 17179869184 30202549661 60799557042176 qz326 (@Enclosure.Real.IsNear.recentre' (Real.cos qz110) Bool.false 130417 131072 4802552 3710910464 130417 131072 600319 463863808 (ep280 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110)) 49541 131072 1 131072 6541 65536 600319 463863808 324047681 8589934592 3723412637 7599944630272 qz326 (@Enclosure.Real.IsNear.neg (Real.sin qz110) Bool.true 6541 65536 600319 463863808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz110) Bool.true 13082 131072 4802552 3710910464 6541 65536 600319 463863808 (ep284 rfl rfl) rfl)) rfl)

noncomputable def ep286 := @ep192 6460988597 17179869184 30202549661 60799557042176 Bool.false 324047681 8589934592 3723412637 7599944630272 Bool.false 453628458885397348352 52809303031 17179869184 240498143231 60799557042176 Bool.true 28643463082610262016 3334537973 17179869184 240025495625 60799557042176 (ep193 (BSN.head_sum_c_succ qz11 6 7 rfl rfl) (ep271 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep272 ep285) rfl rfl

noncomputable def ep287 := @Enclosure.Complex.IsNear.mul qz69 (@HAdd.hAdd Complex Complex Complex qz8 qz70 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.true 22200945036969500680617 345839862108982870016000 45431636252159624783059 ep53 Bool.false

noncomputable abbrev qz113 := (Complex.re qz297)

noncomputable abbrev qz114 := (Complex.im qz297)

noncomputable def ep288 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz113 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz70 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz114 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz70 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 18611326902754573185 1383359448435931480064 3378086085929287600879

noncomputable def ep289 := nat_lit 14687127264044284523839488

noncomputable def ep290 := nat_lit 1835890908005535565479936000

noncomputable def ep291 := nat_lit 30711887081098558883159587048344424166719488

noncomputable def ep292 := @Enclosure.Real.IsNear.mulLit_tf qz113 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz70 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 460397835 17179869184 27855143063 60799557042176 121273334633

noncomputable abbrev qz115 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable abbrev qz327 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz397 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable abbrev qz116 := (Real.cos qz327)

noncomputable abbrev qz117 := (@Neg.neg Real Real.instNeg (Real.sin qz327))

noncomputable def ep293 := @Enclosure.Complex.IsNear.of_eq qz69 (Complex.mk (@HMul.hMul Real Real Real qz0 qz115 qz116) (@HMul.hMul Real Real Real qz0 qz115 qz117)) Bool.true 460397835 17179869184 27855143063 60799557042176 Bool.false 3028245327 8589934592 7070627291 15199889260544 (BSN.cpow_neg_s_mk qz36 35467 1000 8 qz37 rfl)

noncomputable abbrev qz118 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable abbrev qz119 := (@HDiv.hDiv Real Real Real qz252 (@Nat.cast Real Real.instNatCast 8) (@Nat.cast Real Real.instNatCast 1))

noncomputable def ep294 := @Enclosure.Real.IsNear.inv_image qz118 370727 131072 1 131072 23170 23171 65536 (@Enclosure.Real.IsNear.of_eq qz118 (Real.sqrt qz119) Bool.false 370727 131072 1 131072 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz119) Bool.false 370727 131072 1 131072 370727 131072 1 131072 (BSN.sqrt_enclosure 8 1 185363 185364 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep295 := BSN.log_dyadic_bound 0 16 1 0 1 65536 28312 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz328 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz120 := qz328

noncomputable def ep296 := @Enclosure.Real.IsNear.mulLit_ff qz36 qz120 35467 1000 0 1 9364972152248037 4503599627370496 125000000010617 3539000000000000000 332147467323781128279 4503599627370496000 4433375000376553139 3539000000000000000000 qz91 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 125000000010617 3539000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz119) Bool.false 4909942519757818822656 2361183241434822606848 1000000000084936 28312000000000000000 9364972152248037 4503599627370496 125000000010617 3539000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 65536 24973259072661432 36028797018963968 28312 1000000000000000 rfl rfl rfl rfl (ep295 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep297 := nat_lit 226874989141921812577451233225754553754707903070390622311579425122024161

noncomputable def ep298 := nat_lit 672445938175843324831468241607825866519848022408665989511581235411681

noncomputable def ep299 := nat_lit 679280075549413751082690763194048009531084013166354534955715112895249121

noncomputable def ep300 := BSN.cos_dyadic_bound_f 401288923 268435456 3 2 131072 56680 ep297 ep213 ep298 ep299 ep216 ep298 9935 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 401288923) qz305 0 2 ep297 ep213 ep298 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 401288923) qz306 0 2 ep299 ep216 ep298 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz121 := qz327

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9666763) qz12)

noncomputable def ep301 := @Enclosure.Real.IsNear.cos_image qz121 qz329 Bool.false 9666763 131072 165 131072 Bool.true 9935 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 332147467323781128279 4503599627370496000 4433375000376553139 3539000000000000000000 9666763 131072 165 131072 (ep296 rfl) rfl) (Enclosure.sfrac_false_div 9666763 131072) (BSN.cos_reduce2 qz329 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28238197616665612517376) qz66) 226375608064910080 72057594037927936 Bool.false 9935 131072 11 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q2 9666763 131072 226375608064910080 72057594037927936 11 28238197616665612517376 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 9935 131072 28238197616665612517376 18889465931478580854784 401288923 268435456 56680 56624 (ep300 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep302 := nat_lit 407837023704918587979547045213071936065258347108776187369233700231314145

noncomputable def ep303 := nat_lit 1067055863898692555515753217452585257339406393248609317222117130986584801

noncomputable def ep304 := BSN.sin_dyadic_bound_f 401288923 268435456 3 2 131072 56680 ep302 ep177 ep298 ep303 ep180 ep298 130694 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 401288923) qz293 0 2 ep302 ep177 ep298 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 401288923) qz294 0 2 ep303 ep180 ep298 rfl rfl rfl rfl) rfl rfl

noncomputable def ep305 := @Enclosure.Real.IsNear.sin_image qz121 qz329 Bool.false 9666763 131072 165 131072 Bool.true 130694 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 332147467323781128279 4503599627370496000 4433375000376553139 3539000000000000000000 9666763 131072 165 131072 (ep296 rfl) rfl) (Enclosure.sfrac_false_div 9666763 131072) (BSN.sin_reduce2 qz329 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28238197616665612517376) qz66) 226375608064910080 72057594037927936 Bool.false 130694 131072 11 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q2 9666763 131072 226375608064910080 72057594037927936 11 28238197616665612517376 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 130694 131072 28238197616665612517376 18889465931478580854784 401288923 268435456 56680 56624 (ep304 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz122 := (Real.sin qz327)

noncomputable abbrev qz330 := (@Enclosure.Real.IsNear.recentre' qz115 Bool.false 46341 131072 1 131072 46341 131072 1 131072 (ep294 rfl rfl) rfl)

noncomputable def ep306 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz115 qz116) (@HMul.hMul Real Real Real qz0 qz115 qz117) Bool.true 460397835 17179869184 27855143063 60799557042176 Bool.false 3028245327 8589934592 7070627291 15199889260544 (@Enclosure.Real.IsNear.mulLit_ft qz115 qz116 46341 131072 1 131072 9935 131072 600319 463863808 460397835 17179869184 27855143063 60799557042176 qz330 (@Enclosure.Real.IsNear.recentre' qz116 Bool.true 9935 131072 4802552 3710910464 9935 131072 600319 463863808 (ep301 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz115 qz117 46341 131072 1 131072 65347 65536 600319 463863808 3028245327 8589934592 7070627291 15199889260544 qz330 (@Enclosure.Real.IsNear.neg qz122 Bool.true 65347 65536 600319 463863808 (@Enclosure.Real.IsNear.recentre' qz122 Bool.true 130694 131072 4802552 3710910464 65347 65536 600319 463863808 (ep305 rfl rfl) rfl)) rfl)

noncomputable def ep307 := @ep292 241566353088 0 1 18611326902754573185 1383359448435931480064 3378086085929287600879 ep289 (@Enclosure.Complex.IsNear.re_isNear qz69 Bool.true 460397835 17179869184 27855143063 60799557042176 Bool.false 3028245327 8589934592 7070627291 15199889260544 (ep293 ep306))

noncomputable def ep308 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz70 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 121273334633 241566353088 0 1 Bool.false

noncomputable def ep309 := @Enclosure.Complex.IsNear.addLitP qz70 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) Bool.false 1250158089 2516316178 0 1 Bool.true 283736000

noncomputable def ep310 := @ep309 1258158089 0 1 Bool.false 1 192 0 1 Bool.false 35467 96000 0 1 Bool.false 242546669266 121273334633 241566353088 0 1 Bool.false 17384436942563 17384436942563 120783176544000 0 1

noncomputable abbrev qz123 := (@HDiv.hDiv Complex Complex Complex qz265 qz298 (@HSub.hSub Complex Complex Complex qz255 qz260 (1 : Complex)))

noncomputable def ep311 := @Enclosure.Complex.IsNear.addLitP qz123 qz40 Bool.true 16000000 5032632356 0 1 Bool.true 1134944000 5032632356 0 1

noncomputable def ep312 := @Enclosure.Complex.IsNear.of_eq qz123 (Complex.mk (Enclosure.sfrac Bool.true 16000000 5032632356) (Enclosure.sfrac Bool.true 1134944000 5032632356)) Bool.true 16000000 5032632356 0 1 Bool.true 1134944000 5032632356 0 1

noncomputable def ep313 := @ep311 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 5000632356 1250158089 2516316178 0 1 Bool.true 1134944000 283736000 1258158089 0 1 (ep312 (BSN.N_div_s_sub_one_mk qz36 35467 1000 8 qz37 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 16000000 5032632356) (Enclosure.sfrac Bool.true 1134944000 5032632356) Bool.true 16000000 5032632356 0 1 Bool.true 1134944000 5032632356 0 1 (Enclosure.Real.IsNear.const Bool.true 16000000 5032632356) (Enclosure.Real.IsNear.const Bool.true 1134944000 5032632356))) qz42 rfl

noncomputable abbrev qz124 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz331 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz402 qz405 1))

noncomputable abbrev qz125 := qz331

noncomputable def ep314 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz125)) Bool.false 1 192 0 1

noncomputable def ep315 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz125) Bool.false 0 1 0 1 Bool.false

noncomputable def ep316 := @ep315 0 1 0 1 Bool.false 1 192 0 1 Bool.false 35467 96000 0 1 Bool.false 1 1 192 0 1 Bool.false 35467 35467 96000 0

noncomputable def ep317 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (Complex.mk qz43 qz43) Bool.false 0 1 0 1 Bool.false

noncomputable def ep318 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz125 Bool.false 1 192 0 1 Bool.false 35467 96000 0 1

noncomputable abbrev qz126 := (Complex.re qz331)

noncomputable abbrev qz127 := (Complex.im qz331)

noncomputable def ep319 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127) 1 192 0 1 0 1 0

noncomputable def ep320 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126 1 24 0 1 1 8 0 1 1

noncomputable def ep321 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep322 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep323 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz43) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow06.d6 rfl) qz284

noncomputable def ep324 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz11 Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 (BSN.ascPochhammer_one_eval qz11)

noncomputable def ep325 := ep324 (@Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk qz32 qz36) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 (BSN.s_crit_mk qz36 Bool.false 35467 1000 qz37) (@Enclosure.Complex.IsNear.mk qz32 qz36 Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 qz33 qz91))

noncomputable def ep326 := @ep322 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep325)

noncomputable def ep327 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 35467 1000 0 1 0 1 0

noncomputable def ep328 := @ep327 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep325)

noncomputable def ep329 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) 35467 12000 0 1 0 1 0 1 35467

noncomputable def ep330 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 35467 1000 0 1 35467 12000 0

noncomputable def ep331 := @ep330 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep325)

noncomputable def ep332 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep333 := @ep332 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep325)

noncomputable def ep334 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 35467 12000 0 1 (@ep321 1 24 0 1 (ep326 rfl) (ep328 rfl) rfl rfl) (@ep329 35467 12000 0 1 (ep331 rfl) (ep333 rfl) rfl rfl)

noncomputable def ep335 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 35467 12000 0 1 ep334

noncomputable abbrev qz128 := (@Enclosure.Complex.IsNear.re_isNear qz331 Bool.false 1 8 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz331 (Complex.mk (Enclosure.sfrac Bool.false 1 8) qz280) Bool.false 1 8 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 8 1 8 EMRow06.d7 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 8) qz280 Bool.false 1 8 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 8) qz281)))

noncomputable def ep336 := @ep320 192 0 1 ep335 qz128

noncomputable def ep337 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127 35467 12000 0 1 0 1 0 1 0

noncomputable def ep338 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 35467 12000 0 1 ep334

noncomputable abbrev qz129 := (@Enclosure.Complex.IsNear.im_isNear qz331 Bool.false 1 8 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz331 (Complex.mk (Enclosure.sfrac Bool.false 1 8) qz280) Bool.false 1 8 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 8 1 8 EMRow06.d7 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 8) qz280 Bool.false 1 8 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 8) qz281)))

noncomputable def ep339 := @ep337 1 0 1 ep338 qz129

noncomputable def ep340 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126) 0 1 0 1 35467 96000 0

noncomputable def ep341 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127 1 24 0 1 0 1 0 1 0

noncomputable def ep342 := @ep341 1 0 1 ep335 qz129

noncomputable def ep343 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126 35467 12000 0 1 1 8 0 1 35467

noncomputable def ep344 := @ep343 96000 0 1 ep338 qz128

noncomputable def ep345 := @ep316 1 (@ep317 0 1 0 1 (BSN.bern_sum_base qz11 8) qz60) (ep318 (@ep319 1 1 1 192 0 1 (ep336 rfl) (ep339 rfl) rfl rfl) (@ep340 1 35467 35467 96000 0 1 (ep342 rfl) (ep344 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep346 := ep310 (ep313 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep314 Bool.false 35467 96000 0 1 (BSN.bern_sum_succ qz11 8 0 1 1 rfl rfl) (ep345 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep347 := @Enclosure.Real.IsNear.mulLit_ff qz114 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz70 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 3028245327 8589934592 7070627291 15199889260544 17384436942563

noncomputable def ep348 := @ep347 120783176544000 0 1 17548113311280857384367 345839862108982870016000 122918874284754547286833 ep290 (@Enclosure.Complex.IsNear.im_isNear qz69 Bool.true 460397835 17179869184 27855143063 60799557042176 Bool.false 3028245327 8589934592 7070627291 15199889260544 (ep293 ep306))

noncomputable def ep349 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz70 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 121273334633 241566353088 0 1 Bool.false

noncomputable def ep350 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz113 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz70 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz114 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz70 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 533583808736668303407 138335944843593148006400 484245978104794678890469

noncomputable def ep351 := nat_lit 7343563632022142261919744000

noncomputable def ep352 := nat_lit 3671781816011071130959872

noncomputable def ep353 := nat_lit 16565344441178818514572106643897280182091776

noncomputable def ep354 := @Enclosure.Real.IsNear.mulLit_tf qz113 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz70 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 460397835 17179869184 27855143063 60799557042176 17384436942563

noncomputable def ep355 := @ep354 120783176544000 0 1 533583808736668303407 138335944843593148006400 484245978104794678890469 ep351 (@Enclosure.Complex.IsNear.re_isNear qz69 Bool.true 460397835 17179869184 27855143063 60799557042176 Bool.false 3028245327 8589934592 7070627291 15199889260544 (ep293 ep306))

noncomputable def ep356 := @Enclosure.Real.IsNear.mulLit_ff qz114 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz70 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 3028245327 8589934592 7070627291 15199889260544 121273334633

noncomputable def ep357 := @ep356 241566353088 0 1 122415136297363169997 691679724217965740032 857478549526665269203 ep352 (@Enclosure.Complex.IsNear.im_isNear qz69 Bool.true 460397835 17179869184 27855143063 60799557042176 Bool.false 3028245327 8589934592 7070627291 15199889260544 (ep293 ep306))

noncomputable abbrev qz332 := (ep346 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep358 := @ep287 23949443450735965695993 138335944843593148006400 733067692386041739098823 ep184 (@ep288 ep289 17548113311280857384367 345839862108982870016000 122918874284754547286833 ep290 ep291 22200945036969500680617 345839862108982870016000 45431636252159624783059 ep53 (ep307 (@ep308 17384436942563 120783176544000 0 1 qz332) rfl) (ep348 (@ep349 17384436942563 120783176544000 0 1 qz332) rfl) rfl rfl) (@ep350 ep351 122415136297363169997 691679724217965740032 857478549526665269203 ep352 ep353 23949443450735965695993 138335944843593148006400 733067692386041739098823 ep184 (ep355 (@ep349 17384436942563 120783176544000 0 1 qz332) rfl) (ep357 (@ep308 17384436942563 120783176544000 0 1 qz332) rfl) rfl rfl)

noncomputable def ep359 := @ep189 ep183 ep184 (@ep190 60799557042176 (BSN.head_sum_c_eq qz11 8) (ep191 (BSN.head_sum_c_succ qz11 7 8 rfl rfl) (ep286 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep358 rfl rfl rfl

noncomputable def ep360 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz11 1 8) Bool.false 1040878283489508383463383 345839862108982870016000 650601004843286115901059 ep53 Bool.true 2900962461632761324807 138335944843593148006400 ep183 ep184 (@ep185 ep53 Bool.true 2900962461632761324807 138335944843593148006400 ep183 ep184 (BSN.zetaApproximant_eq_folded' qz11 1 8 rfl) (ep359 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep361 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 8)) 5 32768 373823

noncomputable def ep362 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) Bool.true 20 131072 2990584

noncomputable def ep363 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) qz261 Bool.false 1647079 131072 101

noncomputable def ep364 := nat_lit 276634687633597653630350868591659362022121693900801616604393764292772096

noncomputable def ep365 := nat_lit 827907123125710899699895979612695266840841475399264397364418624893337856

noncomputable def ep366 := BSN.cos_dyadic_bound_f 421615794 268435456 3 2 131072 56680 ep364 ep213 ep178 ep365 ep216 ep178 20 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 421615794) qz305 0 2 ep364 ep213 ep178 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 421615794) qz306 0 2 ep365 ep216 ep178 rfl rfl rfl rfl) rfl rfl

noncomputable def ep367 := @ep363 131072 Bool.true 20 131072 1 28312 (@ep57 1647079 131072 101 131072 ep175 rfl) (Enclosure.sfrac_false_div 1647079 131072) (BSN.sin_reduce3 qz261 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29668573958805355757568) qz66) 226375608064910080 72057594037927936 Bool.false 20 131072 1 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q3 1647079 131072 226375608064910080 72057594037927936 1 29668573958805355757568 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 20 131072 29668573958805355757568 18889465931478580854784 421615794 268435456 56680 56624 (ep366 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep368 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz11 1 8) Bool.false 1040878283489508383463383 345839862108982870016000 650601004843286115901059 ep53 Bool.true 2900962461632761324807 138335944843593148006400 ep183 ep184 (@ep185 ep53 Bool.true 2900962461632761324807 138335944843593148006400 ep183 ep184 (BSN.zetaApproximant_eq_folded' qz11 1 8 rfl) (ep359 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow06.d8 : Enclosure.Real.IsNear (hardyZApproximantEM 1 8 qz36) Bool.false ep38 ep39 ep40 ep41 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 8 qz36) ep42 Bool.false ep38 ep39 ep40 ep41 (@Eq.refl Real ep42) (@ep43 Bool.false ep38 ep39 ep40 ep41 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) (zetaApproximant qz11 1 8)) (@ep45 ep39 ep46 ep47 2900962461632761324807 ep48 ep49 ep50 ep51 ep38 ep39 ep40 ep41 (@ep52 463863808 1040878283489508383463383 345839862108982870016000 650601004843286115901059 ep53 ep44 ep39 ep46 ep47 (@ep54 3710910464 131071 131072 373823 463863808 (ep182 rfl rfl) rfl) ep360 rfl) (@ep361 463863808 2900962461632761324807 138335944843593148006400 ep183 ep184 2900962461632761324807 ep48 ep49 ep50 (@ep362 3710910464 5 32768 373823 463863808 (ep367 rfl rfl) rfl) ep368 rfl) rfl rfl))

noncomputable def ep369 := nat_lit 197548421233170458301982433999

noncomputable def ep370 := nat_lit 109611994509920508298919936000

noncomputable def ep371 := nat_lit 8731321436132263850667401515422427

noncomputable def ep372 := nat_lit 1372837727091384114520497015750656000

noncomputable abbrev qz422 := (Enclosure.sfrac Bool.false 38999 1000)

noncomputable abbrev qz408 := (@HAdd.hAdd Complex Complex Complex qz416 (@HAdd.hAdd Complex Complex Complex qz416 qz417 (@HMul.hMul Complex Complex Complex qz415 Complex.I (@HDiv.hDiv Complex Complex Complex qz418 (↑qz422) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz333 := qz408

noncomputable abbrev qz130 := (Complex.Stirling.logGammaStirling 1 qz333)

noncomputable abbrev qz409 := (@HAdd.hAdd Complex Complex Complex qz416 qz417 (@HMul.hMul Complex Complex Complex qz415 Complex.I (@HDiv.hDiv Complex Complex Complex qz418 (↑qz422) (2 : Complex))))

noncomputable abbrev qz334 := qz409

noncomputable abbrev qz131 := qz334

noncomputable abbrev qz410 := qz422

noncomputable abbrev qz335 := qz410

noncomputable abbrev qz132 := (@HMul.hMul Real Real Real qz249 (@HDiv.hDiv Real Real Real qz252 qz335 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz423 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 38999 1000)))

noncomputable abbrev qz411 := qz423

noncomputable abbrev qz336 := qz411

noncomputable abbrev qz133 := qz336

noncomputable def ep373 := Complex.re (@HMul.hMul Complex Complex Complex qz4 (Complex.exp (@HMul.hMul Complex Complex Complex qz4 Complex.I ↑(@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))))) qz132))) (zetaApproximant qz133 1 8))

noncomputable def ep374 := @Enclosure.Real.IsNear.of_eq ep373 (@HSub.hSub Real Real Real qz5 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))))) qz132)) (Complex.re (zetaApproximant qz133 1 8))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))))) qz132)) (Complex.im (zetaApproximant qz133 1 8))))

noncomputable def ep375 := nat_lit 197551247816788960192113381959

noncomputable def ep376 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))))) qz132)) (Complex.re (zetaApproximant qz133 1 8))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))))) qz132)) (Complex.im (zetaApproximant qz133 1 8))) ep375

noncomputable def ep377 := nat_lit 5153380925155993382349511435309837

noncomputable def ep378 := nat_lit 823702636254830468712298209450393600

noncomputable def ep379 := nat_lit 2740299862748012707472998400

noncomputable def ep380 := nat_lit 26691230163551540015915460607381

noncomputable def ep381 := nat_lit 257407073829634521472593190453248000

noncomputable def ep382 := nat_lit 541341911591343606131039418086595965764145233402632601600

noncomputable def ep383 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))))) qz132)) (Complex.re (zetaApproximant qz133 1 8)) 131071 131072 202837

noncomputable def ep384 := nat_lit 1507207908818800193727929

noncomputable def ep385 := nat_lit 41517795719503500085129121

noncomputable def ep386 := nat_lit 8878712049193008702160896000

noncomputable def ep387 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))))) qz132)) Bool.true 131071 131072 1622696

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 514711) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep388 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))))) qz132) qz337 Bool.false 514711 32768 55

noncomputable def ep389 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))))) qz132) Bool.false 7074134682170366117 450359962737049600 144988539722542504366769 ep56

noncomputable def ep390 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))))) qz132 85634572235947473721 2251799813685248000 41475443972542504366769 ep56 2925743979 131072000

noncomputable def ep391 := nat_lit 4636104905307171138437120000

noncomputable def ep392 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 34287718001537743771 1125899906842624000 5693100000999635180689 ep60 Bool.false 85634572235947473721 2251799813685248000

noncomputable def ep393 := @Enclosure.Complex.IsNear.subLitP qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 27596601353156833771 1125899906842624000 5437100000883669228689 ep60 Bool.false 92535808705293033721 2251799813685248000 35331443972368555438769

noncomputable def ep394 := nat_lit 19302269251888753830274362666647552

noncomputable def ep395 := nat_lit 24103989225740304069788593580670976

noncomputable abbrev qz338 := (@HSub.hSub Complex Complex Complex qz393 qz408 qz399)

noncomputable abbrev qz339 := (Complex.log qz408)

noncomputable abbrev qz134 := (@HSub.hSub Complex Complex Complex qz255 (@HMul.hMul Complex Complex Complex qz254 qz338 qz339) qz333)

noncomputable abbrev qz135 := qz333

noncomputable def ep396 := @Enclosure.Complex.IsNear.of_eq qz130 (@HAdd.hAdd Complex Complex Complex qz8 (@HAdd.hAdd Complex Complex Complex qz8 qz134 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz135 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k)))))) Bool.true 27596601353156833771

noncomputable def ep397 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz8 qz134 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz135 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) Bool.true 27597149266622689771 1125899906842624000

noncomputable def ep398 := nat_lit 29631625073139486851338338304

noncomputable def ep399 := nat_lit 9935956802453642048208004710400

noncomputable def ep400 := @ep397 5309628418205859461 14156000000000000000000 Bool.false 18509061125703488357 450359962737049600 718734375279131547 3539000000000000000000 Bool.false 522531 1073741824 3 1073741824 Bool.true 2264242941 536870912000 38999 1610612736000 Bool.true ep398 27596601353156833771 1125899906842624000 5437100000883669228689 ep60 Bool.false ep399

noncomputable def ep401 := @Enclosure.Complex.IsNear.addLitP qz134 qz14 Bool.true 28631772528490721771 1125899906842624000 5093625000237109461 14156000000000000000000

noncomputable def ep402 := nat_lit 1808606774337384596832256

noncomputable def ep403 := @ep401 Bool.false 18509061125703488357 450359962737049600 718734375279131547 3539000000000000000000 Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 Bool.true ep402 27597149266622689771 1125899906842624000 5309628418205859461 14156000000000000000000 Bool.false 18509061125703488357 18509061125703488357 450359962737049600

noncomputable abbrev qz136 := (@HMul.hMul Complex Complex Complex qz254 qz338 qz339)

noncomputable def ep404 := @Enclosure.Complex.IsNear.subLitP qz136 qz135 Bool.true 26098497738094817771 1125899906842624000 5093625000237109461 14156000000000000000000 Bool.false 136454276095472935161

noncomputable def ep405 := @ep404 2251799813685248000 718734375279131547 3539000000000000000000 Bool.false 9000 4000 0 1 Bool.false 77998 4000 0 1 Bool.true 114527090113962887084000 28631772528490721771 1125899906842624000 5093625000237109461 14156000000000000000000 Bool.false 370181222514069767140000 18509061125703488357 450359962737049600 718734375279131547 3539000000000000000000

noncomputable abbrev qz137 := qz338

noncomputable abbrev qz138 := qz339

noncomputable def ep406 := @Enclosure.Complex.IsNear.mul qz137 qz138 Bool.true 26098497738094817771 1125899906842624000 5093625000237109461 14156000000000000000000 Bool.false 136454276095472935161 2251799813685248000 718734375279131547

noncomputable abbrev qz139 := (Complex.re qz338)

noncomputable abbrev qz140 := (Complex.re qz339)

noncomputable abbrev qz141 := (Complex.im qz338)

noncomputable abbrev qz142 := (Complex.im qz339)

noncomputable def ep407 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz139 qz140) (@HMul.hMul Real Real Real qz0 qz141 qz142) 23462622446471873 4503599627370496 54687500024773 3539000000000000000 31964153349712786021 1125899906842624000

noncomputable def ep408 := nat_lit 117537184688213554022081749021884416

noncomputable def ep409 := @Enclosure.Real.IsNear.mulLit_ff qz139 qz140 7000 4000 0 1 3351803206638839 1125899906842624 7812500003539 884750000000000000

noncomputable def ep410 := @Enclosure.Complex.IsNear.re_isNear qz137 Bool.false 7000 4000 0 1 Bool.false 77998 4000 0 1

noncomputable abbrev qz340 := (Enclosure.sfrac Bool.false 77998 4000)

noncomputable abbrev qz143 := qz340

noncomputable def ep411 := @Enclosure.Complex.IsNear.of_eq qz137 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz143) Bool.false 7000 4000 0 1 Bool.false 77998 4000 0

noncomputable abbrev qz144 := (Complex.mk qz272 qz340)

noncomputable def ep412 := @Enclosure.Complex.IsNear.of_eq qz138 (Complex.log qz144) Bool.false 3351803206638839 1125899906842624 7812500003539 884750000000000000 Bool.false 819614691394979 562949953421312 125000000003539 7078000000000000000

noncomputable def ep413 := nat_lit 122531624846649601414448192969443059096501150027820475842990080

noncomputable def ep414 := nat_lit 1701879614403922283536153327373275574474609943920686170402816

noncomputable def ep415 := nat_lit 1175604487970525294547554566600419363059228274464686141440

noncomputable def ep416 := BSN.log_dyadic_bound 2068688004 10260688004 4 3 ep413 131072 56624 ep414 ep415 53585 12329376008 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2068688004) (BSN.artanhQ 10260688004) 0 3 ep414 ep413 ep415 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz341 := (Real.log (Enclosure.sfrac Bool.false 6164688004 16000000))

noncomputable def ep417 := @Enclosure.Real.IsNear.mulLit_ff qz32 qz341 1 2 0 1 3351803206638839 562949953421312 7812500003539 442375000000000000 3351803206638839 1125899906842624 7812500003539 884750000000000000 qz33 (BSN.isNear_log_sfrac 6164688004 16000000 3351803206638839 562949953421312 7812500003539 442375000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6164688004) qz274)) Bool.false 28116963193636217946112 4722366482869645213696 1000000000452992 56624000000000000000 3351803206638839 562949953421312 7812500003539 442375000000000000 (BSN.log_rat_reduce_isNear 6164688004 16000000 8 12329376008 8192000000 53585 131072 24973259072661432 36028797018963968 56624 1000000000000000 rfl rfl rfl rfl (ep416 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep418 := BSN.arctan_dyadic_bound_f 9000 77998 1 0 131072 56624 0 1 1 0 1 1 15056 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 77998) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 77998) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz342 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 77998)))

noncomputable def ep419 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz342 884279719003555 562949953421312 1 2000000000000000 15056 131072 1 56624 107428536830522687488 819614691394979 562949953421312 125000000003539 7078000000000000000 qz35 (ep418 rfl) rfl rfl

noncomputable abbrev qz145 := qz335

noncomputable abbrev qz343 := (@Eq.refl Real qz410)

noncomputable abbrev qz146 := qz343

noncomputable abbrev qz344 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 77998) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep420 := @Enclosure.Complex.IsNear.re_isNear qz138 Bool.false 3351803206638839 1125899906842624 7812500003539 884750000000000000 Bool.false 819614691394979 562949953421312 125000000003539 7078000000000000000 (ep412 (@congrArg Complex Complex qz135 qz144 Complex.log (BSN.w_shift_mk qz145 Bool.false 38999 1000 2 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz144) Bool.false 3351803206638839 1125899906842624 7812500003539 884750000000000000 Bool.false 819614691394979 562949953421312 125000000003539 7078000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz144)) (@HMul.hMul Real Real Real qz0 qz32 qz341) Bool.false 3351803206638839 1125899906842624 7812500003539 884750000000000000 (Enclosure.clog_re_eq 9000 77998 4000 6164688004 16000000 rfl rfl rfl) (ep417 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz144)) qz344 Bool.false 819614691394979 562949953421312 125000000003539 7078000000000000000 (Enclosure.clog_im_eq 9000 77998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz344 (@HSub.hSub Real Real Real qz5 qz34 qz342) Bool.false 819614691394979 562949953421312 125000000003539 7078000000000000000 (BSN.arctan_recip 77998 9000 rfl rfl) ep419))))

noncomputable def ep421 := @Enclosure.Real.IsNear.mulLit_ff qz141 qz142 77998 4000 0 1 819614691394979 562949953421312 125000000003539 7078000000000000000

noncomputable def ep422 := @Enclosure.Complex.IsNear.im_isNear qz137 Bool.false 7000 4000 0 1 Bool.false 77998 4000 0 1

noncomputable def ep423 := @Enclosure.Complex.IsNear.im_isNear qz138 Bool.false 3351803206638839 1125899906842624 7812500003539 884750000000000000 Bool.false 819614691394979 562949953421312 125000000003539 7078000000000000000 (ep412 (@congrArg Complex Complex qz135 qz144 Complex.log (BSN.w_shift_mk qz145 Bool.false 38999 1000 2 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz144) Bool.false 3351803206638839 1125899906842624 7812500003539 884750000000000000 Bool.false 819614691394979 562949953421312 125000000003539 7078000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz144)) (@HMul.hMul Real Real Real qz0 qz32 qz341) Bool.false 3351803206638839 1125899906842624 7812500003539 884750000000000000 (Enclosure.clog_re_eq 9000 77998 4000 6164688004 16000000 rfl rfl rfl) (ep417 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz144)) qz344 Bool.false 819614691394979 562949953421312 125000000003539 7078000000000000000 (Enclosure.clog_im_eq 9000 77998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz344 (@HSub.hSub Real Real Real qz5 qz34 qz342) Bool.false 819614691394979 562949953421312 125000000003539 7078000000000000000 (BSN.arctan_recip 77998 9000 rfl rfl) ep419))))

noncomputable abbrev qz345 := (Enclosure.Real.IsNear.const Bool.false 77998 4000)

noncomputable abbrev qz147 := (@ep411 1 (BSN.w_sub_half_mk qz335 Bool.false 38999 1000 2 qz343 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz340 Bool.false 7000 4000 0 1 Bool.false 77998 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz345))

noncomputable def ep424 := @ep407 4874875000138017461 14156000000000000000000 ep408 26098497738094817771 1125899906842624000 5093625000237109461 14156000000000000000000 (@ep409 23462622446471873 4503599627370496 54687500024773 3539000000000000000 (ep410 qz147) ep420 rfl) (@ep421 31964153349712786021 1125899906842624000 4874875000138017461 14156000000000000000000 (ep422 qz147) ep423 rfl) rfl

noncomputable def ep425 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz139 qz142) (@HMul.hMul Real Real Real qz0 qz141 qz140) 5737302839764853 2251799813685248 875000000024773 28312000000000000000 130716973255708082161 2251799813685248000

noncomputable def ep426 := nat_lit 307267713488341345327971562766204928

noncomputable def ep427 := @Enclosure.Real.IsNear.mulLit_ff qz139 qz142 7000 4000 0 1 819614691394979 562949953421312 125000000003539 7078000000000000000

noncomputable def ep428 := @Enclosure.Real.IsNear.mulLit_ff qz141 qz140 77998 4000 0 1 3351803206638839 1125899906842624 7812500003539 884750000000000000

noncomputable def ep429 := @ep425 304679687638017461 1769500000000000000000 ep426 136454276095472935161 2251799813685248000 718734375279131547 3539000000000000000000 (@ep427 5737302839764853 2251799813685248 875000000024773 28312000000000000000 (ep410 qz147) ep423 rfl) (@ep428 130716973255708082161 2251799813685248000 304679687638017461 1769500000000000000000 (ep422 qz147) ep420 rfl) rfl

noncomputable def ep430 := @Enclosure.Complex.IsNear.of_eq qz135 qz144 Bool.false 9000 4000 0 1 Bool.false 77998 4000 0 1 (BSN.w_shift_mk qz145 Bool.false 38999 1000 2 qz146 rfl)

noncomputable abbrev qz346 := (ep430 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 77998 4000) Bool.false 9000 4000 0 1 Bool.false 77998 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 77998 4000)))

noncomputable abbrev qz148 := qz346

noncomputable def ep431 := ep405 (@ep406 3539000000000000000000 (ep424 rfl) (ep429 rfl)) qz148 rfl rfl rfl rfl rfl rfl

noncomputable def ep432 := @ep403 718734375279131547 3539000000000000000000 (ep431 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz40 (↑qz3) Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 (@ep100 65536 1 65536 (ep102 rfl) (ep104 rfl) rfl rfl) (@ep105 1 0 1 (ep107 rfl) (ep109 rfl) rfl rfl))

noncomputable abbrev qz347 := (@HPow.hPow Complex Int Complex qz401 qz408 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz149 := qz347

noncomputable def ep433 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz135 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz135 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46) qz149)) Bool.false 522531 1073741824 3 1073741824

noncomputable def ep434 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz135 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46) qz149) Bool.false 0 1 0 1 Bool.false

noncomputable def ep435 := @ep434 0 1 0 1 Bool.false 522531 1073741824 3 1073741824 Bool.true 2264242941 536870912000 38999 1610612736000 Bool.false 522531 522531 1073741824 3 1073741824 Bool.true 2264242941 2264242941 536870912000 38999

noncomputable def ep436 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz135 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz43 qz43) Bool.false 0 1 0 1 Bool.false

noncomputable def ep437 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46) qz149 Bool.false 522531 1073741824 3 1073741824 Bool.true 2264242941 536870912000 38999 1610612736000

noncomputable abbrev qz150 := (Complex.re qz347)

noncomputable abbrev qz151 := (Complex.im qz347)

noncomputable def ep438 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz150) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz151) 522531 1073741824 3 1073741824 0 1 0

noncomputable def ep439 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz150 1 12 0 1 1567593 268435456 9 268435456 522531

noncomputable def ep440 := @Enclosure.Complex.IsNear.re_isNear qz149 Bool.false 1567593 268435456 9 268435456 Bool.true 6792728823 134217728000 38999 134217728000

noncomputable abbrev qz348 := (@HPow.hPow Complex Nat Complex qz402 qz408 1)

noncomputable abbrev qz152 := (@Inv.inv Complex Complex.instInv qz348)

noncomputable def ep441 := @Enclosure.Complex.IsNear.of_eq qz149 qz152 Bool.false 1567593 268435456 9 268435456 Bool.true 6792728823 134217728000 38999

noncomputable def ep442 := @Enclosure.Complex.IsNear.of_parts qz152 Bool.false 1567593 268435456 9 268435456 Bool.true 6792728823 134217728000 38999

noncomputable abbrev qz153 := (Complex.re qz348)

noncomputable abbrev qz154 := qz348

noncomputable def ep443 := @Enclosure.Real.IsNear.mulLit_ff qz153 (@Inv.inv Real Real.instInv (@DFunLike.coe qz52 Complex (fun (x : Complex) => Real) qz53 Complex.normSq qz154)) 9000 4000 0 1 174177 67108864 1 67108864

noncomputable def ep444 := @Enclosure.Complex.IsNear.re_isNear qz154 Bool.false 9000 4000 0 1 Bool.false 77998 4000 0 1

noncomputable def ep445 := @Enclosure.Complex.IsNear.of_eq qz154 qz135 Bool.false 9000 4000 0 1 Bool.false 77998 4000 0

noncomputable def ep446 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz52 Complex (fun (x : Complex) => Real) qz53 Complex.normSq qz154)) Bool.false 174177 67108864 1 67108864 174177 67108864 1

noncomputable abbrev qz155 := (Complex.im qz348)

noncomputable def ep447 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz52 Complex (fun (x : Complex) => Real) qz53 Complex.normSq qz154) (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 qz153 qz153) (@HMul.hMul Real Real Real qz0 qz155 qz155)) Bool.false 1541172001 4000000 0 1

noncomputable def ep448 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz153 qz153) (@HMul.hMul Real Real Real qz0 qz155 qz155) 81 16 0 1 1520922001 4000000

noncomputable def ep449 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz153 9000 4000 0 1 9000 4000 0 1

noncomputable def ep450 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz155 77998 4000 0 1 77998 4000 0 1

noncomputable def ep451 := @Enclosure.Complex.IsNear.im_isNear qz154 Bool.false 9000 4000 0 1 Bool.false 77998 4000 0 1

noncomputable abbrev qz156 := (ep444 (@ep445 1 (BSN.pow_one_c qz333) qz346))

noncomputable abbrev qz157 := (ep451 (@ep445 1 (BSN.pow_one_c qz333) qz346))

noncomputable def ep452 := @ep448 0 1 24658752016 1541172001 4000000 0 1 (@ep449 81 16 0 1 qz156 qz156 rfl) (@ep450 1520922001 4000000 0 1 qz157 qz157 rfl)

noncomputable def ep453 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz52 Complex (fun (x : Complex) => Real) qz53 Complex.normSq qz154) 1541172001 4000000 0 1 87088 87089 33554432 (ep447 (Enclosure.Complex.normSq_eq_mul_add_mul qz154) (ep452 rfl rfl)) rfl

noncomputable def ep454 := @Enclosure.Real.IsNear.of_eq (Complex.re qz152) (@HMul.hMul Real Real Real qz0 qz153 (@Inv.inv Real Real.instInv (@DFunLike.coe qz52 Complex (fun (x : Complex) => Real) qz53 Complex.normSq qz154))) Bool.false 1567593 268435456 9 268435456 (Enclosure.Complex.inv_re_eq_mul qz154) (@ep443 1567593 268435456 9 268435456 qz156 (@ep446 67108864 (ep453 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep455 := @Enclosure.Real.IsNear.of_eq (Complex.im qz152) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz155) (@Inv.inv Real Real.instInv (@DFunLike.coe qz52 Complex (fun (x : Complex) => Real) qz53 Complex.normSq qz154))) Bool.true 6792728823 134217728000 38999 134217728000 (Enclosure.Complex.inv_im_eq_mul qz154)

noncomputable def ep456 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz155) (@Inv.inv Real Real.instInv (@DFunLike.coe qz52 Complex (fun (x : Complex) => Real) qz53 Complex.normSq qz154)) 77998 4000 0 1 174177 67108864 1

noncomputable def ep457 := @ep456 67108864 6792728823 134217728000 38999 134217728000 (@Enclosure.Real.IsNear.neg qz155 Bool.false 77998 4000 0 1 qz157) (@ep446 67108864 (ep453 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep458 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz151 0 1 0 1 6792728823 134217728000 38999 134217728000 0

noncomputable def ep459 := @Enclosure.Complex.IsNear.im_isNear qz149 Bool.false 1567593 268435456 9 268435456 Bool.true 6792728823 134217728000 38999 134217728000

noncomputable abbrev qz158 := (@ep441 134217728000 (BSN.zpow_one_sub_two_mul qz333 1 1 rfl rfl) (@ep442 134217728000 ep454 (ep455 ep457)))

noncomputable def ep460 := @ep438 1 522531 522531 1073741824 3 1073741824 (@ep439 1073741824 3 1073741824 ep119 (ep440 qz158) rfl) (@ep458 1 0 1 ep139 (ep459 qz158) rfl) rfl

noncomputable def ep461 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz151) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz150) 2264242941 536870912000 38999 1610612736000 0 1 0

noncomputable def ep462 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz151 1 12 0 1 6792728823 134217728000 38999 134217728000 2264242941

noncomputable def ep463 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz45)) qz46)) qz150 0 1 0 1 1567593 268435456 9 268435456 0

noncomputable def ep464 := @ep461 1 2264242941 2264242941 536870912000 38999 1610612736000 (@ep462 536870912000 38999 1610612736000 ep119 (ep459 qz158) rfl) (@ep463 1 0 1 ep139 (ep440 qz158) rfl) rfl

noncomputable def ep465 := @ep435 1610612736000 (@ep436 0 1 0 1 (BSN.stirling_sum_base qz135) qz60) (ep437 (ep460 rfl) (ep464 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep466 := @ep400 92535808705293033721 2251799813685248000 35331443972368555438769 ep56 (ep432 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep433 Bool.true 2264242941 536870912000 38999 1610612736000 (BSN.stirling_sum_succ qz135 0 1 rfl) (ep465 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep467 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz145 2) Bool.false 3345558324190455 562949953421312 7812500003539 442375000000000000 Bool.false 862654558668195 281474976710656

noncomputable abbrev qz159 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz257 qz334 qz282))

noncomputable def ep468 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 2) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz145 1) qz159) Bool.false 3345558324190455 562949953421312 7812500003539 442375000000000000 Bool.false 862654558668195 281474976710656 125000000003539 3539000000000000000

noncomputable def ep469 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz145 1) qz159 Bool.false 3344450222628087 1125899906842624 7812500003539 884750000000000000 Bool.false 877064173946275 562949953421312 125000000003539 7078000000000000000 Bool.false

noncomputable def ep470 := nat_lit 7533527611085197095919775907840

noncomputable def ep471 := nat_lit 971262687241885670532899143680

noncomputable abbrev qz160 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz257 qz334 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep472 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 1) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz145 0) qz160) Bool.false 3344450222628087 1125899906842624 7812500003539 884750000000000000 Bool.false 877064173946275 562949953421312 125000000003539 7078000000000000000

noncomputable def ep473 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz145 0) qz160 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz349 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz143))

noncomputable def ep474 := @Enclosure.Complex.IsNear.of_eq qz160 qz349 Bool.false 3344450222628087 1125899906842624 7812500003539 884750000000000000 Bool.false 877064173946275 562949953421312 125000000003539 7078000000000000000

noncomputable def ep475 := nat_lit 116910109959347088000397231372500787279770280939512866242990080

noncomputable def ep476 := nat_lit 1521968070132942208514166151547368728911992386074588250402816

noncomputable def ep477 := nat_lit 927878652742729103186008108135876868025687659091886141440

noncomputable def ep478 := BSN.log_dyadic_bound 1988688004 10180688004 4 3 ep475 131072 56624 ep476 ep477 51873 12169376008 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 1988688004) (BSN.artanhQ 10180688004) 0 3 ep476 ep475 ep477 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep479 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 6084688004 16000000)) 1 2 0 1 3344450222628087 562949953421312 7812500003539 442375000000000000 3344450222628087 1125899906842624 7812500003539 884750000000000000 qz33 (BSN.isNear_log_sfrac 6084688004 16000000 3344450222628087 562949953421312 7812500003539 442375000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6084688004) qz274)) Bool.false 28055281893139751632896 4722366482869645213696 1000000000452992 56624000000000000000 3344450222628087 562949953421312 7812500003539 442375000000000000 (BSN.log_rat_reduce_isNear 6084688004 16000000 8 12169376008 8192000000 51873 131072 24973259072661432 36028797018963968 56624 1000000000000000 rfl rfl rfl rfl (ep478 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep480 := BSN.arctan_dyadic_bound_f 1000 77998 1 0 131072 56624 0 1 1 0 1 1 1680 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 77998) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 77998) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz350 := (@Nat.cast Real Real.instNatCast 77998)

noncomputable def ep481 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz287 qz350)) 884279719003555 562949953421312 1 2000000000000000 1680 131072 1 56624 114958555407486156800 877064173946275 562949953421312 125000000003539 7078000000000000000 qz35 (ep480 rfl) rfl rfl

noncomputable abbrev qz161 := (@HAdd.hAdd Complex Complex Complex qz257 qz334 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz351 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz143)

noncomputable def ep482 := @ep473 3344450222628087 1125899906842624 7812500003539 884750000000000000 Bool.false 877064173946275 562949953421312 125000000003539 7078000000000000000 Bool.false 3344450222628087 3344450222628087 1125899906842624 7812500003539 884750000000000000 Bool.false 877064173946275 877064173946275 562949953421312 125000000003539 7078000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 0) (Complex.mk qz43 qz43) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz145) qz60) (ep474 (@congrArg Complex Complex qz161 qz351 Complex.log (BSN.w_shift_mk qz145 Bool.false 38999 1000 0 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts qz349 Bool.false 3344450222628087 1125899906842624 7812500003539 884750000000000000 Bool.false 877064173946275 562949953421312 125000000003539 7078000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz349) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 6084688004 16000000))) Bool.false 3344450222628087 1125899906842624 7812500003539 884750000000000000 (Enclosure.clog_re_eq 1000 77998 4000 6084688004 16000000 rfl rfl rfl) (ep479 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz349) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz350 qz287)) Bool.false 877064173946275 562949953421312 125000000003539 7078000000000000000 (Enclosure.clog_im_eq 1000 77998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz350 qz287)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz287 qz350))) Bool.false 877064173946275 562949953421312 125000000003539 7078000000000000000 (BSN.arctan_recip 77998 1000 rfl rfl) ep481)))) rfl rfl

noncomputable abbrev qz352 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz143))

noncomputable def ep483 := @Enclosure.Complex.IsNear.of_eq qz159 qz352 Bool.false 3346666425752823 1125899906842624 7812500003539 884750000000000000 Bool.false 848244943390115 562949953421312 125000000003539 7078000000000000000

noncomputable def ep484 := nat_lit 118573512848510475178707129295089549508319649365205149122990080

noncomputable def ep485 := nat_lit 1574399942973563597891125368131165879229197145268417626402816

noncomputable def ep486 := nat_lit 997125924709291662180652701531809971351135443703726141440

noncomputable def ep487 := BSN.log_dyadic_bound 2012688004 10204688004 4 3 ep484 131072 56624 ep485 ep486 52389 12217376008 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2012688004) (BSN.artanhQ 10204688004) 0 3 ep485 ep484 ep486 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep488 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 6108688004 16000000)) 1 2 0 1 3346666425752823 562949953421312 7812500003539 442375000000000000 3346666425752823 1125899906842624 7812500003539 884750000000000000 qz33 (BSN.isNear_log_sfrac 6108688004 16000000 3346666425752823 562949953421312 7812500003539 442375000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6108688004) qz274)) Bool.false 28073872752401537040384 4722366482869645213696 1000000000452992 56624000000000000000 3346666425752823 562949953421312 7812500003539 442375000000000000 (BSN.log_rat_reduce_isNear 6108688004 16000000 8 12217376008 8192000000 52389 131072 24973259072661432 36028797018963968 56624 1000000000000000 rfl rfl rfl rfl (ep487 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep489 := BSN.arctan_dyadic_bound_f 5000 77998 1 0 131072 56624 0 1 1 0 1 1 8390 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 77998) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 77998) 0 0 rfl) rfl rfl rfl

noncomputable def ep490 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz291 qz350)) 884279719003555 562949953421312 1 2000000000000000 8390 131072 1 56624 111181161220029153280 848244943390115 562949953421312 125000000003539 7078000000000000000 qz35 (ep489 rfl) rfl rfl

noncomputable abbrev qz162 := (@HAdd.hAdd Complex Complex Complex qz257 qz334 qz282)

noncomputable abbrev qz353 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz143)

noncomputable def ep491 := @ep469 3346666425752823 1125899906842624 7812500003539 884750000000000000 Bool.false 848244943390115 562949953421312 125000000003539 7078000000000000000 Bool.false ep470 3345558324190455 562949953421312 7812500003539 442375000000000000 Bool.false ep471 862654558668195 281474976710656 125000000003539 3539000000000000000 (ep472 (BSN.log_sum_c_succ qz145 0 1 rfl) (ep482 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep483 (@congrArg Complex Complex qz162 qz353 Complex.log (BSN.w_shift_mk qz145 Bool.false 38999 1000 1 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts qz352 Bool.false 3346666425752823 1125899906842624 7812500003539 884750000000000000 Bool.false 848244943390115 562949953421312 125000000003539 7078000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz352) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 6108688004 16000000))) Bool.false 3346666425752823 1125899906842624 7812500003539 884750000000000000 (Enclosure.clog_re_eq 5000 77998 4000 6108688004 16000000 rfl rfl rfl) (ep488 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz352) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz350 qz291)) Bool.false 848244943390115 562949953421312 125000000003539 7078000000000000000 (Enclosure.clog_im_eq 5000 77998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz350 qz291)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz291 qz350))) Bool.false 848244943390115 562949953421312 125000000003539 7078000000000000000 (BSN.arctan_recip 77998 5000 rfl rfl) ep490)))) rfl rfl

noncomputable def ep492 := @ep393 ep56 Bool.false 3345558324190455 562949953421312 7812500003539 442375000000000000 Bool.false 862654558668195 281474976710656 125000000003539 3539000000000000000 Bool.true ep394 34287718001537743771 1125899906842624000 5693100000999635180689 ep60 Bool.false ep395 85634572235947473721 2251799813685248000 41475443972542504366769 ep56 (@ep396 1125899906842624000 5437100000883669228689 ep60 Bool.false 92535808705293033721 2251799813685248000 35331443972368555438769 ep56 (BSN.logGammaStirling_unfold 1 qz135) (ep466 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep467 125000000003539 3539000000000000000 (BSN.log_sum_c_eq qz145 2) (ep468 (BSN.log_sum_c_succ qz145 1 2 rfl) (ep491 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz163 := (@HDiv.hDiv Real Real Real qz252 qz335 (2 : Real))

noncomputable def ep493 := @Enclosure.Real.IsNear.mulLit_ff qz163 (Real.log Real.pi) 38999 2000 0 1 75021 65536 1 32768 2925743979 131072000 38999 65536000 (@Enclosure.Real.IsNear.of_eq qz163 (Enclosure.sfrac Bool.false 38999 2000) Bool.false 38999 2000 0 1 (BSN.t_half_eq qz145 Bool.false 38999 1000 qz146) (Enclosure.Real.IsNear.const Bool.false 38999 2000)) EMRow06.d5 rfl

noncomputable def ep494 := @ep390 38999 65536000 ep391 7074134682170366117 450359962737049600 144988539722542504366769 ep56 (@ep392 41475443972542504366769 ep56 (ep492 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep493 rfl rfl

noncomputable def ep495 := nat_lit 497048500635992941278709264631778202067139925682697725399381553195165505

noncomputable def ep496 := nat_lit 998088444005431997316880136454194539381330553241187008232418397038401

noncomputable def ep497 := nat_lit 1300177739423020337258106458576588499969225270178008311366003961915942721

noncomputable def ep498 := BSN.sin_dyadic_bound_f 421595657 268435456 3 2 131072 56680 ep495 ep177 ep496 ep497 ep180 ep496 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 421595657) qz293 0 2 ep495 ep177 ep496 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 421595657) qz294 0 2 ep497 ep180 ep496 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz354 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep499 := @ep388 65536 Bool.true 131071 131072 1 28312 (@ep389 514711 32768 55 65536 ep494 rfl) (Enclosure.sfrac_false_div 514711 32768) (BSN.cos_reduce1 qz337 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7416789244073090220032) qz354) 226375608064910080 72057594037927936 Bool.false 131071 131072 2 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q1 514711 32768 226375608064910080 72057594037927936 2 7416789244073090220032 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131071 131072 7416789244073090220032 4722366482869645213696 421595657 268435456 56680 56624 (ep498 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep500 := nat_lit 4152172309425096080183201

noncomputable def ep501 := nat_lit 887871204919300870216089600

noncomputable abbrev qz412 := (@Neg.neg Complex Complex.instNeg qz423)

noncomputable abbrev qz355 := qz412

noncomputable abbrev qz164 := qz355

noncomputable abbrev qz356 := (@HPow.hPow Complex Complex Complex qz403 qz405 qz412)

noncomputable abbrev qz165 := qz356

noncomputable abbrev qz166 := (@HAdd.hAdd Complex Complex Complex qz257 (@HDiv.hDiv Complex Complex Complex qz265 qz298 (@HSub.hSub Complex Complex Complex qz255 qz336 (1 : Complex))) qz264)

noncomputable def ep502 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz133 1 8) (@HAdd.hAdd Complex Complex Complex qz8 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 8, @HPow.hPow Complex Complex Complex qz67 (@Nat.cast Complex Complex.instNatCast n) qz164) (@HMul.hMul Complex Complex Complex qz4 qz165 (@HAdd.hAdd Complex Complex Complex qz8 qz166 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) Bool.false ep384 836273151473392549888000 ep385

noncomputable def ep503 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 8, @HPow.hPow Complex Complex Complex qz67 (@Nat.cast Complex Complex.instNatCast n) qz164) (@HMul.hMul Complex Complex Complex qz4 qz165 (@HAdd.hAdd Complex Complex Complex qz8 qz166 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) Bool.false 29093465039 17179869184 262635239407 60799557042176

noncomputable def ep504 := nat_lit 3164511943964916718057121

noncomputable def ep505 := nat_lit 25893634706597187288079677507239936

noncomputable def ep506 := nat_lit 101167368340624655221722047315968

noncomputable def ep507 := @ep503 Bool.true 1160080471 4294967296 32837680435 7599944630272 Bool.false 91010647078026656479929 836273151473392549888000 ep504 ep386 Bool.false 32914958317031207980767 209068287868348137472000 315877137162120046775201 ep501 Bool.false ep505 ep384 836273151473392549888000 ep385 ep386 Bool.true ep506 23554863487515751091233 209068287868348137472000

noncomputable def ep508 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 8, @HPow.hPow Complex Complex Complex qz67 (@Nat.cast Complex Complex.instNatCast n) qz164) (BSN.headSumC qz133 8) Bool.false 29093465039 17179869184 262635239407 60799557042176 Bool.true 1160080471 4294967296 32837680435

noncomputable abbrev qz167 := (BSN.headSumC qz336 7)

noncomputable abbrev qz168 := (@HPow.hPow Complex Complex Complex qz295 (@Nat.cast Complex Complex.instNatCast 7) qz355)

noncomputable def ep509 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz133 8) (@HAdd.hAdd Complex Complex Complex qz8 qz167 qz168) Bool.false 29093465039 17179869184 262635239407 60799557042176 Bool.true 1160080471 4294967296 32837680435 7599944630272

noncomputable def ep510 := @Enclosure.Complex.IsNear.addLitP qz167 qz168 Bool.false 11681652637 8589934592 7172009429 1899986157568 Bool.true 1585871529 17179869184 229761647191 60799557042176 Bool.false

noncomputable abbrev qz169 := (BSN.headSumC qz336 6)

noncomputable abbrev qz170 := (@HPow.hPow Complex Complex Complex qz295 (@Nat.cast Complex Complex.instNatCast 6) qz355)

noncomputable def ep511 := @Enclosure.Complex.IsNear.of_eq qz167 (@HAdd.hAdd Complex Complex Complex qz8 qz169 qz170) Bool.false 11681652637 8589934592 7172009429 1899986157568 Bool.true 1585871529 17179869184 229761647191 60799557042176

noncomputable def ep512 := @Enclosure.Complex.IsNear.addLitP qz169 qz170 Bool.false 9143298767 8589934592 48372267693 15199889260544 Bool.false 3253305321 17179869184 193777835477 60799557042176 Bool.false

noncomputable abbrev qz171 := (BSN.headSumC qz336 5)

noncomputable abbrev qz172 := (@HPow.hPow Complex Complex Complex qz295 (@Nat.cast Complex Complex.instNatCast 5) qz355)

noncomputable def ep513 := @Enclosure.Complex.IsNear.of_eq qz169 (@HAdd.hAdd Complex Complex Complex qz8 qz171 qz172) Bool.false 9143298767 8589934592 48372267693 15199889260544 Bool.false 3253305321 17179869184 193777835477 60799557042176

noncomputable def ep514 := @Enclosure.Complex.IsNear.addLitP qz171 qz172 Bool.false 10620021487 17179869184 154517516649 60799557042176 Bool.false 687695445 4294967296 19404851357 7599944630272 Bool.false

noncomputable abbrev qz173 := (BSN.headSumC qz336 4)

noncomputable abbrev qz174 := (@HPow.hPow Complex Complex Complex qz295 (@Nat.cast Complex Complex.instNatCast 4) qz355)

noncomputable def ep515 := @Enclosure.Complex.IsNear.of_eq qz171 (@HAdd.hAdd Complex Complex Complex qz8 qz173 qz174) Bool.false 10620021487 17179869184 154517516649 60799557042176 Bool.false 687695445 4294967296 19404851357 7599944630272

noncomputable def ep516 := @Enclosure.Complex.IsNear.addLitP qz173 qz174 Bool.false 8711047871 8589934592 55548388387 30399778521088 Bool.true 2494705155 17179869184 111902129309 60799557042176 Bool.true

noncomputable abbrev qz175 := (BSN.headSumC qz336 3)

noncomputable abbrev qz176 := (@HPow.hPow Complex Complex Complex qz295 qz300 qz355)

noncomputable def ep517 := @Enclosure.Complex.IsNear.of_eq qz173 (@HAdd.hAdd Complex Complex Complex qz8 qz175 qz176) Bool.false 8711047871 8589934592 55548388387 30399778521088 Bool.true 2494705155 17179869184 111902129309 60799557042176

noncomputable def ep518 := @Enclosure.Complex.IsNear.addLitP qz175 qz176 Bool.false 6630590771 8589934592 30593684965 30399778521088 Bool.true 5749296165 8589934592 30883118541 30399778521088 Bool.false

noncomputable abbrev qz177 := (BSN.headSumC qz336 2)

noncomputable abbrev qz178 := (@HPow.hPow Complex Complex Complex qz295 qz301 qz355)

noncomputable def ep519 := @Enclosure.Complex.IsNear.of_eq qz175 (@HAdd.hAdd Complex Complex Complex qz8 qz177 qz178) Bool.false 6630590771 8589934592 30593684965 30399778521088 Bool.true 5749296165 8589934592 30883118541 30399778521088

noncomputable def ep520 := @Enclosure.Complex.IsNear.addLitP qz177 qz178 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep521 := @Enclosure.Complex.IsNear.of_eq qz177 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz43) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz133)

noncomputable abbrev qz179 := (@HMul.hMul Real Real Real qz249 qz335 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable def ep522 := @Enclosure.Complex.IsNear.of_eq qz178 (Complex.mk (@HMul.hMul Real Real Real qz0 qz86 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz86 (@Neg.neg Real Real.instNeg (Real.sin qz179)))) Bool.true 1959343821 8589934592 30593684965 30399778521088 Bool.true 5749296165 8589934592 30883118541 30399778521088 (BSN.cpow_neg_s_mk qz145 38999 1000 2 qz146 rfl)

noncomputable def ep523 := nat_lit 60429607009115666104057009350625

noncomputable def ep524 := BSN.sin_dyadic_bound_f 88168295 268435456 2 1 131072 56680 ep523 ep208 ep523 ep523 ep209 ep523 42281 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 88168295) qz293 0 1 ep523 ep208 ep523 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 88168295) qz294 0 1 ep523 ep209 ep523 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz357 := (Enclosure.Real.IsNear.const Bool.false 38999 1000)

noncomputable abbrev qz180 := qz357

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3543137) qz12)

noncomputable abbrev qz359 := (@Nat.cast Real Real.instNatCast 6204292228697548652544)

noncomputable def ep525 := @Enclosure.Real.IsNear.cos_image qz179 qz358 Bool.false 3543137 131072 181 131072 Bool.true 42281 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 885784287 32768000 38999 28312000 3543137 131072 181 131072 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz90 38999 1000 0 1 45426 65536 1 28312 885784287 32768000 38999 28312000 qz180 qz304 rfl) rfl) (Enclosure.sfrac_false_div 3543137 131072) (BSN.cos_reduce1 qz358 (@HDiv.hDiv Real Real Real qz2 qz359 qz66) 226375608064910080 72057594037927936 Bool.false 42281 131072 4 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q1 3543137 131072 226375608064910080 72057594037927936 4 6204292228697548652544 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 42281 131072 6204292228697548652544 18889465931478580854784 88168295 268435456 56680 56624 (ep524 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep526 := BSN.cos_dyadic_bound_f 88168295 268435456 2 1 131072 56680 ep523 ep243 ep523 ep523 ep244 ep523 124065 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 88168295) qz305 0 1 ep523 ep243 ep523 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 88168295) qz306 0 1 ep523 ep244 ep523 rfl rfl rfl rfl) rfl rfl

noncomputable def ep527 := @Enclosure.Real.IsNear.sin_image qz179 qz358 Bool.false 3543137 131072 181 131072 Bool.false 124065 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 885784287 32768000 38999 28312000 3543137 131072 181 131072 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz90 38999 1000 0 1 45426 65536 1 28312 885784287 32768000 38999 28312000 qz180 qz304 rfl) rfl) (Enclosure.sfrac_false_div 3543137 131072) (BSN.sin_reduce1 qz358 (@HDiv.hDiv Real Real Real qz2 qz359 qz66) 226375608064910080 72057594037927936 Bool.false 124065 131072 4 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q1 3543137 131072 226375608064910080 72057594037927936 4 6204292228697548652544 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 124065 131072 6204292228697548652544 18889465931478580854784 88168295 268435456 56680 56624 (ep526 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep528 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz86 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz86 (@Neg.neg Real Real.instNeg (Real.sin qz179))) Bool.true 1959343821 8589934592 30593684965 30399778521088 Bool.true 5749296165 8589934592 30883118541 30399778521088 (@Enclosure.Real.IsNear.mulLit_ft qz86 (Real.cos qz179) 46341 65536 1 65536 42281 131072 656943 463863808 1959343821 8589934592 30593684965 30399778521088 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz179) Bool.true 42281 131072 5255544 3710910464 42281 131072 656943 463863808 (ep525 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz86 (@Neg.neg Real Real.instNeg (Real.sin qz179)) 46341 65536 1 65536 124065 131072 656943 463863808 5749296165 8589934592 30883118541 30399778521088 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz179) Bool.false 124065 131072 656943 463863808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz179) Bool.false 124065 131072 5255544 3710910464 124065 131072 656943 463863808 (ep527 rfl rfl) rfl)) rfl)

noncomputable def ep529 := @ep520 1959343821 8589934592 30593684965 30399778521088 Bool.true 5749296165 8589934592 30883118541 30399778521088 Bool.false 6630590771 6630590771 8589934592 30593684965 30399778521088 Bool.true 5749296165 5749296165 8589934592 30883118541 30399778521088 (ep521 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz43 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz44)) (ep522 ep528) rfl rfl

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz249 qz335 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep530 := @Enclosure.Complex.IsNear.of_eq qz176 (Complex.mk (@HMul.hMul Real Real Real qz0 qz92 (Real.cos qz181)) (@HMul.hMul Real Real Real qz0 qz92 (@Neg.neg Real Real.instNeg (Real.sin qz181)))) Bool.false 520114275 2147483648 12477351711 15199889260544 Bool.false 9003887175 17179869184 50135892227 60799557042176 (BSN.cpow_neg_s_mk qz145 38999 1000 3 qz146 rfl)

noncomputable def ep531 := nat_lit 182334940436312956127111454351616

noncomputable def ep532 := BSN.sin_dyadic_bound_f 116203036 268435456 2 1 131072 56680 ep531 ep208 ep531 ep531 ep209 ep531 54984 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 116203036) qz293 0 1 ep531 ep208 ep531 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 116203036) qz294 0 1 ep531 ep209 ep531 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz360 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1403925) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep533 := @Enclosure.Real.IsNear.cos_image qz181 qz360 Bool.false 1403925 32768 181 131072 Bool.false 54984 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 1403925001 32768000 38999 28312000 1403925 32768 181 131072 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz96 38999 1000 0 1 71998 65536 1 28312 1403925001 32768000 38999 28312000 qz180 qz310 rfl) rfl) (Enclosure.sfrac_false_div 1403925 32768) (BSN.cos_reduce3 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2044265442479670558720) qz354) 226375608064910080 72057594037927936 Bool.false 54984 131072 6 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q3 1403925 32768 226375608064910080 72057594037927936 6 2044265442479670558720 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 54984 131072 2044265442479670558720 4722366482869645213696 116203036 268435456 56680 56624 (ep532 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep534 := BSN.cos_dyadic_bound_f 116203036 268435456 2 1 131072 56680 ep531 ep243 ep531 ep531 ep244 ep531 118981 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 116203036) qz305 0 1 ep531 ep243 ep531 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 116203036) qz306 0 1 ep531 ep244 ep531 rfl rfl rfl rfl) rfl rfl

noncomputable def ep535 := @Enclosure.Real.IsNear.sin_image qz181 qz360 Bool.false 1403925 32768 181 131072 Bool.true 118981 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 1403925001 32768000 38999 28312000 1403925 32768 181 131072 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz96 38999 1000 0 1 71998 65536 1 28312 1403925001 32768000 38999 28312000 qz180 qz310 rfl) rfl) (Enclosure.sfrac_false_div 1403925 32768) (BSN.sin_reduce3 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2044265442479670558720) qz354) 226375608064910080 72057594037927936 Bool.false 118981 131072 6 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q3 1403925 32768 226375608064910080 72057594037927936 6 2044265442479670558720 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 118981 131072 2044265442479670558720 4722366482869645213696 116203036 268435456 56680 56624 (ep534 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep536 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz92 (Real.cos qz181)) (@HMul.hMul Real Real Real qz0 qz92 (@Neg.neg Real Real.instNeg (Real.sin qz181))) Bool.false 520114275 2147483648 12477351711 15199889260544 Bool.false 9003887175 17179869184 50135892227 60799557042176 (@Enclosure.Real.IsNear.mulLit_ff qz92 (Real.cos qz181) 75675 131072 1 131072 6873 16384 656943 463863808 520114275 2147483648 12477351711 15199889260544 qz312 (@Enclosure.Real.IsNear.recentre' (Real.cos qz181) Bool.false 54984 131072 5255544 3710910464 6873 16384 656943 463863808 (ep533 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz92 (@Neg.neg Real Real.instNeg (Real.sin qz181)) 75675 131072 1 131072 118981 131072 656943 463863808 9003887175 17179869184 50135892227 60799557042176 qz312 (@Enclosure.Real.IsNear.neg (Real.sin qz181) Bool.true 118981 131072 656943 463863808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz181) Bool.true 118981 131072 5255544 3710910464 118981 131072 656943 463863808 (ep535 rfl rfl) rfl)) rfl)

noncomputable def ep537 := @ep518 520114275 2147483648 12477351711 15199889260544 Bool.false 9003887175 17179869184 50135892227 60799557042176 Bool.false 18706832859917713408 8711047871 8589934592 55548388387 30399778521088 Bool.true 21429354107775221760 2494705155 17179869184 111902129309 60799557042176 (ep519 (BSN.head_sum_c_succ qz133 2 3 rfl rfl) (ep529 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep530 ep536) rfl rfl

noncomputable abbrev qz182 := (@HMul.hMul Real Real Real qz249 qz335 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep538 := @Enclosure.Complex.IsNear.of_eq qz174 (Complex.mk (@HMul.hMul Real Real Real qz0 qz97 (Real.cos qz182)) (@HMul.hMul Real Real Real qz0 qz97 (@Neg.neg Real Real.instNeg (Real.sin qz182)))) Bool.true 6802074255 17179869184 43420739875 60799557042176 Bool.false 5245486935 17179869184 43336681547 60799557042176 (BSN.cpow_neg_s_mk qz145 38999 1000 4 qz146 rfl)

noncomputable def ep539 := nat_lit 966873712145850657664912149610000

noncomputable def ep540 := BSN.cos_dyadic_bound_f 176336590 268435456 2 1 131072 56680 ep539 ep243 ep539 ep539 ep244 ep539 103793 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 176336590) qz305 0 1 ep539 ep243 ep539 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 176336590) qz306 0 1 ep539 ep244 ep539 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz361 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3543137) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep541 := @Enclosure.Real.IsNear.cos_image qz182 qz361 Bool.false 3543137 65536 181 131072 Bool.true 103793 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz182 Bool.false 885784287 16384000 38999 28312000 3543137 65536 181 131072 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz100 38999 1000 0 1 90852 65536 1 28312 885784287 16384000 38999 28312000 qz180 qz314 rfl) rfl) (Enclosure.sfrac_false_div 3543137 65536) (BSN.cos_reduce2 qz361 (@HDiv.hDiv Real Real Real qz2 qz359 qz311) 226375608064910080 72057594037927936 Bool.false 103793 131072 8 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q2 3543137 65536 226375608064910080 72057594037927936 8 6204292228697548652544 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 103793 131072 6204292228697548652544 9444732965739290427392 176336590 268435456 56680 56624 (ep540 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep542 := BSN.sin_dyadic_bound_f 176336590 268435456 2 1 131072 56680 ep539 ep208 ep539 ep539 ep209 ep539 80041 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 176336590) qz293 0 1 ep539 ep208 ep539 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 176336590) qz294 0 1 ep539 ep209 ep539 rfl rfl rfl rfl) rfl rfl

noncomputable def ep543 := @Enclosure.Real.IsNear.sin_image qz182 qz361 Bool.false 3543137 65536 181 131072 Bool.true 80041 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz182 Bool.false 885784287 16384000 38999 28312000 3543137 65536 181 131072 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz100 38999 1000 0 1 90852 65536 1 28312 885784287 16384000 38999 28312000 qz180 qz314 rfl) rfl) (Enclosure.sfrac_false_div 3543137 65536) (BSN.sin_reduce2 qz361 (@HDiv.hDiv Real Real Real qz2 qz359 qz311) 226375608064910080 72057594037927936 Bool.false 80041 131072 8 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q2 3543137 65536 226375608064910080 72057594037927936 8 6204292228697548652544 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 80041 131072 6204292228697548652544 9444732965739290427392 176336590 268435456 56680 56624 (ep542 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep544 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz97 (Real.cos qz182)) (@HMul.hMul Real Real Real qz0 qz97 (@Neg.neg Real Real.instNeg (Real.sin qz182))) Bool.true 6802074255 17179869184 43420739875 60799557042176 Bool.false 5245486935 17179869184 43336681547 60799557042176 (@Enclosure.Real.IsNear.mulLit_ft qz97 (Real.cos qz182) 65535 131072 1 131072 103793 131072 656943 463863808 6802074255 17179869184 43420739875 60799557042176 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz182) Bool.true 103793 131072 5255544 3710910464 103793 131072 656943 463863808 (ep541 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz97 (@Neg.neg Real Real.instNeg (Real.sin qz182)) 65535 131072 1 131072 80041 131072 656943 463863808 5245486935 17179869184 43336681547 60799557042176 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz182) Bool.true 80041 131072 656943 463863808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz182) Bool.true 80041 131072 5255544 3710910464 80041 131072 656943 463863808 (ep543 rfl rfl) rfl)) rfl)

noncomputable def ep545 := @ep516 6802074255 17179869184 43420739875 60799557042176 Bool.false 5245486935 17179869184 43336681547 60799557042176 Bool.false 91225289938964578304 10620021487 17179869184 154517516649 60799557042176 Bool.false 47258071134130667520 687695445 4294967296 19404851357 7599944630272 (ep517 (BSN.head_sum_c_succ qz133 3 4 rfl rfl) (ep537 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep538 ep544) rfl rfl

noncomputable abbrev qz183 := (@HMul.hMul Real Real Real qz249 qz335 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep546 := @Enclosure.Complex.IsNear.of_eq qz172 (Complex.mk (@HMul.hMul Real Real Real qz0 qz101 (Real.cos qz183)) (@HMul.hMul Real Real Real qz0 qz101 (@Neg.neg Real Real.instNeg (Real.sin qz183)))) Bool.false 7666576047 17179869184 38971554123 60799557042176 Bool.false 502523541 17179869184 38539024621 60799557042176 (BSN.cpow_neg_s_mk qz145 38999 1000 5 qz146 rfl)

noncomputable def ep547 := nat_lit 419348119305180556739738439399216917771589466812400066450614144890777665

noncomputable def ep548 := nat_lit 710874808016663285741062232492244022546351657067729969412124505747521

noncomputable def ep549 := nat_lit 1097141753252969717570019907192961627650992605635319087420179320752255041

noncomputable def ep550 := BSN.sin_dyadic_bound_f 404086313 268435456 3 2 131072 56680 ep547 ep177 ep548 ep549 ep180 ep548 130791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 404086313) qz293 0 2 ep547 ep177 ep548 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 404086313) qz294 0 2 ep549 ep180 ep548 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8226917) qz12)

noncomputable def ep551 := @Enclosure.Real.IsNear.cos_image qz183 qz362 Bool.false 8226917 131072 181 131072 Bool.false 130791 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 1028364631 16384000 38999 28312000 8226917 131072 181 131072 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz104 38999 1000 0 1 105476 65536 1 28312 1028364631 16384000 38999 28312000 qz180 qz317 rfl) rfl) (Enclosure.sfrac_false_div 8226917 131072) (BSN.cos_reduce3 qz362 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28435046428384096681984) qz66) 226375608064910080 72057594037927936 Bool.false 130791 131072 9 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q3 8226917 131072 226375608064910080 72057594037927936 9 28435046428384096681984 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 130791 131072 28435046428384096681984 18889465931478580854784 404086313 268435456 56680 56624 (ep550 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep552 := nat_lit 233287121750885492982406271769561507216459193410030139125635469164097601

noncomputable def ep553 := nat_lit 698439615636623152375736690843700033604284876915954957438082158480797761

noncomputable def ep554 := BSN.cos_dyadic_bound_f 404086313 268435456 3 2 131072 56680 ep552 ep213 ep548 ep553 ep216 ep548 8573 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 404086313) qz305 0 2 ep552 ep213 ep548 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 404086313) qz306 0 2 ep553 ep216 ep548 rfl rfl rfl rfl) rfl rfl

noncomputable def ep555 := @Enclosure.Real.IsNear.sin_image qz183 qz362 Bool.false 8226917 131072 181 131072 Bool.true 8573 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 1028364631 16384000 38999 28312000 8226917 131072 181 131072 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz104 38999 1000 0 1 105476 65536 1 28312 1028364631 16384000 38999 28312000 qz180 qz317 rfl) rfl) (Enclosure.sfrac_false_div 8226917 131072) (BSN.sin_reduce3 qz362 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28435046428384096681984) qz66) 226375608064910080 72057594037927936 Bool.false 8573 131072 9 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q3 8226917 131072 226375608064910080 72057594037927936 9 28435046428384096681984 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8573 131072 28435046428384096681984 18889465931478580854784 404086313 268435456 56680 56624 (ep554 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep556 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz101 (Real.cos qz183)) (@HMul.hMul Real Real Real qz0 qz101 (@Neg.neg Real Real.instNeg (Real.sin qz183))) Bool.false 7666576047 17179869184 38971554123 60799557042176 Bool.false 502523541 17179869184 38539024621 60799557042176 (@Enclosure.Real.IsNear.mulLit_ff qz101 (Real.cos qz183) 58617 131072 1 131072 130791 131072 656943 463863808 7666576047 17179869184 38971554123 60799557042176 qz318 (@Enclosure.Real.IsNear.recentre' (Real.cos qz183) Bool.false 130791 131072 5255544 3710910464 130791 131072 656943 463863808 (ep551 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz101 (@Neg.neg Real Real.instNeg (Real.sin qz183)) 58617 131072 1 131072 8573 131072 656943 463863808 502523541 17179869184 38539024621 60799557042176 qz318 (@Enclosure.Real.IsNear.neg (Real.sin qz183) Bool.true 8573 131072 656943 463863808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz183) Bool.true 8573 131072 5255544 3710910464 8573 131072 656943 463863808 (ep555 rfl rfl) rfl)) rfl)

noncomputable def ep557 := @ep514 7666576047 17179869184 38971554123 60799557042176 Bool.false 502523541 17179869184 38539024621 60799557042176 Bool.false 314161353454576992256 9143298767 8589934592 48372267693 15199889260544 Bool.false 13972839957597782016 3253305321 17179869184 193777835477 60799557042176 (ep515 (BSN.head_sum_c_succ qz133 4 5 rfl rfl) (ep545 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep546 ep556) rfl rfl

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz249 qz335 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep558 := @Enclosure.Complex.IsNear.of_eq qz170 (Complex.mk (@HMul.hMul Real Real Real qz0 qz105 (Real.cos qz184)) (@HMul.hMul Real Real Real qz0 qz105 (@Neg.neg Real Real.instNeg (Real.sin qz184)))) Bool.false 1269176935 4294967296 9003807739 15199889260544 Bool.true 2419588425 8589934592 17991905857 30399778521088 (BSN.cpow_neg_s_mk qz145 38999 1000 6 qz146 rfl)

noncomputable def ep559 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz108 38999 1000 0 1 4034664351997175 2251799813685248 62500000003539 1769500000000000000 6293915002541513113 90071992547409920 2437437500138017461 1769500000000000000000 qz180 (BSN.isNear_log_sfrac 6 1 4034664351997175 2251799813685248 62500000003539 1769500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz320) Bool.false 4230652207559789772800 2361183241434822606848 1000000000056624 28312000000000000000 4034664351997175 2251799813685248 62500000003539 1769500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 26572 65536 24973259072661432 36028797018963968 28312 1000000000000000 rfl rfl rfl rfl (ep263 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep560 := nat_lit 1745515058644822954818612326400256

noncomputable def ep561 := BSN.cos_dyadic_bound_f 204400004 268435456 2 1 131072 56680 ep560 ep243 ep560 ep560 ep244 ep560 94874 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 204400004) qz305 0 1 ep560 ep243 ep560 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 204400004) qz306 0 1 ep560 ep244 ep560 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9158851) qz12)

noncomputable def ep562 := @Enclosure.Real.IsNear.cos_image qz184 qz363 Bool.false 9158851 131072 91 65536 Bool.false 94874 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz184 Bool.false 6293915002541513113 90071992547409920 2437437500138017461 1769500000000000000000 9158851 131072 91 65536 (ep559 rfl) rfl) (Enclosure.sfrac_false_div 9158851 131072) (BSN.cos_reduce0 qz363 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14383371611249292869632) qz66) 226375608064910080 72057594037927936 Bool.false 94874 131072 11 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q0 9158851 131072 226375608064910080 72057594037927936 11 14383371611249292869632 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 94874 131072 14383371611249292869632 18889465931478580854784 204400004 268435456 56680 56624 (ep561 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep563 := BSN.sin_dyadic_bound_f 204400004 268435456 2 1 131072 56680 ep560 ep208 ep560 ep560 ep209 ep560 90435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 204400004) qz293 0 1 ep560 ep208 ep560 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 204400004) qz294 0 1 ep560 ep209 ep560 rfl rfl rfl rfl) rfl rfl

noncomputable def ep564 := @Enclosure.Real.IsNear.sin_image qz184 qz363 Bool.false 9158851 131072 91 65536 Bool.false 90435 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz184 Bool.false 6293915002541513113 90071992547409920 2437437500138017461 1769500000000000000000 9158851 131072 91 65536 (ep559 rfl) rfl) (Enclosure.sfrac_false_div 9158851 131072) (BSN.sin_reduce0 qz363 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14383371611249292869632) qz66) 226375608064910080 72057594037927936 Bool.false 90435 131072 11 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q0 9158851 131072 226375608064910080 72057594037927936 11 14383371611249292869632 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 90435 131072 14383371611249292869632 18889465931478580854784 204400004 268435456 56680 56624 (ep563 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep565 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz105 (Real.cos qz184)) (@HMul.hMul Real Real Real qz0 qz105 (@Neg.neg Real Real.instNeg (Real.sin qz184))) Bool.false 1269176935 4294967296 9003807739 15199889260544 Bool.true 2419588425 8589934592 17991905857 30399778521088 (@Enclosure.Real.IsNear.mulLit_ff qz105 (Real.cos qz184) 26755 65536 1 65536 47437 65536 330241 231931904 1269176935 4294967296 9003807739 15199889260544 qz322 (@Enclosure.Real.IsNear.recentre' (Real.cos qz184) Bool.false 94874 131072 2641928 1855455232 47437 65536 330241 231931904 (ep562 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz105 (@Neg.neg Real Real.instNeg (Real.sin qz184)) 26755 65536 1 65536 90435 131072 330241 231931904 2419588425 8589934592 17991905857 30399778521088 qz322 (@Enclosure.Real.IsNear.neg (Real.sin qz184) Bool.false 90435 131072 330241 231931904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz184) Bool.false 90435 131072 2641928 1855455232 90435 131072 330241 231931904 (ep564 rfl rfl) rfl)) rfl)

noncomputable def ep566 := @ep512 1269176935 4294967296 9003807739 15199889260544 Bool.true 2419588425 8589934592 17991905857 30399778521088 Bool.false 50172316039147159552 11681652637 8589934592 7172009429 1899986157568 Bool.true 13622532705425031168 1585871529 17179869184 229761647191 60799557042176 (ep513 (BSN.head_sum_c_succ qz133 5 6 rfl rfl) (ep557 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep558 ep565) rfl rfl

noncomputable abbrev qz185 := (@HMul.hMul Real Real Real qz249 qz335 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep567 := @Enclosure.Complex.IsNear.of_eq qz168 (Complex.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz185)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz185)))) Bool.false 5730159765 17179869184 33130937679 60799557042176 Bool.true 3054450355 17179869184 32939796289 60799557042176 (BSN.cpow_neg_s_mk qz145 38999 1000 7 qz146 rfl)

noncomputable def ep568 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz112 38999 1000 0 1 4381766428990711 2251799813685248 62500000003539 1769500000000000000 170884508964208738289 2251799813685248000 2437437500138017461 1769500000000000000000 qz180 (BSN.isNear_log_sfrac 7 1 4381766428990711 2251799813685248 62500000003539 1769500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz324) Bool.false 4594615115045363777536 2361183241434822606848 1000000000056624 28312000000000000000 4381766428990711 2251799813685248 62500000003539 1769500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 36674 65536 24973259072661432 36028797018963968 28312 1000000000000000 rfl rfl rfl rfl (ep274 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep569 := nat_lit 298687500592363559826744876325521

noncomputable def ep570 := BSN.cos_dyadic_bound_f 131463219 268435456 2 1 131072 56680 ep569 ep243 ep569 ep569 ep244 ep569 115665 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 131463219) qz305 0 1 ep569 ep243 ep569 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 131463219) qz306 0 1 ep569 ep244 ep569 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9946787) qz12)

noncomputable def ep571 := @Enclosure.Real.IsNear.cos_image qz185 qz364 Bool.false 9946787 131072 91 65536 Bool.false 115665 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz185 Bool.false 170884508964208738289 2251799813685248000 2437437500138017461 1769500000000000000000 9946787 131072 91 65536 (ep568 rfl) rfl) (Enclosure.sfrac_false_div 9946787 131072) (BSN.cos_reduce0 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9250901641851289206784) qz66) 226375608064910080 72057594037927936 Bool.false 115665 131072 12 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q0 9946787 131072 226375608064910080 72057594037927936 12 9250901641851289206784 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 115665 131072 9250901641851289206784 18889465931478580854784 131463219 268435456 56680 56624 (ep570 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep572 := BSN.sin_dyadic_bound_f 131463219 268435456 2 1 131072 56680 ep569 ep208 ep569 ep569 ep209 ep569 61655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 131463219) qz293 0 1 ep569 ep208 ep569 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 131463219) qz294 0 1 ep569 ep209 ep569 rfl rfl rfl rfl) rfl rfl

noncomputable def ep573 := @Enclosure.Real.IsNear.sin_image qz185 qz364 Bool.false 9946787 131072 91 65536 Bool.false 61655 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz185 Bool.false 170884508964208738289 2251799813685248000 2437437500138017461 1769500000000000000000 9946787 131072 91 65536 (ep568 rfl) rfl) (Enclosure.sfrac_false_div 9946787 131072) (BSN.sin_reduce0 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9250901641851289206784) qz66) 226375608064910080 72057594037927936 Bool.false 61655 131072 12 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q0 9946787 131072 226375608064910080 72057594037927936 12 9250901641851289206784 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 61655 131072 9250901641851289206784 18889465931478580854784 131463219 268435456 56680 56624 (ep572 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep574 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz185)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz185))) Bool.false 5730159765 17179869184 33130937679 60799557042176 Bool.true 3054450355 17179869184 32939796289 60799557042176 (@Enclosure.Real.IsNear.mulLit_ff qz109 (Real.cos qz185) 49541 131072 1 131072 115665 131072 330241 231931904 5730159765 17179869184 33130937679 60799557042176 qz326 (@Enclosure.Real.IsNear.recentre' (Real.cos qz185) Bool.false 115665 131072 2641928 1855455232 115665 131072 330241 231931904 (ep571 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz109 (@Neg.neg Real Real.instNeg (Real.sin qz185)) 49541 131072 1 131072 61655 131072 330241 231931904 3054450355 17179869184 32939796289 60799557042176 qz326 (@Enclosure.Real.IsNear.neg (Real.sin qz185) Bool.false 61655 131072 330241 231931904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz185) Bool.false 61655 131072 2641928 1855455232 61655 131072 330241 231931904 (ep573 rfl rfl) rfl)) rfl)

noncomputable def ep575 := @ep510 5730159765 17179869184 33130937679 60799557042176 Bool.true 3054450355 17179869184 32939796289 60799557042176 Bool.false 249910961739648729088 29093465039 17179869184 262635239407 60799557042176 Bool.true 79720122938772422656 1160080471 4294967296 32837680435 7599944630272 (ep511 (BSN.head_sum_c_succ qz133 6 7 rfl rfl) (ep566 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep567 ep574) rfl rfl

noncomputable def ep576 := @Enclosure.Complex.IsNear.mul qz165 (@HAdd.hAdd Complex Complex Complex qz8 qz166 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 91010647078026656479929 836273151473392549888000 ep504 ep386 Bool.false

noncomputable abbrev qz186 := (Complex.re qz356)

noncomputable abbrev qz187 := (Complex.im qz356)

noncomputable def ep577 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz186 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz166 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz187 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz166 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 30965860798898524863 209068287868348137472 2262753391842759990265

noncomputable def ep578 := nat_lit 8878712049193008702160896

noncomputable def ep579 := nat_lit 19027440162393514290922172123136906900799488

noncomputable def ep580 := @Enclosure.Real.IsNear.mulLit_ff qz186 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz166 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 632879037 2147483648 15415354745 30399778521088 146785684097

noncomputable abbrev qz365 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz410 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable abbrev qz188 := (Real.cos qz365)

noncomputable abbrev qz189 := (@Neg.neg Real Real.instNeg (Real.sin qz365))

noncomputable def ep581 := @Enclosure.Complex.IsNear.of_eq qz165 (Complex.mk (@HMul.hMul Real Real Real qz0 qz115 qz188) (@HMul.hMul Real Real Real qz0 qz115 qz189)) Bool.false 632879037 2147483648 15415354745 30399778521088 Bool.false 3355412787 17179869184 30700300879 60799557042176 (BSN.cpow_neg_s_mk qz145 38999 1000 8 qz146 rfl)

noncomputable def ep582 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz120 38999 1000 0 1 9364972152248037 4503599627370496 125000000010617 3539000000000000000 365224548965521194963 4503599627370496000 4874875000414052383 3539000000000000000000 qz180 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 125000000010617 3539000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz119) Bool.false 4909942519757818822656 2361183241434822606848 1000000000084936 28312000000000000000 9364972152248037 4503599627370496 125000000010617 3539000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 65536 24973259072661432 36028797018963968 28312 1000000000000000 rfl rfl rfl rfl (ep295 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep583 := nat_lit 4898134231349060902396792492916496

noncomputable def ep584 := BSN.sin_dyadic_bound_f 264549942 268435456 2 1 131072 56680 ep583 ep208 ep583 ep583 ep209 ep583 109256 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 264549942) qz293 0 1 ep583 ep208 ep583 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 264549942) qz294 0 1 ep583 ep209 ep583 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz190 := qz365

noncomputable abbrev qz366 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10629433) qz12)

noncomputable def ep585 := @Enclosure.Real.IsNear.cos_image qz190 qz366 Bool.false 10629433 131072 181 131072 Bool.false 109256 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz190 Bool.false 365224548965521194963 4503599627370496000 4874875000414052383 3539000000000000000000 10629433 131072 181 131072 (ep582 rfl) rfl) (Enclosure.sfrac_false_div 10629433 131072) (BSN.cos_reduce3 qz366 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18616047220230314786816) qz66) 226375608064910080 72057594037927936 Bool.false 109256 131072 12 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q3 10629433 131072 226375608064910080 72057594037927936 12 18616047220230314786816 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 109256 131072 18616047220230314786816 18889465931478580854784 264549942 268435456 56680 56624 (ep584 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep586 := nat_lit 42750704248902574442773105193359232206490746532478498752596079642992896

noncomputable def ep587 := nat_lit 23991718948313455670588802021898291259475117691313671528336028918016

noncomputable def ep588 := nat_lit 128204129308811096416978137976033900036953289362052868914731566871142656

noncomputable def ep589 := BSN.cos_dyadic_bound_f 264549942 268435456 3 2 131072 56680 ep586 ep213 ep587 ep588 ep216 ep587 72407 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 264549942) qz305 0 2 ep586 ep213 ep587 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 264549942) qz306 0 2 ep588 ep216 ep587 rfl rfl rfl rfl) rfl rfl

noncomputable def ep590 := @Enclosure.Real.IsNear.sin_image qz190 qz366 Bool.false 10629433 131072 181 131072 Bool.true 72407 131072 1 28312 (@Enclosure.Real.IsNear.recentre' qz190 Bool.false 365224548965521194963 4503599627370496000 4874875000414052383 3539000000000000000000 10629433 131072 181 131072 (ep582 rfl) rfl) (Enclosure.sfrac_false_div 10629433 131072) (BSN.sin_reduce3 qz366 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18616047220230314786816) qz66) 226375608064910080 72057594037927936 Bool.false 72407 131072 12 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q3 10629433 131072 226375608064910080 72057594037927936 12 18616047220230314786816 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 72407 131072 18616047220230314786816 18889465931478580854784 264549942 268435456 56680 56624 (ep589 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz191 := (Real.sin qz365)

noncomputable def ep591 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz115 qz188) (@HMul.hMul Real Real Real qz0 qz115 qz189) Bool.false 632879037 2147483648 15415354745 30399778521088 Bool.false 3355412787 17179869184 30700300879 60799557042176 (@Enclosure.Real.IsNear.mulLit_ff qz115 qz188 46341 131072 1 131072 13657 16384 656943 463863808 632879037 2147483648 15415354745 30399778521088 qz330 (@Enclosure.Real.IsNear.recentre' qz188 Bool.false 109256 131072 5255544 3710910464 13657 16384 656943 463863808 (ep585 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz115 qz189 46341 131072 1 131072 72407 131072 656943 463863808 3355412787 17179869184 30700300879 60799557042176 qz330 (@Enclosure.Real.IsNear.neg qz191 Bool.true 72407 131072 656943 463863808 (@Enclosure.Real.IsNear.recentre' qz191 Bool.true 72407 131072 5255544 3710910464 72407 131072 656943 463863808 (ep590 rfl rfl) rfl)) rfl)

noncomputable def ep592 := @ep580 292065024192 0 1 30965860798898524863 209068287868348137472 2262753391842759990265 ep578 (@Enclosure.Complex.IsNear.re_isNear qz165 Bool.false 632879037 2147483648 15415354745 30399778521088 Bool.false 3355412787 17179869184 30700300879 60799557042176 (ep581 ep591))

noncomputable def ep593 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz166 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 146785684097 292065024192 0 1 Bool.false

noncomputable def ep594 := @Enclosure.Complex.IsNear.addLitP qz166 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) Bool.false 1513172001 3042344002 0 1 Bool.true 311992000

noncomputable def ep595 := @ep594 1521172001 0 1 Bool.false 1 192 0 1 Bool.false 38999 96000 0 1 Bool.false 293571368194 146785684097 292065024192 0 1 Bool.false 29372954866999 29372954866999 146032512096000 0 1

noncomputable abbrev qz192 := (@HDiv.hDiv Complex Complex Complex qz265 qz298 (@HSub.hSub Complex Complex Complex qz255 qz336 (1 : Complex)))

noncomputable def ep596 := @Enclosure.Complex.IsNear.addLitP qz192 qz40 Bool.true 16000000 6084688004 0 1 Bool.true 1247968000 6084688004 0 1

noncomputable def ep597 := @Enclosure.Complex.IsNear.of_eq qz192 (Complex.mk (Enclosure.sfrac Bool.true 16000000 6084688004) (Enclosure.sfrac Bool.true 1247968000 6084688004)) Bool.true 16000000 6084688004 0 1 Bool.true 1247968000 6084688004 0 1

noncomputable def ep598 := @ep596 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 6052688004 1513172001 3042344002 0 1 Bool.true 1247968000 311992000 1521172001 0 1 (ep597 (BSN.N_div_s_sub_one_mk qz145 38999 1000 8 qz146 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 16000000 6084688004) (Enclosure.sfrac Bool.true 1247968000 6084688004) Bool.true 16000000 6084688004 0 1 Bool.true 1247968000 6084688004 0 1 (Enclosure.Real.IsNear.const Bool.true 16000000 6084688004) (Enclosure.Real.IsNear.const Bool.true 1247968000 6084688004))) qz42 rfl

noncomputable def ep599 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) qz125)) Bool.false 1 192 0 1

noncomputable def ep600 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) qz125) Bool.false 0 1 0 1 Bool.false

noncomputable def ep601 := @ep600 0 1 0 1 Bool.false 1 192 0 1 Bool.false 38999 96000 0 1 Bool.false 1 1 192 0 1 Bool.false 38999 38999 96000 0

noncomputable def ep602 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (Complex.mk qz43 qz43) Bool.false 0 1 0 1 Bool.false

noncomputable def ep603 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) qz125 Bool.false 1 192 0 1 Bool.false 38999 96000 0 1

noncomputable def ep604 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127) 1 192 0 1 0 1 0

noncomputable def ep605 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126 1 24 0 1 1 8 0 1 1

noncomputable def ep606 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep607 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep608 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)) qz133 Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 (BSN.ascPochhammer_one_eval qz133)

noncomputable def ep609 := ep608 (@Enclosure.Complex.IsNear.of_eq qz133 (Complex.mk qz32 qz145) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 (BSN.s_crit_mk qz145 Bool.false 38999 1000 qz146) (@Enclosure.Complex.IsNear.mk qz32 qz145 Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 qz33 qz180))

noncomputable def ep610 := @ep607 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep609)

noncomputable def ep611 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 38999 1000 0 1 0 1 0

noncomputable def ep612 := @ep611 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep609)

noncomputable def ep613 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)))) 38999 12000 0 1 0 1 0 1 38999

noncomputable def ep614 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 38999 1000 0 1 38999 12000 0

noncomputable def ep615 := @ep614 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep609)

noncomputable def ep616 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep617 := @ep616 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep323) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep609)

noncomputable def ep618 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 38999 12000 0 1 (@ep606 1 24 0 1 (ep610 rfl) (ep612 rfl) rfl rfl) (@ep613 38999 12000 0 1 (ep615 rfl) (ep617 rfl) rfl rfl)

noncomputable def ep619 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 38999 12000 0 1 ep618

noncomputable def ep620 := @ep605 192 0 1 ep619 qz128

noncomputable def ep621 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127 38999 12000 0 1 0 1 0 1 0

noncomputable def ep622 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 38999 12000 0 1 ep618

noncomputable def ep623 := @ep621 1 0 1 ep622 qz129

noncomputable def ep624 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126) 0 1 0 1 38999 96000 0

noncomputable def ep625 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127 1 24 0 1 0 1 0 1 0

noncomputable def ep626 := @ep625 1 0 1 ep619 qz129

noncomputable def ep627 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz45)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126 38999 12000 0 1 1 8 0 1 38999

noncomputable def ep628 := @ep627 96000 0 1 ep622 qz128

noncomputable def ep629 := @ep601 1 (@ep602 0 1 0 1 (BSN.bern_sum_base qz133 8) qz60) (ep603 (@ep604 1 1 1 192 0 1 (ep620 rfl) (ep623 rfl) rfl rfl) (@ep624 1 38999 38999 96000 0 1 (ep626 rfl) (ep628 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep630 := ep595 (ep598 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep599 Bool.false 38999 96000 0 1 (BSN.bern_sum_succ qz133 8 0 1 1 rfl rfl) (ep629 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep631 := @Enclosure.Real.IsNear.mulLit_ff qz187 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz166 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 3355412787 17179869184 30700300879 60799557042176 29372954866999

noncomputable def ep632 := @ep631 146032512096000 0 1 32852796117567442972071 836273151473392549888000 901758552122156727792121 ep386 (@Enclosure.Complex.IsNear.im_isNear qz165 Bool.false 632879037 2147483648 15415354745 30399778521088 Bool.false 3355412787 17179869184 30700300879 60799557042176 (ep581 ep591))

noncomputable def ep633 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz166 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 146785684097 292065024192 0 1 Bool.false

noncomputable def ep634 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz186 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz166 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz187 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz166 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 6196509130023596733321 104534143934174068736000 90558903836732775712051

noncomputable def ep635 := nat_lit 17757424098386017404321792

noncomputable def ep636 := nat_lit 27525895922399041310569003130905145792004096

noncomputable def ep637 := @Enclosure.Real.IsNear.mulLit_ff qz186 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz166 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 632879037 2147483648 15415354745 30399778521088 29372954866999

noncomputable def ep638 := @ep637 146032512096000 0 1 6196509130023596733321 104534143934174068736000 90558903836732775712051 ep501 (@Enclosure.Complex.IsNear.re_isNear qz165 Bool.false 632879037 2147483648 15415354745 30399778521088 Bool.false 3355412787 17179869184 30700300879 60799557042176 (ep581 ep591))

noncomputable def ep639 := @Enclosure.Real.IsNear.mulLit_ff qz187 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz166 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz72 qz73 (@HSub.hSub Nat Nat Nat qz71 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 3355412787 17179869184 30700300879 60799557042176 146785684097

noncomputable def ep640 := @ep639 292065024192 0 1 164175520455872116113 1672546302946785099776 4506364666507745421263 ep635 (@Enclosure.Complex.IsNear.im_isNear qz165 Bool.false 632879037 2147483648 15415354745 30399778521088 Bool.false 3355412787 17179869184 30700300879 60799557042176 (ep581 ep591))

noncomputable abbrev qz367 := (ep630 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep641 := @ep576 32914958317031207980767 209068287868348137472000 315877137162120046775201 ep501 (@ep577 ep578 32852796117567442972071 836273151473392549888000 901758552122156727792121 ep386 ep579 91010647078026656479929 836273151473392549888000 ep504 ep386 (ep592 (@ep593 29372954866999 146032512096000 0 1 qz367) rfl) (ep632 (@ep633 29372954866999 146032512096000 0 1 qz367) rfl) rfl rfl) (@ep634 ep501 164175520455872116113 1672546302946785099776 4506364666507745421263 ep635 ep636 32914958317031207980767 209068287868348137472000 315877137162120046775201 ep501 (ep638 (@ep633 29372954866999 146032512096000 0 1 qz367) rfl) (ep640 (@ep593 29372954866999 146032512096000 0 1 qz367) rfl) rfl rfl)

noncomputable def ep642 := @ep507 ep500 ep501 (@ep508 7599944630272 (BSN.head_sum_c_eq qz133 8) (ep509 (BSN.head_sum_c_succ qz133 7 8 rfl rfl) (ep575 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep641 rfl rfl rfl

noncomputable def ep643 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz133 1 8) Bool.false ep384 836273151473392549888000 ep385 ep386 Bool.true 23554863487515751091233 209068287868348137472000 ep500 ep501 (@ep502 ep386 Bool.true 23554863487515751091233 209068287868348137472000 ep500 ep501 (BSN.zetaApproximant_eq_folded' qz133 1 8 rfl) (ep642 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))))) qz132)) (Complex.im (zetaApproximant qz133 1 8)) 15 65536 202837

noncomputable def ep645 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))))) qz132)) Bool.false 30 131072 1622696

noncomputable def ep646 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))))) qz132) qz337 Bool.false 514711 32768 55

noncomputable def ep647 := nat_lit 276581650772887381598090427078300865388136105625161486114426382173775681

noncomputable def ep648 := nat_lit 827748775430651280799637520961994207085645655769002084326814309727250241

noncomputable def ep649 := BSN.cos_dyadic_bound_f 421595657 268435456 3 2 131072 56680 ep647 ep213 ep496 ep648 ep216 ep496 30 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 421595657) qz305 0 2 ep647 ep213 ep496 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 421595657) qz306 0 2 ep648 ep216 ep496 rfl rfl rfl rfl) rfl rfl

noncomputable def ep650 := @ep646 65536 Bool.false 30 131072 1 28312 (@ep389 514711 32768 55 65536 ep494 rfl) (Enclosure.sfrac_false_div 514711 32768) (BSN.sin_reduce1 qz337 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7416789244073090220032) qz354) 226375608064910080 72057594037927936 Bool.false 30 131072 2 1000000000000000 56624 28312 (BSN.sin_reduce_arg_pos_rat_q1 514711 32768 226375608064910080 72057594037927936 2 7416789244073090220032 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 30 131072 7416789244073090220032 4722366482869645213696 421595657 268435456 56680 56624 (ep649 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep651 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz133 1 8) Bool.false ep384 836273151473392549888000 ep385 ep386 Bool.true 23554863487515751091233 209068287868348137472000 ep500 ep501 (@ep502 ep386 Bool.true 23554863487515751091233 209068287868348137472000 ep500 ep501 (BSN.zetaApproximant_eq_folded' qz133 1 8 rfl) (ep642 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow06.d9 : Enclosure.Real.IsNear (hardyZApproximantEM 1 8 qz145) Bool.true ep369 ep370 ep371 ep372 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 8 qz145) ep373 Bool.true ep369 ep370 ep371 ep372 (@Eq.refl Real ep373) (@ep374 Bool.true ep369 ep370 ep371 ep372 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz130 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz131 (@Nat.cast Complex Complex.instNatCast j))))) qz132) (zetaApproximant qz133 1 8)) (@ep376 ep370 ep377 ep378 70664590462547253273699 ep379 ep380 ep381 ep382 ep369 ep370 ep371 ep372 (@ep383 231931904 ep384 836273151473392549888000 ep385 ep386 ep375 ep370 ep377 ep378 (@ep387 1855455232 131071 131072 202837 231931904 (ep499 rfl rfl) rfl) ep643 rfl) (@ep644 231931904 23554863487515751091233 209068287868348137472000 ep500 ep501 70664590462547253273699 ep379 ep380 ep381 (@ep645 1855455232 15 65536 202837 231931904 (ep650 rfl rfl) rfl) ep651 rfl) rfl rfl))

theorem EMRow06.d10 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow06.d11 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow06.d12 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow06.d13 : @Eq Nat (Nat.pow 8 (Nat.succ (Nat.mul 2 3))) 2097152 := @Eq.refl Nat 2097152

noncomputable abbrev qz413 := (@HAdd.hAdd Complex Complex Complex qz416 qz420 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz368 := qz413

noncomputable abbrev qz193 := (@HDiv.hDiv Real Real Real qz252 (@Norm.norm Complex Complex.instNorm qz368) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz260) qz308))

noncomputable abbrev qz194 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz195 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz369 := (@HPow.hPow Complex Complex Complex qz403 qz405 (@HSub.hSub Complex Complex Complex qz393 qz404 qz406))

noncomputable abbrev qz196 := qz369

noncomputable def ep652 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 qz193 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) 48523377 1073741824 2264785 28991029248 53840778504929 123145302310912 179693071

noncomputable def ep653 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 8)) 123 8192 1 221184 394499 131072 563 131072 48523377 1073741824

noncomputable abbrev qz370 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz371 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz197 := (@HPow.hPow Real Nat Real qz370 qz371 2)

noncomputable def ep654 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz197) 96 162 0 1 3321 131072 1 131072 123 8192 1 221184

noncomputable def ep655 := nat_lit 781950621441006189802102638025

noncomputable def ep656 := nat_lit 19807040628566084398385987584

noncomputable def ep657 := nat_lit 26986075409044041160201671

noncomputable def ep658 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz198 := qz371

noncomputable abbrev qz372 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz198 1)

noncomputable def ep659 := @Enclosure.Real.IsNear.mulLit_ff qz372 qz198 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep655 ep656 ep657 ep658

noncomputable def ep660 := ep659 (@Enclosure.Real.IsNear.of_eq qz372 qz198 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz198) (@Enclosure.Real.IsNear.of_eq qz198 qz250 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz251)) (@Enclosure.Real.IsNear.of_eq qz198 qz250 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz251) rfl

noncomputable def ep661 := @Enclosure.Real.IsNear.inv_image qz197 ep655 ep656 ep657 ep658 1660 1661 65536 (@Enclosure.Real.IsNear.of_eq qz197 (@HMul.hMul Real Real Real qz0 qz372 qz198) Bool.false ep655 ep656 ep657 ep658 (BSN.pow_succ_r qz198 1 2 rfl) ep660) rfl rfl rfl

noncomputable def ep662 := ep654 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz197) Bool.false 3321 131072 1 131072 3321 131072 1 131072 (ep661 rfl rfl rfl) rfl)

noncomputable def ep663 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 8)) (Real.sqrt (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 8)) (Complex.re (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 8)) (Complex.im (zetaApproximant qz11 1 8))))) Bool.false 394499 131072 563 131072

noncomputable def ep664 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 8)) (Complex.re (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 8)) (Complex.im (zetaApproximant qz11 1 8))))) Bool.false 394499 131072 563 131072

noncomputable def ep665 := nat_lit 3444655192087197702515255417668506758629

noncomputable def ep666 := nat_lit 380254949737275139722992383164416000000

noncomputable def ep667 := nat_lit 154666124045912704206575220574153755976487038995292367

noncomputable def ep668 := nat_lit 5991991868617581960303176818007037616138699669504000000

noncomputable def ep669 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 8)) (Complex.re (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 8)) (Complex.im (zetaApproximant qz11 1 8)))) ep665 ep666 ep667 ep668 196968 197531

noncomputable def ep670 := nat_lit 1083427601040065380626561838303712415294101804689

noncomputable def ep671 := nat_lit 119605210223560285465272021540924351840256000000

noncomputable def ep672 := nat_lit 2398291388551569143686526149217814653622399807856707

noncomputable def ep673 := nat_lit 93624872947149718129737137781359962752167182336000000

noncomputable def ep674 := nat_lit 8415583203802410221475857034225509753587249

noncomputable def ep675 := nat_lit 19136833635769645674443523446547896294440960000

noncomputable def ep676 := nat_lit 1175475178612279010637547024213618144653451292463119

noncomputable def ep677 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 8)) (Complex.re (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 8)) (Complex.im (zetaApproximant qz11 1 8))) ep670 ep671 ep672 ep673 ep674 ep675 ep676

noncomputable def ep678 := nat_lit 20734380305102984175543120307945708343475817794083582487126301240997630335300612660857405440000

noncomputable def ep679 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz11 1 8)) (Complex.re (zetaApproximant qz11 1 8)) 1040878283489508383463383 345839862108982870016000 650601004843286115901059 ep53 1040878283489508383463383 345839862108982870016000 650601004843286115901059 ep53 ep670

noncomputable def ep680 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz11 1 8)) (Complex.im (zetaApproximant qz11 1 8)) 2900962461632761324807 138335944843593148006400 ep183 ep184 2900962461632761324807 138335944843593148006400 ep183 ep184 ep674

noncomputable def ep681 := @ep652 123145302310912 63786521647273811640320 59405827566305 123145302310912 264595374997 3324923162394624 (@ep653 2264785 28991029248 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz197)) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow06.d10 EMRow06.d11 rfl) (ep662 rfl)) (ep663 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz11 1 8)) (@ep664 394499 131072 563 131072 (@ep669 65536 (@ep677 ep668 ep678 ep665 ep666 ep667 ep668 (@ep679 ep671 ep672 ep673 ep360 ep360 rfl) (@ep680 ep675 ep676 ep668 ep368 ep368 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz199 := (@Norm.norm Complex Complex.instNorm qz368)

noncomputable abbrev qz373 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep682 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz193 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz199 qz373) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) Bool.false 53840778504929 123145302310912 179693071 123145302310912 (BSN.zrb_shape_eq qz199 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) qz36 3)

noncomputable def ep683 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz199 qz373) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) 4671311 458752 1 458752 11525839 268435456 9 67108864

noncomputable def ep684 := @Enclosure.Real.IsNear.mulLit_ff qz199 qz373 4671311 131072 1 131072 2 7 0 1 4671311 458752

noncomputable abbrev qz374 := (Complex.re qz413)

noncomputable abbrev qz375 := (Complex.im qz413)

noncomputable abbrev qz200 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz249 qz374 qz374) (@HMul.hMul Real Real Real qz249 qz375 qz375))

noncomputable abbrev qz201 := qz368

noncomputable def ep685 := @Enclosure.Real.IsNear.of_eq qz199 (Real.sqrt qz200) Bool.false 4671311 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz201)

noncomputable def ep686 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz200) Bool.false 4671311 131072 1 131072 4671311

noncomputable def ep687 := @Enclosure.Real.IsNear.sqrt_image qz200 1270158089 1000000 0 1 2335655 2335656 65536

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz249 qz374 qz374)

noncomputable abbrev qz203 := (@HMul.hMul Real Real Real qz249 qz375 qz375)

noncomputable def ep688 := @Enclosure.Real.IsNear.addLit_ff qz202 qz203 49 4 0 1 1257908089 1000000 0 1

noncomputable abbrev qz204 := qz374

noncomputable def ep689 := @Enclosure.Real.IsNear.mulLit_ff qz204 qz204 7 2 0 1 7 2 0 1 49 4

noncomputable def ep690 := @Enclosure.Complex.IsNear.of_eq qz201 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz36) Bool.false 7 2 0 1 Bool.false 35467 1000 0 1 (BSN.s_add_nat_mk qz36 Bool.false 35467 1000 3 qz37)

noncomputable abbrev qz205 := (ep690 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz259 Bool.false 7 2 0 1 Bool.false 35467 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz302))

noncomputable def ep691 := @ep689 0 1 (@Enclosure.Complex.IsNear.re_isNear qz201 Bool.false 7 2 0 1 Bool.false 35467 1000 0 1 qz205)

noncomputable def ep692 := ep691 (@Enclosure.Complex.IsNear.re_isNear qz201 Bool.false 7 2 0 1 Bool.false 35467 1000 0 1 qz205)

noncomputable abbrev qz206 := qz375

noncomputable def ep693 := @Enclosure.Real.IsNear.mulLit_ff qz206 qz206 35467 1000 0 1 35467 1000 0 1 1257908089 1000000

noncomputable def ep694 := @ep693 0 1 (@Enclosure.Complex.IsNear.im_isNear qz201 Bool.false 7 2 0 1 Bool.false 35467 1000 0 1 qz205)

noncomputable def ep695 := ep694 (@Enclosure.Complex.IsNear.im_isNear qz201 Bool.false 7 2 0 1 Bool.false 35467 1000 0 1 qz205)

noncomputable def ep696 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Real.sqrt (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))))) Bool.false 11525839 268435456

noncomputable def ep697 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))))) Bool.false 23051678 536870912

noncomputable def ep698 := nat_lit 15879609206986983153587397494060641207044963776637925409

noncomputable def ep699 := nat_lit 8613397412686254856416669750616632852480000000000000000000

noncomputable def ep700 := nat_lit 9829355532183403117031487761295340788762452738380707431

noncomputable def ep701 := nat_lit 863029414212277322884340520333302248881405296640000000000000000

noncomputable def ep702 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)))) ep698 ep699 ep700 ep701

noncomputable def ep703 := nat_lit 19798206646230741931037564208625799290252261607517433801

noncomputable def ep704 := nat_lit 10766746765857818570520837188270791065600000000000000000000

noncomputable def ep705 := nat_lit 1513183520973324415876468250538296547017582448180335185823

noncomputable def ep706 := nat_lit 134848345970668331700678206302078476387719577600000000000000000000

noncomputable def ep707 := nat_lit 22802161112438671531858959533334319357308050346654649

noncomputable def ep708 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) ep703 ep704 ep705 ep706 ep707

noncomputable def ep709 := nat_lit 4785220784825697142453705417009240473600000000000000000000

noncomputable def ep710 := nat_lit 10068124857925476070978538739600200545133685418511266787

noncomputable def ep711 := nat_lit 59932598209185925200301425023145989505653145600000000000000000000

noncomputable def ep712 := nat_lit 94984295040229522186868727234209452041635083356501623124522817718653321256870274499375792128000000000000000000000

noncomputable def ep713 := nat_lit 4449517574550160368322088099

noncomputable def ep714 := nat_lit 103762935414616227840000000000

noncomputable def ep715 := nat_lit 48047130514580859440297651

noncomputable def ep716 := nat_lit 367217028432326830325760000000000

noncomputable def ep717 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) ep713 ep714 ep715 ep716 ep713 ep714 ep715

noncomputable def ep718 := nat_lit 151003844694228469607388907

noncomputable def ep719 := nat_lit 69175290276410818560000000000

noncomputable def ep720 := nat_lit 9419898035098283059719073

noncomputable def ep721 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196) Bool.true ep713 ep714 ep715 ep716 Bool.false ep718 ep719 ep720

noncomputable def ep722 := nat_lit 244811352288217886883840000000000

noncomputable def ep723 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196 Bool.true ep713 ep714 ep715 ep716 Bool.false ep718 ep719 ep720 ep722

noncomputable def ep724 := nat_lit 46116860184273879040000000

noncomputable def ep725 := nat_lit 163207568192145257922560000000

noncomputable def ep726 := nat_lit 4406831226806129076475004849

noncomputable def ep727 := nat_lit 47009954592701745727119401

noncomputable abbrev qz207 := (Complex.re qz369)

noncomputable abbrev qz208 := (Complex.im qz369)

noncomputable def ep728 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz207) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz208) 18971710108458351932037 ep724 460967076390717205857 ep725 ep726 ep714 ep727

noncomputable def ep729 := nat_lit 205197779872999172002468605894035450115349544960000000

noncomputable def ep730 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz207 3772474267 480000000 0 1 15086949915933 288230376151711744 366576716313 1020047301200907862016 18971710108458351932037

noncomputable def ep731 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) 3772474267 480000000 0 1 0 1 0 1 3772474267

noncomputable def ep732 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 11317422801 2000000 0 1 3772474267 480000000 0

noncomputable def ep733 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz43) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow06.d12 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz43 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz44)

noncomputable abbrev qz376 := (@HAdd.hAdd Complex Complex Complex qz395 qz398 qz407)

noncomputable abbrev qz209 := qz376

noncomputable def ep734 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) qz209) Bool.true 11317422801 2000000 0 1 Bool.true 44410290942563 1000000000 0 1

noncomputable abbrev qz210 := (Complex.re qz376)

noncomputable abbrev qz211 := (Complex.im qz376)

noncomputable def ep735 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz210) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz211) 1257158089 400000 0 1 1257908089 500000 0 1

noncomputable def ep736 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz210 1257158089 1000000 0 1 5 2 0 1 1257158089 400000

noncomputable abbrev qz377 := (@HAdd.hAdd Complex Complex Complex qz395 qz398 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz212 := qz377

noncomputable def ep737 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz212) Bool.true 1257158089 1000000 0 1 Bool.false 35467 500 0 1

noncomputable abbrev qz213 := (Complex.re qz377)

noncomputable abbrev qz214 := (Complex.im qz377)

noncomputable def ep738 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz213) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz214) 3 4 0 1 1257908089 1000000 0 1

noncomputable def ep739 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz213 1 2 0 1 3 2 0 1 3 4

noncomputable def ep740 := @ep739 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep325)

noncomputable def ep741 := @Enclosure.Complex.IsNear.of_eq qz212 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz36) Bool.false 3 2 0 1 Bool.false 35467 1000 0 1 (BSN.s_add_nat_mk qz36 Bool.false 35467 1000 1 qz37)

noncomputable abbrev qz215 := (ep741 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz259 Bool.false 3 2 0 1 Bool.false 35467 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz302))

noncomputable def ep742 := ep740 (@Enclosure.Complex.IsNear.re_isNear qz212 Bool.false 3 2 0 1 Bool.false 35467 1000 0 1 qz215)

noncomputable def ep743 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz214 35467 1000 0 1 35467 1000 0 1 1257908089 1000000

noncomputable def ep744 := @ep743 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep325)

noncomputable def ep745 := ep744 (@Enclosure.Complex.IsNear.im_isNear qz212 Bool.false 3 2 0 1 Bool.false 35467 1000 0 1 qz215)

noncomputable def ep746 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz212 Bool.true 1257158089 1000000 0 1 Bool.false 35467 500 0 1 (@ep738 5028632356 1257158089 1000000 0 1 (ep742 rfl) (ep745 rfl) rfl rfl)

noncomputable def ep747 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz214) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz213) 35467 2000 0 1 106401 2000 0 1

noncomputable def ep748 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz214 1 2 0 1 35467 1000 0 1 35467 2000

noncomputable def ep749 := @ep748 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep325)

noncomputable def ep750 := ep749 (@Enclosure.Complex.IsNear.im_isNear qz212 Bool.false 3 2 0 1 Bool.false 35467 1000 0 1 qz215)

noncomputable def ep751 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz213 35467 1000 0 1 3 2 0 1 106401 2000

noncomputable def ep752 := @ep751 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep325)

noncomputable def ep753 := ep752 (@Enclosure.Complex.IsNear.re_isNear qz212 Bool.false 3 2 0 1 Bool.false 35467 1000 0 1 qz215)

noncomputable abbrev qz216 := (ep737 (BSN.ascPochhammer_succ_eval_c 1 2 qz260 rfl) (ep746 (@ep747 283736000 35467 500 0 1 (ep750 rfl) (ep753 rfl) rfl rfl)))

noncomputable def ep754 := @ep736 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1257158089 1000000 0 1 Bool.false 35467 500 0 1 qz216)

noncomputable def ep755 := @Enclosure.Complex.IsNear.of_eq qz209 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz36) Bool.false 5 2 0 1 Bool.false 35467 1000 0 1 (BSN.s_add_nat_mk qz36 Bool.false 35467 1000 2 qz37)

noncomputable abbrev qz217 := (ep755 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz259 Bool.false 5 2 0 1 Bool.false 35467 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz302))

noncomputable def ep756 := ep754 (@Enclosure.Complex.IsNear.re_isNear qz209 Bool.false 5 2 0 1 Bool.false 35467 1000 0 1 qz217)

noncomputable def ep757 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz211 35467 500 0 1 35467 1000 0 1 1257908089 500000

noncomputable def ep758 := @ep757 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1257158089 1000000 0 1 Bool.false 35467 500 0 1 qz216)

noncomputable def ep759 := ep758 (@Enclosure.Complex.IsNear.im_isNear qz209 Bool.false 5 2 0 1 Bool.false 35467 1000 0 1 qz217)

noncomputable def ep760 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) qz209 Bool.true 11317422801 2000000 0 1 Bool.true 44410290942563 1000000000 0 1 (@ep735 1131742280100000 11317422801 2000000 0 1 (ep756 rfl) (ep759 rfl) rfl rfl)

noncomputable def ep761 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz211) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz210) 44587625942563 1000000000 0 1 35467 200 0 1

noncomputable def ep762 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz211 1257158089 1000000 0 1 35467 1000 0 1 44587625942563 1000000000

noncomputable def ep763 := @ep762 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1257158089 1000000 0 1 Bool.false 35467 500 0 1 qz216)

noncomputable def ep764 := ep763 (@Enclosure.Complex.IsNear.im_isNear qz209 Bool.false 5 2 0 1 Bool.false 35467 1000 0 1 qz217)

noncomputable def ep765 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz210 35467 500 0 1 5 2 0 1 35467 200

noncomputable def ep766 := @ep765 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1257158089 1000000 0 1 Bool.false 35467 500 0 1 qz216)

noncomputable def ep767 := ep766 (@Enclosure.Complex.IsNear.re_isNear qz209 Bool.false 5 2 0 1 Bool.false 35467 1000 0 1 qz217)

noncomputable abbrev qz218 := (ep734 (BSN.ascPochhammer_succ_eval_c 2 3 qz260 rfl) (ep760 (@ep761 8882058188512600 44410290942563 1000000000 0 1 (ep764 rfl) (ep767 rfl) rfl rfl)))

noncomputable def ep768 := @ep732 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep733) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 11317422801 2000000 0 1 Bool.true 44410290942563 1000000000 0 1 qz218)

noncomputable def ep769 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 44410290942563 1000000000 0 1 0 1 0

noncomputable def ep770 := @ep769 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep733) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 11317422801 2000000 0 1 Bool.true 44410290942563 1000000000 0 1 qz218)

noncomputable def ep771 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) 44410290942563 720000000000 0 1 0 1 0 1 44410290942563

noncomputable def ep772 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 44410290942563 1000000000 0 1 44410290942563 720000000000 0

noncomputable def ep773 := @ep772 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep733) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 11317422801 2000000 0 1 Bool.true 44410290942563 1000000000 0 1 qz218)

noncomputable def ep774 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 11317422801 2000000 0 1 0 1 0

noncomputable def ep775 := @ep774 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep733) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 11317422801 2000000 0 1 Bool.true 44410290942563 1000000000 0 1 qz218)

noncomputable def ep776 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 3772474267 480000000 0 1 Bool.false 44410290942563 720000000000 0 1 (@ep731 3772474267 480000000 0 1 (ep768 rfl) (ep770 rfl) rfl rfl) (@ep771 44410290942563 720000000000 0 1 (ep773 rfl) (ep775 rfl) rfl rfl)

noncomputable def ep777 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 3772474267 480000000 0 1 Bool.false 44410290942563 720000000000 0 1 ep776

noncomputable def ep778 := @Enclosure.Complex.IsNear.re_isNear qz196 Bool.true 15086949915933 288230376151711744 366576716313 1020047301200907862016 Bool.false 99229956239323 144115188075855872 1058537415427 510023650600453931008

noncomputable abbrev qz219 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2097152)))

noncomputable def ep779 := @Enclosure.Complex.IsNear.of_eq qz196 (Complex.mk (@HMul.hMul Real Real Real qz0 qz219 qz116) (@HMul.hMul Real Real Real qz0 qz219 qz117)) Bool.true 15086949915933 288230376151711744 366576716313 1020047301200907862016 Bool.false 99229956239323 144115188075855872 1058537415427

noncomputable abbrev qz220 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2097152))

noncomputable abbrev qz221 := (@Nat.cast Real Real.instNatCast 2097152)

noncomputable def ep780 := @Enclosure.Real.IsNear.inv_image qz220 777472127993 536870912 1 536870912 185363 185364 268435456 (@Enclosure.Real.IsNear.of_eq qz220 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz221 qz89)) Bool.false 777472127993 536870912 1 536870912 (BSN.sqrt_natCast_div_one 2097152) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz221 qz89)) Bool.false 777472127993 536870912 1 536870912 777472127993 536870912 1 536870912 (BSN.sqrt_enclosure 2097152 1 388736063996 388736063997 268435456 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep781 := nat_lit 20111124560928025897598976

noncomputable def ep782 := nat_lit 9671406556917033397649408

noncomputable def ep783 := BSN.log_dyadic_bound 0 16 1 0 1 268435456 115965952 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep784 := @Enclosure.Real.IsNear.mulLit_ff qz36 qz120 35467 1000 0 1 9364972152248037 4503599627370496 15258794371 1769500000000000000 332147467323781128279 4503599627370496000 541183659956257 1769500000000000000000 qz91 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 15258794371 1769500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz119) Bool.false ep781 ep782 1000000347897856 115965952000000000000000 9364972152248037 4503599627370496 15258794371 1769500000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 268435456 24973259072661432 36028797018963968 115965952 1000000000000000 rfl rfl rfl rfl (ep783 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep785 := nat_lit 115663997117360643663462400

noncomputable def ep786 := nat_lit 77371252455336267181195264

noncomputable def ep787 := nat_lit 312095576673376184640575972950134389775735299847028589358806224129044485360078783778135042914858745609600842771278475351132646538165970583452882598629376

noncomputable def ep788 := nat_lit 1495322550399040784419355283626494329519667708093549445215377558311688463489449843662618815857177555772710955730243566617516213067140175522969484368281600

noncomputable def ep789 := nat_lit 388884606442292932799566752705714971390038508886557302180634442085593730651550687269094151755711876905608812872428104788986956217182644846827933696

noncomputable def ep790 := nat_lit 1889636567883988658705080175859535960953102494238065616847348070243762275356952358423976004171397976290895722154342003443221218888738991351521665670451200

noncomputable def ep791 := nat_lit 136074352086312711382161330810010983986289761436512999514599357806363650177539935773298312243003157575316696971452164562193975389109755972590223077513625600

noncomputable def ep792 := BSN.cos_dyadic_bound_f 1643684258814 1099511627776 4 3 536870912 232158401 ep787 ep788 ep789 ep790 ep791 ep789 40695579 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1643684258814) (BSN.cosEvenQ 1099511627776) 0 3 ep787 ep788 ep789 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1643684258814) (BSN.cosOddQ 1099511627776) 0 3 ep790 ep791 ep789 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz378 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39595063605) (@Nat.cast Real Real.instNatCast 536870912))

noncomputable def ep793 := @Enclosure.Real.IsNear.cos_image qz121 qz378 Bool.false 39595063605 536870912 165 536870912 Bool.true 40695579 536870912 1 115965952 (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 332147467323781128279 4503599627370496000 541183659956257 1769500000000000000000 39595063605 536870912 165 536870912 (ep784 rfl) rfl) (Enclosure.sfrac_false_div 39595063605 536870912) (BSN.cos_reduce2 qz378 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep785) (@Nat.cast Real Real.instNatCast ep786)) 226375608064910080 72057594037927936 Bool.false 40695579 536870912 11 1000000000000000 231931904 115965952 (BSN.sin_reduce_arg_pos_rat_q2 39595063605 536870912 226375608064910080 72057594037927936 11 ep785 ep786 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 40695579 536870912 ep785 ep786 1643684258814 1099511627776 232158401 231931904 (ep792 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep794 := nat_lit 810378936110887518921503752582669190540432808310527885258618796313379457704533806206843549760834829026766836829291384775238388360418796083024235593732096

noncomputable def ep795 := nat_lit 19439193155187530197451618687144426283755680205216142787799908258051950025362847967614044606143308225045242424493166366027710769872822281798603296787660800

noncomputable def ep796 := nat_lit 4047763125603092664281214368674769176784796503464002087812954291774699231650261466809074392531740597939447199931013402505463668941858371000617797010067456

noncomputable def ep797 := nat_lit 680371760431563556910806654050054919931448807182564997572996789031818250887699678866491561215015787876583484857260822810969876945548779862951115387568128000

noncomputable def ep798 := BSN.sin_dyadic_bound_f 1643684258814 1099511627776 4 3 536870912 232158401 ep794 ep795 ep789 ep796 ep797 ep789 535326298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 1643684258814) (BSN.sinEvenQ 1099511627776) 0 3 ep794 ep795 ep789 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 1643684258814) (BSN.sinOddQ 1099511627776) 0 3 ep796 ep797 ep789 rfl rfl rfl rfl) rfl rfl

noncomputable def ep799 := @Enclosure.Real.IsNear.sin_image qz121 qz378 Bool.false 39595063605 536870912 165 536870912 Bool.true 535326298 536870912 1 115965952 (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 332147467323781128279 4503599627370496000 541183659956257 1769500000000000000000 39595063605 536870912 165 536870912 (ep784 rfl) rfl) (Enclosure.sfrac_false_div 39595063605 536870912) (BSN.sin_reduce2 qz378 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep785) (@Nat.cast Real Real.instNatCast ep786)) 226375608064910080 72057594037927936 Bool.false 535326298 536870912 11 1000000000000000 231931904 115965952 (BSN.sin_reduce_arg_pos_rat_q2 39595063605 536870912 226375608064910080 72057594037927936 11 ep785 ep786 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 535326298 536870912 ep785 ep786 1643684258814 1099511627776 232158401 231931904 (ep798 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz379 := (@Enclosure.Real.IsNear.recentre' qz219 Bool.false 370727 536870912 1 536870912 370727 536870912 1 536870912 (ep780 rfl rfl) rfl)

noncomputable def ep800 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz219 qz116) (@HMul.hMul Real Real Real qz0 qz219 qz117) Bool.true 15086949915933 288230376151711744 366576716313 1020047301200907862016 Bool.false 99229956239323 144115188075855872 1058537415427 510023650600453931008 (@Enclosure.Real.IsNear.mulLit_ft qz219 qz116 370727 536870912 1 536870912 40695579 536870912 600319 1899986157568 15086949915933 288230376151711744 366576716313 1020047301200907862016 qz379 (@Enclosure.Real.IsNear.recentre' qz116 Bool.true 40695579 536870912 19671252992 62258746411188224 40695579 536870912 600319 1899986157568 (ep793 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz219 qz117 370727 536870912 1 536870912 267663149 268435456 600319 1899986157568 99229956239323 144115188075855872 1058537415427 510023650600453931008 qz379 (@Enclosure.Real.IsNear.neg qz122 Bool.true 267663149 268435456 600319 1899986157568 (@Enclosure.Real.IsNear.recentre' qz122 Bool.true 535326298 536870912 19671252992 62258746411188224 267663149 268435456 600319 1899986157568 (ep799 rfl rfl) rfl)) rfl)

noncomputable def ep801 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz208 44410290942563 720000000000 0 1 99229956239323 144115188075855872 1058537415427 510023650600453931008 ep726

noncomputable def ep802 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 3772474267 480000000 0 1 Bool.false 44410290942563 720000000000 0 1 ep776

noncomputable def ep803 := @Enclosure.Complex.IsNear.im_isNear qz196 Bool.true 15086949915933 288230376151711744 366576716313 1020047301200907862016 Bool.false 99229956239323 144115188075855872 1058537415427 510023650600453931008

noncomputable def ep804 := nat_lit 69175290276410818560000000

noncomputable def ep805 := nat_lit 244811352288217886883840000000

noncomputable def ep806 := nat_lit 74446203911384547131284031

noncomputable def ep807 := nat_lit 23058430092136939520000000000

noncomputable def ep808 := nat_lit 1808864291581078914236691

noncomputable def ep809 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz208) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz207) 374342456428382111001241 ep804 3993305160355046317009 ep805 ep806 ep807 ep808

noncomputable def ep810 := nat_lit 81603784096072628961280000000000

noncomputable def ep811 := nat_lit 3481911596525770676328705992114159869377904640000000

noncomputable def ep812 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz208 3772474267 480000000 0 1 99229956239323 144115188075855872 1058537415427 510023650600453931008 374342456428382111001241

noncomputable def ep813 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz207 44410290942563 720000000000 0 1 15086949915933 288230376151711744 366576716313 1020047301200907862016 ep806

noncomputable abbrev qz380 := (@ep779 510023650600453931008 (BSN.cpow_neg_s_sub_mk qz36 35467 1000 8 3 2097152 qz37 rfl EMRow06.d13) ep800)

noncomputable def ep814 := ep723 (@ep728 ep716 ep729 ep713 ep714 ep715 ep716 (@ep730 ep724 460967076390717205857 ep725 ep777 (ep778 qz380) rfl) (@ep801 ep714 ep727 ep716 ep802 (ep803 qz380) rfl) rfl rfl) (@ep809 ep810 ep811 ep718 ep719 ep720 ep722 (@ep812 ep804 3993305160355046317009 ep805 ep777 (ep803 qz380) rfl) (@ep813 ep807 ep808 ep810 ep802 (ep778 qz380) rfl) rfl rfl)

noncomputable def ep815 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) ep718 ep719 ep720 ep722 ep718 ep719 ep720

noncomputable def ep816 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196) Bool.true ep713 ep714 ep715 ep716 Bool.false ep718 ep719 ep720

noncomputable def ep817 := @ep683 53840778504929 123145302310912 179693071 123145302310912 (@ep684 1 458752 (ep685 (@ep686 131072 1 131072 (ep687 (@ep688 5080632356 1270158089 1000000 0 1 (ep692 rfl) (ep695 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep696 9 67108864 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (@ep697 72 536870912 11525839 268435456 9 67108864 (@ep702 11525803 11525875 268435456 (@ep708 ep709 ep710 ep711 ep712 ep698 ep699 ep700 ep701 (@ep717 ep716 ep703 ep704 ep705 ep706 (@ep721 ep722 ep814) (@ep721 ep722 ep814) rfl) (@ep815 ep722 ep707 ep709 ep710 ep711 (@ep816 ep722 ep814) (@ep816 ep722 ep814) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow06.d14 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 qz193 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)))) Bool.false 59405827566305 123145302310912 264595374997 3324923162394624 := ep681 (ep682 ep817) rfl rfl

noncomputable abbrev qz414 := (@HAdd.hAdd Complex Complex Complex qz416 qz423 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz381 := qz414

noncomputable abbrev qz222 := (@HDiv.hDiv Real Real Real qz252 (@Norm.norm Complex Complex.instNorm qz381) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz336) qz308))

noncomputable abbrev qz382 := (@HPow.hPow Complex Complex Complex qz403 qz405 (@HSub.hSub Complex Complex Complex qz393 qz412 qz406))

noncomputable abbrev qz223 := qz382

noncomputable def ep818 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz133 1 8))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 14556435 536870912 400439 4831838208 78596767241317 123145302310912 287322143

noncomputable def ep819 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz133 1 8)) 123 8192 1 221184 118345 65536 163 32768 14556435 536870912

noncomputable def ep820 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz133 1 8)) (Real.sqrt (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz133 1 8)) (Complex.re (zetaApproximant qz133 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz133 1 8)) (Complex.im (zetaApproximant qz133 1 8))))) Bool.false 118345 65536 163 32768

noncomputable def ep821 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz133 1 8)) (Complex.re (zetaApproximant qz133 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz133 1 8)) (Complex.im (zetaApproximant qz133 1 8))))) Bool.false 236690 131072 652 131072

noncomputable def ep822 := nat_lit 299841567476837717822810184485018122733

noncomputable def ep823 := nat_lit 91949205404187525528038616648908800000

noncomputable def ep824 := nat_lit 1415256184204854754830071304445638714688636846241714327

noncomputable def ep825 := nat_lit 78831527652485115779912851662781641460259871522816000000

noncomputable def ep826 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz133 1 8)) (Complex.re (zetaApproximant qz133 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz133 1 8)) (Complex.im (zetaApproximant qz133 1 8)))) ep822 ep823 ep824 ep825 118019 118671

noncomputable def ep827 := nat_lit 2271675680405940718787766935773958060910474629041

noncomputable def ep828 := nat_lit 699352783875239759933625420465462568812544000000

noncomputable def ep829 := nat_lit 1330461451044992721315640489179643917264304518858197347

noncomputable def ep830 := nat_lit 554831593915502692263795194207050030289460289

noncomputable def ep831 := nat_lit 43709548992202484995851588779091410550784000000

noncomputable def ep832 := nat_lit 4239736657993101675721540763299739871216616369175849

noncomputable def ep833 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz133 1 8)) (Complex.re (zetaApproximant qz133 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz133 1 8)) (Complex.im (zetaApproximant qz133 1 8))) ep827 ep828 ep829 ep825 ep830 ep831 ep832

noncomputable def ep834 := nat_lit 3941576382624255788995642583139082073012993576140800000

noncomputable def ep835 := nat_lit 99681942466885123882165618815180544273022937638992302551048379785097775846557977264783360000000

noncomputable def ep836 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz133 1 8)) (Complex.re (zetaApproximant qz133 1 8)) ep384 836273151473392549888000 ep385 ep386 ep384 836273151473392549888000 ep385 ep386 ep827

noncomputable def ep837 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz133 1 8)) (Complex.im (zetaApproximant qz133 1 8)) 23554863487515751091233 209068287868348137472000 ep500 ep501 23554863487515751091233 209068287868348137472000 ep500 ep501 ep830

noncomputable def ep838 := @ep818 123145302310912 43988874697741722189824 81935664075877 123145302310912 94436995351 1108307720798208 (@ep819 400439 4831838208 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz197)) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow06.d10 EMRow06.d11 rfl) (ep662 rfl)) (ep820 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz133 1 8)) (@ep821 118345 65536 163 32768 (@ep826 65536 (@ep833 ep834 ep835 ep822 ep823 ep824 ep825 (@ep836 ep828 ep829 ep825 ep643 ep643 rfl) (@ep837 ep831 ep832 ep834 ep651 ep651 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz224 := (@Norm.norm Complex Complex.instNorm qz381)

noncomputable def ep839 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz224 qz373) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 78596767241317 123145302310912 287322143 123145302310912 (BSN.zrb_shape_eq qz224 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz145 3)

noncomputable def ep840 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz224 qz373) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 5132221 458752 1 458752 15314377 268435456 53 268435456

noncomputable def ep841 := @Enclosure.Real.IsNear.mulLit_ff qz224 qz373 5132221 131072 1 131072 2 7 0 1 5132221 458752

noncomputable abbrev qz383 := (Complex.re qz414)

noncomputable abbrev qz384 := (Complex.im qz414)

noncomputable abbrev qz225 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz249 qz383 qz383) (@HMul.hMul Real Real Real qz249 qz384 qz384))

noncomputable abbrev qz226 := qz381

noncomputable def ep842 := @Enclosure.Real.IsNear.of_eq qz224 (Real.sqrt qz225) Bool.false 5132221 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz226)

noncomputable def ep843 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz225) Bool.false 5132221 131072 1 131072 5132221

noncomputable def ep844 := @Enclosure.Real.IsNear.sqrt_image qz225 1533172001 1000000 0 1 2566110 2566111 65536

noncomputable abbrev qz227 := (@HMul.hMul Real Real Real qz249 qz383 qz383)

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz249 qz384 qz384)

noncomputable def ep845 := @Enclosure.Real.IsNear.addLit_ff qz227 qz228 49 4 0 1 1520922001 1000000 0 1

noncomputable abbrev qz229 := qz383

noncomputable def ep846 := @Enclosure.Real.IsNear.mulLit_ff qz229 qz229 7 2 0 1 7 2 0 1 49 4

noncomputable def ep847 := @Enclosure.Complex.IsNear.of_eq qz226 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz145) Bool.false 7 2 0 1 Bool.false 38999 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 38999 1000 3 qz146)

noncomputable abbrev qz230 := (ep847 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz335 Bool.false 7 2 0 1 Bool.false 38999 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz357))

noncomputable def ep848 := @ep846 0 1 (@Enclosure.Complex.IsNear.re_isNear qz226 Bool.false 7 2 0 1 Bool.false 38999 1000 0 1 qz230)

noncomputable def ep849 := ep848 (@Enclosure.Complex.IsNear.re_isNear qz226 Bool.false 7 2 0 1 Bool.false 38999 1000 0 1 qz230)

noncomputable abbrev qz231 := qz384

noncomputable def ep850 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 38999 1000 0 1 38999 1000 0 1 1520922001 1000000

noncomputable def ep851 := @ep850 0 1 (@Enclosure.Complex.IsNear.im_isNear qz226 Bool.false 7 2 0 1 Bool.false 38999 1000 0 1 qz230)

noncomputable def ep852 := ep851 (@Enclosure.Complex.IsNear.im_isNear qz226 Bool.false 7 2 0 1 Bool.false 38999 1000 0 1 qz230)

noncomputable def ep853 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 15314377 268435456

noncomputable def ep854 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 30628754 536870912

noncomputable def ep855 := nat_lit 35043172321384640846114227452865589250424395423954264689

noncomputable def ep856 := nat_lit 3028125435379197933022270609939348180013481609772004644711

noncomputable def ep857 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep855 ep704 ep856 ep706

noncomputable def ep858 := nat_lit 287488974946707921970807043773319402662547857458741001

noncomputable def ep859 := nat_lit 430669870634312742820833487530831642624000000000000000000

noncomputable def ep860 := nat_lit 844422202158077468832583114192805894175204108432199442999

noncomputable def ep861 := nat_lit 1740996746732308924802753209908287761491293686717858729

noncomputable def ep862 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep858 ep859 ep860 ep706 ep861

noncomputable def ep863 := nat_lit 672921672866113660657552324266924441600000000000000000000

noncomputable def ep864 := nat_lit 136481452076320029011855468484158892864892343833737825107

noncomputable def ep865 := nat_lit 8428021623166770731292387893879904774232473600000000000000000000

noncomputable def ep866 := nat_lit 943252405641665765344581904047877140679224459991205707355929471929565522700786984081996906496000000000000000000

noncomputable def ep867 := nat_lit 536179983724409393371589251

noncomputable def ep868 := nat_lit 20752587082923245568000000000

noncomputable def ep869 := nat_lit 44500763808111676897173587

noncomputable def ep870 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep867 ep868 ep869 ep716 ep867 ep868 ep869

noncomputable def ep871 := nat_lit 1319468357609347494731716723

noncomputable def ep872 := nat_lit 25940733853654056960000000000

noncomputable def ep873 := nat_lit 14613808660328091514202749

noncomputable def ep874 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.true ep867 ep868 ep869 ep716 Bool.false ep871 ep872 ep873

noncomputable def ep875 := nat_lit 91804257108081707581440000000000

noncomputable def ep876 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.true ep867 ep868 ep869 ep716 Bool.false ep871 ep872 ep873 ep875

noncomputable def ep877 := nat_lit 8646911284551352320000000

noncomputable def ep878 := nat_lit 15300709518013617930240000000

noncomputable def ep879 := nat_lit 649697648311425698249436451

noncomputable def ep880 := nat_lit 38244807578111667981405587

noncomputable abbrev qz232 := (Complex.re qz382)

noncomputable abbrev qz233 := (Complex.im qz382)

noncomputable def ep881 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) 47299026911256793699103 ep877 260664842916667038157 ep878 ep879 ep868 ep880

noncomputable def ep882 := nat_lit 4636300751817156007744405259150226639625912320000000

noncomputable def ep883 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 4561516003 480000000 0 1 10369146327701 18014398509481984 57144344719 31876478162528370688 47299026911256793699103

noncomputable def ep884 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)))) 4561516003 480000000 0 1 0 1 0 1 4561516003

noncomputable def ep885 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 13684548009 2000000 0 1 4561516003 480000000 0

noncomputable abbrev qz385 := (@HAdd.hAdd Complex Complex Complex qz395 qz411 qz407)

noncomputable abbrev qz234 := qz385

noncomputable def ep886 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 13684548009 2000000 0 1 Bool.true 59090192866999 1000000000 0 1

noncomputable abbrev qz235 := (Complex.re qz385)

noncomputable abbrev qz236 := (Complex.im qz385)

noncomputable def ep887 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 1520172001 400000 0 1 1520922001 500000 0 1

noncomputable def ep888 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 1520172001 1000000 0 1 5 2 0 1 1520172001 400000

noncomputable abbrev qz386 := (@HAdd.hAdd Complex Complex Complex qz395 qz411 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz386

noncomputable def ep889 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 1520172001 1000000 0 1 Bool.false 38999 500 0 1

noncomputable abbrev qz238 := (Complex.re qz386)

noncomputable abbrev qz239 := (Complex.im qz386)

noncomputable def ep890 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 1520922001 1000000 0 1

noncomputable def ep891 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep892 := @ep891 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep609)

noncomputable def ep893 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz145) Bool.false 3 2 0 1 Bool.false 38999 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 38999 1000 1 qz146)

noncomputable abbrev qz240 := (ep893 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz335 Bool.false 3 2 0 1 Bool.false 38999 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz357))

noncomputable def ep894 := ep892 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 38999 1000 0 1 qz240)

noncomputable def ep895 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 38999 1000 0 1 38999 1000 0 1 1520922001 1000000

noncomputable def ep896 := @ep895 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep609)

noncomputable def ep897 := ep896 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 38999 1000 0 1 qz240)

noncomputable def ep898 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 1520172001 1000000 0 1 Bool.false 38999 500 0 1 (@ep890 6080688004 1520172001 1000000 0 1 (ep894 rfl) (ep897 rfl) rfl rfl)

noncomputable def ep899 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 38999 2000 0 1 116997 2000 0 1

noncomputable def ep900 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 38999 1000 0 1 38999 2000

noncomputable def ep901 := @ep900 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep609)

noncomputable def ep902 := ep901 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 38999 1000 0 1 qz240)

noncomputable def ep903 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 38999 1000 0 1 3 2 0 1 116997 2000

noncomputable def ep904 := @ep903 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 38999 1000 0 1 ep609)

noncomputable def ep905 := ep904 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 38999 1000 0 1 qz240)

noncomputable abbrev qz241 := (ep889 (BSN.ascPochhammer_succ_eval_c 1 2 qz336 rfl) (ep898 (@ep899 311992000 38999 500 0 1 (ep902 rfl) (ep905 rfl) rfl rfl)))

noncomputable def ep906 := @ep888 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1520172001 1000000 0 1 Bool.false 38999 500 0 1 qz241)

noncomputable def ep907 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz145) Bool.false 5 2 0 1 Bool.false 38999 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 38999 1000 2 qz146)

noncomputable abbrev qz242 := (ep907 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz335 Bool.false 5 2 0 1 Bool.false 38999 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz357))

noncomputable def ep908 := ep906 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 38999 1000 0 1 qz242)

noncomputable def ep909 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 38999 500 0 1 38999 1000 0 1 1520922001 500000

noncomputable def ep910 := @ep909 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1520172001 1000000 0 1 Bool.false 38999 500 0 1 qz241)

noncomputable def ep911 := ep910 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 38999 1000 0 1 qz242)

noncomputable def ep912 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 13684548009 2000000 0 1 Bool.true 59090192866999 1000000000 0 1 (@ep887 1368454800900000 13684548009 2000000 0 1 (ep908 rfl) (ep911 rfl) rfl rfl)

noncomputable def ep913 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 59285187866999 1000000000 0 1 38999 200 0 1

noncomputable def ep914 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 1520172001 1000000 0 1 38999 1000 0 1 59285187866999 1000000000

noncomputable def ep915 := @ep914 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1520172001 1000000 0 1 Bool.false 38999 500 0 1 qz241)

noncomputable def ep916 := ep915 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 38999 1000 0 1 qz242)

noncomputable def ep917 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 38999 500 0 1 5 2 0 1 38999 200

noncomputable def ep918 := @ep917 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1520172001 1000000 0 1 Bool.false 38999 500 0 1 qz241)

noncomputable def ep919 := ep918 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 38999 1000 0 1 qz242)

noncomputable abbrev qz243 := (ep886 (BSN.ascPochhammer_succ_eval_c 2 3 qz336 rfl) (ep912 (@ep913 11818038573399800 59090192866999 1000000000 0 1 (ep916 rfl) (ep919 rfl) rfl rfl)))

noncomputable def ep920 := @ep885 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep733) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 13684548009 2000000 0 1 Bool.true 59090192866999 1000000000 0 1 qz243)

noncomputable def ep921 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 59090192866999 1000000000 0 1 0 1 0

noncomputable def ep922 := @ep921 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep733) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 13684548009 2000000 0 1 Bool.true 59090192866999 1000000000 0 1 qz243)

noncomputable def ep923 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)))) 59090192866999 720000000000 0 1 0 1 0 1 59090192866999

noncomputable def ep924 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 59090192866999 1000000000 0 1 59090192866999 720000000000 0

noncomputable def ep925 := @ep924 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep733) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 13684548009 2000000 0 1 Bool.true 59090192866999 1000000000 0 1 qz243)

noncomputable def ep926 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 13684548009 2000000 0 1 0 1 0

noncomputable def ep927 := @ep926 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep733) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 13684548009 2000000 0 1 Bool.true 59090192866999 1000000000 0 1 qz243)

noncomputable def ep928 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 4561516003 480000000 0 1 Bool.false 59090192866999 720000000000 0 1 (@ep884 4561516003 480000000 0 1 (ep920 rfl) (ep922 rfl) rfl rfl) (@ep923 59090192866999 720000000000 0 1 (ep925 rfl) (ep927 rfl) rfl rfl)

noncomputable def ep929 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 4561516003 480000000 0 1 Bool.false 59090192866999 720000000000 0 1 ep928

noncomputable def ep930 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.false 10369146327701 18014398509481984 57144344719 31876478162528370688 Bool.false 54975082732745 144115188075855872 647227665413 510023650600453931008

noncomputable def ep931 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz219 qz188) (@HMul.hMul Real Real Real qz0 qz219 qz189)) Bool.false 10369146327701 18014398509481984 57144344719 31876478162528370688 Bool.false 54975082732745 144115188075855872 647227665413

noncomputable def ep932 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz120 38999 1000 0 1 9364972152248037 4503599627370496 15258794371 1769500000000000000 365224548965521194963 4503599627370496000 595077721674629 1769500000000000000000 qz180 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 15258794371 1769500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz119) Bool.false ep781 ep782 1000000347897856 115965952000000000000000 9364972152248037 4503599627370496 15258794371 1769500000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 268435456 24973259072661432 36028797018963968 115965952 1000000000000000 rfl rfl rfl rfl (ep783 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep933 := nat_lit 2382860529372943706226688

noncomputable def ep934 := nat_lit 2417851639229258349412352

noncomputable def ep935 := nat_lit 6095253297269824472276868938451785229672730396396642962210348737213518815802343625716933187799613440

noncomputable def ep936 := nat_lit 775106975594979850699505476734807071347029417072782157158382458646527094091278842792332482107544698880

noncomputable def ep937 := nat_lit 1900861218473397978867123540414839348058312884295819245857735696040894125354480874927536583213056

noncomputable def ep938 := nat_lit 15960681050876773830664109972117813480674580436369014527010000834908483069946040336413513765959499776

noncomputable def ep939 := nat_lit 14210294552574630596157600406804796308028872646334339547903678408519663391673445451192762171971652812800

noncomputable def ep940 := BSN.sin_dyadic_bound_f 1083599513264 1099511627776 3 2 536870912 232158401 ep935 ep936 ep937 ep938 ep939 ep937 447516208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1083599513264) (BSN.sinEvenQ 1099511627776) 0 2 ep935 ep936 ep937 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1083599513264) (BSN.sinOddQ 1099511627776) 0 2 ep938 ep939 ep937 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz387 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1360567469) (@Nat.cast Real Real.instNatCast 16777216))

noncomputable def ep941 := @Enclosure.Real.IsNear.cos_image qz190 qz387 Bool.false 1360567469 16777216 91 268435456 Bool.false 447516208 536870912 1 115965952 (@Enclosure.Real.IsNear.recentre' qz190 Bool.false 365224548965521194963 4503599627370496000 595077721674629 1769500000000000000000 1360567469 16777216 91 268435456 (ep932 rfl) rfl) (Enclosure.sfrac_false_div 1360567469 16777216) (BSN.cos_reduce3 qz387 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep933) (@Nat.cast Real Real.instNatCast ep934)) 226375608064910080 72057594037927936 Bool.false 447516208 536870912 12 1000000000000000 231931904 115965952 (BSN.sin_reduce_arg_pos_rat_q3 1360567469 16777216 226375608064910080 72057594037927936 12 ep933 ep934 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 447516208 536870912 ep933 ep934 1083599513264 1099511627776 232158401 231931904 (ep940 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep942 := nat_lit 58808940698747552381828242286265992888375658468664297581503221808489370958714499158248585423674436045693318089843421280791611998335404962130134067838976

noncomputable def ep943 := nat_lit 2620750126276833616604463316160531307428294024857155261293814900449318461638152473497381574523645453135883096245565927272125336036501029488951296

noncomputable def ep944 := nat_lit 356640744245644978428579460907299633045751706797604211411639440151600130028470638417549674125410984301468919297906137090598799639760627150861850011238400

noncomputable def ep945 := BSN.cos_dyadic_bound_f 1083599513264 1099511627776 4 3 536870912 232158401 ep942 ep788 ep943 ep944 ep791 ep943 296579870 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1083599513264) (BSN.cosEvenQ 1099511627776) 0 3 ep942 ep788 ep943 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1083599513264) (BSN.cosOddQ 1099511627776) 0 3 ep944 ep791 ep943 rfl rfl rfl rfl) rfl rfl

noncomputable def ep946 := @Enclosure.Real.IsNear.sin_image qz190 qz387 Bool.false 1360567469 16777216 91 268435456 Bool.true 296579870 536870912 1 115965952 (@Enclosure.Real.IsNear.recentre' qz190 Bool.false 365224548965521194963 4503599627370496000 595077721674629 1769500000000000000000 1360567469 16777216 91 268435456 (ep932 rfl) rfl) (Enclosure.sfrac_false_div 1360567469 16777216) (BSN.sin_reduce3 qz387 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep933) (@Nat.cast Real Real.instNatCast ep934)) 226375608064910080 72057594037927936 Bool.false 296579870 536870912 12 1000000000000000 231931904 115965952 (BSN.sin_reduce_arg_pos_rat_q3 1360567469 16777216 226375608064910080 72057594037927936 12 ep933 ep934 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 296579870 536870912 ep933 ep934 1083599513264 1099511627776 232158401 231931904 (ep945 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep947 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz219 qz188) (@HMul.hMul Real Real Real qz0 qz219 qz189) Bool.false 10369146327701 18014398509481984 57144344719 31876478162528370688 Bool.false 54975082732745 144115188075855872 647227665413 510023650600453931008 (@Enclosure.Real.IsNear.mulLit_ff qz219 qz188 370727 536870912 1 536870912 27969763 33554432 330241 949993078784 10369146327701 18014398509481984 57144344719 31876478162528370688 qz379 (@Enclosure.Real.IsNear.recentre' qz188 Bool.false 447516208 536870912 10821337088 31129373205594112 27969763 33554432 330241 949993078784 (ep941 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz219 qz189 370727 536870912 1 536870912 148289935 268435456 330241 949993078784 54975082732745 144115188075855872 647227665413 510023650600453931008 qz379 (@Enclosure.Real.IsNear.neg qz191 Bool.true 148289935 268435456 330241 949993078784 (@Enclosure.Real.IsNear.recentre' qz191 Bool.true 296579870 536870912 10821337088 31129373205594112 148289935 268435456 330241 949993078784 (ep946 rfl rfl) rfl)) rfl)

noncomputable def ep948 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 59090192866999 720000000000 0 1 54975082732745 144115188075855872 647227665413 510023650600453931008 ep879

noncomputable def ep949 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 4561516003 480000000 0 1 Bool.false 59090192866999 720000000000 0 1 ep928

noncomputable def ep950 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.false 10369146327701 18014398509481984 57144344719 31876478162528370688 Bool.false 54975082732745 144115188075855872 647227665413 510023650600453931008

noncomputable def ep951 := nat_lit 13835058055282163712000000

noncomputable def ep952 := nat_lit 612714856369986505562439299

noncomputable def ep953 := nat_lit 12970366926827028480000000000

noncomputable def ep954 := nat_lit 3376670350703985775028281

noncomputable def ep955 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) 50153943930333057923647 ep951 2952339353365729104239 ep805 ep952 ep953 ep954

noncomputable def ep956 := nat_lit 22951064277020426895360000000000

noncomputable def ep957 := nat_lit 9127460664816564844965852223765377699847077888000000

noncomputable def ep958 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 4561516003 480000000 0 1 54975082732745 144115188075855872 647227665413 510023650600453931008 50153943930333057923647

noncomputable def ep959 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 59090192866999 720000000000 0 1 10369146327701 18014398509481984 57144344719 31876478162528370688 ep952

noncomputable abbrev qz388 := (@ep931 510023650600453931008 (BSN.cpow_neg_s_sub_mk qz145 38999 1000 8 3 2097152 qz146 rfl EMRow06.d13) ep947)

noncomputable def ep960 := ep876 (@ep881 ep716 ep882 ep867 ep868 ep869 ep716 (@ep883 ep877 260664842916667038157 ep878 ep929 (ep930 qz388) rfl) (@ep948 ep868 ep880 ep716 ep949 (ep950 qz388) rfl) rfl rfl) (@ep955 ep956 ep957 ep871 ep872 ep873 ep875 (@ep958 ep951 2952339353365729104239 ep805 ep929 (ep950 qz388) rfl) (@ep959 ep953 ep954 ep956 ep949 (ep930 qz388) rfl) rfl rfl)

noncomputable def ep961 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep871 ep872 ep873 ep875 ep871 ep872 ep873

noncomputable def ep962 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.true ep867 ep868 ep869 ep716 Bool.false ep871 ep872 ep873

noncomputable def ep963 := @ep840 78596767241317 123145302310912 287322143 123145302310912 (@ep841 1 458752 (ep842 (@ep843 131072 1 131072 (ep844 (@ep845 6132688004 1533172001 1000000 0 1 (ep849 rfl) (ep852 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep853 53 268435456 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep854 106 536870912 15314377 268435456 53 268435456 (@ep857 15314324 15314430 268435456 (@ep862 ep863 ep864 ep865 ep866 ep855 ep704 ep856 ep706 (@ep870 ep716 ep858 ep859 ep860 ep706 (@ep874 ep875 ep960) (@ep874 ep875 ep960) rfl) (@ep961 ep875 ep861 ep863 ep864 ep865 (@ep962 ep875 ep960) (@ep962 ep875 ep960) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow06.d15 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz133 1 8))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 81935664075877 123145302310912 94436995351 1108307720798208 := ep838 (ep839 ep963) rfl rfl

noncomputable def EMRow06.d16 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz389 := (EMRow06.d3 qz397 qz410 (@Enclosure.dec_le_dec qz397 qz410 35467 1000 38999 1000 (@Eq.refl Real qz397) (@Eq.refl Real qz410) rfl rfl rfl) 8 8 1 1)

noncomputable abbrev qz244 := qz389

noncomputable def ep964 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz244 (@Enclosure.dec_nonneg qz36 35467 1000 qz37) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 8 rfl)

noncomputable abbrev qz245 := (Zeta.Certificates.ZIntervalEM.fstVal qz389)

noncomputable def ep965 := @Enclosure.Real.IsNear.pos_val qz245 ep38 ep39

noncomputable def ep966 := @Enclosure.Real.IsNear.of_eq qz245 (hardyZApproximantEM 1 8 qz36) Bool.false

noncomputable abbrev qz246 := (Zeta.Certificates.ZIntervalEM.sndVal qz389)

noncomputable def ep967 := BSN.mul_neg_of_pos_neg_r qz245 qz246 (@ep965 ep40 ep41 (@ep966 ep38 ep39 ep40 ep41 (@Eq.refl Real (hardyZApproximantEM 1 8 qz36)) EMRow06.d8) rfl rfl rfl)

noncomputable def ep968 := @Enclosure.Real.IsNear.neg_val qz246 ep369 ep370

noncomputable def ep969 := @Enclosure.Real.IsNear.of_eq qz246 (hardyZApproximantEM 1 8 qz145) Bool.true

noncomputable def ep970 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz245) (BSN.hardyZErrorBoundStrong 1 8 qz36)

noncomputable def ep971 := @Enclosure.norm_gt_of_isNear qz245 (BSN.hardyZErrorBoundStrong 1 8 qz36) Bool.false

noncomputable def ep972 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 8 qz36) (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 qz193 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)))) Bool.false 59405827566305 123145302310912 264595374997 3324923162394624 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 8))) (@HMul.hMul Real Real Real qz0 qz193 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)))))

noncomputable def ep973 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz246) (BSN.hardyZErrorBoundStrong 1 8 qz145)

noncomputable def ep974 := @Enclosure.norm_gt_of_isNear qz246 (BSN.hardyZErrorBoundStrong 1 8 qz145) Bool.true

noncomputable def ep975 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 8 qz145) (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz133 1 8))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 81935664075877 123145302310912 94436995351 1108307720798208 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz55 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz133 1 8))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz133 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep976 := @List.cons EMRow06.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz244 (ep964 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 8 rfl) (ep967 (@ep968 ep371 ep372 (@ep969 ep369 ep370 ep371 ep372 (@Eq.refl Real (hardyZApproximantEM 1 8 qz145)) EMRow06.d9) rfl rfl rfl)) (ep970 (hardyZErrorBoundEM 1 8 qz36) (BSN.hardyZErrorBoundEM_le_strong 1 8 qz36 rfl) (@ep971 Bool.false ep38 ep39 ep40 ep41 59405827566305 123145302310912 264595374997 3324923162394624 (@ep966 ep38 ep39 ep40 ep41 (@Eq.refl Real (hardyZApproximantEM 1 8 qz36)) EMRow06.d8) (ep972 EMRow06.d14) rfl rfl rfl rfl rfl)) (ep973 (hardyZErrorBoundEM 1 8 qz145) (BSN.hardyZErrorBoundEM_le_strong 1 8 qz145 rfl) (@ep974 Bool.false ep369 ep370 ep371 ep372 81935664075877 123145302310912 94436995351 1108307720798208 (@ep969 ep369 ep370 ep371 ep372 (@Eq.refl Real (hardyZApproximantEM 1 8 qz145)) EMRow06.d9) (ep975 EMRow06.d15) rfl rfl rfl rfl rfl)))) (@List.nil EMRow06.d0)

noncomputable abbrev qz390 := (@Enclosure.dec_le_dec qz397 qz410 35467 1000 38999 1000 (@Eq.refl Real qz397) (@Eq.refl Real qz410) rfl rfl rfl)

noncomputable abbrev qz247 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep976 (@List.IsChain.singleton EMRow06.d1 EMRow06.d16 (EMRow06.d2 qz259 qz335 qz390))))

noncomputable abbrev qz391 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep977 := And (@Eq (Option Real) (@Option.map qz391 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz391 qz247)) (@Option.some Real qz36))

noncomputable def ep978 := ep977 (@Eq (Option Real) (@Option.map qz391 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz391 qz247)) (@Option.some Real qz145))

noncomputable def ep979 := @And.intro (@Eq Nat (@List.length qz391 qz247) 1) ep978

noncomputable def ep980 := @And.intro (@Eq (Option Real) (@Option.map qz391 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz391 qz247)) (@Option.some Real qz36))

noncomputable def ep981 := @ep980 (@Eq (Option Real) (@Option.map qz391 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz391 qz247)) (@Option.some Real qz145))

noncomputable abbrev qz248 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep976 (@List.IsChain.singleton EMRow06.d1 EMRow06.d16 (EMRow06.d2 qz259 qz335 qz390)))

theorem EMRow06.d17 : Zeta.Certificates.BatchSpec 1 35467 1000 38999 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz391 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz391 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz391 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz36)) (@Eq (Option Real) (@Option.map qz391 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz391 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz145)))) qz248 (ep979 (@Eq.refl Nat 1) (ep981 (@Eq.refl (Option Real) (@Option.some Real qz36)) (@Eq.refl (Option Real) (@Option.some Real qz145))))

theorem solution : Zeta.Certificates.BatchSpec 1 35467 1000 38999 1000 := EMRow06.d17
#print axioms solution
#check solution
