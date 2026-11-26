-- Prove2me | solution 1 for RHHeight1000.em_main_0004_0004
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:44:38.31636+00:00
-- url     : https://prove2.me/submissions/2dc36402-1038-4dde-a6ed-c9483fa1478b

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow04.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow04.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow04.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow04.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow04.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz249 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz249

noncomputable abbrev qz250 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz1 := qz250

noncomputable abbrev qz251 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz251 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138516661214455 2251799813685248 250000000024703 12351500000000000000 4138516661214455 2251799813685248 250000000024703 12351500000000000000 120446 65536

noncomputable abbrev qz252 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 65536 qz252 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 779317518150410741488063439345657628452599855445271348474342368876423347582876053728679783827237610085654588674605917415063316248867402488514697634436426745

noncomputable def ep10 := nat_lit 13198325246229587668616048586507268161410801335203869857947191811663857046415771104290097871102374067703089877156867761119753226876438075596795543285583799

noncomputable def ep11 := nat_lit 13338205139369261376383149914767634013226508915861991492218067381232119098362059104733250767410551174650894954010182016771344050520336484956804919489535

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 4 3 ep9 131072 49406 ep10 ep11 59189 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 3 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz253 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz253

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138516661214455 2251799813685248 250000000024703 12351500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000098812 49406000000000000000 4138516661214455 2251799813685248 250000000024703 12351500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 59189 131072 24973259072661432 36028797018963968 49406 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 779317518150412560342812906055656980396982394702499187106382620393032652998517540933158707129341055012778793601285942846917973645097155238594697634436426745

noncomputable def ep18 := nat_lit 13198325246229655554962711811363413523213721429909419700721697472804734044169853548961061453892255410264786862895235075217650796661500958924795543285583799

noncomputable def ep19 := nat_lit 13338205139369401582665284895604560799810298653799657073142644093199656832454717421805370366589019475922075211274104314270069372987910244956804919489535

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 4 3 ep17 131072 49406 ep18 ep19 59189 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 3 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138516661214455 2251799813685248 250000000024703 12351500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000098812 49406000000000000000 4138516661214455 2251799813685248 250000000024703 12351500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 59189 131072 24973259072661432 36028797018963968 49406 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz254 := (Real.log (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz3 := qz254

theorem EMRow04.d4 : Enclosure.Real.IsNear qz3 Bool.false 60223 32768 3 65536 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz251) Bool.false 60223 32768 3 65536 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz251) Bool.false 120446 65536 3 65536 60223 32768 3 65536 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 150042 131072 1 49406 150042 131072 1 49406 75021 65536 2 65536 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 5456220599384213465248909714772227496572670538165976141063262914812807742611017753801422503639530882087556452122005170047444298375835020188444492540969863625638808382453421118235702266947370928498132967594635949979551089348001357731941995137847266570621617494261809398531128871567535833923098076891483476912075228072418610430965163137427706923427310178652894498746239459018086669257415154730407592571637957767157504839263249849478535520334507104454135585522664276476675

noncomputable def ep28 := nat_lit 583201912334273870627228188254822588827079241605343036411752047433839590517388190714780374919746279700129906501257101384229175562492847525225536391462542197025353003914524118772974087630067522636400444148635637549655768907025719966434833632093412247469427754039812435067522613541620617101084764807513402584784781490076808276521160080078978009740617112077674385114356333461540984478969922738031393369686631450339262287925718320742111081121726382582016608811398564907105

noncomputable def ep29 := nat_lit 2006268627360805445673839316848610509641534779303135707206598861506426804997221642604762844037348942607248852390277353874343091902420975230792155995982437872051629609224882022549487822374001366578458875613104959699164386313425243185530298109514065278868815165519648262204211929774735225023360668387821809970420335957473972782118680523137645713941929429588852958886338507735711181009301082096313539911189247153419366938656533848809858580689548163599238034961919825

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 10 9 ep27 131072 49406 ep28 ep29 150042 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 9 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 5456220599384260892400251500854699790811159195150212163211869656216336849990273498858157048596616978904240776489460003685239051624059887013466241201881443704542959173524008982544253046253151867013374679201187657749749224297051088632484873343955402287279851789208893474071824987110190207053471018354491495133306616646837230249901879422821128116650397962087630806812522581253210958036113071268120219429850657911869289056672761916619783759890108169949892385522664276476675

noncomputable def ep34 := nat_lit 583201912334279575053067226115417021307550325332234501953544426829928714668898700518418107620762577859683234776628347658361181262145210140271013263714562720079188253110303208819702903278206870150494721073991877864419341163488949363940583288588224434829960190109694548513088121652843287215458036179968684293644459891198769761601084092249455692877745995219003758983943549453190712470220270279351626860119698313725888367584660500821040083453648022042061408811398564907105

noncomputable def ep35 := nat_lit 2006268627360839170887858856494478835319319717359667041823756329478526322484078784125879825811686186445537802910004300367040714583746383402724632880452479311196631191501299191497899488881639138562974769996989848045902383299749709271247360054208480548633525642122514778503225872819822968825602771791453574137145372948950799520945900351638147820910599315255916738483881817718250085827996954508077874524152655659774549924038927632065100609588052048399238034961919825

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 10 9 ep33 131072 49406 ep34 ep35 150042 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 9 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 75021 65536 2 65536 75021 65536 1 32768 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 150042 131072 1 49406 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 150042 131072 49406 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 150042 131072 1 49406 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 150042 131072 49406 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow04.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 32768 := ep37

theorem EMRow04.d6 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow04.d7 : @Eq Nat (Nat.pow 6 1) 6 := @Eq.refl Nat 6

noncomputable def ep38 := nat_lit 11853261393716373176139607

noncomputable def ep39 := nat_lit 4139054314381110442721280

noncomputable def ep40 := nat_lit 189035133485597286806363346656689

noncomputable def ep41 := nat_lit 37887136376424776699961464900812800

noncomputable abbrev qz418 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz396 := qz418

noncomputable abbrev qz255 := qz396

noncomputable abbrev qz4 := qz255

noncomputable abbrev qz5 := (@instHSub Real Real.instSub)

noncomputable abbrev qz397 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz256 := qz397

noncomputable abbrev qz6 := qz256

noncomputable abbrev qz419 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz420 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz421 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz422 := (Enclosure.sfrac Bool.false 27670 1000)

noncomputable abbrev qz398 := (@HAdd.hAdd Complex Complex Complex qz419 (@HAdd.hAdd Complex Complex Complex qz419 qz420 (@HMul.hMul Complex Complex Complex qz418 Complex.I (@HDiv.hDiv Complex Complex Complex qz421 (↑qz422) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz257 := qz398

noncomputable abbrev qz7 := (Complex.Stirling.logGammaStirling 1 qz257)

noncomputable abbrev qz399 := qz419

noncomputable abbrev qz258 := qz399

noncomputable abbrev qz8 := qz258

noncomputable abbrev qz400 := (@HAdd.hAdd Complex Complex Complex qz419 qz420 (@HMul.hMul Complex Complex Complex qz418 Complex.I (@HDiv.hDiv Complex Complex Complex qz421 (↑qz422) (2 : Complex))))

noncomputable abbrev qz259 := qz400

noncomputable abbrev qz9 := qz259

noncomputable abbrev qz401 := qz422

noncomputable abbrev qz260 := qz401

noncomputable abbrev qz10 := (@HMul.hMul Real Real Real qz249 (@HDiv.hDiv Real Real Real qz253 qz260 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz423 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 27670 1000)))

noncomputable abbrev qz402 := qz423

noncomputable abbrev qz261 := qz402

noncomputable abbrev qz11 := qz261

noncomputable def ep42 := Complex.re (@HMul.hMul Complex Complex Complex qz4 (Complex.exp (@HMul.hMul Complex Complex Complex qz4 Complex.I ↑(@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10))) (zetaApproximant qz11 1 6))

noncomputable def ep43 := @Enclosure.Real.IsNear.of_eq ep42 (@HSub.hSub Real Real Real qz5 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 6))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 6))))

noncomputable def ep44 := nat_lit 35559964118216062689879401

noncomputable def ep45 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 6))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 6))) ep44

noncomputable def ep46 := nat_lit 12417162943143331328163840

noncomputable def ep47 := nat_lit 129058923770842962894367858897

noncomputable def ep48 := nat_lit 26219471540778392179904127959040

noncomputable def ep49 := nat_lit 636247159182301356000447637631

noncomputable def ep50 := nat_lit 9471784094106194174990366225203200

noncomputable def ep51 := nat_lit 22077581720016963863063171520661433904883021381632

noncomputable def ep52 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 6)) 131071 131072 551531

noncomputable def ep53 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) Bool.false 131071 131072 551531

noncomputable abbrev qz12 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz262 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 823529) qz12)

noncomputable def ep54 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) qz262 Bool.false 823529 131072 21

noncomputable def ep55 := nat_lit 60710092800000000000000000

noncomputable def ep56 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) Bool.false 11318500618344259247 1801439850948198400 38742760352205177220733 ep55

noncomputable def ep57 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10 39848505602890456751 1801439850948198400 13110309977205177220733 ep55 207583107 13107200

noncomputable def ep58 := nat_lit 148353851304761874802278400

noncomputable def ep59 := nat_lit 10118348800000000000000000

noncomputable def ep60 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 19338308215257051969 900719925474099200 3449055165882728646449 ep59 Bool.false 39848505602890456751 1801439850948198400

noncomputable def ep61 := @Enclosure.Complex.IsNear.subLitP qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 14601757734198299769 900719925474099200 3244255165811900204849 ep59 Bool.false 45313034856280607151 1801439850948198400 10652709977144467127933

noncomputable def ep62 := nat_lit 87091997672207460797227892289306624

noncomputable def ep63 := nat_lit 11216357186528036442344483408838656

noncomputable abbrev qz424 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz403 := qz424

noncomputable abbrev qz263 := (@HSub.hSub Complex Complex Complex qz397 qz398 qz403)

noncomputable abbrev qz264 := (Complex.log qz398)

noncomputable abbrev qz13 := (@HSub.hSub Complex Complex Complex qz256 (@HMul.hMul Complex Complex Complex qz255 qz263 qz264) qz257)

noncomputable abbrev qz265 := qz403

noncomputable abbrev qz14 := (@HMul.hMul Complex Complex Complex qz255 qz265 ↑qz254)

noncomputable abbrev qz404 := qz421

noncomputable abbrev qz266 := qz404

noncomputable abbrev qz15 := qz266

noncomputable abbrev qz16 := (@instHMul Nat instMulNat)

noncomputable abbrev qz405 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz267 := qz405

noncomputable abbrev qz17 := qz267

noncomputable abbrev qz18 := qz257

noncomputable abbrev qz268 := (@instHSub Int Int.instSub)

noncomputable abbrev qz19 := qz268

noncomputable abbrev qz269 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz20 := qz269

noncomputable abbrev qz270 := (@instHMul Int Int.instMul)

noncomputable abbrev qz21 := qz270

noncomputable abbrev qz271 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz22 := qz271

noncomputable def ep64 := @Enclosure.Complex.IsNear.of_eq qz7 (@HAdd.hAdd Complex Complex Complex qz8 (@HAdd.hAdd Complex Complex Complex qz8 qz13 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k)))))) Bool.true 14601757734198299769

noncomputable def ep65 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz8 qz13 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) Bool.true 14602617333314997369 900719925474099200

noncomputable def ep66 := nat_lit 7839258991562094785832419328

noncomputable def ep67 := nat_lit 1216362517438957924453554585600

noncomputable def ep68 := @ep65 3168162719855438051 9881200000000000000000 Bool.false 45323606015195728303 1801439850948198400 1733500000487118457 9881200000000000000000 Bool.false 512361 536870912 3 536870912 Bool.true 157522543 26843545600 2767 80530636800 Bool.true ep66 14601757734198299769 900719925474099200 3244255165811900204849 ep59 Bool.false ep67

noncomputable def ep69 := @Enclosure.Complex.IsNear.addLitP qz13 qz14 Bool.true 15430315942809422969 900719925474099200 2942000000128875551 9881200000000000000000

noncomputable def ep70 := @ep69 Bool.false 45323606015195728303 1801439850948198400 1733500000487118457 9881200000000000000000 Bool.false 60223 65536 3 131072 Bool.false 0 1 0 1 Bool.true 956997129556131667574784 14602617333314997369 900719925474099200 3168162719855438051 9881200000000000000000 Bool.false 45323606015195728303 45323606015195728303 1801439850948198400

noncomputable abbrev qz23 := (@HMul.hMul Complex Complex Complex qz255 qz263 qz264)

noncomputable def ep71 := @Enclosure.Complex.IsNear.subLitP qz23 qz18 Bool.true 13403696110492699769 900719925474099200 2942000000128875551 9881200000000000000000 Bool.false 70246526353064053167

noncomputable def ep72 := @ep71 1801439850948198400 1733500000487118457 9881200000000000000000 Bool.false 9000 4000 0 1 Bool.false 55340 4000 0 1 Bool.true 61721263771237691876000 15430315942809422969 900719925474099200 2942000000128875551 9881200000000000000000 Bool.false 181294424060782913212000 45323606015195728303 1801439850948198400 1733500000487118457 9881200000000000000000

noncomputable abbrev qz24 := qz263

noncomputable abbrev qz25 := qz264

noncomputable def ep73 := @Enclosure.Complex.IsNear.mul qz24 qz25 Bool.true 13403696110492699769 900719925474099200 2942000000128875551 9881200000000000000000 Bool.false 70246526353064053167 1801439850948198400 1733500000487118457

noncomputable abbrev qz26 := (Complex.re qz263)

noncomputable abbrev qz27 := (Complex.re qz264)

noncomputable abbrev qz28 := (Complex.im qz263)

noncomputable abbrev qz29 := (Complex.im qz264)

noncomputable def ep74 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz26 qz27) (@HMul.hMul Real Real Real qz0 qz28 qz29) 166468952685448007 36028797018963968 500000000172921 28232000000000000000 2195677490953612493 112589990684262400

noncomputable def ep75 := nat_lit 60364880808602289260044489456615424

noncomputable def ep76 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz27 7000 4000 0 1 23781278955064001 9007199254740992 500000000172921 49406000000000000000

noncomputable def ep77 := @Enclosure.Complex.IsNear.re_isNear qz24 Bool.false 7000 4000 0 1 Bool.false 55340 4000 0 1

noncomputable abbrev qz272 := (Enclosure.sfrac Bool.false 55340 4000)

noncomputable abbrev qz30 := qz272

noncomputable def ep78 := @Enclosure.Complex.IsNear.of_eq qz24 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz30) Bool.false 7000 4000 0 1 Bool.false 55340 4000 0

noncomputable abbrev qz273 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz31 := (Complex.log (Complex.mk qz273 qz272))

noncomputable def ep79 := @Enclosure.Complex.IsNear.of_eq qz25 qz31 Bool.false 23781278955064001 9007199254740992 500000000172921 49406000000000000000 Bool.false 793522765071779 562949953421312 1000000000024703 49406000000000000000

noncomputable def ep80 := nat_lit 2055674171640608507139442628641918122726071930880000000000000

noncomputable def ep81 := nat_lit 31353946953738333341578587171935170706358398976000000000000

noncomputable def ep82 := nat_lit 25930008341728104069528937153096611763875840000000000000

noncomputable def ep83 := BSN.log_dyadic_bound 1095515600 5191515600 4 3 ep80 131072 49406 ep81 ep82 56161 6287031200 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 1095515600) (BSN.artanhQ 5191515600) 0 3 ep81 ep80 ep82 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz32 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz33 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz274 := (Real.log (Enclosure.sfrac Bool.false 3143515600 16000000))

noncomputable abbrev qz275 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep84 := @Enclosure.Real.IsNear.mulLit_ff qz32 qz274 1 2 0 1 23781278955064001 4503599627370496 500000000172921 24703000000000000000 23781278955064001 9007199254740992 500000000172921 49406000000000000000 qz33 (BSN.isNear_log_sfrac 3143515600 16000000 23781278955064001 4503599627370496 500000000172921 24703000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3143515600) qz275)) Bool.false 24936478361585189912576 4722366482869645213696 1000000000345842 49406000000000000000 23781278955064001 4503599627370496 500000000172921 24703000000000000000 (BSN.log_rat_reduce_isNear 3143515600 16000000 7 6287031200 4096000000 56161 131072 24973259072661432 36028797018963968 49406 1000000000000000 rfl rfl rfl rfl (ep83 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep85 := BSN.arctan_dyadic_bound_f 9000 55340 2 1 131072 49406 6561000000000000 46895009001216800000 6561000000000000 19683000000000000 65653012601703520000 19683000000000000 21131 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 55340) 0 1 6561000000000000 46895009001216800000 6561000000000000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.arctanOddP 9000) (BSN.arctanOddQ 55340) 0 1 19683000000000000 65653012601703520000 19683000000000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz249 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz35 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz276 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 55340)))

noncomputable def ep86 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz276 884279719003555 562949953421312 1 2000000000000000 21131 131072 1 49406 104008615863488217088 793522765071779 562949953421312 1000000000024703 49406000000000000000 qz35 (ep85 rfl) rfl rfl

noncomputable abbrev qz36 := (Complex.mk qz273 qz272)

noncomputable abbrev qz37 := qz260

noncomputable abbrev qz277 := (@Eq.refl Real qz401)

noncomputable abbrev qz38 := qz277

noncomputable abbrev qz278 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 55340) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep87 := @Enclosure.Complex.IsNear.re_isNear qz25 Bool.false 23781278955064001 9007199254740992 500000000172921 49406000000000000000 Bool.false 793522765071779 562949953421312 1000000000024703 49406000000000000000 (ep79 (@congrArg Complex Complex qz18 qz36 Complex.log (BSN.w_shift_mk qz37 Bool.false 27670 1000 2 qz38 rfl)) (@Enclosure.Complex.IsNear.of_parts qz31 Bool.false 23781278955064001 9007199254740992 500000000172921 49406000000000000000 Bool.false 793522765071779 562949953421312 1000000000024703 49406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz31) (@HMul.hMul Real Real Real qz0 qz32 qz274) Bool.false 23781278955064001 9007199254740992 500000000172921 49406000000000000000 (Enclosure.clog_re_eq 9000 55340 4000 3143515600 16000000 rfl rfl rfl) (ep84 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz31) qz278 Bool.false 793522765071779 562949953421312 1000000000024703 49406000000000000000 (Enclosure.clog_im_eq 9000 55340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz278 (@HSub.hSub Real Real Real qz5 qz34 qz276) Bool.false 793522765071779 562949953421312 1000000000024703 49406000000000000000 (BSN.arctan_recip 55340 9000 rfl rfl) ep86))))

noncomputable def ep88 := @Enclosure.Real.IsNear.mulLit_ff qz28 qz29 55340 4000 0 1 793522765071779 562949953421312 1000000000024703 49406000000000000000

noncomputable def ep89 := @Enclosure.Complex.IsNear.im_isNear qz24 Bool.false 7000 4000 0 1 Bool.false 55340 4000 0 1

noncomputable def ep90 := @Enclosure.Complex.IsNear.im_isNear qz25 Bool.false 23781278955064001 9007199254740992 500000000172921 49406000000000000000 Bool.false 793522765071779 562949953421312 1000000000024703 49406000000000000000 (ep79 (@congrArg Complex Complex qz18 qz36 Complex.log (BSN.w_shift_mk qz37 Bool.false 27670 1000 2 qz38 rfl)) (@Enclosure.Complex.IsNear.of_parts qz31 Bool.false 23781278955064001 9007199254740992 500000000172921 49406000000000000000 Bool.false 793522765071779 562949953421312 1000000000024703 49406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz31) (@HMul.hMul Real Real Real qz0 qz32 qz274) Bool.false 23781278955064001 9007199254740992 500000000172921 49406000000000000000 (Enclosure.clog_re_eq 9000 55340 4000 3143515600 16000000 rfl rfl rfl) (ep84 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz31) qz278 Bool.false 793522765071779 562949953421312 1000000000024703 49406000000000000000 (Enclosure.clog_im_eq 9000 55340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz278 (@HSub.hSub Real Real Real qz5 qz34 qz276) Bool.false 793522765071779 562949953421312 1000000000024703 49406000000000000000 (BSN.arctan_recip 55340 9000 rfl rfl) ep86))))

noncomputable abbrev qz279 := (Enclosure.Real.IsNear.const Bool.false 55340 4000)

noncomputable abbrev qz39 := (@ep78 1 (BSN.w_sub_half_mk qz260 Bool.false 27670 1000 2 qz277 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz272 Bool.false 7000 4000 0 1 Bool.false 55340 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz279))

noncomputable def ep91 := @ep74 2767000000068353201 9881200000000000000000 ep75 13403696110492699769 900719925474099200 2942000000128875551 9881200000000000000000 (@ep76 166468952685448007 36028797018963968 500000000172921 28232000000000000000 (ep77 qz39) ep87 rfl) (@ep88 2195677490953612493 112589990684262400 2767000000068353201 9881200000000000000000 (ep89 qz39) ep90 rfl) rfl

noncomputable def ep92 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz26 qz29) (@HMul.hMul Real Real Real qz0 qz28 qz27) 5554659355502453 2251799813685248 1000000000024703 28232000000000000000 65802798868662090767 1801439850948198400

noncomputable def ep93 := nat_lit 158181114953865498588857094075580416

noncomputable def ep94 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz29 7000 4000 0 1 793522765071779 562949953421312 1000000000024703 49406000000000000000

noncomputable def ep95 := @Enclosure.Real.IsNear.mulLit_ff qz28 qz27 55340 4000 0 1 23781278955064001 9007199254740992 500000000172921 49406000000000000000

noncomputable def ep96 := @ep92 1383500000478472407 9881200000000000000000 ep93 70246526353064053167 1801439850948198400 1733500000487118457 9881200000000000000000 (@ep94 5554659355502453 2251799813685248 1000000000024703 28232000000000000000 (ep77 qz39) ep90 rfl) (@ep95 65802798868662090767 1801439850948198400 1383500000478472407 9881200000000000000000 (ep89 qz39) ep87 rfl) rfl

noncomputable def ep97 := @Enclosure.Complex.IsNear.of_eq qz18 qz36 Bool.false 9000 4000 0 1 Bool.false 55340 4000 0 1 (BSN.w_shift_mk qz37 Bool.false 27670 1000 2 qz38 rfl)

noncomputable abbrev qz280 := (ep97 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 55340 4000) Bool.false 9000 4000 0 1 Bool.false 55340 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 55340 4000)))

noncomputable abbrev qz40 := qz280

noncomputable def ep98 := ep72 (@ep73 9881200000000000000000 (ep91 rfl) (ep96 rfl)) qz40 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz41 := qz265

noncomputable abbrev qz42 := (Complex.im ↑qz254)

noncomputable def ep99 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz41) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz41) qz42) 60223 65536 3 131072 0 1 0 1 60223 60223

noncomputable def ep100 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz41) (Complex.re ↑qz3) 1 2 0 1 60223 32768 3 65536 60223 65536 3 131072

noncomputable abbrev qz281 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz282 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz43 := (@Enclosure.Complex.IsNear.of_eq qz265 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz281) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz281 Bool.false 1 2 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 2) qz282))

noncomputable def ep101 := ep100 (@Enclosure.Complex.IsNear.re_isNear qz41 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz43) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 60223 32768 3 65536 (Complex.ofReal_re qz3) EMRow04.d4)

noncomputable def ep102 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz41) qz42 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable abbrev qz44 := qz281

noncomputable abbrev qz45 := qz282

noncomputable def ep103 := ep102 (@Enclosure.Complex.IsNear.im_isNear qz41 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz43) (@Enclosure.Real.IsNear.of_eq qz42 qz44 Bool.false 0 1 0 1 (@Eq.trans Real qz42 (0 : Real) qz44 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz45)

noncomputable def ep104 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz41) qz42) (@HMul.hMul Real Real Real qz0 (Complex.im qz41) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep105 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz41) qz42 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep106 := ep105 (@Enclosure.Complex.IsNear.re_isNear qz41 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz43) (@Enclosure.Real.IsNear.of_eq qz42 qz44 Bool.false 0 1 0 1 (@Eq.trans Real qz42 (0 : Real) qz44 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz45)

noncomputable def ep107 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz41) (Complex.re ↑qz3) 0 1 0 1 60223 32768 3 65536 0 1 0 1

noncomputable def ep108 := ep107 (@Enclosure.Complex.IsNear.im_isNear qz41 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz43) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 60223 32768 3 65536 (Complex.ofReal_re qz3) EMRow04.d4)

noncomputable def ep109 := @ep70 1733500000487118457 9881200000000000000000 (ep98 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz41 (↑qz3) Bool.false 60223 65536 3 131072 Bool.false 0 1 0 1 (@ep99 65536 3 131072 (ep101 rfl) (ep103 rfl) rfl rfl) (@ep104 1 0 1 (ep106 rfl) (ep108 rfl) rfl rfl))

noncomputable abbrev qz46 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz283 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz47 := (@HMul.hMul Complex Complex Complex qz255 (@HMul.hMul Complex Complex Complex qz255 (2 : Complex) qz283) (@HSub.hSub Complex Complex Complex qz256 (@HMul.hMul Complex Complex Complex qz255 (2 : Complex) qz283) (1 : Complex)))

noncomputable abbrev qz284 := (@HPow.hPow Complex Int Complex qz405 qz398 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz48 := qz284

noncomputable def ep110 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) qz48)) Bool.false 512361 536870912 3 536870912

noncomputable def ep111 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) qz48) Bool.false 0 1 0 1 Bool.false

noncomputable def ep112 := @ep111 0 1 0 1 Bool.false 512361 536870912 3 536870912 Bool.true 157522543 26843545600 2767 80530636800 Bool.false 512361 512361 536870912 3 536870912 Bool.true 157522543 157522543 26843545600 2767

noncomputable def ep113 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz44 qz44) Bool.false 0 1 0 1 Bool.false

noncomputable def ep114 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) qz48 Bool.false 512361 536870912 3 536870912 Bool.true 157522543 26843545600 2767 80530636800

noncomputable abbrev qz49 := (Complex.re qz284)

noncomputable abbrev qz50 := (Complex.im qz284)

noncomputable def ep115 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz49) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz50) 512361 536870912 3 536870912 0 1 0

noncomputable def ep116 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz49 1 12 0 1 1537083 134217728 9 134217728 512361

noncomputable def ep117 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz44) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz285 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz44 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz45)

noncomputable def ep118 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep117 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz285)

noncomputable def ep119 := @Enclosure.Complex.IsNear.re_isNear qz48 Bool.false 1537083 134217728 9 134217728 Bool.true 472567629 6710886400 2767 6710886400

noncomputable abbrev qz406 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz286 := (@HPow.hPow Complex Nat Complex qz406 qz398 1)

noncomputable abbrev qz51 := (@Inv.inv Complex Complex.instInv qz286)

noncomputable def ep120 := @Enclosure.Complex.IsNear.of_eq qz48 qz51 Bool.false 1537083 134217728 9 134217728 Bool.true 472567629 6710886400 2767

noncomputable def ep121 := @Enclosure.Complex.IsNear.of_parts qz51 Bool.false 1537083 134217728 9 134217728 Bool.true 472567629 6710886400 2767

noncomputable abbrev qz52 := (Complex.re qz286)

noncomputable abbrev qz53 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz54 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz55 := qz286

noncomputable def ep122 := @Enclosure.Real.IsNear.mulLit_ff qz52 (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz55)) 9000 4000 0 1 170787 33554432 1 33554432

noncomputable def ep123 := @Enclosure.Complex.IsNear.re_isNear qz55 Bool.false 9000 4000 0 1 Bool.false 55340 4000 0 1

noncomputable def ep124 := @Enclosure.Complex.IsNear.of_eq qz55 qz18 Bool.false 9000 4000 0 1 Bool.false 55340 4000 0

noncomputable def ep125 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz55)) Bool.false 170787 33554432 1 33554432 170787 33554432 1

noncomputable abbrev qz56 := (@instHAdd Real Real.instAdd)

noncomputable abbrev qz57 := (Complex.im qz286)

noncomputable def ep126 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz55) (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 qz52 qz52) (@HMul.hMul Real Real Real qz0 qz57 qz57)) Bool.false 7858789 40000 0 1

noncomputable def ep127 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz52 qz52) (@HMul.hMul Real Real Real qz0 qz57 qz57) 81 16 0 1 7656289 40000

noncomputable def ep128 := @Enclosure.Real.IsNear.mulLit_ff qz52 qz52 9000 4000 0 1 9000 4000 0 1

noncomputable def ep129 := @Enclosure.Real.IsNear.mulLit_ff qz57 qz57 55340 4000 0 1 55340 4000 0 1

noncomputable def ep130 := @Enclosure.Complex.IsNear.im_isNear qz55 Bool.false 9000 4000 0 1 Bool.false 55340 4000 0 1

noncomputable abbrev qz58 := (ep123 (@ep124 1 (BSN.pow_one_c qz257) qz280))

noncomputable abbrev qz59 := (ep130 (@ep124 1 (BSN.pow_one_c qz257) qz280))

noncomputable def ep131 := @ep127 0 1 125740624 7858789 40000 0 1 (@ep128 81 16 0 1 qz58 qz58 rfl) (@ep129 7656289 40000 0 1 qz59 qz59 rfl)

noncomputable def ep132 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz55) 7858789 40000 0 1 85393 85394 16777216 (ep126 (Enclosure.Complex.normSq_eq_mul_add_mul qz55) (ep131 rfl rfl)) rfl

noncomputable def ep133 := @Enclosure.Real.IsNear.of_eq (Complex.re qz51) (@HMul.hMul Real Real Real qz0 qz52 (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz55))) Bool.false 1537083 134217728 9 134217728 (Enclosure.Complex.inv_re_eq_mul qz55) (@ep122 1537083 134217728 9 134217728 qz58 (@ep125 33554432 (ep132 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep134 := @Enclosure.Real.IsNear.of_eq (Complex.im qz51) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz57) (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz55))) Bool.true 472567629 6710886400 2767 6710886400 (Enclosure.Complex.inv_im_eq_mul qz55)

noncomputable def ep135 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz57) (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz55)) 55340 4000 0 1 170787 33554432 1

noncomputable def ep136 := @ep135 33554432 472567629 6710886400 2767 6710886400 (@Enclosure.Real.IsNear.neg qz57 Bool.false 55340 4000 0 1 qz59) (@ep125 33554432 (ep132 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep137 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz50 0 1 0 1 472567629 6710886400 2767 6710886400 0

noncomputable def ep138 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep117 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz285)

noncomputable def ep139 := @Enclosure.Complex.IsNear.im_isNear qz48 Bool.false 1537083 134217728 9 134217728 Bool.true 472567629 6710886400 2767 6710886400

noncomputable abbrev qz60 := (@ep120 6710886400 (BSN.zpow_one_sub_two_mul qz257 1 1 rfl rfl) (@ep121 6710886400 ep133 (ep134 ep136)))

noncomputable def ep140 := @ep115 1 512361 512361 536870912 3 536870912 (@ep116 536870912 3 536870912 ep118 (ep119 qz60) rfl) (@ep137 1 0 1 ep138 (ep139 qz60) rfl) rfl

noncomputable def ep141 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz50) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz49) 157522543 26843545600 2767 80530636800 0 1 0

noncomputable def ep142 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz50 1 12 0 1 472567629 6710886400 2767 6710886400 157522543

noncomputable def ep143 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz49 0 1 0 1 1537083 134217728 9 134217728 0

noncomputable def ep144 := @ep141 1 157522543 157522543 26843545600 2767 80530636800 (@ep142 26843545600 2767 80530636800 ep118 (ep139 qz60) rfl) (@ep143 1 0 1 ep138 (ep119 qz60) rfl) rfl

noncomputable abbrev qz61 := (@Enclosure.Complex.IsNear.mk qz281 qz281 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz282 qz282)

noncomputable def ep145 := @ep112 80530636800 (@ep113 0 1 0 1 (BSN.stirling_sum_base qz18) qz61) (ep114 (ep140 rfl) (ep144 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep146 := @ep68 45313034856280607151 1801439850948198400 10652709977144467127933 ep55 (ep109 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep110 Bool.true 157522543 26843545600 2767 80530636800 (BSN.stirling_sum_succ qz18 0 1 rfl) (ep145 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep147 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz37 2) Bool.false 23682752405293761 4503599627370496 500000000172921 24703000000000000000 Bool.false 853832695842211 281474976710656

noncomputable abbrev qz62 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz258 qz259 qz283))

noncomputable def ep148 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz37 2) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz37 1) qz62) Bool.false 23682752405293761 4503599627370496 500000000172921 24703000000000000000 Bool.false 853832695842211 281474976710656 1000000000024703 24703000000000000000

noncomputable def ep149 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz37 1) qz62 Bool.false 23665177399118529 9007199254740992 500000000172921 49406000000000000000 Bool.false 874109236446627 562949953421312 1000000000024703 49406000000000000000 Bool.false

noncomputable def ep150 := nat_lit 426630539630354799600715457101824

noncomputable def ep151 := nat_lit 961330152707931877233513201664

noncomputable abbrev qz63 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz258 qz259 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep152 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz37 1) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz37 0) qz63) Bool.false 23665177399118529 9007199254740992 500000000172921 49406000000000000000 Bool.false 874109236446627 562949953421312 1000000000024703 49406000000000000000

noncomputable def ep153 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz37 0) qz63 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz287 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz30))

noncomputable def ep154 := @Enclosure.Complex.IsNear.of_eq qz63 qz287 Bool.false 23665177399118529 9007199254740992 500000000172921 49406000000000000000 Bool.false 874109236446627 562949953421312 1000000000024703 49406000000000000000

noncomputable def ep155 := nat_lit 1872782931211029648364340058519821025718967930880000000000000

noncomputable def ep156 := nat_lit 25239944615390075133983859487111560318697598976000000000000

noncomputable def ep157 := nat_lit 16451702774273028581668499496426067891875840000000000000

noncomputable def ep158 := BSN.log_dyadic_bound 1015515600 5111515600 4 3 ep155 131072 49406 ep156 ep157 52782 6127031200 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 1015515600) (BSN.artanhQ 5111515600) 0 3 ep156 ep155 ep157 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep159 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 3063515600 16000000)) 1 2 0 1 23665177399118529 4503599627370496 500000000172921 24703000000000000000 23665177399118529 9007199254740992 500000000172921 49406000000000000000 qz33 (BSN.isNear_log_sfrac 3063515600 16000000 23665177399118529 4503599627370496 500000000172921 24703000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3063515600) qz275)) Bool.false 24814737056458110664704 4722366482869645213696 1000000000345842 49406000000000000000 23665177399118529 4503599627370496 500000000172921 24703000000000000000 (BSN.log_rat_reduce_isNear 3063515600 16000000 7 6127031200 4096000000 52782 131072 24973259072661432 36028797018963968 49406 1000000000000000 rfl rfl rfl rfl (ep158 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep160 := BSN.arctan_dyadic_bound_f 1000 55340 1 0 131072 49406 0 1 1 0 1 1 2368 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 55340) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 55340) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz288 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz289 := (@Nat.cast Real Real.instNatCast 55340)

noncomputable def ep161 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz288 qz289)) 884279719003555 562949953421312 1 2000000000000000 2368 131072 1 49406 114571245839532294144 874109236446627 562949953421312 1000000000024703 49406000000000000000 qz35 (ep160 rfl) rfl rfl

noncomputable abbrev qz64 := (@HAdd.hAdd Complex Complex Complex qz258 qz259 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz290 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz30)

noncomputable def ep162 := @ep153 23665177399118529 9007199254740992 500000000172921 49406000000000000000 Bool.false 874109236446627 562949953421312 1000000000024703 49406000000000000000 Bool.false 23665177399118529 23665177399118529 9007199254740992 500000000172921 49406000000000000000 Bool.false 874109236446627 874109236446627 562949953421312 1000000000024703 49406000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz37 0) (Complex.mk qz44 qz44) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz37) qz61) (ep154 (@congrArg Complex Complex qz64 qz290 Complex.log (BSN.w_shift_mk qz37 Bool.false 27670 1000 0 qz38 rfl)) (@Enclosure.Complex.IsNear.of_parts qz287 Bool.false 23665177399118529 9007199254740992 500000000172921 49406000000000000000 Bool.false 874109236446627 562949953421312 1000000000024703 49406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz287) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 3063515600 16000000))) Bool.false 23665177399118529 9007199254740992 500000000172921 49406000000000000000 (Enclosure.clog_re_eq 1000 55340 4000 3063515600 16000000 rfl rfl rfl) (ep159 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz287) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz289 qz288)) Bool.false 874109236446627 562949953421312 1000000000024703 49406000000000000000 (Enclosure.clog_im_eq 1000 55340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz289 qz288)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz288 qz289))) Bool.false 874109236446627 562949953421312 1000000000024703 49406000000000000000 (BSN.arctan_recip 55340 1000 rfl rfl) ep161)))) rfl rfl

noncomputable abbrev qz291 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz30))

noncomputable def ep163 := @Enclosure.Complex.IsNear.of_eq qz62 qz291 Bool.false 23700327411468993 9007199254740992 500000000172921 49406000000000000000 Bool.false 833556155237795 562949953421312 1000000000024703 49406000000000000000

noncomputable def ep164 := nat_lit 1926165571094312575449936751605578889541099130880000000000000

noncomputable def ep165 := nat_lit 26972333878290649150512377853279033578995838976000000000000

noncomputable def ep166 := nat_lit 18926805801561563279149058683132191053475840000000000000

noncomputable def ep167 := BSN.log_dyadic_bound 1039515600 5135515600 4 3 ep164 131072 49406 ep165 ep166 53805 6175031200 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 1039515600) (BSN.artanhQ 5135515600) 0 3 ep165 ep164 ep166 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep168 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 3087515600 16000000)) 1 2 0 1 23700327411468993 4503599627370496 500000000172921 24703000000000000000 23700327411468993 9007199254740992 500000000172921 49406000000000000000 qz33 (BSN.isNear_log_sfrac 3087515600 16000000 23700327411468993 4503599627370496 500000000172921 24703000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3087515600) qz275)) Bool.false 24851594515808510803968 4722366482869645213696 1000000000345842 49406000000000000000 23700327411468993 4503599627370496 500000000172921 24703000000000000000 (BSN.log_rat_reduce_isNear 3087515600 16000000 7 6175031200 4096000000 53805 131072 24973259072661432 36028797018963968 49406 1000000000000000 rfl rfl rfl rfl (ep167 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep169 := BSN.arctan_dyadic_bound_f 5000 55340 1 0 131072 49406 0 1 1 0 1 1 11810 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 55340) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 55340) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz292 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep170 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz292 qz289)) 884279719003555 562949953421312 1 2000000000000000 11810 131072 1 49406 109255872379328266240 833556155237795 562949953421312 1000000000024703 49406000000000000000 qz35 (ep169 rfl) rfl rfl

noncomputable abbrev qz65 := (@HAdd.hAdd Complex Complex Complex qz258 qz259 qz283)

noncomputable abbrev qz293 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz30)

noncomputable def ep171 := @ep149 23700327411468993 9007199254740992 500000000172921 49406000000000000000 Bool.false 833556155237795 562949953421312 1000000000024703 49406000000000000000 Bool.false ep150 23682752405293761 4503599627370496 500000000172921 24703000000000000000 Bool.false ep151 853832695842211 281474976710656 1000000000024703 24703000000000000000 (ep152 (BSN.log_sum_c_succ qz37 0 1 rfl) (ep162 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep163 (@congrArg Complex Complex qz65 qz293 Complex.log (BSN.w_shift_mk qz37 Bool.false 27670 1000 1 qz38 rfl)) (@Enclosure.Complex.IsNear.of_parts qz291 Bool.false 23700327411468993 9007199254740992 500000000172921 49406000000000000000 Bool.false 833556155237795 562949953421312 1000000000024703 49406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz291) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 3087515600 16000000))) Bool.false 23700327411468993 9007199254740992 500000000172921 49406000000000000000 (Enclosure.clog_re_eq 5000 55340 4000 3087515600 16000000 rfl rfl rfl) (ep168 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz291) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz289 qz292)) Bool.false 833556155237795 562949953421312 1000000000024703 49406000000000000000 (Enclosure.clog_im_eq 5000 55340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz289 qz292)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz292 qz289))) Bool.false 833556155237795 562949953421312 1000000000024703 49406000000000000000 (BSN.arctan_recip 55340 5000 rfl rfl) ep170)))) rfl rfl

noncomputable def ep172 := @ep61 ep55 Bool.false 23682752405293761 4503599627370496 500000000172921 24703000000000000000 Bool.false 853832695842211 281474976710656 1000000000024703 24703000000000000000 Bool.true ep62 19338308215257051969 900719925474099200 3449055165882728646449 ep59 Bool.false ep63 39848505602890456751 1801439850948198400 13110309977205177220733 ep55 (@ep64 900719925474099200 3244255165811900204849 ep59 Bool.false 45313034856280607151 1801439850948198400 10652709977144467127933 ep55 (BSN.logGammaStirling_unfold 1 qz18) (ep146 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep147 1000000000024703 24703000000000000000 (BSN.log_sum_c_eq qz37 2) (ep148 (BSN.log_sum_c_succ qz37 1 2 rfl) (ep171 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz66 := (@HDiv.hDiv Real Real Real qz253 qz260 (2 : Real))

noncomputable def ep173 := @Enclosure.Real.IsNear.mulLit_ff qz66 (Real.log Real.pi) 27670 2000 0 1 75021 65536 1 32768 207583107 13107200 2767 6553600 (@Enclosure.Real.IsNear.of_eq qz66 (Enclosure.sfrac Bool.false 27670 2000) Bool.false 27670 2000 0 1 (BSN.t_half_eq qz37 Bool.false 27670 1000 qz38) (Enclosure.Real.IsNear.const Bool.false 27670 2000)) EMRow04.d5 rfl

noncomputable def ep174 := @ep57 2767 6553600 ep58 11318500618344259247 1801439850948198400 38742760352205177220733 ep55 (@ep60 13110309977205177220733 ep55 (ep172 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep173 rfl rfl

noncomputable def ep175 := nat_lit 497140415056404234682128590279333722365785711425011746362913801096767905

noncomputable def ep176 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080

noncomputable def ep177 := nat_lit 998456871996347343458926812708431666508244176128389756812449109879201

noncomputable def ep178 := nat_lit 1300417871164493195135212807320536573974139706018441942772792180504111521

noncomputable def ep179 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800

noncomputable abbrev qz294 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz295 := (BSN.sinOddQ 268435456)

noncomputable def ep180 := BSN.sin_dyadic_bound_f 421615107 268435456 3 2 131072 49455 ep175 ep176 ep177 ep178 ep179 ep177 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 421615107) qz294 0 2 ep175 ep176 ep177 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 421615107) qz295 0 2 ep178 ep179 ep177 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz67 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep181 := @ep54 32768 Bool.false 131071 131072 1 24703 (@ep56 823529 131072 21 32768 ep174 rfl) (Enclosure.sfrac_false_div 823529 131072) (BSN.cos_reduce3 qz262 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29668525620069828395008) qz67) 226375608064910080 72057594037927936 Bool.false 131071 131072 0 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q3 823529 131072 226375608064910080 72057594037927936 0 29668525620069828395008 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131071 131072 29668525620069828395008 18889465931478580854784 421615107 268435456 49455 49406 (ep180 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep182 := nat_lit 11701247260454929878220800

noncomputable abbrev qz407 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz296 := qz407

noncomputable abbrev qz68 := qz296

noncomputable abbrev qz408 := (@Neg.neg Complex Complex.instNeg qz423)

noncomputable abbrev qz297 := qz408

noncomputable abbrev qz69 := qz297

noncomputable abbrev qz298 := (@HPow.hPow Complex Complex Complex qz407 (@Nat.cast Complex Complex.instNatCast 6) qz408)

noncomputable abbrev qz70 := qz298

noncomputable abbrev qz299 := (@Nat.cast Complex Complex.instNatCast 6)

noncomputable abbrev qz71 := (@HAdd.hAdd Complex Complex Complex qz258 (@HDiv.hDiv Complex Complex Complex qz266 qz299 (@HSub.hSub Complex Complex Complex qz256 qz261 (1 : Complex))) qz265)

noncomputable abbrev qz72 := (@instHSub Nat instSubNat)

noncomputable abbrev qz300 := qz406

noncomputable abbrev qz73 := qz300

noncomputable abbrev qz74 := qz299

noncomputable def ep183 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz11 1 6) (@HAdd.hAdd Complex Complex Complex qz8 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 6, @HPow.hPow Complex Complex Complex qz68 (@Nat.cast Complex Complex.instNatCast n) qz69) (@HMul.hMul Complex Complex Complex qz4 qz70 (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) Bool.false 271303065653089262231 94735435052057886720 408718558890826232969

noncomputable def ep184 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 6, @HPow.hPow Complex Complex Complex qz68 (@Nat.cast Complex Complex.instNatCast n) qz69) (@HMul.hMul Complex Complex Complex qz4 qz70 (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) Bool.false 47219485369 17179869184 1120930126371 424394308452352

noncomputable def ep185 := nat_lit 1671606751493561411174400

noncomputable def ep186 := nat_lit 4660951177138237050603651989504

noncomputable def ep187 := nat_lit 154564763571808232807738638336

noncomputable def ep188 := @ep184 Bool.true 4779043701 17179869184 1116315062505 424394308452352 Bool.false 10919331559663400711 94735435052057886720 6445706130911698847 19665961782277193072640 Bool.false 17356361528813351051 94735435052057886720 546705023315203480693 ep185 Bool.false ep186 271303065653089262231 94735435052057886720 408718558890826232969 137661732475940351508480 Bool.true ep187 8996853347158073029 94735435052057886720

noncomputable def ep189 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 6, @HPow.hPow Complex Complex Complex qz68 (@Nat.cast Complex Complex.instNatCast n) qz69) (BSN.headSumC qz11 6) Bool.false 47219485369 17179869184 1120930126371 424394308452352 Bool.true 4779043701 17179869184 1116315062505

noncomputable abbrev qz75 := (BSN.headSumC qz261 5)

noncomputable abbrev qz76 := (@HPow.hPow Complex Complex Complex qz296 (@Nat.cast Complex Complex.instNatCast 5) qz297)

noncomputable def ep190 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz11 6) (@HAdd.hAdd Complex Complex Complex qz8 qz75 qz76) Bool.false 47219485369 17179869184 1120930126371 424394308452352 Bool.true 4779043701 17179869184 1116315062505 424394308452352

noncomputable def ep191 := @Enclosure.Complex.IsNear.addLitP qz75 qz76 Bool.false 20336364245 8589934592 448088978361 212197154226176 Bool.true 758034735 17179869184 892627320423 424394308452352 Bool.false

noncomputable abbrev qz77 := (BSN.headSumC qz261 4)

noncomputable abbrev qz78 := (@HPow.hPow Complex Complex Complex qz296 (@Nat.cast Complex Complex.instNatCast 4) qz297)

noncomputable def ep192 := @Enclosure.Complex.IsNear.of_eq qz75 (@HAdd.hAdd Complex Complex Complex qz8 qz77 qz78) Bool.false 20336364245 8589934592 448088978361 212197154226176 Bool.true 758034735 17179869184 892627320423 424394308452352

noncomputable def ep193 := @Enclosure.Complex.IsNear.addLitP qz77 qz78 Bool.false 16942306595 8589934592 322713392903 212197154226176 Bool.false 1126384965 4294967296 160612703849 106098577113088 Bool.false

noncomputable abbrev qz79 := (BSN.headSumC qz261 3)

noncomputable abbrev qz409 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz301 := qz409

noncomputable abbrev qz80 := (@HPow.hPow Complex Complex Complex qz296 qz301 qz297)

noncomputable def ep194 := @Enclosure.Complex.IsNear.of_eq qz77 (@HAdd.hAdd Complex Complex Complex qz8 qz79 qz80) Bool.false 16942306595 8589934592 322713392903 212197154226176 Bool.false 1126384965 4294967296 160612703849 106098577113088

noncomputable def ep195 := @Enclosure.Complex.IsNear.addLitP qz79 qz80 Bool.false 1792073665 1073741824 5580184353 6631161069568 Bool.true 1966943745 8589934592 176551048507 212197154226176 Bool.false

noncomputable abbrev qz81 := (BSN.headSumC qz261 2)

noncomputable abbrev qz410 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz302 := qz410

noncomputable abbrev qz82 := (@HPow.hPow Complex Complex Complex qz296 qz302 qz297)

noncomputable def ep196 := @Enclosure.Complex.IsNear.of_eq qz79 (@HAdd.hAdd Complex Complex Complex qz8 qz81 qz82) Bool.false 1792073665 1073741824 5580184353 6631161069568 Bool.true 1966943745 8589934592 176551048507 212197154226176

noncomputable def ep197 := @Enclosure.Complex.IsNear.addLitP qz81 qz82 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep198 := @Enclosure.Complex.IsNear.of_eq qz81 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz44) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz11)

noncomputable abbrev qz83 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable abbrev qz303 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz84 := (@HMul.hMul Real Real Real qz249 qz260 qz303)

noncomputable abbrev qz85 := (Real.sin (@HMul.hMul Real Real Real qz249 qz260 qz303))

noncomputable def ep199 := @Enclosure.Complex.IsNear.of_eq qz82 (Complex.mk (@HMul.hMul Real Real Real qz0 qz83 (Real.cos qz84)) (@HMul.hMul Real Real Real qz0 qz83 (@Neg.neg Real Real.instNeg qz85))) Bool.false 718331841 1073741824 5580184353 6631161069568 Bool.true 1966943745 8589934592 176551048507 212197154226176 (BSN.cpow_neg_s_mk qz37 27670 1000 2 qz38 rfl)

noncomputable abbrev qz86 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz304 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep200 := @Enclosure.Real.IsNear.inv_image qz86 185363 131072 1 131072 46340 46342 65536 (@Enclosure.Real.IsNear.of_eq qz86 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2) qz304)) Bool.false 185363 131072 1 131072 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2) qz304)) Bool.false 185363 131072 1 131072 185363 131072 1 131072 (BSN.sqrt_enclosure 2 1 92681 92682 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep201 := BSN.log_dyadic_bound 1 3 6 5 613814355 65536 24703 24381081 945 45426 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep202 := nat_lit 61412963159365318301862893998336

noncomputable def ep203 := nat_lit 124615124604835863084731911901282304

noncomputable def ep204 := nat_lit 1869226869072537946270978678519234560

noncomputable abbrev qz305 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz306 := (BSN.cosOddQ 268435456)

noncomputable def ep205 := BSN.cos_dyadic_bound_f 88524812 268435456 2 1 131072 49455 ep202 ep203 ep202 ep202 ep204 ep202 124008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 88524812) qz305 0 1 ep202 ep203 ep202 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 88524812) qz306 0 1 ep202 ep204 ep202 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz87 := qz303

noncomputable abbrev qz307 := (Enclosure.Real.IsNear.const Bool.false 27670 1000)

noncomputable abbrev qz88 := qz307

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1256937) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz309 := (BSN.isNear_log_sfrac 2 1 45426 65536 1 24703 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 45426 65536 24703 rfl rfl rfl (ep201 rfl)))

noncomputable abbrev qz310 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep206 := @Enclosure.Real.IsNear.cos_image qz84 qz308 Bool.false 1256937 65536 37 32768 Bool.false 124008 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz84 Bool.false 62846871 3276800 2767 2470300 1256937 65536 37 32768 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz87 27670 1000 0 1 45426 65536 1 24703 62846871 3276800 2767 2470300 qz88 qz309 rfl) rfl) (Enclosure.sfrac_false_div 1256937 65536) (BSN.cos_reduce0 qz308 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3114689952798688149504) qz310) 226375608064910080 72057594037927936 Bool.false 124008 131072 3 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q0 1256937 65536 226375608064910080 72057594037927936 3 3114689952798688149504 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 124008 131072 3114689952798688149504 9444732965739290427392 88524812 268435456 49455 49406 (ep205 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep207 := nat_lit 623075623024179315423659559506411520

noncomputable def ep208 := nat_lit 4361529361169255207965616916544880640

noncomputable def ep209 := BSN.sin_dyadic_bound_f 88524812 268435456 2 1 131072 49455 ep202 ep207 ep202 ep202 ep208 ep202 42445 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 88524812) qz294 0 1 ep202 ep207 ep202 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 88524812) qz295 0 1 ep202 ep208 ep202 rfl rfl rfl rfl) rfl rfl

noncomputable def ep210 := @Enclosure.Real.IsNear.sin_image qz84 qz308 Bool.false 1256937 65536 37 32768 Bool.false 42445 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz84 Bool.false 62846871 3276800 2767 2470300 1256937 65536 37 32768 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz87 27670 1000 0 1 45426 65536 1 24703 62846871 3276800 2767 2470300 qz88 qz309 rfl) rfl) (Enclosure.sfrac_false_div 1256937 65536) (BSN.sin_reduce0 qz308 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3114689952798688149504) qz310) 226375608064910080 72057594037927936 Bool.false 42445 131072 3 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q0 1256937 65536 226375608064910080 72057594037927936 3 3114689952798688149504 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 42445 131072 3114689952798688149504 9444732965739290427392 88524812 268435456 49455 49406 (ep209 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz311 := (@Enclosure.Real.IsNear.recentre' qz83 Bool.false 92682 131072 2 131072 46341 65536 1 65536 (ep200 rfl rfl) rfl)

noncomputable def ep211 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz83 (Real.cos qz84)) (@HMul.hMul Real Real Real qz0 qz83 (@Neg.neg Real Real.instNeg qz85)) Bool.false 718331841 1073741824 5580184353 6631161069568 Bool.true 1966943745 8589934592 176551048507 212197154226176 (@Enclosure.Real.IsNear.mulLit_ff qz83 (Real.cos qz84) 46341 65536 1 65536 15501 16384 946779 809467904 718331841 1073741824 5580184353 6631161069568 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz84) Bool.false 124008 131072 946779 809467904 15501 16384 946779 809467904 (ep206 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz83 (@Neg.neg Real Real.instNeg qz85) 46341 65536 1 65536 42445 131072 946779 809467904 1966943745 8589934592 176551048507 212197154226176 qz311 (@Enclosure.Real.IsNear.neg qz85 Bool.false 42445 131072 946779 809467904 (@Enclosure.Real.IsNear.recentre' qz85 Bool.false 42445 131072 946779 809467904 42445 131072 946779 809467904 (ep210 rfl rfl) rfl)) rfl)

noncomputable def ep212 := @ep197 718331841 1073741824 5580184353 6631161069568 Bool.true 1966943745 8589934592 176551048507 212197154226176 Bool.false 1792073665 1792073665 1073741824 5580184353 6631161069568 Bool.true 1966943745 1966943745 8589934592 176551048507 212197154226176 (ep198 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz44 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz45)) (ep199 ep211) rfl rfl

noncomputable abbrev qz312 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz89 := (@Inv.inv Real Real.instInv (Real.sqrt qz312))

noncomputable abbrev qz313 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz90 := (@HMul.hMul Real Real Real qz249 qz260 qz313)

noncomputable abbrev qz91 := (Real.sin (@HMul.hMul Real Real Real qz249 qz260 qz313))

noncomputable def ep213 := @Enclosure.Complex.IsNear.of_eq qz80 (Complex.mk (@HMul.hMul Real Real Real qz0 qz89 (Real.cos qz90)) (@HMul.hMul Real Real Real qz0 qz89 (@Neg.neg Real Real.instNeg qz91))) Bool.false 2605717275 8589934592 144147493607 212197154226176 Bool.false 4219713675 8589934592 144674359191 212197154226176 (BSN.cpow_neg_s_mk qz37 27670 1000 3 qz38 rfl)

noncomputable abbrev qz92 := (Real.sqrt qz312)

noncomputable abbrev qz93 := qz312

noncomputable def ep214 := @Enclosure.Real.IsNear.inv_image qz92 227023 131072 1 131072 37837 37838 65536 (@Enclosure.Real.IsNear.of_eq qz92 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz93 qz304)) Bool.false 227023 131072 1 131072 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz93 qz304)) Bool.false 227023 131072 1 131072 227023 131072 1 131072 (BSN.sqrt_enclosure 3 1 113511 113512 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep215 := BSN.log_dyadic_bound 1 2 9 8 2258332876800 65536 24703 222698787165 2027025 71998 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1) (BSN.artanhQ 2) 0 8 222698787165 2258332876800 2027025 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep216 := nat_lit 486256854316453644583659398850576

noncomputable def ep217 := BSN.sin_dyadic_bound_f 148496574 268435456 2 1 131072 49455 ep216 ep207 ep216 ep216 ep208 ep216 68866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 148496574) qz294 0 1 ep216 ep207 ep216 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 148496574) qz295 0 1 ep216 ep208 ep216 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz94 := qz313

noncomputable abbrev qz314 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3984369) qz12)

noncomputable abbrev qz315 := (BSN.isNear_log_sfrac 3 1 71998 65536 1 24703 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 71998 65536 24703 rfl rfl rfl (ep215 rfl)))

noncomputable def ep218 := @Enclosure.Real.IsNear.cos_image qz90 qz314 Bool.false 3984369 131072 37 32768 Bool.false 68866 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz90 Bool.false 99609233 3276800 2767 2470300 3984369 131072 37 32768 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz94 27670 1000 0 1 71998 65536 1 24703 99609233 3276800 2767 2470300 qz88 qz315 rfl) rfl) (Enclosure.sfrac_false_div 3984369 131072) (BSN.cos_reduce3 qz314 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10449517493215798755328) qz67) 226375608064910080 72057594037927936 Bool.false 68866 131072 4 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q3 3984369 131072 226375608064910080 72057594037927936 4 10449517493215798755328 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 68866 131072 10449517493215798755328 18889465931478580854784 148496574 268435456 49455 49406 (ep217 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep219 := BSN.cos_dyadic_bound_f 148496574 268435456 2 1 131072 49455 ep216 ep203 ep216 ep216 ep204 ep216 111522 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 148496574) qz305 0 1 ep216 ep203 ep216 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 148496574) qz306 0 1 ep216 ep204 ep216 rfl rfl rfl rfl) rfl rfl

noncomputable def ep220 := @Enclosure.Real.IsNear.sin_image qz90 qz314 Bool.false 3984369 131072 37 32768 Bool.true 111522 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz90 Bool.false 99609233 3276800 2767 2470300 3984369 131072 37 32768 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz94 27670 1000 0 1 71998 65536 1 24703 99609233 3276800 2767 2470300 qz88 qz315 rfl) rfl) (Enclosure.sfrac_false_div 3984369 131072) (BSN.sin_reduce3 qz314 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10449517493215798755328) qz67) 226375608064910080 72057594037927936 Bool.false 111522 131072 4 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q3 3984369 131072 226375608064910080 72057594037927936 4 10449517493215798755328 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 111522 131072 10449517493215798755328 18889465931478580854784 148496574 268435456 49455 49406 (ep219 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz316 := (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 75675 131072 1 131072 75675 131072 1 131072 (ep214 rfl rfl) rfl)

noncomputable def ep221 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz89 (Real.cos qz90)) (@HMul.hMul Real Real Real qz0 qz89 (@Neg.neg Real Real.instNeg qz91)) Bool.false 2605717275 8589934592 144147493607 212197154226176 Bool.false 4219713675 8589934592 144674359191 212197154226176 (@Enclosure.Real.IsNear.mulLit_ff qz89 (Real.cos qz90) 75675 131072 1 131072 34433 65536 946779 809467904 2605717275 8589934592 144147493607 212197154226176 qz316 (@Enclosure.Real.IsNear.recentre' (Real.cos qz90) Bool.false 68866 131072 946779 809467904 34433 65536 946779 809467904 (ep218 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz89 (@Neg.neg Real Real.instNeg qz91) 75675 131072 1 131072 55761 65536 946779 809467904 4219713675 8589934592 144674359191 212197154226176 qz316 (@Enclosure.Real.IsNear.neg qz91 Bool.true 55761 65536 946779 809467904 (@Enclosure.Real.IsNear.recentre' qz91 Bool.true 111522 131072 946779 809467904 55761 65536 946779 809467904 (ep220 rfl rfl) rfl)) rfl)

noncomputable def ep222 := @ep195 2605717275 8589934592 144147493607 212197154226176 Bool.false 4219713675 8589934592 144674359191 212197154226176 Bool.false 18191663186082529280 16942306595 8589934592 322713392903 212197154226176 Bool.false 19351146349524418560 1126384965 4294967296 160612703849 106098577113088 (ep196 (BSN.head_sum_c_succ qz11 2 3 rfl rfl) (ep212 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep213 ep221) rfl rfl

noncomputable abbrev qz95 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable abbrev qz317 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz96 := (@HMul.hMul Real Real Real qz249 qz260 qz317)

noncomputable abbrev qz97 := (Real.sin (@HMul.hMul Real Real Real qz249 qz260 qz317))

noncomputable def ep223 := @Enclosure.Complex.IsNear.of_eq qz78 (Complex.mk (@HMul.hMul Real Real Real qz0 qz95 (Real.cos qz96)) (@HMul.hMul Real Real Real qz0 qz95 (@Neg.neg Real Real.instNeg qz97))) Bool.false 1697028825 4294967296 62687792729 106098577113088 Bool.true 5263574595 17179869184 250176505027 424394308452352 (BSN.cpow_neg_s_mk qz37 27670 1000 4 qz38 rfl)

noncomputable abbrev qz98 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable def ep224 := @Enclosure.Real.IsNear.inv_image qz98 262145 131072 1 131072 32767 32768 65536 (@Enclosure.Real.IsNear.of_eq qz98 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4) qz304)) Bool.false 262145 131072 1 131072 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4) qz304)) Bool.false 262145 131072 1 131072 262145 131072 1 131072 (BSN.sqrt_enclosure 4 1 131072 131073 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep225 := nat_lit 753960950911045074462890625

noncomputable def ep226 := nat_lit 117048680082474133384580175

noncomputable def ep227 := BSN.log_dyadic_bound 3 5 12 11 ep225 65536 24703 ep226 431467934736729065175 90852 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 3) (BSN.artanhQ 5) 0 11 ep226 ep225 431467934736729065175 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep228 := nat_lit 982652898306103400820708282947041

noncomputable def ep229 := BSN.cos_dyadic_bound_f 177051673 268435456 2 1 131072 49455 ep228 ep203 ep228 ep228 ep204 ep228 103580 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 177051673) qz305 0 1 ep228 ep203 ep228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 177051673) qz306 0 1 ep228 ep204 ep228 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz99 := qz317

noncomputable abbrev qz318 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5027749) qz12)

noncomputable abbrev qz319 := (BSN.isNear_log_sfrac 4 1 90852 65536 1 24703 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 90852 65536 24703 rfl rfl rfl (ep227 rfl)))

noncomputable def ep230 := @Enclosure.Real.IsNear.cos_image qz96 qz318 Bool.false 5027749 131072 37 32768 Bool.false 103580 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz96 Bool.false 62846871 1638400 2767 2470300 5027749 131072 37 32768 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz99 27670 1000 0 1 90852 65536 1 24703 62846871 1638400 2767 2470300 qz88 qz319 rfl) rfl) (Enclosure.sfrac_false_div 5027749 131072) (BSN.cos_reduce0 qz318 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12458903926382828453888) qz67) 226375608064910080 72057594037927936 Bool.false 103580 131072 6 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q0 5027749 131072 226375608064910080 72057594037927936 6 12458903926382828453888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 103580 131072 12458903926382828453888 18889465931478580854784 177051673 268435456 49455 49406 (ep229 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep231 := BSN.sin_dyadic_bound_f 177051673 268435456 2 1 131072 49455 ep228 ep207 ep228 ep228 ep208 ep228 80317 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 177051673) qz294 0 1 ep228 ep207 ep228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 177051673) qz295 0 1 ep228 ep208 ep228 rfl rfl rfl rfl) rfl rfl

noncomputable def ep232 := @Enclosure.Real.IsNear.sin_image qz96 qz318 Bool.false 5027749 131072 37 32768 Bool.false 80317 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz96 Bool.false 62846871 1638400 2767 2470300 5027749 131072 37 32768 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz99 27670 1000 0 1 90852 65536 1 24703 62846871 1638400 2767 2470300 qz88 qz319 rfl) rfl) (Enclosure.sfrac_false_div 5027749 131072) (BSN.sin_reduce0 qz318 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12458903926382828453888) qz67) 226375608064910080 72057594037927936 Bool.false 80317 131072 6 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q0 5027749 131072 226375608064910080 72057594037927936 6 12458903926382828453888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 80317 131072 12458903926382828453888 18889465931478580854784 177051673 268435456 49455 49406 (ep231 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz320 := (@Enclosure.Real.IsNear.recentre' qz95 Bool.false 65535 131072 1 131072 65535 131072 1 131072 (ep224 rfl rfl) rfl)

noncomputable def ep233 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz95 (Real.cos qz96)) (@HMul.hMul Real Real Real qz0 qz95 (@Neg.neg Real Real.instNeg qz97)) Bool.false 1697028825 4294967296 62687792729 106098577113088 Bool.true 5263574595 17179869184 250176505027 424394308452352 (@Enclosure.Real.IsNear.mulLit_ff qz95 (Real.cos qz96) 65535 131072 1 131072 25895 32768 946779 809467904 1697028825 4294967296 62687792729 106098577113088 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz96) Bool.false 103580 131072 946779 809467904 25895 32768 946779 809467904 (ep230 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz95 (@Neg.neg Real Real.instNeg qz97) 65535 131072 1 131072 80317 131072 946779 809467904 5263574595 17179869184 250176505027 424394308452352 qz320 (@Enclosure.Real.IsNear.neg qz97 Bool.false 80317 131072 946779 809467904 (@Enclosure.Real.IsNear.recentre' qz97 Bool.false 80317 131072 946779 809467904 80317 131072 946779 809467904 (ep232 rfl rfl) rfl)) rfl)

noncomputable def ep234 := @ep193 1697028825 4294967296 62687792729 106098577113088 Bool.true 5263574595 17179869184 250176505027 424394308452352 Bool.false 87344019351818731520 20336364245 8589934592 448088978361 212197154226176 Bool.true 3255734396057026560 758034735 17179869184 892627320423 424394308452352 (ep194 (BSN.head_sum_c_succ qz11 3 4 rfl rfl) (ep222 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep223 ep233) rfl rfl

noncomputable abbrev qz100 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable abbrev qz321 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz101 := (@HMul.hMul Real Real Real qz249 qz260 qz321)

noncomputable abbrev qz102 := (Real.sin (@HMul.hMul Real Real Real qz249 qz260 qz321))

noncomputable def ep235 := @Enclosure.Complex.IsNear.of_eq qz76 (Complex.mk (@HMul.hMul Real Real Real qz0 qz100 (Real.cos qz101)) (@HMul.hMul Real Real Real qz0 qz100 (@Neg.neg Real Real.instNeg qz102))) Bool.false 6546756879 17179869184 32107452807 60627758350336 Bool.true 2010504483 8589934592 15977695863 30313879175168 (BSN.cpow_neg_s_mk qz37 27670 1000 5 qz38 rfl)

noncomputable abbrev qz103 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def ep236 := @Enclosure.Real.IsNear.inv_image qz103 293085 131072 1 131072 29308 29309 65536 (@Enclosure.Real.IsNear.of_eq qz103 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5) qz304)) Bool.false 293085 131072 1 131072 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5) qz304)) Bool.false 293085 131072 1 131072 293085 131072 1 131072 (BSN.sqrt_enclosure 5 1 146542 146543 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep237 := nat_lit 141613827518379161815574079375

noncomputable def ep238 := nat_lit 29325128709309236875766211300

noncomputable def ep239 := BSN.log_dyadic_bound 2 3 15 14 ep237 65536 24703 ep238 57299708096576225280000 105476 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP 2) (BSN.artanhQ 3) 0 14 ep238 ep237 57299708096576225280000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep240 := nat_lit 477868641649381241223108600139776

noncomputable def ep241 := BSN.cos_dyadic_bound_f 147851976 268435456 2 1 131072 49455 ep240 ep203 ep240 ep240 ep204 ep240 111687 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 147851976) qz305 0 1 ep240 ep203 ep240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 147851976) qz306 0 1 ep240 ep204 ep240 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz104 := qz321

noncomputable abbrev qz322 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5837041) qz12)

noncomputable abbrev qz323 := (BSN.isNear_log_sfrac 5 1 105476 65536 1 24703 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 105476 65536 24703 rfl rfl rfl (ep239 rfl)))

noncomputable def ep242 := @Enclosure.Real.IsNear.cos_image qz101 qz322 Bool.false 5837041 131072 37 32768 Bool.false 111687 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz101 Bool.false 72963023 1638400 2767 2470300 5837041 131072 37 32768 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz104 27670 1000 0 1 105476 65536 1 24703 72963023 1638400 2767 2470300 qz88 qz323 rfl) rfl) (Enclosure.sfrac_false_div 5837041 131072) (BSN.cos_reduce0 qz322 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10404157913532802793472) qz67) 226375608064910080 72057594037927936 Bool.false 111687 131072 7 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q0 5837041 131072 226375608064910080 72057594037927936 7 10404157913532802793472 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 111687 131072 10404157913532802793472 18889465931478580854784 147851976 268435456 49455 49406 (ep241 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep243 := BSN.sin_dyadic_bound_f 147851976 268435456 2 1 131072 49455 ep240 ep207 ep240 ep240 ep208 ep240 68598 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 147851976) qz294 0 1 ep240 ep207 ep240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 147851976) qz295 0 1 ep240 ep208 ep240 rfl rfl rfl rfl) rfl rfl

noncomputable def ep244 := @Enclosure.Real.IsNear.sin_image qz101 qz322 Bool.false 5837041 131072 37 32768 Bool.false 68598 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz101 Bool.false 72963023 1638400 2767 2470300 5837041 131072 37 32768 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz104 27670 1000 0 1 105476 65536 1 24703 72963023 1638400 2767 2470300 qz88 qz323 rfl) rfl) (Enclosure.sfrac_false_div 5837041 131072) (BSN.sin_reduce0 qz322 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10404157913532802793472) qz67) 226375608064910080 72057594037927936 Bool.false 68598 131072 7 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q0 5837041 131072 226375608064910080 72057594037927936 7 10404157913532802793472 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 68598 131072 10404157913532802793472 18889465931478580854784 147851976 268435456 49455 49406 (ep243 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz324 := (@Enclosure.Real.IsNear.recentre' qz100 Bool.false 58617 131072 1 131072 58617 131072 1 131072 (ep236 rfl rfl) rfl)

noncomputable def ep245 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz100 (Real.cos qz101)) (@HMul.hMul Real Real Real qz0 qz100 (@Neg.neg Real Real.instNeg qz102)) Bool.false 6546756879 17179869184 32107452807 60627758350336 Bool.true 2010504483 8589934592 15977695863 30313879175168 (@Enclosure.Real.IsNear.mulLit_ff qz100 (Real.cos qz101) 58617 131072 1 131072 111687 131072 946779 809467904 6546756879 17179869184 32107452807 60627758350336 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz101) Bool.false 111687 131072 946779 809467904 111687 131072 946779 809467904 (ep242 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz100 (@Neg.neg Real Real.instNeg qz102) 58617 131072 1 131072 34299 65536 946779 809467904 2010504483 8589934592 15977695863 30313879175168 qz324 (@Enclosure.Real.IsNear.neg qz102 Bool.false 34299 65536 946779 809467904 (@Enclosure.Real.IsNear.recentre' qz102 Bool.false 68598 131072 946779 809467904 34299 65536 946779 809467904 (ep244 rfl rfl) rfl)) rfl)

noncomputable def ep246 := @ep191 6546756879 17179869184 32107452807 60627758350336 Bool.true 2010504483 8589934592 15977695863 30313879175168 Bool.false 405612290787610984448 47219485369 17179869184 1120930126371 424394308452352 Bool.true 41051672803899604992 4779043701 17179869184 1116315062505 424394308452352 (ep192 (BSN.head_sum_c_succ qz11 4 5 rfl rfl) (ep234 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep235 ep245) rfl rfl

noncomputable def ep247 := @Enclosure.Complex.IsNear.mul qz70 (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 10919331559663400711 94735435052057886720 6445706130911698847 19665961782277193072640 Bool.false

noncomputable abbrev qz105 := (Complex.re qz298)

noncomputable abbrev qz106 := (Complex.im qz298)

noncomputable def ep248 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz105 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz106 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 167027312116751955 1052615945022865408 19200630442147102973

noncomputable def ep249 := nat_lit 2340249452090985975644160

noncomputable def ep250 := nat_lit 11493862508693089392521916894924505088

noncomputable def ep251 := @Enclosure.Real.IsNear.mulLit_ff qz105 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2709666135 8589934592 103829921427 212197154226176 554771597

noncomputable abbrev qz107 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable abbrev qz325 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz401 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable abbrev qz108 := (Real.cos qz325)

noncomputable abbrev qz109 := (@Neg.neg Real Real.instNeg (Real.sin qz325))

noncomputable def ep252 := @Enclosure.Complex.IsNear.of_eq qz70 (Complex.mk (@HMul.hMul Real Real Real qz0 qz107 qz108) (@HMul.hMul Real Real Real qz0 qz107 qz109)) Bool.false 2709666135 8589934592 103829921427 212197154226176 Bool.false 2226096265 8589934592 103383439405 212197154226176 (BSN.cpow_neg_s_mk qz37 27670 1000 6 qz38 rfl)

noncomputable abbrev qz110 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable abbrev qz111 := (@HDiv.hDiv Real Real Real qz253 (@Nat.cast Real Real.instNatCast 6) qz304)

noncomputable def ep253 := @Enclosure.Real.IsNear.inv_image qz110 321059 131072 1 131072 26754 26756 65536 (@Enclosure.Real.IsNear.of_eq qz110 (Real.sqrt qz111) Bool.false 321059 131072 1 131072 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz111) Bool.false 321059 131072 1 131072 321059 131072 1 131072 (BSN.sqrt_enclosure 6 1 160529 160530 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep254 := BSN.log_dyadic_bound 2 10 4 3 105000000 65536 24703 1434560 960 26572 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz326 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz112 := qz326

noncomputable def ep255 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz112 27670 1000 0 1 4034664351997175 2251799813685248 500000000024703 12351500000000000000 446556650479047329 9007199254740992 1383500000068353201 1235150000000000000000 qz88 (BSN.isNear_log_sfrac 6 1 4034664351997175 2251799813685248 500000000024703 12351500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz111) Bool.false 4230652207559789772800 2361183241434822606848 1000000000049406 24703000000000000000 4034664351997175 2251799813685248 500000000024703 12351500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 26572 65536 24973259072661432 36028797018963968 24703 1000000000000000 rfl rfl rfl rfl (ep254 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep256 := nat_lit 3157295606250945252252667066200625

noncomputable def ep257 := BSN.sin_dyadic_bound_f 237043915 268435456 2 1 131072 49455 ep256 ep207 ep256 ep256 ep208 ep256 101277 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 237043915) qz294 0 1 ep256 ep207 ep256 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 237043915) qz295 0 1 ep256 ep208 ep256 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz113 := qz325

noncomputable abbrev qz327 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3249127) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep258 := @Enclosure.Real.IsNear.cos_image qz113 qz327 Bool.false 3249127 65536 37 32768 Bool.false 101277 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 446556650479047329 9007199254740992 1383500000068353201 1235150000000000000000 3249127 65536 37 32768 (ep255 rfl) rfl) (Enclosure.sfrac_false_div 3249127 65536) (BSN.cos_reduce3 qz327 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8340241332941004734464) qz310) 226375608064910080 72057594037927936 Bool.false 101277 131072 7 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q3 3249127 65536 226375608064910080 72057594037927936 7 8340241332941004734464 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 101277 131072 8340241332941004734464 9444732965739290427392 237043915 268435456 49455 49406 (ep257 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep259 := nat_lit 27551243492653614676217612948851793167180690899285077476037910587190625

noncomputable def ep260 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120

noncomputable def ep261 := nat_lit 9968515545251523920630788179420443559170973692707431016272750390625

noncomputable def ep262 := nat_lit 82633793446870340980811577270196538614423730750469817566081186260790625

noncomputable def ep263 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400

noncomputable def ep264 := BSN.cos_dyadic_bound_f 237043915 268435456 3 2 131072 49455 ep259 ep260 ep261 ep262 ep263 ep261 83203 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 237043915) qz305 0 2 ep259 ep260 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 237043915) qz306 0 2 ep262 ep263 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable def ep265 := @Enclosure.Real.IsNear.sin_image qz113 qz327 Bool.false 3249127 65536 37 32768 Bool.true 83203 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 446556650479047329 9007199254740992 1383500000068353201 1235150000000000000000 3249127 65536 37 32768 (ep255 rfl) rfl) (Enclosure.sfrac_false_div 3249127 65536) (BSN.sin_reduce3 qz327 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8340241332941004734464) qz310) 226375608064910080 72057594037927936 Bool.false 83203 131072 7 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q3 3249127 65536 226375608064910080 72057594037927936 7 8340241332941004734464 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 83203 131072 8340241332941004734464 9444732965739290427392 237043915 268435456 49455 49406 (ep264 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz114 := (Real.sin qz325)

noncomputable abbrev qz328 := (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 53510 131072 2 131072 26755 65536 1 65536 (ep253 rfl rfl) rfl)

noncomputable def ep266 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz107 qz108) (@HMul.hMul Real Real Real qz0 qz107 qz109) Bool.false 2709666135 8589934592 103829921427 212197154226176 Bool.false 2226096265 8589934592 103383439405 212197154226176 (@Enclosure.Real.IsNear.mulLit_ff qz107 qz108 26755 65536 1 65536 101277 131072 946779 809467904 2709666135 8589934592 103829921427 212197154226176 qz328 (@Enclosure.Real.IsNear.recentre' qz108 Bool.false 101277 131072 946779 809467904 101277 131072 946779 809467904 (ep258 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz107 qz109 26755 65536 1 65536 83203 131072 946779 809467904 2226096265 8589934592 103383439405 212197154226176 qz328 (@Enclosure.Real.IsNear.neg qz114 Bool.true 83203 131072 946779 809467904 (@Enclosure.Real.IsNear.recentre' qz114 Bool.true 83203 131072 946779 809467904 83203 131072 946779 809467904 (ep265 rfl rfl) rfl)) rfl)

noncomputable def ep267 := @ep251 1102865616 0 1 167027312116751955 1052615945022865408 19200630442147102973 78008315069699532521472 (@Enclosure.Complex.IsNear.re_isNear qz70 Bool.false 2709666135 8589934592 103829921427 212197154226176 Bool.false 2226096265 8589934592 103383439405 212197154226176 (ep252 ep266))

noncomputable def ep268 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 554771597 1102865616 0 1 Bool.false

noncomputable def ep269 := @Enclosure.Complex.IsNear.addLitP qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) Bool.false 7598789 15317578 0 1 Bool.true 1660200

noncomputable def ep270 := @ep269 7658789 0 1 Bool.false 1 144 0 1 Bool.false 2767 7200 0 1 Bool.false 1109543194 554771597 1102865616 0 1 Bool.false 9238429163 9238429163 55143280800 0 1

noncomputable abbrev qz115 := (@HDiv.hDiv Complex Complex Complex qz266 qz299 (@HSub.hSub Complex Complex Complex qz256 qz261 (1 : Complex)))

noncomputable def ep271 := @Enclosure.Complex.IsNear.addLitP qz115 qz41 Bool.true 12000000 3063515600 0 1 Bool.true 664080000 3063515600 0 1

noncomputable def ep272 := @Enclosure.Complex.IsNear.of_eq qz115 (Complex.mk (Enclosure.sfrac Bool.true 12000000 3063515600) (Enclosure.sfrac Bool.true 664080000 3063515600)) Bool.true 12000000 3063515600 0 1 Bool.true 664080000 3063515600 0 1

noncomputable def ep273 := @ep271 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 3039515600 7598789 15317578 0 1 Bool.true 664080000 1660200 7658789 0 1 (ep272 (BSN.N_div_s_sub_one_mk qz37 27670 1000 6 qz38 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 12000000 3063515600) (Enclosure.sfrac Bool.true 664080000 3063515600) Bool.true 12000000 3063515600 0 1 Bool.true 664080000 3063515600 0 1 (Enclosure.Real.IsNear.const Bool.true 12000000 3063515600) (Enclosure.Real.IsNear.const Bool.true 664080000 3063515600))) qz43 rfl

noncomputable abbrev qz116 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz329 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz406 (@Nat.cast Complex Complex.instNatCast 6) 1))

noncomputable abbrev qz117 := qz329

noncomputable def ep274 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz117)) Bool.false 1 144 0 1

noncomputable def ep275 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz117) Bool.false 0 1 0 1 Bool.false

noncomputable def ep276 := @ep275 0 1 0 1 Bool.false 1 144 0 1 Bool.false 2767 7200 0 1 Bool.false 1 1 144 0 1 Bool.false 2767 2767 7200 0

noncomputable def ep277 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (Complex.mk qz44 qz44) Bool.false 0 1 0 1 Bool.false

noncomputable def ep278 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz117 Bool.false 1 144 0 1 Bool.false 2767 7200 0 1

noncomputable abbrev qz118 := (Complex.re qz329)

noncomputable abbrev qz119 := (Complex.im qz329)

noncomputable def ep279 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz118) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz119) 1 144 0 1 0 1 0

noncomputable def ep280 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz118 1 24 0 1 1 6 0 1 1

noncomputable def ep281 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep282 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep283 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz44) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow04.d6 rfl) qz285

noncomputable def ep284 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz11 Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 (BSN.ascPochhammer_one_eval qz11)

noncomputable def ep285 := ep284 (@Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk qz32 qz37) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 (BSN.s_crit_mk qz37 Bool.false 27670 1000 qz38) (@Enclosure.Complex.IsNear.mk qz32 qz37 Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 qz33 qz88))

noncomputable def ep286 := @ep282 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep283) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep285)

noncomputable def ep287 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 27670 1000 0 1 0 1 0

noncomputable def ep288 := @ep287 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep283) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep285)

noncomputable def ep289 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) 2767 1200 0 1 0 1 0 1 2767

noncomputable def ep290 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 27670 1000 0 1 2767 1200 0

noncomputable def ep291 := @ep290 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep283) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep285)

noncomputable def ep292 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep293 := @ep292 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep283) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep285)

noncomputable def ep294 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 2767 1200 0 1 (@ep281 1 24 0 1 (ep286 rfl) (ep288 rfl) rfl rfl) (@ep289 2767 1200 0 1 (ep291 rfl) (ep293 rfl) rfl rfl)

noncomputable def ep295 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2767 1200 0 1 ep294

noncomputable abbrev qz120 := (@Enclosure.Complex.IsNear.of_eq qz329 (Complex.mk (Enclosure.sfrac Bool.false 1 6) qz281) Bool.false 1 6 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 6 1 6 EMRow04.d7 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 6) qz281 Bool.false 1 6 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 6) qz282))

noncomputable def ep296 := @ep280 144 0 1 ep295 (@Enclosure.Complex.IsNear.re_isNear qz117 Bool.false 1 6 0 1 Bool.false 0 1 0 1 qz120)

noncomputable def ep297 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz119 2767 1200 0 1 0 1 0 1 0

noncomputable def ep298 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2767 1200 0 1 ep294

noncomputable def ep299 := @ep297 1 0 1 ep298 (@Enclosure.Complex.IsNear.im_isNear qz117 Bool.false 1 6 0 1 Bool.false 0 1 0 1 qz120)

noncomputable def ep300 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz119) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz118) 0 1 0 1 2767 7200 0

noncomputable def ep301 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz119 1 24 0 1 0 1 0 1 0

noncomputable def ep302 := @ep301 1 0 1 ep295 (@Enclosure.Complex.IsNear.im_isNear qz117 Bool.false 1 6 0 1 Bool.false 0 1 0 1 qz120)

noncomputable def ep303 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz118 2767 1200 0 1 1 6 0 1 2767

noncomputable def ep304 := @ep303 7200 0 1 ep298 (@Enclosure.Complex.IsNear.re_isNear qz117 Bool.false 1 6 0 1 Bool.false 0 1 0 1 qz120)

noncomputable def ep305 := @ep276 1 (@ep277 0 1 0 1 (BSN.bern_sum_base qz11 6) qz61) (ep278 (@ep279 1 1 1 144 0 1 (ep296 rfl) (ep299 rfl) rfl rfl) (@ep300 1 2767 2767 7200 0 1 (ep302 rfl) (ep304 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep306 := ep270 (ep273 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep274 Bool.false 2767 7200 0 1 (BSN.bern_sum_succ qz11 6 0 1 1 rfl rfl) (ep305 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep307 := @Enclosure.Real.IsNear.mulLit_ff qz106 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2226096265 8589934592 103383439405 212197154226176 9238429163

noncomputable def ep308 := @ep307 55143280800 0 1 4113126530844275239 94735435052057886720 191020116314079073603 ep249 (@Enclosure.Complex.IsNear.im_isNear qz70 Bool.false 2709666135 8589934592 103829921427 212197154226176 Bool.false 2226096265 8589934592 103383439405 212197154226176 (ep252 ep266))

noncomputable def ep309 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 554771597 1102865616 0 1 Bool.false

noncomputable def ep310 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz105 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz106 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 556290192079499889 10526159450228654080 319741791367731791867

noncomputable def ep311 := nat_lit 3900415753484976626073600

noncomputable def ep312 := nat_lit 18269582892810370532916929222628343808

noncomputable def ep313 := @Enclosure.Real.IsNear.mulLit_ff qz105 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2709666135 8589934592 103829921427 212197154226176 9238429163

noncomputable def ep314 := @ep313 55143280800 0 1 556290192079499889 10526159450228654080 319741791367731791867 ep311 (@Enclosure.Complex.IsNear.re_isNear qz70 Bool.false 2709666135 8589934592 103829921427 212197154226176 Bool.false 2226096265 8589934592 103383439405 212197154226176 (ep252 ep266))

noncomputable def ep315 := @Enclosure.Real.IsNear.mulLit_ff qz106 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2226096265 8589934592 103383439405 212197154226176 554771597

noncomputable def ep316 := @ep315 1102865616 0 1 1234974980009785205 9473543505205788672 57354195782064579785 234024945209098597564416 (@Enclosure.Complex.IsNear.im_isNear qz70 Bool.false 2709666135 8589934592 103829921427 212197154226176 Bool.false 2226096265 8589934592 103383439405 212197154226176 (ep252 ep266))

noncomputable abbrev qz330 := (ep306 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep317 := @ep247 17356361528813351051 94735435052057886720 546705023315203480693 ep185 (@ep248 78008315069699532521472 4113126530844275239 94735435052057886720 191020116314079073603 ep249 ep250 10919331559663400711 94735435052057886720 6445706130911698847 19665961782277193072640 (ep267 (@ep268 9238429163 55143280800 0 1 qz330) rfl) (ep308 (@ep309 9238429163 55143280800 0 1 qz330) rfl) rfl rfl) (@ep310 ep311 1234974980009785205 9473543505205788672 57354195782064579785 234024945209098597564416 ep312 17356361528813351051 94735435052057886720 546705023315203480693 ep185 (ep314 (@ep309 9238429163 55143280800 0 1 qz330) rfl) (ep316 (@ep268 9238429163 55143280800 0 1 qz330) rfl) rfl rfl)

noncomputable def ep318 := @ep188 34605572639697807566851 ep182 (@ep189 424394308452352 (BSN.head_sum_c_eq qz11 6) (ep190 (BSN.head_sum_c_succ qz11 5 6 rfl rfl) (ep246 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep317 rfl rfl rfl

noncomputable def ep319 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz11 1 6) Bool.false 271303065653089262231 94735435052057886720 408718558890826232969 137661732475940351508480 Bool.true 8996853347158073029 94735435052057886720 34605572639697807566851 ep182 (@ep183 137661732475940351508480 Bool.true 8996853347158073029 94735435052057886720 34605572639697807566851 ep182 (BSN.zetaApproximant_eq_folded' qz11 1 6 rfl) (ep318 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep320 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 6)) 5 32768 551531

noncomputable def ep321 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) Bool.true 20 131072 551531

noncomputable def ep322 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) qz262 Bool.false 823529 131072 21

noncomputable def ep323 := nat_lit 276632878085556284753830962071944704277217948203285810093535422435928481

noncomputable def ep324 := nat_lit 827901720512676159574575032590417249498637356257600650766981369088027041

noncomputable def ep325 := BSN.cos_dyadic_bound_f 421615107 268435456 3 2 131072 49455 ep323 ep260 ep177 ep324 ep263 ep177 20 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 421615107) qz305 0 2 ep323 ep260 ep177 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 421615107) qz306 0 2 ep324 ep263 ep177 rfl rfl rfl rfl) rfl rfl

noncomputable def ep326 := @ep322 32768 Bool.true 20 131072 1 24703 (@ep56 823529 131072 21 32768 ep174 rfl) (Enclosure.sfrac_false_div 823529 131072) (BSN.sin_reduce3 qz262 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29668525620069828395008) qz67) 226375608064910080 72057594037927936 Bool.false 20 131072 0 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q3 823529 131072 226375608064910080 72057594037927936 0 29668525620069828395008 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 20 131072 29668525620069828395008 18889465931478580854784 421615107 268435456 49455 49406 (ep325 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep327 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz11 1 6) Bool.false 271303065653089262231 94735435052057886720 408718558890826232969 137661732475940351508480 Bool.true 8996853347158073029 94735435052057886720 34605572639697807566851 ep182 (@ep183 137661732475940351508480 Bool.true 8996853347158073029 94735435052057886720 34605572639697807566851 ep182 (BSN.zetaApproximant_eq_folded' qz11 1 6 rfl) (ep318 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow04.d8 : Enclosure.Real.IsNear (hardyZApproximantEM 1 6 qz37) Bool.false ep38 ep39 ep40 ep41 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 6 qz37) ep42 Bool.false ep38 ep39 ep40 ep41 (@Eq.refl Real ep42) (@ep43 Bool.false ep38 ep39 ep40 ep41 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) (zetaApproximant qz11 1 6)) (@ep45 ep46 ep47 ep48 8996853347158073029 620858147157166566408192 ep49 ep50 ep51 ep38 ep39 ep40 ep41 (@ep52 809467904 271303065653089262231 94735435052057886720 408718558890826232969 137661732475940351508480 ep44 ep46 ep47 ep48 (@ep53 809467904 131071 131072 551531 809467904 (ep181 rfl rfl) rfl) ep319 rfl) (@ep320 809467904 8996853347158073029 94735435052057886720 34605572639697807566851 ep182 8996853347158073029 620858147157166566408192 ep49 ep50 (@ep321 809467904 5 32768 551531 809467904 (ep326 rfl rfl) rfl) ep327 rfl) rfl rfl))

theorem EMRow04.d9 : @Eq Nat (Nat.pow 7 1) 7 := @Eq.refl Nat 7

noncomputable def ep328 := nat_lit 4660542172964952805198769737

noncomputable def ep329 := nat_lit 4758483551342025568891699200

noncomputable def ep330 := nat_lit 22835595676349082519059683654298019

noncomputable def ep331 := nat_lit 4839680799878195382654461057957888000

noncomputable abbrev qz425 := (Enclosure.sfrac Bool.false 31718 1000)

noncomputable abbrev qz411 := (@HAdd.hAdd Complex Complex Complex qz419 (@HAdd.hAdd Complex Complex Complex qz419 qz420 (@HMul.hMul Complex Complex Complex qz418 Complex.I (@HDiv.hDiv Complex Complex Complex qz421 (↑qz425) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz331 := qz411

noncomputable abbrev qz121 := (Complex.Stirling.logGammaStirling 1 qz331)

noncomputable abbrev qz412 := (@HAdd.hAdd Complex Complex Complex qz419 qz420 (@HMul.hMul Complex Complex Complex qz418 Complex.I (@HDiv.hDiv Complex Complex Complex qz421 (↑qz425) (2 : Complex))))

noncomputable abbrev qz332 := qz412

noncomputable abbrev qz122 := qz332

noncomputable abbrev qz413 := qz425

noncomputable abbrev qz333 := qz413

noncomputable abbrev qz123 := (@HMul.hMul Real Real Real qz249 (@HDiv.hDiv Real Real Real qz253 qz333 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz426 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 31718 1000)))

noncomputable abbrev qz414 := qz426

noncomputable abbrev qz334 := qz414

noncomputable abbrev qz124 := qz334

noncomputable def ep332 := Complex.re (@HMul.hMul Complex Complex Complex qz4 (Complex.exp (@HMul.hMul Complex Complex Complex qz4 Complex.I ↑(@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123))) (zetaApproximant qz124 1 7))

noncomputable def ep333 := @Enclosure.Real.IsNear.of_eq ep332 (@HSub.hSub Real Real Real qz5 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) (Complex.re (zetaApproximant qz124 1 7))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) (Complex.im (zetaApproximant qz124 1 7))))

noncomputable def ep334 := nat_lit 5825686800443525404514058221

noncomputable def ep335 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) (Complex.re (zetaApproximant qz124 1 7))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) (Complex.im (zetaApproximant qz124 1 7))) ep334

noncomputable def ep336 := nat_lit 5948104439177531961114624000

noncomputable def ep337 := nat_lit 6771331864668491382250904940229789

noncomputable def ep338 := nat_lit 1451904239963458614796338317387366400

noncomputable def ep339 := nat_lit 7930805918903375948152832000

noncomputable def ep340 := nat_lit 793468382362333734670001560596167

noncomputable def ep341 := nat_lit 14519042399634586147963383173873664000

noncomputable def ep342 := nat_lit 46202319313311561273086972986336476465900280065556480000

noncomputable def ep343 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) (Complex.re (zetaApproximant qz124 1 7)) 131071 131072 78205

noncomputable def ep344 := nat_lit 1750501987081107685744829

noncomputable def ep345 := nat_lit 448413159060676794541670400

noncomputable def ep346 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) Bool.true 131071 131072 78205

noncomputable abbrev qz335 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1235321) qz12)

noncomputable def ep347 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123) qz335 Bool.false 1235321 131072 3

noncomputable def ep348 := nat_lit 43364352000000000000000000

noncomputable def ep349 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123) Bool.false 31834003130154812747 3377699720527872000 31240376087152237552847 ep348

noncomputable def ep350 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123 3726146621682076931 135107988821114880 10252971962152237552847 ep348 1189758039 65536000

noncomputable def ep351 := nat_lit 83450929165513032327495680

noncomputable def ep352 := nat_lit 50591744000000000000000000

noncomputable def ep353 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 13895465485198078137 562949953421312000 19317851829509109853173 ep352 Bool.false 3726146621682076931 135107988821114880

noncomputable def ep354 := @Enclosure.Complex.IsNear.subLitP qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 2695490725190249503 140737488355328000 18293851829154967645173 ep352 Bool.false 4137844833934663331 135107988821114880 59482803734762112405929

noncomputable def ep355 := nat_lit 303550464000000000000000000

noncomputable def ep356 := nat_lit 15644903295319413274828500514111488

noncomputable def ep357 := nat_lit 1048817033558452137361476719476736

noncomputable abbrev qz336 := (@HSub.hSub Complex Complex Complex qz397 qz411 qz403)

noncomputable abbrev qz337 := (Complex.log qz411)

noncomputable abbrev qz125 := (@HSub.hSub Complex Complex Complex qz256 (@HMul.hMul Complex Complex Complex qz255 qz336 qz337) qz331)

noncomputable abbrev qz126 := qz331

noncomputable def ep358 := @Enclosure.Complex.IsNear.of_eq qz121 (@HAdd.hAdd Complex Complex Complex qz8 (@HAdd.hAdd Complex Complex Complex qz8 qz125 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz126 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k)))))) Bool.true 2695490725190249503

noncomputable def ep359 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz8 qz125 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz126 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) Bool.true 2695593575553641503 140737488355328000

noncomputable def ep360 := nat_lit 1447130563920430624183156736

noncomputable def ep361 := nat_lit 13884303310681195318293299200000

noncomputable def ep362 := @ep359 17864813599370419377 49406000000000000000000 Bool.false 34487839763368536569 1125899906842624000 4839750001588674633 24703000000000000000000 Bool.false 392343 536870912 3 536870912 Bool.true 2074055879 402653184000 15859 402653184000 Bool.true ep360 2695490725190249503 140737488355328000 18293851829154967645173 ep352 Bool.false ep361

noncomputable def ep363 := @Enclosure.Complex.IsNear.addLitP qz125 qz14 Bool.true 2824921483287145503 140737488355328000 16734000000737606877 49406000000000000000000

noncomputable def ep364 := @ep363 Bool.false 34487839763368536569 1125899906842624000 4839750001588674633 24703000000000000000000 Bool.false 60223 65536 3 131072 Bool.false 0 1 0 1 Bool.true 176658420567483449540608 2695593575553641503 140737488355328000 17864813599370419377 49406000000000000000000 Bool.false 34487839763368536569 34487839763368536569 1125899906842624000

noncomputable abbrev qz127 := (@HMul.hMul Complex Complex Complex qz255 qz336 qz337)

noncomputable def ep365 := @Enclosure.Complex.IsNear.subLitP qz127 qz126 Bool.true 2508262134487657503 140737488355328000 16734000000737606877 49406000000000000000000 Bool.false 10468697277197142117

noncomputable def ep366 := @ep365 225179981368524800 4839750001588674633 24703000000000000000000 Bool.false 9000 4000 0 1 Bool.false 63436 4000 0 1 Bool.true 11299685933148582012000 2824921483287145503 140737488355328000 16734000000737606877 49406000000000000000000 Bool.false 27590271810694829255200 34487839763368536569 1125899906842624000 4839750001588674633 24703000000000000000000

noncomputable abbrev qz128 := qz336

noncomputable abbrev qz129 := qz337

noncomputable def ep367 := @Enclosure.Complex.IsNear.mul qz128 qz129 Bool.true 2508262134487657503 140737488355328000 16734000000737606877 49406000000000000000000 Bool.false 10468697277197142117 225179981368524800 4839750001588674633

noncomputable abbrev qz130 := (Complex.re qz336)

noncomputable abbrev qz131 := (Complex.re qz337)

noncomputable abbrev qz132 := (Complex.im qz336)

noncomputable abbrev qz133 := (Complex.im qz337)

noncomputable def ep368 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz130 qz131) (@HMul.hMul Real Real Real qz0 qz132 qz133) 21860350536960705 4503599627370496 62500000024703 3529000000000000000 12765592355070718137 562949953421312000

noncomputable def ep369 := nat_lit 45184833656904557017574762140925952

noncomputable def ep370 := @Enclosure.Real.IsNear.mulLit_ff qz130 qz131 7000 4000 0 1 3122907219565815 1125899906842624 62500000024703 6175750000000000000

noncomputable def ep371 := @Enclosure.Complex.IsNear.re_isNear qz128 Bool.false 7000 4000 0 1 Bool.false 63436 4000 0 1

noncomputable abbrev qz338 := (Enclosure.sfrac Bool.false 63436 4000)

noncomputable abbrev qz134 := qz338

noncomputable def ep372 := @Enclosure.Complex.IsNear.of_eq qz128 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz134) Bool.false 7000 4000 0 1 Bool.false 63436 4000 0

noncomputable abbrev qz135 := (Complex.log (Complex.mk qz273 qz338))

noncomputable def ep373 := @Enclosure.Complex.IsNear.of_eq qz129 qz135 Bool.false 3122907219565815 1125899906842624 62500000024703 6175750000000000000 Bool.false 804943083111843 562949953421312 1000000000024703 49406000000000000000

noncomputable def ep374 := BSN.log_dyadic_bound 9126096 8201126096 1 0 1 131072 49406 0 1 291 8210252192 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 9126096) (BSN.artanhQ 8201126096) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz339 := (Real.log (Enclosure.sfrac Bool.false 4105126096 16000000))

noncomputable def ep375 := @Enclosure.Real.IsNear.mulLit_ff qz32 qz339 1 2 0 1 3122907219565815 562949953421312 62500000024703 3087875000000000000 3122907219565815 1125899906842624 62500000024703 6175750000000000000 qz33 (BSN.isNear_log_sfrac 4105126096 16000000 3122907219565815 562949953421312 62500000024703 3087875000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4105126096) qz275)) Bool.false 26196844485307552235520 4722366482869645213696 1000000000395248 49406000000000000000 3122907219565815 562949953421312 62500000024703 3087875000000000000 (BSN.log_rat_reduce_isNear 4105126096 16000000 8 8210252192 8192000000 291 131072 24973259072661432 36028797018963968 49406 1000000000000000 rfl rfl rfl rfl (ep374 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep376 := BSN.arctan_dyadic_bound_f 9000 63436 2 1 131072 49406 6561000000000000 80967954182541006080 6561000000000000 19683000000000000 113355135855557408512 19683000000000000 18472 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 63436) 0 1 6561000000000000 80967954182541006080 6561000000000000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.arctanOddP 9000) (BSN.arctanOddQ 63436) 0 1 19683000000000000 113355135855557408512 19683000000000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz340 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 63436)))

noncomputable def ep377 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz340 884279719003555 562949953421312 1 2000000000000000 18472 131072 1 49406 105505499789635485696 804943083111843 562949953421312 1000000000024703 49406000000000000000 qz35 (ep376 rfl) rfl rfl

noncomputable abbrev qz136 := (Complex.mk qz273 qz338)

noncomputable abbrev qz137 := qz333

noncomputable abbrev qz341 := (@Eq.refl Real qz413)

noncomputable abbrev qz138 := qz341

noncomputable abbrev qz342 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 63436) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep378 := @Enclosure.Complex.IsNear.re_isNear qz129 Bool.false 3122907219565815 1125899906842624 62500000024703 6175750000000000000 Bool.false 804943083111843 562949953421312 1000000000024703 49406000000000000000 (ep373 (@congrArg Complex Complex qz126 qz136 Complex.log (BSN.w_shift_mk qz137 Bool.false 31718 1000 2 qz138 rfl)) (@Enclosure.Complex.IsNear.of_parts qz135 Bool.false 3122907219565815 1125899906842624 62500000024703 6175750000000000000 Bool.false 804943083111843 562949953421312 1000000000024703 49406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz135) (@HMul.hMul Real Real Real qz0 qz32 qz339) Bool.false 3122907219565815 1125899906842624 62500000024703 6175750000000000000 (Enclosure.clog_re_eq 9000 63436 4000 4105126096 16000000 rfl rfl rfl) (ep375 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz135) qz342 Bool.false 804943083111843 562949953421312 1000000000024703 49406000000000000000 (Enclosure.clog_im_eq 9000 63436 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz342 (@HSub.hSub Real Real Real qz5 qz34 qz340) Bool.false 804943083111843 562949953421312 1000000000024703 49406000000000000000 (BSN.arctan_recip 63436 9000 rfl rfl) ep377))))

noncomputable def ep379 := @Enclosure.Real.IsNear.mulLit_ff qz132 qz133 63436 4000 0 1 804943083111843 562949953421312 1000000000024703 49406000000000000000

noncomputable def ep380 := @Enclosure.Complex.IsNear.im_isNear qz128 Bool.false 7000 4000 0 1 Bool.false 63436 4000 0 1

noncomputable def ep381 := @Enclosure.Complex.IsNear.im_isNear qz129 Bool.false 3122907219565815 1125899906842624 62500000024703 6175750000000000000 Bool.false 804943083111843 562949953421312 1000000000024703 49406000000000000000 (ep373 (@congrArg Complex Complex qz126 qz136 Complex.log (BSN.w_shift_mk qz137 Bool.false 31718 1000 2 qz138 rfl)) (@Enclosure.Complex.IsNear.of_parts qz135 Bool.false 3122907219565815 1125899906842624 62500000024703 6175750000000000000 Bool.false 804943083111843 562949953421312 1000000000024703 49406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz135) (@HMul.hMul Real Real Real qz0 qz32 qz339) Bool.false 3122907219565815 1125899906842624 62500000024703 6175750000000000000 (Enclosure.clog_re_eq 9000 63436 4000 4105126096 16000000 rfl rfl rfl) (ep375 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz135) qz342 Bool.false 804943083111843 562949953421312 1000000000024703 49406000000000000000 (Enclosure.clog_im_eq 9000 63436 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz342 (@HSub.hSub Real Real Real qz5 qz34 qz340) Bool.false 804943083111843 562949953421312 1000000000024703 49406000000000000000 (BSN.arctan_recip 63436 9000 rfl rfl) ep377))))

noncomputable abbrev qz343 := (Enclosure.Real.IsNear.const Bool.false 63436 4000)

noncomputable abbrev qz139 := (@ep372 1 (BSN.w_sub_half_mk qz333 Bool.false 31718 1000 2 qz341 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz338 Bool.false 7000 4000 0 1 Bool.false 63436 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz343))

noncomputable def ep382 := @ep368 15859000000391764877 49406000000000000000000 ep369 2508262134487657503 140737488355328000 16734000000737606877 49406000000000000000000 (@ep370 21860350536960705 4503599627370496 62500000024703 3529000000000000000 (ep371 qz139) ep378 rfl) (@ep379 12765592355070718137 562949953421312000 15859000000391764877 49406000000000000000000 (ep380 qz139) ep381 rfl) rfl

noncomputable def ep383 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz130 qz133) (@HMul.hMul Real Real Real qz0 qz132 qz131) 5634601581782901 2251799813685248 1000000000024703 28232000000000000000 9905237119018852017 225179981368524800

noncomputable def ep384 := nat_lit 23573410578319787654999811362390016

noncomputable def ep385 := @Enclosure.Real.IsNear.mulLit_ff qz130 qz133 7000 4000 0 1 804943083111843 562949953421312 1000000000024703 49406000000000000000

noncomputable def ep386 := @Enclosure.Real.IsNear.mulLit_ff qz132 qz131 63436 4000 0 1 3122907219565815 1125899906842624 62500000024703 6175750000000000000

noncomputable def ep387 := @ep383 991187500391764877 6175750000000000000000 ep384 10468697277197142117 225179981368524800 4839750001588674633 24703000000000000000000 (@ep385 5634601581782901 2251799813685248 1000000000024703 28232000000000000000 (ep371 qz139) ep381 rfl) (@ep386 9905237119018852017 225179981368524800 991187500391764877 6175750000000000000000 (ep380 qz139) ep378 rfl) rfl

noncomputable def ep388 := @Enclosure.Complex.IsNear.of_eq qz126 qz136 Bool.false 9000 4000 0 1 Bool.false 63436 4000 0 1 (BSN.w_shift_mk qz137 Bool.false 31718 1000 2 qz138 rfl)

noncomputable abbrev qz344 := (ep388 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 63436 4000) Bool.false 9000 4000 0 1 Bool.false 63436 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 63436 4000)))

noncomputable abbrev qz140 := qz344

noncomputable def ep389 := ep366 (@ep367 24703000000000000000000 (ep382 rfl) (ep387 rfl)) qz140 rfl rfl rfl rfl rfl rfl

noncomputable def ep390 := @ep364 4839750001588674633 24703000000000000000000 (ep389 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz41 (↑qz3) Bool.false 60223 65536 3 131072 Bool.false 0 1 0 1 (@ep99 65536 3 131072 (ep101 rfl) (ep103 rfl) rfl rfl) (@ep104 1 0 1 (ep106 rfl) (ep108 rfl) rfl rfl))

noncomputable abbrev qz345 := (@HPow.hPow Complex Int Complex qz405 qz411 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz141 := qz345

noncomputable def ep391 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz126 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz126 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) qz141)) Bool.false 392343 536870912 3 536870912

noncomputable def ep392 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz126 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) qz141) Bool.false 0 1 0 1 Bool.false

noncomputable def ep393 := @ep392 0 1 0 1 Bool.false 392343 536870912 3 536870912 Bool.true 2074055879 402653184000 15859 402653184000 Bool.false 392343 392343 536870912 3 536870912 Bool.true 2074055879 2074055879 402653184000 15859

noncomputable def ep394 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz126 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz44 qz44) Bool.false 0 1 0 1 Bool.false

noncomputable def ep395 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) qz141 Bool.false 392343 536870912 3 536870912 Bool.true 2074055879 402653184000 15859 402653184000

noncomputable abbrev qz142 := (Complex.re qz345)

noncomputable abbrev qz143 := (Complex.im qz345)

noncomputable def ep396 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz142) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz143) 392343 536870912 3 536870912 0 1 0

noncomputable def ep397 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz142 1 12 0 1 1177029 134217728 9 134217728 392343

noncomputable def ep398 := @Enclosure.Complex.IsNear.re_isNear qz141 Bool.false 1177029 134217728 9 134217728 Bool.true 2074055879 33554432000 15859 33554432000

noncomputable abbrev qz346 := (@HPow.hPow Complex Nat Complex qz406 qz411 1)

noncomputable abbrev qz144 := (@Inv.inv Complex Complex.instInv qz346)

noncomputable def ep399 := @Enclosure.Complex.IsNear.of_eq qz141 qz144 Bool.false 1177029 134217728 9 134217728 Bool.true 2074055879 33554432000 15859

noncomputable def ep400 := @Enclosure.Complex.IsNear.of_parts qz144 Bool.false 1177029 134217728 9 134217728 Bool.true 2074055879 33554432000 15859

noncomputable abbrev qz145 := (Complex.re qz346)

noncomputable abbrev qz146 := qz346

noncomputable def ep401 := @Enclosure.Real.IsNear.mulLit_ff qz145 (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz146)) 9000 4000 0 1 130781 33554432 1 33554432

noncomputable def ep402 := @Enclosure.Complex.IsNear.re_isNear qz146 Bool.false 9000 4000 0 1 Bool.false 63436 4000 0 1

noncomputable def ep403 := @Enclosure.Complex.IsNear.of_eq qz146 qz126 Bool.false 9000 4000 0 1 Bool.false 63436 4000 0

noncomputable def ep404 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz146)) Bool.false 130781 33554432 1 33554432 130781 33554432 1

noncomputable abbrev qz147 := (Complex.im qz346)

noncomputable def ep405 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz146) (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 qz145 qz145) (@HMul.hMul Real Real Real qz0 qz147 qz147)) Bool.false 256570381 1000000 0 1

noncomputable def ep406 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz145 qz145) (@HMul.hMul Real Real Real qz0 qz147 qz147) 81 16 0 1 251507881 1000000

noncomputable def ep407 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz145 9000 4000 0 1 9000 4000 0 1

noncomputable def ep408 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz147 63436 4000 0 1 63436 4000 0 1

noncomputable def ep409 := @Enclosure.Complex.IsNear.im_isNear qz146 Bool.false 9000 4000 0 1 Bool.false 63436 4000 0 1

noncomputable abbrev qz148 := (ep402 (@ep403 1 (BSN.pow_one_c qz331) qz344))

noncomputable abbrev qz149 := (ep409 (@ep403 1 (BSN.pow_one_c qz331) qz344))

noncomputable def ep410 := @ep406 0 1 4105126096 256570381 1000000 0 1 (@ep407 81 16 0 1 qz148 qz148 rfl) (@ep408 251507881 1000000 0 1 qz149 qz149 rfl)

noncomputable def ep411 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz146) 256570381 1000000 0 1 65390 65391 16777216 (ep405 (Enclosure.Complex.normSq_eq_mul_add_mul qz146) (ep410 rfl rfl)) rfl

noncomputable def ep412 := @Enclosure.Real.IsNear.of_eq (Complex.re qz144) (@HMul.hMul Real Real Real qz0 qz145 (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz146))) Bool.false 1177029 134217728 9 134217728 (Enclosure.Complex.inv_re_eq_mul qz146) (@ep401 1177029 134217728 9 134217728 qz148 (@ep404 33554432 (ep411 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep413 := @Enclosure.Real.IsNear.of_eq (Complex.im qz144) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz147) (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz146))) Bool.true 2074055879 33554432000 15859 33554432000 (Enclosure.Complex.inv_im_eq_mul qz146)

noncomputable def ep414 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz147) (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz146)) 63436 4000 0 1 130781 33554432 1

noncomputable def ep415 := @ep414 33554432 2074055879 33554432000 15859 33554432000 (@Enclosure.Real.IsNear.neg qz147 Bool.false 63436 4000 0 1 qz149) (@ep404 33554432 (ep411 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep416 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz143 0 1 0 1 2074055879 33554432000 15859 33554432000 0

noncomputable def ep417 := @Enclosure.Complex.IsNear.im_isNear qz141 Bool.false 1177029 134217728 9 134217728 Bool.true 2074055879 33554432000 15859 33554432000

noncomputable abbrev qz150 := (@ep399 33554432000 (BSN.zpow_one_sub_two_mul qz331 1 1 rfl rfl) (@ep400 33554432000 ep412 (ep413 ep415)))

noncomputable def ep418 := @ep396 1 392343 392343 536870912 3 536870912 (@ep397 536870912 3 536870912 ep118 (ep398 qz150) rfl) (@ep416 1 0 1 ep138 (ep417 qz150) rfl) rfl

noncomputable def ep419 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz143) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz142) 2074055879 402653184000 15859 402653184000 0 1 0

noncomputable def ep420 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz143 1 12 0 1 2074055879 33554432000 15859 33554432000 2074055879

noncomputable def ep421 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz142 0 1 0 1 1177029 134217728 9 134217728 0

noncomputable def ep422 := @ep419 1 2074055879 2074055879 402653184000 15859 402653184000 (@ep420 402653184000 15859 402653184000 ep118 (ep417 qz150) rfl) (@ep421 1 0 1 ep138 (ep398 qz150) rfl) rfl

noncomputable def ep423 := @ep393 402653184000 (@ep394 0 1 0 1 (BSN.stirling_sum_base qz126) qz61) (ep395 (ep418 rfl) (ep422 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep424 := @ep362 4137844833934663331 135107988821114880 59482803734762112405929 ep355 (ep390 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep391 Bool.true 2074055879 402653184000 15859 402653184000 (BSN.stirling_sum_succ qz126 0 1 rfl) (ep423 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep425 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz137 2) Bool.false 24908020675496641 4503599627370496 500000000172921 24703000000000000000 Bool.false 857704608859555 281474976710656

noncomputable abbrev qz151 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz258 qz332 qz283))

noncomputable def ep426 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz137 2) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz137 1) qz151) Bool.false 24908020675496641 4503599627370496 500000000172921 24703000000000000000 Bool.false 857704608859555 281474976710656 1000000000024703 24703000000000000000

noncomputable def ep427 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz137 1) qz151 Bool.false 24894637557402305 9007199254740992 500000000172921 49406000000000000000 Bool.false 875406316570019 562949953421312 1000000000024703 49406000000000000000 Bool.false

noncomputable def ep428 := nat_lit 448703010530813129902166842015744

noncomputable def ep429 := nat_lit 965689539213462230037503672320

noncomputable abbrev qz152 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz258 qz332 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep430 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz137 1) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz137 0) qz152) Bool.false 24894637557402305 9007199254740992 500000000172921 49406000000000000000 Bool.false 875406316570019 562949953421312 1000000000024703 49406000000000000000

noncomputable def ep431 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz137 0) qz152 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz347 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz134))

noncomputable def ep432 := @Enclosure.Complex.IsNear.of_eq qz152 qz347 Bool.false 24894637557402305 9007199254740992 500000000172921 49406000000000000000 Bool.false 875406316570019 562949953421312 1000000000024703 49406000000000000000

noncomputable def ep433 := nat_lit 709491959660455965840958881073301571024881379377513623723562596151062688187235714785485108054348267520

noncomputable def ep434 := nat_lit 26790544821614938106190631911590508924963230541155460594769533147035419967029759989227747181858914304

noncomputable def ep435 := nat_lit 862532547933414112277510674998600325733912468695918042352437317842000793112486365617434468024320

noncomputable def ep436 := BSN.log_dyadic_bound 1977126096 6073126096 6 5 ep433 131072 49406 ep434 ep435 88564 8050252192 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1977126096) (BSN.artanhQ 6073126096) 0 5 ep434 ep433 ep435 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep437 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 4025126096 16000000)) 1 2 0 1 24894637557402305 4503599627370496 500000000172921 24703000000000000000 24894637557402305 9007199254740992 500000000172921 49406000000000000000 qz33 (BSN.isNear_log_sfrac 4025126096 16000000 24894637557402305 4503599627370496 500000000172921 24703000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4025126096) qz275)) Bool.false 26103919471390679367680 4722366482869645213696 1000000000345842 49406000000000000000 24894637557402305 4503599627370496 500000000172921 24703000000000000000 (BSN.log_rat_reduce_isNear 4025126096 16000000 7 8050252192 4096000000 88564 131072 24973259072661432 36028797018963968 49406 1000000000000000 rfl rfl rfl rfl (ep436 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep438 := BSN.arctan_dyadic_bound_f 1000 63436 1 0 131072 49406 0 1 1 0 1 1 2066 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 63436) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 63436) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz348 := (@Nat.cast Real Real.instNatCast 63436)

noncomputable def ep439 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz288 qz348)) 884279719003555 562949953421312 1 2000000000000000 2066 131072 1 49406 114741256725465530368 875406316570019 562949953421312 1000000000024703 49406000000000000000 qz35 (ep438 rfl) rfl rfl

noncomputable abbrev qz153 := (@HAdd.hAdd Complex Complex Complex qz258 qz332 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz349 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz134)

noncomputable def ep440 := @ep431 24894637557402305 9007199254740992 500000000172921 49406000000000000000 Bool.false 875406316570019 562949953421312 1000000000024703 49406000000000000000 Bool.false 24894637557402305 24894637557402305 9007199254740992 500000000172921 49406000000000000000 Bool.false 875406316570019 875406316570019 562949953421312 1000000000024703 49406000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz137 0) (Complex.mk qz44 qz44) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz137) qz61) (ep432 (@congrArg Complex Complex qz153 qz349 Complex.log (BSN.w_shift_mk qz137 Bool.false 31718 1000 0 qz138 rfl)) (@Enclosure.Complex.IsNear.of_parts qz347 Bool.false 24894637557402305 9007199254740992 500000000172921 49406000000000000000 Bool.false 875406316570019 562949953421312 1000000000024703 49406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz347) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 4025126096 16000000))) Bool.false 24894637557402305 9007199254740992 500000000172921 49406000000000000000 (Enclosure.clog_re_eq 1000 63436 4000 4025126096 16000000 rfl rfl rfl) (ep437 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz347) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz348 qz288)) Bool.false 875406316570019 562949953421312 1000000000024703 49406000000000000000 (Enclosure.clog_im_eq 1000 63436 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz348 qz288)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz288 qz348))) Bool.false 875406316570019 562949953421312 1000000000024703 49406000000000000000 (BSN.arctan_recip 63436 1000 rfl rfl) ep439)))) rfl rfl

noncomputable abbrev qz350 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz134))

noncomputable def ep441 := @Enclosure.Complex.IsNear.of_eq qz151 qz350 Bool.false 24921403793590977 9007199254740992 500000000172921 49406000000000000000 Bool.false 840002901149091 562949953421312 1000000000024703 49406000000000000000

noncomputable def ep442 := nat_lit 738033817654713845015982425671564467569969565942392597269860564536203706600145370352495525923148267520

noncomputable def ep443 := nat_lit 28357058384442384832702954831588563788509788118858101936382993818449075923708414622234615907618914304

noncomputable def ep444 := nat_lit 973142328593388800251269837021903908055243341201766130712437965300467839105084601182695268024320

noncomputable def ep445 := BSN.log_dyadic_bound 2001126096 6097126096 6 5 ep442 131072 49406 ep443 ep444 89343 8098252192 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 2001126096) (BSN.artanhQ 6097126096) 0 5 ep443 ep442 ep444 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep446 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 4049126096 16000000)) 1 2 0 1 24921403793590977 4503599627370496 500000000172921 24703000000000000000 24921403793590977 9007199254740992 500000000172921 49406000000000000000 qz33 (BSN.isNear_log_sfrac 4049126096 16000000 24921403793590977 4503599627370496 500000000172921 24703000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4049126096) qz275)) Bool.false 26131985904268452298752 4722366482869645213696 1000000000345842 49406000000000000000 24921403793590977 4503599627370496 500000000172921 24703000000000000000 (BSN.log_rat_reduce_isNear 4049126096 16000000 7 8098252192 4096000000 89343 131072 24973259072661432 36028797018963968 49406 1000000000000000 rfl rfl rfl rfl (ep445 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep447 := BSN.arctan_dyadic_bound_f 5000 63436 1 0 131072 49406 0 1 1 0 1 1 10309 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 63436) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 63436) 0 0 rfl) rfl rfl rfl

noncomputable def ep448 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz292 qz348)) 884279719003555 562949953421312 1 2000000000000000 10309 131072 1 49406 110100860259413655552 840002901149091 562949953421312 1000000000024703 49406000000000000000 qz35 (ep447 rfl) rfl rfl

noncomputable abbrev qz154 := (@HAdd.hAdd Complex Complex Complex qz258 qz332 qz283)

noncomputable abbrev qz351 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz134)

noncomputable def ep449 := @ep427 24921403793590977 9007199254740992 500000000172921 49406000000000000000 Bool.false 840002901149091 562949953421312 1000000000024703 49406000000000000000 Bool.false ep428 24908020675496641 4503599627370496 500000000172921 24703000000000000000 Bool.false ep429 857704608859555 281474976710656 1000000000024703 24703000000000000000 (ep430 (BSN.log_sum_c_succ qz137 0 1 rfl) (ep440 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep441 (@congrArg Complex Complex qz154 qz351 Complex.log (BSN.w_shift_mk qz137 Bool.false 31718 1000 1 qz138 rfl)) (@Enclosure.Complex.IsNear.of_parts qz350 Bool.false 24921403793590977 9007199254740992 500000000172921 49406000000000000000 Bool.false 840002901149091 562949953421312 1000000000024703 49406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz350) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 4049126096 16000000))) Bool.false 24921403793590977 9007199254740992 500000000172921 49406000000000000000 (Enclosure.clog_re_eq 5000 63436 4000 4049126096 16000000 rfl rfl rfl) (ep446 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz350) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz348 qz292)) Bool.false 840002901149091 562949953421312 1000000000024703 49406000000000000000 (Enclosure.clog_im_eq 5000 63436 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz348 qz292)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz292 qz348))) Bool.false 840002901149091 562949953421312 1000000000024703 49406000000000000000 (BSN.arctan_recip 63436 5000 rfl rfl) ep448)))) rfl rfl

noncomputable def ep450 := @ep354 ep355 Bool.false 24908020675496641 4503599627370496 500000000172921 24703000000000000000 Bool.false 857704608859555 281474976710656 1000000000024703 24703000000000000000 Bool.true ep356 13895465485198078137 562949953421312000 19317851829509109853173 ep352 Bool.false ep357 3726146621682076931 135107988821114880 10252971962152237552847 ep348 (@ep358 140737488355328000 18293851829154967645173 ep352 Bool.false 4137844833934663331 135107988821114880 59482803734762112405929 ep355 (BSN.logGammaStirling_unfold 1 qz126) (ep424 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep425 1000000000024703 24703000000000000000 (BSN.log_sum_c_eq qz137 2) (ep426 (BSN.log_sum_c_succ qz137 1 2 rfl) (ep449 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz155 := (@HDiv.hDiv Real Real Real qz253 qz333 (2 : Real))

noncomputable def ep451 := @Enclosure.Real.IsNear.mulLit_ff qz155 (Real.log Real.pi) 31718 2000 0 1 75021 65536 1 32768 1189758039 65536000 15859 32768000 (@Enclosure.Real.IsNear.of_eq qz155 (Enclosure.sfrac Bool.false 31718 2000) Bool.false 31718 2000 0 1 (BSN.t_half_eq qz137 Bool.false 31718 1000 qz138) (Enclosure.Real.IsNear.const Bool.false 31718 2000)) EMRow04.d5 rfl

noncomputable def ep452 := @ep350 15859 32768000 ep351 31834003130154812747 3377699720527872000 31240376087152237552847 ep348 (@ep353 10252971962152237552847 ep348 (ep450 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep451 rfl rfl

noncomputable def ep453 := nat_lit 497306597595129109137774355208510475865360064902290490289686697928106240

noncomputable def ep454 := nat_lit 999123166771566304614004320303359645221990541929144706089597573079296

noncomputable def ep455 := nat_lit 1300852032383898464200986351884655330697964566247637430758367717550530816

noncomputable def ep456 := BSN.sin_dyadic_bound_f 421650266 268435456 3 2 131072 49455 ep453 ep176 ep454 ep455 ep179 ep454 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 421650266) qz294 0 2 ep453 ep176 ep454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 421650266) qz295 0 2 ep455 ep179 ep454 rfl rfl rfl rfl) rfl rfl

noncomputable def ep457 := @ep347 4096 Bool.true 131071 131072 1 24703 (@ep349 1235321 131072 3 4096 ep452 rfl) (Enclosure.sfrac_false_div 1235321 131072) (BSN.cos_reduce1 qz335 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29670999747634881626112) qz67) 226375608064910080 72057594037927936 Bool.false 131071 131072 1 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q1 1235321 131072 226375608064910080 72057594037927936 1 29670999747634881626112 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131071 131072 29670999747634881626112 18889465931478580854784 421650266 268435456 49455 49406 (ep456 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep458 := nat_lit 17338672697498705670268883

noncomputable def ep459 := nat_lit 4484131590606767945416704000

noncomputable abbrev qz415 := (@Neg.neg Complex Complex.instNeg qz426)

noncomputable abbrev qz352 := qz415

noncomputable abbrev qz156 := qz352

noncomputable abbrev qz353 := (@HPow.hPow Complex Complex Complex qz407 (@Nat.cast Complex Complex.instNatCast 7) qz415)

noncomputable abbrev qz157 := qz353

noncomputable abbrev qz354 := (@Nat.cast Complex Complex.instNatCast 7)

noncomputable abbrev qz158 := (@HAdd.hAdd Complex Complex Complex qz258 (@HDiv.hDiv Complex Complex Complex qz266 qz354 (@HSub.hSub Complex Complex Complex qz256 qz334 (1 : Complex))) qz265)

noncomputable abbrev qz159 := qz354

noncomputable def ep460 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz124 1 7) (@HAdd.hAdd Complex Complex Complex qz8 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 7, @HPow.hPow Complex Complex Complex qz68 (@Nat.cast Complex Complex.instNatCast n) qz156) (@HMul.hMul Complex Complex Complex qz4 qz157 (@HAdd.hAdd Complex Complex Complex qz8 qz158 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) Bool.false 44446802118268155461651 45380435479564910592000 ep344

noncomputable def ep461 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 7, @HPow.hPow Complex Complex Complex qz68 (@Nat.cast Complex Complex.instNatCast n) qz156) (@HMul.hMul Complex Complex Complex qz4 qz157 (@HAdd.hAdd Complex Complex Complex qz8 qz158 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) Bool.false 4073764361 4294967296 757445489315 212197154226176

noncomputable def ep462 := nat_lit 1504110885712344613792883

noncomputable def ep463 := nat_lit 190897561509745251866034827165696

noncomputable def ep464 := nat_lit 52022003013788923776442164051968

noncomputable def ep465 := @ep461 Bool.true 1130760431 4294967296 749319882119 212197154226176 Bool.false 1403587117426510739651 45380435479564910592000 149874844277977462018829 ep345 Bool.false 35677943405130206653267 181521741918259642368000 ep462 ep459 Bool.false ep463 44446802118268155461651 45380435479564910592000 ep344 ep345 Bool.true ep464 12112316445864020794733 181521741918259642368000

noncomputable def ep466 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 7, @HPow.hPow Complex Complex Complex qz68 (@Nat.cast Complex Complex.instNatCast n) qz156) (BSN.headSumC qz124 7) Bool.false 4073764361 4294967296 757445489315 212197154226176 Bool.true 1130760431 4294967296 749319882119

noncomputable abbrev qz160 := (BSN.headSumC qz334 6)

noncomputable abbrev qz161 := (@HPow.hPow Complex Complex Complex qz296 qz299 qz352)

noncomputable def ep467 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz124 7) (@HAdd.hAdd Complex Complex Complex qz8 qz160 qz161) Bool.false 4073764361 4294967296 757445489315 212197154226176 Bool.true 1130760431 4294967296 749319882119 212197154226176

noncomputable def ep468 := @Enclosure.Complex.IsNear.addLitP qz160 qz161 Bool.false 4779315017 8589934592 319233275975 106098577113088 Bool.true 642695721 4294967296 632549565875 212197154226176 Bool.false

noncomputable abbrev qz162 := (BSN.headSumC qz334 5)

noncomputable abbrev qz163 := (@HPow.hPow Complex Complex Complex qz296 (@Nat.cast Complex Complex.instNatCast 5) qz352)

noncomputable def ep469 := @Enclosure.Complex.IsNear.of_eq qz160 (@HAdd.hAdd Complex Complex Complex qz8 qz162 qz163) Bool.false 4779315017 8589934592 319233275975 106098577113088 Bool.true 642695721 4294967296 632549565875 212197154226176

noncomputable def ep470 := @Enclosure.Complex.IsNear.addLitP qz162 qz163 Bool.false 4110824671 17179869184 1022235216561 424394308452352 Bool.false 1423358745 8589934592 505207007931 212197154226176 Bool.false

noncomputable abbrev qz164 := (BSN.headSumC qz334 4)

noncomputable abbrev qz165 := (@HPow.hPow Complex Complex Complex qz296 (@Nat.cast Complex Complex.instNatCast 4) qz352)

noncomputable def ep471 := @Enclosure.Complex.IsNear.of_eq qz162 (@HAdd.hAdd Complex Complex Complex qz8 qz164 qz165) Bool.false 4110824671 17179869184 1022235216561 424394308452352 Bool.false 1423358745 8589934592 505207007931 212197154226176

noncomputable def ep472 := @Enclosure.Complex.IsNear.addLitP qz164 qz165 Bool.true 4478323499 17179869184 736807505831 424394308452352 Bool.false 1372241445 8589934592 364092696519 212197154226176 Bool.false

noncomputable abbrev qz166 := (BSN.headSumC qz334 3)

noncomputable abbrev qz167 := (@HPow.hPow Complex Complex Complex qz296 qz301 qz352)

noncomputable def ep473 := @Enclosure.Complex.IsNear.of_eq qz164 (@HAdd.hAdd Complex Complex Complex qz8 qz166 qz167) Bool.true 4478323499 17179869184 736807505831 424394308452352 Bool.false 1372241445 8589934592 364092696519 212197154226176

noncomputable def ep474 := @Enclosure.Complex.IsNear.addLitP qz166 qz167 Bool.false 2516066063 8589934592 203925628551 212197154226176 Bool.true 9036495 2147483648 25088387423 26524644278272 Bool.true

noncomputable abbrev qz168 := (BSN.headSumC qz334 2)

noncomputable abbrev qz169 := (@HPow.hPow Complex Complex Complex qz296 qz302 qz352)

noncomputable def ep475 := @Enclosure.Complex.IsNear.of_eq qz166 (@HAdd.hAdd Complex Complex Complex qz8 qz168 qz169) Bool.false 2516066063 8589934592 203925628551 212197154226176 Bool.true 9036495 2147483648 25088387423 26524644278272

noncomputable def ep476 := @Enclosure.Complex.IsNear.addLitP qz168 qz169 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep477 := @Enclosure.Complex.IsNear.of_eq qz168 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz44) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz124)

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz249 qz333 qz303)

noncomputable abbrev qz171 := (Real.sin (@HMul.hMul Real Real Real qz249 qz333 qz303))

noncomputable def ep478 := @Enclosure.Complex.IsNear.of_eq qz169 (Complex.mk (@HMul.hMul Real Real Real qz0 qz83 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz83 (@Neg.neg Real Real.instNeg qz171))) Bool.true 6073868529 8589934592 203925628551 212197154226176 Bool.true 9036495 2147483648 25088387423 26524644278272 (BSN.cpow_neg_s_mk qz137 31718 1000 2 qz138 rfl)

noncomputable def ep479 := nat_lit 489823783529698895319573242949174366273403009698842795262216245933506560

noncomputable def ep480 := nat_lit 969340883777844449407366473117924317591324469170881798123224286887936

noncomputable def ep481 := nat_lit 1281302404956428215776032281053265748487574309594502083727890661932793856

noncomputable def ep482 := BSN.sin_dyadic_bound_f 420058296 268435456 3 2 131072 49455 ep479 ep176 ep480 ep481 ep179 ep480 131069 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 420058296) qz294 0 2 ep479 ep176 ep480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 420058296) qz295 0 2 ep481 ep179 ep480 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz355 := (Enclosure.Real.IsNear.const Bool.false 31718 1000)

noncomputable abbrev qz172 := qz355

noncomputable abbrev qz356 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2881643) qz12)

noncomputable def ep483 := @Enclosure.Real.IsNear.cos_image qz170 qz356 Bool.false 2881643 131072 85 65536 Bool.true 131069 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 360205467 16384000 15859 12351500 2881643 131072 85 65536 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz87 31718 1000 0 1 45426 65536 1 24703 360205467 16384000 15859 12351500 qz172 qz309 rfl) rfl) (Enclosure.sfrac_false_div 2881643 131072) (BSN.cos_reduce1 qz356 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29558974808782920482816) qz67) 226375608064910080 72057594037927936 Bool.false 131069 131072 3 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q1 2881643 131072 226375608064910080 72057594037927936 3 29558974808782920482816 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131069 131072 29558974808782920482816 18889465931478580854784 420058296 268435456 49455 49406 (ep482 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep484 := nat_lit 272555142353733983821721742293149280959708927374544167055952680757231616

noncomputable def ep485 := nat_lit 815726745293646262566350493933211994243944133185290737571611593697918976

noncomputable def ep486 := BSN.cos_dyadic_bound_f 420058296 268435456 3 2 131072 49455 ep484 ep260 ep480 ep485 ep263 ep480 780 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 420058296) qz305 0 2 ep484 ep260 ep480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 420058296) qz306 0 2 ep485 ep263 ep480 rfl rfl rfl rfl) rfl rfl

noncomputable def ep487 := @Enclosure.Real.IsNear.sin_image qz170 qz356 Bool.false 2881643 131072 85 65536 Bool.false 780 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 360205467 16384000 15859 12351500 2881643 131072 85 65536 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz87 31718 1000 0 1 45426 65536 1 24703 360205467 16384000 15859 12351500 qz172 qz309 rfl) rfl) (Enclosure.sfrac_false_div 2881643 131072) (BSN.sin_reduce1 qz356 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29558974808782920482816) qz67) 226375608064910080 72057594037927936 Bool.false 780 131072 3 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q1 2881643 131072 226375608064910080 72057594037927936 3 29558974808782920482816 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 780 131072 29558974808782920482816 18889465931478580854784 420058296 268435456 49455 49406 (ep486 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep488 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz83 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz83 (@Neg.neg Real Real.instNeg qz171)) Bool.true 6073868529 8589934592 203925628551 212197154226176 Bool.true 9036495 2147483648 25088387423 26524644278272 (@Enclosure.Real.IsNear.mulLit_ft qz83 (Real.cos qz170) 46341 65536 1 65536 131069 131072 2165291 1618935808 6073868529 8589934592 203925628551 212197154226176 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.true 131069 131072 2165291 1618935808 131069 131072 2165291 1618935808 (ep483 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz83 (@Neg.neg Real Real.instNeg qz171) 46341 65536 1 65536 195 32768 2165291 1618935808 9036495 2147483648 25088387423 26524644278272 qz311 (@Enclosure.Real.IsNear.neg qz171 Bool.false 195 32768 2165291 1618935808 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 780 131072 2165291 1618935808 195 32768 2165291 1618935808 (ep487 rfl rfl) rfl)) rfl)

noncomputable def ep489 := @ep476 6073868529 8589934592 203925628551 212197154226176 Bool.true 9036495 2147483648 25088387423 26524644278272 Bool.false 2516066063 2516066063 8589934592 203925628551 212197154226176 Bool.true 9036495 9036495 2147483648 25088387423 26524644278272 (ep477 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz44 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz45)) (ep478 ep488) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz249 qz333 qz313)

noncomputable abbrev qz174 := (Real.sin (@HMul.hMul Real Real Real qz249 qz333 qz313))

noncomputable def ep490 := @Enclosure.Complex.IsNear.of_eq qz167 (Complex.mk (@HMul.hMul Real Real Real qz0 qz89 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz89 (@Neg.neg Real Real.instNeg qz174))) Bool.true 9510455625 17179869184 328956248729 424394308452352 Bool.false 1408387425 8589934592 163385597135 212197154226176 (BSN.cpow_neg_s_mk qz137 31718 1000 3 qz138 rfl)

noncomputable def ep491 := nat_lit 35695404151148014137349860710416

noncomputable def ep492 := BSN.cos_dyadic_bound_f 77295298 268435456 2 1 131072 49455 ep491 ep203 ep491 ep491 ep204 ep491 125675 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 77295298) qz305 0 1 ep491 ep203 ep491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 77295298) qz306 0 1 ep491 ep204 ep491 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4567265) qz12)

noncomputable def ep493 := @Enclosure.Real.IsNear.cos_image qz173 qz357 Bool.false 4567265 131072 169 131072 Bool.true 125675 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 570908141 16384000 15859 12351500 4567265 131072 169 131072 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz94 31718 1000 0 1 71998 65536 1 24703 570908141 16384000 15859 12351500 qz172 qz315 rfl) rfl) (Enclosure.sfrac_false_div 4567265 131072) (BSN.cos_reduce2 qz357 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5439173061028201103360) qz67) 226375608064910080 72057594037927936 Bool.false 125675 131072 5 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q2 4567265 131072 226375608064910080 72057594037927936 5 5439173061028201103360 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 125675 131072 5439173061028201103360 18889465931478580854784 77295298 268435456 49455 49406 (ep492 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep494 := BSN.sin_dyadic_bound_f 77295298 268435456 2 1 131072 49455 ep491 ep207 ep491 ep491 ep208 ep491 37222 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 77295298) qz294 0 1 ep491 ep207 ep491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 77295298) qz295 0 1 ep491 ep208 ep491 rfl rfl rfl rfl) rfl rfl

noncomputable def ep495 := @Enclosure.Real.IsNear.sin_image qz173 qz357 Bool.false 4567265 131072 169 131072 Bool.true 37222 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 570908141 16384000 15859 12351500 4567265 131072 169 131072 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz94 31718 1000 0 1 71998 65536 1 24703 570908141 16384000 15859 12351500 qz172 qz315 rfl) rfl) (Enclosure.sfrac_false_div 4567265 131072) (BSN.sin_reduce2 qz357 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5439173061028201103360) qz67) 226375608064910080 72057594037927936 Bool.false 37222 131072 5 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q2 4567265 131072 226375608064910080 72057594037927936 5 5439173061028201103360 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 37222 131072 5439173061028201103360 18889465931478580854784 77295298 268435456 49455 49406 (ep494 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep496 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz89 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz89 (@Neg.neg Real Real.instNeg qz174)) Bool.true 9510455625 17179869184 328956248729 424394308452352 Bool.false 1408387425 8589934592 163385597135 212197154226176 (@Enclosure.Real.IsNear.mulLit_ft qz89 (Real.cos qz173) 75675 131072 1 131072 125675 131072 4305879 3237871616 9510455625 17179869184 328956248729 424394308452352 qz316 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.true 125675 131072 4305879 3237871616 125675 131072 4305879 3237871616 (ep493 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz89 (@Neg.neg Real Real.instNeg qz174) 75675 131072 1 131072 18611 65536 4305879 3237871616 1408387425 8589934592 163385597135 212197154226176 qz316 (@Enclosure.Real.IsNear.neg qz174 Bool.true 18611 65536 4305879 3237871616 (@Enclosure.Real.IsNear.recentre' qz174 Bool.true 37222 131072 4305879 3237871616 18611 65536 4305879 3237871616 (ep495 rfl rfl) rfl)) rfl)

noncomputable def ep497 := @ep474 9510455625 17179869184 328956248729 424394308452352 Bool.false 1408387425 8589934592 163385597135 212197154226176 Bool.true 38468505938226577408 4478323499 17179869184 736807505831 424394308452352 Bool.false 2946866064245391360 1372241445 8589934592 364092696519 212197154226176 (ep475 (BSN.head_sum_c_succ qz124 2 3 rfl rfl) (ep489 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep490 ep496) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz249 qz333 qz317)

noncomputable abbrev qz176 := (Real.sin (@HMul.hMul Real Real Real qz249 qz333 qz317))

noncomputable def ep498 := @Enclosure.Complex.IsNear.of_eq qz165 (Complex.mk (@HMul.hMul Real Real Real qz0 qz95 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz95 (@Neg.neg Real Real.instNeg qz176))) Bool.false 4294574085 8589934592 142713855365 212197154226176 Bool.false 12779325 2147483648 35278577853 53049288556544 (BSN.cpow_neg_s_mk qz137 31718 1000 4 qz138 rfl)

noncomputable def ep499 := nat_lit 482402379339082605579735826403575451986617993910098538624510396993699840

noncomputable def ep500 := nat_lit 940246376927964828488922264686835269635258431153872815032262679658496

noncomputable def ep501 := nat_lit 1261912499373047262034135575961776069528399565637913711839855947787862016

noncomputable def ep502 := BSN.sin_dyadic_bound_f 418461212 268435456 3 2 131072 49455 ep499 ep176 ep500 ep501 ep179 ep500 131062 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 418461212) qz294 0 2 ep499 ep176 ep500 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 418461212) qz295 0 2 ep501 ep179 ep500 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5763287) qz12)

noncomputable def ep503 := @Enclosure.Real.IsNear.cos_image qz175 qz358 Bool.false 5763287 131072 169 131072 Bool.false 131062 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 360205467 8192000 15859 12351500 5763287 131072 169 131072 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz99 31718 1000 0 1 90852 65536 1 24703 360205467 8192000 15859 12351500 qz172 qz319 rfl) rfl) (Enclosure.sfrac_false_div 5763287 131072) (BSN.cos_reduce3 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29446590032470022815744) qz67) 226375608064910080 72057594037927936 Bool.false 131062 131072 6 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q3 5763287 131072 226375608064910080 72057594037927936 6 29446590032470022815744 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131062 131072 29446590032470022815744 18889465931478580854784 418461212 268435456 49455 49406 (ep502 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep504 := nat_lit 268419209133680543023626091230736066779070111475012020486964559520792576

noncomputable def ep505 := nat_lit 803377134647185699413900429162834529797939817562728315830829153203060736

noncomputable def ep506 := BSN.cos_dyadic_bound_f 418461212 268435456 3 2 131072 49455 ep504 ep260 ep500 ep505 ep263 ep500 1560 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 418461212) qz305 0 2 ep504 ep260 ep500 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 418461212) qz306 0 2 ep505 ep263 ep500 rfl rfl rfl rfl) rfl rfl

noncomputable def ep507 := @Enclosure.Real.IsNear.sin_image qz175 qz358 Bool.false 5763287 131072 169 131072 Bool.true 1560 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 360205467 8192000 15859 12351500 5763287 131072 169 131072 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz99 31718 1000 0 1 90852 65536 1 24703 360205467 8192000 15859 12351500 qz172 qz319 rfl) rfl) (Enclosure.sfrac_false_div 5763287 131072) (BSN.sin_reduce3 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29446590032470022815744) qz67) 226375608064910080 72057594037927936 Bool.false 1560 131072 6 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q3 5763287 131072 226375608064910080 72057594037927936 6 29446590032470022815744 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1560 131072 29446590032470022815744 18889465931478580854784 418461212 268435456 49455 49406 (ep506 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep508 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz95 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz95 (@Neg.neg Real Real.instNeg qz176)) Bool.false 4294574085 8589934592 142713855365 212197154226176 Bool.false 12779325 2147483648 35278577853 53049288556544 (@Enclosure.Real.IsNear.mulLit_ff qz95 (Real.cos qz175) 65535 131072 1 131072 65531 65536 4305879 3237871616 4294574085 8589934592 142713855365 212197154226176 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 131062 131072 4305879 3237871616 65531 65536 4305879 3237871616 (ep503 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz95 (@Neg.neg Real Real.instNeg qz176) 65535 131072 1 131072 195 16384 4305879 3237871616 12779325 2147483648 35278577853 53049288556544 qz320 (@Enclosure.Real.IsNear.neg qz176 Bool.true 195 16384 4305879 3237871616 (@Enclosure.Real.IsNear.recentre' qz176 Bool.true 1560 131072 4305879 3237871616 195 16384 4305879 3237871616 (ep507 rfl rfl) rfl)) rfl)

noncomputable def ep509 := @ep472 4294574085 8589934592 142713855365 212197154226176 Bool.false 12779325 2147483648 35278577853 53049288556544 Bool.false 35311715043069919232 4110824671 17179869184 1022235216561 424394308452352 Bool.false 3056639630125301760 1423358745 8589934592 505207007931 212197154226176 (ep473 (BSN.head_sum_c_succ qz124 3 4 rfl rfl) (ep497 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep498 ep508) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz249 qz333 qz321)

noncomputable abbrev qz178 := (Real.sin (@HMul.hMul Real Real Real qz249 qz333 qz321))

noncomputable def ep510 := @Enclosure.Complex.IsNear.of_eq qz163 (Complex.mk (@HMul.hMul Real Real Real qz0 qz100 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz100 (@Neg.neg Real Real.instNeg qz178))) Bool.false 5447805363 17179869184 36385412477 60627758350336 Bool.true 2708750187 8589934592 2273974249 3789234896896 (BSN.cpow_neg_s_mk qz137 31718 1000 5 qz138 rfl)

noncomputable def ep511 := nat_lit 1947741650938321805591236161950625

noncomputable def ep512 := BSN.cos_dyadic_bound_f 210079095 268435456 2 1 131072 49455 ep511 ep203 ep511 ep511 ep204 ep511 92939 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 210079095) qz305 0 1 ep511 ep203 ep511 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 210079095) qz306 0 1 ep511 ep204 ep511 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6690975) qz12)

noncomputable def ep513 := @Enclosure.Real.IsNear.cos_image qz177 qz359 Bool.false 6690975 131072 169 131072 Bool.false 92939 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 418185971 8192000 15859 12351500 6690975 131072 169 131072 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz104 31718 1000 0 1 105476 65536 1 24703 418185971 8192000 15859 12351500 qz172 qz323 rfl) rfl) (Enclosure.sfrac_false_div 6690975 131072) (BSN.cos_reduce0 qz359 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14783002126765134970880) qz67) 226375608064910080 72057594037927936 Bool.false 92939 131072 8 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q0 6690975 131072 226375608064910080 72057594037927936 8 14783002126765134970880 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 92939 131072 14783002126765134970880 18889465931478580854784 210079095 268435456 49455 49406 (ep512 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep514 := BSN.sin_dyadic_bound_f 210079095 268435456 2 1 131072 49455 ep511 ep207 ep511 ep511 ep208 ep511 92422 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 210079095) qz294 0 1 ep511 ep207 ep511 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 210079095) qz295 0 1 ep511 ep208 ep511 rfl rfl rfl rfl) rfl rfl

noncomputable def ep515 := @Enclosure.Real.IsNear.sin_image qz177 qz359 Bool.false 6690975 131072 169 131072 Bool.false 92422 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 418185971 8192000 15859 12351500 6690975 131072 169 131072 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz104 31718 1000 0 1 105476 65536 1 24703 418185971 8192000 15859 12351500 qz172 qz323 rfl) rfl) (Enclosure.sfrac_false_div 6690975 131072) (BSN.sin_reduce0 qz359 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14783002126765134970880) qz67) 226375608064910080 72057594037927936 Bool.false 92422 131072 8 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q0 6690975 131072 226375608064910080 72057594037927936 8 14783002126765134970880 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 92422 131072 14783002126765134970880 18889465931478580854784 210079095 268435456 49455 49406 (ep514 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep516 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz100 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz100 (@Neg.neg Real Real.instNeg qz178)) Bool.false 5447805363 17179869184 36385412477 60627758350336 Bool.true 2708750187 8589934592 2273974249 3789234896896 (@Enclosure.Real.IsNear.mulLit_ff qz100 (Real.cos qz177) 58617 131072 1 131072 92939 131072 4305879 3237871616 5447805363 17179869184 36385412477 60627758350336 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.false 92939 131072 4305879 3237871616 92939 131072 4305879 3237871616 (ep513 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz100 (@Neg.neg Real Real.instNeg qz178) 58617 131072 1 131072 46211 65536 4305879 3237871616 2708750187 8589934592 2273974249 3789234896896 qz324 (@Enclosure.Real.IsNear.neg qz178 Bool.false 46211 65536 4305879 3237871616 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 92422 131072 4305879 3237871616 46211 65536 4305879 3237871616 (ep515 rfl rfl) rfl)) rfl)

noncomputable def ep517 := @ep470 5447805363 17179869184 36385412477 60627758350336 Bool.true 2708750187 8589934592 2273974249 3789234896896 Bool.false 164216013562373472256 4779315017 8589934592 319233275975 106098577113088 Bool.true 11041428411896561664 642695721 4294967296 632549565875 212197154226176 (ep471 (BSN.head_sum_c_succ qz124 4 5 rfl rfl) (ep509 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep510 ep516) rfl rfl

noncomputable abbrev qz179 := (@HMul.hMul Real Real Real qz249 qz333 qz326)

noncomputable abbrev qz180 := (Real.sin (@HMul.hMul Real Real Real qz249 qz333 qz326))

noncomputable def ep518 := @Enclosure.Complex.IsNear.of_eq qz161 (Complex.mk (@HMul.hMul Real Real Real qz0 qz107 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz107 (@Neg.neg Real Real.instNeg qz180))) Bool.false 3368213705 8589934592 118978937365 212197154226176 Bool.true 244032355 2147483648 29192579061 53049288556544 (BSN.cpow_neg_s_mk qz137 31718 1000 6 qz138 rfl)

noncomputable def ep519 := @Enclosure.Real.IsNear.mulLit_ff qz137 qz112 31718 1000 0 1 4034664351997175 2251799813685248 500000000024703 12351500000000000000 2559429678332927933 45035996273704960 7929500000391764877 6175750000000000000000 qz172 (BSN.isNear_log_sfrac 6 1 4034664351997175 2251799813685248 500000000024703 12351500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz111) Bool.false 4230652207559789772800 2361183241434822606848 1000000000049406 24703000000000000000 4034664351997175 2251799813685248 500000000024703 12351500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 26572 65536 24973259072661432 36028797018963968 24703 1000000000000000 rfl rfl rfl rfl (ep254 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep520 := nat_lit 32874521795574016742648366158096

noncomputable def ep521 := BSN.cos_dyadic_bound_f 75720742 268435456 2 1 131072 49455 ep520 ep203 ep520 ep520 ep204 ep520 125891 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 75720742) qz305 0 1 ep520 ep203 ep520 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 75720742) qz306 0 1 ep520 ep204 ep520 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz360 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 931115) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep522 := @Enclosure.Real.IsNear.cos_image qz179 qz360 Bool.false 931115 16384 85 65536 Bool.false 125891 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 2559429678332927933 45035996273704960 7929500000391764877 6175750000000000000000 931115 16384 85 65536 (ep519 rfl) rfl) (Enclosure.sfrac_false_div 931115 16384) (BSN.cos_reduce0 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 666046693973017231360) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 125891 131072 9 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q0 931115 16384 226375608064910080 72057594037927936 9 666046693973017231360 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 125891 131072 666046693973017231360 2361183241434822606848 75720742 268435456 49455 49406 (ep521 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep523 := BSN.sin_dyadic_bound_f 75720742 268435456 2 1 131072 49455 ep520 ep207 ep520 ep520 ep208 ep520 36484 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 75720742) qz294 0 1 ep520 ep207 ep520 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 75720742) qz295 0 1 ep520 ep208 ep520 rfl rfl rfl rfl) rfl rfl

noncomputable def ep524 := @Enclosure.Real.IsNear.sin_image qz179 qz360 Bool.false 931115 16384 85 65536 Bool.false 36484 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 2559429678332927933 45035996273704960 7929500000391764877 6175750000000000000000 931115 16384 85 65536 (ep519 rfl) rfl) (Enclosure.sfrac_false_div 931115 16384) (BSN.sin_reduce0 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 666046693973017231360) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 36484 131072 9 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q0 931115 16384 226375608064910080 72057594037927936 9 666046693973017231360 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 36484 131072 666046693973017231360 2361183241434822606848 75720742 268435456 49455 49406 (ep523 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep525 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz107 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz107 (@Neg.neg Real Real.instNeg qz180)) Bool.false 3368213705 8589934592 118978937365 212197154226176 Bool.true 244032355 2147483648 29192579061 53049288556544 (@Enclosure.Real.IsNear.mulLit_ff qz107 (Real.cos qz179) 26755 65536 1 65536 125891 131072 2165291 1618935808 3368213705 8589934592 118978937365 212197154226176 qz328 (@Enclosure.Real.IsNear.recentre' (Real.cos qz179) Bool.false 125891 131072 2165291 1618935808 125891 131072 2165291 1618935808 (ep522 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz107 (@Neg.neg Real Real.instNeg qz180) 26755 65536 1 65536 9121 32768 2165291 1618935808 244032355 2147483648 29192579061 53049288556544 qz328 (@Enclosure.Real.IsNear.neg qz180 Bool.false 9121 32768 2165291 1618935808 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 36484 131072 2165291 1618935808 9121 32768 2165291 1618935808 (ep524 rfl rfl) rfl)) rfl)

noncomputable def ep526 := @ep468 3368213705 8589934592 118978937365 212197154226176 Bool.true 244032355 2147483648 29192579061 53049288556544 Bool.false 69986738808421351424 4073764361 4294967296 757445489315 212197154226176 Bool.true 2428289535377932288 1130760431 4294967296 749319882119 212197154226176 (ep469 (BSN.head_sum_c_succ qz124 5 6 rfl rfl) (ep517 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep518 ep525) rfl rfl

noncomputable def ep527 := @Enclosure.Complex.IsNear.mul qz157 (@HAdd.hAdd Complex Complex Complex qz8 qz158 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 1403587117426510739651 45380435479564910592000 149874844277977462018829 ep345 Bool.false

noncomputable abbrev qz181 := (Complex.re qz353)

noncomputable abbrev qz182 := (Complex.im qz353)

noncomputable def ep528 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz181 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz158 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz182 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz158 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 20358733780286600035 242028989224346189824 1520220250420405158215

noncomputable def ep529 := nat_lit 5978842120809023927222272

noncomputable def ep530 := nat_lit 7006455610323074914713600

noncomputable def ep531 := nat_lit 679417542638104195992125399213435779022848

noncomputable def ep532 := @Enclosure.Real.IsNear.mulLit_ff qz181 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz158 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2876003673 17179869184 214755940677 424394308452352 21236482385

noncomputable abbrev qz361 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz413 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable abbrev qz183 := (Real.cos qz361)

noncomputable abbrev qz184 := (@Neg.neg Real Real.instNeg (Real.sin qz361))

noncomputable abbrev qz362 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable def ep533 := @Enclosure.Complex.IsNear.of_eq qz157 (Complex.mk (@HMul.hMul Real Real Real qz0 qz362 qz183) (@HMul.hMul Real Real Real qz0 qz362 qz184)) Bool.false 2876003673 17179869184 214755940677 424394308452352 Bool.false 2910880537 8589934592 1689256295 3315580534784 (BSN.cpow_neg_s_mk qz137 31718 1000 7 qz138 rfl)

noncomputable abbrev qz363 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1))

noncomputable def ep534 := @Enclosure.Real.IsNear.inv_image qz363 346783 131072 1 131072 24770 24771 65536 (@Enclosure.Real.IsNear.of_eq qz363 (Real.sqrt qz364) Bool.false 346783 131072 1 131072 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz364) Bool.false 346783 131072 1 131072 346783 131072 1 131072 (BSN.sqrt_enclosure 7 1 173391 173392 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep535 := BSN.log_dyadic_bound 3 11 5 4 202569142545 65536 24703 5259111624 688905 36674 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz365 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz185 := qz365

noncomputable def ep536 := @Enclosure.Real.IsNear.mulLit_ff qz137 qz185 31718 1000 0 1 4381766428990711 2251799813685248 500000000024703 12351500000000000000 69490433797363685749 1125899906842624000 7929500000391764877 6175750000000000000000 qz172 (BSN.isNear_log_sfrac 7 1 4381766428990711 2251799813685248 500000000024703 12351500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz364) Bool.false 4594615115045363777536 2361183241434822606848 1000000000049406 24703000000000000000 4381766428990711 2251799813685248 500000000024703 12351500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 36674 65536 24973259072661432 36028797018963968 24703 1000000000000000 rfl rfl rfl rfl (ep535 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep537 := nat_lit 230157235016438929913175931950625

noncomputable def ep538 := BSN.sin_dyadic_bound_f 123170345 268435456 2 1 131072 49455 ep537 ep207 ep537 ep537 ep208 ep537 58053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 123170345) qz294 0 1 ep537 ep207 ep537 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 123170345) qz295 0 1 ep537 ep208 ep537 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz186 := qz361

noncomputable abbrev qz366 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8089751) qz12)

noncomputable def ep539 := @Enclosure.Real.IsNear.cos_image qz186 qz366 Bool.false 8089751 131072 169 131072 Bool.false 58053 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz186 Bool.false 69490433797363685749 1125899906842624000 7929500000391764877 6175750000000000000000 8089751 131072 169 131072 (ep536 rfl) rfl) (Enclosure.sfrac_false_div 8089751 131072) (BSN.cos_reduce3 qz366 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8667342540771250143232) qz67) 226375608064910080 72057594037927936 Bool.false 58053 131072 9 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q3 8089751 131072 226375608064910080 72057594037927936 9 8667342540771250143232 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 58053 131072 8667342540771250143232 18889465931478580854784 123170345 268435456 49455 49406 (ep538 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep540 := BSN.cos_dyadic_bound_f 123170345 268435456 2 1 131072 49455 ep537 ep203 ep537 ep537 ep204 ep537 117514 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 123170345) qz305 0 1 ep537 ep203 ep537 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 123170345) qz306 0 1 ep537 ep204 ep537 rfl rfl rfl rfl) rfl rfl

noncomputable def ep541 := @Enclosure.Real.IsNear.sin_image qz186 qz366 Bool.false 8089751 131072 169 131072 Bool.true 117514 131072 1 24703 (@Enclosure.Real.IsNear.recentre' qz186 Bool.false 69490433797363685749 1125899906842624000 7929500000391764877 6175750000000000000000 8089751 131072 169 131072 (ep536 rfl) rfl) (Enclosure.sfrac_false_div 8089751 131072) (BSN.sin_reduce3 qz366 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8667342540771250143232) qz67) 226375608064910080 72057594037927936 Bool.false 117514 131072 9 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q3 8089751 131072 226375608064910080 72057594037927936 9 8667342540771250143232 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 117514 131072 8667342540771250143232 18889465931478580854784 123170345 268435456 49455 49406 (ep540 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz187 := (Real.sin qz361)

noncomputable def ep542 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz362 qz183) (@HMul.hMul Real Real Real qz0 qz362 qz184) Bool.false 2876003673 17179869184 214755940677 424394308452352 Bool.false 2910880537 8589934592 1689256295 3315580534784 (@Enclosure.Real.IsNear.mulLit_ff qz362 qz183 49541 131072 1 131072 58053 131072 4305879 3237871616 2876003673 17179869184 214755940677 424394308452352 (@Enclosure.Real.IsNear.recentre' qz362 Bool.false 49541 131072 1 131072 49541 131072 1 131072 (ep534 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 58053 131072 4305879 3237871616 58053 131072 4305879 3237871616 (ep539 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz362 qz184 49541 131072 1 131072 58757 65536 4305879 3237871616 2910880537 8589934592 1689256295 3315580534784 (@Enclosure.Real.IsNear.recentre' qz362 Bool.false 49541 131072 1 131072 49541 131072 1 131072 (ep534 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz187 Bool.true 58757 65536 4305879 3237871616 (@Enclosure.Real.IsNear.recentre' qz187 Bool.true 117514 131072 4305879 3237871616 58757 65536 4305879 3237871616 (ep541 rfl rfl) rfl)) rfl)

noncomputable def ep543 := @ep532 42263824008 0 1 20358733780286600035 242028989224346189824 1520220250420405158215 ep529 (@Enclosure.Complex.IsNear.re_isNear qz157 Bool.false 2876003673 17179869184 214755940677 424394308452352 Bool.false 2910880537 8589934592 1689256295 3315580534784 (ep533 ep542))

noncomputable def ep544 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz158 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 21236482385 42263824008 0 1 Bool.false

noncomputable def ep545 := @Enclosure.Complex.IsNear.addLitP qz158 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) Bool.false 249820381 503140762 0 1 Bool.true 55506500

noncomputable def ep546 := @ep545 251570381 0 1 Bool.false 1 168 0 1 Bool.false 15859 42000 0 1 Bool.false 42472964770 21236482385 42263824008 0 1 Bool.false 1658381672279 1658381672279 10565956002000 0 1

noncomputable abbrev qz188 := (@HDiv.hDiv Complex Complex Complex qz266 qz354 (@HSub.hSub Complex Complex Complex qz256 qz334 (1 : Complex)))

noncomputable def ep547 := @Enclosure.Complex.IsNear.addLitP qz188 qz41 Bool.true 14000000 4025126096 0 1 Bool.true 888104000 4025126096 0 1

noncomputable def ep548 := @Enclosure.Complex.IsNear.of_eq qz188 (Complex.mk (Enclosure.sfrac Bool.true 14000000 4025126096) (Enclosure.sfrac Bool.true 888104000 4025126096)) Bool.true 14000000 4025126096 0 1 Bool.true 888104000 4025126096 0 1

noncomputable def ep549 := @ep547 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 3997126096 249820381 503140762 0 1 Bool.true 888104000 55506500 251570381 0 1 (ep548 (BSN.N_div_s_sub_one_mk qz137 31718 1000 7 qz138 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 14000000 4025126096) (Enclosure.sfrac Bool.true 888104000 4025126096) Bool.true 14000000 4025126096 0 1 Bool.true 888104000 4025126096 0 1 (Enclosure.Real.IsNear.const Bool.true 14000000 4025126096) (Enclosure.Real.IsNear.const Bool.true 888104000 4025126096))) qz43 rfl

noncomputable abbrev qz367 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz406 (@Nat.cast Complex Complex.instNatCast 7) 1))

noncomputable abbrev qz189 := qz367

noncomputable def ep550 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz189)) Bool.false 1 168 0 1

noncomputable def ep551 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz189) Bool.false 0 1 0 1 Bool.false

noncomputable def ep552 := @ep551 0 1 0 1 Bool.false 1 168 0 1 Bool.false 15859 42000 0 1 Bool.false 1 1 168 0 1 Bool.false 15859 15859 42000 0

noncomputable def ep553 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (Complex.mk qz44 qz44) Bool.false 0 1 0 1 Bool.false

noncomputable def ep554 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz189 Bool.false 1 168 0 1 Bool.false 15859 42000 0 1

noncomputable abbrev qz190 := (Complex.re qz367)

noncomputable abbrev qz191 := (Complex.im qz367)

noncomputable def ep555 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz190) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz191) 1 168 0 1 0 1 0

noncomputable def ep556 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz190 1 24 0 1 1 7 0 1 1

noncomputable def ep557 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep558 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep559 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) qz124 Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 (BSN.ascPochhammer_one_eval qz124)

noncomputable def ep560 := ep559 (@Enclosure.Complex.IsNear.of_eq qz124 (Complex.mk qz32 qz137) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 (BSN.s_crit_mk qz137 Bool.false 31718 1000 qz138) (@Enclosure.Complex.IsNear.mk qz32 qz137 Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 qz33 qz172))

noncomputable def ep561 := @ep558 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep283) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep560)

noncomputable def ep562 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 31718 1000 0 1 0 1 0

noncomputable def ep563 := @ep562 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep283) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep560)

noncomputable def ep564 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) 15859 6000 0 1 0 1 0 1 15859

noncomputable def ep565 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 31718 1000 0 1 15859 6000 0

noncomputable def ep566 := @ep565 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep283) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep560)

noncomputable def ep567 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep568 := @ep567 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep283) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep560)

noncomputable def ep569 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 15859 6000 0 1 (@ep557 1 24 0 1 (ep561 rfl) (ep563 rfl) rfl rfl) (@ep564 15859 6000 0 1 (ep566 rfl) (ep568 rfl) rfl rfl)

noncomputable def ep570 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 15859 6000 0 1 ep569

noncomputable abbrev qz192 := (@Enclosure.Complex.IsNear.of_eq qz367 (Complex.mk (Enclosure.sfrac Bool.false 1 7) qz281) Bool.false 1 7 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 7 1 7 EMRow04.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 7) qz281 Bool.false 1 7 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 7) qz282))

noncomputable def ep571 := @ep556 168 0 1 ep570 (@Enclosure.Complex.IsNear.re_isNear qz189 Bool.false 1 7 0 1 Bool.false 0 1 0 1 qz192)

noncomputable def ep572 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz191 15859 6000 0 1 0 1 0 1 0

noncomputable def ep573 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 15859 6000 0 1 ep569

noncomputable def ep574 := @ep572 1 0 1 ep573 (@Enclosure.Complex.IsNear.im_isNear qz189 Bool.false 1 7 0 1 Bool.false 0 1 0 1 qz192)

noncomputable def ep575 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz191) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz190) 0 1 0 1 15859 42000 0

noncomputable def ep576 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz191 1 24 0 1 0 1 0 1 0

noncomputable def ep577 := @ep576 1 0 1 ep570 (@Enclosure.Complex.IsNear.im_isNear qz189 Bool.false 1 7 0 1 Bool.false 0 1 0 1 qz192)

noncomputable def ep578 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz116) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)))) qz190 15859 6000 0 1 1 7 0 1 15859

noncomputable def ep579 := @ep578 42000 0 1 ep573 (@Enclosure.Complex.IsNear.re_isNear qz189 Bool.false 1 7 0 1 Bool.false 0 1 0 1 qz192)

noncomputable def ep580 := @ep552 1 (@ep553 0 1 0 1 (BSN.bern_sum_base qz124 7) qz61) (ep554 (@ep555 1 1 1 168 0 1 (ep571 rfl) (ep574 rfl) rfl rfl) (@ep575 1 15859 15859 42000 0 1 (ep577 rfl) (ep579 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep581 := ep546 (ep549 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep550 Bool.false 15859 42000 0 1 (BSN.bern_sum_succ qz124 7 0 1 1 rfl rfl) (ep580 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep582 := @Enclosure.Real.IsNear.mulLit_ff qz182 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz158 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2910880537 8589934592 1689256295 3315580534784 1658381672279

noncomputable def ep583 := @ep582 10565956002000 0 1 4827350932754453533823 90760870959129821184000 560286335881985549261 ep530 (@Enclosure.Complex.IsNear.im_isNear qz157 Bool.false 2876003673 17179869184 214755940677 424394308452352 Bool.false 2910880537 8589934592 1689256295 3315580534784 (ep533 ep542))

noncomputable def ep584 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz158 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 21236482385 42263824008 0 1 Bool.false

noncomputable def ep585 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz181 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz158 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz182 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz158 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 1589837260236762093589 60507247306086547456000 118715772010590993130961

noncomputable def ep586 := nat_lit 1494710530202255981805568000

noncomputable def ep587 := nat_lit 4317548289973545996674277917166593065877504

noncomputable def ep588 := @Enclosure.Real.IsNear.mulLit_ff qz181 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz158 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2876003673 17179869184 214755940677 424394308452352 1658381672279

noncomputable def ep589 := @ep588 10565956002000 0 1 1589837260236762093589 60507247306086547456000 118715772010590993130961 ep586 (@Enclosure.Complex.IsNear.re_isNear qz157 Bool.false 2876003673 17179869184 214755940677 424394308452352 Bool.false 2910880537 8589934592 1689256295 3315580534784 (ep533 ep542))

noncomputable def ep590 := @Enclosure.Real.IsNear.mulLit_ff qz182 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz158 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz159 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2910880537 8589934592 1689256295 3315580534784 21236482385

noncomputable def ep591 := @ep590 42263824008 0 1 61816863248839840745 363043483836519284736 35873861552517863575 140129112206461498294272 (@Enclosure.Complex.IsNear.im_isNear qz157 Bool.false 2876003673 17179869184 214755940677 424394308452352 Bool.false 2910880537 8589934592 1689256295 3315580534784 (ep533 ep542))

noncomputable abbrev qz368 := (ep581 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep592 := @ep527 35677943405130206653267 181521741918259642368000 ep462 ep459 (@ep528 ep529 4827350932754453533823 90760870959129821184000 560286335881985549261 ep530 ep531 1403587117426510739651 45380435479564910592000 149874844277977462018829 ep345 (ep543 (@ep544 1658381672279 10565956002000 0 1 qz368) rfl) (ep583 (@ep584 1658381672279 10565956002000 0 1 qz368) rfl) rfl rfl) (@ep585 ep586 61816863248839840745 363043483836519284736 35873861552517863575 140129112206461498294272 ep587 35677943405130206653267 181521741918259642368000 ep462 ep459 (ep589 (@ep584 1658381672279 10565956002000 0 1 qz368) rfl) (ep591 (@ep544 1658381672279 10565956002000 0 1 qz368) rfl) rfl rfl)

noncomputable def ep593 := @ep465 ep458 ep459 (@ep466 212197154226176 (BSN.head_sum_c_eq qz124 7) (ep467 (BSN.head_sum_c_succ qz124 6 7 rfl rfl) (ep526 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep592 rfl rfl rfl

noncomputable def ep594 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz124 1 7) Bool.false 44446802118268155461651 45380435479564910592000 ep344 ep345 Bool.true 12112316445864020794733 181521741918259642368000 ep458 ep459 (@ep460 ep345 Bool.true 12112316445864020794733 181521741918259642368000 ep458 ep459 (BSN.zetaApproximant_eq_folded' qz124 1 7 rfl) (ep593 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep595 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) (Complex.im (zetaApproximant qz124 1 7)) 3 131072 78205

noncomputable def ep596 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123)) Bool.false 3 131072 78205

noncomputable def ep597 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123) qz335 Bool.false 1235321 131072 3

noncomputable def ep598 := nat_lit 276725497849192423434147532591529535323076476297685447808087986659205376

noncomputable def ep599 := nat_lit 828178247214034137693214589133981886678785447809198054012084764831457536

noncomputable def ep600 := BSN.cos_dyadic_bound_f 421650266 268435456 3 2 131072 49455 ep598 ep260 ep454 ep599 ep263 ep454 3 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 421650266) qz305 0 2 ep598 ep260 ep454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 421650266) qz306 0 2 ep599 ep263 ep454 rfl rfl rfl rfl) rfl rfl

noncomputable def ep601 := @ep597 4096 Bool.false 3 131072 1 24703 (@ep349 1235321 131072 3 4096 ep452 rfl) (Enclosure.sfrac_false_div 1235321 131072) (BSN.sin_reduce1 qz335 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29670999747634881626112) qz67) 226375608064910080 72057594037927936 Bool.false 3 131072 1 1000000000000000 49406 24703 (BSN.sin_reduce_arg_pos_rat_q1 1235321 131072 226375608064910080 72057594037927936 1 29670999747634881626112 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 3 131072 29670999747634881626112 18889465931478580854784 421650266 268435456 49455 49406 (ep600 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep602 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz124 1 7) Bool.false 44446802118268155461651 45380435479564910592000 ep344 ep345 Bool.true 12112316445864020794733 181521741918259642368000 ep458 ep459 (@ep460 ep345 Bool.true 12112316445864020794733 181521741918259642368000 ep458 ep459 (BSN.zetaApproximant_eq_folded' qz124 1 7 rfl) (ep593 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow04.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 7 qz137) Bool.true ep328 ep329 ep330 ep331 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 7 qz137) ep332 Bool.true ep328 ep329 ep330 ep331 (@Eq.refl Real ep332) (@ep333 Bool.true ep328 ep329 ep330 ep331 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz121 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz122 (@Nat.cast Complex Complex.instNatCast j))))) qz123) (zetaApproximant qz124 1 7)) (@ep335 ep336 ep337 ep338 12112316445864020794733 ep339 ep340 ep341 ep342 ep328 ep329 ep330 ep331 (@ep343 101183488 44446802118268155461651 45380435479564910592000 ep344 ep345 ep334 ep336 ep337 ep338 (@ep346 101183488 131071 131072 78205 101183488 (ep457 rfl rfl) rfl) ep594 rfl) (@ep595 101183488 12112316445864020794733 181521741918259642368000 ep458 ep459 12112316445864020794733 ep339 ep340 ep341 (@ep596 101183488 3 131072 78205 101183488 (ep601 rfl rfl) rfl) ep602 rfl) rfl rfl))

theorem EMRow04.d11 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow04.d12 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow04.d13 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow04.d14 : @Eq Nat (Nat.pow 6 (Nat.succ (Nat.mul 2 3))) 279936 := @Eq.refl Nat 279936

noncomputable abbrev qz416 := (@HAdd.hAdd Complex Complex Complex qz419 qz423 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz369 := qz416

noncomputable abbrev qz193 := (@HDiv.hDiv Real Real Real qz253 (@Norm.norm Complex Complex.instNorm qz369) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz261) qz312))

noncomputable abbrev qz194 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz195 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz370 := (@HPow.hPow Complex Complex Complex qz407 (@Nat.cast Complex Complex.instNatCast 6) (@HSub.hSub Complex Complex Complex qz397 qz408 qz409))

noncomputable abbrev qz196 := qz370

noncomputable def ep603 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 6))) (@HMul.hMul Real Real Real qz0 qz193 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) 46194987 1073741824 571445 9663676416 3920283332807 8796093022208 172011499

noncomputable def ep604 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 6)) 123 8192 1 221184 375569 131072 403 131072 46194987 1073741824

noncomputable abbrev qz371 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz372 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz197 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz371 qz372 2))

noncomputable def ep605 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz197 96 162 0 1 3321 131072 1 131072 123 8192 1 221184

noncomputable def ep606 := nat_lit 781950621441006189802102638025

noncomputable def ep607 := nat_lit 19807040628566084398385987584

noncomputable def ep608 := nat_lit 26986075409044041160201671

noncomputable def ep609 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz198 := qz372

noncomputable abbrev qz373 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz198 1)

noncomputable def ep610 := @Enclosure.Real.IsNear.mulLit_ff qz373 qz198 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep606 ep607 ep608 ep609

noncomputable def ep611 := ep610 (@Enclosure.Real.IsNear.of_eq qz373 qz198 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz198) (@Enclosure.Real.IsNear.of_eq qz198 qz251 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz252)) (@Enclosure.Real.IsNear.of_eq qz198 qz251 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz252) rfl

noncomputable abbrev qz199 := (@HPow.hPow Real Nat Real qz371 qz372 2)

noncomputable def ep612 := @Enclosure.Real.IsNear.inv_image qz199 ep606 ep607 ep608 ep609 1660 1661 65536 (@Enclosure.Real.IsNear.of_eq qz199 (@HMul.hMul Real Real Real qz0 qz373 qz198) Bool.false ep606 ep607 ep608 ep609 (BSN.pow_succ_r qz198 1 2 rfl) ep611) rfl rfl rfl

noncomputable def ep613 := ep605 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 3321 131072 1 131072 3321 131072 1 131072 (ep612 rfl rfl rfl) rfl)

noncomputable def ep614 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 6)) (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 6)) (Complex.re (zetaApproximant qz11 1 6))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 6)) (Complex.im (zetaApproximant qz11 1 6))))) Bool.false 375569 131072 403 131072

noncomputable def ep615 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 6)) (Complex.re (zetaApproximant qz11 1 6))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 6)) (Complex.im (zetaApproximant qz11 1 6))))) Bool.false 375569 131072 403 131072

noncomputable def ep616 := nat_lit 4810571018663311652297298150833009

noncomputable def ep617 := nat_lit 585915257262125780584232701132800

noncomputable def ep618 := nat_lit 1203831003131658580625490885554520907643037153623

noncomputable def ep619 := nat_lit 68459593725152000791126750272056995959086776320000

noncomputable def ep620 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 6)) (Complex.re (zetaApproximant qz11 1 6))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 6)) (Complex.im (zetaApproximant qz11 1 6)))) ep616 ep617 ep618 ep619 187583 187986

noncomputable def ep621 := nat_lit 73605353432764462550243660471431883097361

noncomputable def ep622 := nat_lit 8974802654502678089909869969752352358400

noncomputable def ep623 := nat_lit 5481303126224445515580065757759647886371243971

noncomputable def ep624 := nat_lit 322162794000715297840596471868503510395702476800

noncomputable def ep625 := nat_lit 80943370150269422129083143208497234841

noncomputable def ep626 := nat_lit 78108177617927817129453824061191463578295619571

noncomputable def ep627 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 6)) (Complex.re (zetaApproximant qz11 1 6))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 6)) (Complex.im (zetaApproximant qz11 1 6))) ep621 ep622 ep623 ep624 ep625 ep622 ep626

noncomputable def ep628 := nat_lit 136919187450304001582253500544113991918173552640000

noncomputable def ep629 := nat_lit 661319972147271338370770489810986455687691665754348794623340074352543150165196800

noncomputable def ep630 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz11 1 6)) (Complex.re (zetaApproximant qz11 1 6)) 271303065653089262231 94735435052057886720 408718558890826232969 137661732475940351508480 271303065653089262231 94735435052057886720 408718558890826232969 137661732475940351508480 ep621

noncomputable def ep631 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz11 1 6)) (Complex.im (zetaApproximant qz11 1 6)) 8996853347158073029 94735435052057886720 34605572639697807566851 ep182 8996853347158073029 94735435052057886720 34605572639697807566851 ep182 ep625

noncomputable def ep632 := @ep603 61572651155456 4615707579176676491264 4298712666311 8796093022208 34317045571 554153860399104 (@ep604 571445 9663676416 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz197) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow04.d11 EMRow04.d12 rfl) (ep613 rfl)) (ep614 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz11 1 6)) (@ep615 375569 131072 403 131072 (@ep620 65536 (@ep627 ep628 ep629 ep616 ep617 ep618 ep619 (@ep630 ep622 ep623 ep624 ep319 ep319 rfl) (@ep631 ep622 ep626 ep628 ep327 ep327 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz200 := (@Norm.norm Complex Complex.instNorm qz369)

noncomputable abbrev qz374 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep633 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz193 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz200 qz374) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) Bool.false 3920283332807 8796093022208 172011499 61572651155456 (BSN.zrb_shape_eq qz200 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) qz37 3)

noncomputable def ep634 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz200 qz374) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) 3655661 458752 1 458752 7506709 134217728 45 134217728

noncomputable def ep635 := @Enclosure.Real.IsNear.mulLit_ff qz200 qz374 3655661 131072 1 131072 2 7 0 1 3655661 458752

noncomputable abbrev qz375 := (Complex.re qz416)

noncomputable abbrev qz376 := (Complex.im qz416)

noncomputable abbrev qz201 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz249 qz375 qz375) (@HMul.hMul Real Real Real qz249 qz376 qz376))

noncomputable abbrev qz202 := qz369

noncomputable def ep636 := @Enclosure.Real.IsNear.of_eq qz200 (Real.sqrt qz201) Bool.false 3655661 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz202)

noncomputable def ep637 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz201) Bool.false 3655661 131072 1 131072 3655661

noncomputable def ep638 := @Enclosure.Real.IsNear.sqrt_image qz201 7778789 10000 0 1 1827830 1827831 65536

noncomputable abbrev qz203 := (@HMul.hMul Real Real Real qz249 qz375 qz375)

noncomputable abbrev qz204 := (@HMul.hMul Real Real Real qz249 qz376 qz376)

noncomputable def ep639 := @Enclosure.Real.IsNear.addLit_ff qz203 qz204 49 4 0 1 7656289 10000 0 1

noncomputable abbrev qz205 := qz375

noncomputable def ep640 := @Enclosure.Real.IsNear.mulLit_ff qz205 qz205 7 2 0 1 7 2 0 1 49 4

noncomputable def ep641 := @Enclosure.Complex.IsNear.of_eq qz202 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz37) Bool.false 7 2 0 1 Bool.false 27670 1000 0 1 (BSN.s_add_nat_mk qz37 Bool.false 27670 1000 3 qz38)

noncomputable abbrev qz206 := (ep641 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz260 Bool.false 7 2 0 1 Bool.false 27670 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz307))

noncomputable def ep642 := @ep640 0 1 (@Enclosure.Complex.IsNear.re_isNear qz202 Bool.false 7 2 0 1 Bool.false 27670 1000 0 1 qz206)

noncomputable def ep643 := ep642 (@Enclosure.Complex.IsNear.re_isNear qz202 Bool.false 7 2 0 1 Bool.false 27670 1000 0 1 qz206)

noncomputable abbrev qz207 := qz376

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_ff qz207 qz207 27670 1000 0 1 27670 1000 0 1 7656289 10000

noncomputable def ep645 := @ep644 0 1 (@Enclosure.Complex.IsNear.im_isNear qz202 Bool.false 7 2 0 1 Bool.false 27670 1000 0 1 qz206)

noncomputable def ep646 := ep645 (@Enclosure.Complex.IsNear.im_isNear qz202 Bool.false 7 2 0 1 Bool.false 27670 1000 0 1 qz206)

noncomputable def ep647 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))))) Bool.false 7506709 134217728

noncomputable def ep648 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))))) Bool.false 7506709 134217728

noncomputable def ep649 := nat_lit 5847112447939226267031601012995890474031012661

noncomputable def ep650 := nat_lit 1869226869072537946270978678519234560000000000000

noncomputable def ep651 := nat_lit 12331838924577231086376045824719626430533597041284060087

noncomputable def ep652 := nat_lit 336778193801178787234614526312822425929000996044800000000000000

noncomputable def ep653 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)))) ep649 ep650 ep651 ep652

noncomputable def ep654 := nat_lit 14697258558477288328156536004926103685051866009

noncomputable def ep655 := nat_lit 18692268690725379462709786785192345600000000000000

noncomputable def ep656 := nat_lit 1689353900273153017404730775814726301293687344359744883

noncomputable def ep657 := nat_lit 134711277520471514893845810525128970371600398417920000000000000

noncomputable def ep658 := nat_lit 4863762880101663815795497125003644561695362289

noncomputable def ep659 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196))) ep654 ep655 ep656 ep657 ep658

noncomputable def ep660 := nat_lit 2076918743413931051412198531688038400000000000000

noncomputable def ep661 := nat_lit 16216908347788697085728437770365621354598757360769395759

noncomputable def ep662 := nat_lit 673556387602357574469229052625644851858001992089600000000000000

noncomputable def ep663 := nat_lit 121439774379738921622166929956835497028594467676391638732145854666341404926541824000000000000000

noncomputable def ep664 := nat_lit 4323455642275676160000000

noncomputable def ep665 := nat_lit 5190592981933210969571328000000

noncomputable def ep666 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) 121232250488379899282747 ep664 1160686069993559346140213 ep665 121232250488379899282747 ep664 1160686069993559346140213

noncomputable def ep667 := nat_lit 1441151880758558720000000

noncomputable def ep668 := nat_lit 6456148730351537805291469

noncomputable def ep669 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196) Bool.true 121232250488379899282747 ep664 1160686069993559346140213 ep665 Bool.false 69740683106072769638233 ep667 ep668

noncomputable def ep670 := nat_lit 25952964909666054847856640000000

noncomputable def ep671 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196 Bool.true 121232250488379899282747 ep664 1160686069993559346140213 ep665 Bool.false 69740683106072769638233 ep667 ep668 ep670

noncomputable def ep672 := nat_lit 24717109437777195093196800000

noncomputable abbrev qz208 := (Complex.re qz370)

noncomputable abbrev qz209 := (Complex.im qz370)

noncomputable def ep673 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz208) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz209) 201353992447735218441 28823037615171174400000 882413414594145780953 ep672 151435349355540182048897 ep664 975379252928788732140083

noncomputable def ep674 := nat_lit 3494281715998427815174526437760189648076800000

noncomputable def ep675 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz208 22956367 4800000 0 1 26313483198069 18014398509481984 269071055631713 36045784596758409510912 201353992447735218441

noncomputable def ep676 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) 22956367 4800000 0 1 0 1 0 1 22956367

noncomputable def ep677 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 68869101 20000 0 1 22956367 4800000 0

noncomputable def ep678 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz44) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow04.d13 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz44 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz45)

noncomputable abbrev qz377 := (@HAdd.hAdd Complex Complex Complex qz399 qz402 qz410)

noncomputable abbrev qz210 := qz377

noncomputable def ep679 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) qz210) Bool.true 68869101 20000 0 1 Bool.true 21025849163 1000000 0 1

noncomputable abbrev qz211 := (Complex.re qz377)

noncomputable abbrev qz212 := (Complex.im qz377)

noncomputable def ep680 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz211) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz212) 7648789 4000 0 1 7656289 5000 0 1

noncomputable def ep681 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz211 7648789 10000 0 1 5 2 0 1 7648789 4000

noncomputable abbrev qz378 := (@HAdd.hAdd Complex Complex Complex qz399 qz402 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz213 := qz378

noncomputable def ep682 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz213) Bool.true 7648789 10000 0 1 Bool.false 2767 50 0 1

noncomputable abbrev qz214 := (Complex.re qz378)

noncomputable abbrev qz215 := (Complex.im qz378)

noncomputable def ep683 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz214) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz215) 3 4 0 1 7656289 10000 0 1

noncomputable def ep684 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz214 1 2 0 1 3 2 0 1 3 4

noncomputable def ep685 := @ep684 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep285)

noncomputable def ep686 := @Enclosure.Complex.IsNear.of_eq qz213 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz37) Bool.false 3 2 0 1 Bool.false 27670 1000 0 1 (BSN.s_add_nat_mk qz37 Bool.false 27670 1000 1 qz38)

noncomputable abbrev qz216 := (ep686 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz260 Bool.false 3 2 0 1 Bool.false 27670 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz307))

noncomputable def ep687 := ep685 (@Enclosure.Complex.IsNear.re_isNear qz213 Bool.false 3 2 0 1 Bool.false 27670 1000 0 1 qz216)

noncomputable def ep688 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz215 27670 1000 0 1 27670 1000 0 1 7656289 10000

noncomputable def ep689 := @ep688 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep285)

noncomputable def ep690 := ep689 (@Enclosure.Complex.IsNear.im_isNear qz213 Bool.false 3 2 0 1 Bool.false 27670 1000 0 1 qz216)

noncomputable def ep691 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz213 Bool.true 7648789 10000 0 1 Bool.false 2767 50 0 1 (@ep683 30595156 7648789 10000 0 1 (ep687 rfl) (ep690 rfl) rfl rfl)

noncomputable def ep692 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz215) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz214) 2767 200 0 1 8301 200 0 1

noncomputable def ep693 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz215 1 2 0 1 27670 1000 0 1 2767 200

noncomputable def ep694 := @ep693 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep285)

noncomputable def ep695 := ep694 (@Enclosure.Complex.IsNear.im_isNear qz213 Bool.false 3 2 0 1 Bool.false 27670 1000 0 1 qz216)

noncomputable def ep696 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz214 27670 1000 0 1 3 2 0 1 8301 200

noncomputable def ep697 := @ep696 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 27670 1000 0 1 ep285)

noncomputable def ep698 := ep697 (@Enclosure.Complex.IsNear.re_isNear qz213 Bool.false 3 2 0 1 Bool.false 27670 1000 0 1 qz216)

noncomputable abbrev qz217 := (ep682 (BSN.ascPochhammer_succ_eval_c 1 2 qz261 rfl) (ep691 (@ep692 2213600 2767 50 0 1 (ep695 rfl) (ep698 rfl) rfl rfl)))

noncomputable def ep699 := @ep681 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7648789 10000 0 1 Bool.false 2767 50 0 1 qz217)

noncomputable def ep700 := @Enclosure.Complex.IsNear.of_eq qz210 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz37) Bool.false 5 2 0 1 Bool.false 27670 1000 0 1 (BSN.s_add_nat_mk qz37 Bool.false 27670 1000 2 qz38)

noncomputable abbrev qz218 := (ep700 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz260 Bool.false 5 2 0 1 Bool.false 27670 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz307))

noncomputable def ep701 := ep699 (@Enclosure.Complex.IsNear.re_isNear qz210 Bool.false 5 2 0 1 Bool.false 27670 1000 0 1 qz218)

noncomputable def ep702 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz212 2767 50 0 1 27670 1000 0 1 7656289 5000

noncomputable def ep703 := @ep702 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7648789 10000 0 1 Bool.false 2767 50 0 1 qz217)

noncomputable def ep704 := ep703 (@Enclosure.Complex.IsNear.im_isNear qz210 Bool.false 5 2 0 1 Bool.false 27670 1000 0 1 qz218)

noncomputable def ep705 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) qz210 Bool.true 68869101 20000 0 1 Bool.true 21025849163 1000000 0 1 (@ep680 68869101000 68869101 20000 0 1 (ep701 rfl) (ep704 rfl) rfl rfl)

noncomputable def ep706 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz212) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz211) 21164199163 1000000 0 1 2767 20 0 1

noncomputable def ep707 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz212 7648789 10000 0 1 27670 1000 0 1 21164199163 1000000

noncomputable def ep708 := @ep707 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7648789 10000 0 1 Bool.false 2767 50 0 1 qz217)

noncomputable def ep709 := ep708 (@Enclosure.Complex.IsNear.im_isNear qz210 Bool.false 5 2 0 1 Bool.false 27670 1000 0 1 qz218)

noncomputable def ep710 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz211 2767 50 0 1 5 2 0 1 2767 20

noncomputable def ep711 := @ep710 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7648789 10000 0 1 Bool.false 2767 50 0 1 qz217)

noncomputable def ep712 := ep711 (@Enclosure.Complex.IsNear.re_isNear qz210 Bool.false 5 2 0 1 Bool.false 27670 1000 0 1 qz218)

noncomputable abbrev qz219 := (ep679 (BSN.ascPochhammer_succ_eval_c 2 3 qz261 rfl) (ep705 (@ep706 420516983260 21025849163 1000000 0 1 (ep709 rfl) (ep712 rfl) rfl rfl)))

noncomputable def ep713 := @ep677 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep678) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 68869101 20000 0 1 Bool.true 21025849163 1000000 0 1 qz219)

noncomputable def ep714 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 21025849163 1000000 0 1 0 1 0

noncomputable def ep715 := @ep714 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep678) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 68869101 20000 0 1 Bool.true 21025849163 1000000 0 1 qz219)

noncomputable def ep716 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) 21025849163 720000000 0 1 0 1 0 1 21025849163

noncomputable def ep717 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 21025849163 1000000 0 1 21025849163 720000000 0

noncomputable def ep718 := @ep717 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep678) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 68869101 20000 0 1 Bool.true 21025849163 1000000 0 1 qz219)

noncomputable def ep719 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 68869101 20000 0 1 0 1 0

noncomputable def ep720 := @ep719 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep678) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 68869101 20000 0 1 Bool.true 21025849163 1000000 0 1 qz219)

noncomputable def ep721 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 22956367 4800000 0 1 Bool.false 21025849163 720000000 0 1 (@ep676 22956367 4800000 0 1 (ep713 rfl) (ep715 rfl) rfl rfl) (@ep716 21025849163 720000000 0 1 (ep718 rfl) (ep720 rfl) rfl rfl)

noncomputable def ep722 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 22956367 4800000 0 1 Bool.false 21025849163 720000000 0 1 ep721

noncomputable def ep723 := @Enclosure.Complex.IsNear.re_isNear qz196 Bool.false 26313483198069 18014398509481984 269071055631713 36045784596758409510912 Bool.false 21607024978857 18014398509481984 231947648194205 36045784596758409510912

noncomputable abbrev qz379 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 279936)))

noncomputable def ep724 := @Enclosure.Complex.IsNear.of_eq qz196 (Complex.mk (@HMul.hMul Real Real Real qz0 qz379 qz108) (@HMul.hMul Real Real Real qz0 qz379 qz109)) Bool.false 26313483198069 18014398509481984 269071055631713 36045784596758409510912 Bool.false 21607024978857 18014398509481984 231947648194205

noncomputable abbrev qz380 := (Real.sqrt (@Nat.cast Real Real.instNatCast 279936))

noncomputable abbrev qz381 := (@Nat.cast Real Real.instNatCast 279936)

noncomputable def ep725 := @Enclosure.Real.IsNear.inv_image qz380 71013228775 134217728 1 134217728 126838 126839 67108864 (@Enclosure.Real.IsNear.of_eq qz380 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz381 qz304)) Bool.false 71013228775 134217728 1 134217728 (BSN.sqrt_natCast_div_one 279936) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz381 qz304)) Bool.false 71013228775 134217728 1 134217728 71013228775 134217728 1 134217728 (BSN.sqrt_enclosure 279936 1 35506614387 35506614388 67108864 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep726 := nat_lit 4332208541070713612664832

noncomputable def ep727 := nat_lit 2417851639229258349412352

noncomputable def ep728 := BSN.log_dyadic_bound 2 10 6 5 103950000000000 67108864 32015088 1420244935680 967680 27210302 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 2) (BSN.artanhQ 10) 0 5 1420244935680 103950000000000 967680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep729 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz112 27670 1000 0 1 4034683612241143 2251799813685248 31250002000943 1000471500000000000000 11163969555071242681 225179981368524800 86468755536609281 100047150000000000000000 qz88 (BSN.isNear_log_sfrac 6 1 4034683612241143 2251799813685248 31250002000943 1000471500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz111) Bool.false ep726 ep727 1000000064030176 32015088000000000000000 4034683612241143 2251799813685248 31250002000943 1000471500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 27210302 67108864 24973259072661432 36028797018963968 32015088 1000000000000000 rfl rfl rfl rfl (ep728 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep730 := nat_lit 4271367292609506960211968

noncomputable def ep731 := nat_lit 4835703278458516698824704

noncomputable def ep732 := nat_lit 60009081213351719392606546835257411397902560869226954374604658163441749943398876482249387516160

noncomputable def ep733 := nat_lit 11827193841476132975761497142559922353317709611095919146093482340187486176929913983037299836846080

noncomputable def ep734 := nat_lit 12077495060944549418095119006071793917208541636023770542952110501076589163022496900883783936

noncomputable def ep735 := nat_lit 157147087233441545329197373423473865994831226542469413447847420344393316326447401982337441177856

noncomputable def ep736 := nat_lit 216831887093729104555627447613598576477491342870091851011713842903437246577048423022350497008844800

noncomputable def ep737 := BSN.sin_dyadic_bound_f 242799120122 274877906944 3 2 134217728 64092706 ep732 ep733 ep734 ep735 ep736 ep734 103728297 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 242799120122) (BSN.sinEvenQ 274877906944) 0 2 ep732 ep733 ep734 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 242799120122) (BSN.sinOddQ 274877906944) 0 2 ep735 ep736 ep734 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz382 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1663561099) (@Nat.cast Real Real.instNatCast 33554432))

noncomputable def ep738 := @Enclosure.Real.IsNear.cos_image qz113 qz382 Bool.false 1663561099 33554432 117 134217728 Bool.false 103728297 134217728 1 32015088 (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 11163969555071242681 225179981368524800 86468755536609281 100047150000000000000000 1663561099 33554432 117 134217728 (ep729 rfl) rfl) (Enclosure.sfrac_false_div 1663561099 33554432) (BSN.cos_reduce3 qz382 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep730) (@Nat.cast Real Real.instNatCast ep731)) 226375608064910080 72057594037927936 Bool.false 103728297 134217728 7 1000000000000000 64030176 32015088 (BSN.sin_reduce_arg_pos_rat_q3 1663561099 33554432 226375608064910080 72057594037927936 7 ep730 ep731 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 103728297 134217728 ep730 ep731 242799120122 274877906944 64092706 64030176 (ep737 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep739 := nat_lit 33343746227444708351189457183590149351686848723630985217243899917690339563738496933205608079616

noncomputable def ep740 := nat_lit 1314132649052903663973499682506658039257523290121768794010386926687498464103323775893033315205120

noncomputable def ep741 := nat_lit 100007083692212235954732181312758304467226129087620908110645795532068865512889445805815056670976

noncomputable def ep742 := nat_lit 59135969207380664878807485712799611766588548055479595730467411700937430884649569915186499184230400

noncomputable def ep743 := BSN.cos_dyadic_bound_f 242799120122 274877906944 3 2 134217728 64092706 ep739 ep740 ep734 ep741 ep742 ep734 85175341 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 242799120122) (BSN.cosEvenQ 274877906944) 0 2 ep739 ep740 ep734 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 242799120122) (BSN.cosOddQ 274877906944) 0 2 ep741 ep742 ep734 rfl rfl rfl rfl) rfl rfl

noncomputable def ep744 := @Enclosure.Real.IsNear.sin_image qz113 qz382 Bool.false 1663561099 33554432 117 134217728 Bool.true 85175341 134217728 1 32015088 (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 11163969555071242681 225179981368524800 86468755536609281 100047150000000000000000 1663561099 33554432 117 134217728 (ep729 rfl) rfl) (Enclosure.sfrac_false_div 1663561099 33554432) (BSN.sin_reduce3 qz382 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep730) (@Nat.cast Real Real.instNatCast ep731)) 226375608064910080 72057594037927936 Bool.false 85175341 134217728 7 1000000000000000 64030176 32015088 (BSN.sin_reduce_arg_pos_rat_q3 1663561099 33554432 226375608064910080 72057594037927936 7 ep730 ep731 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 85175341 134217728 ep730 ep731 242799120122 274877906944 64092706 64030176 (ep743 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep745 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz379 qz108) (@HMul.hMul Real Real Real qz0 qz379 qz109) Bool.false 26313483198069 18014398509481984 269071055631713 36045784596758409510912 Bool.false 21607024978857 18014398509481984 231947648194205 36045784596758409510912 (@Enclosure.Real.IsNear.mulLit_ff qz379 qz108 253677 134217728 1 134217728 103728297 134217728 242498939 268562023317504 26313483198069 18014398509481984 269071055631713 36045784596758409510912 (@Enclosure.Real.IsNear.recentre' qz379 Bool.false 253677 134217728 1 134217728 253677 134217728 1 134217728 (ep725 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz108 Bool.false 103728297 134217728 3879983024 4296992373080064 103728297 134217728 242498939 268562023317504 (ep738 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz379 qz109 253677 134217728 1 134217728 85175341 134217728 242498939 268562023317504 21607024978857 18014398509481984 231947648194205 36045784596758409510912 (@Enclosure.Real.IsNear.recentre' qz379 Bool.false 253677 134217728 1 134217728 253677 134217728 1 134217728 (ep725 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz114 Bool.true 85175341 134217728 242498939 268562023317504 (@Enclosure.Real.IsNear.recentre' qz114 Bool.true 85175341 134217728 3879983024 4296992373080064 85175341 134217728 242498939 268562023317504 (ep744 rfl rfl) rfl)) rfl)

noncomputable def ep746 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz209 21025849163 720000000 0 1 21607024978857 18014398509481984 231947648194205 36045784596758409510912 151435349355540182048897

noncomputable def ep747 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 22956367 4800000 0 1 Bool.false 21025849163 720000000 0 1 ep721

noncomputable def ep748 := @Enclosure.Complex.IsNear.im_isNear qz196 Bool.false 26313483198069 18014398509481984 269071055631713 36045784596758409510912 Bool.false 21607024978857 18014398509481984 231947648194205 36045784596758409510912

noncomputable def ep749 := nat_lit 4943421887555439018639360000

noncomputable def ep750 := nat_lit 5657447429841579217306219

noncomputable def ep751 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz209) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz208) 165339598397602844173 28823037615171174400000 152133581049515921521 ep749 61473703186192627429583 ep667 ep750

noncomputable def ep752 := nat_lit 2010138332474068293796291843833457750835200000

noncomputable def ep753 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz209 22956367 4800000 0 1 21607024978857 18014398509481984 231947648194205 36045784596758409510912 165339598397602844173

noncomputable def ep754 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz208 21025849163 720000000 0 1 26313483198069 18014398509481984 269071055631713 36045784596758409510912 61473703186192627429583

noncomputable abbrev qz220 := (@ep724 36045784596758409510912 (BSN.cpow_neg_s_sub_mk qz260 27670 1000 6 3 279936 qz277 rfl EMRow04.d14) ep745)

noncomputable def ep755 := ep671 (@ep673 ep665 ep674 121232250488379899282747 ep664 1160686069993559346140213 ep665 (@ep675 28823037615171174400000 882413414594145780953 ep672 ep722 (ep723 qz220) rfl) (@ep746 ep664 975379252928788732140083 ep665 ep747 (ep748 qz220) rfl) rfl rfl) (@ep751 ep670 ep752 69740683106072769638233 ep667 ep668 ep670 (@ep753 28823037615171174400000 152133581049515921521 ep749 ep722 (ep748 qz220) rfl) (@ep754 ep667 ep750 ep670 ep747 (ep723 qz220) rfl) rfl rfl)

noncomputable def ep756 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) 69740683106072769638233 ep667 ep668 ep670 69740683106072769638233 ep667 ep668

noncomputable def ep757 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196) Bool.true 121232250488379899282747 ep664 1160686069993559346140213 ep665 Bool.false 69740683106072769638233 ep667 ep668

noncomputable def ep758 := @ep634 3920283332807 8796093022208 172011499 61572651155456 (@ep635 1 458752 (ep636 (@ep637 131072 1 131072 (ep638 (@ep639 31115156 7778789 10000 0 1 (ep643 rfl) (ep646 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep647 45 134217728 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)) (@ep648 45 134217728 7506709 134217728 45 134217728 (@ep653 3753332 3753377 67108864 (@ep659 ep660 ep661 ep662 ep663 ep649 ep650 ep651 ep652 (@ep666 ep665 ep654 ep655 ep656 ep657 (@ep669 ep670 ep755) (@ep669 ep670 ep755) rfl) (@ep756 ep670 ep658 ep660 ep661 ep662 (@ep757 ep670 ep755) (@ep757 ep670 ep755) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow04.d15 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 6))) (@HMul.hMul Real Real Real qz0 qz193 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)))) Bool.false 4298712666311 8796093022208 34317045571 554153860399104 := ep632 (ep633 ep758) rfl rfl

theorem EMRow04.d16 : @Eq Nat (Nat.pow 7 (Nat.succ (Nat.mul 2 3))) 823543 := @Eq.refl Nat 823543

noncomputable abbrev qz417 := (@HAdd.hAdd Complex Complex Complex qz419 qz426 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz383 := qz417

noncomputable abbrev qz221 := (@HDiv.hDiv Real Real Real qz253 (@Norm.norm Complex Complex.instNorm qz383) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz334) qz312))

noncomputable abbrev qz384 := (@HPow.hPow Complex Complex Complex qz407 (@Nat.cast Complex Complex.instNatCast 7) (@HSub.hSub Complex Complex Complex qz397 qz415 qz409))

noncomputable abbrev qz222 := qz384

noncomputable def ep759 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz124 1 7))) (@HMul.hMul Real Real Real qz0 qz221 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) 494583 33554432 243641 3623878656 3933520672447 8796093022208 136243095

noncomputable def ep760 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz124 1 7)) 123 8192 1 221184 4021 4096 137 32768 494583 33554432

noncomputable def ep761 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz124 1 7)) (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz124 1 7)) (Complex.re (zetaApproximant qz124 1 7))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz124 1 7)) (Complex.im (zetaApproximant qz124 1 7))))) Bool.false 4021 4096 137 32768

noncomputable def ep762 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz124 1 7)) (Complex.re (zetaApproximant qz124 1 7))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz124 1 7)) (Complex.im (zetaApproximant qz124 1 7))))) Bool.false 128672 131072 548 131072

noncomputable def ep763 := nat_lit 25245420053112320473911627876881173241

noncomputable def ep764 := nat_lit 26195566153743082965362457496780800000

noncomputable def ep765 := nat_lit 54914228561908085892172770198148488813828244465168261

noncomputable def ep766 := nat_lit 6702478707292527574684347859914642761560067407872000000

noncomputable def ep767 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz124 1 7)) (Complex.re (zetaApproximant qz124 1 7))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz124 1 7)) (Complex.im (zetaApproximant qz124 1 7)))) ep763 ep764 ep765 ep766 64062 64610

noncomputable def ep768 := nat_lit 1975518218540486591405797776505249260931645801

noncomputable def ep769 := nat_lit 2059383924314953736784638511112953790464000000

noncomputable def ep770 := nat_lit 855923491205445321248256652713817234438053097612617

noncomputable def ep771 := nat_lit 111707978454875459578072464331910712692667790131200000

noncomputable def ep772 := nat_lit 146708209684748024587479502502101044920541289

noncomputable def ep773 := nat_lit 32950142789039259788554216177807260647424000000

noncomputable def ep774 := nat_lit 3558819089581366617277371035319454747545058608411241

noncomputable def ep775 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz124 1 7)) (Complex.re (zetaApproximant qz124 1 7))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz124 1 7)) (Complex.im (zetaApproximant qz124 1 7))) ep768 ep769 ep770 ep771 ep772 ep773 ep774

noncomputable def ep776 := nat_lit 65395735911847296280589246010480102826984511973901914774967130176125191627012277534720000000

noncomputable def ep777 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz124 1 7)) (Complex.re (zetaApproximant qz124 1 7)) 44446802118268155461651 45380435479564910592000 ep344 ep345 44446802118268155461651 45380435479564910592000 ep344 ep345 ep768

noncomputable def ep778 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz124 1 7)) (Complex.im (zetaApproximant qz124 1 7)) 12112316445864020794733 181521741918259642368000 ep458 ep459 12112316445864020794733 181521741918259642368000 ep458 ep459 ep772

noncomputable def ep779 := @ep759 61572651155456 136337449999419834368 4063172638399 8796093022208 115449359597 1662461581197312 (@ep760 243641 3623878656 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz197) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow04.d11 EMRow04.d12 rfl) (ep613 rfl)) (ep761 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz124 1 7)) (@ep762 4021 4096 137 32768 (@ep767 65536 (@ep775 ep766 ep776 ep763 ep764 ep765 ep766 (@ep777 ep769 ep770 ep771 ep594 ep594 rfl) (@ep778 ep773 ep774 ep766 ep602 ep602 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz223 := (@Norm.norm Complex Complex.instNorm qz383)

noncomputable def ep780 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz221 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz223 qz374) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) Bool.false 3933520672447 8796093022208 136243095 61572651155456 (BSN.zrb_shape_eq qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) qz137 3)

noncomputable def ep781 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz223 qz374) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) 597511 65536 1 458752 6583177 134217728 31 134217728

noncomputable def ep782 := @Enclosure.Real.IsNear.mulLit_ff qz223 qz374 4182577 131072 1 131072 2 7 0 1 597511 65536

noncomputable abbrev qz385 := (Complex.re qz417)

noncomputable abbrev qz386 := (Complex.im qz417)

noncomputable abbrev qz224 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz249 qz385 qz385) (@HMul.hMul Real Real Real qz249 qz386 qz386))

noncomputable abbrev qz225 := qz383

noncomputable def ep783 := @Enclosure.Real.IsNear.of_eq qz223 (Real.sqrt qz224) Bool.false 4182577 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz225)

noncomputable def ep784 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz224) Bool.false 4182577 131072 1 131072 4182577

noncomputable def ep785 := @Enclosure.Real.IsNear.sqrt_image qz224 254570381 250000 0 1 2091288 2091289 65536

noncomputable abbrev qz226 := (@HMul.hMul Real Real Real qz249 qz385 qz385)

noncomputable abbrev qz227 := (@HMul.hMul Real Real Real qz249 qz386 qz386)

noncomputable def ep786 := @Enclosure.Real.IsNear.addLit_ff qz226 qz227 49 4 0 1 251507881 250000 0 1

noncomputable abbrev qz228 := qz385

noncomputable def ep787 := @Enclosure.Real.IsNear.mulLit_ff qz228 qz228 7 2 0 1 7 2 0 1 49 4

noncomputable def ep788 := @Enclosure.Complex.IsNear.of_eq qz225 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz137) Bool.false 7 2 0 1 Bool.false 31718 1000 0 1 (BSN.s_add_nat_mk qz137 Bool.false 31718 1000 3 qz138)

noncomputable abbrev qz229 := (ep788 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz333 Bool.false 7 2 0 1 Bool.false 31718 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz355))

noncomputable def ep789 := @ep787 0 1 (@Enclosure.Complex.IsNear.re_isNear qz225 Bool.false 7 2 0 1 Bool.false 31718 1000 0 1 qz229)

noncomputable def ep790 := ep789 (@Enclosure.Complex.IsNear.re_isNear qz225 Bool.false 7 2 0 1 Bool.false 31718 1000 0 1 qz229)

noncomputable abbrev qz230 := qz386

noncomputable def ep791 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 31718 1000 0 1 31718 1000 0 1 251507881 250000

noncomputable def ep792 := @ep791 0 1 (@Enclosure.Complex.IsNear.im_isNear qz225 Bool.false 7 2 0 1 Bool.false 31718 1000 0 1 qz229)

noncomputable def ep793 := ep792 (@Enclosure.Complex.IsNear.im_isNear qz225 Bool.false 7 2 0 1 Bool.false 31718 1000 0 1 qz229)

noncomputable def ep794 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))))) Bool.false 6583177 134217728

noncomputable def ep795 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))))) Bool.false 13166354 268435456

noncomputable def ep796 := nat_lit 6323766408184878939580842600925136820531341186954497

noncomputable def ep797 := nat_lit 2628600284633256486943563766667673600000000000000000000

noncomputable def ep798 := nat_lit 204663001797405671403694533011438643147552153964749098679283727

noncomputable def ep799 := nat_lit 9247157771315487701135940862209862415304121280102400000000000000000000

noncomputable def ep800 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)))) ep796 ep797 ep798 ep799

noncomputable def ep801 := nat_lit 268858460741849228024331117743348890664433516082801

noncomputable def ep802 := nat_lit 164287517789578530433972735416729600000000000000000000

noncomputable def ep803 := nat_lit 1100160336464635464346345885477480259809286314137982530163627

noncomputable def ep804 := nat_lit 72243420088402247665124537986014550119563447500800000000000000000000

noncomputable def ep805 := nat_lit 224670115146143476799060524114617174433378325514409

noncomputable def ep806 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) ep801 ep802 ep803 ep804 ep805

noncomputable def ep807 := nat_lit 292066698292584054104840418518630400000000000000000000

noncomputable def ep808 := nat_lit 2364536249256753035828231839641524810813463176114345734012573

noncomputable def ep809 := nat_lit 342487324863536581523553365267031941307560047411200000000000000000000

noncomputable def ep810 := nat_lit 115435098475756936145740948812492454773370464306282350937735344826166331549151972556800000000000000000000

noncomputable def ep811 := nat_lit 16396903998677592673061401

noncomputable def ep812 := nat_lit 405323966463344640000000000

noncomputable def ep813 := nat_lit 1131230903265489237493401743

noncomputable def ep814 := nat_lit 6010133945612287585812480000000000

noncomputable def ep815 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) ep811 ep812 ep813 ep814 ep811 ep812 ep813

noncomputable def ep816 := nat_lit 14988999804728248671292403

noncomputable def ep817 := nat_lit 540431955284459520000000000

noncomputable def ep818 := nat_lit 3989530122676493589977281691

noncomputable def ep819 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222) Bool.true ep811 ep812 ep813 ep814 Bool.false ep816 ep817 ep818

noncomputable def ep820 := nat_lit 32054047709932200457666560000000000

noncomputable def ep821 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222 Bool.true ep811 ep812 ep813 ep814 Bool.false ep816 ep817 ep818 ep820

noncomputable def ep822 := nat_lit 6105532897129942944317440000000

noncomputable def ep823 := nat_lit 35282880243879526729917677

noncomputable def ep824 := nat_lit 810647932926689280000000000

noncomputable def ep825 := nat_lit 8366503406468640691058386069

noncomputable abbrev qz231 := (Complex.re qz384)

noncomputable abbrev qz232 := (Complex.im qz384)

noncomputable def ep826 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) 2212508663577192341151 720575940379279360000000 86773818368923582081121 ep822 ep823 ep824 ep825

noncomputable def ep827 := nat_lit 48081071564898300686499840000000000

noncomputable def ep828 := nat_lit 23630429036311744703856419797342714823966720000000

noncomputable def ep829 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231 754211143 120000000 0 1 8800620426171 18014398509481984 2416100852738787 1068468256997740015255552 2212508663577192341151

noncomputable def ep830 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) 754211143 120000000 0 1 0 1 0 1 754211143

noncomputable def ep831 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 2262633429 500000 0 1 754211143 120000000 0

noncomputable abbrev qz387 := (@HAdd.hAdd Complex Complex Complex qz399 qz414 qz410)

noncomputable abbrev qz233 := qz387

noncomputable def ep832 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2)) qz233) Bool.true 2262633429 500000 0 1 Bool.true 3965866172279 125000000 0 1

noncomputable abbrev qz234 := (Complex.re qz387)

noncomputable abbrev qz235 := (Complex.im qz387)

noncomputable def ep833 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz234) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 251320381 100000 0 1 251507881 125000 0 1

noncomputable def ep834 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz234 251320381 250000 0 1 5 2 0 1 251320381 100000

noncomputable abbrev qz388 := (@HAdd.hAdd Complex Complex Complex qz399 qz414 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz236 := qz388

noncomputable def ep835 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) qz236) Bool.true 251320381 250000 0 1 Bool.false 15859 250 0 1

noncomputable abbrev qz237 := (Complex.re qz388)

noncomputable abbrev qz238 := (Complex.im qz388)

noncomputable def ep836 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 3 4 0 1 251507881 250000 0 1

noncomputable def ep837 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz237 1 2 0 1 3 2 0 1 3 4

noncomputable def ep838 := @ep837 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep560)

noncomputable def ep839 := @Enclosure.Complex.IsNear.of_eq qz236 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz137) Bool.false 3 2 0 1 Bool.false 31718 1000 0 1 (BSN.s_add_nat_mk qz137 Bool.false 31718 1000 1 qz138)

noncomputable abbrev qz239 := (ep839 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz333 Bool.false 3 2 0 1 Bool.false 31718 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz355))

noncomputable def ep840 := ep838 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 3 2 0 1 Bool.false 31718 1000 0 1 qz239)

noncomputable def ep841 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 31718 1000 0 1 31718 1000 0 1 251507881 250000

noncomputable def ep842 := @ep841 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep560)

noncomputable def ep843 := ep842 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 3 2 0 1 Bool.false 31718 1000 0 1 qz239)

noncomputable def ep844 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) qz236 Bool.true 251320381 250000 0 1 Bool.false 15859 250 0 1 (@ep836 1005281524 251320381 250000 0 1 (ep840 rfl) (ep843 rfl) rfl rfl)

noncomputable def ep845 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz237) 15859 1000 0 1 47577 1000 0 1

noncomputable def ep846 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 31718 1000 0 1 15859 1000

noncomputable def ep847 := @ep846 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep560)

noncomputable def ep848 := ep847 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 3 2 0 1 Bool.false 31718 1000 0 1 qz239)

noncomputable def ep849 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1))) qz237 31718 1000 0 1 3 2 0 1 47577 1000

noncomputable def ep850 := @ep849 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep560)

noncomputable def ep851 := ep850 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 3 2 0 1 Bool.false 31718 1000 0 1 qz239)

noncomputable abbrev qz240 := (ep835 (BSN.ascPochhammer_succ_eval_c 1 2 qz334 rfl) (ep844 (@ep845 63436000 15859 250 0 1 (ep848 rfl) (ep851 rfl) rfl rfl)))

noncomputable def ep852 := @ep834 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 251320381 250000 0 1 Bool.false 15859 250 0 1 qz240)

noncomputable def ep853 := @Enclosure.Complex.IsNear.of_eq qz233 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz137) Bool.false 5 2 0 1 Bool.false 31718 1000 0 1 (BSN.s_add_nat_mk qz137 Bool.false 31718 1000 2 qz138)

noncomputable abbrev qz241 := (ep853 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz333 Bool.false 5 2 0 1 Bool.false 31718 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz355))

noncomputable def ep854 := ep852 (@Enclosure.Complex.IsNear.re_isNear qz233 Bool.false 5 2 0 1 Bool.false 31718 1000 0 1 qz241)

noncomputable def ep855 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 15859 250 0 1 31718 1000 0 1 251507881 125000

noncomputable def ep856 := @ep855 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 251320381 250000 0 1 Bool.false 15859 250 0 1 qz240)

noncomputable def ep857 := ep856 (@Enclosure.Complex.IsNear.im_isNear qz233 Bool.false 5 2 0 1 Bool.false 31718 1000 0 1 qz241)

noncomputable def ep858 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2)) qz233 Bool.true 2262633429 500000 0 1 Bool.true 3965866172279 125000000 0 1 (@ep833 56565835725000 2262633429 500000 0 1 (ep854 rfl) (ep857 rfl) rfl rfl)

noncomputable def ep859 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz234) 3985689922279 125000000 0 1 15859 100 0 1

noncomputable def ep860 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 251320381 250000 0 1 31718 1000 0 1 3985689922279 125000000

noncomputable def ep861 := @ep860 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 251320381 250000 0 1 Bool.false 15859 250 0 1 qz240)

noncomputable def ep862 := ep861 (@Enclosure.Complex.IsNear.im_isNear qz233 Bool.false 5 2 0 1 Bool.false 31718 1000 0 1 qz241)

noncomputable def ep863 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2))) qz234 15859 250 0 1 5 2 0 1 15859 100

noncomputable def ep864 := @ep863 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 251320381 250000 0 1 Bool.false 15859 250 0 1 qz240)

noncomputable def ep865 := ep864 (@Enclosure.Complex.IsNear.re_isNear qz233 Bool.false 5 2 0 1 Bool.false 31718 1000 0 1 qz241)

noncomputable abbrev qz242 := (ep832 (BSN.ascPochhammer_succ_eval_c 2 3 qz334 rfl) (ep858 (@ep859 396586617227900 3965866172279 125000000 0 1 (ep862 rfl) (ep865 rfl) rfl rfl)))

noncomputable def ep866 := @ep831 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep678) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2262633429 500000 0 1 Bool.true 3965866172279 125000000 0 1 qz242)

noncomputable def ep867 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3965866172279 125000000 0 1 0 1 0

noncomputable def ep868 := @ep867 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep678) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2262633429 500000 0 1 Bool.true 3965866172279 125000000 0 1 qz242)

noncomputable def ep869 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) 3965866172279 90000000000 0 1 0 1 0 1 3965866172279

noncomputable def ep870 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3965866172279 125000000 0 1 3965866172279 90000000000 0

noncomputable def ep871 := @ep870 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep678) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2262633429 500000 0 1 Bool.true 3965866172279 125000000 0 1 qz242)

noncomputable def ep872 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 2262633429 500000 0 1 0 1 0

noncomputable def ep873 := @ep872 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep678) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2262633429 500000 0 1 Bool.true 3965866172279 125000000 0 1 qz242)

noncomputable def ep874 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 754211143 120000000 0 1 Bool.false 3965866172279 90000000000 0 1 (@ep830 754211143 120000000 0 1 (ep866 rfl) (ep868 rfl) rfl rfl) (@ep869 3965866172279 90000000000 0 1 (ep871 rfl) (ep873 rfl) rfl rfl)

noncomputable def ep875 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 754211143 120000000 0 1 Bool.false 3965866172279 90000000000 0 1 ep874

noncomputable def ep876 := @Enclosure.Complex.IsNear.re_isNear qz222 Bool.false 8800620426171 18014398509481984 2416100852738787 1068468256997740015255552 Bool.false 8896639147963 9007199254740992 2109628273629011 534234128498870007627776

noncomputable abbrev qz389 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 823543)))

noncomputable def ep877 := @Enclosure.Complex.IsNear.of_eq qz222 (Complex.mk (@HMul.hMul Real Real Real qz0 qz389 qz183) (@HMul.hMul Real Real Real qz0 qz389 qz184)) Bool.false 8800620426171 18014398509481984 2416100852738787 1068468256997740015255552 Bool.false 8896639147963 9007199254740992 2109628273629011

noncomputable abbrev qz390 := (Real.sqrt (@Nat.cast Real Real.instNatCast 823543))

noncomputable abbrev qz391 := (@Nat.cast Real Real.instNatCast 823543)

noncomputable def ep878 := @Enclosure.Real.IsNear.inv_image qz390 243603216659 268435456 1 268435456 147899 147900 134217728 (@Enclosure.Real.IsNear.of_eq qz390 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz391 qz304)) Bool.false 243603216659 268435456 1 268435456 (BSN.sqrt_natCast_div_one 823543) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz391 qz304)) Bool.false 243603216659 268435456 1 268435456 243603216659 268435456 1 268435456 (BSN.sqrt_enclosure 823543 1 121801608329 121801608330 134217728 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep879 := nat_lit 14827975750000000000000000

noncomputable def ep880 := nat_lit 9409844065408522077077504

noncomputable def ep881 := BSN.log_dyadic_bound 3 11 8 7 769762406419069088025 134217728 59311903 19984785452821035495 646346515815 75110359 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 3) (BSN.artanhQ 11) 0 7 19984785452821035495 769762406419069088025 646346515815 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep882 := @Enclosure.Real.IsNear.mulLit_ff qz137 qz185 31718 1000 0 1 4381800100863223 2251799813685248 500000059311903 29655951500000000000000 69490967799589853557 1125899906842624000 7929500940627469677 ep879 qz172 (BSN.isNear_log_sfrac 7 1 4381800100863223 2251799813685248 500000059311903 29655951500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz364) Bool.false ep880 ep731 1000000118623806 59311903000000000000000 4381800100863223 2251799813685248 500000059311903 29655951500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 75110359 134217728 24973259072661432 36028797018963968 59311903 1000000000000000 rfl rfl rfl rfl (ep881 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep883 := nat_lit 17769128959352151260266496

noncomputable def ep884 := nat_lit 38685626227668133590597632

noncomputable def ep885 := nat_lit 1123085597076883208532090602502486766315659903028169362374325291184907269593247275863120819238465

noncomputable def ep886 := nat_lit 3027761623417890041794943268495340122449333660440555301399931479087996461294057979657548758232596480

noncomputable def ep887 := nat_lit 16530679650990396029940119151377080790996346814798441178010081921255865985556431476200552001

noncomputable def ep888 := nat_lit 2941387895053354418847617389218363110791161942417029132551801841542122720389766250181021630445121

noncomputable def ep889 := nat_lit 55508963095994650766240626589081235578237783774743513858998743783279935123724396293721727234264268800

noncomputable def ep890 := BSN.sin_dyadic_bound_f 252514510057 549755813888 3 2 268435456 118739650 ep885 ep886 ep887 ep888 ep889 ep887 119008116 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 252514510057) (BSN.sinEvenQ 549755813888) 0 2 ep885 ep886 ep887 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 252514510057) (BSN.sinOddQ 549755813888) 0 2 ep888 ep889 ep887 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz392 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16567937803) (@Nat.cast Real Real.instNatCast 268435456))

noncomputable def ep891 := @Enclosure.Real.IsNear.cos_image qz186 qz392 Bool.false 16567937803 268435456 9 16777216 Bool.false 119008116 268435456 1 59311903 (@Enclosure.Real.IsNear.recentre' qz186 Bool.false 69490967799589853557 1125899906842624000 7929500940627469677 ep879 16567937803 268435456 9 16777216 (ep882 rfl) rfl) (Enclosure.sfrac_false_div 16567937803 268435456) (BSN.cos_reduce3 qz392 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep883) (@Nat.cast Real Real.instNatCast ep884)) 226375608064910080 72057594037927936 Bool.false 119008116 268435456 9 1000000000000000 118623806 59311903 (BSN.sin_reduce_arg_pos_rat_q3 16567937803 268435456 226375608064910080 72057594037927936 9 ep883 ep884 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 119008116 268435456 ep883 ep884 252514510057 549755813888 118739650 118623806 (ep890 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep892 := nat_lit 623943789789224444916063641443226593322384833392011778404037610694691263492242067226834322044481

noncomputable def ep893 := nat_lit 336417958157543337977215918721704458049925962271172811266659053231999606810450886628616528692510720

noncomputable def ep894 := nat_lit 1871798308008371353956131044091377025805572507482405738329756811920231278744755088817550565029441

noncomputable def ep895 := nat_lit 15138808117089450208974716342476700612246668302202776506999657395439982306470289898287743791162982400

noncomputable def ep896 := BSN.cos_dyadic_bound_f 252514510057 549755813888 3 2 268435456 118739650 ep892 ep893 ep887 ep894 ep895 ep887 240613096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 252514510057) (BSN.cosEvenQ 549755813888) 0 2 ep892 ep893 ep887 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 252514510057) (BSN.cosOddQ 549755813888) 0 2 ep894 ep895 ep887 rfl rfl rfl rfl) rfl rfl

noncomputable def ep897 := @Enclosure.Real.IsNear.sin_image qz186 qz392 Bool.false 16567937803 268435456 9 16777216 Bool.true 240613096 268435456 1 59311903 (@Enclosure.Real.IsNear.recentre' qz186 Bool.false 69490967799589853557 1125899906842624000 7929500940627469677 ep879 16567937803 268435456 9 16777216 (ep882 rfl) rfl) (Enclosure.sfrac_false_div 16567937803 268435456) (BSN.sin_reduce3 qz392 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep883) (@Nat.cast Real Real.instNatCast ep884)) 226375608064910080 72057594037927936 Bool.false 240613096 268435456 9 1000000000000000 118623806 59311903 (BSN.sin_reduce_arg_pos_rat_q3 16567937803 268435456 226375608064910080 72057594037927936 9 ep883 ep884 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 240613096 268435456 ep883 ep884 252514510057 549755813888 118739650 118623806 (ep896 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep898 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz389 qz183) (@HMul.hMul Real Real Real qz0 qz389 qz184) Bool.false 8800620426171 18014398509481984 2416100852738787 1068468256997740015255552 Bool.false 8896639147963 9007199254740992 2109628273629011 534234128498870007627776 (@Enclosure.Real.IsNear.mulLit_ff qz389 qz183 295799 268435456 1 268435456 29752029 67108864 550584343 995088608002048 8800620426171 18014398509481984 2416100852738787 1068468256997740015255552 (@Enclosure.Real.IsNear.recentre' qz389 Bool.false 295799 268435456 1 268435456 295799 268435456 1 268435456 (ep878 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 119008116 268435456 550584343 995088608002048 29752029 67108864 550584343 995088608002048 (ep891 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz389 qz184 295799 268435456 1 268435456 30076637 33554432 550584343 995088608002048 8896639147963 9007199254740992 2109628273629011 534234128498870007627776 (@Enclosure.Real.IsNear.recentre' qz389 Bool.false 295799 268435456 1 268435456 295799 268435456 1 268435456 (ep878 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz187 Bool.true 30076637 33554432 550584343 995088608002048 (@Enclosure.Real.IsNear.recentre' qz187 Bool.true 240613096 268435456 550584343 995088608002048 30076637 33554432 550584343 995088608002048 (ep897 rfl rfl) rfl)) rfl)

noncomputable def ep899 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 3965866172279 90000000000 0 1 8896639147963 9007199254740992 2109628273629011 534234128498870007627776 ep823

noncomputable def ep900 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 754211143 120000000 0 1 Bool.false 3965866172279 90000000000 0 1 ep874

noncomputable def ep901 := @Enclosure.Complex.IsNear.im_isNear qz222 Bool.false 8800620426171 18014398509481984 2416100852738787 1068468256997740015255552 Bool.false 8896639147963 9007199254740992 2109628273629011 534234128498870007627776

noncomputable def ep902 := nat_lit 9158299345694914416476160000000

noncomputable def ep903 := nat_lit 3878009204802129498479301

noncomputable def ep904 := nat_lit 180143985094819840000000000

noncomputable def ep905 := nat_lit 3193977546897067017842495191

noncomputable def ep906 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231) 6709944380643720351709 1080863910568919040000000 227300735936979020609939 ep902 ep903 ep904 ep905

noncomputable def ep907 := nat_lit 5400356314818446241923864718276226491351040000000

noncomputable def ep908 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 754211143 120000000 0 1 8896639147963 9007199254740992 2109628273629011 534234128498870007627776 6709944380643720351709

noncomputable def ep909 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231 3965866172279 90000000000 0 1 8800620426171 18014398509481984 2416100852738787 1068468256997740015255552 ep903

noncomputable abbrev qz243 := (@ep877 534234128498870007627776 (BSN.cpow_neg_s_sub_mk qz333 31718 1000 7 3 823543 qz341 rfl EMRow04.d16) ep898)

noncomputable def ep910 := ep821 (@ep826 ep827 ep828 ep811 ep812 ep813 ep814 (@ep829 720575940379279360000000 86773818368923582081121 ep822 ep875 (ep876 qz243) rfl) (@ep899 ep824 ep825 ep827 ep900 (ep901 qz243) rfl) rfl rfl) (@ep906 ep820 ep907 ep816 ep817 ep818 ep820 (@ep908 1080863910568919040000000 227300735936979020609939 ep902 ep875 (ep901 qz243) rfl) (@ep909 ep904 ep905 ep820 ep900 (ep876 qz243) rfl) rfl rfl)

noncomputable def ep911 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) ep816 ep817 ep818 ep820 ep816 ep817 ep818

noncomputable def ep912 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222) Bool.true ep811 ep812 ep813 ep814 Bool.false ep816 ep817 ep818

noncomputable def ep913 := @ep781 3933520672447 8796093022208 136243095 61572651155456 (@ep782 1 458752 (ep783 (@ep784 131072 1 131072 (ep785 (@ep786 1018281524 254570381 250000 0 1 (ep790 rfl) (ep793 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep794 31 134217728 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (@ep795 62 268435456 6583177 134217728 31 134217728 (@ep800 6583146 6583208 134217728 (@ep806 ep807 ep808 ep809 ep810 ep796 ep797 ep798 ep799 (@ep815 ep814 ep801 ep802 ep803 ep804 (@ep819 ep820 ep910) (@ep819 ep820 ep910) rfl) (@ep911 ep820 ep805 ep807 ep808 ep809 (@ep912 ep820 ep910) (@ep912 ep820 ep910) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow04.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz124 1 7))) (@HMul.hMul Real Real Real qz0 qz221 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)))) Bool.false 4063172638399 8796093022208 115449359597 1662461581197312 := ep779 (ep780 ep913) rfl rfl

noncomputable def EMRow04.d18 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz393 := (EMRow04.d3 qz401 qz413 (@Enclosure.dec_le_dec qz401 qz413 27670 1000 31718 1000 (@Eq.refl Real qz401) (@Eq.refl Real qz413) rfl rfl rfl) 6 7 1 1)

noncomputable abbrev qz244 := qz393

noncomputable def ep914 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz244 (@Enclosure.dec_nonneg qz37 27670 1000 qz38) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 6 rfl)

noncomputable abbrev qz245 := (Zeta.Certificates.ZIntervalEM.fstVal qz393)

noncomputable def ep915 := @Enclosure.Real.IsNear.pos_val qz245 ep38 ep39

noncomputable def ep916 := @Enclosure.Real.IsNear.of_eq qz245 (hardyZApproximantEM 1 6 qz37) Bool.false

noncomputable abbrev qz246 := (Zeta.Certificates.ZIntervalEM.sndVal qz393)

noncomputable def ep917 := BSN.mul_neg_of_pos_neg_r qz245 qz246 (@ep915 ep40 ep41 (@ep916 ep38 ep39 ep40 ep41 (@Eq.refl Real (hardyZApproximantEM 1 6 qz37)) EMRow04.d8) rfl rfl rfl)

noncomputable def ep918 := @Enclosure.Real.IsNear.neg_val qz246 ep328 ep329

noncomputable def ep919 := @Enclosure.Real.IsNear.of_eq qz246 (hardyZApproximantEM 1 7 qz137) Bool.true

noncomputable def ep920 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz245) (BSN.hardyZErrorBoundStrong 1 6 qz37)

noncomputable def ep921 := @Enclosure.norm_gt_of_isNear qz245 (BSN.hardyZErrorBoundStrong 1 6 qz37) Bool.false

noncomputable def ep922 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 6 qz37) (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 6))) (@HMul.hMul Real Real Real qz0 qz193 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)))) Bool.false 4298712666311 8796093022208 34317045571 554153860399104 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 6))) (@HMul.hMul Real Real Real qz0 qz193 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz196)))))

noncomputable def ep923 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz246) (BSN.hardyZErrorBoundStrong 1 7 qz137)

noncomputable def ep924 := @Enclosure.norm_gt_of_isNear qz246 (BSN.hardyZErrorBoundStrong 1 7 qz137) Bool.true

noncomputable def ep925 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 7 qz137) (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz124 1 7))) (@HMul.hMul Real Real Real qz0 qz221 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)))) Bool.false 4063172638399 8796093022208 115449359597 1662461581197312 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz124 1 7))) (@HMul.hMul Real Real Real qz0 qz221 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz194)) ↑qz195) (@Polynomial.eval Complex Complex.instSemiring qz124 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)))))

noncomputable def ep926 := @List.cons EMRow04.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz244 (ep914 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 7 rfl) (ep917 (@ep918 ep330 ep331 (@ep919 ep328 ep329 ep330 ep331 (@Eq.refl Real (hardyZApproximantEM 1 7 qz137)) EMRow04.d10) rfl rfl rfl)) (ep920 (hardyZErrorBoundEM 1 6 qz37) (BSN.hardyZErrorBoundEM_le_strong 1 6 qz37 rfl) (@ep921 Bool.false ep38 ep39 ep40 ep41 4298712666311 8796093022208 34317045571 554153860399104 (@ep916 ep38 ep39 ep40 ep41 (@Eq.refl Real (hardyZApproximantEM 1 6 qz37)) EMRow04.d8) (ep922 EMRow04.d15) rfl rfl rfl rfl rfl)) (ep923 (hardyZErrorBoundEM 1 7 qz137) (BSN.hardyZErrorBoundEM_le_strong 1 7 qz137 rfl) (@ep924 Bool.false ep328 ep329 ep330 ep331 4063172638399 8796093022208 115449359597 1662461581197312 (@ep919 ep328 ep329 ep330 ep331 (@Eq.refl Real (hardyZApproximantEM 1 7 qz137)) EMRow04.d10) (ep925 EMRow04.d17) rfl rfl rfl rfl rfl)))) (@List.nil EMRow04.d0)

noncomputable abbrev qz394 := (@Enclosure.dec_le_dec qz401 qz413 27670 1000 31718 1000 (@Eq.refl Real qz401) (@Eq.refl Real qz413) rfl rfl rfl)

noncomputable abbrev qz247 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep926 (@List.IsChain.singleton EMRow04.d1 EMRow04.d18 (EMRow04.d2 qz260 qz333 qz394))))

noncomputable abbrev qz395 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep927 := And (@Eq (Option Real) (@Option.map qz395 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz395 qz247)) (@Option.some Real qz37))

noncomputable def ep928 := ep927 (@Eq (Option Real) (@Option.map qz395 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz395 qz247)) (@Option.some Real qz137))

noncomputable def ep929 := @And.intro (@Eq Nat (@List.length qz395 qz247) 1) ep928

noncomputable def ep930 := @And.intro (@Eq (Option Real) (@Option.map qz395 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz395 qz247)) (@Option.some Real qz37))

noncomputable def ep931 := @ep930 (@Eq (Option Real) (@Option.map qz395 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz395 qz247)) (@Option.some Real qz137))

noncomputable abbrev qz248 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep926 (@List.IsChain.singleton EMRow04.d1 EMRow04.d18 (EMRow04.d2 qz260 qz333 qz394)))

theorem EMRow04.d19 : Zeta.Certificates.BatchSpec 1 27670 1000 31718 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz395 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz395 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz395 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz37)) (@Eq (Option Real) (@Option.map qz395 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz395 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz137)))) qz248 (ep929 (@Eq.refl Nat 1) (ep931 (@Eq.refl (Option Real) (@Option.some Real qz37)) (@Eq.refl (Option Real) (@Option.some Real qz137))))

theorem solution : Zeta.Certificates.BatchSpec 1 27670 1000 31718 1000 := EMRow04.d19
#print axioms solution
#check solution
