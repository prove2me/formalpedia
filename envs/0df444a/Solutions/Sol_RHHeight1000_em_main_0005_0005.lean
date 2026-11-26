-- Prove2me | solution 1 for RHHeight1000.em_main_0005_0005
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:45:01.252514+00:00
-- url     : https://prove2.me/submissions/65f686a2-6bab-4347-81f1-86186ba1c8c5

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow05.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow05.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow05.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow05.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow05.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz248 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz248

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz249 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138516661214455 2251799813685248 250000000026673 13336500000000000000 4138516661214455 2251799813685248 250000000026673 13336500000000000000 120446 65536

noncomputable abbrev qz250 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 65536 qz250 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 779317518150410741488063439345657628452599855445271348474342368876423347582876053728679783827237610085654588674605917415063316248867402488514697634436426745

noncomputable def ep10 := nat_lit 13198325246229587668616048586507268161410801335203869857947191811663857046415771104290097871102374067703089877156867761119753226876438075596795543285583799

noncomputable def ep11 := nat_lit 13338205139369261376383149914767634013226508915861991492218067381232119098362059104733250767410551174650894954010182016771344050520336484956804919489535

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 4 3 ep9 131072 53346 ep10 ep11 59189 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 3 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz251 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz251

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138516661214455 2251799813685248 250000000026673 13336500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000106692 53346000000000000000 4138516661214455 2251799813685248 250000000026673 13336500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 59189 131072 24973259072661432 36028797018963968 53346 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 779317518150412560342812906055656980396982394702499187106382620393032652998517540933158707129341055012778793601285942846917973645097155238594697634436426745

noncomputable def ep18 := nat_lit 13198325246229655554962711811363413523213721429909419700721697472804734044169853548961061453892255410264786862895235075217650796661500958924795543285583799

noncomputable def ep19 := nat_lit 13338205139369401582665284895604560799810298653799657073142644093199656832454717421805370366589019475922075211274104314270069372987910244956804919489535

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 4 3 ep17 131072 53346 ep18 ep19 59189 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 3 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138516661214455 2251799813685248 250000000026673 13336500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000106692 53346000000000000000 4138516661214455 2251799813685248 250000000026673 13336500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 59189 131072 24973259072661432 36028797018963968 53346 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz252 := (Real.log (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz3 := qz252

theorem EMRow05.d4 : Enclosure.Real.IsNear qz3 Bool.false 60223 32768 1 32768 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz249) Bool.false 60223 32768 1 32768 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz249) Bool.false 120446 65536 2 65536 60223 32768 1 32768 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 150042 131072 1 53346 150042 131072 1 53346 75021 65536 2 65536 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 5456220599384213465248909714772227496572670538165976141063262914812807742611017753801422503639530882087556452122005170047444298375835020188444492540969863625638808382453421118235702266947370928498132967594635949979551089348001357731941995137847266570621617494261809398531128871567535833923098076891483476912075228072418610430965163137427706923427310178652894498746239459018086669257415154730407592571637957767157504839263249849478535520334507104454135585522664276476675

noncomputable def ep28 := nat_lit 583201912334273870627228188254822588827079241605343036411752047433839590517388190714780374919746279700129906501257101384229175562492847525225536391462542197025353003914524118772974087630067522636400444148635637549655768907025719966434833632093412247469427754039812435067522613541620617101084764807513402584784781490076808276521160080078978009740617112077674385114356333461540984478969922738031393369686631450339262287925718320742111081121726382582016608811398564907105

noncomputable def ep29 := nat_lit 2006268627360805445673839316848610509641534779303135707206598861506426804997221642604762844037348942607248852390277353874343091902420975230792155995982437872051629609224882022549487822374001366578458875613104959699164386313425243185530298109514065278868815165519648262204211929774735225023360668387821809970420335957473972782118680523137645713941929429588852958886338507735711181009301082096313539911189247153419366938656533848809858580689548163599238034961919825

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 10 9 ep27 131072 53346 ep28 ep29 150042 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 9 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 5456220599384260892400251500854699790811159195150212163211869656216336849990273498858157048596616978904240776489460003685239051624059887013466241201881443704542959173524008982544253046253151867013374679201187657749749224297051088632484873343955402287279851789208893474071824987110190207053471018354491495133306616646837230249901879422821128116650397962087630806812522581253210958036113071268120219429850657911869289056672761916619783759890108169949892385522664276476675

noncomputable def ep34 := nat_lit 583201912334279575053067226115417021307550325332234501953544426829928714668898700518418107620762577859683234776628347658361181262145210140271013263714562720079188253110303208819702903278206870150494721073991877864419341163488949363940583288588224434829960190109694548513088121652843287215458036179968684293644459891198769761601084092249455692877745995219003758983943549453190712470220270279351626860119698313725888367584660500821040083453648022042061408811398564907105

noncomputable def ep35 := nat_lit 2006268627360839170887858856494478835319319717359667041823756329478526322484078784125879825811686186445537802910004300367040714583746383402724632880452479311196631191501299191497899488881639138562974769996989848045902383299749709271247360054208480548633525642122514778503225872819822968825602771791453574137145372948950799520945900351638147820910599315255916738483881817718250085827996954508077874524152655659774549924038927632065100609588052048399238034961919825

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 10 9 ep33 131072 53346 ep34 ep35 150042 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 9 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 75021 65536 2 65536 75021 65536 1 32768 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 150042 131072 1 53346 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 150042 131072 53346 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 150042 131072 1 53346 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 150042 131072 53346 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow05.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 32768 := ep37

theorem EMRow05.d6 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow05.d7 : @Eq Nat (Nat.pow 7 1) 7 := @Eq.refl Nat 7

noncomputable def ep38 := nat_lit 4660542172964952805198769737

noncomputable def ep39 := nat_lit 4758483551342025568891699200

noncomputable def ep40 := nat_lit 8299299810301072650972341153944457

noncomputable def ep41 := nat_lit 1880787792370222557599230618238976000

noncomputable abbrev qz418 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz396 := qz418

noncomputable abbrev qz253 := qz396

noncomputable abbrev qz4 := qz253

noncomputable abbrev qz5 := (@instHSub Real Real.instSub)

noncomputable abbrev qz397 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz254 := qz397

noncomputable abbrev qz6 := qz254

noncomputable abbrev qz419 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz420 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz421 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz422 := (Enclosure.sfrac Bool.false 31718 1000)

noncomputable abbrev qz398 := (@HAdd.hAdd Complex Complex Complex qz419 (@HAdd.hAdd Complex Complex Complex qz419 qz420 (@HMul.hMul Complex Complex Complex qz418 Complex.I (@HDiv.hDiv Complex Complex Complex qz421 (↑qz422) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz255 := qz398

noncomputable abbrev qz7 := (Complex.Stirling.logGammaStirling 1 qz255)

noncomputable abbrev qz399 := qz419

noncomputable abbrev qz256 := qz399

noncomputable abbrev qz8 := qz256

noncomputable abbrev qz400 := (@HAdd.hAdd Complex Complex Complex qz419 qz420 (@HMul.hMul Complex Complex Complex qz418 Complex.I (@HDiv.hDiv Complex Complex Complex qz421 (↑qz422) (2 : Complex))))

noncomputable abbrev qz257 := qz400

noncomputable abbrev qz9 := qz257

noncomputable abbrev qz401 := qz422

noncomputable abbrev qz258 := qz401

noncomputable abbrev qz10 := (@HMul.hMul Real Real Real qz248 (@HDiv.hDiv Real Real Real qz251 qz258 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz423 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 31718 1000)))

noncomputable abbrev qz402 := qz423

noncomputable abbrev qz259 := qz402

noncomputable abbrev qz11 := qz259

noncomputable def ep42 := Complex.re (@HMul.hMul Complex Complex Complex qz4 (Complex.exp (@HMul.hMul Complex Complex Complex qz4 Complex.I ↑(@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10))) (zetaApproximant qz11 1 7))

noncomputable def ep43 := @Enclosure.Real.IsNear.of_eq ep42 (@HSub.hSub Real Real Real qz5 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 7))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 7))))

noncomputable def ep44 := nat_lit 5825686800443525404514058221

noncomputable def ep45 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 7))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 7))) ep44

noncomputable def ep46 := nat_lit 5948104439177531961114624000

noncomputable def ep47 := nat_lit 4099677816509337964742101132972379

noncomputable def ep48 := nat_lit 940393896185111278799615309119488000

noncomputable def ep49 := nat_lit 7930805918903375948152832000

noncomputable def ep50 := nat_lit 99944177282396721488138887999699

noncomputable def ep51 := nat_lit 46202319313311561273086972986336476465900280065556480000

noncomputable def ep52 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.re (zetaApproximant qz11 1 7)) 131071 131072 1319167

noncomputable def ep53 := nat_lit 115279271956803320020992000

noncomputable def ep54 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) Bool.true 131071 131072 1319167

noncomputable abbrev qz12 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz260 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1235321) qz12)

noncomputable def ep55 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) qz260 Bool.false 1235321 131072 47

noncomputable def ep56 := nat_lit 109252608000000000000000000

noncomputable def ep57 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) Bool.false 31834003130154812747 3377699720527872000 76799807432947164659213 ep56

noncomputable def ep58 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10 3726146621682076931 135107988821114880 23923919057947164659213 ep56 1189758039 65536000

noncomputable def ep59 := nat_lit 83450929165513032327495680

noncomputable def ep60 := nat_lit 54626304000000000000000000

noncomputable def ep61 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 13895465485198078137 562949953421312000 18993452499458425580443 ep60 Bool.false 3726146621682076931 135107988821114880

noncomputable def ep62 := nat_lit 18208768000000000000000000

noncomputable def ep63 := @Enclosure.Complex.IsNear.subLitP qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 2695490725190249503 140737488355328000 5989817499692013817481 ep62 Bool.false 4137844833934663331 135107988821114880 19827919057837912051213

noncomputable def ep64 := nat_lit 15644903295319413274828500514111488

noncomputable def ep65 := nat_lit 1048817033558452137361476719476736

noncomputable abbrev qz424 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz403 := qz424

noncomputable abbrev qz261 := (@HSub.hSub Complex Complex Complex qz397 qz398 qz403)

noncomputable abbrev qz262 := (Complex.log qz398)

noncomputable abbrev qz13 := (@HSub.hSub Complex Complex Complex qz254 (@HMul.hMul Complex Complex Complex qz253 qz261 qz262) qz255)

noncomputable abbrev qz263 := qz403

noncomputable abbrev qz14 := (@HMul.hMul Complex Complex Complex qz253 qz263 ↑qz252)

noncomputable abbrev qz404 := qz421

noncomputable abbrev qz264 := qz404

noncomputable abbrev qz15 := qz264

noncomputable abbrev qz16 := (@instHMul Nat instMulNat)

noncomputable abbrev qz405 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz265 := qz405

noncomputable abbrev qz17 := qz265

noncomputable abbrev qz18 := qz255

noncomputable abbrev qz266 := (@instHSub Int Int.instSub)

noncomputable abbrev qz19 := qz266

noncomputable abbrev qz267 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz20 := qz267

noncomputable abbrev qz268 := (@instHMul Int Int.instMul)

noncomputable abbrev qz21 := qz268

noncomputable abbrev qz269 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz22 := qz269

noncomputable def ep66 := @Enclosure.Complex.IsNear.of_eq qz7 (@HAdd.hAdd Complex Complex Complex qz8 (@HAdd.hAdd Complex Complex Complex qz8 qz13 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k)))))) Bool.true 2695490725190249503

noncomputable def ep67 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz8 qz13 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) Bool.true 2695593575553641503 140737488355328000

noncomputable def ep68 := nat_lit 1447130563920430624183156736

noncomputable def ep69 := nat_lit 13884303310681195318293299200000

noncomputable def ep70 := @ep67 5849331787374851369 17782000000000000000000 Bool.false 34487839763368536569 1125899906842624000 1613250000571789101 8891000000000000000000 Bool.false 392343 536870912 3 536870912 Bool.true 2074055879 402653184000 15859 402653184000 Bool.true ep68 2695490725190249503 140737488355328000 5989817499692013817481 ep62 Bool.false ep69

noncomputable def ep71 := @Enclosure.Complex.IsNear.addLitP qz13 qz14 Bool.true 2824921483287145503 140737488355328000 5578000000265476369 17782000000000000000000

noncomputable def ep72 := @ep71 Bool.false 34487839763368536569 1125899906842624000 1613250000571789101 8891000000000000000000 Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 Bool.true 176658420567483449540608 2695593575553641503 140737488355328000 5849331787374851369 17782000000000000000000 Bool.false 34487839763368536569 34487839763368536569 1125899906842624000

noncomputable abbrev qz23 := (@HMul.hMul Complex Complex Complex qz253 qz261 qz262)

noncomputable def ep73 := @Enclosure.Complex.IsNear.subLitP qz23 qz18 Bool.true 2508262134487657503 140737488355328000 5578000000265476369 17782000000000000000000 Bool.false 10468697277197142117

noncomputable def ep74 := @ep73 225179981368524800 1613250000571789101 8891000000000000000000 Bool.false 9000 4000 0 1 Bool.false 63436 4000 0 1 Bool.true 11299685933148582012000 2824921483287145503 140737488355328000 5578000000265476369 17782000000000000000000 Bool.false 27590271810694829255200 34487839763368536569 1125899906842624000 1613250000571789101 8891000000000000000000

noncomputable abbrev qz24 := qz261

noncomputable abbrev qz25 := qz262

noncomputable def ep75 := @Enclosure.Complex.IsNear.mul qz24 qz25 Bool.true 2508262134487657503 140737488355328000 5578000000265476369 17782000000000000000000 Bool.false 10468697277197142117 225179981368524800 1613250000571789101

noncomputable abbrev qz26 := (Complex.re qz261)

noncomputable abbrev qz27 := (Complex.re qz262)

noncomputable abbrev qz28 := (Complex.im qz261)

noncomputable abbrev qz29 := (Complex.im qz262)

noncomputable def ep76 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz26 qz27) (@HMul.hMul Real Real Real qz0 qz28 qz29) 21860350536960705 4503599627370496 437500000186711 26673000000000000000 12765592355070718137 562949953421312000

noncomputable def ep77 := nat_lit 45184833656904557017574762140925952

noncomputable def ep78 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz27 7000 4000 0 1 3122907219565815 1125899906842624 62500000026673 6668250000000000000

noncomputable def ep79 := @Enclosure.Complex.IsNear.re_isNear qz24 Bool.false 7000 4000 0 1 Bool.false 63436 4000 0 1

noncomputable abbrev qz270 := (Enclosure.sfrac Bool.false 63436 4000)

noncomputable abbrev qz30 := qz270

noncomputable def ep80 := @Enclosure.Complex.IsNear.of_eq qz24 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz30) Bool.false 7000 4000 0 1 Bool.false 63436 4000 0

noncomputable abbrev qz271 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz31 := (Complex.log (Complex.mk qz271 qz270))

noncomputable def ep81 := @Enclosure.Complex.IsNear.of_eq qz25 qz31 Bool.false 3122907219565815 1125899906842624 62500000026673 6668250000000000000 Bool.false 804943083111843 562949953421312 1000000000026673 53346000000000000000

noncomputable def ep82 := BSN.log_dyadic_bound 9126096 8201126096 1 0 1 131072 53346 0 1 291 8210252192 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 9126096) (BSN.artanhQ 8201126096) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz32 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz33 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz272 := (Real.log (Enclosure.sfrac Bool.false 4105126096 16000000))

noncomputable abbrev qz273 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep83 := @Enclosure.Real.IsNear.mulLit_ff qz32 qz272 1 2 0 1 3122907219565815 562949953421312 62500000026673 3334125000000000000 3122907219565815 1125899906842624 62500000026673 6668250000000000000 qz33 (BSN.isNear_log_sfrac 4105126096 16000000 3122907219565815 562949953421312 62500000026673 3334125000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4105126096) qz273)) Bool.false 26196844485307552235520 4722366482869645213696 1000000000426768 53346000000000000000 3122907219565815 562949953421312 62500000026673 3334125000000000000 (BSN.log_rat_reduce_isNear 4105126096 16000000 8 8210252192 8192000000 291 131072 24973259072661432 36028797018963968 53346 1000000000000000 rfl rfl rfl rfl (ep82 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep84 := BSN.arctan_dyadic_bound_f 9000 63436 2 1 131072 53346 6561000000000000 80967954182541006080 6561000000000000 19683000000000000 113355135855557408512 19683000000000000 18472 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 63436) 0 1 6561000000000000 80967954182541006080 6561000000000000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.arctanOddP 9000) (BSN.arctanOddQ 63436) 0 1 19683000000000000 113355135855557408512 19683000000000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz248 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz35 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz274 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 63436)))

noncomputable def ep85 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz274 884279719003555 562949953421312 1 2000000000000000 18472 131072 1 53346 105505499789635485696 804943083111843 562949953421312 1000000000026673 53346000000000000000 qz35 (ep84 rfl) rfl rfl

noncomputable abbrev qz36 := (Complex.mk qz271 qz270)

noncomputable abbrev qz37 := qz258

noncomputable abbrev qz275 := (@Eq.refl Real qz401)

noncomputable abbrev qz38 := qz275

noncomputable abbrev qz276 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 63436) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep86 := @Enclosure.Complex.IsNear.re_isNear qz25 Bool.false 3122907219565815 1125899906842624 62500000026673 6668250000000000000 Bool.false 804943083111843 562949953421312 1000000000026673 53346000000000000000 (ep81 (@congrArg Complex Complex qz18 qz36 Complex.log (BSN.w_shift_mk qz37 Bool.false 31718 1000 2 qz38 rfl)) (@Enclosure.Complex.IsNear.of_parts qz31 Bool.false 3122907219565815 1125899906842624 62500000026673 6668250000000000000 Bool.false 804943083111843 562949953421312 1000000000026673 53346000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz31) (@HMul.hMul Real Real Real qz0 qz32 qz272) Bool.false 3122907219565815 1125899906842624 62500000026673 6668250000000000000 (Enclosure.clog_re_eq 9000 63436 4000 4105126096 16000000 rfl rfl rfl) (ep83 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz31) qz276 Bool.false 804943083111843 562949953421312 1000000000026673 53346000000000000000 (Enclosure.clog_im_eq 9000 63436 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz276 (@HSub.hSub Real Real Real qz5 qz34 qz274) Bool.false 804943083111843 562949953421312 1000000000026673 53346000000000000000 (BSN.arctan_recip 63436 9000 rfl rfl) ep85))))

noncomputable def ep87 := @Enclosure.Real.IsNear.mulLit_ff qz28 qz29 63436 4000 0 1 804943083111843 562949953421312 1000000000026673 53346000000000000000

noncomputable def ep88 := @Enclosure.Complex.IsNear.im_isNear qz24 Bool.false 7000 4000 0 1 Bool.false 63436 4000 0 1

noncomputable def ep89 := @Enclosure.Complex.IsNear.im_isNear qz25 Bool.false 3122907219565815 1125899906842624 62500000026673 6668250000000000000 Bool.false 804943083111843 562949953421312 1000000000026673 53346000000000000000 (ep81 (@congrArg Complex Complex qz18 qz36 Complex.log (BSN.w_shift_mk qz37 Bool.false 31718 1000 2 qz38 rfl)) (@Enclosure.Complex.IsNear.of_parts qz31 Bool.false 3122907219565815 1125899906842624 62500000026673 6668250000000000000 Bool.false 804943083111843 562949953421312 1000000000026673 53346000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz31) (@HMul.hMul Real Real Real qz0 qz32 qz272) Bool.false 3122907219565815 1125899906842624 62500000026673 6668250000000000000 (Enclosure.clog_re_eq 9000 63436 4000 4105126096 16000000 rfl rfl rfl) (ep83 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz31) qz276 Bool.false 804943083111843 562949953421312 1000000000026673 53346000000000000000 (Enclosure.clog_im_eq 9000 63436 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz276 (@HSub.hSub Real Real Real qz5 qz34 qz274) Bool.false 804943083111843 562949953421312 1000000000026673 53346000000000000000 (BSN.arctan_recip 63436 9000 rfl rfl) ep85))))

noncomputable abbrev qz277 := (Enclosure.Real.IsNear.const Bool.false 63436 4000)

noncomputable abbrev qz39 := (@ep80 1 (BSN.w_sub_half_mk qz258 Bool.false 31718 1000 2 qz275 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz270 Bool.false 7000 4000 0 1 Bool.false 63436 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz277))

noncomputable def ep90 := @ep76 15859000000423007107 53346000000000000000000 ep77 2508262134487657503 140737488355328000 5578000000265476369 17782000000000000000000 (@ep78 21860350536960705 4503599627370496 437500000186711 26673000000000000000 (ep79 qz39) ep86 rfl) (@ep87 12765592355070718137 562949953421312000 15859000000423007107 53346000000000000000000 (ep88 qz39) ep89 rfl) rfl

noncomputable def ep91 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz26 qz29) (@HMul.hMul Real Real Real qz0 qz28 qz27) 5634601581782901 2251799813685248 7000000000186711 213384000000000000000 9905237119018852017 225179981368524800

noncomputable def ep92 := nat_lit 23573410578319787654999811362390016

noncomputable def ep93 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz29 7000 4000 0 1 804943083111843 562949953421312 1000000000026673 53346000000000000000

noncomputable def ep94 := @Enclosure.Real.IsNear.mulLit_ff qz28 qz27 63436 4000 0 1 3122907219565815 1125899906842624 62500000026673 6668250000000000000

noncomputable def ep95 := @ep91 991187500423007107 6668250000000000000000 ep92 10468697277197142117 225179981368524800 1613250000571789101 8891000000000000000000 (@ep93 5634601581782901 2251799813685248 7000000000186711 213384000000000000000 (ep79 qz39) ep89 rfl) (@ep94 9905237119018852017 225179981368524800 991187500423007107 6668250000000000000000 (ep88 qz39) ep86 rfl) rfl

noncomputable def ep96 := @Enclosure.Complex.IsNear.of_eq qz18 qz36 Bool.false 9000 4000 0 1 Bool.false 63436 4000 0 1 (BSN.w_shift_mk qz37 Bool.false 31718 1000 2 qz38 rfl)

noncomputable abbrev qz278 := (ep96 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 63436 4000) Bool.false 9000 4000 0 1 Bool.false 63436 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 63436 4000)))

noncomputable abbrev qz40 := qz278

noncomputable def ep97 := ep74 (@ep75 8891000000000000000000 (ep90 rfl) (ep95 rfl)) qz40 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz41 := qz263

noncomputable abbrev qz42 := (Complex.im ↑qz252)

noncomputable def ep98 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz41) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz41) qz42) 60223 65536 1 65536 0 1 0 1 60223 60223

noncomputable def ep99 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz41) (Complex.re ↑qz3) 1 2 0 1 60223 32768 1 32768 60223 65536 1 65536

noncomputable abbrev qz279 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz280 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz43 := (@Enclosure.Complex.IsNear.of_eq qz263 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz279) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz279 Bool.false 1 2 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 2) qz280))

noncomputable def ep100 := ep99 (@Enclosure.Complex.IsNear.re_isNear qz41 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz43) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 60223 32768 1 32768 (Complex.ofReal_re qz3) EMRow05.d4)

noncomputable def ep101 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz41) qz42 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable abbrev qz44 := qz279

noncomputable abbrev qz45 := qz280

noncomputable def ep102 := ep101 (@Enclosure.Complex.IsNear.im_isNear qz41 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz43) (@Enclosure.Real.IsNear.of_eq qz42 qz44 Bool.false 0 1 0 1 (@Eq.trans Real qz42 (0 : Real) qz44 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz45)

noncomputable def ep103 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz41) qz42) (@HMul.hMul Real Real Real qz0 (Complex.im qz41) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep104 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz41) qz42 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep105 := ep104 (@Enclosure.Complex.IsNear.re_isNear qz41 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz43) (@Enclosure.Real.IsNear.of_eq qz42 qz44 Bool.false 0 1 0 1 (@Eq.trans Real qz42 (0 : Real) qz44 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz45)

noncomputable def ep106 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz41) (Complex.re ↑qz3) 0 1 0 1 60223 32768 1 32768 0 1 0 1

noncomputable def ep107 := ep106 (@Enclosure.Complex.IsNear.im_isNear qz41 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz43) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 60223 32768 1 32768 (Complex.ofReal_re qz3) EMRow05.d4)

noncomputable def ep108 := @ep72 1613250000571789101 8891000000000000000000 (ep97 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz41 (↑qz3) Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 (@ep98 65536 1 65536 (ep100 rfl) (ep102 rfl) rfl rfl) (@ep103 1 0 1 (ep105 rfl) (ep107 rfl) rfl rfl))

noncomputable abbrev qz46 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz281 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz47 := (@HMul.hMul Complex Complex Complex qz253 (@HMul.hMul Complex Complex Complex qz253 (2 : Complex) qz281) (@HSub.hSub Complex Complex Complex qz254 (@HMul.hMul Complex Complex Complex qz253 (2 : Complex) qz281) (1 : Complex)))

noncomputable abbrev qz282 := (@HPow.hPow Complex Int Complex qz405 qz398 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz48 := qz282

noncomputable def ep109 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) qz48)) Bool.false 392343 536870912 3 536870912

noncomputable def ep110 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) qz48) Bool.false 0 1 0 1 Bool.false

noncomputable def ep111 := @ep110 0 1 0 1 Bool.false 392343 536870912 3 536870912 Bool.true 2074055879 402653184000 15859 402653184000 Bool.false 392343 392343 536870912 3 536870912 Bool.true 2074055879 2074055879 402653184000 15859

noncomputable def ep112 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz18 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz44 qz44) Bool.false 0 1 0 1 Bool.false

noncomputable def ep113 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) qz48 Bool.false 392343 536870912 3 536870912 Bool.true 2074055879 402653184000 15859 402653184000

noncomputable abbrev qz49 := (Complex.re qz282)

noncomputable abbrev qz50 := (Complex.im qz282)

noncomputable def ep114 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz49) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz50) 392343 536870912 3 536870912 0 1 0

noncomputable def ep115 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz49 1 12 0 1 1177029 134217728 9 134217728 392343

noncomputable def ep116 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz44) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz283 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz44 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz45)

noncomputable def ep117 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep116 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz283)

noncomputable def ep118 := @Enclosure.Complex.IsNear.re_isNear qz48 Bool.false 1177029 134217728 9 134217728 Bool.true 2074055879 33554432000 15859 33554432000

noncomputable abbrev qz406 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz284 := (@HPow.hPow Complex Nat Complex qz406 qz398 1)

noncomputable abbrev qz51 := (@Inv.inv Complex Complex.instInv qz284)

noncomputable def ep119 := @Enclosure.Complex.IsNear.of_eq qz48 qz51 Bool.false 1177029 134217728 9 134217728 Bool.true 2074055879 33554432000 15859

noncomputable def ep120 := @Enclosure.Complex.IsNear.of_parts qz51 Bool.false 1177029 134217728 9 134217728 Bool.true 2074055879 33554432000 15859

noncomputable abbrev qz52 := (Complex.re qz284)

noncomputable abbrev qz53 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz54 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz55 := qz284

noncomputable def ep121 := @Enclosure.Real.IsNear.mulLit_ff qz52 (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz55)) 9000 4000 0 1 130781 33554432 1 33554432

noncomputable def ep122 := @Enclosure.Complex.IsNear.re_isNear qz55 Bool.false 9000 4000 0 1 Bool.false 63436 4000 0 1

noncomputable def ep123 := @Enclosure.Complex.IsNear.of_eq qz55 qz18 Bool.false 9000 4000 0 1 Bool.false 63436 4000 0

noncomputable def ep124 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz55)) Bool.false 130781 33554432 1 33554432 130781 33554432 1

noncomputable abbrev qz56 := (@instHAdd Real Real.instAdd)

noncomputable abbrev qz57 := (Complex.im qz284)

noncomputable def ep125 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz55) (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 qz52 qz52) (@HMul.hMul Real Real Real qz0 qz57 qz57)) Bool.false 256570381 1000000 0 1

noncomputable def ep126 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz52 qz52) (@HMul.hMul Real Real Real qz0 qz57 qz57) 81 16 0 1 251507881 1000000

noncomputable def ep127 := @Enclosure.Real.IsNear.mulLit_ff qz52 qz52 9000 4000 0 1 9000 4000 0 1

noncomputable def ep128 := @Enclosure.Real.IsNear.mulLit_ff qz57 qz57 63436 4000 0 1 63436 4000 0 1

noncomputable def ep129 := @Enclosure.Complex.IsNear.im_isNear qz55 Bool.false 9000 4000 0 1 Bool.false 63436 4000 0 1

noncomputable abbrev qz58 := (ep122 (@ep123 1 (BSN.pow_one_c qz255) qz278))

noncomputable abbrev qz59 := (ep129 (@ep123 1 (BSN.pow_one_c qz255) qz278))

noncomputable def ep130 := @ep126 0 1 4105126096 256570381 1000000 0 1 (@ep127 81 16 0 1 qz58 qz58 rfl) (@ep128 251507881 1000000 0 1 qz59 qz59 rfl)

noncomputable def ep131 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz55) 256570381 1000000 0 1 65390 65391 16777216 (ep125 (Enclosure.Complex.normSq_eq_mul_add_mul qz55) (ep130 rfl rfl)) rfl

noncomputable def ep132 := @Enclosure.Real.IsNear.of_eq (Complex.re qz51) (@HMul.hMul Real Real Real qz0 qz52 (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz55))) Bool.false 1177029 134217728 9 134217728 (Enclosure.Complex.inv_re_eq_mul qz55) (@ep121 1177029 134217728 9 134217728 qz58 (@ep124 33554432 (ep131 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep133 := @Enclosure.Real.IsNear.of_eq (Complex.im qz51) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz57) (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz55))) Bool.true 2074055879 33554432000 15859 33554432000 (Enclosure.Complex.inv_im_eq_mul qz55)

noncomputable def ep134 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz57) (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz55)) 63436 4000 0 1 130781 33554432 1

noncomputable def ep135 := @ep134 33554432 2074055879 33554432000 15859 33554432000 (@Enclosure.Real.IsNear.neg qz57 Bool.false 63436 4000 0 1 qz59) (@ep124 33554432 (ep131 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep136 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz50 0 1 0 1 2074055879 33554432000 15859 33554432000 0

noncomputable def ep137 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep116 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz283)

noncomputable def ep138 := @Enclosure.Complex.IsNear.im_isNear qz48 Bool.false 1177029 134217728 9 134217728 Bool.true 2074055879 33554432000 15859 33554432000

noncomputable abbrev qz60 := (@ep119 33554432000 (BSN.zpow_one_sub_two_mul qz255 1 1 rfl rfl) (@ep120 33554432000 ep132 (ep133 ep135)))

noncomputable def ep139 := @ep114 1 392343 392343 536870912 3 536870912 (@ep115 536870912 3 536870912 ep117 (ep118 qz60) rfl) (@ep136 1 0 1 ep137 (ep138 qz60) rfl) rfl

noncomputable def ep140 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz50) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz49) 2074055879 402653184000 15859 402653184000 0 1 0

noncomputable def ep141 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz50 1 12 0 1 2074055879 33554432000 15859 33554432000 2074055879

noncomputable def ep142 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz49 0 1 0 1 1177029 134217728 9 134217728 0

noncomputable def ep143 := @ep140 1 2074055879 2074055879 402653184000 15859 402653184000 (@ep141 402653184000 15859 402653184000 ep117 (ep138 qz60) rfl) (@ep142 1 0 1 ep137 (ep118 qz60) rfl) rfl

noncomputable abbrev qz61 := (@Enclosure.Complex.IsNear.mk qz279 qz279 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz280 qz280)

noncomputable def ep144 := @ep111 402653184000 (@ep112 0 1 0 1 (BSN.stirling_sum_base qz18) qz61) (ep113 (ep139 rfl) (ep143 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep145 := @ep70 4137844833934663331 135107988821114880 19827919057837912051213 ep56 (ep108 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep109 Bool.true 2074055879 402653184000 15859 402653184000 (BSN.stirling_sum_succ qz18 0 1 rfl) (ep144 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep146 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz37 2) Bool.false 24908020675496641 4503599627370496 500000000186711 26673000000000000000 Bool.false 857704608859555 281474976710656

noncomputable abbrev qz62 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz256 qz257 qz281))

noncomputable def ep147 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz37 2) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz37 1) qz62) Bool.false 24908020675496641 4503599627370496 500000000186711 26673000000000000000 Bool.false 857704608859555 281474976710656 1000000000026673 26673000000000000000

noncomputable def ep148 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz37 1) qz62 Bool.false 24894637557402305 9007199254740992 500000000186711 53346000000000000000 Bool.false 875406316570019 562949953421312 1000000000026673 53346000000000000000 Bool.false

noncomputable def ep149 := nat_lit 448703010530813129902166842015744

noncomputable def ep150 := nat_lit 965689539213462230037503672320

noncomputable abbrev qz63 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz256 qz257 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep151 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz37 1) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz37 0) qz63) Bool.false 24894637557402305 9007199254740992 500000000186711 53346000000000000000 Bool.false 875406316570019 562949953421312 1000000000026673 53346000000000000000

noncomputable def ep152 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz37 0) qz63 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz285 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz30))

noncomputable def ep153 := @Enclosure.Complex.IsNear.of_eq qz63 qz285 Bool.false 24894637557402305 9007199254740992 500000000186711 53346000000000000000 Bool.false 875406316570019 562949953421312 1000000000026673 53346000000000000000

noncomputable def ep154 := nat_lit 709491959660455965840958881073301571024881379377513623723562596151062688187235714785485108054348267520

noncomputable def ep155 := nat_lit 26790544821614938106190631911590508924963230541155460594769533147035419967029759989227747181858914304

noncomputable def ep156 := nat_lit 862532547933414112277510674998600325733912468695918042352437317842000793112486365617434468024320

noncomputable def ep157 := BSN.log_dyadic_bound 1977126096 6073126096 6 5 ep154 131072 53346 ep155 ep156 88564 8050252192 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1977126096) (BSN.artanhQ 6073126096) 0 5 ep155 ep154 ep156 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep158 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 4025126096 16000000)) 1 2 0 1 24894637557402305 4503599627370496 500000000186711 26673000000000000000 24894637557402305 9007199254740992 500000000186711 53346000000000000000 qz33 (BSN.isNear_log_sfrac 4025126096 16000000 24894637557402305 4503599627370496 500000000186711 26673000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4025126096) qz273)) Bool.false 26103919471390679367680 4722366482869645213696 1000000000373422 53346000000000000000 24894637557402305 4503599627370496 500000000186711 26673000000000000000 (BSN.log_rat_reduce_isNear 4025126096 16000000 7 8050252192 4096000000 88564 131072 24973259072661432 36028797018963968 53346 1000000000000000 rfl rfl rfl rfl (ep157 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep159 := BSN.arctan_dyadic_bound_f 1000 63436 1 0 131072 53346 0 1 1 0 1 1 2066 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 63436) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 63436) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz286 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz287 := (@Nat.cast Real Real.instNatCast 63436)

noncomputable def ep160 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz286 qz287)) 884279719003555 562949953421312 1 2000000000000000 2066 131072 1 53346 114741256725465530368 875406316570019 562949953421312 1000000000026673 53346000000000000000 qz35 (ep159 rfl) rfl rfl

noncomputable abbrev qz64 := (@HAdd.hAdd Complex Complex Complex qz256 qz257 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz288 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz30)

noncomputable def ep161 := @ep152 24894637557402305 9007199254740992 500000000186711 53346000000000000000 Bool.false 875406316570019 562949953421312 1000000000026673 53346000000000000000 Bool.false 24894637557402305 24894637557402305 9007199254740992 500000000186711 53346000000000000000 Bool.false 875406316570019 875406316570019 562949953421312 1000000000026673 53346000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz37 0) (Complex.mk qz44 qz44) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz37) qz61) (ep153 (@congrArg Complex Complex qz64 qz288 Complex.log (BSN.w_shift_mk qz37 Bool.false 31718 1000 0 qz38 rfl)) (@Enclosure.Complex.IsNear.of_parts qz285 Bool.false 24894637557402305 9007199254740992 500000000186711 53346000000000000000 Bool.false 875406316570019 562949953421312 1000000000026673 53346000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz285) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 4025126096 16000000))) Bool.false 24894637557402305 9007199254740992 500000000186711 53346000000000000000 (Enclosure.clog_re_eq 1000 63436 4000 4025126096 16000000 rfl rfl rfl) (ep158 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz285) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz287 qz286)) Bool.false 875406316570019 562949953421312 1000000000026673 53346000000000000000 (Enclosure.clog_im_eq 1000 63436 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz287 qz286)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz286 qz287))) Bool.false 875406316570019 562949953421312 1000000000026673 53346000000000000000 (BSN.arctan_recip 63436 1000 rfl rfl) ep160)))) rfl rfl

noncomputable abbrev qz289 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz30))

noncomputable def ep162 := @Enclosure.Complex.IsNear.of_eq qz62 qz289 Bool.false 24921403793590977 9007199254740992 500000000186711 53346000000000000000 Bool.false 840002901149091 562949953421312 1000000000026673 53346000000000000000

noncomputable def ep163 := nat_lit 738033817654713845015982425671564467569969565942392597269860564536203706600145370352495525923148267520

noncomputable def ep164 := nat_lit 28357058384442384832702954831588563788509788118858101936382993818449075923708414622234615907618914304

noncomputable def ep165 := nat_lit 973142328593388800251269837021903908055243341201766130712437965300467839105084601182695268024320

noncomputable def ep166 := BSN.log_dyadic_bound 2001126096 6097126096 6 5 ep163 131072 53346 ep164 ep165 89343 8098252192 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 2001126096) (BSN.artanhQ 6097126096) 0 5 ep164 ep163 ep165 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep167 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 4049126096 16000000)) 1 2 0 1 24921403793590977 4503599627370496 500000000186711 26673000000000000000 24921403793590977 9007199254740992 500000000186711 53346000000000000000 qz33 (BSN.isNear_log_sfrac 4049126096 16000000 24921403793590977 4503599627370496 500000000186711 26673000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4049126096) qz273)) Bool.false 26131985904268452298752 4722366482869645213696 1000000000373422 53346000000000000000 24921403793590977 4503599627370496 500000000186711 26673000000000000000 (BSN.log_rat_reduce_isNear 4049126096 16000000 7 8098252192 4096000000 89343 131072 24973259072661432 36028797018963968 53346 1000000000000000 rfl rfl rfl rfl (ep166 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep168 := BSN.arctan_dyadic_bound_f 5000 63436 1 0 131072 53346 0 1 1 0 1 1 10309 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 63436) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 63436) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz290 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep169 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz290 qz287)) 884279719003555 562949953421312 1 2000000000000000 10309 131072 1 53346 110100860259413655552 840002901149091 562949953421312 1000000000026673 53346000000000000000 qz35 (ep168 rfl) rfl rfl

noncomputable abbrev qz65 := (@HAdd.hAdd Complex Complex Complex qz256 qz257 qz281)

noncomputable abbrev qz291 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz30)

noncomputable def ep170 := @ep148 24921403793590977 9007199254740992 500000000186711 53346000000000000000 Bool.false 840002901149091 562949953421312 1000000000026673 53346000000000000000 Bool.false ep149 24908020675496641 4503599627370496 500000000186711 26673000000000000000 Bool.false ep150 857704608859555 281474976710656 1000000000026673 26673000000000000000 (ep151 (BSN.log_sum_c_succ qz37 0 1 rfl) (ep161 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep162 (@congrArg Complex Complex qz65 qz291 Complex.log (BSN.w_shift_mk qz37 Bool.false 31718 1000 1 qz38 rfl)) (@Enclosure.Complex.IsNear.of_parts qz289 Bool.false 24921403793590977 9007199254740992 500000000186711 53346000000000000000 Bool.false 840002901149091 562949953421312 1000000000026673 53346000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz289) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 4049126096 16000000))) Bool.false 24921403793590977 9007199254740992 500000000186711 53346000000000000000 (Enclosure.clog_re_eq 5000 63436 4000 4049126096 16000000 rfl rfl rfl) (ep167 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz289) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz287 qz290)) Bool.false 840002901149091 562949953421312 1000000000026673 53346000000000000000 (Enclosure.clog_im_eq 5000 63436 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz287 qz290)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz290 qz287))) Bool.false 840002901149091 562949953421312 1000000000026673 53346000000000000000 (BSN.arctan_recip 63436 5000 rfl rfl) ep169)))) rfl rfl

noncomputable def ep171 := @ep63 ep56 Bool.false 24908020675496641 4503599627370496 500000000186711 26673000000000000000 Bool.false 857704608859555 281474976710656 1000000000026673 26673000000000000000 Bool.true ep64 13895465485198078137 562949953421312000 18993452499458425580443 ep60 Bool.false ep65 3726146621682076931 135107988821114880 23923919057947164659213 ep56 (@ep66 140737488355328000 5989817499692013817481 ep62 Bool.false 4137844833934663331 135107988821114880 19827919057837912051213 ep56 (BSN.logGammaStirling_unfold 1 qz18) (ep145 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep146 1000000000026673 26673000000000000000 (BSN.log_sum_c_eq qz37 2) (ep147 (BSN.log_sum_c_succ qz37 1 2 rfl) (ep170 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz66 := (@HDiv.hDiv Real Real Real qz251 qz258 (2 : Real))

noncomputable def ep172 := @Enclosure.Real.IsNear.mulLit_ff qz66 (Real.log Real.pi) 31718 2000 0 1 75021 65536 1 32768 1189758039 65536000 15859 32768000 (@Enclosure.Real.IsNear.of_eq qz66 (Enclosure.sfrac Bool.false 31718 2000) Bool.false 31718 2000 0 1 (BSN.t_half_eq qz37 Bool.false 31718 1000 qz38) (Enclosure.Real.IsNear.const Bool.false 31718 2000)) EMRow05.d5 rfl

noncomputable def ep173 := @ep58 15859 32768000 ep59 31834003130154812747 3377699720527872000 76799807432947164659213 ep56 (@ep61 23923919057947164659213 ep56 (ep171 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep172 rfl rfl

noncomputable def ep174 := nat_lit 497306597595129109137774355208510475865360064902290490289686697928106240

noncomputable def ep175 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080

noncomputable def ep176 := nat_lit 999123166771566304614004320303359645221990541929144706089597573079296

noncomputable def ep177 := nat_lit 1300852032383898464200986351884655330697964566247637430758367717550530816

noncomputable def ep178 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800

noncomputable abbrev qz292 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz293 := (BSN.sinOddQ 268435456)

noncomputable def ep179 := BSN.sin_dyadic_bound_f 421650266 268435456 3 2 131072 53399 ep174 ep175 ep176 ep177 ep178 ep176 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 421650266) qz292 0 2 ep174 ep175 ep176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 421650266) qz293 0 2 ep177 ep178 ep176 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz67 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep180 := @ep55 65536 Bool.true 131071 131072 1 26673 (@ep57 1235321 131072 47 65536 ep173 rfl) (Enclosure.sfrac_false_div 1235321 131072) (BSN.cos_reduce1 qz260 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29670999747634881626112) qz67) 226375608064910080 72057594037927936 Bool.false 131071 131072 1 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q1 1235321 131072 226375608064910080 72057594037927936 1 29670999747634881626112 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131071 131072 29670999747634881626112 18889465931478580854784 421650266 268435456 53399 53346 (ep179 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep181 := nat_lit 322781961479049296058777600

noncomputable abbrev qz407 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz294 := qz407

noncomputable abbrev qz68 := qz294

noncomputable abbrev qz408 := (@Neg.neg Complex Complex.instNeg qz423)

noncomputable abbrev qz295 := qz408

noncomputable abbrev qz69 := qz295

noncomputable abbrev qz296 := (@HPow.hPow Complex Complex Complex qz407 (@Nat.cast Complex Complex.instNatCast 7) qz408)

noncomputable abbrev qz70 := qz296

noncomputable abbrev qz297 := (@Nat.cast Complex Complex.instNatCast 7)

noncomputable abbrev qz71 := (@HAdd.hAdd Complex Complex Complex qz256 (@HDiv.hDiv Complex Complex Complex qz264 qz297 (@HSub.hSub Complex Complex Complex qz254 qz259 (1 : Complex))) qz263)

noncomputable abbrev qz72 := (@instHSub Nat instSubNat)

noncomputable abbrev qz298 := qz406

noncomputable abbrev qz73 := qz298

noncomputable abbrev qz74 := qz297

noncomputable def ep182 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz11 1 7) (@HAdd.hAdd Complex Complex Complex qz8 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 7, @HPow.hPow Complex Complex Complex qz68 (@Nat.cast Complex Complex.instNatCast n) qz69) (@HMul.hMul Complex Complex Complex qz4 qz70 (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) Bool.false 44446802118268155461651 45380435479564910592000 417046021976728046659471

noncomputable def ep183 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 7, @HPow.hPow Complex Complex Complex qz68 (@Nat.cast Complex Complex.instNatCast n) qz69) (@HMul.hMul Complex Complex Complex qz4 qz70 (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) Bool.false 4073764361 4294967296 252568349203 76373108457472

noncomputable def ep184 := nat_lit 190897561509745251866034827165696

noncomputable def ep185 := nat_lit 52022003013788923776442164051968

noncomputable def ep186 := @ep183 Bool.true 1130760431 4294967296 249643814791 76373108457472 Bool.false 1403587117426510739651 45380435479564910592000 35813726951489508601471 ep53 Bool.false 35677943405130206653267 181521741918259642368000 100664441051455405795963 ep181 Bool.false ep184 44446802118268155461651 45380435479564910592000 417046021976728046659471 ep53 Bool.true ep185 12112316445864020794733 181521741918259642368000

noncomputable def ep187 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 7, @HPow.hPow Complex Complex Complex qz68 (@Nat.cast Complex Complex.instNatCast n) qz69) (BSN.headSumC qz11 7) Bool.false 4073764361 4294967296 252568349203 76373108457472 Bool.true 1130760431 4294967296 249643814791

noncomputable abbrev qz75 := (BSN.headSumC qz259 6)

noncomputable abbrev qz76 := (@HPow.hPow Complex Complex Complex qz294 (@Nat.cast Complex Complex.instNatCast 6) qz295)

noncomputable def ep188 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz11 7) (@HAdd.hAdd Complex Complex Complex qz8 qz75 qz76) Bool.false 4073764361 4294967296 252568349203 76373108457472 Bool.true 1130760431 4294967296 249643814791 76373108457472

noncomputable def ep189 := @Enclosure.Complex.IsNear.addLitP qz75 qz76 Bool.false 4779315017 8589934592 319397568409 114559662686208 Bool.true 642695721 4294967296 632406286493 229119325372416 Bool.false

noncomputable abbrev qz77 := (BSN.headSumC qz259 5)

noncomputable abbrev qz78 := (@HPow.hPow Complex Complex Complex qz294 (@Nat.cast Complex Complex.instNatCast 5) qz295)

noncomputable def ep190 := @Enclosure.Complex.IsNear.of_eq qz75 (@HAdd.hAdd Complex Complex Complex qz8 qz77 qz78) Bool.false 4779315017 8589934592 319397568409 114559662686208 Bool.true 642695721 4294967296 632406286493 229119325372416

noncomputable def ep191 := @Enclosure.Complex.IsNear.addLitP qz77 qz78 Bool.false 4110824671 17179869184 1021955820695 458238650744832 Bool.false 1423358745 8589934592 504595954993 229119325372416 Bool.false

noncomputable abbrev qz79 := (BSN.headSumC qz259 4)

noncomputable abbrev qz80 := (@HPow.hPow Complex Complex Complex qz294 (@Nat.cast Complex Complex.instNatCast 4) qz295)

noncomputable def ep192 := @Enclosure.Complex.IsNear.of_eq qz77 (@HAdd.hAdd Complex Complex Complex qz8 qz79 qz80) Bool.false 4110824671 17179869184 1021955820695 458238650744832 Bool.false 1423358745 8589934592 504595954993 229119325372416

noncomputable def ep193 := @Enclosure.Complex.IsNear.addLitP qz79 qz80 Bool.true 4478323499 17179869184 245142506027 152746216914944 Bool.false 1372241445 8589934592 121019635703 76373108457472 Bool.false

noncomputable abbrev qz81 := (BSN.headSumC qz259 3)

noncomputable abbrev qz409 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz299 := qz409

noncomputable abbrev qz82 := (@HPow.hPow Complex Complex Complex qz294 qz299 qz295)

noncomputable def ep194 := @Enclosure.Complex.IsNear.of_eq qz79 (@HAdd.hAdd Complex Complex Complex qz8 qz81 qz82) Bool.true 4478323499 17179869184 245142506027 152746216914944 Bool.false 1372241445 8589934592 121019635703 76373108457472

noncomputable def ep195 := @Enclosure.Complex.IsNear.addLitP qz81 qz82 Bool.false 2516066063 8589934592 11978513419 13477607374848 Bool.true 9036495 2147483648 5887044989 6738803687424 Bool.true

noncomputable abbrev qz83 := (BSN.headSumC qz259 2)

noncomputable abbrev qz410 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz300 := qz410

noncomputable abbrev qz84 := (@HPow.hPow Complex Complex Complex qz294 qz300 qz295)

noncomputable def ep196 := @Enclosure.Complex.IsNear.of_eq qz81 (@HAdd.hAdd Complex Complex Complex qz8 qz83 qz84) Bool.false 2516066063 8589934592 11978513419 13477607374848 Bool.true 9036495 2147483648 5887044989 6738803687424

noncomputable def ep197 := @Enclosure.Complex.IsNear.addLitP qz83 qz84 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep198 := @Enclosure.Complex.IsNear.of_eq qz83 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz44) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz11)

noncomputable abbrev qz85 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable abbrev qz86 := (@HMul.hMul Real Real Real qz248 qz258 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable def ep199 := @Enclosure.Complex.IsNear.of_eq qz84 (Complex.mk (@HMul.hMul Real Real Real qz0 qz85 (Real.cos qz86)) (@HMul.hMul Real Real Real qz0 qz85 (@Neg.neg Real Real.instNeg (Real.sin qz86)))) Bool.true 6073868529 8589934592 11978513419 13477607374848 Bool.true 9036495 2147483648 5887044989 6738803687424 (BSN.cpow_neg_s_mk qz37 31718 1000 2 qz38 rfl)

noncomputable abbrev qz87 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz88 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep200 := @Enclosure.Real.IsNear.inv_image qz87 185363 131072 1 131072 46340 46342 65536 (@Enclosure.Real.IsNear.of_eq qz87 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2) qz88)) Bool.false 185363 131072 1 131072 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2) qz88)) Bool.false 185363 131072 1 131072 185363 131072 1 131072 (BSN.sqrt_enclosure 2 1 92681 92682 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep201 := BSN.log_dyadic_bound 1 3 6 5 613814355 65536 26673 24381081 945 45426 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep202 := nat_lit 489823783529698895319573242949174366273403009698842795262216245933506560

noncomputable def ep203 := nat_lit 969340883777844449407366473117924317591324469170881798123224286887936

noncomputable def ep204 := nat_lit 1281302404956428215776032281053265748487574309594502083727890661932793856

noncomputable def ep205 := BSN.sin_dyadic_bound_f 420058296 268435456 3 2 131072 53399 ep202 ep175 ep203 ep204 ep178 ep203 131069 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 420058296) qz292 0 2 ep202 ep175 ep203 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 420058296) qz293 0 2 ep204 ep178 ep203 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz89 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz301 := (Enclosure.Real.IsNear.const Bool.false 31718 1000)

noncomputable abbrev qz90 := qz301

noncomputable abbrev qz302 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2881643) qz12)

noncomputable abbrev qz303 := (BSN.isNear_log_sfrac 2 1 45426 65536 1 26673 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 45426 65536 26673 rfl rfl rfl (ep201 rfl)))

noncomputable def ep206 := @Enclosure.Real.IsNear.cos_image qz86 qz302 Bool.false 2881643 131072 157 131072 Bool.true 131069 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz86 Bool.false 360205467 16384000 15859 13336500 2881643 131072 157 131072 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz89 31718 1000 0 1 45426 65536 1 26673 360205467 16384000 15859 13336500 qz90 qz303 rfl) rfl) (Enclosure.sfrac_false_div 2881643 131072) (BSN.cos_reduce1 qz302 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29558974808782920482816) qz67) 226375608064910080 72057594037927936 Bool.false 131069 131072 3 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q1 2881643 131072 226375608064910080 72057594037927936 3 29558974808782920482816 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131069 131072 29558974808782920482816 18889465931478580854784 420058296 268435456 53399 53346 (ep205 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep207 := nat_lit 272555142353733983821721742293149280959708927374544167055952680757231616

noncomputable def ep208 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120

noncomputable def ep209 := nat_lit 815726745293646262566350493933211994243944133185290737571611593697918976

noncomputable def ep210 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400

noncomputable abbrev qz304 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz305 := (BSN.cosOddQ 268435456)

noncomputable def ep211 := BSN.cos_dyadic_bound_f 420058296 268435456 3 2 131072 53399 ep207 ep208 ep203 ep209 ep210 ep203 780 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 420058296) qz304 0 2 ep207 ep208 ep203 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 420058296) qz305 0 2 ep209 ep210 ep203 rfl rfl rfl rfl) rfl rfl

noncomputable def ep212 := @Enclosure.Real.IsNear.sin_image qz86 qz302 Bool.false 2881643 131072 157 131072 Bool.false 780 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz86 Bool.false 360205467 16384000 15859 13336500 2881643 131072 157 131072 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz89 31718 1000 0 1 45426 65536 1 26673 360205467 16384000 15859 13336500 qz90 qz303 rfl) rfl) (Enclosure.sfrac_false_div 2881643 131072) (BSN.sin_reduce1 qz302 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29558974808782920482816) qz67) 226375608064910080 72057594037927936 Bool.false 780 131072 3 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q1 2881643 131072 226375608064910080 72057594037927936 3 29558974808782920482816 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 780 131072 29558974808782920482816 18889465931478580854784 420058296 268435456 53399 53346 (ep211 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz306 := (@Enclosure.Real.IsNear.recentre' qz85 Bool.false 92682 131072 2 131072 46341 65536 1 65536 (ep200 rfl rfl) rfl)

noncomputable def ep213 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz85 (Real.cos qz86)) (@HMul.hMul Real Real Real qz0 qz85 (@Neg.neg Real Real.instNeg (Real.sin qz86))) Bool.true 6073868529 8589934592 11978513419 13477607374848 Bool.true 9036495 2147483648 5887044989 6738803687424 (@Enclosure.Real.IsNear.mulLit_ft qz85 (Real.cos qz86) 46341 65536 1 65536 131069 131072 4318733 3496083456 6073868529 8589934592 11978513419 13477607374848 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz86) Bool.true 131069 131072 4318733 3496083456 131069 131072 4318733 3496083456 (ep206 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz85 (@Neg.neg Real Real.instNeg (Real.sin qz86)) 46341 65536 1 65536 195 32768 4318733 3496083456 9036495 2147483648 5887044989 6738803687424 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz86) Bool.false 195 32768 4318733 3496083456 (@Enclosure.Real.IsNear.recentre' (Real.sin qz86) Bool.false 780 131072 4318733 3496083456 195 32768 4318733 3496083456 (ep212 rfl rfl) rfl)) rfl)

noncomputable def ep214 := @ep197 6073868529 8589934592 11978513419 13477607374848 Bool.true 9036495 2147483648 5887044989 6738803687424 Bool.false 2516066063 2516066063 8589934592 11978513419 13477607374848 Bool.true 9036495 9036495 2147483648 5887044989 6738803687424 (ep198 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz44 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz45)) (ep199 ep213) rfl rfl

noncomputable abbrev qz307 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz91 := (@Inv.inv Real Real.instInv (Real.sqrt qz307))

noncomputable abbrev qz92 := (@HMul.hMul Real Real Real qz248 qz258 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep215 := @Enclosure.Complex.IsNear.of_eq qz82 (Complex.mk (@HMul.hMul Real Real Real qz0 qz91 (Real.cos qz92)) (@HMul.hMul Real Real Real qz0 qz91 (@Neg.neg Real Real.instNeg (Real.sin qz92)))) Bool.true 9510455625 17179869184 328158061835 458238650744832 Bool.false 1408387425 8589934592 162899377483 229119325372416 (BSN.cpow_neg_s_mk qz37 31718 1000 3 qz38 rfl)

noncomputable abbrev qz93 := (Real.sqrt qz307)

noncomputable abbrev qz94 := qz307

noncomputable def ep216 := @Enclosure.Real.IsNear.inv_image qz93 227023 131072 1 131072 37837 37838 65536 (@Enclosure.Real.IsNear.of_eq qz93 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz94 qz88)) Bool.false 227023 131072 1 131072 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz94 qz88)) Bool.false 227023 131072 1 131072 227023 131072 1 131072 (BSN.sqrt_enclosure 3 1 113511 113512 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep217 := BSN.log_dyadic_bound 1 2 9 8 2258332876800 65536 26673 222698787165 2027025 71998 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1) (BSN.artanhQ 2) 0 8 222698787165 2258332876800 2027025 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep218 := nat_lit 35695404151148014137349860710416

noncomputable def ep219 := nat_lit 124615124604835863084731911901282304

noncomputable def ep220 := nat_lit 1869226869072537946270978678519234560

noncomputable def ep221 := BSN.cos_dyadic_bound_f 77295298 268435456 2 1 131072 53399 ep218 ep219 ep218 ep218 ep220 ep218 125675 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 77295298) qz304 0 1 ep218 ep219 ep218 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 77295298) qz305 0 1 ep218 ep220 ep218 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz95 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4567265) qz12)

noncomputable abbrev qz309 := (BSN.isNear_log_sfrac 3 1 71998 65536 1 26673 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 71998 65536 26673 rfl rfl rfl (ep217 rfl)))

noncomputable def ep222 := @Enclosure.Real.IsNear.cos_image qz92 qz308 Bool.false 4567265 131072 39 32768 Bool.true 125675 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz92 Bool.false 570908141 16384000 15859 13336500 4567265 131072 39 32768 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz95 31718 1000 0 1 71998 65536 1 26673 570908141 16384000 15859 13336500 qz90 qz309 rfl) rfl) (Enclosure.sfrac_false_div 4567265 131072) (BSN.cos_reduce2 qz308 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5439173061028201103360) qz67) 226375608064910080 72057594037927936 Bool.false 125675 131072 5 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q2 4567265 131072 226375608064910080 72057594037927936 5 5439173061028201103360 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 125675 131072 5439173061028201103360 18889465931478580854784 77295298 268435456 53399 53346 (ep221 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep223 := nat_lit 623075623024179315423659559506411520

noncomputable def ep224 := nat_lit 4361529361169255207965616916544880640

noncomputable def ep225 := BSN.sin_dyadic_bound_f 77295298 268435456 2 1 131072 53399 ep218 ep223 ep218 ep218 ep224 ep218 37222 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 77295298) qz292 0 1 ep218 ep223 ep218 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 77295298) qz293 0 1 ep218 ep224 ep218 rfl rfl rfl rfl) rfl rfl

noncomputable def ep226 := @Enclosure.Real.IsNear.sin_image qz92 qz308 Bool.false 4567265 131072 39 32768 Bool.true 37222 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz92 Bool.false 570908141 16384000 15859 13336500 4567265 131072 39 32768 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz95 31718 1000 0 1 71998 65536 1 26673 570908141 16384000 15859 13336500 qz90 qz309 rfl) rfl) (Enclosure.sfrac_false_div 4567265 131072) (BSN.sin_reduce2 qz308 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5439173061028201103360) qz67) 226375608064910080 72057594037927936 Bool.false 37222 131072 5 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q2 4567265 131072 226375608064910080 72057594037927936 5 5439173061028201103360 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 37222 131072 5439173061028201103360 18889465931478580854784 77295298 268435456 53399 53346 (ep225 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz310 := (@Enclosure.Real.IsNear.recentre' qz91 Bool.false 75675 131072 1 131072 75675 131072 1 131072 (ep216 rfl rfl) rfl)

noncomputable def ep227 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz91 (Real.cos qz92)) (@HMul.hMul Real Real Real qz0 qz91 (@Neg.neg Real Real.instNeg (Real.sin qz92))) Bool.true 9510455625 17179869184 328158061835 458238650744832 Bool.false 1408387425 8589934592 162899377483 229119325372416 (@Enclosure.Real.IsNear.mulLit_ft qz91 (Real.cos qz92) 75675 131072 1 131072 125675 131072 1073015 874020864 9510455625 17179869184 328158061835 458238650744832 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz92) Bool.true 125675 131072 1073015 874020864 125675 131072 1073015 874020864 (ep222 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz91 (@Neg.neg Real Real.instNeg (Real.sin qz92)) 75675 131072 1 131072 18611 65536 1073015 874020864 1408387425 8589934592 162899377483 229119325372416 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz92) Bool.true 18611 65536 1073015 874020864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz92) Bool.true 37222 131072 1073015 874020864 18611 65536 1073015 874020864 (ep226 rfl rfl) rfl)) rfl)

noncomputable def ep228 := @ep195 9510455625 17179869184 328158061835 458238650744832 Bool.false 1408387425 8589934592 162899377483 229119325372416 Bool.true 38468505938226577408 4478323499 17179869184 245142506027 152746216914944 Bool.false 2946866064245391360 1372241445 8589934592 121019635703 76373108457472 (ep196 (BSN.head_sum_c_succ qz11 2 3 rfl rfl) (ep214 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep215 ep227) rfl rfl

noncomputable abbrev qz96 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable abbrev qz97 := (@HMul.hMul Real Real Real qz248 qz258 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep229 := @Enclosure.Complex.IsNear.of_eq qz80 (Complex.mk (@HMul.hMul Real Real Real qz0 qz96 (Real.cos qz97)) (@HMul.hMul Real Real Real qz0 qz96 (@Neg.neg Real Real.instNeg (Real.sin qz97)))) Bool.false 4294574085 8589934592 143264151307 229119325372416 Bool.false 12779325 2147483648 35384261971 57279831343104 (BSN.cpow_neg_s_mk qz37 31718 1000 4 qz38 rfl)

noncomputable abbrev qz98 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable def ep230 := @Enclosure.Real.IsNear.inv_image qz98 262145 131072 1 131072 32767 32768 65536 (@Enclosure.Real.IsNear.of_eq qz98 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4) qz88)) Bool.false 262145 131072 1 131072 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4) qz88)) Bool.false 262145 131072 1 131072 262145 131072 1 131072 (BSN.sqrt_enclosure 4 1 131072 131073 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep231 := nat_lit 753960950911045074462890625

noncomputable def ep232 := nat_lit 117048680082474133384580175

noncomputable def ep233 := BSN.log_dyadic_bound 3 5 12 11 ep231 65536 26673 ep232 431467934736729065175 90852 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 3) (BSN.artanhQ 5) 0 11 ep232 ep231 431467934736729065175 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep234 := nat_lit 482402379339082605579735826403575451986617993910098538624510396993699840

noncomputable def ep235 := nat_lit 940246376927964828488922264686835269635258431153872815032262679658496

noncomputable def ep236 := nat_lit 1261912499373047262034135575961776069528399565637913711839855947787862016

noncomputable def ep237 := BSN.sin_dyadic_bound_f 418461212 268435456 3 2 131072 53399 ep234 ep175 ep235 ep236 ep178 ep235 131062 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 418461212) qz292 0 2 ep234 ep175 ep235 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 418461212) qz293 0 2 ep236 ep178 ep235 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz99 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz311 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5763287) qz12)

noncomputable abbrev qz312 := (BSN.isNear_log_sfrac 4 1 90852 65536 1 26673 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 90852 65536 26673 rfl rfl rfl (ep233 rfl)))

noncomputable def ep238 := @Enclosure.Real.IsNear.cos_image qz97 qz311 Bool.false 5763287 131072 157 131072 Bool.false 131062 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz97 Bool.false 360205467 8192000 15859 13336500 5763287 131072 157 131072 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz99 31718 1000 0 1 90852 65536 1 26673 360205467 8192000 15859 13336500 qz90 qz312 rfl) rfl) (Enclosure.sfrac_false_div 5763287 131072) (BSN.cos_reduce3 qz311 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29446590032470022815744) qz67) 226375608064910080 72057594037927936 Bool.false 131062 131072 6 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q3 5763287 131072 226375608064910080 72057594037927936 6 29446590032470022815744 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131062 131072 29446590032470022815744 18889465931478580854784 418461212 268435456 53399 53346 (ep237 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep239 := nat_lit 268419209133680543023626091230736066779070111475012020486964559520792576

noncomputable def ep240 := nat_lit 803377134647185699413900429162834529797939817562728315830829153203060736

noncomputable def ep241 := BSN.cos_dyadic_bound_f 418461212 268435456 3 2 131072 53399 ep239 ep208 ep235 ep240 ep210 ep235 1560 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 418461212) qz304 0 2 ep239 ep208 ep235 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 418461212) qz305 0 2 ep240 ep210 ep235 rfl rfl rfl rfl) rfl rfl

noncomputable def ep242 := @Enclosure.Real.IsNear.sin_image qz97 qz311 Bool.false 5763287 131072 157 131072 Bool.true 1560 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz97 Bool.false 360205467 8192000 15859 13336500 5763287 131072 157 131072 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz99 31718 1000 0 1 90852 65536 1 26673 360205467 8192000 15859 13336500 qz90 qz312 rfl) rfl) (Enclosure.sfrac_false_div 5763287 131072) (BSN.sin_reduce3 qz311 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29446590032470022815744) qz67) 226375608064910080 72057594037927936 Bool.false 1560 131072 6 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q3 5763287 131072 226375608064910080 72057594037927936 6 29446590032470022815744 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1560 131072 29446590032470022815744 18889465931478580854784 418461212 268435456 53399 53346 (ep241 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz313 := (@Enclosure.Real.IsNear.recentre' qz96 Bool.false 65535 131072 1 131072 65535 131072 1 131072 (ep230 rfl rfl) rfl)

noncomputable def ep243 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz96 (Real.cos qz97)) (@HMul.hMul Real Real Real qz0 qz96 (@Neg.neg Real Real.instNeg (Real.sin qz97))) Bool.false 4294574085 8589934592 143264151307 229119325372416 Bool.false 12779325 2147483648 35384261971 57279831343104 (@Enclosure.Real.IsNear.mulLit_ff qz96 (Real.cos qz97) 65535 131072 1 131072 65531 65536 4318733 3496083456 4294574085 8589934592 143264151307 229119325372416 qz313 (@Enclosure.Real.IsNear.recentre' (Real.cos qz97) Bool.false 131062 131072 4318733 3496083456 65531 65536 4318733 3496083456 (ep238 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz96 (@Neg.neg Real Real.instNeg (Real.sin qz97)) 65535 131072 1 131072 195 16384 4318733 3496083456 12779325 2147483648 35384261971 57279831343104 qz313 (@Enclosure.Real.IsNear.neg (Real.sin qz97) Bool.true 195 16384 4318733 3496083456 (@Enclosure.Real.IsNear.recentre' (Real.sin qz97) Bool.true 1560 131072 4318733 3496083456 195 16384 4318733 3496083456 (ep242 rfl rfl) rfl)) rfl)

noncomputable def ep244 := @ep193 4294574085 8589934592 143264151307 229119325372416 Bool.false 12779325 2147483648 35384261971 57279831343104 Bool.false 35311715043069919232 4110824671 17179869184 1021955820695 458238650744832 Bool.false 3056639630125301760 1423358745 8589934592 504595954993 229119325372416 (ep194 (BSN.head_sum_c_succ qz11 3 4 rfl rfl) (ep228 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep229 ep243) rfl rfl

noncomputable abbrev qz100 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable abbrev qz101 := (@HMul.hMul Real Real Real qz248 qz258 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep245 := @Enclosure.Complex.IsNear.of_eq qz78 (Complex.mk (@HMul.hMul Real Real Real qz0 qz100 (Real.cos qz101)) (@HMul.hMul Real Real Real qz0 qz100 (@Neg.neg Real Real.instNeg (Real.sin qz101)))) Bool.false 5447805363 17179869184 255634452941 458238650744832 Bool.true 2708750187 8589934592 31952582875 57279831343104 (BSN.cpow_neg_s_mk qz37 31718 1000 5 qz38 rfl)

noncomputable abbrev qz102 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def ep246 := @Enclosure.Real.IsNear.inv_image qz102 293085 131072 1 131072 29308 29309 65536 (@Enclosure.Real.IsNear.of_eq qz102 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5) qz88)) Bool.false 293085 131072 1 131072 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5) qz88)) Bool.false 293085 131072 1 131072 293085 131072 1 131072 (BSN.sqrt_enclosure 5 1 146542 146543 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep247 := nat_lit 141613827518379161815574079375

noncomputable def ep248 := nat_lit 29325128709309236875766211300

noncomputable def ep249 := BSN.log_dyadic_bound 2 3 15 14 ep247 65536 26673 ep248 57299708096576225280000 105476 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP 2) (BSN.artanhQ 3) 0 14 ep248 ep247 57299708096576225280000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep250 := nat_lit 1947741650938321805591236161950625

noncomputable def ep251 := BSN.cos_dyadic_bound_f 210079095 268435456 2 1 131072 53399 ep250 ep219 ep250 ep250 ep220 ep250 92939 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 210079095) qz304 0 1 ep250 ep219 ep250 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 210079095) qz305 0 1 ep250 ep220 ep250 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz103 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz314 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6690975) qz12)

noncomputable abbrev qz315 := (BSN.isNear_log_sfrac 5 1 105476 65536 1 26673 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 105476 65536 26673 rfl rfl rfl (ep249 rfl)))

noncomputable def ep252 := @Enclosure.Real.IsNear.cos_image qz101 qz314 Bool.false 6690975 131072 157 131072 Bool.false 92939 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz101 Bool.false 418185971 8192000 15859 13336500 6690975 131072 157 131072 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz103 31718 1000 0 1 105476 65536 1 26673 418185971 8192000 15859 13336500 qz90 qz315 rfl) rfl) (Enclosure.sfrac_false_div 6690975 131072) (BSN.cos_reduce0 qz314 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14783002126765134970880) qz67) 226375608064910080 72057594037927936 Bool.false 92939 131072 8 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q0 6690975 131072 226375608064910080 72057594037927936 8 14783002126765134970880 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 92939 131072 14783002126765134970880 18889465931478580854784 210079095 268435456 53399 53346 (ep251 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep253 := BSN.sin_dyadic_bound_f 210079095 268435456 2 1 131072 53399 ep250 ep223 ep250 ep250 ep224 ep250 92422 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 210079095) qz292 0 1 ep250 ep223 ep250 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 210079095) qz293 0 1 ep250 ep224 ep250 rfl rfl rfl rfl) rfl rfl

noncomputable def ep254 := @Enclosure.Real.IsNear.sin_image qz101 qz314 Bool.false 6690975 131072 157 131072 Bool.false 92422 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz101 Bool.false 418185971 8192000 15859 13336500 6690975 131072 157 131072 (@Enclosure.Real.IsNear.mulLit_ff qz37 qz103 31718 1000 0 1 105476 65536 1 26673 418185971 8192000 15859 13336500 qz90 qz315 rfl) rfl) (Enclosure.sfrac_false_div 6690975 131072) (BSN.sin_reduce0 qz314 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14783002126765134970880) qz67) 226375608064910080 72057594037927936 Bool.false 92422 131072 8 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q0 6690975 131072 226375608064910080 72057594037927936 8 14783002126765134970880 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 92422 131072 14783002126765134970880 18889465931478580854784 210079095 268435456 53399 53346 (ep253 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz316 := (@Enclosure.Real.IsNear.recentre' qz100 Bool.false 58617 131072 1 131072 58617 131072 1 131072 (ep246 rfl rfl) rfl)

noncomputable def ep255 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz100 (Real.cos qz101)) (@HMul.hMul Real Real Real qz0 qz100 (@Neg.neg Real Real.instNeg (Real.sin qz101))) Bool.false 5447805363 17179869184 255634452941 458238650744832 Bool.true 2708750187 8589934592 31952582875 57279831343104 (@Enclosure.Real.IsNear.mulLit_ff qz100 (Real.cos qz101) 58617 131072 1 131072 92939 131072 4318733 3496083456 5447805363 17179869184 255634452941 458238650744832 qz316 (@Enclosure.Real.IsNear.recentre' (Real.cos qz101) Bool.false 92939 131072 4318733 3496083456 92939 131072 4318733 3496083456 (ep252 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz100 (@Neg.neg Real Real.instNeg (Real.sin qz101)) 58617 131072 1 131072 46211 65536 4318733 3496083456 2708750187 8589934592 31952582875 57279831343104 qz316 (@Enclosure.Real.IsNear.neg (Real.sin qz101) Bool.false 46211 65536 4318733 3496083456 (@Enclosure.Real.IsNear.recentre' (Real.sin qz101) Bool.false 92422 131072 4318733 3496083456 46211 65536 4318733 3496083456 (ep254 rfl rfl) rfl)) rfl)

noncomputable def ep256 := @ep191 5447805363 17179869184 255634452941 458238650744832 Bool.true 2708750187 8589934592 31952582875 57279831343104 Bool.false 164216013562373472256 4779315017 8589934592 319397568409 114559662686208 Bool.true 11041428411896561664 642695721 4294967296 632406286493 229119325372416 (ep192 (BSN.head_sum_c_succ qz11 4 5 rfl rfl) (ep244 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep245 ep255) rfl rfl

noncomputable abbrev qz317 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz104 := (@Inv.inv Real Real.instInv (Real.sqrt qz317))

noncomputable abbrev qz105 := (@HMul.hMul Real Real Real qz248 qz258 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep257 := @Enclosure.Complex.IsNear.of_eq qz76 (Complex.mk (@HMul.hMul Real Real Real qz0 qz104 (Real.cos qz105)) (@HMul.hMul Real Real Real qz0 qz104 (@Neg.neg Real Real.instNeg (Real.sin qz105)))) Bool.false 3368213705 8589934592 118909910791 229119325372416 Bool.true 244032355 2147483648 14565644735 28639915671552 (BSN.cpow_neg_s_mk qz37 31718 1000 6 qz38 rfl)

noncomputable abbrev qz106 := (Real.sqrt qz317)

noncomputable abbrev qz318 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz88)

noncomputable def ep258 := @Enclosure.Real.IsNear.inv_image qz106 321059 131072 1 131072 26754 26756 65536 (@Enclosure.Real.IsNear.of_eq qz106 (Real.sqrt qz318) Bool.false 321059 131072 1 131072 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz318) Bool.false 321059 131072 1 131072 321059 131072 1 131072 (BSN.sqrt_enclosure 6 1 160529 160530 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep259 := BSN.log_dyadic_bound 2 10 4 3 105000000 65536 26673 1434560 960 26572 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz107 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep260 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz107 31718 1000 0 1 4034664351997175 2251799813685248 500000000026673 13336500000000000000 2559429678332927933 45035996273704960 7929500000423007107 6668250000000000000000 qz90 (BSN.isNear_log_sfrac 6 1 4034664351997175 2251799813685248 500000000026673 13336500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz318) Bool.false 4230652207559789772800 2361183241434822606848 1000000000053346 26673000000000000000 4034664351997175 2251799813685248 500000000026673 13336500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 26572 65536 24973259072661432 36028797018963968 26673 1000000000000000 rfl rfl rfl rfl (ep259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep261 := nat_lit 32874521795574016742648366158096

noncomputable def ep262 := BSN.cos_dyadic_bound_f 75720742 268435456 2 1 131072 53399 ep261 ep219 ep261 ep261 ep220 ep261 125891 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 75720742) qz304 0 1 ep261 ep219 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 75720742) qz305 0 1 ep261 ep220 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz319 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 931115) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep263 := @Enclosure.Real.IsNear.cos_image qz105 qz319 Bool.false 931115 16384 157 131072 Bool.false 125891 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz105 Bool.false 2559429678332927933 45035996273704960 7929500000423007107 6668250000000000000000 931115 16384 157 131072 (ep260 rfl) rfl) (Enclosure.sfrac_false_div 931115 16384) (BSN.cos_reduce0 qz319 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 666046693973017231360) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 125891 131072 9 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q0 931115 16384 226375608064910080 72057594037927936 9 666046693973017231360 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 125891 131072 666046693973017231360 2361183241434822606848 75720742 268435456 53399 53346 (ep262 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep264 := BSN.sin_dyadic_bound_f 75720742 268435456 2 1 131072 53399 ep261 ep223 ep261 ep261 ep224 ep261 36484 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 75720742) qz292 0 1 ep261 ep223 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 75720742) qz293 0 1 ep261 ep224 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable def ep265 := @Enclosure.Real.IsNear.sin_image qz105 qz319 Bool.false 931115 16384 157 131072 Bool.false 36484 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz105 Bool.false 2559429678332927933 45035996273704960 7929500000423007107 6668250000000000000000 931115 16384 157 131072 (ep260 rfl) rfl) (Enclosure.sfrac_false_div 931115 16384) (BSN.sin_reduce0 qz319 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 666046693973017231360) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 36484 131072 9 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q0 931115 16384 226375608064910080 72057594037927936 9 666046693973017231360 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 36484 131072 666046693973017231360 2361183241434822606848 75720742 268435456 53399 53346 (ep264 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz320 := (@Enclosure.Real.IsNear.recentre' qz104 Bool.false 53510 131072 2 131072 26755 65536 1 65536 (ep258 rfl rfl) rfl)

noncomputable def ep266 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz104 (Real.cos qz105)) (@HMul.hMul Real Real Real qz0 qz104 (@Neg.neg Real Real.instNeg (Real.sin qz105))) Bool.false 3368213705 8589934592 118909910791 229119325372416 Bool.true 244032355 2147483648 14565644735 28639915671552 (@Enclosure.Real.IsNear.mulLit_ff qz104 (Real.cos qz105) 26755 65536 1 65536 125891 131072 4318733 3496083456 3368213705 8589934592 118909910791 229119325372416 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz105) Bool.false 125891 131072 4318733 3496083456 125891 131072 4318733 3496083456 (ep263 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz104 (@Neg.neg Real Real.instNeg (Real.sin qz105)) 26755 65536 1 65536 9121 32768 4318733 3496083456 244032355 2147483648 14565644735 28639915671552 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz105) Bool.false 9121 32768 4318733 3496083456 (@Enclosure.Real.IsNear.recentre' (Real.sin qz105) Bool.false 36484 131072 4318733 3496083456 9121 32768 4318733 3496083456 (ep265 rfl rfl) rfl)) rfl)

noncomputable def ep267 := @ep189 3368213705 8589934592 118909910791 229119325372416 Bool.true 244032355 2147483648 14565644735 28639915671552 Bool.false 69986738808421351424 4073764361 4294967296 252568349203 76373108457472 Bool.true 2428289535377932288 1130760431 4294967296 249643814791 76373108457472 (ep190 (BSN.head_sum_c_succ qz11 5 6 rfl rfl) (ep256 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep257 ep266) rfl rfl

noncomputable def ep268 := @Enclosure.Complex.IsNear.mul qz70 (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 1403587117426510739651 45380435479564910592000 35813726951489508601471 ep53 Bool.false

noncomputable abbrev qz108 := (Complex.re qz296)

noncomputable abbrev qz109 := (Complex.im qz296)

noncomputable def ep269 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz108 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz109 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 20358733780286600035 242028989224346189824 1525537704764491574225

noncomputable def ep270 := nat_lit 6455639229580985921175552

noncomputable def ep271 := nat_lit 67246241974801936678912000

noncomputable def ep272 := nat_lit 679417542638104195992125399213435779022848

noncomputable def ep273 := @Enclosure.Real.IsNear.mulLit_ff qz108 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2876003673 17179869184 71835705985 152746216914944 21236482385

noncomputable abbrev qz110 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable abbrev qz321 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz401 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable abbrev qz111 := (Real.cos qz321)

noncomputable abbrev qz112 := (@Neg.neg Real Real.instNeg (Real.sin qz321))

noncomputable def ep274 := @Enclosure.Complex.IsNear.of_eq qz70 (Complex.mk (@HMul.hMul Real Real Real qz0 qz110 qz111) (@HMul.hMul Real Real Real qz0 qz110 qz112)) Bool.false 2876003673 17179869184 71835705985 152746216914944 Bool.false 2910880537 8589934592 9045546717 19093277114368 (BSN.cpow_neg_s_mk qz37 31718 1000 7 qz38 rfl)

noncomputable abbrev qz113 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable abbrev qz114 := (@HDiv.hDiv Real Real Real qz251 (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1))

noncomputable def ep275 := @Enclosure.Real.IsNear.inv_image qz113 346783 131072 1 131072 24770 24771 65536 (@Enclosure.Real.IsNear.of_eq qz113 (Real.sqrt qz114) Bool.false 346783 131072 1 131072 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz114) Bool.false 346783 131072 1 131072 346783 131072 1 131072 (BSN.sqrt_enclosure 7 1 173391 173392 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep276 := BSN.log_dyadic_bound 3 11 5 4 202569142545 65536 26673 5259111624 688905 36674 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz322 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz115 := qz322

noncomputable def ep277 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz115 31718 1000 0 1 4381766428990711 2251799813685248 500000000026673 13336500000000000000 69490433797363685749 1125899906842624000 7929500000423007107 6668250000000000000000 qz90 (BSN.isNear_log_sfrac 7 1 4381766428990711 2251799813685248 500000000026673 13336500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz114) Bool.false 4594615115045363777536 2361183241434822606848 1000000000053346 26673000000000000000 4381766428990711 2251799813685248 500000000026673 13336500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 36674 65536 24973259072661432 36028797018963968 26673 1000000000000000 rfl rfl rfl rfl (ep276 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep278 := nat_lit 230157235016438929913175931950625

noncomputable def ep279 := BSN.sin_dyadic_bound_f 123170345 268435456 2 1 131072 53399 ep278 ep223 ep278 ep278 ep224 ep278 58053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 123170345) qz292 0 1 ep278 ep223 ep278 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 123170345) qz293 0 1 ep278 ep224 ep278 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz116 := qz321

noncomputable abbrev qz323 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8089751) qz12)

noncomputable def ep280 := @Enclosure.Real.IsNear.cos_image qz116 qz323 Bool.false 8089751 131072 157 131072 Bool.false 58053 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 69490433797363685749 1125899906842624000 7929500000423007107 6668250000000000000000 8089751 131072 157 131072 (ep277 rfl) rfl) (Enclosure.sfrac_false_div 8089751 131072) (BSN.cos_reduce3 qz323 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8667342540771250143232) qz67) 226375608064910080 72057594037927936 Bool.false 58053 131072 9 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q3 8089751 131072 226375608064910080 72057594037927936 9 8667342540771250143232 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 58053 131072 8667342540771250143232 18889465931478580854784 123170345 268435456 53399 53346 (ep279 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep281 := BSN.cos_dyadic_bound_f 123170345 268435456 2 1 131072 53399 ep278 ep219 ep278 ep278 ep220 ep278 117514 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 123170345) qz304 0 1 ep278 ep219 ep278 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 123170345) qz305 0 1 ep278 ep220 ep278 rfl rfl rfl rfl) rfl rfl

noncomputable def ep282 := @Enclosure.Real.IsNear.sin_image qz116 qz323 Bool.false 8089751 131072 157 131072 Bool.true 117514 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 69490433797363685749 1125899906842624000 7929500000423007107 6668250000000000000000 8089751 131072 157 131072 (ep277 rfl) rfl) (Enclosure.sfrac_false_div 8089751 131072) (BSN.sin_reduce3 qz323 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8667342540771250143232) qz67) 226375608064910080 72057594037927936 Bool.false 117514 131072 9 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q3 8089751 131072 226375608064910080 72057594037927936 9 8667342540771250143232 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 117514 131072 8667342540771250143232 18889465931478580854784 123170345 268435456 53399 53346 (ep281 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz117 := (Real.sin qz321)

noncomputable abbrev qz324 := (@Enclosure.Real.IsNear.recentre' qz110 Bool.false 49541 131072 1 131072 49541 131072 1 131072 (ep275 rfl rfl) rfl)

noncomputable def ep283 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz110 qz111) (@HMul.hMul Real Real Real qz0 qz110 qz112) Bool.false 2876003673 17179869184 71835705985 152746216914944 Bool.false 2910880537 8589934592 9045546717 19093277114368 (@Enclosure.Real.IsNear.mulLit_ff qz110 qz111 49541 131072 1 131072 58053 131072 4318733 3496083456 2876003673 17179869184 71835705985 152746216914944 qz324 (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 58053 131072 4318733 3496083456 58053 131072 4318733 3496083456 (ep280 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz110 qz112 49541 131072 1 131072 58757 65536 4318733 3496083456 2910880537 8589934592 9045546717 19093277114368 qz324 (@Enclosure.Real.IsNear.neg qz117 Bool.true 58757 65536 4318733 3496083456 (@Enclosure.Real.IsNear.recentre' qz117 Bool.true 117514 131072 4318733 3496083456 58757 65536 4318733 3496083456 (ep282 rfl rfl) rfl)) rfl)

noncomputable def ep284 := @ep273 42263824008 0 1 20358733780286600035 242028989224346189824 1525537704764491574225 ep270 (@Enclosure.Complex.IsNear.re_isNear qz70 Bool.false 2876003673 17179869184 71835705985 152746216914944 Bool.false 2910880537 8589934592 9045546717 19093277114368 (ep274 ep283))

noncomputable def ep285 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 21236482385 42263824008 0 1 Bool.false

noncomputable def ep286 := @Enclosure.Complex.IsNear.addLitP qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) Bool.false 249820381 503140762 0 1 Bool.true 55506500

noncomputable def ep287 := @ep286 251570381 0 1 Bool.false 1 168 0 1 Bool.false 15859 42000 0 1 Bool.false 42472964770 21236482385 42263824008 0 1 Bool.false 1658381672279 1658381672279 10565956002000 0 1

noncomputable abbrev qz118 := (@HDiv.hDiv Complex Complex Complex qz264 qz297 (@HSub.hSub Complex Complex Complex qz254 qz259 (1 : Complex)))

noncomputable def ep288 := @Enclosure.Complex.IsNear.addLitP qz118 qz41 Bool.true 14000000 4025126096 0 1 Bool.true 888104000 4025126096 0 1

noncomputable def ep289 := @Enclosure.Complex.IsNear.of_eq qz118 (Complex.mk (Enclosure.sfrac Bool.true 14000000 4025126096) (Enclosure.sfrac Bool.true 888104000 4025126096)) Bool.true 14000000 4025126096 0 1 Bool.true 888104000 4025126096 0 1

noncomputable def ep290 := @ep288 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 3997126096 249820381 503140762 0 1 Bool.true 888104000 55506500 251570381 0 1 (ep289 (BSN.N_div_s_sub_one_mk qz37 31718 1000 7 qz38 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 14000000 4025126096) (Enclosure.sfrac Bool.true 888104000 4025126096) Bool.true 14000000 4025126096 0 1 Bool.true 888104000 4025126096 0 1 (Enclosure.Real.IsNear.const Bool.true 14000000 4025126096) (Enclosure.Real.IsNear.const Bool.true 888104000 4025126096))) qz43 rfl

noncomputable abbrev qz119 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz325 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz406 (@Nat.cast Complex Complex.instNatCast 7) 1))

noncomputable abbrev qz120 := qz325

noncomputable def ep291 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz120)) Bool.false 1 168 0 1

noncomputable def ep292 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz120) Bool.false 0 1 0 1 Bool.false

noncomputable def ep293 := @ep292 0 1 0 1 Bool.false 1 168 0 1 Bool.false 15859 42000 0 1 Bool.false 1 1 168 0 1 Bool.false 15859 15859 42000 0

noncomputable def ep294 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (Complex.mk qz44 qz44) Bool.false 0 1 0 1 Bool.false

noncomputable def ep295 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz120 Bool.false 1 168 0 1 Bool.false 15859 42000 0 1

noncomputable abbrev qz121 := (Complex.re qz325)

noncomputable abbrev qz122 := (Complex.im qz325)

noncomputable def ep296 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz121) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz122) 1 168 0 1 0 1 0

noncomputable def ep297 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz121 1 24 0 1 1 7 0 1 1

noncomputable def ep298 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep299 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep300 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz44) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow05.d6 rfl) qz283

noncomputable def ep301 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz11 Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 (BSN.ascPochhammer_one_eval qz11)

noncomputable def ep302 := ep301 (@Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk qz32 qz37) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 (BSN.s_crit_mk qz37 Bool.false 31718 1000 qz38) (@Enclosure.Complex.IsNear.mk qz32 qz37 Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 qz33 qz90))

noncomputable def ep303 := @ep299 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep300) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep302)

noncomputable def ep304 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 31718 1000 0 1 0 1 0

noncomputable def ep305 := @ep304 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep300) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep302)

noncomputable def ep306 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) 15859 6000 0 1 0 1 0 1 15859

noncomputable def ep307 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 31718 1000 0 1 15859 6000 0

noncomputable def ep308 := @ep307 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep300) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep302)

noncomputable def ep309 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep310 := @ep309 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep300) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep302)

noncomputable def ep311 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 15859 6000 0 1 (@ep298 1 24 0 1 (ep303 rfl) (ep305 rfl) rfl rfl) (@ep306 15859 6000 0 1 (ep308 rfl) (ep310 rfl) rfl rfl)

noncomputable def ep312 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 15859 6000 0 1 ep311

noncomputable abbrev qz123 := (@Enclosure.Complex.IsNear.of_eq qz325 (Complex.mk (Enclosure.sfrac Bool.false 1 7) qz279) Bool.false 1 7 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 7 1 7 EMRow05.d7 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 7) qz279 Bool.false 1 7 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 7) qz280))

noncomputable def ep313 := @ep297 168 0 1 ep312 (@Enclosure.Complex.IsNear.re_isNear qz120 Bool.false 1 7 0 1 Bool.false 0 1 0 1 qz123)

noncomputable def ep314 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz122 15859 6000 0 1 0 1 0 1 0

noncomputable def ep315 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 15859 6000 0 1 ep311

noncomputable def ep316 := @ep314 1 0 1 ep315 (@Enclosure.Complex.IsNear.im_isNear qz120 Bool.false 1 7 0 1 Bool.false 0 1 0 1 qz123)

noncomputable def ep317 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz122) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz121) 0 1 0 1 15859 42000 0

noncomputable def ep318 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz122 1 24 0 1 0 1 0 1 0

noncomputable def ep319 := @ep318 1 0 1 ep312 (@Enclosure.Complex.IsNear.im_isNear qz120 Bool.false 1 7 0 1 Bool.false 0 1 0 1 qz123)

noncomputable def ep320 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)))) qz121 15859 6000 0 1 1 7 0 1 15859

noncomputable def ep321 := @ep320 42000 0 1 ep315 (@Enclosure.Complex.IsNear.re_isNear qz120 Bool.false 1 7 0 1 Bool.false 0 1 0 1 qz123)

noncomputable def ep322 := @ep293 1 (@ep294 0 1 0 1 (BSN.bern_sum_base qz11 7) qz61) (ep295 (@ep296 1 1 1 168 0 1 (ep313 rfl) (ep316 rfl) rfl rfl) (@ep317 1 15859 15859 42000 0 1 (ep319 rfl) (ep321 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep323 := ep287 (ep290 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep291 Bool.false 15859 42000 0 1 (BSN.bern_sum_succ qz11 7 0 1 1 rfl rfl) (ep322 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep324 := @Enclosure.Real.IsNear.mulLit_ff qz109 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2910880537 8589934592 9045546717 19093277114368 1658381672279

noncomputable def ep325 := @ep324 10565956002000 0 1 4827350932754453533823 90760870959129821184000 5000322963738759452681 ep271 (@Enclosure.Complex.IsNear.im_isNear qz70 Bool.false 2876003673 17179869184 71835705985 152746216914944 Bool.false 2910880537 8589934592 9045546717 19093277114368 (ep274 ep283))

noncomputable def ep326 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 21236482385 42263824008 0 1 Bool.false

noncomputable def ep327 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz108 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz109 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 1589837260236762093589 60507247306086547456000 23826203644149373777963

noncomputable def ep328 := nat_lit 4317548289973545996674277917166593065877504

noncomputable def ep329 := @Enclosure.Real.IsNear.mulLit_ff qz108 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2876003673 17179869184 71835705985 152746216914944 1658381672279

noncomputable def ep330 := @ep329 10565956002000 0 1 1589837260236762093589 60507247306086547456000 23826203644149373777963 ep181 (@Enclosure.Complex.IsNear.re_isNear qz70 Bool.false 2876003673 17179869184 71835705985 152746216914944 Bool.false 2910880537 8589934592 9045546717 19093277114368 (ep274 ep283))

noncomputable def ep331 := @Enclosure.Real.IsNear.mulLit_ff qz109 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz71 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz74 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 2910880537 8589934592 9045546717 19093277114368 21236482385

noncomputable def ep332 := @ep331 42263824008 0 1 61816863248839840745 363043483836519284736 64031864506088360015 268984967899207746715648 (@Enclosure.Complex.IsNear.im_isNear qz70 Bool.false 2876003673 17179869184 71835705985 152746216914944 Bool.false 2910880537 8589934592 9045546717 19093277114368 (ep274 ep283))

noncomputable abbrev qz326 := (ep323 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep333 := @ep268 35677943405130206653267 181521741918259642368000 100664441051455405795963 ep181 (@ep269 ep270 4827350932754453533823 90760870959129821184000 5000322963738759452681 ep271 ep272 1403587117426510739651 45380435479564910592000 35813726951489508601471 ep53 (ep284 (@ep285 1658381672279 10565956002000 0 1 qz326) rfl) (ep325 (@ep326 1658381672279 10565956002000 0 1 qz326) rfl) rfl rfl) (@ep327 ep181 61816863248839840745 363043483836519284736 64031864506088360015 268984967899207746715648 ep328 35677943405130206653267 181521741918259642368000 100664441051455405795963 ep181 (ep330 (@ep326 1658381672279 10565956002000 0 1 qz326) rfl) (ep332 (@ep285 1658381672279 10565956002000 0 1 qz326) rfl) rfl rfl)

noncomputable def ep334 := @ep186 1155754666352712536028763 ep181 (@ep187 76373108457472 (BSN.head_sum_c_eq qz11 7) (ep188 (BSN.head_sum_c_succ qz11 6 7 rfl rfl) (ep267 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep333 rfl rfl rfl

noncomputable def ep335 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz11 1 7) Bool.false 44446802118268155461651 45380435479564910592000 417046021976728046659471 ep53 Bool.true 12112316445864020794733 181521741918259642368000 1155754666352712536028763 ep181 (@ep182 ep53 Bool.true 12112316445864020794733 181521741918259642368000 1155754666352712536028763 ep181 (BSN.zetaApproximant_eq_folded' qz11 1 7 rfl) (ep334 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep336 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) (Complex.im (zetaApproximant qz11 1 7)) 3 131072 1319167

noncomputable def ep337 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10)) Bool.false 3 131072 1319167

noncomputable def ep338 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) qz260 Bool.false 1235321 131072 47

noncomputable def ep339 := nat_lit 276725497849192423434147532591529535323076476297685447808087986659205376

noncomputable def ep340 := nat_lit 828178247214034137693214589133981886678785447809198054012084764831457536

noncomputable def ep341 := BSN.cos_dyadic_bound_f 421650266 268435456 3 2 131072 53399 ep339 ep208 ep176 ep340 ep210 ep176 3 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 421650266) qz304 0 2 ep339 ep208 ep176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 421650266) qz305 0 2 ep340 ep210 ep176 rfl rfl rfl rfl) rfl rfl

noncomputable def ep342 := @ep338 65536 Bool.false 3 131072 1 26673 (@ep57 1235321 131072 47 65536 ep173 rfl) (Enclosure.sfrac_false_div 1235321 131072) (BSN.sin_reduce1 qz260 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29670999747634881626112) qz67) 226375608064910080 72057594037927936 Bool.false 3 131072 1 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q1 1235321 131072 226375608064910080 72057594037927936 1 29670999747634881626112 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 3 131072 29670999747634881626112 18889465931478580854784 421650266 268435456 53399 53346 (ep341 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep343 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz11 1 7) Bool.false 44446802118268155461651 45380435479564910592000 417046021976728046659471 ep53 Bool.true 12112316445864020794733 181521741918259642368000 1155754666352712536028763 ep181 (@ep182 ep53 Bool.true 12112316445864020794733 181521741918259642368000 1155754666352712536028763 ep181 (BSN.zetaApproximant_eq_folded' qz11 1 7 rfl) (ep334 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow05.d8 : Enclosure.Real.IsNear (hardyZApproximantEM 1 7 qz37) Bool.true ep38 ep39 ep40 ep41 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 7 qz37) ep42 Bool.true ep38 ep39 ep40 ep41 (@Eq.refl Real ep42) (@ep43 Bool.true ep38 ep39 ep40 ep41 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz7 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz9 (@Nat.cast Complex Complex.instNatCast j))))) qz10) (zetaApproximant qz11 1 7)) (@ep45 ep46 ep47 ep48 12112316445864020794733 ep49 ep50 ep41 ep51 ep38 ep39 ep40 ep41 (@ep52 1748041728 44446802118268155461651 45380435479564910592000 417046021976728046659471 ep53 ep44 ep46 ep47 ep48 (@ep54 1748041728 131071 131072 1319167 1748041728 (ep180 rfl rfl) rfl) ep335 rfl) (@ep336 1748041728 12112316445864020794733 181521741918259642368000 1155754666352712536028763 ep181 12112316445864020794733 ep49 ep50 ep41 (@ep337 1748041728 3 131072 1319167 1748041728 (ep342 rfl rfl) rfl) ep343 rfl) rfl rfl))

theorem EMRow05.d9 : @Eq Nat (Nat.pow 8 1) 8 := @Eq.refl Nat 8

noncomputable def ep344 := nat_lit 136428812447130271690862832843

noncomputable def ep345 := nat_lit 45329922406348602738737152000

noncomputable def ep346 := nat_lit 226213129636080499835191156412455273

noncomputable def ep347 := nat_lit 32249924747649816219121013602910208000

noncomputable abbrev qz425 := (Enclosure.sfrac Bool.false 35467 1000)

noncomputable abbrev qz411 := (@HAdd.hAdd Complex Complex Complex qz419 (@HAdd.hAdd Complex Complex Complex qz419 qz420 (@HMul.hMul Complex Complex Complex qz418 Complex.I (@HDiv.hDiv Complex Complex Complex qz421 (↑qz425) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz327 := qz411

noncomputable abbrev qz124 := (Complex.Stirling.logGammaStirling 1 qz327)

noncomputable abbrev qz412 := (@HAdd.hAdd Complex Complex Complex qz419 qz420 (@HMul.hMul Complex Complex Complex qz418 Complex.I (@HDiv.hDiv Complex Complex Complex qz421 (↑qz425) (2 : Complex))))

noncomputable abbrev qz328 := qz412

noncomputable abbrev qz125 := qz328

noncomputable abbrev qz413 := qz425

noncomputable abbrev qz329 := qz413

noncomputable abbrev qz126 := (@HMul.hMul Real Real Real qz248 (@HDiv.hDiv Real Real Real qz251 qz329 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz426 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 35467 1000)))

noncomputable abbrev qz414 := qz426

noncomputable abbrev qz330 := qz414

noncomputable abbrev qz127 := qz330

noncomputable def ep348 := Complex.re (@HMul.hMul Complex Complex Complex qz4 (Complex.exp (@HMul.hMul Complex Complex Complex qz4 Complex.I ↑(@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))))) qz126))) (zetaApproximant qz127 1 8))

noncomputable def ep349 := @Enclosure.Real.IsNear.of_eq ep348 (@HSub.hSub Real Real Real qz5 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))))) qz126)) (Complex.re (zetaApproximant qz127 1 8))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))))) qz126)) (Complex.im (zetaApproximant qz127 1 8))))

noncomputable def ep350 := nat_lit 136428957495253353328929073193

noncomputable def ep351 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))))) qz126)) (Complex.re (zetaApproximant qz127 1 8))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))))) qz126)) (Complex.im (zetaApproximant qz127 1 8))) ep350

noncomputable def ep352 := nat_lit 225514512332484094755884305718901941

noncomputable def ep353 := nat_lit 906598448126972054774743040

noncomputable def ep354 := nat_lit 174654325899101269826712673388333

noncomputable def ep355 := nat_lit 8062481186912454054780253400727552000

noncomputable def ep356 := nat_lit 123686149644374033015644749937393680548139380861797662720

noncomputable def ep357 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))))) qz126)) (Complex.re (zetaApproximant qz127 1 8)) 131071 131072 2878391

noncomputable def ep358 := nat_lit 20806436604910635444267239

noncomputable def ep359 := nat_lit 4612293321016450045968384000

noncomputable def ep360 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))))) qz126)) Bool.false 131071 131072 2878391

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1647079) qz12)

noncomputable def ep361 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))))) qz126) qz331 Bool.false 1647079 131072 103

noncomputable def ep362 := nat_lit 145670144000000000000000000

noncomputable def ep363 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))))) qz126) Bool.false 84889846038812529199 6755399441055744000 113289620702103900248871 ep362

noncomputable def ep364 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))))) qz126 222024877677803311663 6755399441055744000 34455346452103900248871 ep362 2660769807 131072000

noncomputable def ep365 := nat_lit 11126681899999235827171328000

noncomputable def ep366 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 6227548056493499531 225179981368524800 41825575750868002728859 ep56 Bool.false 222024877677803311663 6755399441055744000

noncomputable def ep367 := @Enclosure.Complex.IsNear.subLitP qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 4931978906027352731 225179981368524800 39777575749993981864859 ep56 Bool.false 242677047478287991663 6755399441055744000 86982039355874690314613

noncomputable def ep368 := nat_lit 437010432000000000000000000

noncomputable def ep369 := nat_lit 3505797888331997632559361317404672

noncomputable def ep370 := nat_lit 62494447273545934354060435341180928

noncomputable abbrev qz332 := (@HSub.hSub Complex Complex Complex qz397 qz411 qz403)

noncomputable abbrev qz333 := (Complex.log qz411)

noncomputable abbrev qz128 := (@HSub.hSub Complex Complex Complex qz254 (@HMul.hMul Complex Complex Complex qz253 qz332 qz333) qz327)

noncomputable abbrev qz129 := qz327

noncomputable def ep371 := @Enclosure.Complex.IsNear.of_eq qz124 (@HAdd.hAdd Complex Complex Complex qz8 (@HAdd.hAdd Complex Complex Complex qz8 qz128 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz129 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k)))))) Bool.true 4931978906027352731

noncomputable def ep372 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz8 qz128 qz14) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz129 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) Bool.true 4932111037298827931 225179981368524800

noncomputable def ep373 := nat_lit 5295672026487334315275321344

noncomputable def ep374 := nat_lit 130286247801135774282763206656000

noncomputable def ep375 := @ep372 38844990724349105291 106692000000000000000000 Bool.false 80902763158996910373 2251799813685248000 5308375001915361457 26673000000000000000000 Bool.false 630051 1073741824 3 1073741824 Bool.true 7448672939 1610612736000 35467 1610612736000 Bool.true ep373 4931978906027352731 225179981368524800 39777575749993981864859 ep56 Bool.false ep374

noncomputable def ep376 := @Enclosure.Complex.IsNear.addLitP qz128 qz14 Bool.true 5139035689672434331 225179981368524800 37217000001692855291 106692000000000000000000

noncomputable def ep377 := @ep376 Bool.false 80902763158996910373 2251799813685248000 5308375001915361457 26673000000000000000000 Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 Bool.true 323230828940415987286016 4932111037298827931 225179981368524800 38844990724349105291 106692000000000000000000 Bool.false 80902763158996910373 80902763158996910373 2251799813685248000

noncomputable abbrev qz130 := (@HMul.hMul Complex Complex Complex qz253 qz332 qz333)

noncomputable def ep378 := @Enclosure.Complex.IsNear.subLitP qz130 qz129 Bool.true 4632380731593253531 225179981368524800 37217000001692855291 106692000000000000000000 Bool.false 120835055154984255781

noncomputable def ep379 := @ep378 2251799813685248000 5308375001915361457 26673000000000000000000 Bool.false 9000 4000 0 1 Bool.false 70934 4000 0 1 Bool.true 20556142758689737324000 5139035689672434331 225179981368524800 37217000001692855291 106692000000000000000000 Bool.false 323611052635987641492000 80902763158996910373 2251799813685248000 5308375001915361457 26673000000000000000000

noncomputable abbrev qz131 := qz332

noncomputable abbrev qz132 := qz333

noncomputable def ep380 := @Enclosure.Complex.IsNear.mul qz131 qz132 Bool.true 4632380731593253531 225179981368524800 37217000001692855291 106692000000000000000000 Bool.false 120835055154984255781 2251799813685248000 5308375001915361457

noncomputable abbrev qz133 := (Complex.re qz332)

noncomputable abbrev qz134 := (Complex.re qz333)

noncomputable abbrev qz135 := (Complex.im qz332)

noncomputable abbrev qz136 := (Complex.im qz333)

noncomputable def ep381 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz133 qz134) (@HMul.hMul Real Real Real qz0 qz135 qz136) 22725253871160001 4503599627370496 437500000186711 26673000000000000000 5768643425151253581 225179981368524800

noncomputable def ep382 := nat_lit 20862388136641642249460406997221376

noncomputable def ep383 := @Enclosure.Real.IsNear.mulLit_ff qz133 qz134 7000 4000 0 1 3246464838737143 1125899906842624 62500000026673 6668250000000000000

noncomputable def ep384 := @Enclosure.Complex.IsNear.re_isNear qz131 Bool.false 7000 4000 0 1 Bool.false 70934 4000 0 1

noncomputable abbrev qz334 := (Enclosure.sfrac Bool.false 70934 4000)

noncomputable abbrev qz137 := qz334

noncomputable def ep385 := @Enclosure.Complex.IsNear.of_eq qz131 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz137) Bool.false 7000 4000 0 1 Bool.false 70934 4000 0

noncomputable abbrev qz138 := (Complex.log (Complex.mk qz271 qz334))

noncomputable def ep386 := @Enclosure.Complex.IsNear.of_eq qz132 qz138 Bool.false 3246464838737143 1125899906842624 62500000026673 6668250000000000000 Bool.false 813240959927715 562949953421312 1000000000026673 53346000000000000000

noncomputable def ep387 := nat_lit 107862826721941779351241307685961536925440

noncomputable def ep388 := nat_lit 441420520907722545532371005053235693568

noncomputable def ep389 := nat_lit 3204623149525941918432053123443385088

noncomputable def ep390 := BSN.log_dyadic_bound 1016632356 9208632356 3 2 ep387 131072 53346 ep388 ep389 29059 10225264712 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1016632356) (BSN.artanhQ 9208632356) 0 2 ep388 ep387 ep389 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz335 := (Real.log (Enclosure.sfrac Bool.false 5112632356 16000000))

noncomputable def ep391 := @Enclosure.Real.IsNear.mulLit_ff qz32 qz335 1 2 0 1 3246464838737143 562949953421312 62500000026673 3334125000000000000 3246464838737143 1125899906842624 62500000026673 6668250000000000000 qz33 (BSN.isNear_log_sfrac 5112632356 16000000 3246464838737143 562949953421312 62500000026673 3334125000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5112632356) qz273)) Bool.false 27233320917949107666944 4722366482869645213696 1000000000426768 53346000000000000000 3246464838737143 562949953421312 62500000026673 3334125000000000000 (BSN.log_rat_reduce_isNear 5112632356 16000000 8 10225264712 8192000000 29059 131072 24973259072661432 36028797018963968 53346 1000000000000000 rfl rfl rfl rfl (ep390 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep392 := BSN.arctan_dyadic_bound_f 9000 70934 1 0 131072 53346 0 1 1 0 1 1 16540 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 70934) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 70934) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz336 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 70934)))

noncomputable def ep393 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz336 884279719003555 562949953421312 1 2000000000000000 16540 131072 1 53346 106593119099645460480 813240959927715 562949953421312 1000000000026673 53346000000000000000 qz35 (ep392 rfl) rfl rfl

noncomputable abbrev qz139 := (Complex.mk qz271 qz334)

noncomputable abbrev qz140 := qz329

noncomputable abbrev qz337 := (@Eq.refl Real qz413)

noncomputable abbrev qz141 := qz337

noncomputable abbrev qz338 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 70934) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep394 := @Enclosure.Complex.IsNear.re_isNear qz132 Bool.false 3246464838737143 1125899906842624 62500000026673 6668250000000000000 Bool.false 813240959927715 562949953421312 1000000000026673 53346000000000000000 (ep386 (@congrArg Complex Complex qz129 qz139 Complex.log (BSN.w_shift_mk qz140 Bool.false 35467 1000 2 qz141 rfl)) (@Enclosure.Complex.IsNear.of_parts qz138 Bool.false 3246464838737143 1125899906842624 62500000026673 6668250000000000000 Bool.false 813240959927715 562949953421312 1000000000026673 53346000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz138) (@HMul.hMul Real Real Real qz0 qz32 qz335) Bool.false 3246464838737143 1125899906842624 62500000026673 6668250000000000000 (Enclosure.clog_re_eq 9000 70934 4000 5112632356 16000000 rfl rfl rfl) (ep391 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz138) qz338 Bool.false 813240959927715 562949953421312 1000000000026673 53346000000000000000 (Enclosure.clog_im_eq 9000 70934 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz338 (@HSub.hSub Real Real Real qz5 qz34 qz336) Bool.false 813240959927715 562949953421312 1000000000026673 53346000000000000000 (BSN.arctan_recip 70934 9000 rfl rfl) ep393))))

noncomputable def ep395 := @Enclosure.Real.IsNear.mulLit_ff qz135 qz136 70934 4000 0 1 813240959927715 562949953421312 1000000000026673 53346000000000000000

noncomputable def ep396 := @Enclosure.Complex.IsNear.im_isNear qz131 Bool.false 7000 4000 0 1 Bool.false 70934 4000 0 1

noncomputable def ep397 := @Enclosure.Complex.IsNear.im_isNear qz132 Bool.false 3246464838737143 1125899906842624 62500000026673 6668250000000000000 Bool.false 813240959927715 562949953421312 1000000000026673 53346000000000000000 (ep386 (@congrArg Complex Complex qz129 qz139 Complex.log (BSN.w_shift_mk qz140 Bool.false 35467 1000 2 qz141 rfl)) (@Enclosure.Complex.IsNear.of_parts qz138 Bool.false 3246464838737143 1125899906842624 62500000026673 6668250000000000000 Bool.false 813240959927715 562949953421312 1000000000026673 53346000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz138) (@HMul.hMul Real Real Real qz0 qz32 qz335) Bool.false 3246464838737143 1125899906842624 62500000026673 6668250000000000000 (Enclosure.clog_re_eq 9000 70934 4000 5112632356 16000000 rfl rfl rfl) (ep391 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz138) qz338 Bool.false 813240959927715 562949953421312 1000000000026673 53346000000000000000 (Enclosure.clog_im_eq 9000 70934 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz338 (@HSub.hSub Real Real Real qz5 qz34 qz336) Bool.false 813240959927715 562949953421312 1000000000026673 53346000000000000000 (BSN.arctan_recip 70934 9000 rfl rfl) ep393))))

noncomputable abbrev qz339 := (Enclosure.Real.IsNear.const Bool.false 70934 4000)

noncomputable abbrev qz142 := (@ep385 1 (BSN.w_sub_half_mk qz329 Bool.false 35467 1000 2 qz337 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz334 Bool.false 7000 4000 0 1 Bool.false 70934 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz339))

noncomputable def ep398 := @ep381 35467000000946011291 106692000000000000000000 ep382 4632380731593253531 225179981368524800 37217000001692855291 106692000000000000000000 (@ep383 22725253871160001 4503599627370496 437500000186711 26673000000000000000 (ep384 qz142) ep394 rfl) (@ep395 5768643425151253581 225179981368524800 35467000000946011291 106692000000000000000000 (ep396 qz142) ep397 rfl) rfl

noncomputable def ep399 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz133 qz136) (@HMul.hMul Real Real Real qz0 qz135 qz134) 5692686719494005 2251799813685248 7000000000186711 213384000000000000000 115142368435490250781 2251799813685248000

noncomputable def ep400 := nat_lit 272096354684640213060442620258418688

noncomputable def ep401 := @Enclosure.Real.IsNear.mulLit_ff qz133 qz136 7000 4000 0 1 813240959927715 562949953421312 1000000000026673 53346000000000000000

noncomputable def ep402 := @Enclosure.Real.IsNear.mulLit_ff qz135 qz134 70934 4000 0 1 3246464838737143 1125899906842624 62500000026673 6668250000000000000

noncomputable def ep403 := @ep399 2216687500946011291 13336500000000000000000 ep400 120835055154984255781 2251799813685248000 5308375001915361457 26673000000000000000000 (@ep401 5692686719494005 2251799813685248 7000000000186711 213384000000000000000 (ep384 qz142) ep397 rfl) (@ep402 115142368435490250781 2251799813685248000 2216687500946011291 13336500000000000000000 (ep396 qz142) ep394 rfl) rfl

noncomputable def ep404 := @Enclosure.Complex.IsNear.of_eq qz129 qz139 Bool.false 9000 4000 0 1 Bool.false 70934 4000 0 1 (BSN.w_shift_mk qz140 Bool.false 35467 1000 2 qz141 rfl)

noncomputable abbrev qz340 := (ep404 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 70934 4000) Bool.false 9000 4000 0 1 Bool.false 70934 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 70934 4000)))

noncomputable abbrev qz143 := qz340

noncomputable def ep405 := ep379 (@ep380 26673000000000000000000 (ep398 rfl) (ep403 rfl)) qz143 rfl rfl rfl rfl rfl rfl

noncomputable def ep406 := @ep377 5308375001915361457 26673000000000000000000 (ep405 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz41 (↑qz3) Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 (@ep98 65536 1 65536 (ep100 rfl) (ep102 rfl) rfl rfl) (@ep103 1 0 1 (ep105 rfl) (ep107 rfl) rfl rfl))

noncomputable abbrev qz341 := (@HPow.hPow Complex Int Complex qz405 qz411 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz144 := qz341

noncomputable def ep407 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz129 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz129 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) qz144)) Bool.false 630051 1073741824 3 1073741824

noncomputable def ep408 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz129 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) qz144) Bool.false 0 1 0 1 Bool.false

noncomputable def ep409 := @ep408 0 1 0 1 Bool.false 630051 1073741824 3 1073741824 Bool.true 7448672939 1610612736000 35467 1610612736000 Bool.false 630051 630051 1073741824 3 1073741824 Bool.true 7448672939 7448672939 1610612736000 35467

noncomputable def ep410 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz6 (@HMul.hMul Complex Complex Complex qz4 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz17 qz129 (@HSub.hSub Int Int Int qz19 qz20 (@HMul.hMul Int Int Int qz21 qz22 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz44 qz44) Bool.false 0 1 0 1 Bool.false

noncomputable def ep411 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47) qz144 Bool.false 630051 1073741824 3 1073741824 Bool.true 7448672939 1610612736000 35467 1610612736000

noncomputable abbrev qz145 := (Complex.re qz341)

noncomputable abbrev qz146 := (Complex.im qz341)

noncomputable def ep412 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz145) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz146) 630051 1073741824 3 1073741824 0 1 0

noncomputable def ep413 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz145 1 12 0 1 1890153 268435456 9 268435456 630051

noncomputable def ep414 := @Enclosure.Complex.IsNear.re_isNear qz144 Bool.false 1890153 268435456 9 268435456 Bool.true 7448672939 134217728000 35467 134217728000

noncomputable abbrev qz342 := (@HPow.hPow Complex Nat Complex qz406 qz411 1)

noncomputable abbrev qz147 := (@Inv.inv Complex Complex.instInv qz342)

noncomputable def ep415 := @Enclosure.Complex.IsNear.of_eq qz144 qz147 Bool.false 1890153 268435456 9 268435456 Bool.true 7448672939 134217728000 35467

noncomputable def ep416 := @Enclosure.Complex.IsNear.of_parts qz147 Bool.false 1890153 268435456 9 268435456 Bool.true 7448672939 134217728000 35467

noncomputable abbrev qz148 := (Complex.re qz342)

noncomputable abbrev qz149 := qz342

noncomputable def ep417 := @Enclosure.Real.IsNear.mulLit_ff qz148 (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz149)) 9000 4000 0 1 210017 67108864 1 67108864

noncomputable def ep418 := @Enclosure.Complex.IsNear.re_isNear qz149 Bool.false 9000 4000 0 1 Bool.false 70934 4000 0 1

noncomputable def ep419 := @Enclosure.Complex.IsNear.of_eq qz149 qz129 Bool.false 9000 4000 0 1 Bool.false 70934 4000 0

noncomputable def ep420 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz149)) Bool.false 210017 67108864 1 67108864 210017 67108864 1

noncomputable abbrev qz150 := (Complex.im qz342)

noncomputable def ep421 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz149) (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 qz148 qz148) (@HMul.hMul Real Real Real qz0 qz150 qz150)) Bool.false 1278158089 4000000 0 1

noncomputable def ep422 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz148 qz148) (@HMul.hMul Real Real Real qz0 qz150 qz150) 81 16 0 1 1257908089 4000000

noncomputable def ep423 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz148 9000 4000 0 1 9000 4000 0 1

noncomputable def ep424 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz150 70934 4000 0 1 70934 4000 0 1

noncomputable def ep425 := @Enclosure.Complex.IsNear.im_isNear qz149 Bool.false 9000 4000 0 1 Bool.false 70934 4000 0 1

noncomputable abbrev qz151 := (ep418 (@ep419 1 (BSN.pow_one_c qz327) qz340))

noncomputable abbrev qz152 := (ep425 (@ep419 1 (BSN.pow_one_c qz327) qz340))

noncomputable def ep426 := @ep422 0 1 20450529424 1278158089 4000000 0 1 (@ep423 81 16 0 1 qz151 qz151 rfl) (@ep424 1257908089 4000000 0 1 qz152 qz152 rfl)

noncomputable def ep427 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz149) 1278158089 4000000 0 1 105008 105009 33554432 (ep421 (Enclosure.Complex.normSq_eq_mul_add_mul qz149) (ep426 rfl rfl)) rfl

noncomputable def ep428 := @Enclosure.Real.IsNear.of_eq (Complex.re qz147) (@HMul.hMul Real Real Real qz0 qz148 (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz149))) Bool.false 1890153 268435456 9 268435456 (Enclosure.Complex.inv_re_eq_mul qz149) (@ep417 1890153 268435456 9 268435456 qz151 (@ep420 67108864 (ep427 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep429 := @Enclosure.Real.IsNear.of_eq (Complex.im qz147) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz150) (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz149))) Bool.true 7448672939 134217728000 35467 134217728000 (Enclosure.Complex.inv_im_eq_mul qz149)

noncomputable def ep430 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz150) (@Inv.inv Real Real.instInv (@DFunLike.coe qz53 Complex (fun (x : Complex) => Real) qz54 Complex.normSq qz149)) 70934 4000 0 1 210017 67108864 1

noncomputable def ep431 := @ep430 67108864 7448672939 134217728000 35467 134217728000 (@Enclosure.Real.IsNear.neg qz150 Bool.false 70934 4000 0 1 qz152) (@ep420 67108864 (ep427 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep432 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz146 0 1 0 1 7448672939 134217728000 35467 134217728000 0

noncomputable def ep433 := @Enclosure.Complex.IsNear.im_isNear qz144 Bool.false 1890153 268435456 9 268435456 Bool.true 7448672939 134217728000 35467 134217728000

noncomputable abbrev qz153 := (@ep415 134217728000 (BSN.zpow_one_sub_two_mul qz327 1 1 rfl rfl) (@ep416 134217728000 ep428 (ep429 ep431)))

noncomputable def ep434 := @ep412 1 630051 630051 1073741824 3 1073741824 (@ep413 1073741824 3 1073741824 ep117 (ep414 qz153) rfl) (@ep432 1 0 1 ep137 (ep433 qz153) rfl) rfl

noncomputable def ep435 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz146) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz145) 7448672939 1610612736000 35467 1610612736000 0 1 0

noncomputable def ep436 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz146 1 12 0 1 7448672939 134217728000 35467 134217728000 7448672939

noncomputable def ep437 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 (@Rat.cast Complex Complex.instRatCast (bernoulli qz46)) qz47)) qz145 0 1 0 1 1890153 268435456 9 268435456 0

noncomputable def ep438 := @ep435 1 7448672939 7448672939 1610612736000 35467 1610612736000 (@ep436 1610612736000 35467 1610612736000 ep117 (ep433 qz153) rfl) (@ep437 1 0 1 ep137 (ep414 qz153) rfl) rfl

noncomputable def ep439 := @ep409 1610612736000 (@ep410 0 1 0 1 (BSN.stirling_sum_base qz129) qz61) (ep411 (ep434 rfl) (ep438 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep440 := @ep375 242677047478287991663 6755399441055744000 86982039355874690314613 ep368 (ep406 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep407 Bool.true 7448672939 1610612736000 35467 1610612736000 (BSN.stirling_sum_succ qz129 0 1 rfl) (ep439 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep441 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz140 2) Bool.false 3238922876165367 562949953421312 62500000026673 3334125000000000000 Bool.false 860507075020195 281474976710656

noncomputable abbrev qz154 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz256 qz328 qz281))

noncomputable def ep442 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz140 2) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz140 1) qz154) Bool.false 3238922876165367 562949953421312 62500000026673 3334125000000000000 Bool.false 860507075020195 281474976710656 1000000000026673 26673000000000000000

noncomputable def ep443 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz140 1) qz154 Bool.false 3237582846369015 1125899906842624 62500000026673 6668250000000000000 Bool.false 876346914407843 562949953421312 1000000000026673 53346000000000000000 Bool.false

noncomputable def ep444 := nat_lit 7293405929090060990722936406016

noncomputable def ep445 := nat_lit 968844835602656412183486791680

noncomputable abbrev qz155 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz256 qz328 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep446 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz140 1) (@HAdd.hAdd Complex Complex Complex qz8 (BSN.logSumC qz140 0) qz155) Bool.false 3237582846369015 1125899906842624 62500000026673 6668250000000000000 Bool.false 876346914407843 562949953421312 1000000000026673 53346000000000000000

noncomputable def ep447 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz140 0) qz155 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz343 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz137))

noncomputable def ep448 := @Enclosure.Complex.IsNear.of_eq qz155 qz343 Bool.false 3237582846369015 1125899906842624 62500000026673 6668250000000000000 Bool.false 876346914407843 562949953421312 1000000000026673 53346000000000000000

noncomputable def ep449 := nat_lit 104163155090453911016155967330684736925440

noncomputable def ep450 := nat_lit 367836104461567083181890175572275693568

noncomputable def ep451 := nat_lit 2308861491636955971382542068083385088

noncomputable def ep452 := BSN.log_dyadic_bound 936632356 9128632356 3 2 ep449 131072 53346 ep450 ep451 26991 10065264712 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 936632356) (BSN.artanhQ 9128632356) 0 2 ep450 ep449 ep451 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep453 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 5032632356 16000000)) 1 2 0 1 3237582846369015 562949953421312 62500000026673 3334125000000000000 3237582846369015 1125899906842624 62500000026673 6668250000000000000 qz33 (BSN.isNear_log_sfrac 5032632356 16000000 3237582846369015 562949953421312 62500000026673 3334125000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5032632356) qz273)) Bool.false 27158813365713890181120 4722366482869645213696 1000000000426768 53346000000000000000 3237582846369015 562949953421312 62500000026673 3334125000000000000 (BSN.log_rat_reduce_isNear 5032632356 16000000 8 10065264712 8192000000 26991 131072 24973259072661432 36028797018963968 53346 1000000000000000 rfl rfl rfl rfl (ep452 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep454 := BSN.arctan_dyadic_bound_f 1000 70934 1 0 131072 53346 0 1 1 0 1 1 1847 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 70934) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 70934) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz344 := (@Nat.cast Real Real.instNatCast 70934)

noncomputable def ep455 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz286 qz344)) 884279719003555 562949953421312 1 2000000000000000 1847 131072 1 53346 114864542765264797696 876346914407843 562949953421312 1000000000026673 53346000000000000000 qz35 (ep454 rfl) rfl rfl

noncomputable abbrev qz156 := (@HAdd.hAdd Complex Complex Complex qz256 qz328 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz345 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz137)

noncomputable def ep456 := @ep447 3237582846369015 1125899906842624 62500000026673 6668250000000000000 Bool.false 876346914407843 562949953421312 1000000000026673 53346000000000000000 Bool.false 3237582846369015 3237582846369015 1125899906842624 62500000026673 6668250000000000000 Bool.false 876346914407843 876346914407843 562949953421312 1000000000026673 53346000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz140 0) (Complex.mk qz44 qz44) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz140) qz61) (ep448 (@congrArg Complex Complex qz156 qz345 Complex.log (BSN.w_shift_mk qz140 Bool.false 35467 1000 0 qz141 rfl)) (@Enclosure.Complex.IsNear.of_parts qz343 Bool.false 3237582846369015 1125899906842624 62500000026673 6668250000000000000 Bool.false 876346914407843 562949953421312 1000000000026673 53346000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz343) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 5032632356 16000000))) Bool.false 3237582846369015 1125899906842624 62500000026673 6668250000000000000 (Enclosure.clog_re_eq 1000 70934 4000 5032632356 16000000 rfl rfl rfl) (ep453 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz343) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz344 qz286)) Bool.false 876346914407843 562949953421312 1000000000026673 53346000000000000000 (Enclosure.clog_im_eq 1000 70934 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz344 qz286)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz286 qz344))) Bool.false 876346914407843 562949953421312 1000000000026673 53346000000000000000 (BSN.arctan_recip 70934 1000 rfl rfl) ep455)))) rfl rfl

noncomputable abbrev qz346 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz137))

noncomputable def ep457 := @Enclosure.Complex.IsNear.of_eq qz154 qz346 Bool.false 3240262905961719 1125899906842624 62500000026673 6668250000000000000 Bool.false 844667235632547 562949953421312 1000000000026673 53346000000000000000

noncomputable def ep458 := nat_lit 105262900012639475398326942877267776925440

noncomputable def ep459 := nat_lit 389078756216163389239233592416563693568

noncomputable def ep460 := nat_lit 2554759933761299252572083384691385088

noncomputable def ep461 := BSN.log_dyadic_bound 960632356 9152632356 3 2 ep458 131072 53346 ep459 ep460 27615 10113264712 8192000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 960632356) (BSN.artanhQ 9152632356) 0 2 ep459 ep458 ep460 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep462 := @Enclosure.Real.IsNear.mulLit_ff qz32 (Real.log (Enclosure.sfrac Bool.false 5056632356 16000000)) 1 2 0 1 3240262905961719 562949953421312 62500000026673 3334125000000000000 3240262905961719 1125899906842624 62500000026673 6668250000000000000 qz33 (BSN.isNear_log_sfrac 5056632356 16000000 3240262905961719 562949953421312 62500000026673 3334125000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5056632356) qz273)) Bool.false 27181295335053723697152 4722366482869645213696 1000000000426768 53346000000000000000 3240262905961719 562949953421312 62500000026673 3334125000000000000 (BSN.log_rat_reduce_isNear 5056632356 16000000 8 10113264712 8192000000 27615 131072 24973259072661432 36028797018963968 53346 1000000000000000 rfl rfl rfl rfl (ep461 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep463 := BSN.arctan_dyadic_bound_f 5000 70934 1 0 131072 53346 0 1 1 0 1 1 9223 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 70934) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 70934) 0 0 rfl) rfl rfl rfl

noncomputable def ep464 := @Enclosure.Real.IsNear.subLit_ff_p qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz290 qz344)) 884279719003555 562949953421312 1 2000000000000000 9223 131072 1 53346 110712223908829200384 844667235632547 562949953421312 1000000000026673 53346000000000000000 qz35 (ep463 rfl) rfl rfl

noncomputable abbrev qz157 := (@HAdd.hAdd Complex Complex Complex qz256 qz328 qz281)

noncomputable abbrev qz347 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz137)

noncomputable def ep465 := @ep443 3240262905961719 1125899906842624 62500000026673 6668250000000000000 Bool.false 844667235632547 562949953421312 1000000000026673 53346000000000000000 Bool.false ep444 3238922876165367 562949953421312 62500000026673 3334125000000000000 Bool.false ep445 860507075020195 281474976710656 1000000000026673 26673000000000000000 (ep446 (BSN.log_sum_c_succ qz140 0 1 rfl) (ep456 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep457 (@congrArg Complex Complex qz157 qz347 Complex.log (BSN.w_shift_mk qz140 Bool.false 35467 1000 1 qz141 rfl)) (@Enclosure.Complex.IsNear.of_parts qz346 Bool.false 3240262905961719 1125899906842624 62500000026673 6668250000000000000 Bool.false 844667235632547 562949953421312 1000000000026673 53346000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz346) (@HMul.hMul Real Real Real qz0 qz32 (Real.log (Enclosure.sfrac Bool.false 5056632356 16000000))) Bool.false 3240262905961719 1125899906842624 62500000026673 6668250000000000000 (Enclosure.clog_re_eq 5000 70934 4000 5056632356 16000000 rfl rfl rfl) (ep462 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz346) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz344 qz290)) Bool.false 844667235632547 562949953421312 1000000000026673 53346000000000000000 (Enclosure.clog_im_eq 5000 70934 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz344 qz290)) (@HSub.hSub Real Real Real qz5 qz34 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz290 qz344))) Bool.false 844667235632547 562949953421312 1000000000026673 53346000000000000000 (BSN.arctan_recip 70934 5000 rfl rfl) ep464)))) rfl rfl

noncomputable def ep466 := @ep367 ep368 Bool.false 3238922876165367 562949953421312 62500000026673 3334125000000000000 Bool.false 860507075020195 281474976710656 1000000000026673 26673000000000000000 Bool.true ep369 6227548056493499531 225179981368524800 41825575750868002728859 ep56 Bool.false ep370 222024877677803311663 6755399441055744000 34455346452103900248871 ep362 (@ep371 225179981368524800 39777575749993981864859 ep56 Bool.false 242677047478287991663 6755399441055744000 86982039355874690314613 ep368 (BSN.logGammaStirling_unfold 1 qz129) (ep440 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep441 1000000000026673 26673000000000000000 (BSN.log_sum_c_eq qz140 2) (ep442 (BSN.log_sum_c_succ qz140 1 2 rfl) (ep465 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz158 := (@HDiv.hDiv Real Real Real qz251 qz329 (2 : Real))

noncomputable def ep467 := @Enclosure.Real.IsNear.mulLit_ff qz158 (Real.log Real.pi) 35467 2000 0 1 75021 65536 1 32768 2660769807 131072000 35467 65536000 (@Enclosure.Real.IsNear.of_eq qz158 (Enclosure.sfrac Bool.false 35467 2000) Bool.false 35467 2000 0 1 (BSN.t_half_eq qz140 Bool.false 35467 1000 qz141) (Enclosure.Real.IsNear.const Bool.false 35467 2000)) EMRow05.d5 rfl

noncomputable def ep468 := @ep364 35467 65536000 ep365 84889846038812529199 6755399441055744000 113289620702103900248871 ep362 (@ep366 34455346452103900248871 ep362 (ep466 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep467 rfl rfl

noncomputable def ep469 := nat_lit 497143661830442952058168913000073723949609606500186728908403708532998400

noncomputable def ep470 := nat_lit 998469887541030595578313081141409612761803151570226224381333992489216

noncomputable def ep471 := nat_lit 1300426353547522253473791789059297470971172716683661066587297076836679936

noncomputable def ep472 := BSN.sin_dyadic_bound_f 421615794 268435456 3 2 131072 53399 ep469 ep175 ep470 ep471 ep178 ep470 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 421615794) qz292 0 2 ep469 ep175 ep470 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 421615794) qz293 0 2 ep471 ep178 ep470 rfl rfl rfl rfl) rfl rfl

noncomputable def ep473 := @ep361 131072 Bool.false 131071 131072 1 26673 (@ep363 1647079 131072 103 131072 ep468 rfl) (Enclosure.sfrac_false_div 1647079 131072) (BSN.cos_reduce3 qz331 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29668573958805355757568) qz67) 226375608064910080 72057594037927936 Bool.false 131071 131072 1 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q3 1647079 131072 226375608064910080 72057594037927936 1 29668573958805355757568 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131071 131072 29668573958805355757568 18889465931478580854784 421615794 268435456 53399 53346 (ep472 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep474 := nat_lit 83128763567040356708558009

noncomputable def ep475 := nat_lit 18449173284065800183873536000

noncomputable abbrev qz415 := (@Neg.neg Complex Complex.instNeg qz426)

noncomputable abbrev qz348 := qz415

noncomputable abbrev qz159 := qz348

noncomputable abbrev qz349 := (@HPow.hPow Complex Complex Complex qz407 (@Nat.cast Complex Complex.instNatCast 8) qz415)

noncomputable abbrev qz160 := qz349

noncomputable abbrev qz350 := (@Nat.cast Complex Complex.instNatCast 8)

noncomputable abbrev qz161 := (@HAdd.hAdd Complex Complex Complex qz256 (@HDiv.hDiv Complex Complex Complex qz264 qz350 (@HSub.hSub Complex Complex Complex qz254 qz330 (1 : Complex))) qz263)

noncomputable abbrev qz162 := qz350

noncomputable def ep476 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz127 1 8) (@HAdd.hAdd Complex Complex Complex qz8 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 8, @HPow.hPow Complex Complex Complex qz68 (@Nat.cast Complex Complex.instNatCast n) qz159) (@HMul.hMul Complex Complex Complex qz4 qz160 (@HAdd.hAdd Complex Complex Complex qz8 qz161 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) Bool.false 1040878283489508383463383 345839862108982870016000 ep358

noncomputable def ep477 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 8, @HPow.hPow Complex Complex Complex qz68 (@Nat.cast Complex Complex.instNatCast n) qz159) (@HMul.hMul Complex Complex Complex qz4 qz160 (@HAdd.hAdd Complex Complex Complex qz8 qz161 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) Bool.false 52809303031 17179869184 640954600999 152746216914944

noncomputable def ep478 := nat_lit 271311371824497061527552000

noncomputable def ep479 := nat_lit 1085245487297988246110208000

noncomputable def ep480 := nat_lit 17882152746816221064372228794089472

noncomputable def ep481 := nat_lit 49838155598545458608878794047488

noncomputable def ep482 := @ep477 Bool.true 3334537973 17179869184 639767172385 152746216914944 Bool.true 22200945036969500680617 345839862108982870016000 85429613095459500141367 ep478 Bool.false 23949443450735965695993 138335944843593148006400 344450131635718833595177 ep479 Bool.false ep480 1040878283489508383463383 345839862108982870016000 ep358 ep359 Bool.true ep481 2900962461632761324807 138335944843593148006400

noncomputable def ep483 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 8, @HPow.hPow Complex Complex Complex qz68 (@Nat.cast Complex Complex.instNatCast n) qz159) (BSN.headSumC qz127 8) Bool.false 52809303031 17179869184 640954600999 152746216914944 Bool.true 3334537973 17179869184 639767172385

noncomputable abbrev qz163 := (BSN.headSumC qz330 7)

noncomputable abbrev qz164 := (@HPow.hPow Complex Complex Complex qz294 qz297 qz348)

noncomputable def ep484 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz127 8) (@HAdd.hAdd Complex Complex Complex qz8 qz163 qz164) Bool.false 52809303031 17179869184 640954600999 152746216914944 Bool.true 3334537973 17179869184 639767172385 152746216914944

noncomputable def ep485 := @Enclosure.Complex.IsNear.addLitP qz163 qz164 Bool.false 23174157217 8589934592 280273452047 76373108457472 Bool.true 3982633335 17179869184 560402700965 152746216914944 Bool.false

noncomputable abbrev qz165 := (BSN.headSumC qz330 6)

noncomputable abbrev qz166 := (@HPow.hPow Complex Complex Complex qz294 (@Nat.cast Complex Complex.instNatCast 6) qz348)

noncomputable def ep486 := @Enclosure.Complex.IsNear.of_eq qz163 (@HAdd.hAdd Complex Complex Complex qz8 qz165 qz166) Bool.false 23174157217 8589934592 280273452047 76373108457472 Bool.true 3982633335 17179869184 560402700965 152746216914944

noncomputable def ep487 := @Enclosure.Complex.IsNear.addLitP qz165 qz166 Bool.false 20528890367 8589934592 709785246299 229119325372416 Bool.false 621848655 17179869184 1419821832277 458238650744832 Bool.false

noncomputable abbrev qz167 := (BSN.headSumC qz330 5)

noncomputable abbrev qz168 := (@HPow.hPow Complex Complex Complex qz294 (@Nat.cast Complex Complex.instNatCast 5) qz348)

noncomputable def ep488 := @Enclosure.Complex.IsNear.of_eq qz165 (@HAdd.hAdd Complex Complex Complex qz8 qz167 qz168) Bool.false 20528890367 8589934592 709785246299 229119325372416 Bool.false 621848655 17179869184 1419821832277 458238650744832

noncomputable def ep489 := @Enclosure.Complex.IsNear.addLitP qz167 qz168 Bool.false 34441269625 17179869184 1135260910931 458238650744832 Bool.false 4527030429 17179869184 1136746010225 458238650744832 Bool.false

noncomputable abbrev qz169 := (BSN.headSumC qz330 4)

noncomputable abbrev qz170 := (@HPow.hPow Complex Complex Complex qz294 (@Nat.cast Complex Complex.instNatCast 4) qz348)

noncomputable def ep490 := @Enclosure.Complex.IsNear.of_eq qz167 (@HAdd.hAdd Complex Complex Complex qz8 qz169 qz170) Bool.false 34441269625 17179869184 1135260910931 458238650744832 Bool.false 4527030429 17179869184 1136746010225 458238650744832

noncomputable def ep491 := @Enclosure.Complex.IsNear.addLitP qz169 qz170 Bool.false 30528830125 17179869184 272474418037 152746216914944 Bool.true 3119986581 17179869184 272462788609 152746216914944 Bool.false

noncomputable abbrev qz171 := (BSN.headSumC qz330 3)

noncomputable abbrev qz172 := (@HPow.hPow Complex Complex Complex qz294 qz299 qz348)

noncomputable def ep492 := @Enclosure.Complex.IsNear.of_eq qz169 (@HAdd.hAdd Complex Complex Complex qz8 qz171 qz172) Bool.false 30528830125 17179869184 272474418037 152746216914944 Bool.true 3119986581 17179869184 272462788609 152746216914944

noncomputable def ep493 := @Enclosure.Complex.IsNear.addLitP qz171 qz172 Bool.false 13771460825 8589934592 13329802117 13477607374848 Bool.false 396169209 1073741824 1657709321 1684700921856 Bool.false

noncomputable abbrev qz173 := (BSN.headSumC qz330 2)

noncomputable abbrev qz174 := (@HPow.hPow Complex Complex Complex qz294 qz300 qz348)

noncomputable def ep494 := @Enclosure.Complex.IsNear.of_eq qz171 (@HAdd.hAdd Complex Complex Complex qz8 qz173 qz174) Bool.false 13771460825 8589934592 13329802117 13477607374848 Bool.false 396169209 1073741824 1657709321 1684700921856

noncomputable def ep495 := @Enclosure.Complex.IsNear.addLitP qz173 qz174 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep496 := @Enclosure.Complex.IsNear.of_eq qz173 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz44) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz127)

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz248 qz329 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable def ep497 := @Enclosure.Complex.IsNear.of_eq qz174 (Complex.mk (@HMul.hMul Real Real Real qz0 qz85 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz85 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 5181526233 8589934592 13329802117 13477607374848 Bool.false 396169209 1073741824 1657709321 1684700921856 (BSN.cpow_neg_s_mk qz140 35467 1000 2 qz141 rfl)

noncomputable def ep498 := nat_lit 5661166998794301471692579238117376

noncomputable def ep499 := BSN.sin_dyadic_bound_f 274300432 268435456 2 1 131072 53399 ep498 ep223 ep498 ep498 ep224 ep498 111813 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 274300432) qz292 0 1 ep498 ep223 ep498 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 274300432) qz293 0 1 ep498 ep224 ep498 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz351 := (Enclosure.Real.IsNear.const Bool.false 35467 1000)

noncomputable abbrev qz176 := qz351

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3222247) qz12)

noncomputable def ep500 := @Enclosure.Real.IsNear.cos_image qz175 qz352 Bool.false 3222247 131072 11 8192 Bool.false 111813 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 805561971 32768000 35467 26673000 3222247 131072 11 8192 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz89 35467 1000 0 1 45426 65536 1 26673 805561971 32768000 35467 26673000 qz176 qz303 rfl) rfl) (Enclosure.sfrac_false_div 3222247 131072) (BSN.cos_reduce3 qz352 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19302176927603945897984) qz67) 226375608064910080 72057594037927936 Bool.false 111813 131072 3 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q3 3222247 131072 226375608064910080 72057594037927936 3 19302176927603945897984 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 111813 131072 19302176927603945897984 18889465931478580854784 274300432 268435456 53399 53346 (ep499 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep501 := nat_lit 49414740979235796610524071796998727803596160830900304872302341213126656

noncomputable def ep502 := nat_lit 32048811788237678560648636396593142579835544055991437005292753125376

noncomputable def ep503 := nat_lit 148180125314130914474450918118202997125628811404588931742896438133129216

noncomputable def ep504 := BSN.cos_dyadic_bound_f 274300432 268435456 3 2 131072 53399 ep501 ep208 ep502 ep503 ep210 ep502 68392 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 274300432) qz304 0 2 ep501 ep208 ep502 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 274300432) qz305 0 2 ep503 ep210 ep502 rfl rfl rfl rfl) rfl rfl

noncomputable def ep505 := @Enclosure.Real.IsNear.sin_image qz175 qz352 Bool.false 3222247 131072 11 8192 Bool.true 68392 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 805561971 32768000 35467 26673000 3222247 131072 11 8192 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz89 35467 1000 0 1 45426 65536 1 26673 805561971 32768000 35467 26673000 qz176 qz303 rfl) rfl) (Enclosure.sfrac_false_div 3222247 131072) (BSN.sin_reduce3 qz352 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19302176927603945897984) qz67) 226375608064910080 72057594037927936 Bool.false 68392 131072 3 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q3 3222247 131072 226375608064910080 72057594037927936 3 19302176927603945897984 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 68392 131072 19302176927603945897984 18889465931478580854784 274300432 268435456 53399 53346 (ep504 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep506 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz85 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz85 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 5181526233 8589934592 13329802117 13477607374848 Bool.false 396169209 1073741824 1657709321 1684700921856 (@Enclosure.Real.IsNear.mulLit_ff qz85 (Real.cos qz175) 46341 65536 1 65536 111813 131072 301595 218505216 5181526233 8589934592 13329802117 13477607374848 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 111813 131072 301595 218505216 111813 131072 301595 218505216 (ep500 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz85 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 46341 65536 1 65536 8549 16384 301595 218505216 396169209 1073741824 1657709321 1684700921856 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 8549 16384 301595 218505216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 68392 131072 301595 218505216 8549 16384 301595 218505216 (ep505 rfl rfl) rfl)) rfl)

noncomputable def ep507 := @ep495 5181526233 8589934592 13329802117 13477607374848 Bool.false 396169209 1073741824 1657709321 1684700921856 Bool.false 13771460825 13771460825 8589934592 13329802117 13477607374848 Bool.false 396169209 396169209 1073741824 1657709321 1684700921856 (ep496 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz44 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz45)) (ep497 ep506) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz248 qz329 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep508 := @Enclosure.Complex.IsNear.of_eq qz172 (Complex.mk (@HMul.hMul Real Real Real qz0 qz91 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz91 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.false 2985908475 17179869184 364209982133 458238650744832 Bool.true 9458693925 17179869184 366491430515 458238650744832 (BSN.cpow_neg_s_mk qz140 35467 1000 3 qz141 rfl)

noncomputable def ep509 := nat_lit 116164158702571594683947827744869038183147962484027262445095338182078401

noncomputable def ep510 := nat_lit 176800594372274305816923439836603481740468153192125564961143897616321

noncomputable def ep511 := nat_lit 348138874918970235440209636354933907585962951145697536205363726751002561

noncomputable def ep512 := BSN.cos_dyadic_bound_f 339574809 268435456 3 2 131072 53399 ep509 ep208 ep510 ep511 ep210 ep510 39457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 339574809) qz304 0 2 ep509 ep208 ep510 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 339574809) qz305 0 2 ep511 ep210 ep510 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz353 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2553553) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz354 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep513 := @Enclosure.Real.IsNear.cos_image qz177 qz353 Bool.false 2553553 65536 175 131072 Bool.false 39457 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 1276776533 32768000 35467 26673000 2553553 65536 175 131072 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz95 35467 1000 0 1 71998 65536 1 26673 1276776533 32768000 35467 26673000 qz176 qz309 rfl) rfl) (Enclosure.sfrac_false_div 2553553 65536) (BSN.cos_reduce0 qz353 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11947726453259261444096) qz354) 226375608064910080 72057594037927936 Bool.false 39457 131072 6 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q0 2553553 65536 226375608064910080 72057594037927936 6 11947726453259261444096 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 39457 131072 11947726453259261444096 9444732965739290427392 339574809 268435456 53399 53346 (ep512 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep514 := nat_lit 208954045189131050986452551188894985944273957948695371949202693609648065

noncomputable def ep515 := nat_lit 546974345961597641802719758020703795645518655712843485142736631238651841

noncomputable def ep516 := BSN.sin_dyadic_bound_f 339574809 268435456 3 2 131072 53399 ep514 ep175 ep510 ep515 ep178 ep510 124991 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 339574809) qz292 0 2 ep514 ep175 ep510 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 339574809) qz293 0 2 ep515 ep178 ep510 rfl rfl rfl rfl) rfl rfl

noncomputable def ep517 := @Enclosure.Real.IsNear.sin_image qz177 qz353 Bool.false 2553553 65536 175 131072 Bool.false 124991 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 1276776533 32768000 35467 26673000 2553553 65536 175 131072 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz95 35467 1000 0 1 71998 65536 1 26673 1276776533 32768000 35467 26673000 qz176 qz309 rfl) rfl) (Enclosure.sfrac_false_div 2553553 65536) (BSN.sin_reduce0 qz353 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11947726453259261444096) qz354) 226375608064910080 72057594037927936 Bool.false 124991 131072 6 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q0 2553553 65536 226375608064910080 72057594037927936 6 11947726453259261444096 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 124991 131072 11947726453259261444096 9444732965739290427392 339574809 268435456 53399 53346 (ep516 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep518 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz91 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz91 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.false 2985908475 17179869184 364209982133 458238650744832 Bool.true 9458693925 17179869184 366491430515 458238650744832 (@Enclosure.Real.IsNear.mulLit_ff qz91 (Real.cos qz177) 75675 131072 1 131072 39457 131072 4798847 3496083456 2985908475 17179869184 364209982133 458238650744832 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.false 39457 131072 4798847 3496083456 39457 131072 4798847 3496083456 (ep513 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz91 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 75675 131072 1 131072 124991 131072 4798847 3496083456 9458693925 17179869184 366491430515 458238650744832 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.false 124991 131072 4798847 3496083456 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.false 124991 131072 4798847 3496083456 124991 131072 4798847 3496083456 (ep517 rfl rfl) rfl)) rfl)

noncomputable def ep519 := @ep493 2985908475 17179869184 364209982133 458238650744832 Bool.true 9458693925 17179869184 366491430515 458238650744832 Bool.false 262240653944029184000 30528830125 17179869184 272474418037 152746216914944 Bool.true 3350060082338463744 3119986581 17179869184 272462788609 152746216914944 (ep494 (BSN.head_sum_c_succ qz127 2 3 rfl rfl) (ep507 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep508 ep518) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz248 qz329 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep520 := @Enclosure.Complex.IsNear.of_eq qz170 (Complex.mk (@HMul.hMul Real Real Real qz0 qz96 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz96 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.false 978109875 4294967296 79459414205 114559662686208 Bool.false 3823508505 8589934592 159678822199 229119325372416 (BSN.cpow_neg_s_mk qz140 35467 1000 4 qz141 rfl)

noncomputable def ep521 := nat_lit 259698241755977204340702680617521

noncomputable def ep522 := BSN.sin_dyadic_bound_f 126945483 268435456 2 1 131072 53399 ep521 ep223 ep521 ep521 ep224 ep521 59700 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 126945483) qz292 0 1 ep521 ep223 ep521 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 126945483) qz293 0 1 ep521 ep224 ep521 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6444495) qz12)

noncomputable def ep523 := @Enclosure.Real.IsNear.cos_image qz178 qz355 Bool.false 6444495 131072 11 8192 Bool.false 59700 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 805561971 16384000 35467 26673000 6444495 131072 11 8192 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz99 35467 1000 0 1 90852 65536 1 26673 805561971 16384000 35467 26673000 qz176 qz312 rfl) rfl) (Enclosure.sfrac_false_div 6444495 131072) (BSN.cos_reduce3 qz355 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8932994270112073646080) qz67) 226375608064910080 72057594037927936 Bool.false 59700 131072 7 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q3 6444495 131072 226375608064910080 72057594037927936 7 8932994270112073646080 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 59700 131072 8932994270112073646080 18889465931478580854784 126945483 268435456 53399 53346 (ep522 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep524 := BSN.cos_dyadic_bound_f 126945483 268435456 2 1 131072 53399 ep521 ep219 ep521 ep521 ep220 ep521 116686 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 126945483) qz304 0 1 ep521 ep219 ep521 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 126945483) qz305 0 1 ep521 ep220 ep521 rfl rfl rfl rfl) rfl rfl

noncomputable def ep525 := @Enclosure.Real.IsNear.sin_image qz178 qz355 Bool.false 6444495 131072 11 8192 Bool.true 116686 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 805561971 16384000 35467 26673000 6444495 131072 11 8192 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz99 35467 1000 0 1 90852 65536 1 26673 805561971 16384000 35467 26673000 qz176 qz312 rfl) rfl) (Enclosure.sfrac_false_div 6444495 131072) (BSN.sin_reduce3 qz355 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8932994270112073646080) qz67) 226375608064910080 72057594037927936 Bool.false 116686 131072 7 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q3 6444495 131072 226375608064910080 72057594037927936 7 8932994270112073646080 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 116686 131072 8932994270112073646080 18889465931478580854784 126945483 268435456 53399 53346 (ep524 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep526 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz96 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz96 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.false 978109875 4294967296 79459414205 114559662686208 Bool.false 3823508505 8589934592 159678822199 229119325372416 (@Enclosure.Real.IsNear.mulLit_ff qz96 (Real.cos qz178) 65535 131072 1 131072 14925 32768 301595 218505216 978109875 4294967296 79459414205 114559662686208 qz313 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.false 59700 131072 301595 218505216 14925 32768 301595 218505216 (ep523 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz96 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 65535 131072 1 131072 58343 65536 301595 218505216 3823508505 8589934592 159678822199 229119325372416 qz313 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.true 58343 65536 301595 218505216 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.true 116686 131072 301595 218505216 58343 65536 301595 218505216 (ep525 rfl rfl) rfl)) rfl)

noncomputable def ep527 := @ep491 978109875 4294967296 79459414205 114559662686208 Bool.false 3823508505 8589934592 159678822199 229119325372416 Bool.false 147924126672093184000 34441269625 17179869184 1135260910931 458238650744832 Bool.false 38886895281103699968 4527030429 17179869184 1136746010225 458238650744832 (ep492 (BSN.head_sum_c_succ qz127 3 4 rfl rfl) (ep519 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep520 ep526) rfl rfl

noncomputable abbrev qz179 := (@HMul.hMul Real Real Real qz248 qz329 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep528 := @Enclosure.Complex.IsNear.of_eq qz168 (Complex.mk (@HMul.hMul Real Real Real qz0 qz100 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz100 (@Neg.neg Real Real.instNeg (Real.sin qz179)))) Bool.false 6616511109 17179869184 284309581667 458238650744832 Bool.true 1952590887 8589934592 70768955513 114559662686208 (BSN.cpow_neg_s_mk qz140 35467 1000 5 qz141 rfl)

noncomputable def ep529 := nat_lit 419668007603866924901603556512016

noncomputable def ep530 := BSN.cos_dyadic_bound_f 143128614 268435456 2 1 131072 53399 ep529 ep219 ep529 ep529 ep220 ep529 112877 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 143128614) qz304 0 1 ep529 ep219 ep529 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 143128614) qz305 0 1 ep529 ep220 ep529 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz356 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3740917) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep531 := @Enclosure.Real.IsNear.cos_image qz179 qz356 Bool.false 3740917 65536 175 131072 Bool.false 112877 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 935229323 16384000 35467 26673000 3740917 65536 175 131072 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz103 35467 1000 0 1 105476 65536 1 26673 935229323 16384000 35467 26673000 qz176 qz315 rfl) rfl) (Enclosure.sfrac_false_div 3740917 65536) (BSN.cos_reduce0 qz356 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5035890426056429010944) qz354) 226375608064910080 72057594037927936 Bool.false 112877 131072 9 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q0 3740917 65536 226375608064910080 72057594037927936 9 5035890426056429010944 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 112877 131072 5035890426056429010944 9444732965739290427392 143128614 268435456 53399 53346 (ep530 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep532 := BSN.sin_dyadic_bound_f 143128614 268435456 2 1 131072 53399 ep529 ep223 ep529 ep529 ep224 ep529 66622 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 143128614) qz292 0 1 ep529 ep223 ep529 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 143128614) qz293 0 1 ep529 ep224 ep529 rfl rfl rfl rfl) rfl rfl

noncomputable def ep533 := @Enclosure.Real.IsNear.sin_image qz179 qz356 Bool.false 3740917 65536 175 131072 Bool.false 66622 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 935229323 16384000 35467 26673000 3740917 65536 175 131072 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz103 35467 1000 0 1 105476 65536 1 26673 935229323 16384000 35467 26673000 qz176 qz315 rfl) rfl) (Enclosure.sfrac_false_div 3740917 65536) (BSN.sin_reduce0 qz356 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5035890426056429010944) qz354) 226375608064910080 72057594037927936 Bool.false 66622 131072 9 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q0 3740917 65536 226375608064910080 72057594037927936 9 5035890426056429010944 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 66622 131072 5035890426056429010944 9444732965739290427392 143128614 268435456 53399 53346 (ep532 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep534 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz100 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz100 (@Neg.neg Real Real.instNeg (Real.sin qz179))) Bool.false 6616511109 17179869184 284309581667 458238650744832 Bool.true 1952590887 8589934592 70768955513 114559662686208 (@Enclosure.Real.IsNear.mulLit_ff qz100 (Real.cos qz179) 58617 131072 1 131072 112877 131072 4798847 3496083456 6616511109 17179869184 284309581667 458238650744832 qz316 (@Enclosure.Real.IsNear.recentre' (Real.cos qz179) Bool.false 112877 131072 4798847 3496083456 112877 131072 4798847 3496083456 (ep531 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz100 (@Neg.neg Real Real.instNeg (Real.sin qz179)) 58617 131072 1 131072 33311 65536 4798847 3496083456 1952590887 8589934592 70768955513 114559662686208 qz316 (@Enclosure.Real.IsNear.neg (Real.sin qz179) Bool.false 33311 65536 4798847 3496083456 (@Enclosure.Real.IsNear.recentre' (Real.sin qz179) Bool.false 66622 131072 4798847 3496083456 33311 65536 4798847 3496083456 (ep533 rfl rfl) rfl)) rfl)

noncomputable def ep535 := @ep489 6616511109 17179869184 284309581667 458238650744832 Bool.true 1952590887 8589934592 70768955513 114559662686208 Bool.false 705367301995475501056 20528890367 8589934592 709785246299 229119325372416 Bool.false 5341639272573173760 621848655 17179869184 1419821832277 458238650744832 (ep490 (BSN.head_sum_c_succ qz127 4 5 rfl rfl) (ep527 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep528 ep534) rfl rfl

noncomputable abbrev qz180 := (@HMul.hMul Real Real Real qz248 qz329 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep536 := @Enclosure.Complex.IsNear.of_eq qz166 (Complex.mk (@HMul.hMul Real Real Real qz0 qz104 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz104 (@Neg.neg Real Real.instNeg (Real.sin qz180)))) Bool.false 1322633425 4294967296 65517554921 114559662686208 Bool.true 2302240995 8589934592 130693135309 229119325372416 (BSN.cpow_neg_s_mk qz140 35467 1000 6 qz141 rfl)

noncomputable def ep537 := @Enclosure.Real.IsNear.mulLit_ff qz140 qz107 35467 1000 0 1 4034664351997175 2251799813685248 500000000026673 13336500000000000000 5723897622891352229 90071992547409920 17733500000946011291 13336500000000000000000 qz176 (BSN.isNear_log_sfrac 6 1 4034664351997175 2251799813685248 500000000026673 13336500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz318) Bool.false 4230652207559789772800 2361183241434822606848 1000000000053346 26673000000000000000 4034664351997175 2251799813685248 500000000026673 13336500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 26572 65536 24973259072661432 36028797018963968 26673 1000000000000000 rfl rfl rfl rfl (ep259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep538 := nat_lit 1365946318401232495256418709800625

noncomputable def ep539 := BSN.cos_dyadic_bound_f 192246485 268435456 2 1 131072 53399 ep538 ep219 ep538 ep538 ep220 ep538 98870 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 192246485) qz304 0 1 ep538 ep219 ep538 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 192246485) qz305 0 1 ep538 ep220 ep538 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8329367) qz12)

noncomputable def ep540 := @Enclosure.Real.IsNear.cos_image qz180 qz357 Bool.false 8329367 131072 175 131072 Bool.false 98870 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 5723897622891352229 90071992547409920 17733500000946011291 13336500000000000000000 8329367 131072 175 131072 (ep537 rfl) rfl) (Enclosure.sfrac_false_div 8329367 131072) (BSN.cos_reduce0 qz357 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13528143746471636762624) qz67) 226375608064910080 72057594037927936 Bool.false 98870 131072 10 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q0 8329367 131072 226375608064910080 72057594037927936 10 13528143746471636762624 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 98870 131072 13528143746471636762624 18889465931478580854784 192246485 268435456 53399 53346 (ep539 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep541 := BSN.sin_dyadic_bound_f 192246485 268435456 2 1 131072 53399 ep538 ep223 ep538 ep538 ep224 ep538 86049 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 192246485) qz292 0 1 ep538 ep223 ep538 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 192246485) qz293 0 1 ep538 ep224 ep538 rfl rfl rfl rfl) rfl rfl

noncomputable def ep542 := @Enclosure.Real.IsNear.sin_image qz180 qz357 Bool.false 8329367 131072 175 131072 Bool.false 86049 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 5723897622891352229 90071992547409920 17733500000946011291 13336500000000000000000 8329367 131072 175 131072 (ep537 rfl) rfl) (Enclosure.sfrac_false_div 8329367 131072) (BSN.sin_reduce0 qz357 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13528143746471636762624) qz67) 226375608064910080 72057594037927936 Bool.false 86049 131072 10 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q0 8329367 131072 226375608064910080 72057594037927936 10 13528143746471636762624 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 86049 131072 13528143746471636762624 18889465931478580854784 192246485 268435456 53399 53346 (ep541 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep543 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz104 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz104 (@Neg.neg Real Real.instNeg (Real.sin qz180))) Bool.false 1322633425 4294967296 65517554921 114559662686208 Bool.true 2302240995 8589934592 130693135309 229119325372416 (@Enclosure.Real.IsNear.mulLit_ff qz104 (Real.cos qz180) 26755 65536 1 65536 49435 65536 4798847 3496083456 1322633425 4294967296 65517554921 114559662686208 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz180) Bool.false 98870 131072 4798847 3496083456 49435 65536 4798847 3496083456 (ep540 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz104 (@Neg.neg Real Real.instNeg (Real.sin qz180)) 26755 65536 1 65536 86049 131072 4798847 3496083456 2302240995 8589934592 130693135309 229119325372416 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz180) Bool.false 86049 131072 4798847 3496083456 (@Enclosure.Real.IsNear.recentre' (Real.sin qz180) Bool.false 86049 131072 4798847 3496083456 86049 131072 4798847 3496083456 (ep542 rfl rfl) rfl)) rfl)

noncomputable def ep544 := @ep487 1322633425 4294967296 65517554921 114559662686208 Bool.true 2302240995 8589934592 130693135309 229119325372416 Bool.false 99532247359377375232 23174157217 8589934592 280273452047 76373108457472 Bool.true 34210559851568824320 3982633335 17179869184 560402700965 152746216914944 (ep488 (BSN.head_sum_c_succ qz127 5 6 rfl rfl) (ep535 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep536 ep543) rfl rfl

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz248 qz329 qz322)

noncomputable def ep545 := @Enclosure.Complex.IsNear.of_eq qz164 (Complex.mk (@HMul.hMul Real Real Real qz0 qz110 (Real.cos qz181)) (@HMul.hMul Real Real Real qz0 qz110 (@Neg.neg Real Real.instNeg (Real.sin qz181)))) Bool.false 6460988597 17179869184 80407696905 152746216914944 Bool.false 324047681 8589934592 19841117855 38186554228736 (BSN.cpow_neg_s_mk qz140 35467 1000 7 qz141 rfl)

noncomputable def ep546 := @Enclosure.Real.IsNear.mulLit_ff qz140 qz115 35467 1000 0 1 4381766428990711 2251799813685248 500000000026673 13336500000000000000 155408109937013547037 2251799813685248000 17733500000946011291 13336500000000000000000 qz176 (BSN.isNear_log_sfrac 7 1 4381766428990711 2251799813685248 500000000026673 13336500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz114) Bool.false 4594615115045363777536 2361183241434822606848 1000000000053346 26673000000000000000 4381766428990711 2251799813685248 500000000026673 13336500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 36674 65536 24973259072661432 36028797018963968 26673 1000000000000000 rfl rfl rfl rfl (ep276 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep547 := nat_lit 382127757611640206778983580392772926490351149635639196215207526400000000

noncomputable def ep548 := nat_lit 590461238897247749036501370706178418148525544671234560000000000000000

noncomputable def ep549 := nat_lit 999854808881795473779850279761833375750107779116253991276019712000000000

noncomputable def ep550 := BSN.sin_dyadic_bound_f 394819800 268435456 3 2 131072 53399 ep547 ep175 ep548 ep549 ep178 ep548 130417 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 394819800) qz292 0 2 ep547 ep175 ep548 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 394819800) qz293 0 2 ep549 ep178 ep548 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4522971) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep551 := @Enclosure.Real.IsNear.cos_image qz181 qz358 Bool.false 4522971 65536 175 131072 Bool.false 130417 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 155408109937013547037 2251799813685248000 17733500000946011291 13336500000000000000000 4522971 65536 175 131072 (ep546 rfl) rfl) (Enclosure.sfrac_false_div 4522971 65536) (BSN.cos_reduce3 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13891486770538188111872) qz354) 226375608064910080 72057594037927936 Bool.false 130417 131072 10 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q3 4522971 65536 226375608064910080 72057594037927936 10 13891486770538188111872 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 130417 131072 13891486770538188111872 9444732965739290427392 394819800 268435456 53399 53346 (ep550 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep552 := nat_lit 212555625890421113876784878605187705124927761150764546590670848000000000

noncomputable def ep553 := nat_lit 636485955193468846132281633074150758538486232362951170652012544000000000

noncomputable def ep554 := BSN.cos_dyadic_bound_f 394819800 268435456 3 2 131072 53399 ep552 ep208 ep548 ep553 ep210 ep548 13082 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 394819800) qz304 0 2 ep552 ep208 ep548 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 394819800) qz305 0 2 ep553 ep210 ep548 rfl rfl rfl rfl) rfl rfl

noncomputable def ep555 := @Enclosure.Real.IsNear.sin_image qz181 qz358 Bool.false 4522971 65536 175 131072 Bool.true 13082 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 155408109937013547037 2251799813685248000 17733500000946011291 13336500000000000000000 4522971 65536 175 131072 (ep546 rfl) rfl) (Enclosure.sfrac_false_div 4522971 65536) (BSN.sin_reduce3 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13891486770538188111872) qz354) 226375608064910080 72057594037927936 Bool.false 13082 131072 10 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q3 4522971 65536 226375608064910080 72057594037927936 10 13891486770538188111872 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 13082 131072 13891486770538188111872 9444732965739290427392 394819800 268435456 53399 53346 (ep554 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep556 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz110 (Real.cos qz181)) (@HMul.hMul Real Real Real qz0 qz110 (@Neg.neg Real Real.instNeg (Real.sin qz181))) Bool.false 6460988597 17179869184 80407696905 152746216914944 Bool.false 324047681 8589934592 19841117855 38186554228736 (@Enclosure.Real.IsNear.mulLit_ff qz110 (Real.cos qz181) 49541 131072 1 131072 130417 131072 4798847 3496083456 6460988597 17179869184 80407696905 152746216914944 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz181) Bool.false 130417 131072 4798847 3496083456 130417 131072 4798847 3496083456 (ep551 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz110 (@Neg.neg Real Real.instNeg (Real.sin qz181)) 49541 131072 1 131072 6541 65536 4798847 3496083456 324047681 8589934592 19841117855 38186554228736 qz324 (@Enclosure.Real.IsNear.neg (Real.sin qz181) Bool.true 6541 65536 4798847 3496083456 (@Enclosure.Real.IsNear.recentre' (Real.sin qz181) Bool.true 13082 131072 4798847 3496083456 6541 65536 4798847 3496083456 (ep555 rfl rfl) rfl)) rfl)

noncomputable def ep557 := @ep485 6460988597 17179869184 80407696905 152746216914944 Bool.false 324047681 8589934592 19841117855 38186554228736 Bool.false 453628458885397348352 52809303031 17179869184 640954600999 152746216914944 Bool.true 28643463082610262016 3334537973 17179869184 639767172385 152746216914944 (ep486 (BSN.head_sum_c_succ qz127 6 7 rfl rfl) (ep544 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep545 ep556) rfl rfl

noncomputable def ep558 := @Enclosure.Complex.IsNear.mul qz160 (@HAdd.hAdd Complex Complex Complex qz8 qz161 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.true 22200945036969500680617 345839862108982870016000 85429613095459500141367 ep478 Bool.false

noncomputable abbrev qz182 := (Complex.re qz349)

noncomputable abbrev qz183 := (Complex.im qz349)

noncomputable def ep559 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz182 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz161 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz183 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz161 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 18611326902754573185 1383359448435931480064 1588346568015166003121

noncomputable def ep560 := nat_lit 6511472923787929476661248

noncomputable def ep561 := nat_lit 101741764434186398072832000

noncomputable def ep562 := nat_lit 30711887081098558883159587048344424166719488

noncomputable def ep563 := @Enclosure.Real.IsNear.mulLit_tf qz182 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz161 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 460397835 17179869184 13097244937 26955214749696 121273334633

noncomputable abbrev qz359 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz413 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable abbrev qz184 := (Real.cos qz359)

noncomputable abbrev qz185 := (@Neg.neg Real Real.instNeg (Real.sin qz359))

noncomputable abbrev qz360 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable def ep564 := @Enclosure.Complex.IsNear.of_eq qz160 (Complex.mk (@HMul.hMul Real Real Real qz0 qz360 qz184) (@HMul.hMul Real Real Real qz0 qz360 qz185)) Bool.true 460397835 17179869184 13097244937 26955214749696 Bool.false 3028245327 8589934592 415209869 842350460928 (BSN.cpow_neg_s_mk qz140 35467 1000 8 qz141 rfl)

noncomputable abbrev qz361 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz88)

noncomputable def ep565 := @Enclosure.Real.IsNear.inv_image qz361 370727 131072 1 131072 23170 23171 65536 (@Enclosure.Real.IsNear.of_eq qz361 (Real.sqrt qz362) Bool.false 370727 131072 1 131072 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz362) Bool.false 370727 131072 1 131072 370727 131072 1 131072 (BSN.sqrt_enclosure 8 1 185363 185364 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep566 := BSN.log_dyadic_bound 0 16 1 0 1 65536 26673 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz363 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz186 := qz363

noncomputable def ep567 := @Enclosure.Real.IsNear.mulLit_ff qz140 qz186 35467 1000 0 1 9364972152248037 4503599627370496 1000000000080019 26673000000000000000 332147467323781128279 4503599627370496000 35467000002838033873 26673000000000000000000 qz176 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000080019 26673000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz362) Bool.false 4909942519757818822656 2361183241434822606848 1000000000080019 26673000000000000000 9364972152248037 4503599627370496 1000000000080019 26673000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 65536 24973259072661432 36028797018963968 26673 1000000000000000 rfl rfl rfl rfl (ep566 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep568 := nat_lit 226874989141921812577451233225754553754707903070390622311579425122024161

noncomputable def ep569 := nat_lit 672445938175843324831468241607825866519848022408665989511581235411681

noncomputable def ep570 := nat_lit 679280075549413751082690763194048009531084013166354534955715112895249121

noncomputable def ep571 := BSN.cos_dyadic_bound_f 401288923 268435456 3 2 131072 53399 ep568 ep208 ep569 ep570 ep210 ep569 9935 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 401288923) qz304 0 2 ep568 ep208 ep569 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 401288923) qz305 0 2 ep570 ep210 ep569 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz187 := qz359

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9666763) qz12)

noncomputable def ep572 := @Enclosure.Real.IsNear.cos_image qz187 qz364 Bool.false 9666763 131072 175 131072 Bool.true 9935 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz187 Bool.false 332147467323781128279 4503599627370496000 35467000002838033873 26673000000000000000000 9666763 131072 175 131072 (ep567 rfl) rfl) (Enclosure.sfrac_false_div 9666763 131072) (BSN.cos_reduce2 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28238197616665612517376) qz67) 226375608064910080 72057594037927936 Bool.false 9935 131072 11 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q2 9666763 131072 226375608064910080 72057594037927936 11 28238197616665612517376 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 9935 131072 28238197616665612517376 18889465931478580854784 401288923 268435456 53399 53346 (ep571 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep573 := nat_lit 407837023704918587979547045213071936065258347108776187369233700231314145

noncomputable def ep574 := nat_lit 1067055863898692555515753217452585257339406393248609317222117130986584801

noncomputable def ep575 := BSN.sin_dyadic_bound_f 401288923 268435456 3 2 131072 53399 ep573 ep175 ep569 ep574 ep178 ep569 130694 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 401288923) qz292 0 2 ep573 ep175 ep569 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 401288923) qz293 0 2 ep574 ep178 ep569 rfl rfl rfl rfl) rfl rfl

noncomputable def ep576 := @Enclosure.Real.IsNear.sin_image qz187 qz364 Bool.false 9666763 131072 175 131072 Bool.true 130694 131072 1 26673 (@Enclosure.Real.IsNear.recentre' qz187 Bool.false 332147467323781128279 4503599627370496000 35467000002838033873 26673000000000000000000 9666763 131072 175 131072 (ep567 rfl) rfl) (Enclosure.sfrac_false_div 9666763 131072) (BSN.sin_reduce2 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28238197616665612517376) qz67) 226375608064910080 72057594037927936 Bool.false 130694 131072 11 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q2 9666763 131072 226375608064910080 72057594037927936 11 28238197616665612517376 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 130694 131072 28238197616665612517376 18889465931478580854784 401288923 268435456 53399 53346 (ep575 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz188 := (Real.sin qz359)

noncomputable def ep577 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz360 qz184) (@HMul.hMul Real Real Real qz0 qz360 qz185) Bool.true 460397835 17179869184 13097244937 26955214749696 Bool.false 3028245327 8589934592 415209869 842350460928 (@Enclosure.Real.IsNear.mulLit_ft qz360 qz184 46341 131072 1 131072 9935 131072 4798847 3496083456 460397835 17179869184 13097244937 26955214749696 (@Enclosure.Real.IsNear.recentre' qz360 Bool.false 46341 131072 1 131072 46341 131072 1 131072 (ep565 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz184 Bool.true 9935 131072 4798847 3496083456 9935 131072 4798847 3496083456 (ep572 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz360 qz185 46341 131072 1 131072 65347 65536 4798847 3496083456 3028245327 8589934592 415209869 842350460928 (@Enclosure.Real.IsNear.recentre' qz360 Bool.false 46341 131072 1 131072 46341 131072 1 131072 (ep565 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz188 Bool.true 65347 65536 4798847 3496083456 (@Enclosure.Real.IsNear.recentre' qz188 Bool.true 130694 131072 4798847 3496083456 65347 65536 4798847 3496083456 (ep576 rfl rfl) rfl)) rfl)

noncomputable def ep578 := @ep563 241566353088 0 1 18611326902754573185 1383359448435931480064 1588346568015166003121 ep560 (@Enclosure.Complex.IsNear.re_isNear qz160 Bool.true 460397835 17179869184 13097244937 26955214749696 Bool.false 3028245327 8589934592 415209869 842350460928 (ep564 ep577))

noncomputable def ep579 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz161 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 121273334633 241566353088 0 1 Bool.false

noncomputable def ep580 := @Enclosure.Complex.IsNear.addLitP qz161 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) Bool.false 1250158089 2516316178 0 1 Bool.true 283736000

noncomputable def ep581 := @ep580 1258158089 0 1 Bool.false 1 192 0 1 Bool.false 35467 96000 0 1 Bool.false 242546669266 121273334633 241566353088 0 1 Bool.false 17384436942563 17384436942563 120783176544000 0 1

noncomputable abbrev qz189 := (@HDiv.hDiv Complex Complex Complex qz264 qz350 (@HSub.hSub Complex Complex Complex qz254 qz330 (1 : Complex)))

noncomputable def ep582 := @Enclosure.Complex.IsNear.addLitP qz189 qz41 Bool.true 16000000 5032632356 0 1 Bool.true 1134944000 5032632356 0 1

noncomputable def ep583 := @Enclosure.Complex.IsNear.of_eq qz189 (Complex.mk (Enclosure.sfrac Bool.true 16000000 5032632356) (Enclosure.sfrac Bool.true 1134944000 5032632356)) Bool.true 16000000 5032632356 0 1 Bool.true 1134944000 5032632356 0 1

noncomputable def ep584 := @ep582 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 5000632356 1250158089 2516316178 0 1 Bool.true 1134944000 283736000 1258158089 0 1 (ep583 (BSN.N_div_s_sub_one_mk qz140 35467 1000 8 qz141 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 16000000 5032632356) (Enclosure.sfrac Bool.true 1134944000 5032632356) Bool.true 16000000 5032632356 0 1 Bool.true 1134944000 5032632356 0 1 (Enclosure.Real.IsNear.const Bool.true 16000000 5032632356) (Enclosure.Real.IsNear.const Bool.true 1134944000 5032632356))) qz43 rfl

noncomputable abbrev qz365 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz406 (@Nat.cast Complex Complex.instNatCast 8) 1))

noncomputable abbrev qz190 := qz365

noncomputable def ep585 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz8 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) qz190)) Bool.false 1 192 0 1

noncomputable def ep586 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) qz190) Bool.false 0 1 0 1 Bool.false

noncomputable def ep587 := @ep586 0 1 0 1 Bool.false 1 192 0 1 Bool.false 35467 96000 0 1 Bool.false 1 1 192 0 1 Bool.false 35467 35467 96000 0

noncomputable def ep588 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (Complex.mk qz44 qz44) Bool.false 0 1 0 1 Bool.false

noncomputable def ep589 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) qz190 Bool.false 1 192 0 1 Bool.false 35467 96000 0 1

noncomputable abbrev qz191 := (Complex.re qz365)

noncomputable abbrev qz192 := (Complex.im qz365)

noncomputable def ep590 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)))) qz191) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)))) qz192) 1 192 0 1 0 1 0

noncomputable def ep591 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)))) qz191 1 24 0 1 1 8 0 1 1

noncomputable def ep592 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep593 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep594 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)) qz127 Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 (BSN.ascPochhammer_one_eval qz127)

noncomputable def ep595 := ep594 (@Enclosure.Complex.IsNear.of_eq qz127 (Complex.mk qz32 qz140) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 (BSN.s_crit_mk qz140 Bool.false 35467 1000 qz141) (@Enclosure.Complex.IsNear.mk qz32 qz140 Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 qz33 qz176))

noncomputable def ep596 := @ep593 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep300) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep595)

noncomputable def ep597 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 35467 1000 0 1 0 1 0

noncomputable def ep598 := @ep597 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep300) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep595)

noncomputable def ep599 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)))) 35467 12000 0 1 0 1 0 1 35467

noncomputable def ep600 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 35467 1000 0 1 35467 12000 0

noncomputable def ep601 := @ep600 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep300) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep595)

noncomputable def ep602 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep603 := @ep602 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep300) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep595)

noncomputable def ep604 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 35467 12000 0 1 (@ep592 1 24 0 1 (ep596 rfl) (ep598 rfl) rfl rfl) (@ep599 35467 12000 0 1 (ep601 rfl) (ep603 rfl) rfl rfl)

noncomputable def ep605 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 35467 12000 0 1 ep604

noncomputable abbrev qz193 := (@Enclosure.Complex.IsNear.of_eq qz365 (Complex.mk (Enclosure.sfrac Bool.false 1 8) qz279) Bool.false 1 8 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 8 1 8 EMRow05.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 8) qz279 Bool.false 1 8 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 8) qz280))

noncomputable def ep606 := @ep591 192 0 1 ep605 (@Enclosure.Complex.IsNear.re_isNear qz190 Bool.false 1 8 0 1 Bool.false 0 1 0 1 qz193)

noncomputable def ep607 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)))) qz192 35467 12000 0 1 0 1 0 1 0

noncomputable def ep608 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 35467 12000 0 1 ep604

noncomputable def ep609 := @ep607 1 0 1 ep608 (@Enclosure.Complex.IsNear.im_isNear qz190 Bool.false 1 8 0 1 Bool.false 0 1 0 1 qz193)

noncomputable def ep610 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)))) qz192) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)))) qz191) 0 1 0 1 35467 96000 0

noncomputable def ep611 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)))) qz192 1 24 0 1 0 1 0 1 0

noncomputable def ep612 := @ep611 1 0 1 ep605 (@Enclosure.Complex.IsNear.im_isNear qz190 Bool.false 1 8 0 1 Bool.false 0 1 0 1 qz193)

noncomputable def ep613 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz46)) ↑qz119) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)))) qz191 35467 12000 0 1 1 8 0 1 35467

noncomputable def ep614 := @ep613 96000 0 1 ep608 (@Enclosure.Complex.IsNear.re_isNear qz190 Bool.false 1 8 0 1 Bool.false 0 1 0 1 qz193)

noncomputable def ep615 := @ep587 1 (@ep588 0 1 0 1 (BSN.bern_sum_base qz127 8) qz61) (ep589 (@ep590 1 1 1 192 0 1 (ep606 rfl) (ep609 rfl) rfl rfl) (@ep610 1 35467 35467 96000 0 1 (ep612 rfl) (ep614 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep616 := ep581 (ep584 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep585 Bool.false 35467 96000 0 1 (BSN.bern_sum_succ qz127 8 0 1 1 rfl rfl) (ep615 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep617 := @Enclosure.Real.IsNear.mulLit_ff qz183 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz161 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 3028245327 8589934592 415209869 842350460928 17384436942563

noncomputable def ep618 := @ep617 120783176544000 0 1 17548113311280857384367 345839862108982870016000 7218189785560343754247 ep561 (@Enclosure.Complex.IsNear.im_isNear qz160 Bool.true 460397835 17179869184 13097244937 26955214749696 Bool.false 3028245327 8589934592 415209869 842350460928 (ep564 ep577))

noncomputable def ep619 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz8 qz161 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))) Bool.false 121273334633 241566353088 0 1 Bool.false

noncomputable def ep620 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz182 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz161 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz183 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz161 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1))))))) 533583808736668303407 138335944843593148006400 227688228728579011553531

noncomputable def ep621 := nat_lit 3255736461893964738330624000

noncomputable def ep622 := nat_lit 16565344441178818514572106643897280182091776

noncomputable def ep623 := @Enclosure.Real.IsNear.mulLit_tf qz182 (Complex.im (@HAdd.hAdd Complex Complex Complex qz8 qz161 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 460397835 17179869184 13097244937 26955214749696 17384436942563

noncomputable def ep624 := @ep623 120783176544000 0 1 533583808736668303407 138335944843593148006400 227688228728579011553531 ep621 (@Enclosure.Complex.IsNear.re_isNear qz160 Bool.true 460397835 17179869184 13097244937 26955214749696 Bool.false 3028245327 8589934592 415209869 842350460928 (ep564 ep577))

noncomputable def ep625 := @Enclosure.Real.IsNear.mulLit_ff qz183 (Complex.re (@HAdd.hAdd Complex Complex Complex qz8 qz161 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz16 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz16 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz73 qz162 (@HSub.hSub Nat Nat Nat qz72 (@HMul.hMul Nat Nat Nat qz16 2 k) 1)))))) 3028245327 8589934592 415209869 842350460928 121273334633

noncomputable def ep626 := @ep625 241566353088 0 1 122415136297363169997 691679724217965740032 50353885386161093077 203483528868372796145664 (@Enclosure.Complex.IsNear.im_isNear qz160 Bool.true 460397835 17179869184 13097244937 26955214749696 Bool.false 3028245327 8589934592 415209869 842350460928 (ep564 ep577))

noncomputable abbrev qz366 := (ep616 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep627 := @ep558 23949443450735965695993 138335944843593148006400 344450131635718833595177 ep479 (@ep559 ep560 17548113311280857384367 345839862108982870016000 7218189785560343754247 ep561 ep562 22200945036969500680617 345839862108982870016000 85429613095459500141367 ep478 (ep578 (@ep579 17384436942563 120783176544000 0 1 qz366) rfl) (ep618 (@ep619 17384436942563 120783176544000 0 1 qz366) rfl) rfl rfl) (@ep620 ep621 122415136297363169997 691679724217965740032 50353885386161093077 203483528868372796145664 ep622 23949443450735965695993 138335944843593148006400 344450131635718833595177 ep479 (ep624 (@ep619 17384436942563 120783176544000 0 1 qz366) rfl) (ep626 (@ep579 17384436942563 120783176544000 0 1 qz366) rfl) rfl rfl)

noncomputable def ep628 := @ep482 ep474 ep475 (@ep483 152746216914944 (BSN.head_sum_c_eq qz127 8) (ep484 (BSN.head_sum_c_succ qz127 7 8 rfl rfl) (ep557 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep627 rfl rfl rfl

noncomputable def ep629 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz127 1 8) Bool.false 1040878283489508383463383 345839862108982870016000 ep358 ep359 Bool.true 2900962461632761324807 138335944843593148006400 ep474 ep475 (@ep476 ep359 Bool.true 2900962461632761324807 138335944843593148006400 ep474 ep475 (BSN.zetaApproximant_eq_folded' qz127 1 8 rfl) (ep628 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep630 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))))) qz126)) (Complex.im (zetaApproximant qz127 1 8)) 5 32768 2878391

noncomputable def ep631 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))))) qz126)) Bool.true 20 131072 2878391

noncomputable def ep632 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))))) qz126) qz331 Bool.false 1647079 131072 103

noncomputable def ep633 := nat_lit 276634687633597653630350868591659362022121693900801616604393764292772096

noncomputable def ep634 := nat_lit 827907123125710899699895979612695266840841475399264397364418624893337856

noncomputable def ep635 := BSN.cos_dyadic_bound_f 421615794 268435456 3 2 131072 53399 ep633 ep208 ep470 ep634 ep210 ep470 20 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 421615794) qz304 0 2 ep633 ep208 ep470 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 421615794) qz305 0 2 ep634 ep210 ep470 rfl rfl rfl rfl) rfl rfl

noncomputable def ep636 := @ep632 131072 Bool.true 20 131072 1 26673 (@ep363 1647079 131072 103 131072 ep468 rfl) (Enclosure.sfrac_false_div 1647079 131072) (BSN.sin_reduce3 qz331 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29668573958805355757568) qz67) 226375608064910080 72057594037927936 Bool.false 20 131072 1 1000000000000000 53346 26673 (BSN.sin_reduce_arg_pos_rat_q3 1647079 131072 226375608064910080 72057594037927936 1 29668573958805355757568 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 20 131072 29668573958805355757568 18889465931478580854784 421615794 268435456 53399 53346 (ep635 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep637 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz127 1 8) Bool.false 1040878283489508383463383 345839862108982870016000 ep358 ep359 Bool.true 2900962461632761324807 138335944843593148006400 ep474 ep475 (@ep476 ep359 Bool.true 2900962461632761324807 138335944843593148006400 ep474 ep475 (BSN.zetaApproximant_eq_folded' qz127 1 8 rfl) (ep628 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow05.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 8 qz140) Bool.false ep344 ep345 ep346 ep347 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 8 qz140) ep348 Bool.false ep344 ep345 ep346 ep347 (@Eq.refl Real ep348) (@ep349 Bool.false ep344 ep345 ep346 ep347 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz5 (Complex.im (@HSub.hSub Complex Complex Complex qz6 qz124 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz8 qz125 (@Nat.cast Complex Complex.instNatCast j))))) qz126) (zetaApproximant qz127 1 8)) (@ep351 ep345 ep352 ep347 2900962461632761324807 ep353 ep354 ep355 ep356 ep344 ep345 ep346 ep347 (@ep357 3496083456 1040878283489508383463383 345839862108982870016000 ep358 ep359 ep350 ep345 ep352 ep347 (@ep360 3496083456 131071 131072 2878391 3496083456 (ep473 rfl rfl) rfl) ep629 rfl) (@ep630 3496083456 2900962461632761324807 138335944843593148006400 ep474 ep475 2900962461632761324807 ep353 ep354 ep355 (@ep631 3496083456 5 32768 2878391 3496083456 (ep636 rfl rfl) rfl) ep637 rfl) rfl rfl))

theorem EMRow05.d11 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow05.d12 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow05.d13 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow05.d14 : @Eq Nat (Nat.pow 7 (Nat.succ (Nat.mul 2 3))) 823543 := @Eq.refl Nat 823543

noncomputable abbrev qz416 := (@HAdd.hAdd Complex Complex Complex qz419 qz423 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz367 := qz416

noncomputable abbrev qz194 := (@HDiv.hDiv Real Real Real qz251 (@Norm.norm Complex Complex.instNorm qz367) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz259) qz307))

noncomputable abbrev qz195 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz196 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz368 := (@HPow.hPow Complex Complex Complex qz407 (@Nat.cast Complex Complex.instNatCast 7) (@HSub.hSub Complex Complex Complex qz397 qz408 qz409))

noncomputable abbrev qz197 := qz368

noncomputable def ep638 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 7))) (@HMul.hMul Real Real Real qz0 qz194 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197))) 494583 33554432 75677 1207959552 7867040747383 17592186044416 268303611

noncomputable def ep639 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 7)) 123 8192 1 221184 4021 4096 127 32768 494583 33554432

noncomputable abbrev qz369 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz370 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz198 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz369 qz370 2))

noncomputable def ep640 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz198 96 162 0 1 3321 131072 1 131072 123 8192 1 221184

noncomputable def ep641 := nat_lit 781950621441006189802102638025

noncomputable def ep642 := nat_lit 19807040628566084398385987584

noncomputable def ep643 := nat_lit 26986075409044041160201671

noncomputable def ep644 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz199 := qz370

noncomputable abbrev qz371 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz199 1)

noncomputable def ep645 := @Enclosure.Real.IsNear.mulLit_ff qz371 qz199 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep641 ep642 ep643 ep644

noncomputable def ep646 := ep645 (@Enclosure.Real.IsNear.of_eq qz371 qz199 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz199) (@Enclosure.Real.IsNear.of_eq qz199 qz249 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz250)) (@Enclosure.Real.IsNear.of_eq qz199 qz249 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz250) rfl

noncomputable abbrev qz200 := (@HPow.hPow Real Nat Real qz369 qz370 2)

noncomputable def ep647 := @Enclosure.Real.IsNear.inv_image qz200 ep641 ep642 ep643 ep644 1660 1661 65536 (@Enclosure.Real.IsNear.of_eq qz200 (@HMul.hMul Real Real Real qz0 qz371 qz199) Bool.false ep641 ep642 ep643 ep644 (BSN.pow_succ_r qz199 1 2 rfl) ep646) rfl rfl rfl

noncomputable def ep648 := ep640 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz198 Bool.false 3321 131072 1 131072 3321 131072 1 131072 (ep647 rfl rfl rfl) rfl)

noncomputable def ep649 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 7)) (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 7)) (Complex.re (zetaApproximant qz11 1 7))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 7)) (Complex.im (zetaApproximant qz11 1 7))))) Bool.false 4021 4096 127 32768

noncomputable def ep650 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 7)) (Complex.re (zetaApproximant qz11 1 7))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 7)) (Complex.im (zetaApproximant qz11 1 7))))) Bool.false 128672 131072 508 131072

noncomputable def ep651 := nat_lit 25245420053112320473911627876881173241

noncomputable def ep652 := nat_lit 26195566153743082965362457496780800000

noncomputable def ep653 := nat_lit 19770484188754171107729361113087671852291597268697783

noncomputable def ep654 := nat_lit 2604704866406561590613295950903938795114850156544000000

noncomputable def ep655 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 7)) (Complex.re (zetaApproximant qz11 1 7))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 7)) (Complex.im (zetaApproximant qz11 1 7)))) ep651 ep652 ep653 ep654 64082 64590

noncomputable def ep656 := nat_lit 1975518218540486591405797776505249260931645801

noncomputable def ep657 := nat_lit 2059383924314953736784638511112953790464000000

noncomputable def ep658 := nat_lit 660444670321833276550316469694906407059770865628131

noncomputable def ep659 := nat_lit 93025173800234342521903426817997814111244648448000000

noncomputable def ep660 := nat_lit 146708209684748024587479502502101044920541289

noncomputable def ep661 := nat_lit 32950142789039259788554216177807260647424000000

noncomputable def ep662 := nat_lit 255606683948567872864099992326058490923602606222023

noncomputable def ep663 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz11 1 7)) (Complex.re (zetaApproximant qz11 1 7))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz11 1 7)) (Complex.im (zetaApproximant qz11 1 7))) ep656 ep657 ep658 ep659 ep660 ep661 ep662

noncomputable def ep664 := nat_lit 520940973281312318122659190180787759022970031308800000

noncomputable def ep665 := nat_lit 65395735911847296280589246010480102826984511973901914774967130176125191627012277534720000000

noncomputable def ep666 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz11 1 7)) (Complex.re (zetaApproximant qz11 1 7)) 44446802118268155461651 45380435479564910592000 417046021976728046659471 ep53 44446802118268155461651 45380435479564910592000 417046021976728046659471 ep53 ep656

noncomputable def ep667 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz11 1 7)) (Complex.im (zetaApproximant qz11 1 7)) 12112316445864020794733 181521741918259642368000 1155754666352712536028763 ep181 12112316445864020794733 181521741918259642368000 1155754666352712536028763 ep181 ep660

noncomputable def ep668 := @ep638 123145302310912 272674879949697449984 8126344679287 17592186044416 71848682707 1108307720798208 (@ep639 75677 1207959552 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz198) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow05.d11 EMRow05.d12 rfl) (ep648 rfl)) (ep649 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz11 1 7)) (@ep650 4021 4096 127 32768 (@ep655 65536 (@ep663 ep664 ep665 ep651 ep652 ep653 ep654 (@ep666 ep657 ep658 ep659 ep335 ep335 rfl) (@ep667 ep661 ep662 ep664 ep343 ep343 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz201 := (@Norm.norm Complex Complex.instNorm qz367)

noncomputable abbrev qz372 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep669 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz194 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz201 qz372) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197))) Bool.false 7867040747383 17592186044416 268303611 123145302310912 (BSN.zrb_shape_eq qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) qz37 3)

noncomputable def ep670 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz201 qz372) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) 597511 65536 1 458752 13166353 268435456 61 268435456

noncomputable def ep671 := @Enclosure.Real.IsNear.mulLit_ff qz201 qz372 4182577 131072 1 131072 2 7 0 1 597511 65536

noncomputable abbrev qz373 := (Complex.re qz416)

noncomputable abbrev qz374 := (Complex.im qz416)

noncomputable abbrev qz202 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz248 qz373 qz373) (@HMul.hMul Real Real Real qz248 qz374 qz374))

noncomputable abbrev qz203 := qz367

noncomputable def ep672 := @Enclosure.Real.IsNear.of_eq qz201 (Real.sqrt qz202) Bool.false 4182577 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz203)

noncomputable def ep673 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz202) Bool.false 4182577 131072 1 131072 4182577

noncomputable def ep674 := @Enclosure.Real.IsNear.sqrt_image qz202 254570381 250000 0 1 2091288 2091289 65536

noncomputable abbrev qz204 := (@HMul.hMul Real Real Real qz248 qz373 qz373)

noncomputable abbrev qz205 := (@HMul.hMul Real Real Real qz248 qz374 qz374)

noncomputable def ep675 := @Enclosure.Real.IsNear.addLit_ff qz204 qz205 49 4 0 1 251507881 250000 0 1

noncomputable abbrev qz206 := qz373

noncomputable def ep676 := @Enclosure.Real.IsNear.mulLit_ff qz206 qz206 7 2 0 1 7 2 0 1 49 4

noncomputable def ep677 := @Enclosure.Complex.IsNear.of_eq qz203 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz37) Bool.false 7 2 0 1 Bool.false 31718 1000 0 1 (BSN.s_add_nat_mk qz37 Bool.false 31718 1000 3 qz38)

noncomputable abbrev qz207 := (ep677 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz258 Bool.false 7 2 0 1 Bool.false 31718 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz301))

noncomputable def ep678 := @ep676 0 1 (@Enclosure.Complex.IsNear.re_isNear qz203 Bool.false 7 2 0 1 Bool.false 31718 1000 0 1 qz207)

noncomputable def ep679 := ep678 (@Enclosure.Complex.IsNear.re_isNear qz203 Bool.false 7 2 0 1 Bool.false 31718 1000 0 1 qz207)

noncomputable abbrev qz208 := qz374

noncomputable def ep680 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 31718 1000 0 1 31718 1000 0 1 251507881 250000

noncomputable def ep681 := @ep680 0 1 (@Enclosure.Complex.IsNear.im_isNear qz203 Bool.false 7 2 0 1 Bool.false 31718 1000 0 1 qz207)

noncomputable def ep682 := ep681 (@Enclosure.Complex.IsNear.im_isNear qz203 Bool.false 7 2 0 1 Bool.false 31718 1000 0 1 qz207)

noncomputable def ep683 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197))))) Bool.false 13166353 268435456

noncomputable def ep684 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197))))) Bool.false 13166353 268435456

noncomputable def ep685 := nat_lit 6323766408184878939580842600925136820531341186954497

noncomputable def ep686 := nat_lit 2628600284633256486943563766667673600000000000000000000

noncomputable def ep687 := nat_lit 90529322828094477386472193134483264842372680483097297857687

noncomputable def ep688 := nat_lit 4144882737144625493950367778592181625578481254400000000000000000000

noncomputable def ep689 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)))) ep685 ep686 ep687 ep688

noncomputable def ep690 := nat_lit 268858460741849228024331117743348890664433516082801

noncomputable def ep691 := nat_lit 164287517789578530433972735416729600000000000000000000

noncomputable def ep692 := nat_lit 1300085696538735993571498826538171024014347487883768462857

noncomputable def ep693 := nat_lit 86351723690513031123965995387337117199551692800000000000000000000

noncomputable def ep694 := nat_lit 224670115146143476799060524114617174433378325514409

noncomputable def ep695 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197))) ep690 ep691 ep692 ep693 ep694

noncomputable def ep696 := nat_lit 292066698292584054104840418518630400000000000000000000

noncomputable def ep697 := nat_lit 28125209394235149695040249460651055689684001064676411640551

noncomputable def ep698 := nat_lit 115435098475756936145740948812492454773370464306282350937735344826166331549151972556800000000000000000000

noncomputable def ep699 := nat_lit 16396903998677592673061401

noncomputable def ep700 := nat_lit 405323966463344640000000000

noncomputable def ep701 := nat_lit 94712333667894523600156027

noncomputable def ep702 := nat_lit 508974627139250521374720000000000

noncomputable def ep703 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) ep699 ep700 ep701 ep702 ep699 ep700 ep701

noncomputable def ep704 := nat_lit 14988999804728248671292403

noncomputable def ep705 := nat_lit 540431955284459520000000000

noncomputable def ep706 := nat_lit 249044556464631751985920193

noncomputable def ep707 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197) Bool.true ep699 ep700 ep701 ep702 Bool.false ep704 ep705 ep706

noncomputable def ep708 := nat_lit 2035898508557002085498880000000000

noncomputable def ep709 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197 Bool.true ep699 ep700 ep701 ep702 Bool.false ep704 ep705 ep706 ep708

noncomputable def ep710 := nat_lit 387790192106095635333120000000

noncomputable def ep711 := nat_lit 35282880243879526729917677

noncomputable def ep712 := nat_lit 810647932926689280000000000

noncomputable def ep713 := nat_lit 175228657883097336549969179

noncomputable abbrev qz209 := (Complex.re qz368)

noncomputable abbrev qz210 := (Complex.im qz368)

noncomputable def ep714 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz209) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz210) 2212508663577192341151 720575940379279360000000 5408003601025413581083 ep710 ep711 ep712 ep713

noncomputable def ep715 := nat_lit 1017949254278501042749440000000000

noncomputable def ep716 := nat_lit 23630429036311744703856419797342714823966720000000

noncomputable def ep717 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz209 754211143 120000000 0 1 8800620426171 18014398509481984 50192874447067 22621094539522245394432 2212508663577192341151

noncomputable def ep718 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) 754211143 120000000 0 1 0 1 0 1 754211143

noncomputable def ep719 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 2262633429 500000 0 1 754211143 120000000 0

noncomputable def ep720 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz44) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow05.d13 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz44 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz45)

noncomputable abbrev qz375 := (@HAdd.hAdd Complex Complex Complex qz399 qz402 qz410)

noncomputable abbrev qz211 := qz375

noncomputable def ep721 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) qz211) Bool.true 2262633429 500000 0 1 Bool.true 3965866172279 125000000 0 1

noncomputable abbrev qz212 := (Complex.re qz375)

noncomputable abbrev qz213 := (Complex.im qz375)

noncomputable def ep722 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz212) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz213) 251320381 100000 0 1 251507881 125000 0 1

noncomputable def ep723 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz212 251320381 250000 0 1 5 2 0 1 251320381 100000

noncomputable abbrev qz376 := (@HAdd.hAdd Complex Complex Complex qz399 qz402 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz214 := qz376

noncomputable def ep724 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz214) Bool.true 251320381 250000 0 1 Bool.false 15859 250 0 1

noncomputable abbrev qz215 := (Complex.re qz376)

noncomputable abbrev qz216 := (Complex.im qz376)

noncomputable def ep725 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz215) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz216) 3 4 0 1 251507881 250000 0 1

noncomputable def ep726 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz215 1 2 0 1 3 2 0 1 3 4

noncomputable def ep727 := @ep726 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep302)

noncomputable def ep728 := @Enclosure.Complex.IsNear.of_eq qz214 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz37) Bool.false 3 2 0 1 Bool.false 31718 1000 0 1 (BSN.s_add_nat_mk qz37 Bool.false 31718 1000 1 qz38)

noncomputable abbrev qz217 := (ep728 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz258 Bool.false 3 2 0 1 Bool.false 31718 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz301))

noncomputable def ep729 := ep727 (@Enclosure.Complex.IsNear.re_isNear qz214 Bool.false 3 2 0 1 Bool.false 31718 1000 0 1 qz217)

noncomputable def ep730 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz216 31718 1000 0 1 31718 1000 0 1 251507881 250000

noncomputable def ep731 := @ep730 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep302)

noncomputable def ep732 := ep731 (@Enclosure.Complex.IsNear.im_isNear qz214 Bool.false 3 2 0 1 Bool.false 31718 1000 0 1 qz217)

noncomputable def ep733 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) qz214 Bool.true 251320381 250000 0 1 Bool.false 15859 250 0 1 (@ep725 1005281524 251320381 250000 0 1 (ep729 rfl) (ep732 rfl) rfl rfl)

noncomputable def ep734 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz216) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz215) 15859 1000 0 1 47577 1000 0 1

noncomputable def ep735 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz216 1 2 0 1 31718 1000 0 1 15859 1000

noncomputable def ep736 := @ep735 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep302)

noncomputable def ep737 := ep736 (@Enclosure.Complex.IsNear.im_isNear qz214 Bool.false 3 2 0 1 Bool.false 31718 1000 0 1 qz217)

noncomputable def ep738 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1))) qz215 31718 1000 0 1 3 2 0 1 47577 1000

noncomputable def ep739 := @ep738 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 31718 1000 0 1 ep302)

noncomputable def ep740 := ep739 (@Enclosure.Complex.IsNear.re_isNear qz214 Bool.false 3 2 0 1 Bool.false 31718 1000 0 1 qz217)

noncomputable abbrev qz218 := (ep724 (BSN.ascPochhammer_succ_eval_c 1 2 qz259 rfl) (ep733 (@ep734 63436000 15859 250 0 1 (ep737 rfl) (ep740 rfl) rfl rfl)))

noncomputable def ep741 := @ep723 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 251320381 250000 0 1 Bool.false 15859 250 0 1 qz218)

noncomputable def ep742 := @Enclosure.Complex.IsNear.of_eq qz211 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz37) Bool.false 5 2 0 1 Bool.false 31718 1000 0 1 (BSN.s_add_nat_mk qz37 Bool.false 31718 1000 2 qz38)

noncomputable abbrev qz219 := (ep742 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz258 Bool.false 5 2 0 1 Bool.false 31718 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz301))

noncomputable def ep743 := ep741 (@Enclosure.Complex.IsNear.re_isNear qz211 Bool.false 5 2 0 1 Bool.false 31718 1000 0 1 qz219)

noncomputable def ep744 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz213 15859 250 0 1 31718 1000 0 1 251507881 125000

noncomputable def ep745 := @ep744 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 251320381 250000 0 1 Bool.false 15859 250 0 1 qz218)

noncomputable def ep746 := ep745 (@Enclosure.Complex.IsNear.im_isNear qz211 Bool.false 5 2 0 1 Bool.false 31718 1000 0 1 qz219)

noncomputable def ep747 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) qz211 Bool.true 2262633429 500000 0 1 Bool.true 3965866172279 125000000 0 1 (@ep722 56565835725000 2262633429 500000 0 1 (ep743 rfl) (ep746 rfl) rfl rfl)

noncomputable def ep748 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz213) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz212) 3985689922279 125000000 0 1 15859 100 0 1

noncomputable def ep749 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz213 251320381 250000 0 1 31718 1000 0 1 3985689922279 125000000

noncomputable def ep750 := @ep749 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 251320381 250000 0 1 Bool.false 15859 250 0 1 qz218)

noncomputable def ep751 := ep750 (@Enclosure.Complex.IsNear.im_isNear qz211 Bool.false 5 2 0 1 Bool.false 31718 1000 0 1 qz219)

noncomputable def ep752 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2))) qz212 15859 250 0 1 5 2 0 1 15859 100

noncomputable def ep753 := @ep752 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 251320381 250000 0 1 Bool.false 15859 250 0 1 qz218)

noncomputable def ep754 := ep753 (@Enclosure.Complex.IsNear.re_isNear qz211 Bool.false 5 2 0 1 Bool.false 31718 1000 0 1 qz219)

noncomputable abbrev qz220 := (ep721 (BSN.ascPochhammer_succ_eval_c 2 3 qz259 rfl) (ep747 (@ep748 396586617227900 3965866172279 125000000 0 1 (ep751 rfl) (ep754 rfl) rfl rfl)))

noncomputable def ep755 := @ep719 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep720) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2262633429 500000 0 1 Bool.true 3965866172279 125000000 0 1 qz220)

noncomputable def ep756 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3965866172279 125000000 0 1 0 1 0

noncomputable def ep757 := @ep756 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep720) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2262633429 500000 0 1 Bool.true 3965866172279 125000000 0 1 qz220)

noncomputable def ep758 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) 3965866172279 90000000000 0 1 0 1 0 1 3965866172279

noncomputable def ep759 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3965866172279 125000000 0 1 3965866172279 90000000000 0

noncomputable def ep760 := @ep759 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep720) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2262633429 500000 0 1 Bool.true 3965866172279 125000000 0 1 qz220)

noncomputable def ep761 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 2262633429 500000 0 1 0 1 0

noncomputable def ep762 := @ep761 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep720) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2262633429 500000 0 1 Bool.true 3965866172279 125000000 0 1 qz220)

noncomputable def ep763 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 754211143 120000000 0 1 Bool.false 3965866172279 90000000000 0 1 (@ep718 754211143 120000000 0 1 (ep755 rfl) (ep757 rfl) rfl rfl) (@ep758 3965866172279 90000000000 0 1 (ep760 rfl) (ep762 rfl) rfl rfl)

noncomputable def ep764 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 754211143 120000000 0 1 Bool.false 3965866172279 90000000000 0 1 ep763

noncomputable def ep765 := @Enclosure.Complex.IsNear.re_isNear qz197 Bool.false 8800620426171 18014398509481984 50192874447067 22621094539522245394432 Bool.false 8896639147963 9007199254740992 44184208511101 11310547269761122697216

noncomputable abbrev qz377 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 823543)))

noncomputable def ep766 := @Enclosure.Complex.IsNear.of_eq qz197 (Complex.mk (@HMul.hMul Real Real Real qz0 qz377 qz111) (@HMul.hMul Real Real Real qz0 qz377 qz112)) Bool.false 8800620426171 18014398509481984 50192874447067 22621094539522245394432 Bool.false 8896639147963 9007199254740992 44184208511101

noncomputable abbrev qz378 := (Real.sqrt (@Nat.cast Real Real.instNatCast 823543))

noncomputable abbrev qz379 := (@Nat.cast Real Real.instNatCast 823543)

noncomputable def ep767 := @Enclosure.Real.IsNear.inv_image qz378 243603216659 268435456 1 268435456 147899 147900 134217728 (@Enclosure.Real.IsNear.of_eq qz378 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz379 qz88)) Bool.false 243603216659 268435456 1 268435456 (BSN.sqrt_natCast_div_one 823543) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz379 qz88)) Bool.false 243603216659 268435456 1 268435456 243603216659 268435456 1 268435456 (BSN.sqrt_enclosure 823543 1 121801608329 121801608330 134217728 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep768 := nat_lit 16010468250000000000000000

noncomputable def ep769 := nat_lit 9409844065408522077077504

noncomputable def ep770 := nat_lit 4835703278458516698824704

noncomputable def ep771 := BSN.log_dyadic_bound 3 11 8 7 769762406419069088025 134217728 64041873 19984785452821035495 646346515815 75110359 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 3) (BSN.artanhQ 11) 0 7 19984785452821035495 769762406419069088025 646346515815 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep772 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz115 31718 1000 0 1 4381800100863223 2251799813685248 500000064041873 32020936500000000000000 69490967799589853557 1125899906842624000 7929501015640063907 ep768 qz90 (BSN.isNear_log_sfrac 7 1 4381800100863223 2251799813685248 500000064041873 32020936500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz114) Bool.false ep769 ep770 1000000128083746 64041873000000000000000 4381800100863223 2251799813685248 500000064041873 32020936500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 75110359 134217728 24973259072661432 36028797018963968 64041873 1000000000000000 rfl rfl rfl rfl (ep771 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep773 := nat_lit 17769128959352151260266496

noncomputable def ep774 := nat_lit 38685626227668133590597632

noncomputable def ep775 := nat_lit 1123085597076883208532090602502486766315659903028169362374325291184907269593247275863120819238465

noncomputable def ep776 := nat_lit 3027761623417890041794943268495340122449333660440555301399931479087996461294057979657548758232596480

noncomputable def ep777 := nat_lit 16530679650990396029940119151377080790996346814798441178010081921255865985556431476200552001

noncomputable def ep778 := nat_lit 2941387895053354418847617389218363110791161942417029132551801841542122720389766250181021630445121

noncomputable def ep779 := nat_lit 55508963095994650766240626589081235578237783774743513858998743783279935123724396293721727234264268800

noncomputable def ep780 := BSN.sin_dyadic_bound_f 252514510057 549755813888 3 2 268435456 128208828 ep775 ep776 ep777 ep778 ep779 ep777 119008116 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 252514510057) (BSN.sinEvenQ 549755813888) 0 2 ep775 ep776 ep777 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 252514510057) (BSN.sinOddQ 549755813888) 0 2 ep778 ep779 ep777 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz380 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16567937803) (@Nat.cast Real Real.instNatCast 268435456))

noncomputable def ep781 := @Enclosure.Real.IsNear.cos_image qz116 qz380 Bool.false 16567937803 268435456 67 134217728 Bool.false 119008116 268435456 1 64041873 (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 69490967799589853557 1125899906842624000 7929501015640063907 ep768 16567937803 268435456 67 134217728 (ep772 rfl) rfl) (Enclosure.sfrac_false_div 16567937803 268435456) (BSN.cos_reduce3 qz380 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep773) (@Nat.cast Real Real.instNatCast ep774)) 226375608064910080 72057594037927936 Bool.false 119008116 268435456 9 1000000000000000 128083746 64041873 (BSN.sin_reduce_arg_pos_rat_q3 16567937803 268435456 226375608064910080 72057594037927936 9 ep773 ep774 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 119008116 268435456 ep773 ep774 252514510057 549755813888 128208828 128083746 (ep780 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep782 := nat_lit 623943789789224444916063641443226593322384833392011778404037610694691263492242067226834322044481

noncomputable def ep783 := nat_lit 336417958157543337977215918721704458049925962271172811266659053231999606810450886628616528692510720

noncomputable def ep784 := nat_lit 1871798308008371353956131044091377025805572507482405738329756811920231278744755088817550565029441

noncomputable def ep785 := nat_lit 15138808117089450208974716342476700612246668302202776506999657395439982306470289898287743791162982400

noncomputable def ep786 := BSN.cos_dyadic_bound_f 252514510057 549755813888 3 2 268435456 128208828 ep782 ep783 ep777 ep784 ep785 ep777 240613096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 252514510057) (BSN.cosEvenQ 549755813888) 0 2 ep782 ep783 ep777 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 252514510057) (BSN.cosOddQ 549755813888) 0 2 ep784 ep785 ep777 rfl rfl rfl rfl) rfl rfl

noncomputable def ep787 := @Enclosure.Real.IsNear.sin_image qz116 qz380 Bool.false 16567937803 268435456 67 134217728 Bool.true 240613096 268435456 1 64041873 (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 69490967799589853557 1125899906842624000 7929501015640063907 ep768 16567937803 268435456 67 134217728 (ep772 rfl) rfl) (Enclosure.sfrac_false_div 16567937803 268435456) (BSN.sin_reduce3 qz380 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep773) (@Nat.cast Real Real.instNatCast ep774)) 226375608064910080 72057594037927936 Bool.false 240613096 268435456 9 1000000000000000 128083746 64041873 (BSN.sin_reduce_arg_pos_rat_q3 16567937803 268435456 226375608064910080 72057594037927936 9 ep773 ep774 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 240613096 268435456 ep773 ep774 252514510057 549755813888 128208828 128083746 (ep786 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep788 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz377 qz111) (@HMul.hMul Real Real Real qz0 qz377 qz112) Bool.false 8800620426171 18014398509481984 50192874447067 22621094539522245394432 Bool.false 8896639147963 9007199254740992 44184208511101 11310547269761122697216 (@Enclosure.Real.IsNear.mulLit_ff qz377 qz111 295799 268435456 1 268435456 29752029 67108864 4425023219 8595554690924544 8800620426171 18014398509481984 50192874447067 22621094539522245394432 (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 295799 268435456 1 268435456 295799 268435456 1 268435456 (ep767 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 119008116 268435456 4425023219 8595554690924544 29752029 67108864 4425023219 8595554690924544 (ep781 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz377 qz112 295799 268435456 1 268435456 30076637 33554432 4425023219 8595554690924544 8896639147963 9007199254740992 44184208511101 11310547269761122697216 (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 295799 268435456 1 268435456 295799 268435456 1 268435456 (ep767 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz117 Bool.true 30076637 33554432 4425023219 8595554690924544 (@Enclosure.Real.IsNear.recentre' qz117 Bool.true 240613096 268435456 4425023219 8595554690924544 30076637 33554432 4425023219 8595554690924544 (ep787 rfl rfl) rfl)) rfl)

noncomputable def ep789 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz210 3965866172279 90000000000 0 1 8896639147963 9007199254740992 44184208511101 11310547269761122697216 ep711

noncomputable def ep790 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 754211143 120000000 0 1 Bool.false 3965866172279 90000000000 0 1 ep763

noncomputable def ep791 := @Enclosure.Complex.IsNear.im_isNear qz197 Bool.false 8800620426171 18014398509481984 50192874447067 22621094539522245394432 Bool.false 8896639147963 9007199254740992 44184208511101 11310547269761122697216

noncomputable def ep792 := nat_lit 193895096053047817666560000000

noncomputable def ep793 := nat_lit 3878009204802129498479301

noncomputable def ep794 := nat_lit 180143985094819840000000000

noncomputable def ep795 := nat_lit 199058222859070031888255693

noncomputable def ep796 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz210) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz209) 6709944380643720351709 1080863910568919040000000 4760603200529687628349 ep792 ep793 ep794 ep795

noncomputable def ep797 := nat_lit 5400356314818446241923864718276226491351040000000

noncomputable def ep798 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz210 754211143 120000000 0 1 8896639147963 9007199254740992 44184208511101 11310547269761122697216 6709944380643720351709

noncomputable def ep799 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3)))) qz209 3965866172279 90000000000 0 1 8800620426171 18014398509481984 50192874447067 22621094539522245394432 ep793

noncomputable abbrev qz381 := (@ep766 11310547269761122697216 (BSN.cpow_neg_s_sub_mk qz37 31718 1000 7 3 823543 qz38 rfl EMRow05.d14) ep788)

noncomputable def ep800 := ep709 (@ep714 ep715 ep716 ep699 ep700 ep701 ep702 (@ep717 720575940379279360000000 5408003601025413581083 ep710 ep764 (ep765 qz381) rfl) (@ep789 ep712 ep713 ep715 ep790 (ep791 qz381) rfl) rfl rfl) (@ep796 ep708 ep797 ep704 ep705 ep706 ep708 (@ep798 1080863910568919040000000 4760603200529687628349 ep792 ep764 (ep791 qz381) rfl) (@ep799 ep794 ep795 ep708 ep790 (ep765 qz381) rfl) rfl rfl)

noncomputable def ep801 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) ep704 ep705 ep706 ep708 ep704 ep705 ep706

noncomputable def ep802 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197) Bool.true ep699 ep700 ep701 ep702 Bool.false ep704 ep705 ep706

noncomputable def ep803 := @ep670 7867040747383 17592186044416 268303611 123145302310912 (@ep671 1 458752 (ep672 (@ep673 131072 1 131072 (ep674 (@ep675 1018281524 254570381 250000 0 1 (ep679 rfl) (ep682 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep683 61 268435456 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)) (@ep684 61 268435456 13166353 268435456 61 268435456 (@ep689 6583146 6583207 134217728 (@ep695 ep696 ep697 ep688 ep698 ep685 ep686 ep687 ep688 (@ep703 ep702 ep690 ep691 ep692 ep693 (@ep707 ep708 ep800) (@ep707 ep708 ep800) rfl) (@ep801 ep708 ep694 ep696 ep697 ep688 (@ep802 ep708 ep800) (@ep802 ep708 ep800) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow05.d15 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 7))) (@HMul.hMul Real Real Real qz0 qz194 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)))) Bool.false 8126344679287 17592186044416 71848682707 1108307720798208 := ep668 (ep669 ep803) rfl rfl

theorem EMRow05.d16 : @Eq Nat (Nat.pow 8 (Nat.succ (Nat.mul 2 3))) 2097152 := @Eq.refl Nat 2097152

noncomputable abbrev qz417 := (@HAdd.hAdd Complex Complex Complex qz419 qz426 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz382 := qz417

noncomputable abbrev qz221 := (@HDiv.hDiv Real Real Real qz251 (@Norm.norm Complex Complex.instNorm qz382) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz330) qz307))

noncomputable abbrev qz383 := (@HPow.hPow Complex Complex Complex qz407 (@Nat.cast Complex Complex.instNatCast 8) (@HSub.hSub Complex Complex Complex qz397 qz415 qz409))

noncomputable abbrev qz222 := qz383

noncomputable def ep804 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz127 1 8))) (@HMul.hMul Real Real Real qz0 qz221 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) 24261627 536870912 1190527 14495514624 107681552338547 246290604621824 364057453

noncomputable def ep805 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz127 1 8)) 123 8192 1 221184 197249 65536 299 65536 24261627 536870912

noncomputable def ep806 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz127 1 8)) (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz127 1 8)) (Complex.re (zetaApproximant qz127 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz127 1 8)) (Complex.im (zetaApproximant qz127 1 8))))) Bool.false 197249 65536 299 65536

noncomputable def ep807 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz127 1 8)) (Complex.re (zetaApproximant qz127 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz127 1 8)) (Complex.im (zetaApproximant qz127 1 8))))) Bool.false 394498 131072 598 131072

noncomputable def ep808 := nat_lit 3444655192087197702515255417668506758629

noncomputable def ep809 := nat_lit 380254949737275139722992383164416000000

noncomputable def ep810 := nat_lit 9320660696076413965245314550067947410353802681082380423

noncomputable def ep811 := nat_lit 340371994865487262644808185675822239147077241143296000000

noncomputable def ep812 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz127 1 8)) (Complex.re (zetaApproximant qz127 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz127 1 8)) (Complex.im (zetaApproximant qz127 1 8)))) ep808 ep809 ep810 ep811 196950 197548

noncomputable def ep813 := nat_lit 1083427601040065380626561838303712415294101804689

noncomputable def ep814 := nat_lit 119605210223560285465272021540924351840256000000

noncomputable def ep815 := nat_lit 289044607885525539188331723814656125144774073791031761

noncomputable def ep816 := nat_lit 10636624839546476957650255802369444973346163785728000000

noncomputable def ep817 := nat_lit 8415583203802410221475857034225509753587249

noncomputable def ep818 := nat_lit 19136833635769645674443523446547896294440960000

noncomputable def ep819 := nat_lit 71233243739596711218699387998951405721032319769364071

noncomputable def ep820 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz127 1 8)) (Complex.re (zetaApproximant qz127 1 8))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz127 1 8)) (Complex.im (zetaApproximant qz127 1 8))) ep813 ep814 ep815 ep816 ep817 ep818 ep819

noncomputable def ep821 := nat_lit 20734380305102984175543120307945708343475817794083582487126301240997630335300612660857405440000

noncomputable def ep822 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz127 1 8)) (Complex.re (zetaApproximant qz127 1 8)) 1040878283489508383463383 345839862108982870016000 ep358 ep359 1040878283489508383463383 345839862108982870016000 ep358 ep359 ep813

noncomputable def ep823 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz127 1 8)) (Complex.im (zetaApproximant qz127 1 8)) 2900962461632761324807 138335944843593148006400 ep474 ep475 2900962461632761324807 138335944843593148006400 ep474 ep475 ep817

noncomputable def ep824 := @ep804 246290604621824 63786503992510630592512 118811622248051 246290604621824 555986193535 6649846324789248 (@ep805 1190527 14495514624 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz198) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow05.d11 EMRow05.d12 rfl) (ep648 rfl)) (ep806 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz127 1 8)) (@ep807 197249 65536 299 65536 (@ep812 65536 (@ep820 ep811 ep821 ep808 ep809 ep810 ep811 (@ep822 ep814 ep815 ep816 ep629 ep629 rfl) (@ep823 ep818 ep819 ep811 ep637 ep637 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz223 := (@Norm.norm Complex Complex.instNorm qz382)

noncomputable def ep825 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz221 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz223 qz372) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) Bool.false 107681552338547 246290604621824 364057453 246290604621824 (BSN.zrb_shape_eq qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) qz140 3)

noncomputable def ep826 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz223 qz372) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) 4671311 458752 1 458752 23051677 536870912 73 536870912

noncomputable def ep827 := @Enclosure.Real.IsNear.mulLit_ff qz223 qz372 4671311 131072 1 131072 2 7 0 1 4671311 458752

noncomputable abbrev qz384 := (Complex.re qz417)

noncomputable abbrev qz385 := (Complex.im qz417)

noncomputable abbrev qz224 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz248 qz384 qz384) (@HMul.hMul Real Real Real qz248 qz385 qz385))

noncomputable abbrev qz225 := qz382

noncomputable def ep828 := @Enclosure.Real.IsNear.of_eq qz223 (Real.sqrt qz224) Bool.false 4671311 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz225)

noncomputable def ep829 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz224) Bool.false 4671311 131072 1 131072 4671311

noncomputable def ep830 := @Enclosure.Real.IsNear.sqrt_image qz224 1270158089 1000000 0 1 2335655 2335656 65536

noncomputable abbrev qz226 := (@HMul.hMul Real Real Real qz248 qz384 qz384)

noncomputable abbrev qz227 := (@HMul.hMul Real Real Real qz248 qz385 qz385)

noncomputable def ep831 := @Enclosure.Real.IsNear.addLit_ff qz226 qz227 49 4 0 1 1257908089 1000000 0 1

noncomputable abbrev qz228 := qz384

noncomputable def ep832 := @Enclosure.Real.IsNear.mulLit_ff qz228 qz228 7 2 0 1 7 2 0 1 49 4

noncomputable def ep833 := @Enclosure.Complex.IsNear.of_eq qz225 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz140) Bool.false 7 2 0 1 Bool.false 35467 1000 0 1 (BSN.s_add_nat_mk qz140 Bool.false 35467 1000 3 qz141)

noncomputable abbrev qz229 := (ep833 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz329 Bool.false 7 2 0 1 Bool.false 35467 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz351))

noncomputable def ep834 := @ep832 0 1 (@Enclosure.Complex.IsNear.re_isNear qz225 Bool.false 7 2 0 1 Bool.false 35467 1000 0 1 qz229)

noncomputable def ep835 := ep834 (@Enclosure.Complex.IsNear.re_isNear qz225 Bool.false 7 2 0 1 Bool.false 35467 1000 0 1 qz229)

noncomputable abbrev qz230 := qz385

noncomputable def ep836 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 35467 1000 0 1 35467 1000 0 1 1257908089 1000000

noncomputable def ep837 := @ep836 0 1 (@Enclosure.Complex.IsNear.im_isNear qz225 Bool.false 7 2 0 1 Bool.false 35467 1000 0 1 qz229)

noncomputable def ep838 := ep837 (@Enclosure.Complex.IsNear.im_isNear qz225 Bool.false 7 2 0 1 Bool.false 35467 1000 0 1 qz229)

noncomputable def ep839 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))))) Bool.false 23051677 536870912

noncomputable def ep840 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))))) Bool.false 23051677 536870912

noncomputable def ep841 := nat_lit 15879609206986983153587397494060641207044963776637925409

noncomputable def ep842 := nat_lit 8613397412686254856416669750616632852480000000000000000000

noncomputable def ep843 := nat_lit 39084109176136876055924151227694087054470939672120141841383

noncomputable def ep844 := nat_lit 3404440202392781683677049151012722518046172774400000000000000000000

noncomputable def ep845 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)))) ep841 ep842 ep843 ep844

noncomputable def ep846 := nat_lit 19798206646230741931037564208625799290252261607517433801

noncomputable def ep847 := nat_lit 10766746765857818570520837188270791065600000000000000000000

noncomputable def ep848 := nat_lit 1924859619575601105648934681586205730603478729651994366931

noncomputable def ep849 := nat_lit 170222010119639084183852457550636125902308638720000000000000000000

noncomputable def ep850 := nat_lit 22802161112438671531858959533334319357308050346654649

noncomputable def ep851 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222))) ep846 ep847 ep848 ep849 ep850

noncomputable def ep852 := nat_lit 4785220784825697142453705417009240473600000000000000000000

noncomputable def ep853 := nat_lit 21737658689809405294276207258147127496346854780750166769

noncomputable def ep854 := nat_lit 126090377866399321617668487074545278446154547200000000000000000000

noncomputable def ep855 := nat_lit 94984295040229522186868727234209452041635083356501623124522817718653321256870274499375792128000000000000000000000

noncomputable def ep856 := nat_lit 4449517574550160368322088099

noncomputable def ep857 := nat_lit 103762935414616227840000000000

noncomputable def ep858 := nat_lit 121639567160138111085173447

noncomputable def ep859 := nat_lit 922556258771352881725440000000000

noncomputable def ep860 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) ep856 ep857 ep858 ep859 ep856 ep857 ep858

noncomputable def ep861 := nat_lit 151003844694228469607388907

noncomputable def ep862 := nat_lit 69175290276410818560000000000

noncomputable def ep863 := nat_lit 8095435679864280925100363

noncomputable def ep864 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222) Bool.true ep856 ep857 ep858 ep859 Bool.false ep861 ep862 ep863

noncomputable def ep865 := nat_lit 205012501949189529272320000000000

noncomputable def ep866 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222 Bool.true ep856 ep857 ep858 ep859 Bool.false ep861 ep862 ep863 ep865

noncomputable def ep867 := nat_lit 46116860184273879040000000

noncomputable def ep868 := nat_lit 24119117876375238737920000000

noncomputable def ep869 := nat_lit 4406831226806129076475004849

noncomputable def ep870 := nat_lit 118928640219020912490771197

noncomputable abbrev qz231 := (Complex.re qz383)

noncomputable abbrev qz232 := (Complex.im qz383)

noncomputable def ep871 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) 18971710108458351932037 ep867 70873906957312381553 ep868 ep869 ep857 ep870

noncomputable def ep872 := nat_lit 205197779872999172002468605894035450115349544960000000

noncomputable def ep873 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231 3772474267 480000000 0 1 15086949915933 288230376151711744 958142852409 2562656274364869115904 18971710108458351932037

noncomputable def ep874 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)))) 3772474267 480000000 0 1 0 1 0 1 3772474267

noncomputable def ep875 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 11317422801 2000000 0 1 3772474267 480000000 0

noncomputable abbrev qz386 := (@HAdd.hAdd Complex Complex Complex qz399 qz414 qz410)

noncomputable abbrev qz233 := qz386

noncomputable def ep876 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2)) qz233) Bool.true 11317422801 2000000 0 1 Bool.true 44410290942563 1000000000 0 1

noncomputable abbrev qz234 := (Complex.re qz386)

noncomputable abbrev qz235 := (Complex.im qz386)

noncomputable def ep877 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2))) qz234) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 1257158089 400000 0 1 1257908089 500000 0 1

noncomputable def ep878 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2))) qz234 1257158089 1000000 0 1 5 2 0 1 1257158089 400000

noncomputable abbrev qz387 := (@HAdd.hAdd Complex Complex Complex qz399 qz414 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz236 := qz387

noncomputable def ep879 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz4 (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)) qz236) Bool.true 1257158089 1000000 0 1 Bool.false 35467 500 0 1

noncomputable abbrev qz237 := (Complex.re qz387)

noncomputable abbrev qz238 := (Complex.im qz387)

noncomputable def ep880 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 3 4 0 1 1257908089 1000000 0 1

noncomputable def ep881 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) qz237 1 2 0 1 3 2 0 1 3 4

noncomputable def ep882 := @ep881 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep595)

noncomputable def ep883 := @Enclosure.Complex.IsNear.of_eq qz236 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz140) Bool.false 3 2 0 1 Bool.false 35467 1000 0 1 (BSN.s_add_nat_mk qz140 Bool.false 35467 1000 1 qz141)

noncomputable abbrev qz239 := (ep883 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz329 Bool.false 3 2 0 1 Bool.false 35467 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz351))

noncomputable def ep884 := ep882 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 3 2 0 1 Bool.false 35467 1000 0 1 qz239)

noncomputable def ep885 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 35467 1000 0 1 35467 1000 0 1 1257908089 1000000

noncomputable def ep886 := @ep885 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep595)

noncomputable def ep887 := ep886 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 3 2 0 1 Bool.false 35467 1000 0 1 qz239)

noncomputable def ep888 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)) qz236 Bool.true 1257158089 1000000 0 1 Bool.false 35467 500 0 1 (@ep880 5028632356 1257158089 1000000 0 1 (ep884 rfl) (ep887 rfl) rfl rfl)

noncomputable def ep889 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) qz237) 35467 2000 0 1 106401 2000 0 1

noncomputable def ep890 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 35467 1000 0 1 35467 2000

noncomputable def ep891 := @ep890 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep595)

noncomputable def ep892 := ep891 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 3 2 0 1 Bool.false 35467 1000 0 1 qz239)

noncomputable def ep893 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1))) qz237 35467 1000 0 1 3 2 0 1 106401 2000

noncomputable def ep894 := @ep893 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 35467 1000 0 1 ep595)

noncomputable def ep895 := ep894 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 3 2 0 1 Bool.false 35467 1000 0 1 qz239)

noncomputable abbrev qz240 := (ep879 (BSN.ascPochhammer_succ_eval_c 1 2 qz330 rfl) (ep888 (@ep889 283736000 35467 500 0 1 (ep892 rfl) (ep895 rfl) rfl rfl)))

noncomputable def ep896 := @ep878 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1257158089 1000000 0 1 Bool.false 35467 500 0 1 qz240)

noncomputable def ep897 := @Enclosure.Complex.IsNear.of_eq qz233 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz140) Bool.false 5 2 0 1 Bool.false 35467 1000 0 1 (BSN.s_add_nat_mk qz140 Bool.false 35467 1000 2 qz141)

noncomputable abbrev qz241 := (ep897 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz329 Bool.false 5 2 0 1 Bool.false 35467 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz351))

noncomputable def ep898 := ep896 (@Enclosure.Complex.IsNear.re_isNear qz233 Bool.false 5 2 0 1 Bool.false 35467 1000 0 1 qz241)

noncomputable def ep899 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 35467 500 0 1 35467 1000 0 1 1257908089 500000

noncomputable def ep900 := @ep899 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1257158089 1000000 0 1 Bool.false 35467 500 0 1 qz240)

noncomputable def ep901 := ep900 (@Enclosure.Complex.IsNear.im_isNear qz233 Bool.false 5 2 0 1 Bool.false 35467 1000 0 1 qz241)

noncomputable def ep902 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2)) qz233 Bool.true 11317422801 2000000 0 1 Bool.true 44410290942563 1000000000 0 1 (@ep877 1131742280100000 11317422801 2000000 0 1 (ep898 rfl) (ep901 rfl) rfl rfl)

noncomputable def ep903 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2))) qz234) 44587625942563 1000000000 0 1 35467 200 0 1

noncomputable def ep904 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 1257158089 1000000 0 1 35467 1000 0 1 44587625942563 1000000000

noncomputable def ep905 := @ep904 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1257158089 1000000 0 1 Bool.false 35467 500 0 1 qz240)

noncomputable def ep906 := ep905 (@Enclosure.Complex.IsNear.im_isNear qz233 Bool.false 5 2 0 1 Bool.false 35467 1000 0 1 qz241)

noncomputable def ep907 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2))) qz234 35467 500 0 1 5 2 0 1 35467 200

noncomputable def ep908 := @ep907 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1257158089 1000000 0 1 Bool.false 35467 500 0 1 qz240)

noncomputable def ep909 := ep908 (@Enclosure.Complex.IsNear.re_isNear qz233 Bool.false 5 2 0 1 Bool.false 35467 1000 0 1 qz241)

noncomputable abbrev qz242 := (ep876 (BSN.ascPochhammer_succ_eval_c 2 3 qz330 rfl) (ep902 (@ep903 8882058188512600 44410290942563 1000000000 0 1 (ep906 rfl) (ep909 rfl) rfl rfl)))

noncomputable def ep910 := @ep875 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep720) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 11317422801 2000000 0 1 Bool.true 44410290942563 1000000000 0 1 qz242)

noncomputable def ep911 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 44410290942563 1000000000 0 1 0 1 0

noncomputable def ep912 := @ep911 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep720) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 11317422801 2000000 0 1 Bool.true 44410290942563 1000000000 0 1 qz242)

noncomputable def ep913 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)))) 44410290942563 720000000000 0 1 0 1 0 1 44410290942563

noncomputable def ep914 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 44410290942563 1000000000 0 1 44410290942563 720000000000 0

noncomputable def ep915 := @ep914 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep720) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 11317422801 2000000 0 1 Bool.true 44410290942563 1000000000 0 1 qz242)

noncomputable def ep916 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 11317422801 2000000 0 1 0 1 0

noncomputable def ep917 := @ep916 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep720) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 11317422801 2000000 0 1 Bool.true 44410290942563 1000000000 0 1 qz242)

noncomputable def ep918 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 3772474267 480000000 0 1 Bool.false 44410290942563 720000000000 0 1 (@ep874 3772474267 480000000 0 1 (ep910 rfl) (ep912 rfl) rfl rfl) (@ep913 44410290942563 720000000000 0 1 (ep915 rfl) (ep917 rfl) rfl rfl)

noncomputable def ep919 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 3772474267 480000000 0 1 Bool.false 44410290942563 720000000000 0 1 ep918

noncomputable def ep920 := @Enclosure.Complex.IsNear.re_isNear qz222 Bool.true 15086949915933 288230376151711744 958142852409 2562656274364869115904 Bool.false 99229956239323 144115188075855872 2677952287519 1281328137182434557952

noncomputable abbrev qz388 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2097152)))

noncomputable def ep921 := @Enclosure.Complex.IsNear.of_eq qz222 (Complex.mk (@HMul.hMul Real Real Real qz0 qz388 qz184) (@HMul.hMul Real Real Real qz0 qz388 qz185)) Bool.true 15086949915933 288230376151711744 958142852409 2562656274364869115904 Bool.false 99229956239323 144115188075855872 2677952287519

noncomputable abbrev qz389 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2097152))

noncomputable abbrev qz390 := (@Nat.cast Real Real.instNatCast 2097152)

noncomputable def ep922 := @Enclosure.Real.IsNear.inv_image qz389 777472127993 536870912 1 536870912 185363 185364 268435456 (@Enclosure.Real.IsNear.of_eq qz389 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz390 qz88)) Bool.false 777472127993 536870912 1 536870912 (BSN.sqrt_natCast_div_one 2097152) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz390 qz88)) Bool.false 777472127993 536870912 1 536870912 777472127993 536870912 1 536870912 (BSN.sqrt_enclosure 2097152 1 388736063996 388736063997 268435456 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep923 := nat_lit 20111124560928025897598976

noncomputable def ep924 := nat_lit 9671406556917033397649408

noncomputable def ep925 := BSN.log_dyadic_bound 0 16 1 0 1 268435456 109252608 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep926 := @Enclosure.Real.IsNear.mulLit_ff qz140 qz186 35467 1000 0 1 9364972152248037 4503599627370496 244140705019 26673000000000000000 332147467323781128279 4503599627370496000 8658938384908873 26673000000000000000000 qz176 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 244140705019 26673000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz362) Bool.false ep923 ep924 1000000327757824 109252608000000000000000 9364972152248037 4503599627370496 244140705019 26673000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 268435456 24973259072661432 36028797018963968 109252608 1000000000000000 rfl rfl rfl rfl (ep925 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep927 := nat_lit 115663997117360643663462400

noncomputable def ep928 := nat_lit 77371252455336267181195264

noncomputable def ep929 := nat_lit 312095576673376184640575972950134389775735299847028589358806224129044485360078783778135042914858745609600842771278475351132646538165970583452882598629376

noncomputable def ep930 := nat_lit 1495322550399040784419355283626494329519667708093549445215377558311688463489449843662618815857177555772710955730243566617516213067140175522969484368281600

noncomputable def ep931 := nat_lit 388884606442292932799566752705714971390038508886557302180634442085593730651550687269094151755711876905608812872428104788986956217182644846827933696

noncomputable def ep932 := nat_lit 1889636567883988658705080175859535960953102494238065616847348070243762275356952358423976004171397976290895722154342003443221218888738991351521665670451200

noncomputable def ep933 := nat_lit 136074352086312711382161330810010983986289761436512999514599357806363650177539935773298312243003157575316696971452164562193975389109755972590223077513625600

noncomputable def ep934 := BSN.cos_dyadic_bound_f 1643684258814 1099511627776 4 3 536870912 218718601 ep929 ep930 ep931 ep932 ep933 ep931 40695579 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1643684258814) (BSN.cosEvenQ 1099511627776) 0 3 ep929 ep930 ep931 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1643684258814) (BSN.cosOddQ 1099511627776) 0 3 ep932 ep933 ep931 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz391 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39595063605) (@Nat.cast Real Real.instNatCast 536870912))

noncomputable def ep935 := @Enclosure.Real.IsNear.cos_image qz187 qz391 Bool.false 39595063605 536870912 11 33554432 Bool.true 40695579 536870912 1 109252608 (@Enclosure.Real.IsNear.recentre' qz187 Bool.false 332147467323781128279 4503599627370496000 8658938384908873 26673000000000000000000 39595063605 536870912 11 33554432 (ep926 rfl) rfl) (Enclosure.sfrac_false_div 39595063605 536870912) (BSN.cos_reduce2 qz391 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep927) (@Nat.cast Real Real.instNatCast ep928)) 226375608064910080 72057594037927936 Bool.false 40695579 536870912 11 1000000000000000 218505216 109252608 (BSN.sin_reduce_arg_pos_rat_q2 39595063605 536870912 226375608064910080 72057594037927936 11 ep927 ep928 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 40695579 536870912 ep927 ep928 1643684258814 1099511627776 218718601 218505216 (ep934 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep936 := nat_lit 810378936110887518921503752582669190540432808310527885258618796313379457704533806206843549760834829026766836829291384775238388360418796083024235593732096

noncomputable def ep937 := nat_lit 19439193155187530197451618687144426283755680205216142787799908258051950025362847967614044606143308225045242424493166366027710769872822281798603296787660800

noncomputable def ep938 := nat_lit 4047763125603092664281214368674769176784796503464002087812954291774699231650261466809074392531740597939447199931013402505463668941858371000617797010067456

noncomputable def ep939 := nat_lit 680371760431563556910806654050054919931448807182564997572996789031818250887699678866491561215015787876583484857260822810969876945548779862951115387568128000

noncomputable def ep940 := BSN.sin_dyadic_bound_f 1643684258814 1099511627776 4 3 536870912 218718601 ep936 ep937 ep931 ep938 ep939 ep931 535326298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 1643684258814) (BSN.sinEvenQ 1099511627776) 0 3 ep936 ep937 ep931 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 1643684258814) (BSN.sinOddQ 1099511627776) 0 3 ep938 ep939 ep931 rfl rfl rfl rfl) rfl rfl

noncomputable def ep941 := @Enclosure.Real.IsNear.sin_image qz187 qz391 Bool.false 39595063605 536870912 11 33554432 Bool.true 535326298 536870912 1 109252608 (@Enclosure.Real.IsNear.recentre' qz187 Bool.false 332147467323781128279 4503599627370496000 8658938384908873 26673000000000000000000 39595063605 536870912 11 33554432 (ep926 rfl) rfl) (Enclosure.sfrac_false_div 39595063605 536870912) (BSN.sin_reduce2 qz391 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep927) (@Nat.cast Real Real.instNatCast ep928)) 226375608064910080 72057594037927936 Bool.false 535326298 536870912 11 1000000000000000 218505216 109252608 (BSN.sin_reduce_arg_pos_rat_q2 39595063605 536870912 226375608064910080 72057594037927936 11 ep927 ep928 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 535326298 536870912 ep927 ep928 1643684258814 1099511627776 218718601 218505216 (ep940 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep942 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz388 qz184) (@HMul.hMul Real Real Real qz0 qz388 qz185) Bool.true 15086949915933 288230376151711744 958142852409 2562656274364869115904 Bool.false 99229956239323 144115188075855872 2677952287519 1281328137182434557952 (@Enclosure.Real.IsNear.mulLit_ft qz388 qz184 370727 536870912 1 536870912 40695579 536870912 301595 894997364736 15086949915933 288230376151711744 958142852409 2562656274364869115904 (@Enclosure.Real.IsNear.recentre' qz388 Bool.false 370727 536870912 1 536870912 370727 536870912 1 536870912 (ep922 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz184 Bool.true 40695579 536870912 1235333120 3665909205958656 40695579 536870912 301595 894997364736 (ep935 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz388 qz185 370727 536870912 1 536870912 267663149 268435456 301595 894997364736 99229956239323 144115188075855872 2677952287519 1281328137182434557952 (@Enclosure.Real.IsNear.recentre' qz388 Bool.false 370727 536870912 1 536870912 370727 536870912 1 536870912 (ep922 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz188 Bool.true 267663149 268435456 301595 894997364736 (@Enclosure.Real.IsNear.recentre' qz188 Bool.true 535326298 536870912 1235333120 3665909205958656 267663149 268435456 301595 894997364736 (ep941 rfl rfl) rfl)) rfl)

noncomputable def ep943 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 44410290942563 720000000000 0 1 99229956239323 144115188075855872 2677952287519 1281328137182434557952 ep869

noncomputable def ep944 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 3772474267 480000000 0 1 Bool.false 44410290942563 720000000000 0 1 ep918

noncomputable def ep945 := @Enclosure.Complex.IsNear.im_isNear qz222 Bool.true 15086949915933 288230376151711744 958142852409 2562656274364869115904 Bool.false 99229956239323 144115188075855872 2677952287519 1281328137182434557952

noncomputable def ep946 := nat_lit 69175290276410818560000000

noncomputable def ep947 := nat_lit 36178676814562858106880000000

noncomputable def ep948 := nat_lit 74446203911384547131284031

noncomputable def ep949 := nat_lit 23058430092136939520000000000

noncomputable def ep950 := nat_lit 14183800946673630001728089

noncomputable def ep951 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231) 374342456428382111001241 ep946 594265064289365457269 ep947 ep948 ep949 ep950

noncomputable def ep952 := nat_lit 615037505847568587816960000000000

noncomputable def ep953 := nat_lit 3481911596525770676328705992114159869377904640000000

noncomputable def ep954 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 3772474267 480000000 0 1 99229956239323 144115188075855872 2677952287519 1281328137182434557952 374342456428382111001241

noncomputable def ep955 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3)))) qz231 44410290942563 720000000000 0 1 15086949915933 288230376151711744 958142852409 2562656274364869115904 ep948

noncomputable abbrev qz392 := (@ep921 1281328137182434557952 (BSN.cpow_neg_s_sub_mk qz140 35467 1000 8 3 2097152 qz141 rfl EMRow05.d16) ep942)

noncomputable def ep956 := ep866 (@ep871 ep859 ep872 ep856 ep857 ep858 ep859 (@ep873 ep867 70873906957312381553 ep868 ep919 (ep920 qz392) rfl) (@ep943 ep857 ep870 ep859 ep944 (ep945 qz392) rfl) rfl rfl) (@ep951 ep952 ep953 ep861 ep862 ep863 ep865 (@ep954 ep946 594265064289365457269 ep947 ep919 (ep945 qz392) rfl) (@ep955 ep949 ep950 ep952 ep944 (ep920 qz392) rfl) rfl rfl)

noncomputable def ep957 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (Complex.im (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) ep861 ep862 ep863 ep865 ep861 ep862 ep863

noncomputable def ep958 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222) Bool.true ep856 ep857 ep858 ep859 Bool.false ep861 ep862 ep863

noncomputable def ep959 := @ep826 107681552338547 246290604621824 364057453 246290604621824 (@ep827 1 458752 (ep828 (@ep829 131072 1 131072 (ep830 (@ep831 5080632356 1270158089 1000000 0 1 (ep835 rfl) (ep838 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep839 73 536870912 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)) (@ep840 73 536870912 23051677 536870912 73 536870912 (@ep845 11525802 11525875 268435456 (@ep851 ep852 ep853 ep854 ep855 ep841 ep842 ep843 ep844 (@ep860 ep859 ep846 ep847 ep848 ep849 (@ep864 ep865 ep956) (@ep864 ep865 ep956) rfl) (@ep957 ep865 ep850 ep852 ep853 ep854 (@ep958 ep865 ep956) (@ep958 ep865 ep956) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow05.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz127 1 8))) (@HMul.hMul Real Real Real qz0 qz221 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)))) Bool.false 118811622248051 246290604621824 555986193535 6649846324789248 := ep824 (ep825 ep959) rfl rfl

noncomputable def EMRow05.d18 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz393 := (EMRow05.d3 qz401 qz413 (@Enclosure.dec_le_dec qz401 qz413 31718 1000 35467 1000 (@Eq.refl Real qz401) (@Eq.refl Real qz413) rfl rfl rfl) 7 8 1 1)

noncomputable abbrev qz243 := qz393

noncomputable def ep960 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz243 (@Enclosure.dec_nonneg qz37 31718 1000 qz38) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 7 rfl)

noncomputable abbrev qz244 := (Zeta.Certificates.ZIntervalEM.fstVal qz393)

noncomputable def ep961 := @Enclosure.Real.IsNear.neg_val qz244 ep38 ep39

noncomputable def ep962 := @Enclosure.Real.IsNear.of_eq qz244 (hardyZApproximantEM 1 7 qz37) Bool.true

noncomputable abbrev qz245 := (Zeta.Certificates.ZIntervalEM.sndVal qz393)

noncomputable def ep963 := BSN.mul_neg_of_neg_pos_r qz244 qz245 (@ep961 ep40 ep41 (@ep962 ep38 ep39 ep40 ep41 (@Eq.refl Real (hardyZApproximantEM 1 7 qz37)) EMRow05.d8) rfl rfl rfl)

noncomputable def ep964 := @Enclosure.Real.IsNear.pos_val qz245 ep344 ep345

noncomputable def ep965 := @Enclosure.Real.IsNear.of_eq qz245 (hardyZApproximantEM 1 8 qz140) Bool.false

noncomputable def ep966 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz244) (BSN.hardyZErrorBoundStrong 1 7 qz37)

noncomputable def ep967 := @Enclosure.norm_gt_of_isNear qz244 (BSN.hardyZErrorBoundStrong 1 7 qz37) Bool.true

noncomputable def ep968 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 7 qz37) (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 7))) (@HMul.hMul Real Real Real qz0 qz194 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)))) Bool.false 8126344679287 17592186044416 71848682707 1108307720798208 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz11 1 7))) (@HMul.hMul Real Real Real qz0 qz194 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz11 (@ascPochhammer Complex Complex.instSemiring 3))) qz197)))))

noncomputable def ep969 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz245) (BSN.hardyZErrorBoundStrong 1 8 qz140)

noncomputable def ep970 := @Enclosure.norm_gt_of_isNear qz245 (BSN.hardyZErrorBoundStrong 1 8 qz140) Bool.false

noncomputable def ep971 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 8 qz140) (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz127 1 8))) (@HMul.hMul Real Real Real qz0 qz221 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)))) Bool.false 118811622248051 246290604621824 555986193535 6649846324789248 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz56 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz127 1 8))) (@HMul.hMul Real Real Real qz0 qz221 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz4 (@HMul.hMul Complex Complex Complex qz4 (@HDiv.hDiv Complex Complex Complex qz15 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz195)) ↑qz196) (@Polynomial.eval Complex Complex.instSemiring qz127 (@ascPochhammer Complex Complex.instSemiring 3))) qz222)))))

noncomputable def ep972 := @List.cons EMRow05.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz243 (ep960 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 8 rfl) (ep963 (@ep964 ep346 ep347 (@ep965 ep344 ep345 ep346 ep347 (@Eq.refl Real (hardyZApproximantEM 1 8 qz140)) EMRow05.d10) rfl rfl rfl)) (ep966 (hardyZErrorBoundEM 1 7 qz37) (BSN.hardyZErrorBoundEM_le_strong 1 7 qz37 rfl) (@ep967 Bool.false ep38 ep39 ep40 ep41 8126344679287 17592186044416 71848682707 1108307720798208 (@ep962 ep38 ep39 ep40 ep41 (@Eq.refl Real (hardyZApproximantEM 1 7 qz37)) EMRow05.d8) (ep968 EMRow05.d15) rfl rfl rfl rfl rfl)) (ep969 (hardyZErrorBoundEM 1 8 qz140) (BSN.hardyZErrorBoundEM_le_strong 1 8 qz140 rfl) (@ep970 Bool.false ep344 ep345 ep346 ep347 118811622248051 246290604621824 555986193535 6649846324789248 (@ep965 ep344 ep345 ep346 ep347 (@Eq.refl Real (hardyZApproximantEM 1 8 qz140)) EMRow05.d10) (ep971 EMRow05.d17) rfl rfl rfl rfl rfl)))) (@List.nil EMRow05.d0)

noncomputable abbrev qz394 := (@Enclosure.dec_le_dec qz401 qz413 31718 1000 35467 1000 (@Eq.refl Real qz401) (@Eq.refl Real qz413) rfl rfl rfl)

noncomputable abbrev qz246 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep972 (@List.IsChain.singleton EMRow05.d1 EMRow05.d18 (EMRow05.d2 qz258 qz329 qz394))))

noncomputable abbrev qz395 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep973 := And (@Eq (Option Real) (@Option.map qz395 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz395 qz246)) (@Option.some Real qz37))

noncomputable def ep974 := ep973 (@Eq (Option Real) (@Option.map qz395 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz395 qz246)) (@Option.some Real qz140))

noncomputable def ep975 := @And.intro (@Eq Nat (@List.length qz395 qz246) 1) ep974

noncomputable def ep976 := @And.intro (@Eq (Option Real) (@Option.map qz395 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz395 qz246)) (@Option.some Real qz37))

noncomputable def ep977 := @ep976 (@Eq (Option Real) (@Option.map qz395 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz395 qz246)) (@Option.some Real qz140))

noncomputable abbrev qz247 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep972 (@List.IsChain.singleton EMRow05.d1 EMRow05.d18 (EMRow05.d2 qz258 qz329 qz394)))

theorem EMRow05.d19 : Zeta.Certificates.BatchSpec 1 31718 1000 35467 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz395 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz395 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz395 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz37)) (@Eq (Option Real) (@Option.map qz395 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz395 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz140)))) qz247 (ep975 (@Eq.refl Nat 1) (ep977 (@Eq.refl (Option Real) (@Option.some Real qz37)) (@Eq.refl (Option Real) (@Option.some Real qz140))))

theorem solution : Zeta.Certificates.BatchSpec 1 31718 1000 35467 1000 := EMRow05.d19
#print axioms solution
#check solution
