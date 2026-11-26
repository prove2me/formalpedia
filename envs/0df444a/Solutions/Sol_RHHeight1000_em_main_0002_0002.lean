-- Prove2me | solution 1 for RHHeight1000.em_main_0002_0002
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:36:39.284433+00:00
-- url     : https://prove2.me/submissions/901161e3-e786-4cac-8981-0c223a821f9a

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow02.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow02.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow02.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow02.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow02.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz249 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz249

noncomputable abbrev qz250 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz1 := qz250

noncomputable abbrev qz251 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz251 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138516661214455 2251799813685248 125000000009391 4695500000000000000 4138516661214455 2251799813685248 125000000009391 4695500000000000000 120446 65536

noncomputable abbrev qz2 := (@Enclosure.Real.IsNear.mulLit_ff qz250 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 65536 qz2 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 779317518150410741488063439345657628452599855445271348474342368876423347582876053728679783827237610085654588674605917415063316248867402488514697634436426745

noncomputable def ep10 := nat_lit 13198325246229587668616048586507268161410801335203869857947191811663857046415771104290097871102374067703089877156867761119753226876438075596795543285583799

noncomputable def ep11 := nat_lit 13338205139369261376383149914767634013226508915861991492218067381232119098362059104733250767410551174650894954010182016771344050520336484956804919489535

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 4 3 ep9 131072 37564 ep10 ep11 59189 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 3 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz252 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz3 := qz252

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138516661214455 2251799813685248 125000000009391 4695500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000075128 37564000000000000000 4138516661214455 2251799813685248 125000000009391 4695500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 59189 131072 24973259072661432 36028797018963968 37564 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 779317518150412560342812906055656980396982394702499187106382620393032652998517540933158707129341055012778793601285942846917973645097155238594697634436426745

noncomputable def ep18 := nat_lit 13198325246229655554962711811363413523213721429909419700721697472804734044169853548961061453892255410264786862895235075217650796661500958924795543285583799

noncomputable def ep19 := nat_lit 13338205139369401582665284895604560799810298653799657073142644093199656832454717421805370366589019475922075211274104314270069372987910244956804919489535

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 4 3 ep17 131072 37564 ep18 ep19 59189 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 3 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138516661214455 2251799813685248 125000000009391 4695500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000075128 37564000000000000000 4138516661214455 2251799813685248 125000000009391 4695500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 59189 131072 24973259072661432 36028797018963968 37564 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz253 := (Real.log (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz4 := qz253

theorem EMRow02.d4 : Enclosure.Real.IsNear qz4 Bool.false 60223 32768 3 65536 := @Enclosure.Real.IsNear.of_eq qz4 (Real.log qz251) Bool.false 60223 32768 3 65536 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz251) Bool.false 120446 65536 3 65536 60223 32768 3 65536 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 150042 131072 1 37564 150042 131072 1 37564 75021 65536 2 65536 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 5456220599384213465248909714772227496572670538165976141063262914812807742611017753801422503639530882087556452122005170047444298375835020188444492540969863625638808382453421118235702266947370928498132967594635949979551089348001357731941995137847266570621617494261809398531128871567535833923098076891483476912075228072418610430965163137427706923427310178652894498746239459018086669257415154730407592571637957767157504839263249849478535520334507104454135585522664276476675

noncomputable def ep28 := nat_lit 583201912334273870627228188254822588827079241605343036411752047433839590517388190714780374919746279700129906501257101384229175562492847525225536391462542197025353003914524118772974087630067522636400444148635637549655768907025719966434833632093412247469427754039812435067522613541620617101084764807513402584784781490076808276521160080078978009740617112077674385114356333461540984478969922738031393369686631450339262287925718320742111081121726382582016608811398564907105

noncomputable def ep29 := nat_lit 2006268627360805445673839316848610509641534779303135707206598861506426804997221642604762844037348942607248852390277353874343091902420975230792155995982437872051629609224882022549487822374001366578458875613104959699164386313425243185530298109514065278868815165519648262204211929774735225023360668387821809970420335957473972782118680523137645713941929429588852958886338507735711181009301082096313539911189247153419366938656533848809858580689548163599238034961919825

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 10 9 ep27 131072 37564 ep28 ep29 150042 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 9 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 5456220599384260892400251500854699790811159195150212163211869656216336849990273498858157048596616978904240776489460003685239051624059887013466241201881443704542959173524008982544253046253151867013374679201187657749749224297051088632484873343955402287279851789208893474071824987110190207053471018354491495133306616646837230249901879422821128116650397962087630806812522581253210958036113071268120219429850657911869289056672761916619783759890108169949892385522664276476675

noncomputable def ep34 := nat_lit 583201912334279575053067226115417021307550325332234501953544426829928714668898700518418107620762577859683234776628347658361181262145210140271013263714562720079188253110303208819702903278206870150494721073991877864419341163488949363940583288588224434829960190109694548513088121652843287215458036179968684293644459891198769761601084092249455692877745995219003758983943549453190712470220270279351626860119698313725888367584660500821040083453648022042061408811398564907105

noncomputable def ep35 := nat_lit 2006268627360839170887858856494478835319319717359667041823756329478526322484078784125879825811686186445537802910004300367040714583746383402724632880452479311196631191501299191497899488881639138562974769996989848045902383299749709271247360054208480548633525642122514778503225872819822968825602771791453574137145372948950799520945900351638147820910599315255916738483881817718250085827996954508077874524152655659774549924038927632065100609588052048399238034961919825

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 10 9 ep33 131072 37564 ep34 ep35 150042 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 9 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 75021 65536 2 65536 75021 65536 1 32768 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 150042 131072 1 37564 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 150042 131072 37564 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 150042 131072 1 37564 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 150042 131072 37564 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow02.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 32768 := ep37

theorem EMRow02.d6 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow02.d7 : @Eq Nat (Nat.pow 4 1) 4 := @Eq.refl Nat 4

noncomputable def ep38 := nat_lit 6654828300299491382885967

noncomputable def ep39 := nat_lit 2870862060419008033718272

noncomputable def ep40 := nat_lit 47229516265347007055922054383433

noncomputable def ep41 := nat_lit 15823990896114221727480757092352000

noncomputable abbrev qz386 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz364 := qz386

noncomputable abbrev qz254 := qz364

noncomputable abbrev qz5 := qz254

noncomputable abbrev qz6 := (@instHSub Real Real.instSub)

noncomputable abbrev qz365 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz255 := qz365

noncomputable abbrev qz7 := qz255

noncomputable abbrev qz387 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz388 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz389 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz390 := (Enclosure.sfrac Bool.false 17846 1000)

noncomputable abbrev qz366 := (@HAdd.hAdd Complex Complex Complex qz387 (@HAdd.hAdd Complex Complex Complex qz387 qz388 (@HMul.hMul Complex Complex Complex qz386 Complex.I (@HDiv.hDiv Complex Complex Complex qz389 (↑qz390) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz256 := qz366

noncomputable abbrev qz8 := (Complex.Stirling.logGammaStirling 1 qz256)

noncomputable abbrev qz367 := qz387

noncomputable abbrev qz257 := qz367

noncomputable abbrev qz9 := qz257

noncomputable abbrev qz368 := (@HAdd.hAdd Complex Complex Complex qz387 qz388 (@HMul.hMul Complex Complex Complex qz386 Complex.I (@HDiv.hDiv Complex Complex Complex qz389 (↑qz390) (2 : Complex))))

noncomputable abbrev qz258 := qz368

noncomputable abbrev qz10 := qz258

noncomputable abbrev qz369 := qz390

noncomputable abbrev qz259 := qz369

noncomputable abbrev qz11 := (@HMul.hMul Real Real Real qz249 (@HDiv.hDiv Real Real Real qz252 qz259 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz391 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 17846 1000)))

noncomputable abbrev qz370 := qz391

noncomputable abbrev qz260 := qz370

noncomputable abbrev qz12 := qz260

noncomputable def ep42 := Complex.re (@HMul.hMul Complex Complex Complex qz5 (Complex.exp (@HMul.hMul Complex Complex Complex qz5 Complex.I ↑(@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))))) qz11))) (zetaApproximant qz12 1 4))

noncomputable def ep43 := @Enclosure.Real.IsNear.of_eq ep42 (@HSub.hSub Real Real Real qz6 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))))) qz11)) (Complex.re (zetaApproximant qz12 1 4))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))))) qz11)) (Complex.im (zetaApproximant qz12 1 4))))

noncomputable def ep44 := nat_lit 33273896388836861817800883

noncomputable def ep45 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))))) qz11)) (Complex.re (zetaApproximant qz12 1 4))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))))) qz11)) (Complex.im (zetaApproximant qz12 1 4))) ep44

noncomputable def ep46 := nat_lit 14354310302095040168591360

noncomputable def ep47 := nat_lit 11600018565545854720215805935087

noncomputable def ep48 := nat_lit 3955997724028555431870189273088000

noncomputable def ep49 := nat_lit 1794288787761880021073920

noncomputable def ep50 := nat_lit 165888400632717635011766128617

noncomputable def ep51 := nat_lit 3164798179222844345496151418470400

noncomputable def ep52 := nat_lit 59703419018539134278954549983963234907941188403200

noncomputable def ep53 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))))) qz11)) (Complex.re (zetaApproximant qz12 1 4)) 65535 65536 675951

noncomputable def ep54 := nat_lit 51422625750341233147904000

noncomputable def ep55 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))))) qz11)) Bool.false 65535 65536 1351902

noncomputable abbrev qz261 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz13 := qz261

noncomputable def ep56 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))))) qz11) (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 25) qz13) Bool.false 25 131072 65

noncomputable def ep57 := nat_lit 28849152000000000000000000

noncomputable def ep58 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))))) qz11) Bool.false 2617491401024357 13510798882111488000 14164854217287536750513 ep57

noncomputable def ep59 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))))) qz11 138007623532477490021 13510798882111488000 6308989248537536750513 ep57 669412383 65536000

noncomputable def ep60 := nat_lit 4808192000000000000000000

noncomputable def ep61 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 6144892492588217937 450359962737049600 1492302252791608361733 ep60 Bool.false 138007623532477490021 13510798882111488000

noncomputable def ep62 := @Enclosure.Complex.IsNear.subLitP qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 4168997517674124137 450359962737049600 1364302252762759209733 ep60 Bool.false 178194378283289282021 13510798882111488000 4772989248508687598513

noncomputable def ep63 := nat_lit 13837067769926028327300936945893376

noncomputable def ep64 := nat_lit 38845692619697082433297537644363776

noncomputable abbrev qz392 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz371 := qz392

noncomputable abbrev qz262 := (@HSub.hSub Complex Complex Complex qz365 qz366 qz371)

noncomputable abbrev qz263 := (Complex.log qz366)

noncomputable abbrev qz14 := (@HSub.hSub Complex Complex Complex qz255 (@HMul.hMul Complex Complex Complex qz254 qz262 qz263) qz256)

noncomputable abbrev qz264 := qz371

noncomputable abbrev qz15 := (@HMul.hMul Complex Complex Complex qz254 qz264 ↑qz253)

noncomputable abbrev qz372 := qz389

noncomputable abbrev qz265 := qz372

noncomputable abbrev qz16 := qz265

noncomputable abbrev qz17 := (@instHMul Nat instMulNat)

noncomputable abbrev qz373 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz266 := qz373

noncomputable abbrev qz18 := qz266

noncomputable abbrev qz19 := qz256

noncomputable abbrev qz267 := (@instHSub Int Int.instSub)

noncomputable abbrev qz20 := qz267

noncomputable abbrev qz268 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz21 := qz268

noncomputable abbrev qz269 := (@instHMul Int Int.instMul)

noncomputable abbrev qz22 := qz269

noncomputable abbrev qz270 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz23 := qz270

noncomputable def ep65 := @Enclosure.Complex.IsNear.of_eq qz8 (@HAdd.hAdd Complex Complex Complex qz9 (@HAdd.hAdd Complex Complex Complex qz9 qz14 qz15) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz7 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz18 qz19 (@HSub.hSub Int Int Int qz20 qz21 (@HMul.hMul Int Int Int qz22 qz23 (@Nat.cast Int instNatCastInt k)))))) Bool.true 4168997517674124137

noncomputable def ep66 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz9 qz14 qz15) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz7 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz18 qz19 (@HSub.hSub Int Int Int qz20 qz21 (@HMul.hMul Int Int Int qz22 qz23 (@Nat.cast Int instNatCastInt k))))) Bool.true 4169994678217970537 450359962737049600

noncomputable def ep67 := nat_lit 559553374859860786058100736

noncomputable def ep68 := nat_lit 5979211148888906949902467072000

noncomputable def ep69 := @ep66 5328885864440213893 18782000000000000000000 Bool.false 59437671265686389239 4503599627370496000 388218750064901201 2347750000000000000000 Bool.false 297177 134217728 3 134217728 Bool.true 883903457 100663296000 8923 100663296000 Bool.true ep67 4168997517674124137 450359962737049600 1364302252762759209733 ep60 Bool.false ep68

noncomputable def ep70 := @Enclosure.Complex.IsNear.addLitP qz14 qz15 Bool.true 4583843982965183337 450359962737049600 4899000000182401393 18782000000000000000000

noncomputable def ep71 := @ep70 Bool.false 59437671265686389239 4503599627370496000 388218750064901201 2347750000000000000000 Bool.false 60223 65536 3 131072 Bool.false 0 1 0 1 Bool.true 273284771231692917112832 4169994678217970537 450359962737049600 5328885864440213893 18782000000000000000000 Bool.false 59437671265686389239 59437671265686389239 4503599627370496000

noncomputable abbrev qz24 := (@HMul.hMul Complex Complex Complex qz254 qz262 qz263)

noncomputable def ep72 := @Enclosure.Complex.IsNear.subLitP qz24 qz19 Bool.true 3570534066806821737 450359962737049600 4899000000182401393 18782000000000000000000 Bool.false 99623290740713325047

noncomputable def ep73 := @ep72 4503599627370496000 388218750064901201 2347750000000000000000 Bool.false 9000 4000 0 1 Bool.false 35692 4000 0 1 Bool.true 18335375931860733348000 4583843982965183337 450359962737049600 4899000000182401393 18782000000000000000000 Bool.false 237750685062745556956000 59437671265686389239 4503599627370496000 388218750064901201 2347750000000000000000

noncomputable abbrev qz25 := qz262

noncomputable abbrev qz26 := qz263

noncomputable def ep74 := @Enclosure.Complex.IsNear.mul qz25 qz26 Bool.true 3570534066806821737 450359962737049600 4899000000182401393 18782000000000000000000 Bool.false 99623290740713325047 4503599627370496000 388218750064901201

noncomputable abbrev qz27 := (Complex.re qz262)

noncomputable abbrev qz28 := (Complex.re qz263)

noncomputable abbrev qz29 := (Complex.im qz262)

noncomputable abbrev qz30 := (Complex.im qz263)

noncomputable def ep75 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz27 qz28) (@HMul.hMul Real Real Real qz0 qz29 qz30) 69968674236358723 18014398509481984 875000000197211 37564000000000000000 1329937730678947453 112589990684262400

noncomputable def ep76 := nat_lit 16080255892784864045424352325271552

noncomputable def ep77 := @Enclosure.Real.IsNear.mulLit_ff qz27 qz28 7000 4000 0 1 9995524890908389 4503599627370496 125000000028173 9391000000000000000

noncomputable def ep78 := @Enclosure.Complex.IsNear.re_isNear qz25 Bool.false 7000 4000 0 1 Bool.false 35692 4000 0 1

noncomputable abbrev qz271 := (Enclosure.sfrac Bool.false 35692 4000)

noncomputable abbrev qz31 := qz271

noncomputable def ep79 := @Enclosure.Complex.IsNear.of_eq qz25 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz31) Bool.false 7000 4000 0 1 Bool.false 35692 4000 0

noncomputable abbrev qz272 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz32 := (Complex.log (Complex.mk qz272 qz271))

noncomputable def ep80 := @Enclosure.Complex.IsNear.of_eq qz26 qz32 Bool.false 9995524890908389 4503599627370496 125000000028173 9391000000000000000 Bool.false 745230152795555 562949953421312 500000000009391 18782000000000000000

noncomputable def ep81 := nat_lit 480407500788095182081681444583847690240

noncomputable def ep82 := nat_lit 3134624042719333739620008398254768128

noncomputable def ep83 := nat_lit 35975542679671600956876891425538048

noncomputable def ep84 := BSN.log_dyadic_bound 330918864 2378918864 3 2 ep81 131072 37564 ep82 ep83 36703 2709837728 2048000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 330918864) (BSN.artanhQ 2378918864) 0 2 ep82 ep81 ep83 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz33 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz34 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz273 := (Real.log (Enclosure.sfrac Bool.false 1354918864 16000000))

noncomputable abbrev qz274 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep85 := @Enclosure.Real.IsNear.mulLit_ff qz33 qz273 1 2 0 1 9995524890908389 2251799813685248 125000000028173 4695500000000000000 9995524890908389 4503599627370496 125000000028173 9391000000000000000 qz34 (BSN.isNear_log_sfrac 1354918864 16000000 9995524890908389 2251799813685248 125000000028173 4695500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 1354918864) qz274)) Bool.false 20962135016018309808128 4722366482869645213696 1000000000225384 37564000000000000000 9995524890908389 2251799813685248 125000000028173 4695500000000000000 (BSN.log_rat_reduce_isNear 1354918864 16000000 6 2709837728 2048000000 36703 131072 24973259072661432 36028797018963968 37564 1000000000000000 rfl rfl rfl rfl (ep84 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep86 := BSN.arctan_dyadic_bound_f 9000 35692 2 1 131072 37564 6561000000000000 8114346360275252480 6561000000000000 19683000000000000 11360084904385353472 19683000000000000 32375 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 35692) 0 1 6561000000000000 8114346360275252480 6561000000000000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.arctanOddP 9000) (BSN.arctanOddQ 35692) 0 1 19683000000000000 11360084904385353472 19683000000000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz249 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz36 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz275 := (Real.arctan (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 35692)))

noncomputable def ep87 := @Enclosure.Real.IsNear.subLit_ff_p qz35 qz275 884279719003555 562949953421312 1 2000000000000000 32375 131072 1 37564 97678806587218984960 745230152795555 562949953421312 500000000009391 18782000000000000000 qz36 (ep86 rfl) rfl rfl

noncomputable abbrev qz37 := (Complex.mk qz272 qz271)

noncomputable abbrev qz38 := qz259

noncomputable abbrev qz276 := (@Eq.refl Real qz369)

noncomputable abbrev qz39 := qz276

noncomputable abbrev qz277 := (@Nat.cast Real Real.instNatCast 35692)

noncomputable abbrev qz278 := (@Nat.cast Real Real.instNatCast 9000)

noncomputable abbrev qz40 := (Real.arctan (@HDiv.hDiv Real Real Real qz252 qz277 qz278))

noncomputable def ep88 := @Enclosure.Complex.IsNear.re_isNear qz26 Bool.false 9995524890908389 4503599627370496 125000000028173 9391000000000000000 Bool.false 745230152795555 562949953421312 500000000009391 18782000000000000000 (ep80 (@congrArg Complex Complex qz19 qz37 Complex.log (BSN.w_shift_mk qz38 Bool.false 17846 1000 2 qz39 rfl)) (@Enclosure.Complex.IsNear.of_parts qz32 Bool.false 9995524890908389 4503599627370496 125000000028173 9391000000000000000 Bool.false 745230152795555 562949953421312 500000000009391 18782000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz32) (@HMul.hMul Real Real Real qz0 qz33 qz273) Bool.false 9995524890908389 4503599627370496 125000000028173 9391000000000000000 (Enclosure.clog_re_eq 9000 35692 4000 1354918864 16000000 rfl rfl rfl) (ep85 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz32) qz40 Bool.false 745230152795555 562949953421312 500000000009391 18782000000000000000 (Enclosure.clog_im_eq 9000 35692 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz40 (@HSub.hSub Real Real Real qz6 qz35 qz275) Bool.false 745230152795555 562949953421312 500000000009391 18782000000000000000 (BSN.arctan_recip 35692 9000 rfl rfl) ep87))))

noncomputable def ep89 := @Enclosure.Real.IsNear.mulLit_ff qz29 qz30 35692 4000 0 1 745230152795555 562949953421312 500000000009391 18782000000000000000

noncomputable def ep90 := @Enclosure.Complex.IsNear.im_isNear qz25 Bool.false 7000 4000 0 1 Bool.false 35692 4000 0 1

noncomputable def ep91 := @Enclosure.Complex.IsNear.im_isNear qz26 Bool.false 9995524890908389 4503599627370496 125000000028173 9391000000000000000 Bool.false 745230152795555 562949953421312 500000000009391 18782000000000000000 (ep80 (@congrArg Complex Complex qz19 qz37 Complex.log (BSN.w_shift_mk qz38 Bool.false 17846 1000 2 qz39 rfl)) (@Enclosure.Complex.IsNear.of_parts qz32 Bool.false 9995524890908389 4503599627370496 125000000028173 9391000000000000000 Bool.false 745230152795555 562949953421312 500000000009391 18782000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz32) (@HMul.hMul Real Real Real qz0 qz33 qz273) Bool.false 9995524890908389 4503599627370496 125000000028173 9391000000000000000 (Enclosure.clog_re_eq 9000 35692 4000 1354918864 16000000 rfl rfl rfl) (ep85 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz32) qz40 Bool.false 745230152795555 562949953421312 500000000009391 18782000000000000000 (Enclosure.clog_im_eq 9000 35692 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz40 (@HSub.hSub Real Real Real qz6 qz35 qz275) Bool.false 745230152795555 562949953421312 500000000009391 18782000000000000000 (BSN.arctan_recip 35692 9000 rfl rfl) ep87))))

noncomputable abbrev qz279 := (Enclosure.Real.IsNear.const Bool.false 35692 4000)

noncomputable abbrev qz41 := (@ep79 1 (BSN.w_sub_half_mk qz259 Bool.false 17846 1000 2 qz276 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz271 Bool.false 7000 4000 0 1 Bool.false 35692 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz279))

noncomputable def ep92 := @ep75 4461500000083795893 18782000000000000000000 ep76 3570534066806821737 450359962737049600 4899000000182401393 18782000000000000000000 (@ep77 69968674236358723 18014398509481984 875000000197211 37564000000000000000 (ep78 qz41) ep88 rfl) (@ep89 1329937730678947453 112589990684262400 4461500000083795893 18782000000000000000000 (ep90 qz41) ep91 rfl) rfl

noncomputable def ep93 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz27 qz30) (@HMul.hMul Real Real Real qz0 qz29 qz28) 5216611069568885 2251799813685248 3500000000065737 75128000000000000000 89190068601575555047 4503599627370496000

noncomputable def ep94 := nat_lit 224331707528649557560935140772806656

noncomputable def ep95 := @Enclosure.Real.IsNear.mulLit_ff qz27 qz30 7000 4000 0 1 745230152795555 562949953421312 500000000009391 18782000000000000000

noncomputable def ep96 := @Enclosure.Real.IsNear.mulLit_ff qz29 qz28 35692 4000 0 1 9995524890908389 4503599627370496 125000000028173 9391000000000000000

noncomputable def ep97 := @ep93 1115375000251387679 9391000000000000000000 ep94 99623290740713325047 4503599627370496000 388218750064901201 2347750000000000000000 (@ep95 5216611069568885 2251799813685248 3500000000065737 75128000000000000000 (ep78 qz41) ep91 rfl) (@ep96 89190068601575555047 4503599627370496000 1115375000251387679 9391000000000000000000 (ep90 qz41) ep88 rfl) rfl

noncomputable def ep98 := @Enclosure.Complex.IsNear.of_eq qz19 qz37 Bool.false 9000 4000 0 1 Bool.false 35692 4000 0 1 (BSN.w_shift_mk qz38 Bool.false 17846 1000 2 qz39 rfl)

noncomputable abbrev qz280 := (ep98 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 35692 4000) Bool.false 9000 4000 0 1 Bool.false 35692 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 35692 4000)))

noncomputable abbrev qz42 := qz280

noncomputable def ep99 := ep73 (@ep74 2347750000000000000000 (ep92 rfl) (ep97 rfl)) qz42 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz43 := qz264

noncomputable abbrev qz44 := (Complex.re ↑qz253)

noncomputable abbrev qz45 := (Complex.im ↑qz253)

noncomputable def ep100 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz43) qz44) (@HMul.hMul Real Real Real qz0 (Complex.im qz43) qz45) 60223 65536 3 131072 0 1 0 1 60223 60223

noncomputable def ep101 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz43) qz44 1 2 0 1 60223 32768 3 65536 60223 65536 3 131072

noncomputable abbrev qz281 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz282 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz46 := (@Enclosure.Complex.IsNear.of_eq qz264 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz281) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz281 Bool.false 1 2 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 2) qz282))

noncomputable def ep102 := ep101 (@Enclosure.Complex.IsNear.re_isNear qz43 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz46) (@Enclosure.Real.IsNear.of_eq qz44 qz4 Bool.false 60223 32768 3 65536 (Complex.ofReal_re qz4) EMRow02.d4)

noncomputable def ep103 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz43) qz45 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable abbrev qz47 := qz281

noncomputable abbrev qz48 := qz282

noncomputable def ep104 := ep103 (@Enclosure.Complex.IsNear.im_isNear qz43 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz46) (@Enclosure.Real.IsNear.of_eq qz45 qz47 Bool.false 0 1 0 1 (@Eq.trans Real qz45 (0 : Real) qz47 (Complex.ofReal_im qz4) Enclosure.sfrac_zero_eq) qz48)

noncomputable def ep105 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz43) qz45) (@HMul.hMul Real Real Real qz0 (Complex.im qz43) qz44) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep106 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz43) qz45 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep107 := ep106 (@Enclosure.Complex.IsNear.re_isNear qz43 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz46) (@Enclosure.Real.IsNear.of_eq qz45 qz47 Bool.false 0 1 0 1 (@Eq.trans Real qz45 (0 : Real) qz47 (Complex.ofReal_im qz4) Enclosure.sfrac_zero_eq) qz48)

noncomputable def ep108 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz43) qz44 0 1 0 1 60223 32768 3 65536 0 1 0 1

noncomputable def ep109 := ep108 (@Enclosure.Complex.IsNear.im_isNear qz43 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz46) (@Enclosure.Real.IsNear.of_eq qz44 qz4 Bool.false 60223 32768 3 65536 (Complex.ofReal_re qz4) EMRow02.d4)

noncomputable def ep110 := @ep71 388218750064901201 2347750000000000000000 (ep99 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz43 (↑qz4) Bool.false 60223 65536 3 131072 Bool.false 0 1 0 1 (@ep100 65536 3 131072 (ep102 rfl) (ep104 rfl) rfl rfl) (@ep105 1 0 1 (ep107 rfl) (ep109 rfl) rfl rfl))

noncomputable abbrev qz49 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz283 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz50 := (@HMul.hMul Complex Complex Complex qz254 (@HMul.hMul Complex Complex Complex qz254 (2 : Complex) qz283) (@HSub.hSub Complex Complex Complex qz255 (@HMul.hMul Complex Complex Complex qz254 (2 : Complex) qz283) (1 : Complex)))

noncomputable abbrev qz284 := (@HPow.hPow Complex Int Complex qz373 qz366 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz51 := qz284

noncomputable def ep111 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz7 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz18 qz19 (@HSub.hSub Int Int Int qz20 qz21 (@HMul.hMul Int Int Int qz22 qz23 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz9 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz7 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz18 qz19 (@HSub.hSub Int Int Int qz20 qz21 (@HMul.hMul Int Int Int qz22 qz23 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50) qz51)) Bool.false 297177 134217728 3 134217728

noncomputable def ep112 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz7 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz18 qz19 (@HSub.hSub Int Int Int qz20 qz21 (@HMul.hMul Int Int Int qz22 qz23 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50) qz51) Bool.false 0 1 0 1 Bool.false

noncomputable def ep113 := @ep112 0 1 0 1 Bool.false 297177 134217728 3 134217728 Bool.true 883903457 100663296000 8923 100663296000 Bool.false 297177 297177 134217728 3 134217728 Bool.true 883903457 883903457 100663296000 8923

noncomputable def ep114 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz7 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz18 qz19 (@HSub.hSub Int Int Int qz20 qz21 (@HMul.hMul Int Int Int qz22 qz23 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz47 qz47) Bool.false 0 1 0 1 Bool.false

noncomputable def ep115 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50) qz51 Bool.false 297177 134217728 3 134217728 Bool.true 883903457 100663296000 8923 100663296000

noncomputable abbrev qz52 := (Complex.re qz284)

noncomputable abbrev qz53 := (Complex.im qz284)

noncomputable def ep116 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz52) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz53) 297177 134217728 3 134217728 0 1 0

noncomputable def ep117 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz52 1 12 0 1 891531 33554432 9 33554432 297177

noncomputable def ep118 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz47) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz285 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz47 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz48)

noncomputable def ep119 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep118 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz285)

noncomputable def ep120 := @Enclosure.Complex.IsNear.re_isNear qz51 Bool.false 891531 33554432 9 33554432 Bool.true 883903457 8388608000 8923 8388608000

noncomputable abbrev qz374 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz286 := (@HPow.hPow Complex Nat Complex qz374 qz366 1)

noncomputable abbrev qz54 := (@Inv.inv Complex Complex.instInv qz286)

noncomputable def ep121 := @Enclosure.Complex.IsNear.of_eq qz51 qz54 Bool.false 891531 33554432 9 33554432 Bool.true 883903457 8388608000 8923

noncomputable def ep122 := @Enclosure.Complex.IsNear.of_parts qz54 Bool.false 891531 33554432 9 33554432 Bool.true 883903457 8388608000 8923

noncomputable abbrev qz55 := (Complex.re qz286)

noncomputable abbrev qz56 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz57 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz58 := qz286

noncomputable def ep123 := @Enclosure.Real.IsNear.mulLit_ff qz55 (@Inv.inv Real Real.instInv (@DFunLike.coe qz56 Complex (fun (x : Complex) => Real) qz57 Complex.normSq qz58)) 9000 4000 0 1 99059 8388608 1 8388608

noncomputable def ep124 := @Enclosure.Complex.IsNear.re_isNear qz58 Bool.false 9000 4000 0 1 Bool.false 35692 4000 0 1

noncomputable def ep125 := @Enclosure.Complex.IsNear.of_eq qz58 qz19 Bool.false 9000 4000 0 1 Bool.false 35692 4000 0

noncomputable def ep126 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz56 Complex (fun (x : Complex) => Real) qz57 Complex.normSq qz58)) Bool.false 99059 8388608 1 8388608 99059 8388608 1

noncomputable abbrev qz59 := (@instHAdd Real Real.instAdd)

noncomputable abbrev qz60 := (Complex.im qz286)

noncomputable def ep127 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz56 Complex (fun (x : Complex) => Real) qz57 Complex.normSq qz58) (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 qz55 qz55) (@HMul.hMul Real Real Real qz0 qz60 qz60)) Bool.false 84682429 1000000 0 1

noncomputable def ep128 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz55 qz55) (@HMul.hMul Real Real Real qz0 qz60 qz60) 81 16 0 1 79619929 1000000

noncomputable def ep129 := @Enclosure.Real.IsNear.mulLit_ff qz55 qz55 9000 4000 0 1 9000 4000 0 1

noncomputable def ep130 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz60 35692 4000 0 1 35692 4000 0 1

noncomputable def ep131 := @Enclosure.Complex.IsNear.im_isNear qz58 Bool.false 9000 4000 0 1 Bool.false 35692 4000 0 1

noncomputable abbrev qz61 := (ep124 (@ep125 1 (BSN.pow_one_c qz256) qz280))

noncomputable abbrev qz62 := (ep131 (@ep125 1 (BSN.pow_one_c qz256) qz280))

noncomputable def ep132 := @ep128 0 1 1354918864 84682429 1000000 0 1 (@ep129 81 16 0 1 qz61 qz61 rfl) (@ep130 79619929 1000000 0 1 qz62 qz62 rfl)

noncomputable def ep133 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz56 Complex (fun (x : Complex) => Real) qz57 Complex.normSq qz58) 84682429 1000000 0 1 49529 49530 4194304 (ep127 (Enclosure.Complex.normSq_eq_mul_add_mul qz58) (ep132 rfl rfl)) rfl

noncomputable def ep134 := @Enclosure.Real.IsNear.of_eq (Complex.re qz54) (@HMul.hMul Real Real Real qz0 qz55 (@Inv.inv Real Real.instInv (@DFunLike.coe qz56 Complex (fun (x : Complex) => Real) qz57 Complex.normSq qz58))) Bool.false 891531 33554432 9 33554432 (Enclosure.Complex.inv_re_eq_mul qz58) (@ep123 891531 33554432 9 33554432 qz61 (@ep126 8388608 (ep133 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep135 := @Enclosure.Real.IsNear.of_eq (Complex.im qz54) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz60) (@Inv.inv Real Real.instInv (@DFunLike.coe qz56 Complex (fun (x : Complex) => Real) qz57 Complex.normSq qz58))) Bool.true 883903457 8388608000 8923 8388608000 (Enclosure.Complex.inv_im_eq_mul qz58)

noncomputable def ep136 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz60) (@Inv.inv Real Real.instInv (@DFunLike.coe qz56 Complex (fun (x : Complex) => Real) qz57 Complex.normSq qz58)) 35692 4000 0 1 99059 8388608 1

noncomputable def ep137 := @ep136 8388608 883903457 8388608000 8923 8388608000 (@Enclosure.Real.IsNear.neg qz60 Bool.false 35692 4000 0 1 qz62) (@ep126 8388608 (ep133 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep138 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz53 0 1 0 1 883903457 8388608000 8923 8388608000 0

noncomputable def ep139 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep118 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz285)

noncomputable def ep140 := @Enclosure.Complex.IsNear.im_isNear qz51 Bool.false 891531 33554432 9 33554432 Bool.true 883903457 8388608000 8923 8388608000

noncomputable abbrev qz63 := (@ep121 8388608000 (BSN.zpow_one_sub_two_mul qz256 1 1 rfl rfl) (@ep122 8388608000 ep134 (ep135 ep137)))

noncomputable def ep141 := @ep116 1 297177 297177 134217728 3 134217728 (@ep117 134217728 3 134217728 ep119 (ep120 qz63) rfl) (@ep138 1 0 1 ep139 (ep140 qz63) rfl) rfl

noncomputable def ep142 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz53) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz52) 883903457 100663296000 8923 100663296000 0 1 0

noncomputable def ep143 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz53 1 12 0 1 883903457 8388608000 8923 8388608000 883903457

noncomputable def ep144 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz52 0 1 0 1 891531 33554432 9 33554432 0

noncomputable def ep145 := @ep142 1 883903457 883903457 100663296000 8923 100663296000 (@ep143 100663296000 8923 100663296000 ep119 (ep140 qz63) rfl) (@ep144 1 0 1 ep139 (ep120 qz63) rfl) rfl

noncomputable abbrev qz64 := (@Enclosure.Complex.IsNear.mk qz281 qz281 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz282 qz282)

noncomputable def ep146 := @ep113 100663296000 (@ep114 0 1 0 1 (BSN.stirling_sum_base qz19) qz64) (ep115 (ep141 rfl) (ep145 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep147 := @ep69 178194378283289282021 13510798882111488000 4772989248508687598513 ep57 (ep110 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep111 Bool.true 883903457 100663296000 8923 100663296000 (BSN.stirling_sum_succ qz19 0 1 rfl) (ep146 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep148 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz38 2) Bool.false 9879474874570469 2251799813685248 125000000028173 4695500000000000000 Bool.false 837224057308579 281474976710656

noncomputable abbrev qz65 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz257 qz258 qz283))

noncomputable def ep149 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz38 2) (@HAdd.hAdd Complex Complex Complex qz9 (BSN.logSumC qz38 1) qz65) Bool.false 9879474874570469 2251799813685248 125000000028173 4695500000000000000 Bool.false 837224057308579 281474976710656 500000000009391 9391000000000000000

noncomputable def ep150 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz38 1) qz65 Bool.false 9858481074427621 4503599627370496 125000000028173 9391000000000000000 Bool.false 868512894059939 562949953421312 500000000009391 18782000000000000000 Bool.false

noncomputable def ep151 := nat_lit 88986398727463483793487846965248

noncomputable def ep152 := nat_lit 942630488130132793159158071296

noncomputable abbrev qz66 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz257 qz258 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep153 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz38 1) (@HAdd.hAdd Complex Complex Complex qz9 (BSN.logSumC qz38 0) qz66) Bool.false 9858481074427621 4503599627370496 125000000028173 9391000000000000000 Bool.false 868512894059939 562949953421312 500000000009391 18782000000000000000

noncomputable def ep154 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz38 0) qz66 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz287 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz31))

noncomputable def ep155 := @Enclosure.Complex.IsNear.of_eq qz66 qz287 Bool.false 9858481074427621 4503599627370496 125000000028173 9391000000000000000 Bool.false 868512894059939 562949953421312 500000000009391 18782000000000000000

noncomputable def ep156 := nat_lit 418972805414800638683056053172647690240

noncomputable def ep157 := nat_lit 1675626087274295882486039645614768128

noncomputable def ep158 := nat_lit 11891989179491478758838609185538048

noncomputable def ep159 := BSN.log_dyadic_bound 250918864 2298918864 3 2 ep156 131072 37564 ep157 ep158 28726 2549837728 2048000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 250918864) (BSN.artanhQ 2298918864) 0 2 ep157 ep156 ep158 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep160 := @Enclosure.Real.IsNear.mulLit_ff qz33 (Real.log (Enclosure.sfrac Bool.false 1274918864 16000000)) 1 2 0 1 9858481074427621 2251799813685248 125000000028173 4695500000000000000 9858481074427621 4503599627370496 125000000028173 9391000000000000000 qz34 (BSN.isNear_log_sfrac 1274918864 16000000 9858481074427621 2251799813685248 125000000028173 4695500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 1274918864) qz274)) Bool.false 20674733302198034235392 4722366482869645213696 1000000000225384 37564000000000000000 9858481074427621 2251799813685248 125000000028173 4695500000000000000 (BSN.log_rat_reduce_isNear 1274918864 16000000 6 2549837728 2048000000 28726 131072 24973259072661432 36028797018963968 37564 1000000000000000 rfl rfl rfl rfl (ep159 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep161 := BSN.arctan_dyadic_bound_f 1000 35692 1 0 131072 37564 0 1 1 0 1 1 3671 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 35692) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 35692) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz288 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable def ep162 := @Enclosure.Real.IsNear.subLit_ff_p qz35 (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz288 qz277)) 884279719003555 562949953421312 1 2000000000000000 3671 131072 1 37564 113837722050224324608 868512894059939 562949953421312 500000000009391 18782000000000000000 qz36 (ep161 rfl) rfl rfl

noncomputable abbrev qz67 := (@HAdd.hAdd Complex Complex Complex qz257 qz258 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz289 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz31)

noncomputable def ep163 := @ep154 9858481074427621 4503599627370496 125000000028173 9391000000000000000 Bool.false 868512894059939 562949953421312 500000000009391 18782000000000000000 Bool.false 9858481074427621 9858481074427621 4503599627370496 125000000028173 9391000000000000000 Bool.false 868512894059939 868512894059939 562949953421312 500000000009391 18782000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz38 0) (Complex.mk qz47 qz47) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz38) qz64) (ep155 (@congrArg Complex Complex qz67 qz289 Complex.log (BSN.w_shift_mk qz38 Bool.false 17846 1000 0 qz39 rfl)) (@Enclosure.Complex.IsNear.of_parts qz287 Bool.false 9858481074427621 4503599627370496 125000000028173 9391000000000000000 Bool.false 868512894059939 562949953421312 500000000009391 18782000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz287) (@HMul.hMul Real Real Real qz0 qz33 (Real.log (Enclosure.sfrac Bool.false 1274918864 16000000))) Bool.false 9858481074427621 4503599627370496 125000000028173 9391000000000000000 (Enclosure.clog_re_eq 1000 35692 4000 1274918864 16000000 rfl rfl rfl) (ep160 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz287) (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz277 qz288)) Bool.false 868512894059939 562949953421312 500000000009391 18782000000000000000 (Enclosure.clog_im_eq 1000 35692 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz277 qz288)) (@HSub.hSub Real Real Real qz6 qz35 (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz288 qz277))) Bool.false 868512894059939 562949953421312 500000000009391 18782000000000000000 (BSN.arctan_recip 35692 1000 rfl rfl) ep162)))) rfl rfl

noncomputable abbrev qz290 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz31))

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq qz65 qz290 Bool.false 9900468674713317 4503599627370496 125000000028173 9391000000000000000 Bool.false 805935220557219 562949953421312 500000000009391 18782000000000000000

noncomputable def ep165 := nat_lit 436744477682424802954647510596007690240

noncomputable def ep166 := nat_lit 2056277761960534862028278271406768128

noncomputable def ep167 := nat_lit 17137182331415013819018093857538048

noncomputable def ep168 := BSN.log_dyadic_bound 274918864 2322918864 3 2 ep165 131072 37564 ep166 ep167 31170 2597837728 2048000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 274918864) (BSN.artanhQ 2322918864) 0 2 ep166 ep165 ep167 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep169 := @Enclosure.Real.IsNear.mulLit_ff qz33 (Real.log (Enclosure.sfrac Bool.false 1298918864 16000000)) 1 2 0 1 9900468674713317 2251799813685248 125000000028173 4695500000000000000 9900468674713317 4503599627370496 125000000028173 9391000000000000000 qz34 (BSN.isNear_log_sfrac 1298918864 16000000 9900468674713317 2251799813685248 125000000028173 4695500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 1298918864) qz274)) Bool.false 20762787682112382173184 4722366482869645213696 1000000000225384 37564000000000000000 9900468674713317 2251799813685248 125000000028173 4695500000000000000 (BSN.log_rat_reduce_isNear 1298918864 16000000 6 2597837728 2048000000 31170 131072 24973259072661432 36028797018963968 37564 1000000000000000 rfl rfl rfl rfl (ep168 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep170 := BSN.arctan_dyadic_bound_f 5000 35692 1 0 131072 37564 0 1 1 0 1 1 18241 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 35692) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 35692) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz291 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep171 := @Enclosure.Real.IsNear.subLit_ff_p qz35 (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz291 qz277)) 884279719003555 562949953421312 1 2000000000000000 18241 131072 1 37564 105635541228875808768 805935220557219 562949953421312 500000000009391 18782000000000000000 qz36 (ep170 rfl) rfl rfl

noncomputable abbrev qz68 := (@HAdd.hAdd Complex Complex Complex qz257 qz258 qz283)

noncomputable abbrev qz292 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz31)

noncomputable def ep172 := @ep150 9900468674713317 4503599627370496 125000000028173 9391000000000000000 Bool.false 805935220557219 562949953421312 500000000009391 18782000000000000000 Bool.false ep151 9879474874570469 2251799813685248 125000000028173 4695500000000000000 Bool.false ep152 837224057308579 281474976710656 500000000009391 9391000000000000000 (ep153 (BSN.log_sum_c_succ qz38 0 1 rfl) (ep163 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep164 (@congrArg Complex Complex qz68 qz292 Complex.log (BSN.w_shift_mk qz38 Bool.false 17846 1000 1 qz39 rfl)) (@Enclosure.Complex.IsNear.of_parts qz290 Bool.false 9900468674713317 4503599627370496 125000000028173 9391000000000000000 Bool.false 805935220557219 562949953421312 500000000009391 18782000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz290) (@HMul.hMul Real Real Real qz0 qz33 (Real.log (Enclosure.sfrac Bool.false 1298918864 16000000))) Bool.false 9900468674713317 4503599627370496 125000000028173 9391000000000000000 (Enclosure.clog_re_eq 5000 35692 4000 1298918864 16000000 rfl rfl rfl) (ep169 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz290) (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz277 qz291)) Bool.false 805935220557219 562949953421312 500000000009391 18782000000000000000 (Enclosure.clog_im_eq 5000 35692 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz277 qz291)) (@HSub.hSub Real Real Real qz6 qz35 (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz291 qz277))) Bool.false 805935220557219 562949953421312 500000000009391 18782000000000000000 (BSN.arctan_recip 35692 5000 rfl rfl) ep171)))) rfl rfl

noncomputable def ep173 := @ep62 ep57 Bool.false 9879474874570469 2251799813685248 125000000028173 4695500000000000000 Bool.false 837224057308579 281474976710656 500000000009391 9391000000000000000 Bool.true ep63 6144892492588217937 450359962737049600 1492302252791608361733 ep60 Bool.false ep64 138007623532477490021 13510798882111488000 6308989248537536750513 ep57 (@ep65 450359962737049600 1364302252762759209733 ep60 Bool.false 178194378283289282021 13510798882111488000 4772989248508687598513 ep57 (BSN.logGammaStirling_unfold 1 qz19) (ep147 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep148 500000000009391 9391000000000000000 (BSN.log_sum_c_eq qz38 2) (ep149 (BSN.log_sum_c_succ qz38 1 2 rfl) (ep172 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz69 := (@HDiv.hDiv Real Real Real qz252 qz259 (2 : Real))

noncomputable def ep174 := @Enclosure.Real.IsNear.mulLit_ff qz69 (Real.log Real.pi) 17846 2000 0 1 75021 65536 1 32768 669412383 65536000 8923 32768000 (@Enclosure.Real.IsNear.of_eq qz69 (Enclosure.sfrac Bool.false 17846 2000) Bool.false 17846 2000 0 1 (BSN.t_half_eq qz38 Bool.false 17846 1000 qz39) (Enclosure.Real.IsNear.const Bool.false 17846 2000)) EMRow02.d5 rfl

noncomputable def ep175 := @ep59 8923 32768000 171539916457532260352000 2617491401024357 13510798882111488000 14164854217287536750513 ep57 (@ep61 6308989248537536750513 ep57 (ep173 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep174 rfl rfl

noncomputable def ep176 := BSN.cos_dyadic_bound_f 25 131072 1 0 65536 18782 0 1 1 0 1 1 65535 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 25) (BSN.cosEvenQ 131072) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 25) (BSN.cosOddQ 131072) 0 0 rfl) rfl rfl

noncomputable def ep177 := nat_lit 25711312875170616573952000

noncomputable abbrev qz375 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz293 := qz375

noncomputable abbrev qz70 := qz293

noncomputable abbrev qz376 := (@Neg.neg Complex Complex.instNeg qz391)

noncomputable abbrev qz294 := qz376

noncomputable abbrev qz71 := qz294

noncomputable abbrev qz295 := (@HPow.hPow Complex Complex Complex qz375 (@Nat.cast Complex Complex.instNatCast 4) qz376)

noncomputable abbrev qz72 := qz295

noncomputable abbrev qz296 := (@Nat.cast Complex Complex.instNatCast 4)

noncomputable abbrev qz73 := (@HAdd.hAdd Complex Complex Complex qz257 (@HDiv.hDiv Complex Complex Complex qz265 qz296 (@HSub.hSub Complex Complex Complex qz255 qz260 (1 : Complex))) qz264)

noncomputable abbrev qz74 := (@instHSub Nat instSubNat)

noncomputable abbrev qz297 := qz374

noncomputable abbrev qz75 := qz297

noncomputable abbrev qz76 := qz296

noncomputable def ep178 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz12 1 4) (@HAdd.hAdd Complex Complex Complex qz9 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 4, @HPow.hPow Complex Complex Complex qz70 (@Nat.cast Complex Complex.instNatCast n) qz71) (@HMul.hMul Complex Complex Complex qz5 qz72 (@HAdd.hAdd Complex Complex Complex qz9 qz73 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))))) Bool.false 2538635567928348349569 1095146965186694348800 85279091768549025148507

noncomputable def ep179 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 4, @HPow.hPow Complex Complex Complex qz70 (@Nat.cast Complex Complex.instNatCast n) qz71) (@HMul.hMul Complex Complex Complex qz5 qz72 (@HAdd.hAdd Complex Complex Complex qz9 qz73 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))))) Bool.false 36310188577 17179869184 213558209625 161336151506944

noncomputable def ep180 := nat_lit 43613426962858570530777722781696

noncomputable def ep181 := nat_lit 10966154803036332492798820352

noncomputable def ep182 := @ep179 Bool.true 277094397 1073741824 6611669137 5041754734592 Bool.false 224008349317617523169 1095146965186694348800 17211744265304308648507 ep54 Bool.false 18048802382724707767 109514696518669434880 8568071598496550136207 ep177 Bool.false ep180 2538635567928348349569 1095146965186694348800 85279091768549025148507 ep54 Bool.true ep181 10213027524795692873 109514696518669434880

noncomputable def ep183 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 4, @HPow.hPow Complex Complex Complex qz70 (@Nat.cast Complex Complex.instNatCast n) qz71) (BSN.headSumC qz12 4) Bool.false 36310188577 17179869184 213558209625 161336151506944 Bool.true 277094397 1073741824 6611669137

noncomputable abbrev qz77 := (BSN.headSumC qz260 3)

noncomputable abbrev qz377 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz298 := qz377

noncomputable abbrev qz78 := (@HPow.hPow Complex Complex Complex qz293 qz298 qz294)

noncomputable def ep184 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 4) (@HAdd.hAdd Complex Complex Complex qz9 qz77 qz78) Bool.false 36310188577 17179869184 213558209625 161336151506944 Bool.true 277094397 1073741824 6611669137 5041754734592

noncomputable def ep185 := @Enclosure.Complex.IsNear.addLitP qz77 qz78 Bool.false 14547023801 8589934592 59079185943 80668075753472 Bool.false 1185819849 8589934592 58112288583 80668075753472 Bool.false

noncomputable abbrev qz79 := (BSN.headSumC qz260 2)

noncomputable abbrev qz378 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz299 := qz378

noncomputable abbrev qz80 := (@HPow.hPow Complex Complex Complex qz293 qz299 qz294)

noncomputable def ep186 := @Enclosure.Complex.IsNear.of_eq qz77 (@HAdd.hAdd Complex Complex Complex qz9 qz79 qz80) Bool.false 14547023801 8589934592 59079185943 80668075753472 Bool.false 1185819849 8589934592 58112288583 80668075753472

noncomputable def ep187 := @Enclosure.Complex.IsNear.addLitP qz79 qz80 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep188 := @Enclosure.Complex.IsNear.of_eq qz79 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz47) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz12)

noncomputable abbrev qz81 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable abbrev qz300 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz82 := (@HMul.hMul Real Real Real qz249 qz259 qz300)

noncomputable abbrev qz83 := (Real.sin (@HMul.hMul Real Real Real qz249 qz259 qz300))

noncomputable def ep189 := @Enclosure.Complex.IsNear.of_eq qz80 (Complex.mk (@HMul.hMul Real Real Real qz0 qz81 (Real.cos qz82)) (@HMul.hMul Real Real Real qz0 qz81 (@Neg.neg Real Real.instNeg qz83))) Bool.false 5957089209 8589934592 59079185943 80668075753472 Bool.false 1185819849 8589934592 58112288583 80668075753472 (BSN.cpow_neg_s_mk qz38 17846 1000 2 qz39 rfl)

noncomputable abbrev qz84 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz85 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz301 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep190 := @Enclosure.Real.IsNear.inv_image qz84 185363 131072 1 131072 46340 46342 65536 (@Enclosure.Real.IsNear.of_eq qz84 (Real.sqrt (@HDiv.hDiv Real Real Real qz3 qz85 qz301)) Bool.false 185363 131072 1 131072 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz3 qz85 qz301)) Bool.false 185363 131072 1 131072 185363 131072 1 131072 (BSN.sqrt_enclosure 2 1 92681 92682 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep191 := BSN.log_dyadic_bound 1 3 5 4 6200145 65536 18782 246264 105 45426 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 1) (BSN.artanhQ 3) 0 4 246264 6200145 105 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep192 := nat_lit 291163837023297496014070468047461997985997060622376012577038020248715520

noncomputable def ep193 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080

noncomputable def ep194 := nat_lit 343058561994129275939052519434688653243073086568162338830470046925056

noncomputable def ep195 := nat_lit 762016525960645804066283236045220498810455897585112532010326434861138176

noncomputable def ep196 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800

noncomputable abbrev qz302 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz303 := (BSN.sinOddQ 268435456)

noncomputable def ep197 := BSN.sin_dyadic_bound_f 368910514 268435456 3 2 131072 37601 ep192 ep193 ep194 ep195 ep196 ep194 128549 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 368910514) qz302 0 2 ep192 ep193 ep194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 368910514) qz303 0 2 ep195 ep196 ep194 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz86 := (@HDiv.hDiv Real Real Real qz252 (@Nat.cast Real Real.instNatCast 50667) (@Nat.cast Real Real.instNatCast 4096))

noncomputable abbrev qz87 := qz300

noncomputable abbrev qz304 := (Enclosure.Real.IsNear.const Bool.false 17846 1000)

noncomputable abbrev qz88 := qz304

noncomputable abbrev qz305 := (BSN.isNear_log_sfrac 2 1 45426 65536 1 18782 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 45426 65536 18782 rfl rfl rfl (ep191 rfl)))

noncomputable def ep198 := @Enclosure.Real.IsNear.cos_image qz82 qz86 Bool.false 50667 4096 63 65536 Bool.false 128549 131072 1 18782 (@Enclosure.Real.IsNear.recentre' qz82 Bool.false 202668099 16384000 8923 9391000 50667 4096 63 65536 (@Enclosure.Real.IsNear.mulLit_ff qz38 qz87 17846 1000 0 1 45426 65536 1 18782 202668099 16384000 8923 9391000 qz88 qz305 rfl) rfl) (Enclosure.sfrac_false_div 50667 4096) (BSN.cos_reduce3 qz86 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 811242799802287652864) (@Nat.cast Real Real.instNatCast 590295810358705651712)) 226375608064910080 72057594037927936 Bool.false 128549 131072 1 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q3 50667 4096 226375608064910080 72057594037927936 1 811242799802287652864 590295810358705651712 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 128549 131072 811242799802287652864 590295810358705651712 368910514 268435456 37601 37564 (ep197 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep199 := nat_lit 161910157707162666352678727812783193838106399495350301360056886825697536

noncomputable def ep200 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120

noncomputable def ep201 := nat_lit 485044355997499740506158078399480204207833052312914579402509720383242496

noncomputable def ep202 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400

noncomputable abbrev qz306 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz307 := (BSN.cosOddQ 268435456)

noncomputable def ep203 := BSN.cos_dyadic_bound_f 368910514 268435456 3 2 131072 37601 ep199 ep200 ep194 ep201 ep202 ep194 25589 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 368910514) qz306 0 2 ep199 ep200 ep194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 368910514) qz307 0 2 ep201 ep202 ep194 rfl rfl rfl rfl) rfl rfl

noncomputable def ep204 := @Enclosure.Real.IsNear.sin_image qz82 qz86 Bool.false 50667 4096 63 65536 Bool.true 25589 131072 1 18782 (@Enclosure.Real.IsNear.recentre' qz82 Bool.false 202668099 16384000 8923 9391000 50667 4096 63 65536 (@Enclosure.Real.IsNear.mulLit_ff qz38 qz87 17846 1000 0 1 45426 65536 1 18782 202668099 16384000 8923 9391000 qz88 qz305 rfl) rfl) (Enclosure.sfrac_false_div 50667 4096) (BSN.sin_reduce3 qz86 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 811242799802287652864) (@Nat.cast Real Real.instNatCast 590295810358705651712)) 226375608064910080 72057594037927936 Bool.false 25589 131072 1 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q3 50667 4096 226375608064910080 72057594037927936 1 811242799802287652864 590295810358705651712 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 25589 131072 811242799802287652864 590295810358705651712 368910514 268435456 37601 37564 (ep203 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz89 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) Bool.false 92682 131072 2 131072 46341 65536 1 65536 (ep190 rfl rfl) rfl)

noncomputable def ep205 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz81 (Real.cos qz82)) (@HMul.hMul Real Real Real qz0 qz81 (@Neg.neg Real Real.instNeg qz83)) Bool.false 5957089209 8589934592 59079185943 80668075753472 Bool.false 1185819849 8589934592 58112288583 80668075753472 (@Enclosure.Real.IsNear.mulLit_ff qz81 (Real.cos qz82) 46341 65536 1 65536 128549 131072 624401 615448576 5957089209 8589934592 59079185943 80668075753472 qz89 (@Enclosure.Real.IsNear.recentre' (Real.cos qz82) Bool.false 128549 131072 1248802 1230897152 128549 131072 624401 615448576 (ep198 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz81 (@Neg.neg Real Real.instNeg qz83) 46341 65536 1 65536 25589 131072 624401 615448576 1185819849 8589934592 58112288583 80668075753472 qz89 (@Enclosure.Real.IsNear.neg qz83 Bool.true 25589 131072 624401 615448576 (@Enclosure.Real.IsNear.recentre' qz83 Bool.true 25589 131072 1248802 1230897152 25589 131072 624401 615448576 (ep204 rfl rfl) rfl)) rfl)

noncomputable def ep206 := @ep187 5957089209 8589934592 59079185943 80668075753472 Bool.false 1185819849 8589934592 58112288583 80668075753472 Bool.false 14547023801 14547023801 8589934592 59079185943 80668075753472 Bool.false 1185819849 1185819849 8589934592 58112288583 80668075753472 (ep188 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz47 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz48)) (ep189 ep205) rfl rfl

noncomputable abbrev qz308 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz90 := (@Inv.inv Real Real.instInv (Real.sqrt qz308))

noncomputable abbrev qz309 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz91 := (@HMul.hMul Real Real Real qz249 qz259 qz309)

noncomputable abbrev qz92 := (Real.sin (@HMul.hMul Real Real Real qz249 qz259 qz309))

noncomputable def ep207 := @Enclosure.Complex.IsNear.of_eq qz78 (Complex.mk (@HMul.hMul Real Real Real qz0 qz90 (Real.cos qz91)) (@HMul.hMul Real Real Real qz0 qz90 (@Neg.neg Real Real.instNeg qz92))) Bool.false 7216140975 17179869184 95399837739 161336151506944 Bool.true 3402575025 8589934592 47674417609 80668075753472 (BSN.cpow_neg_s_mk qz38 17846 1000 3 qz39 rfl)

noncomputable abbrev qz93 := (Real.sqrt qz308)

noncomputable abbrev qz94 := qz308

noncomputable def ep208 := @Enclosure.Real.IsNear.inv_image qz93 227023 131072 1 131072 37837 37838 65536 (@Enclosure.Real.IsNear.of_eq qz93 (Real.sqrt (@HDiv.hDiv Real Real Real qz3 qz94 qz301)) Bool.false 227023 131072 1 131072 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz3 qz94 qz301)) Bool.false 227023 131072 1 131072 227023 131072 1 131072 (BSN.sqrt_enclosure 3 1 113511 113512 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep209 := BSN.log_dyadic_bound 1 2 9 8 2258332876800 65536 18782 222698787165 2027025 71998 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1) (BSN.artanhQ 2) 0 8 222698787165 2258332876800 2027025 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep210 := nat_lit 1696942464743836445375121506980096

noncomputable def ep211 := nat_lit 124615124604835863084731911901282304

noncomputable def ep212 := nat_lit 1869226869072537946270978678519234560

noncomputable def ep213 := BSN.cos_dyadic_bound_f 202962956 268435456 2 1 131072 37601 ep210 ep211 ep210 ep210 ep212 ep210 95357 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 202962956) qz306 0 1 ep210 ep211 ep210 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 202962956) qz307 0 1 ep210 ep212 ep210 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz95 := (@HDiv.hDiv Real Real Real qz252 (@Nat.cast Real Real.instNatCast 321219) (@Nat.cast Real Real.instNatCast 16384))

noncomputable abbrev qz96 := qz309

noncomputable abbrev qz310 := (BSN.isNear_log_sfrac 3 1 71998 65536 1 18782 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 71998 65536 18782 rfl rfl rfl (ep209 rfl)))

noncomputable def ep214 := @Enclosure.Real.IsNear.cos_image qz91 qz95 Bool.false 321219 16384 63 65536 Bool.false 95357 131072 1 18782 (@Enclosure.Real.IsNear.recentre' qz91 Bool.false 321219077 16384000 8923 9391000 321219 16384 63 65536 (@Enclosure.Real.IsNear.mulLit_ff qz38 qz96 17846 1000 0 1 71998 65536 1 18782 321219077 16384000 8923 9391000 qz88 qz310 rfl) rfl) (Enclosure.sfrac_false_div 321219 16384) (BSN.cos_reduce0 qz95 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 1785281048112506339328) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 95357 131072 3 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q0 321219 16384 226375608064910080 72057594037927936 3 1785281048112506339328 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 95357 131072 1785281048112506339328 2361183241434822606848 202962956 268435456 37601 37564 (ep213 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep215 := nat_lit 623075623024179315423659559506411520

noncomputable def ep216 := nat_lit 4361529361169255207965616916544880640

noncomputable def ep217 := BSN.sin_dyadic_bound_f 202962956 268435456 2 1 131072 37601 ep210 ep215 ep210 ep210 ep216 ep210 89926 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 202962956) qz302 0 1 ep210 ep215 ep210 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 202962956) qz303 0 1 ep210 ep216 ep210 rfl rfl rfl rfl) rfl rfl

noncomputable def ep218 := @Enclosure.Real.IsNear.sin_image qz91 qz95 Bool.false 321219 16384 63 65536 Bool.false 89926 131072 1 18782 (@Enclosure.Real.IsNear.recentre' qz91 Bool.false 321219077 16384000 8923 9391000 321219 16384 63 65536 (@Enclosure.Real.IsNear.mulLit_ff qz38 qz96 17846 1000 0 1 71998 65536 1 18782 321219077 16384000 8923 9391000 qz88 qz310 rfl) rfl) (Enclosure.sfrac_false_div 321219 16384) (BSN.sin_reduce0 qz95 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 1785281048112506339328) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 89926 131072 3 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q0 321219 16384 226375608064910080 72057594037927936 3 1785281048112506339328 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 89926 131072 1785281048112506339328 2361183241434822606848 202962956 268435456 37601 37564 (ep217 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz97 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz308)) Bool.false 75675 131072 1 131072 75675 131072 1 131072 (ep208 rfl rfl) rfl)

noncomputable def ep219 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz90 (Real.cos qz91)) (@HMul.hMul Real Real Real qz0 qz90 (@Neg.neg Real Real.instNeg qz92)) Bool.false 7216140975 17179869184 95399837739 161336151506944 Bool.true 3402575025 8589934592 47674417609 80668075753472 (@Enclosure.Real.IsNear.mulLit_ff qz90 (Real.cos qz91) 75675 131072 1 131072 95357 131072 624401 615448576 7216140975 17179869184 95399837739 161336151506944 qz97 (@Enclosure.Real.IsNear.recentre' (Real.cos qz91) Bool.false 95357 131072 1248802 1230897152 95357 131072 624401 615448576 (ep214 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz90 (@Neg.neg Real Real.instNeg qz92) 75675 131072 1 131072 44963 65536 624401 615448576 3402575025 8589934592 47674417609 80668075753472 qz97 (@Enclosure.Real.IsNear.neg qz92 Bool.false 44963 65536 624401 615448576 (@Enclosure.Real.IsNear.recentre' qz92 Bool.false 89926 131072 1248802 1230897152 44963 65536 624401 615448576 (ep218 rfl rfl) rfl)) rfl)

noncomputable def ep220 := @ep185 7216140975 17179869184 95399837739 161336151506944 Bool.true 3402575025 8589934592 47674417609 80668075753472 Bool.false 311902144899615555584 36310188577 17179869184 213558209625 161336151506944 Bool.true 19041781968317448192 277094397 1073741824 6611669137 5041754734592 (ep186 (BSN.head_sum_c_succ qz12 2 3 rfl rfl) (ep206 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep207 ep219) rfl rfl

noncomputable def ep221 := @Enclosure.Complex.IsNear.mul qz72 (@HAdd.hAdd Complex Complex Complex qz9 qz73 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))) Bool.false 224008349317617523169 1095146965186694348800 17211744265304308648507 ep54 Bool.false

noncomputable abbrev qz98 := (Complex.re qz295)

noncomputable abbrev qz99 := (Complex.im qz295)

noncomputable def ep222 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz98 (Complex.re (@HAdd.hAdd Complex Complex Complex qz9 qz73 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz99 (Complex.im (@HAdd.hAdd Complex Complex Complex qz9 qz73 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))))) 1275031584112030575 5475734825933471744 40000214839022285149

noncomputable def ep223 := nat_lit 154267877251023699443712000

noncomputable def ep224 := nat_lit 1226610319658348722154815299702526836736

noncomputable def ep225 := @Enclosure.Real.IsNear.mulLit_ff qz98 (Complex.re (@HAdd.hAdd Complex Complex Complex qz9 qz73 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))))) 991872225 2147483648 10372318769 20167018938368 3856439021

noncomputable abbrev qz100 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable abbrev qz311 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz369 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable abbrev qz101 := (Real.cos qz311)

noncomputable abbrev qz102 := (@Neg.neg Real Real.instNeg (Real.sin qz311))

noncomputable def ep226 := @Enclosure.Complex.IsNear.of_eq qz72 (Complex.mk (@HMul.hMul Real Real Real qz0 qz100 qz101) (@HMul.hMul Real Real Real qz0 qz100 qz102)) Bool.false 991872225 2147483648 10372318769 20167018938368 Bool.false 1644731895 8589934592 41156429863 80668075753472 (BSN.cpow_neg_s_mk qz38 17846 1000 4 qz39 rfl)

noncomputable abbrev qz103 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz104 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def ep227 := @Enclosure.Real.IsNear.inv_image qz103 262145 131072 1 131072 32767 32768 65536 (@Enclosure.Real.IsNear.of_eq qz103 (Real.sqrt (@HDiv.hDiv Real Real Real qz3 qz104 qz301)) Bool.false 262145 131072 1 131072 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz3 qz104 qz301)) Bool.false 262145 131072 1 131072 262145 131072 1 131072 (BSN.sqrt_enclosure 4 1 131072 131073 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep228 := nat_lit 753960950911045074462890625

noncomputable def ep229 := nat_lit 117048680082474133384580175

noncomputable def ep230 := BSN.log_dyadic_bound 3 5 12 11 ep228 65536 18782 ep229 431467934736729065175 90852 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 3) (BSN.artanhQ 5) 0 11 ep229 ep228 431467934736729065175 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep231 := nat_lit 156991563665056971544188531208225218057556252064965559809955638615736320

noncomputable def ep232 := nat_lit 99842960466156026545565836632374544688893131236912116770715159494656

noncomputable def ep233 := nat_lit 411006730520108768096562856095566012316484357005288132265588371830603776

noncomputable def ep234 := BSN.sin_dyadic_bound_f 316165648 268435456 3 2 131072 37601 ep231 ep193 ep232 ep233 ep196 ep232 121080 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 316165648) qz302 0 2 ep231 ep193 ep232 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 316165648) qz303 0 2 ep233 ep196 ep232 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz105 := qz311

noncomputable abbrev qz106 := (@HDiv.hDiv Real Real Real qz252 (@Nat.cast Real Real.instNatCast 3242689) qz261)

noncomputable abbrev qz312 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz107 := qz312

noncomputable abbrev qz313 := (BSN.isNear_log_sfrac 4 1 90852 65536 1 18782 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 90852 65536 18782 rfl rfl rfl (ep230 rfl)))

noncomputable abbrev qz314 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep235 := @Enclosure.Real.IsNear.cos_image qz105 qz106 Bool.false 3242689 131072 63 65536 Bool.false 121080 131072 1 18782 (@Enclosure.Real.IsNear.recentre' qz105 Bool.false 202668099 8192000 8923 9391000 3242689 131072 63 65536 (@Enclosure.Real.IsNear.mulLit_ff qz38 qz107 17846 1000 0 1 90852 65536 1 18782 202668099 8192000 8923 9391000 qz88 qz313 rfl) rfl) (Enclosure.sfrac_false_div 3242689 131072) (BSN.cos_reduce3 qz106 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 22248179602250591633408) qz314) 226375608064910080 72057594037927936 Bool.false 121080 131072 3 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q3 3242689 131072 226375608064910080 72057594037927936 3 22248179602250591633408 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 121080 131072 22248179602250591633408 18889465931478580854784 316165648 268435456 37601 37564 (ep234 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep236 := nat_lit 87261910018572164647458324376406176496281870316641716390762339301851136

noncomputable def ep237 := nat_lit 261586044134784181889283841455953780399467824687451324938745587586564096

noncomputable def ep238 := BSN.cos_dyadic_bound_f 316165648 268435456 3 2 131072 37601 ep236 ep200 ep232 ep237 ep202 ep232 50194 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 316165648) qz306 0 2 ep236 ep200 ep232 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 316165648) qz307 0 2 ep237 ep202 ep232 rfl rfl rfl rfl) rfl rfl

noncomputable def ep239 := @Enclosure.Real.IsNear.sin_image qz105 qz106 Bool.false 3242689 131072 63 65536 Bool.true 50194 131072 1 18782 (@Enclosure.Real.IsNear.recentre' qz105 Bool.false 202668099 8192000 8923 9391000 3242689 131072 63 65536 (@Enclosure.Real.IsNear.mulLit_ff qz38 qz107 17846 1000 0 1 90852 65536 1 18782 202668099 8192000 8923 9391000 qz88 qz313 rfl) rfl) (Enclosure.sfrac_false_div 3242689 131072) (BSN.sin_reduce3 qz106 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 22248179602250591633408) qz314) 226375608064910080 72057594037927936 Bool.false 50194 131072 3 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q3 3242689 131072 226375608064910080 72057594037927936 3 22248179602250591633408 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 50194 131072 22248179602250591633408 18889465931478580854784 316165648 268435456 37601 37564 (ep238 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz108 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) Bool.false 65535 131072 1 131072 65535 131072 1 131072 (ep227 rfl rfl) rfl)

noncomputable abbrev qz109 := (Real.sin qz311)

noncomputable def ep240 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz100 qz101) (@HMul.hMul Real Real Real qz0 qz100 qz102) Bool.false 991872225 2147483648 10372318769 20167018938368 Bool.false 1644731895 8589934592 41156429863 80668075753472 (@Enclosure.Real.IsNear.mulLit_ff qz100 qz101 65535 131072 1 131072 15135 16384 624401 615448576 991872225 2147483648 10372318769 20167018938368 qz108 (@Enclosure.Real.IsNear.recentre' qz101 Bool.false 121080 131072 1248802 1230897152 15135 16384 624401 615448576 (ep235 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz100 qz102 65535 131072 1 131072 25097 65536 624401 615448576 1644731895 8589934592 41156429863 80668075753472 qz108 (@Enclosure.Real.IsNear.neg qz109 Bool.true 25097 65536 624401 615448576 (@Enclosure.Real.IsNear.recentre' qz109 Bool.true 50194 131072 1248802 1230897152 25097 65536 624401 615448576 (ep239 rfl rfl) rfl)) rfl)

noncomputable def ep241 := @ep225 7649513184 0 1 1275031584112030575 5475734825933471744 40000214839022285149 154267877251023699443712 (@Enclosure.Complex.IsNear.re_isNear qz72 Bool.false 991872225 2147483648 10372318769 20167018938368 Bool.false 1644731895 8589934592 41156429863 80668075753472 (ep226 ep240))

noncomputable def ep242 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz9 qz73 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))) Bool.false 3856439021 7649513184 0 1 Bool.false

noncomputable def ep243 := @Enclosure.Complex.IsNear.addLitP qz73 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) Bool.false 78682429 159364858 0 1 Bool.true 17846000

noncomputable def ep244 := @ep243 79682429 0 1 Bool.false 1 96 0 1 Bool.false 8923 24000 0 1 Bool.false 7712878042 3856439021 7649513184 0 1 Bool.false 282702313967 282702313967 1912378296000 0 1

noncomputable abbrev qz110 := (@HDiv.hDiv Complex Complex Complex qz265 qz296 (@HSub.hSub Complex Complex Complex qz255 qz260 (1 : Complex)))

noncomputable def ep245 := @Enclosure.Complex.IsNear.addLitP qz110 qz43 Bool.true 8000000 1274918864 0 1 Bool.true 285536000 1274918864 0 1

noncomputable def ep246 := @Enclosure.Complex.IsNear.of_eq qz110 (Complex.mk (Enclosure.sfrac Bool.true 8000000 1274918864) (Enclosure.sfrac Bool.true 285536000 1274918864)) Bool.true 8000000 1274918864 0 1 Bool.true 285536000 1274918864 0 1

noncomputable def ep247 := @ep245 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 1258918864 78682429 159364858 0 1 Bool.true 285536000 17846000 79682429 0 1 (ep246 (BSN.N_div_s_sub_one_mk qz38 17846 1000 4 qz39 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 8000000 1274918864) (Enclosure.sfrac Bool.true 285536000 1274918864) Bool.true 8000000 1274918864 0 1 Bool.true 285536000 1274918864 0 1 (Enclosure.Real.IsNear.const Bool.true 8000000 1274918864) (Enclosure.Real.IsNear.const Bool.true 285536000 1274918864))) qz46 rfl

noncomputable abbrev qz111 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz315 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz374 (@Nat.cast Complex Complex.instNatCast 4) 1))

noncomputable abbrev qz112 := qz315

noncomputable def ep248 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz9 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz112)) Bool.false 1 96 0 1

noncomputable def ep249 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz112) Bool.false 0 1 0 1 Bool.false

noncomputable def ep250 := @ep249 0 1 0 1 Bool.false 1 96 0 1 Bool.false 8923 24000 0 1 Bool.false 1 1 96 0 1 Bool.false 8923 8923 24000 0

noncomputable def ep251 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (Complex.mk qz47 qz47) Bool.false 0 1 0 1 Bool.false

noncomputable def ep252 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz112 Bool.false 1 96 0 1 Bool.false 8923 24000 0 1

noncomputable abbrev qz113 := (Complex.re qz315)

noncomputable abbrev qz114 := (Complex.im qz315)

noncomputable def ep253 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz113) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz114) 1 96 0 1 0 1 0

noncomputable def ep254 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz113 1 24 0 1 1 4 0 1 1

noncomputable def ep255 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep256 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep257 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz47) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow02.d6 rfl) qz285

noncomputable def ep258 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz12 Bool.false 1 2 0 1 Bool.false 17846 1000 0 1 (BSN.ascPochhammer_one_eval qz12)

noncomputable def ep259 := ep258 (@Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk qz33 qz38) Bool.false 1 2 0 1 Bool.false 17846 1000 0 1 (BSN.s_crit_mk qz38 Bool.false 17846 1000 qz39) (@Enclosure.Complex.IsNear.mk qz33 qz38 Bool.false 1 2 0 1 Bool.false 17846 1000 0 1 qz34 qz88))

noncomputable def ep260 := @ep256 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep257) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 17846 1000 0 1 ep259)

noncomputable def ep261 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 17846 1000 0 1 0 1 0

noncomputable def ep262 := @ep261 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep257) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 17846 1000 0 1 ep259)

noncomputable def ep263 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) 8923 6000 0 1 0 1 0 1 8923

noncomputable def ep264 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 17846 1000 0 1 8923 6000 0

noncomputable def ep265 := @ep264 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep257) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 17846 1000 0 1 ep259)

noncomputable def ep266 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep267 := @ep266 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep257) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 17846 1000 0 1 ep259)

noncomputable def ep268 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 8923 6000 0 1 (@ep255 1 24 0 1 (ep260 rfl) (ep262 rfl) rfl rfl) (@ep263 8923 6000 0 1 (ep265 rfl) (ep267 rfl) rfl rfl)

noncomputable def ep269 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 8923 6000 0 1 ep268

noncomputable abbrev qz115 := (@Enclosure.Complex.IsNear.of_eq qz315 (Complex.mk (Enclosure.sfrac Bool.false 1 4) qz281) Bool.false 1 4 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 4 1 4 EMRow02.d7 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 4) qz281 Bool.false 1 4 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 4) qz282))

noncomputable def ep270 := @ep254 96 0 1 ep269 (@Enclosure.Complex.IsNear.re_isNear qz112 Bool.false 1 4 0 1 Bool.false 0 1 0 1 qz115)

noncomputable def ep271 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz114 8923 6000 0 1 0 1 0 1 0

noncomputable def ep272 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 8923 6000 0 1 ep268

noncomputable def ep273 := @ep271 1 0 1 ep272 (@Enclosure.Complex.IsNear.im_isNear qz112 Bool.false 1 4 0 1 Bool.false 0 1 0 1 qz115)

noncomputable def ep274 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz114) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz113) 0 1 0 1 8923 24000 0

noncomputable def ep275 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz114 1 24 0 1 0 1 0 1 0

noncomputable def ep276 := @ep275 1 0 1 ep269 (@Enclosure.Complex.IsNear.im_isNear qz112 Bool.false 1 4 0 1 Bool.false 0 1 0 1 qz115)

noncomputable def ep277 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz113 8923 6000 0 1 1 4 0 1 8923

noncomputable def ep278 := @ep277 24000 0 1 ep272 (@Enclosure.Complex.IsNear.re_isNear qz112 Bool.false 1 4 0 1 Bool.false 0 1 0 1 qz115)

noncomputable def ep279 := @ep250 1 (@ep251 0 1 0 1 (BSN.bern_sum_base qz12 4) qz64) (ep252 (@ep253 1 1 1 96 0 1 (ep270 rfl) (ep273 rfl) rfl rfl) (@ep274 1 8923 8923 24000 0 1 (ep276 rfl) (ep278 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep280 := ep244 (ep247 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep248 Bool.false 8923 24000 0 1 (BSN.bern_sum_succ qz12 4 0 1 1 rfl rfl) (ep279 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep281 := @Enclosure.Real.IsNear.mulLit_ff qz99 (Complex.im (@HAdd.hAdd Complex Complex Complex qz9 qz73 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))))) 1644731895 8589934592 41156429863 80668075753472 282702313967

noncomputable def ep282 := @ep281 1912378296000 0 1 30997967504788591831 1095146965186694348800 11635017956890640796521 ep223 (@Enclosure.Complex.IsNear.im_isNear qz72 Bool.false 991872225 2147483648 10372318769 20167018938368 Bool.false 1644731895 8589934592 41156429863 80668075753472 (ep226 ep240))

noncomputable def ep283 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz9 qz73 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))) Bool.false 3856439021 7649513184 0 1 Bool.false

noncomputable def ep284 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz98 (Complex.im (@HAdd.hAdd Complex Complex Complex qz9 qz73 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz99 (Complex.re (@HAdd.hAdd Complex Complex Complex qz9 qz73 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))))) 3738727642227958221 54757348259334717440 2932278517199644946623

noncomputable def ep285 := nat_lit 38566969312755924860928000

noncomputable def ep286 := nat_lit 197660911546953415490046548412303671296

noncomputable def ep287 := @Enclosure.Real.IsNear.mulLit_ff qz98 (Complex.im (@HAdd.hAdd Complex Complex Complex qz9 qz73 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))))) 991872225 2147483648 10372318769 20167018938368 282702313967

noncomputable def ep288 := @ep287 1912378296000 0 1 3738727642227958221 54757348259334717440 2932278517199644946623 ep285 (@Enclosure.Complex.IsNear.re_isNear qz72 Bool.false 991872225 2147483648 10372318769 20167018938368 Bool.false 1644731895 8589934592 41156429863 80668075753472 (ep226 ep240))

noncomputable def ep289 := @Enclosure.Real.IsNear.mulLit_ff qz99 (Complex.re (@HAdd.hAdd Complex Complex Complex qz9 qz73 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz76 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))))) 1644731895 8589934592 41156429863 80668075753472 3856439021

noncomputable def ep290 := @ep289 7649513184 0 1 2114269419653758265 21902939303733886976 158717262088722884123 617071509004094797774848 (@Enclosure.Complex.IsNear.im_isNear qz72 Bool.false 991872225 2147483648 10372318769 20167018938368 Bool.false 1644731895 8589934592 41156429863 80668075753472 (ep226 ep240))

noncomputable abbrev qz316 := (ep280 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep291 := @ep221 18048802382724707767 109514696518669434880 8568071598496550136207 ep177 (@ep222 154267877251023699443712 30997967504788591831 1095146965186694348800 11635017956890640796521 ep223 ep224 224008349317617523169 1095146965186694348800 17211744265304308648507 ep54 (ep241 (@ep242 282702313967 1912378296000 0 1 qz316) rfl) (ep282 (@ep283 282702313967 1912378296000 0 1 qz316) rfl) rfl rfl) (@ep284 ep285 2114269419653758265 21902939303733886976 158717262088722884123 617071509004094797774848 ep286 18048802382724707767 109514696518669434880 8568071598496550136207 ep177 (ep288 (@ep283 282702313967 1912378296000 0 1 qz316) rfl) (ep290 (@ep242 282702313967 1912378296000 0 1 qz316) rfl) rfl rfl)

noncomputable def ep292 := @ep182 42285438419648151608207 ep177 (@ep183 5041754734592 (BSN.head_sum_c_eq qz12 4) (ep184 (BSN.head_sum_c_succ qz12 3 4 rfl rfl) (ep220 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep291 rfl rfl rfl

noncomputable def ep293 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz12 1 4) Bool.false 2538635567928348349569 1095146965186694348800 85279091768549025148507 ep54 Bool.true 10213027524795692873 109514696518669434880 42285438419648151608207 ep177 (@ep178 ep54 Bool.true 10213027524795692873 109514696518669434880 42285438419648151608207 ep177 (BSN.zetaApproximant_eq_folded' qz12 1 4 rfl) (ep292 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep294 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))))) qz11)) (Complex.im (zetaApproximant qz12 1 4)) 3 16384 675951

noncomputable def ep295 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))))) qz11)) Bool.false 12 65536 1351902

noncomputable def ep296 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))))) qz11) (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 25) qz13) Bool.false 25 131072 65

noncomputable def ep297 := BSN.sin_dyadic_bound_f 25 131072 1 0 65536 18782 0 1 1 0 1 1 12 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 25) (BSN.sinEvenQ 131072) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 25) (BSN.sinOddQ 131072) 0 0 rfl) rfl rfl

noncomputable def ep298 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz12 1 4) Bool.false 2538635567928348349569 1095146965186694348800 85279091768549025148507 ep54 Bool.true 10213027524795692873 109514696518669434880 42285438419648151608207 ep177 (@ep178 ep54 Bool.true 10213027524795692873 109514696518669434880 42285438419648151608207 ep177 (BSN.zetaApproximant_eq_folded' qz12 1 4 rfl) (ep292 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow02.d8 : Enclosure.Real.IsNear (hardyZApproximantEM 1 4 qz38) Bool.false ep38 ep39 ep40 ep41 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 4 qz38) ep42 Bool.false ep38 ep39 ep40 ep41 (@Eq.refl Real ep42) (@ep43 Bool.false ep38 ep39 ep40 ep41 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz8 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz10 (@Nat.cast Complex Complex.instNatCast j))))) qz11) (zetaApproximant qz12 1 4)) (@ep45 ep46 ep47 ep48 30639082574387078619 ep49 ep50 ep51 ep52 ep38 ep39 ep40 ep41 (@ep53 1230897152 2538635567928348349569 1095146965186694348800 85279091768549025148507 ep54 ep44 ep46 ep47 ep48 (@ep55 2461794304 65535 65536 675951 1230897152 (@ep56 131072 Bool.false 65535 65536 1 18782 (@ep58 25 131072 65 131072 ep175 rfl) (Enclosure.sfrac_false_div 25 131072) (ep176 rfl rfl) rfl rfl) rfl) ep293 rfl) (@ep294 1230897152 10213027524795692873 109514696518669434880 42285438419648151608207 ep177 30639082574387078619 ep49 ep50 ep51 (@ep295 2461794304 3 16384 675951 1230897152 (@ep296 131072 Bool.false 12 65536 1 18782 (@ep58 25 131072 65 131072 ep175 rfl) (Enclosure.sfrac_false_div 25 131072) (ep297 rfl rfl) rfl rfl) rfl) ep298 rfl) rfl rfl))

theorem EMRow02.d9 : @Eq Nat (Nat.pow 5 1) 5 := @Eq.refl Nat 5

noncomputable def ep299 := nat_lit 2681950784884925507682931

noncomputable def ep300 := nat_lit 1860675696847002533888000

noncomputable def ep301 := nat_lit 8058317998205215025873205833983

noncomputable def ep302 := nat_lit 2133230176482938983746595979264000

noncomputable abbrev qz393 := (Enclosure.sfrac Bool.false 23170 1000)

noncomputable abbrev qz379 := (@HAdd.hAdd Complex Complex Complex qz387 (@HAdd.hAdd Complex Complex Complex qz387 qz388 (@HMul.hMul Complex Complex Complex qz386 Complex.I (@HDiv.hDiv Complex Complex Complex qz389 (↑qz393) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz317 := qz379

noncomputable abbrev qz116 := (Complex.Stirling.logGammaStirling 1 qz317)

noncomputable abbrev qz380 := (@HAdd.hAdd Complex Complex Complex qz387 qz388 (@HMul.hMul Complex Complex Complex qz386 Complex.I (@HDiv.hDiv Complex Complex Complex qz389 (↑qz393) (2 : Complex))))

noncomputable abbrev qz318 := qz380

noncomputable abbrev qz117 := qz318

noncomputable abbrev qz381 := qz393

noncomputable abbrev qz319 := qz381

noncomputable abbrev qz118 := (@HMul.hMul Real Real Real qz249 (@HDiv.hDiv Real Real Real qz252 qz319 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz394 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 23170 1000)))

noncomputable abbrev qz382 := qz394

noncomputable abbrev qz320 := qz382

noncomputable abbrev qz119 := qz320

noncomputable def ep303 := Complex.re (@HMul.hMul Complex Complex Complex qz5 (Complex.exp (@HMul.hMul Complex Complex Complex qz5 Complex.I ↑(@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))))) qz118))) (zetaApproximant qz119 1 5))

noncomputable def ep304 := @Enclosure.Real.IsNear.of_eq ep303 (@HSub.hSub Real Real Real qz6 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))))) qz118)) (Complex.re (zetaApproximant qz119 1 5))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))))) qz118)) (Complex.im (zetaApproximant qz119 1 5))))

noncomputable def ep305 := nat_lit 1340996606858407861993367

noncomputable def ep306 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))))) qz118)) (Complex.re (zetaApproximant qz119 1 5))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))))) qz118)) (Complex.im (zetaApproximant qz119 1 5))) ep305

noncomputable def ep307 := nat_lit 3952782733933965732179011179461

noncomputable def ep308 := nat_lit 1066615088241469491873297989632000

noncomputable def ep309 := nat_lit 152752530337283561515183475061

noncomputable def ep310 := nat_lit 2495120322787562079738266650623271684343332864000

noncomputable def ep311 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))))) qz118)) (Complex.re (zetaApproximant qz119 1 5)) 131071 131072 826207

noncomputable def ep312 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))))) qz118)) Bool.true 131071 131072 1652414

noncomputable abbrev qz120 := (@HDiv.hDiv Real Real Real qz252 (@Nat.cast Real Real.instNatCast 411745) qz261)

noncomputable def ep313 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))))) qz118) qz120 Bool.false 411745 131072 81

noncomputable def ep314 := nat_lit 11539660800000000000000000

noncomputable def ep315 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))))) qz118) Bool.false 3395395810672474843 1080863910568919040 7011922593354531494663 ep314

noncomputable def ep316 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))))) qz118 88647403573630035527 5404319552844595200 2932120030854531494663 ep314 173823657 13107200

noncomputable def ep317 := nat_lit 222520659848231311310848000

noncomputable def ep318 := nat_lit 1923276800000000000000000

noncomputable def ep319 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 16114911553204186897 900719925474099200 733193806829596479489 ep318 Bool.false 88647403573630035527 5404319552844595200

noncomputable def ep320 := @Enclosure.Complex.IsNear.subLitP qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 11696487581773236297 900719925474099200 681993806816133541889 ep318 Bool.false 104928140209104627527 5404319552844595200 2317720030842991833863

noncomputable def ep321 := nat_lit 72575109666118877034983425847590912

noncomputable def ep322 := nat_lit 24952025856347637716863098879475712

noncomputable abbrev qz321 := (@HSub.hSub Complex Complex Complex qz365 qz379 qz371)

noncomputable abbrev qz322 := (Complex.log qz379)

noncomputable abbrev qz121 := (@HSub.hSub Complex Complex Complex qz255 (@HMul.hMul Complex Complex Complex qz254 qz321 qz322) qz317)

noncomputable abbrev qz122 := qz317

noncomputable def ep323 := @Enclosure.Complex.IsNear.of_eq qz116 (@HAdd.hAdd Complex Complex Complex qz9 (@HAdd.hAdd Complex Complex Complex qz9 qz121 qz15) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz7 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz18 qz122 (@HSub.hSub Int Int Int qz20 qz21 (@HMul.hMul Int Int Int qz22 qz23 (@Nat.cast Int instNatCastInt k)))))) Bool.true 11696487581773236297

noncomputable def ep324 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz9 qz121 qz15) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz7 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz18 qz122 (@HSub.hSub Int Int Int qz20 qz21 (@HMul.hMul Int Int Int qz22 qz23 (@Nat.cast Int instNatCastInt k))))) Bool.true 11697700181903181897 900719925474099200

noncomputable def ep325 := nat_lit 3139751977611635973980946432

noncomputable def ep326 := nat_lit 1408321658213146802096019865600

noncomputable def ep327 := @ep324 1331977172896329397 3756400000000000000000 Bool.false 34988533823039693421 1801439850948198400 754250000155599479 3756400000000000000000 Bool.false 361383 268435456 3 268435456 Bool.true 279108137 40265318400 2317 40265318400 Bool.true ep325 11696487581773236297 900719925474099200 681993806816133541889 ep318 Bool.false ep326

noncomputable def ep328 := @Enclosure.Complex.IsNear.addLitP qz121 qz15 Bool.true 12525398791397607497 900719925474099200 1246000000044766897 3756400000000000000000

noncomputable def ep329 := @ep328 Bool.false 34988533823039693421 1801439850948198400 754250000155599479 3756400000000000000000 Bool.false 60223 65536 3 131072 Bool.false 0 1 0 1 Bool.true 766620479121206928801792 11697700181903181897 900719925474099200 1331977172896329397 3756400000000000000000 Bool.false 34988533823039693421 34988533823039693421 1801439850948198400

noncomputable abbrev qz123 := (@HMul.hMul Complex Complex Complex qz254 qz321 qz322)

noncomputable def ep330 := @Enclosure.Complex.IsNear.subLitP qz123 qz122 Bool.true 10498778959080884297 900719925474099200 1246000000044766897 3756400000000000000000 Bool.false 11171642899254914377

noncomputable def ep331 := @ep330 360287970189639680 754250000155599479 3756400000000000000000 Bool.false 9000 4000 0 1 Bool.false 46340 4000 0 1 Bool.true 50101595165590429988000 12525398791397607497 900719925474099200 1246000000044766897 3756400000000000000000 Bool.false 27990827058431754736800 34988533823039693421 1801439850948198400 754250000155599479 3756400000000000000000

noncomputable abbrev qz124 := qz321

noncomputable abbrev qz125 := qz322

noncomputable def ep332 := @Enclosure.Complex.IsNear.mul qz124 qz125 Bool.true 10498778959080884297 900719925474099200 1246000000044766897 3756400000000000000000 Bool.false 11171642899254914377 360287970189639680 754250000155599479

noncomputable abbrev qz126 := (Complex.re qz321)

noncomputable abbrev qz127 := (Complex.re qz322)

noncomputable abbrev qz128 := (Complex.im qz321)

noncomputable abbrev qz129 := (Complex.im qz322)

noncomputable def ep333 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz126 qz127) (@HMul.hMul Real Real Real qz0 qz128 qz129) 155622304837176135 36028797018963968 1750000000460159 75128000000000000000 1798667072501285959 112589990684262400

noncomputable def ep334 := nat_lit 47282297007961874392022988527501312

noncomputable def ep335 := @Enclosure.Real.IsNear.mulLit_ff qz126 qz127 7000 4000 0 1 22231757833882305 9007199254740992 250000000065737 18782000000000000000

noncomputable def ep336 := @Enclosure.Complex.IsNear.re_isNear qz124 Bool.false 7000 4000 0 1 Bool.false 46340 4000 0 1

noncomputable abbrev qz323 := (Enclosure.sfrac Bool.false 46340 4000)

noncomputable abbrev qz130 := qz323

noncomputable def ep337 := @Enclosure.Complex.IsNear.of_eq qz124 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz130) Bool.false 7000 4000 0 1 Bool.false 46340 4000 0

noncomputable abbrev qz131 := (Complex.log (Complex.mk qz272 qz323))

noncomputable def ep338 := @Enclosure.Complex.IsNear.of_eq qz125 qz131 Bool.false 22231757833882305 9007199254740992 250000000065737 18782000000000000000 Bool.false 776291356280227 562949953421312 500000000009391 18782000000000000000

noncomputable def ep339 := BSN.log_dyadic_bound 180395600 4276395600 2 1 54862677983098080000 131072 37564 32542572499360000 32542572499360000 11064 4456791200 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 180395600) (BSN.artanhQ 4276395600) 0 1 32542572499360000 54862677983098080000 32542572499360000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz324 := (Real.log (Enclosure.sfrac Bool.false 2228395600 16000000))

noncomputable def ep340 := @Enclosure.Real.IsNear.mulLit_ff qz33 qz324 1 2 0 1 22231757833882305 4503599627370496 250000000065737 9391000000000000000 22231757833882305 9007199254740992 250000000065737 18782000000000000000 qz34 (BSN.isNear_log_sfrac 2228395600 16000000 22231757833882305 4503599627370496 250000000065737 9391000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 2228395600) qz274)) Bool.false 23311687702420971847680 4722366482869645213696 1000000000262948 37564000000000000000 22231757833882305 4503599627370496 250000000065737 9391000000000000000 (BSN.log_rat_reduce_isNear 2228395600 16000000 7 4456791200 4096000000 11064 131072 24973259072661432 36028797018963968 37564 1000000000000000 rfl rfl rfl rfl (ep339 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep341 := BSN.arctan_dyadic_bound_f 9000 46340 2 1 131072 37564 6561000000000000 23056539314496800000 6561000000000000 19683000000000000 32279155040295520000 19683000000000000 25143 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 46340) 0 1 6561000000000000 23056539314496800000 6561000000000000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.arctanOddP 9000) (BSN.arctanOddQ 46340) 0 1 19683000000000000 32279155040295520000 19683000000000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz325 := (Real.arctan (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 46340)))

noncomputable def ep342 := @Enclosure.Real.IsNear.subLit_ff_p qz35 qz325 884279719003555 562949953421312 1 2000000000000000 25143 131072 1 37564 101750060650361913344 776291356280227 562949953421312 500000000009391 18782000000000000000 qz36 (ep341 rfl) rfl rfl

noncomputable abbrev qz132 := (Complex.mk qz272 qz323)

noncomputable abbrev qz133 := qz319

noncomputable abbrev qz326 := (@Eq.refl Real qz381)

noncomputable abbrev qz134 := qz326

noncomputable abbrev qz327 := (@Nat.cast Real Real.instNatCast 46340)

noncomputable abbrev qz135 := (Real.arctan (@HDiv.hDiv Real Real Real qz252 qz327 qz278))

noncomputable def ep343 := @Enclosure.Complex.IsNear.re_isNear qz125 Bool.false 22231757833882305 9007199254740992 250000000065737 18782000000000000000 Bool.false 776291356280227 562949953421312 500000000009391 18782000000000000000 (ep338 (@congrArg Complex Complex qz122 qz132 Complex.log (BSN.w_shift_mk qz133 Bool.false 23170 1000 2 qz134 rfl)) (@Enclosure.Complex.IsNear.of_parts qz131 Bool.false 22231757833882305 9007199254740992 250000000065737 18782000000000000000 Bool.false 776291356280227 562949953421312 500000000009391 18782000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz131) (@HMul.hMul Real Real Real qz0 qz33 qz324) Bool.false 22231757833882305 9007199254740992 250000000065737 18782000000000000000 (Enclosure.clog_re_eq 9000 46340 4000 2228395600 16000000 rfl rfl rfl) (ep340 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz131) qz135 Bool.false 776291356280227 562949953421312 500000000009391 18782000000000000000 (Enclosure.clog_im_eq 9000 46340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz135 (@HSub.hSub Real Real Real qz6 qz35 qz325) Bool.false 776291356280227 562949953421312 500000000009391 18782000000000000000 (BSN.arctan_recip 46340 9000 rfl rfl) ep342))))

noncomputable def ep344 := @Enclosure.Real.IsNear.mulLit_ff qz128 qz129 46340 4000 0 1 776291356280227 562949953421312 500000000009391 18782000000000000000

noncomputable def ep345 := @Enclosure.Complex.IsNear.im_isNear qz124 Bool.false 7000 4000 0 1 Bool.false 46340 4000 0 1

noncomputable def ep346 := @Enclosure.Complex.IsNear.im_isNear qz125 Bool.false 22231757833882305 9007199254740992 250000000065737 18782000000000000000 Bool.false 776291356280227 562949953421312 500000000009391 18782000000000000000 (ep338 (@congrArg Complex Complex qz122 qz132 Complex.log (BSN.w_shift_mk qz133 Bool.false 23170 1000 2 qz134 rfl)) (@Enclosure.Complex.IsNear.of_parts qz131 Bool.false 22231757833882305 9007199254740992 250000000065737 18782000000000000000 Bool.false 776291356280227 562949953421312 500000000009391 18782000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz131) (@HMul.hMul Real Real Real qz0 qz33 qz324) Bool.false 22231757833882305 9007199254740992 250000000065737 18782000000000000000 (Enclosure.clog_re_eq 9000 46340 4000 2228395600 16000000 rfl rfl rfl) (ep340 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz131) qz135 Bool.false 776291356280227 562949953421312 500000000009391 18782000000000000000 (Enclosure.clog_im_eq 9000 46340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz135 (@HSub.hSub Real Real Real qz6 qz35 qz325) Bool.false 776291356280227 562949953421312 500000000009391 18782000000000000000 (BSN.arctan_recip 46340 9000 rfl rfl) ep342))))

noncomputable abbrev qz328 := (Enclosure.Real.IsNear.const Bool.false 46340 4000)

noncomputable abbrev qz136 := (@ep337 1 (BSN.w_sub_half_mk qz319 Bool.false 23170 1000 2 qz326 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz323 Bool.false 7000 4000 0 1 Bool.false 46340 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz328))

noncomputable def ep347 := @ep333 1158500000021758947 3756400000000000000000 ep334 10498778959080884297 900719925474099200 1246000000044766897 3756400000000000000000 (@ep335 155622304837176135 36028797018963968 1750000000460159 75128000000000000000 (ep336 qz136) ep343 rfl) (@ep344 1798667072501285959 112589990684262400 1158500000021758947 3756400000000000000000 (ep345 qz136) ep346 rfl) rfl

noncomputable def ep348 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz126 qz129) (@HMul.hMul Real Real Real qz0 qz128 qz127) 5434039493961589 2251799813685248 3500000000065737 75128000000000000000 10302196580221060137 360287970189639680

noncomputable def ep349 := nat_lit 25156303399100339986888243068010496

noncomputable def ep350 := @Enclosure.Real.IsNear.mulLit_ff qz126 qz129 7000 4000 0 1 776291356280227 562949953421312 500000000009391 18782000000000000000

noncomputable def ep351 := @Enclosure.Real.IsNear.mulLit_ff qz128 qz127 46340 4000 0 1 22231757833882305 9007199254740992 250000000065737 18782000000000000000

noncomputable def ep352 := @ep348 579250000152312629 3756400000000000000000 ep349 11171642899254914377 360287970189639680 754250000155599479 3756400000000000000000 (@ep350 5434039493961589 2251799813685248 3500000000065737 75128000000000000000 (ep336 qz136) ep346 rfl) (@ep351 10302196580221060137 360287970189639680 579250000152312629 3756400000000000000000 (ep345 qz136) ep343 rfl) rfl

noncomputable def ep353 := @Enclosure.Complex.IsNear.of_eq qz122 qz132 Bool.false 9000 4000 0 1 Bool.false 46340 4000 0 1 (BSN.w_shift_mk qz133 Bool.false 23170 1000 2 qz134 rfl)

noncomputable abbrev qz329 := (ep353 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 46340 4000) Bool.false 9000 4000 0 1 Bool.false 46340 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 46340 4000)))

noncomputable abbrev qz137 := qz329

noncomputable def ep354 := ep331 (@ep332 3756400000000000000000 (ep347 rfl) (ep352 rfl)) qz137 rfl rfl rfl rfl rfl rfl

noncomputable def ep355 := @ep329 754250000155599479 3756400000000000000000 (ep354 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz43 (↑qz4) Bool.false 60223 65536 3 131072 Bool.false 0 1 0 1 (@ep100 65536 3 131072 (ep102 rfl) (ep104 rfl) rfl rfl) (@ep105 1 0 1 (ep107 rfl) (ep109 rfl) rfl rfl))

noncomputable abbrev qz330 := (@HPow.hPow Complex Int Complex qz373 qz379 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz138 := qz330

noncomputable def ep356 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz7 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz18 qz122 (@HSub.hSub Int Int Int qz20 qz21 (@HMul.hMul Int Int Int qz22 qz23 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz9 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz7 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz18 qz122 (@HSub.hSub Int Int Int qz20 qz21 (@HMul.hMul Int Int Int qz22 qz23 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50) qz138)) Bool.false 361383 268435456 3 268435456

noncomputable def ep357 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz7 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz18 qz122 (@HSub.hSub Int Int Int qz20 qz21 (@HMul.hMul Int Int Int qz22 qz23 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50) qz138) Bool.false 0 1 0 1 Bool.false

noncomputable def ep358 := @ep357 0 1 0 1 Bool.false 361383 268435456 3 268435456 Bool.true 279108137 40265318400 2317 40265318400 Bool.false 361383 361383 268435456 3 268435456 Bool.true 279108137 279108137 40265318400 2317

noncomputable def ep359 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz7 (@HMul.hMul Complex Complex Complex qz5 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz18 qz122 (@HSub.hSub Int Int Int qz20 qz21 (@HMul.hMul Int Int Int qz22 qz23 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz47 qz47) Bool.false 0 1 0 1 Bool.false

noncomputable def ep360 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50) qz138 Bool.false 361383 268435456 3 268435456 Bool.true 279108137 40265318400 2317 40265318400

noncomputable abbrev qz139 := (Complex.re qz330)

noncomputable abbrev qz140 := (Complex.im qz330)

noncomputable def ep361 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz139) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz140) 361383 268435456 3 268435456 0 1 0

noncomputable def ep362 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz139 1 12 0 1 1084149 67108864 9 67108864 361383

noncomputable def ep363 := @Enclosure.Complex.IsNear.re_isNear qz138 Bool.false 1084149 67108864 9 67108864 Bool.true 279108137 3355443200 2317 3355443200

noncomputable abbrev qz331 := (@HPow.hPow Complex Nat Complex qz374 qz379 1)

noncomputable abbrev qz141 := (@Inv.inv Complex Complex.instInv qz331)

noncomputable def ep364 := @Enclosure.Complex.IsNear.of_eq qz138 qz141 Bool.false 1084149 67108864 9 67108864 Bool.true 279108137 3355443200 2317

noncomputable def ep365 := @Enclosure.Complex.IsNear.of_parts qz141 Bool.false 1084149 67108864 9 67108864 Bool.true 279108137 3355443200 2317

noncomputable abbrev qz142 := (Complex.re qz331)

noncomputable abbrev qz143 := qz331

noncomputable def ep366 := @Enclosure.Real.IsNear.mulLit_ff qz142 (@Inv.inv Real Real.instInv (@DFunLike.coe qz56 Complex (fun (x : Complex) => Real) qz57 Complex.normSq qz143)) 9000 4000 0 1 120461 16777216 1 16777216

noncomputable def ep367 := @Enclosure.Complex.IsNear.re_isNear qz143 Bool.false 9000 4000 0 1 Bool.false 46340 4000 0 1

noncomputable def ep368 := @Enclosure.Complex.IsNear.of_eq qz143 qz122 Bool.false 9000 4000 0 1 Bool.false 46340 4000 0

noncomputable def ep369 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz56 Complex (fun (x : Complex) => Real) qz57 Complex.normSq qz143)) Bool.false 120461 16777216 1 16777216 120461 16777216 1

noncomputable abbrev qz144 := (Complex.im qz331)

noncomputable def ep370 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz56 Complex (fun (x : Complex) => Real) qz57 Complex.normSq qz143) (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 qz142 qz142) (@HMul.hMul Real Real Real qz0 qz144 qz144)) Bool.false 5570989 40000 0 1

noncomputable def ep371 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz142 qz142) (@HMul.hMul Real Real Real qz0 qz144 qz144) 81 16 0 1 5368489 40000

noncomputable def ep372 := @Enclosure.Real.IsNear.mulLit_ff qz142 qz142 9000 4000 0 1 9000 4000 0 1

noncomputable def ep373 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz144 46340 4000 0 1 46340 4000 0 1

noncomputable def ep374 := @Enclosure.Complex.IsNear.im_isNear qz143 Bool.false 9000 4000 0 1 Bool.false 46340 4000 0 1

noncomputable abbrev qz145 := (ep367 (@ep368 1 (BSN.pow_one_c qz317) qz329))

noncomputable abbrev qz146 := (ep374 (@ep368 1 (BSN.pow_one_c qz317) qz329))

noncomputable def ep375 := @ep371 0 1 89135824 5570989 40000 0 1 (@ep372 81 16 0 1 qz145 qz145 rfl) (@ep373 5368489 40000 0 1 qz146 qz146 rfl)

noncomputable def ep376 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz56 Complex (fun (x : Complex) => Real) qz57 Complex.normSq qz143) 5570989 40000 0 1 60230 60231 8388608 (ep370 (Enclosure.Complex.normSq_eq_mul_add_mul qz143) (ep375 rfl rfl)) rfl

noncomputable def ep377 := @Enclosure.Real.IsNear.of_eq (Complex.re qz141) (@HMul.hMul Real Real Real qz0 qz142 (@Inv.inv Real Real.instInv (@DFunLike.coe qz56 Complex (fun (x : Complex) => Real) qz57 Complex.normSq qz143))) Bool.false 1084149 67108864 9 67108864 (Enclosure.Complex.inv_re_eq_mul qz143) (@ep366 1084149 67108864 9 67108864 qz145 (@ep369 16777216 (ep376 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep378 := @Enclosure.Real.IsNear.of_eq (Complex.im qz141) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz144) (@Inv.inv Real Real.instInv (@DFunLike.coe qz56 Complex (fun (x : Complex) => Real) qz57 Complex.normSq qz143))) Bool.true 279108137 3355443200 2317 3355443200 (Enclosure.Complex.inv_im_eq_mul qz143)

noncomputable def ep379 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz144) (@Inv.inv Real Real.instInv (@DFunLike.coe qz56 Complex (fun (x : Complex) => Real) qz57 Complex.normSq qz143)) 46340 4000 0 1 120461 16777216 1

noncomputable def ep380 := @ep379 16777216 279108137 3355443200 2317 3355443200 (@Enclosure.Real.IsNear.neg qz144 Bool.false 46340 4000 0 1 qz146) (@ep369 16777216 (ep376 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep381 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz140 0 1 0 1 279108137 3355443200 2317 3355443200 0

noncomputable def ep382 := @Enclosure.Complex.IsNear.im_isNear qz138 Bool.false 1084149 67108864 9 67108864 Bool.true 279108137 3355443200 2317 3355443200

noncomputable abbrev qz147 := (@ep364 3355443200 (BSN.zpow_one_sub_two_mul qz317 1 1 rfl rfl) (@ep365 3355443200 ep377 (ep378 ep380)))

noncomputable def ep383 := @ep361 1 361383 361383 268435456 3 268435456 (@ep362 268435456 3 268435456 ep119 (ep363 qz147) rfl) (@ep381 1 0 1 ep139 (ep382 qz147) rfl) rfl

noncomputable def ep384 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz140) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz139) 279108137 40265318400 2317 40265318400 0 1 0

noncomputable def ep385 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz140 1 12 0 1 279108137 3355443200 2317 3355443200 279108137

noncomputable def ep386 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 (@Rat.cast Complex Complex.instRatCast (bernoulli qz49)) qz50)) qz139 0 1 0 1 1084149 67108864 9 67108864 0

noncomputable def ep387 := @ep384 1 279108137 279108137 40265318400 2317 40265318400 (@ep385 40265318400 2317 40265318400 ep119 (ep382 qz147) rfl) (@ep386 1 0 1 ep139 (ep363 qz147) rfl) rfl

noncomputable def ep388 := @ep358 40265318400 (@ep359 0 1 0 1 (BSN.stirling_sum_base qz122) qz64) (ep360 (ep383 rfl) (ep387 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep389 := @ep327 104928140209104627527 5404319552844595200 2317720030842991833863 ep314 (ep355 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep356 Bool.true 279108137 40265318400 2317 40265318400 (BSN.stirling_sum_succ qz122 0 1 rfl) (ep388 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep390 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz133 2) Bool.false 22092119857154753 4503599627370496 250000000065737 9391000000000000000 Bool.false 847955033097635 281474976710656

noncomputable abbrev qz148 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz257 qz318 qz283))

noncomputable def ep391 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz133 2) (@HAdd.hAdd Complex Complex Complex qz9 (BSN.logSumC qz133 1) qz148) Bool.false 22092119857154753 4503599627370496 250000000065737 9391000000000000000 Bool.false 847955033097635 281474976710656 500000000009391 9391000000000000000

noncomputable def ep392 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz133 1) qz148 Bool.false 22067105967622849 9007199254740992 250000000065737 18782000000000000000 Bool.false 872133551490467 562949953421312 500000000009391 18782000000000000000 Bool.false

noncomputable def ep393 := nat_lit 397976251026025923722694153469952

noncomputable def ep394 := nat_lit 954712492771361397131171594240

noncomputable abbrev qz149 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz257 qz318 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep395 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz133 1) (@HAdd.hAdd Complex Complex Complex qz9 (BSN.logSumC qz133 0) qz149) Bool.false 22067105967622849 9007199254740992 250000000065737 18782000000000000000 Bool.false 872133551490467 562949953421312 500000000009391 18782000000000000000

noncomputable def ep396 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz133 0) qz149 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz332 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz130))

noncomputable def ep397 := @Enclosure.Complex.IsNear.of_eq qz149 qz332 Bool.false 22067105967622849 9007199254740992 250000000065737 18782000000000000000 Bool.false 872133551490467 562949953421312 500000000009391 18782000000000000000

noncomputable def ep398 := BSN.log_dyadic_bound 100395600 4196395600 2 1 52829208095098080000 131072 37564 10079276499360000 10079276499360000 6272 4296791200 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 100395600) (BSN.artanhQ 4196395600) 0 1 10079276499360000 52829208095098080000 10079276499360000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep399 := @Enclosure.Real.IsNear.mulLit_ff qz33 (Real.log (Enclosure.sfrac Bool.false 2148395600 16000000)) 1 2 0 1 22067105967622849 4503599627370496 250000000065737 9391000000000000000 22067105967622849 9007199254740992 250000000065737 18782000000000000000 qz34 (BSN.isNear_log_sfrac 2148395600 16000000 22067105967622849 4503599627370496 250000000065737 9391000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 2148395600) qz274)) Bool.false 23139037707106096513024 4722366482869645213696 1000000000262948 37564000000000000000 22067105967622849 4503599627370496 250000000065737 9391000000000000000 (BSN.log_rat_reduce_isNear 2148395600 16000000 7 4296791200 4096000000 6272 131072 24973259072661432 36028797018963968 37564 1000000000000000 rfl rfl rfl rfl (ep398 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep400 := BSN.arctan_dyadic_bound_f 1000 46340 1 0 131072 37564 0 1 1 0 1 1 2828 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 46340) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 46340) 0 0 rfl) rfl rfl rfl

noncomputable def ep401 := @Enclosure.Real.IsNear.subLit_ff_p qz35 (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz288 qz327)) 884279719003555 562949953421312 1 2000000000000000 2828 131072 1 37564 114312288860958490624 872133551490467 562949953421312 500000000009391 18782000000000000000 qz36 (ep400 rfl) rfl rfl

noncomputable abbrev qz150 := (@HAdd.hAdd Complex Complex Complex qz257 qz318 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz333 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz130)

noncomputable def ep402 := @ep396 22067105967622849 9007199254740992 250000000065737 18782000000000000000 Bool.false 872133551490467 562949953421312 500000000009391 18782000000000000000 Bool.false 22067105967622849 22067105967622849 9007199254740992 250000000065737 18782000000000000000 Bool.false 872133551490467 872133551490467 562949953421312 500000000009391 18782000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz133 0) (Complex.mk qz47 qz47) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz133) qz64) (ep397 (@congrArg Complex Complex qz150 qz333 Complex.log (BSN.w_shift_mk qz133 Bool.false 23170 1000 0 qz134 rfl)) (@Enclosure.Complex.IsNear.of_parts qz332 Bool.false 22067105967622849 9007199254740992 250000000065737 18782000000000000000 Bool.false 872133551490467 562949953421312 500000000009391 18782000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz332) (@HMul.hMul Real Real Real qz0 qz33 (Real.log (Enclosure.sfrac Bool.false 2148395600 16000000))) Bool.false 22067105967622849 9007199254740992 250000000065737 18782000000000000000 (Enclosure.clog_re_eq 1000 46340 4000 2148395600 16000000 rfl rfl rfl) (ep399 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz332) (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz327 qz288)) Bool.false 872133551490467 562949953421312 500000000009391 18782000000000000000 (Enclosure.clog_im_eq 1000 46340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz327 qz288)) (@HSub.hSub Real Real Real qz6 qz35 (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz288 qz327))) Bool.false 872133551490467 562949953421312 500000000009391 18782000000000000000 (BSN.arctan_recip 46340 1000 rfl rfl) ep401)))) rfl rfl

noncomputable abbrev qz334 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz130))

noncomputable def ep403 := @Enclosure.Complex.IsNear.of_eq qz148 qz334 Bool.false 22117133746686657 9007199254740992 250000000065737 18782000000000000000 Bool.false 823776514704803 562949953421312 500000000009391 18782000000000000000

noncomputable def ep404 := BSN.log_dyadic_bound 124395600 4220395600 2 1 53435217061498080000 131072 37564 15474265299360000 15474265299360000 7728 4344791200 4096000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 124395600) (BSN.artanhQ 4220395600) 0 1 15474265299360000 53435217061498080000 15474265299360000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep405 := @Enclosure.Real.IsNear.mulLit_ff qz33 (Real.log (Enclosure.sfrac Bool.false 2172395600 16000000)) 1 2 0 1 22117133746686657 4503599627370496 250000000065737 9391000000000000000 22117133746686657 9007199254740992 250000000065737 18782000000000000000 qz34 (BSN.isNear_log_sfrac 2172395600 16000000 22117133746686657 4503599627370496 250000000065737 9391000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 2172395600) qz274)) Bool.false 23191495635565708050432 4722366482869645213696 1000000000262948 37564000000000000000 22117133746686657 4503599627370496 250000000065737 9391000000000000000 (BSN.log_rat_reduce_isNear 2172395600 16000000 7 4344791200 4096000000 7728 131072 24973259072661432 36028797018963968 37564 1000000000000000 rfl rfl rfl rfl (ep404 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep406 := BSN.arctan_dyadic_bound_f 5000 46340 1 0 131072 37564 0 1 1 0 1 1 14087 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 46340) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 46340) 0 0 rfl) rfl rfl rfl

noncomputable def ep407 := @Enclosure.Real.IsNear.subLit_ff_p qz35 (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz291 qz327)) 884279719003555 562949953421312 1 2000000000000000 14087 131072 1 37564 107974035335387938816 823776514704803 562949953421312 500000000009391 18782000000000000000 qz36 (ep406 rfl) rfl rfl

noncomputable abbrev qz151 := (@HAdd.hAdd Complex Complex Complex qz257 qz318 qz283)

noncomputable abbrev qz335 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz130)

noncomputable def ep408 := @ep392 22117133746686657 9007199254740992 250000000065737 18782000000000000000 Bool.false 823776514704803 562949953421312 500000000009391 18782000000000000000 Bool.false ep393 22092119857154753 4503599627370496 250000000065737 9391000000000000000 Bool.false ep394 847955033097635 281474976710656 500000000009391 9391000000000000000 (ep395 (BSN.log_sum_c_succ qz133 0 1 rfl) (ep402 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep403 (@congrArg Complex Complex qz151 qz335 Complex.log (BSN.w_shift_mk qz133 Bool.false 23170 1000 1 qz134 rfl)) (@Enclosure.Complex.IsNear.of_parts qz334 Bool.false 22117133746686657 9007199254740992 250000000065737 18782000000000000000 Bool.false 823776514704803 562949953421312 500000000009391 18782000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz334) (@HMul.hMul Real Real Real qz0 qz33 (Real.log (Enclosure.sfrac Bool.false 2172395600 16000000))) Bool.false 22117133746686657 9007199254740992 250000000065737 18782000000000000000 (Enclosure.clog_re_eq 5000 46340 4000 2172395600 16000000 rfl rfl rfl) (ep405 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz334) (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz327 qz291)) Bool.false 823776514704803 562949953421312 500000000009391 18782000000000000000 (Enclosure.clog_im_eq 5000 46340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz327 qz291)) (@HSub.hSub Real Real Real qz6 qz35 (Real.arctan (@HDiv.hDiv Real Real Real qz3 qz291 qz327))) Bool.false 823776514704803 562949953421312 500000000009391 18782000000000000000 (BSN.arctan_recip 46340 5000 rfl rfl) ep407)))) rfl rfl

noncomputable def ep409 := @ep320 ep314 Bool.false 22092119857154753 4503599627370496 250000000065737 9391000000000000000 Bool.false 847955033097635 281474976710656 500000000009391 9391000000000000000 Bool.true ep321 16114911553204186897 900719925474099200 733193806829596479489 ep318 Bool.false ep322 88647403573630035527 5404319552844595200 2932120030854531494663 ep314 (@ep323 900719925474099200 681993806816133541889 ep318 Bool.false 104928140209104627527 5404319552844595200 2317720030842991833863 ep314 (BSN.logGammaStirling_unfold 1 qz122) (ep389 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep390 500000000009391 9391000000000000000 (BSN.log_sum_c_eq qz133 2) (ep391 (BSN.log_sum_c_succ qz133 1 2 rfl) (ep408 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz152 := (@HDiv.hDiv Real Real Real qz252 qz319 (2 : Real))

noncomputable def ep410 := @Enclosure.Real.IsNear.mulLit_ff qz152 (Real.log Real.pi) 23170 2000 0 1 75021 65536 1 32768 173823657 13107200 2317 6553600 (@Enclosure.Real.IsNear.of_eq qz152 (Enclosure.sfrac Bool.false 23170 2000) Bool.false 23170 2000 0 1 (BSN.t_half_eq qz133 Bool.false 23170 1000 qz134) (Enclosure.Real.IsNear.const Bool.false 23170 2000)) EMRow02.d5 rfl

noncomputable def ep411 := @ep316 2317 6553600 ep317 3395395810672474843 1080863910568919040 7011922593354531494663 ep314 (@ep319 2932120030854531494663 ep314 (ep409 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep410 rfl rfl

noncomputable def ep412 := nat_lit 497051685528481738977894509570103180122032396889556143609829398013885025

noncomputable def ep413 := nat_lit 998101209134563639911411158943643136761662872727595209826600207071841

noncomputable def ep414 := nat_lit 1300186060140758118096533811759599573336280251964421412447929165891582561

noncomputable def ep415 := BSN.sin_dyadic_bound_f 421596331 268435456 3 2 131072 37601 ep412 ep193 ep413 ep414 ep196 ep413 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 421596331) qz302 0 2 ep412 ep193 ep413 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 421596331) qz303 0 2 ep414 ep196 ep413 rfl rfl rfl rfl) rfl rfl

noncomputable def ep416 := @ep313 131072 Bool.true 131071 131072 1 18782 (@ep315 411745 131072 81 131072 ep411 rfl) (Enclosure.sfrac_false_div 411745 131072) (BSN.cos_reduce1 qz120 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 29667204414009382010880) qz314) 226375608064910080 72057594037927936 Bool.false 131071 131072 0 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q1 411745 131072 226375608064910080 72057594037927936 0 29667204414009382010880 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131071 131072 29667204414009382010880 18889465931478580854784 421596331 268435456 37601 37564 (ep415 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep417 := nat_lit 1733069390092259295232000

noncomputable abbrev qz383 := (@Neg.neg Complex Complex.instNeg qz394)

noncomputable abbrev qz336 := qz383

noncomputable abbrev qz153 := qz336

noncomputable abbrev qz337 := (@HPow.hPow Complex Complex Complex qz375 (@Nat.cast Complex Complex.instNatCast 5) qz383)

noncomputable abbrev qz154 := qz337

noncomputable abbrev qz338 := (@Nat.cast Complex Complex.instNatCast 5)

noncomputable abbrev qz155 := (@HAdd.hAdd Complex Complex Complex qz257 (@HDiv.hDiv Complex Complex Complex qz265 qz338 (@HSub.hSub Complex Complex Complex qz255 qz320 (1 : Complex))) qz264)

noncomputable abbrev qz156 := qz338

noncomputable def ep418 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz119 1 5) (@HAdd.hAdd Complex Complex Complex qz9 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 5, @HPow.hPow Complex Complex Complex qz70 (@Nat.cast Complex Complex.instNatCast n) qz153) (@HMul.hMul Complex Complex Complex qz5 qz154 (@HAdd.hAdd Complex Complex Complex qz9 qz155 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))))) Bool.false 10231070235661647977 7097914492977152000 592835964170235124917

noncomputable def ep419 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 5, @HPow.hPow Complex Complex Complex qz70 (@Nat.cast Complex Complex.instNatCast n) qz153) (@HMul.hMul Complex Complex Complex qz5 qz154 (@HAdd.hAdd Complex Complex Complex qz9 qz155 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))))) Bool.false 21732272689 17179869184 377777173857 161336151506944

noncomputable def ep420 := nat_lit 175768448260983163930718240768

noncomputable def ep421 := nat_lit 1570952115310007648274874368

noncomputable def ep422 := @ep419 Bool.true 281857371 1073741824 93849178751 40334037876736 Bool.false 1252316577383230977 7097914492977152000 85576702860976481667 216633673761532411904000 Bool.false 2263343820196267593 14195828985954304000 682320421653235694389 ep417 Bool.false ep420 10231070235661647977 7097914492977152000 592835964170235124917 216633673761532411904000 Bool.true ep421 1463063168628148407 14195828985954304000

noncomputable def ep423 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 5, @HPow.hPow Complex Complex Complex qz70 (@Nat.cast Complex Complex.instNatCast n) qz153) (BSN.headSumC qz119 5) Bool.false 21732272689 17179869184 377777173857 161336151506944 Bool.true 281857371 1073741824 93849178751

noncomputable abbrev qz157 := (BSN.headSumC qz320 4)

noncomputable abbrev qz158 := (@HPow.hPow Complex Complex Complex qz293 qz296 qz336)

noncomputable def ep424 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz119 5) (@HAdd.hAdd Complex Complex Complex qz9 qz157 qz158) Bool.false 21732272689 17179869184 377777173857 161336151506944 Bool.true 281857371 1073741824 93849178751 40334037876736

noncomputable def ep425 := @Enclosure.Complex.IsNear.addLitP qz157 qz158 Bool.false 7593547817 8589934592 136113090665 80668075753472 Bool.false 1053089469 17179869184 269986493567 161336151506944 Bool.false

noncomputable abbrev qz159 := (BSN.headSumC qz320 3)

noncomputable abbrev qz160 := (@HPow.hPow Complex Complex Complex qz293 qz298 qz336)

noncomputable def ep426 := @Enclosure.Complex.IsNear.of_eq qz157 (@HAdd.hAdd Complex Complex Complex qz9 qz159 qz160) Bool.false 7593547817 8589934592 136113090665 80668075753472 Bool.false 1053089469 17179869184 269986493567 161336151506944

noncomputable def ep427 := @Enclosure.Complex.IsNear.addLitP qz159 qz160 Bool.false 2888833067 8589934592 75129625773 80668075753472 Bool.false 2095400997 8589934592 74398930845 80668075753472 Bool.false

noncomputable abbrev qz161 := (BSN.headSumC qz320 2)

noncomputable abbrev qz162 := (@HPow.hPow Complex Complex Complex qz293 qz299 qz336)

noncomputable def ep428 := @Enclosure.Complex.IsNear.of_eq qz159 (@HAdd.hAdd Complex Complex Complex qz9 qz161 qz162) Bool.false 2888833067 8589934592 75129625773 80668075753472 Bool.false 2095400997 8589934592 74398930845 80668075753472

noncomputable def ep429 := @Enclosure.Complex.IsNear.addLitP qz161 qz162 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep430 := @Enclosure.Complex.IsNear.of_eq qz161 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz47) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz119)

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz249 qz319 qz300)

noncomputable abbrev qz164 := (Real.sin (@HMul.hMul Real Real Real qz249 qz319 qz300))

noncomputable def ep431 := @Enclosure.Complex.IsNear.of_eq qz162 (Complex.mk (@HMul.hMul Real Real Real qz0 qz81 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz81 (@Neg.neg Real Real.instNeg qz164))) Bool.true 5701101525 8589934592 75129625773 80668075753472 Bool.false 2095400997 8589934592 74398930845 80668075753472 (BSN.cpow_neg_s_mk qz133 23170 1000 2 qz134 rfl)

noncomputable def ep432 := nat_lit 79910291795672425523980680845361

noncomputable def ep433 := BSN.cos_dyadic_bound_f 94547637 268435456 2 1 131072 37601 ep432 ep211 ep432 ep432 ep212 ep432 123025 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 94547637) qz306 0 1 ep432 ep211 ep432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 94547637) qz307 0 1 ep432 ep212 ep432 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz165 := (@HDiv.hDiv Real Real Real qz252 (@Nat.cast Real Real.instNatCast 131565) (@Nat.cast Real Real.instNatCast 8192))

noncomputable abbrev qz339 := (Enclosure.Real.IsNear.const Bool.false 23170 1000)

noncomputable abbrev qz166 := qz339

noncomputable def ep434 := @Enclosure.Real.IsNear.cos_image qz163 qz165 Bool.false 131565 8192 163 131072 Bool.true 123025 131072 1 18782 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 52626021 3276800 2317 1878200 131565 8192 163 131072 (@Enclosure.Real.IsNear.mulLit_ff qz133 qz87 23170 1000 0 1 45426 65536 1 18782 52626021 3276800 2317 1878200 qz166 qz305 rfl) rfl) (Enclosure.sfrac_false_div 131565 8192) (BSN.cos_reduce2 qz165 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 415824906522544046080) (@Nat.cast Real Real.instNatCast 1180591620717411303424)) 226375608064910080 72057594037927936 Bool.false 123025 131072 2 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q2 131565 8192 226375608064910080 72057594037927936 2 415824906522544046080 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 123025 131072 415824906522544046080 1180591620717411303424 94547637 268435456 37601 37564 (ep433 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep435 := BSN.sin_dyadic_bound_f 94547637 268435456 2 1 131072 37601 ep432 ep215 ep432 ep432 ep216 ep432 45217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 94547637) qz302 0 1 ep432 ep215 ep432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 94547637) qz303 0 1 ep432 ep216 ep432 rfl rfl rfl rfl) rfl rfl

noncomputable def ep436 := @Enclosure.Real.IsNear.sin_image qz163 qz165 Bool.false 131565 8192 163 131072 Bool.true 45217 131072 1 18782 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 52626021 3276800 2317 1878200 131565 8192 163 131072 (@Enclosure.Real.IsNear.mulLit_ff qz133 qz87 23170 1000 0 1 45426 65536 1 18782 52626021 3276800 2317 1878200 qz166 qz305 rfl) rfl) (Enclosure.sfrac_false_div 131565 8192) (BSN.sin_reduce2 qz165 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 415824906522544046080) (@Nat.cast Real Real.instNatCast 1180591620717411303424)) 226375608064910080 72057594037927936 Bool.false 45217 131072 2 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q2 131565 8192 226375608064910080 72057594037927936 2 415824906522544046080 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 45217 131072 415824906522544046080 1180591620717411303424 94547637 268435456 37601 37564 (ep435 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep437 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz81 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz81 (@Neg.neg Real Real.instNeg qz164)) Bool.true 5701101525 8589934592 75129625773 80668075753472 Bool.false 2095400997 8589934592 74398930845 80668075753472 (@Enclosure.Real.IsNear.mulLit_ft qz81 (Real.cos qz163) 46341 65536 1 65536 123025 131072 1596269 1230897152 5701101525 8589934592 75129625773 80668075753472 qz89 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.true 123025 131072 3192538 2461794304 123025 131072 1596269 1230897152 (ep434 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz81 (@Neg.neg Real Real.instNeg qz164) 46341 65536 1 65536 45217 131072 1596269 1230897152 2095400997 8589934592 74398930845 80668075753472 qz89 (@Enclosure.Real.IsNear.neg qz164 Bool.true 45217 131072 1596269 1230897152 (@Enclosure.Real.IsNear.recentre' qz164 Bool.true 45217 131072 3192538 2461794304 45217 131072 1596269 1230897152 (ep436 rfl rfl) rfl)) rfl)

noncomputable def ep438 := @ep429 5701101525 8589934592 75129625773 80668075753472 Bool.false 2095400997 8589934592 74398930845 80668075753472 Bool.false 2888833067 2888833067 8589934592 75129625773 80668075753472 Bool.false 2095400997 2095400997 8589934592 74398930845 80668075753472 (ep430 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz47 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz48)) (ep431 ep437) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz249 qz319 qz309)

noncomputable abbrev qz168 := (Real.sin (@HMul.hMul Real Real Real qz249 qz319 qz309))

noncomputable def ep439 := @Enclosure.Complex.IsNear.of_eq qz160 (Complex.mk (@HMul.hMul Real Real Real qz0 qz90 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz90 (@Neg.neg Real Real.instNeg qz168))) Bool.false 2352357375 4294967296 15245866223 20167018938368 Bool.true 3137712525 17179869184 121188631877 161336151506944 (BSN.cpow_neg_s_mk qz133 23170 1000 3 qz134 rfl)

noncomputable def ep440 := nat_lit 55730073085343675209348507075441

noncomputable def ep441 := BSN.cos_dyadic_bound_f 86401723 268435456 2 1 131072 37601 ep440 ep211 ep440 ep440 ep212 ep440 124340 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 86401723) qz306 0 1 ep440 ep211 ep440 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 86401723) qz307 0 1 ep440 ep212 ep440 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz169 := (@HDiv.hDiv Real Real Real qz252 (@Nat.cast Real Real.instNatCast 3336387) qz261)

noncomputable def ep442 := @Enclosure.Real.IsNear.cos_image qz167 qz169 Bool.false 3336387 131072 163 131072 Bool.false 124340 131072 1 18782 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 83409683 3276800 2317 1878200 3336387 131072 163 131072 (@Enclosure.Real.IsNear.mulLit_ff qz133 qz96 23170 1000 0 1 71998 65536 1 18782 83409683 3276800 2317 1878200 qz166 qz310 rfl) rfl) (Enclosure.sfrac_false_div 3336387 131072) (BSN.cos_reduce0 qz169 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 6079980794298241122304) qz314) 226375608064910080 72057594037927936 Bool.false 124340 131072 4 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q0 3336387 131072 226375608064910080 72057594037927936 4 6079980794298241122304 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 124340 131072 6079980794298241122304 18889465931478580854784 86401723 268435456 37601 37564 (ep441 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep443 := BSN.sin_dyadic_bound_f 86401723 268435456 2 1 131072 37601 ep440 ep215 ep440 ep440 ep216 ep440 41463 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 86401723) qz302 0 1 ep440 ep215 ep440 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 86401723) qz303 0 1 ep440 ep216 ep440 rfl rfl rfl rfl) rfl rfl

noncomputable def ep444 := @Enclosure.Real.IsNear.sin_image qz167 qz169 Bool.false 3336387 131072 163 131072 Bool.false 41463 131072 1 18782 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 83409683 3276800 2317 1878200 3336387 131072 163 131072 (@Enclosure.Real.IsNear.mulLit_ff qz133 qz96 23170 1000 0 1 71998 65536 1 18782 83409683 3276800 2317 1878200 qz166 qz310 rfl) rfl) (Enclosure.sfrac_false_div 3336387 131072) (BSN.sin_reduce0 qz169 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 6079980794298241122304) qz314) 226375608064910080 72057594037927936 Bool.false 41463 131072 4 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q0 3336387 131072 226375608064910080 72057594037927936 4 6079980794298241122304 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 41463 131072 6079980794298241122304 18889465931478580854784 86401723 268435456 37601 37564 (ep443 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep445 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz90 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz90 (@Neg.neg Real Real.instNeg qz168)) Bool.false 2352357375 4294967296 15245866223 20167018938368 Bool.true 3137712525 17179869184 121188631877 161336151506944 (@Enclosure.Real.IsNear.mulLit_ff qz90 (Real.cos qz167) 75675 131072 1 131072 31085 32768 1596269 1230897152 2352357375 4294967296 15245866223 20167018938368 qz97 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 124340 131072 3192538 2461794304 31085 32768 1596269 1230897152 (ep442 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz90 (@Neg.neg Real Real.instNeg qz168) 75675 131072 1 131072 41463 131072 1596269 1230897152 3137712525 17179869184 121188631877 161336151506944 qz97 (@Enclosure.Real.IsNear.neg qz168 Bool.false 41463 131072 1596269 1230897152 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 41463 131072 3192538 2461794304 41463 131072 1596269 1230897152 (ep444 rfl rfl) rfl)) rfl)

noncomputable def ep446 := @ep427 2352357375 4294967296 15245866223 20167018938368 Bool.true 3137712525 17179869184 121188631877 161336151506944 Bool.false 32614039534627192832 7593547817 8589934592 136113090665 80668075753472 Bool.false 9045969658234011648 1053089469 17179869184 269986493567 161336151506944 (ep428 (BSN.head_sum_c_succ qz119 2 3 rfl rfl) (ep438 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep439 ep445) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz249 qz319 qz312)

noncomputable abbrev qz171 := (Real.sin (@HMul.hMul Real Real Real qz249 qz319 qz312))

noncomputable def ep447 := @Enclosure.Complex.IsNear.of_eq qz158 (Complex.mk (@HMul.hMul Real Real Real qz0 qz100 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz100 (@Neg.neg Real Real.instNeg qz171))) Bool.false 6545177055 17179869184 105550992527 161336151506944 Bool.true 5562807405 17179869184 105410221437 161336151506944 (BSN.cpow_neg_s_mk qz133 23170 1000 4 qz134 rfl)

noncomputable def ep448 := nat_lit 1278620059707509434023432638595856

noncomputable def ep449 := BSN.cos_dyadic_bound_f 189097322 268435456 2 1 131072 37601 ep448 ep211 ep448 ep448 ep212 ep448 99873 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 189097322) qz306 0 1 ep448 ep211 ep448 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 189097322) qz307 0 1 ep448 ep212 ep448 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz172 := (@HDiv.hDiv Real Real Real qz252 (@Nat.cast Real Real.instNatCast 4210081) qz261)

noncomputable def ep450 := @Enclosure.Real.IsNear.cos_image qz170 qz172 Bool.false 4210081 131072 163 131072 Bool.false 99873 131072 1 18782 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 52626021 1638400 2317 1878200 4210081 131072 163 131072 (@Enclosure.Real.IsNear.mulLit_ff qz133 qz107 23170 1000 0 1 90852 65536 1 18782 52626021 1638400 2317 1878200 qz166 qz313 rfl) rfl) (Enclosure.sfrac_false_div 4210081 131072) (BSN.cos_reduce0 qz172 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 13306541123909485330432) qz314) 226375608064910080 72057594037927936 Bool.false 99873 131072 5 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q0 4210081 131072 226375608064910080 72057594037927936 5 13306541123909485330432 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 99873 131072 13306541123909485330432 18889465931478580854784 189097322 268435456 37601 37564 (ep449 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep451 := BSN.sin_dyadic_bound_f 189097322 268435456 2 1 131072 37601 ep448 ep215 ep448 ep448 ep216 ep448 84883 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 189097322) qz302 0 1 ep448 ep215 ep448 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 189097322) qz303 0 1 ep448 ep216 ep448 rfl rfl rfl rfl) rfl rfl

noncomputable def ep452 := @Enclosure.Real.IsNear.sin_image qz170 qz172 Bool.false 4210081 131072 163 131072 Bool.false 84883 131072 1 18782 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 52626021 1638400 2317 1878200 4210081 131072 163 131072 (@Enclosure.Real.IsNear.mulLit_ff qz133 qz107 23170 1000 0 1 90852 65536 1 18782 52626021 1638400 2317 1878200 qz166 qz313 rfl) rfl) (Enclosure.sfrac_false_div 4210081 131072) (BSN.sin_reduce0 qz172 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 13306541123909485330432) qz314) 226375608064910080 72057594037927936 Bool.false 84883 131072 5 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q0 4210081 131072 226375608064910080 72057594037927936 5 13306541123909485330432 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 84883 131072 13306541123909485330432 18889465931478580854784 189097322 268435456 37601 37564 (ep451 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep453 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz100 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz100 (@Neg.neg Real Real.instNeg qz171)) Bool.false 6545177055 17179869184 105550992527 161336151506944 Bool.true 5562807405 17179869184 105410221437 161336151506944 (@Enclosure.Real.IsNear.mulLit_ff qz100 (Real.cos qz170) 65535 131072 1 131072 99873 131072 1596269 1230897152 6545177055 17179869184 105550992527 161336151506944 qz108 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 99873 131072 3192538 2461794304 99873 131072 1596269 1230897152 (ep450 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz100 (@Neg.neg Real Real.instNeg qz171) 65535 131072 1 131072 84883 131072 1596269 1230897152 5562807405 17179869184 105410221437 161336151506944 qz108 (@Enclosure.Real.IsNear.neg qz171 Bool.false 84883 131072 1596269 1230897152 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 84883 131072 3192538 2461794304 84883 131072 1596269 1230897152 (ep452 rfl rfl) rfl)) rfl)

noncomputable def ep454 := @ep425 6545177055 17179869184 105550992527 161336151506944 Bool.true 5562807405 17179869184 105410221437 161336151506944 Bool.false 186678800934017957888 21732272689 17179869184 377777173857 161336151506944 Bool.true 77476364197218484224 281857371 1073741824 93849178751 40334037876736 (ep426 (BSN.head_sum_c_succ qz119 3 4 rfl rfl) (ep446 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep447 ep453) rfl rfl

noncomputable def ep455 := @Enclosure.Complex.IsNear.mul qz154 (@HAdd.hAdd Complex Complex Complex qz9 qz155 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))) Bool.false 1252316577383230977 7097914492977152000 85576702860976481667 216633673761532411904000 Bool.false

noncomputable abbrev qz173 := (Complex.re qz337)

noncomputable abbrev qz174 := (Complex.im qz337)

noncomputable def ep456 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz173 (Complex.re (@HAdd.hAdd Complex Complex Complex qz9 qz155 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz174 (Complex.im (@HAdd.hAdd Complex Complex Complex qz9 qz155 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))))) 58690359001787769 283916579719086080 30742398487140240011

noncomputable def ep457 := nat_lit 2599604085138388942848000

noncomputable def ep458 := nat_lit 22222089961009945594136993999093760

noncomputable def ep459 := @Enclosure.Real.IsNear.mulLit_ff qz173 (Complex.re (@HAdd.hAdd Complex Complex Complex qz9 qz155 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))))) 7050863079 17179869184 94699711459 161336151506944 324630329

noncomputable abbrev qz340 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz175 := (@Inv.inv Real Real.instInv (Real.sqrt qz340))

noncomputable abbrev qz341 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz381 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable abbrev qz176 := (Real.cos qz341)

noncomputable abbrev qz177 := (@Neg.neg Real Real.instNeg (Real.sin qz341))

noncomputable def ep460 := @Enclosure.Complex.IsNear.of_eq qz154 (Complex.mk (@HMul.hMul Real Real Real qz0 qz175 qz176) (@HMul.hMul Real Real Real qz0 qz175 qz177)) Bool.false 7050863079 17179869184 94699711459 161336151506944 Bool.false 95369859 536870912 47029514633 80668075753472 (BSN.cpow_neg_s_mk qz133 23170 1000 5 qz134 rfl)

noncomputable def ep461 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz340) 293085 131072 1 131072 29308 29309 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz340) (Real.sqrt (@HDiv.hDiv Real Real Real qz3 qz340 qz301)) Bool.false 293085 131072 1 131072 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz3 qz340 qz301)) Bool.false 293085 131072 1 131072 293085 131072 1 131072 (BSN.sqrt_enclosure 5 1 146542 146543 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep462 := nat_lit 141613827518379161815574079375

noncomputable def ep463 := nat_lit 29325128709309236875766211300

noncomputable def ep464 := BSN.log_dyadic_bound 2 3 15 14 ep462 65536 18782 ep463 57299708096576225280000 105476 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP 2) (BSN.artanhQ 3) 0 14 ep463 ep462 57299708096576225280000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep465 := nat_lit 148885448241768627457991784429287449628880081184442322042640515150030625

noncomputable def ep466 := nat_lit 89804444587160857714006733498425705917697565638026223062844125390625

noncomputable def ep467 := nat_lit 389792681056252906715584376889136345504152511805363562893385315856590625

noncomputable def ep468 := BSN.sin_dyadic_bound_f 312005485 268435456 3 2 131072 37601 ep465 ep193 ep466 ep467 ep196 ep466 120287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 312005485) qz302 0 2 ep465 ep193 ep466 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 312005485) qz303 0 2 ep467 ep196 ep466 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz178 := qz341

noncomputable abbrev qz179 := (@HDiv.hDiv Real Real Real qz252 (@Nat.cast Real Real.instNatCast 4887757) qz261)

noncomputable abbrev qz342 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz180 := qz342

noncomputable def ep469 := @Enclosure.Real.IsNear.cos_image qz178 qz179 Bool.false 4887757 131072 163 131072 Bool.false 120287 131072 1 18782 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 61096973 1638400 2317 1878200 4887757 131072 163 131072 (@Enclosure.Real.IsNear.mulLit_ff qz133 qz180 23170 1000 0 1 105476 65536 1 18782 61096973 1638400 2317 1878200 qz166 (BSN.isNear_log_sfrac 5 1 105476 65536 1 18782 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 105476 65536 18782 rfl rfl rfl (ep464 rfl))) rfl) rfl) (Enclosure.sfrac_false_div 4887757 131072) (BSN.cos_reduce3 qz179 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 21955434217551507226624) qz314) 226375608064910080 72057594037927936 Bool.false 120287 131072 5 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q3 4887757 131072 226375608064910080 72057594037927936 5 21955434217551507226624 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 120287 131072 21955434217551507226624 18889465931478580854784 312005485 268435456 37601 37564 (ep468 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep470 := nat_lit 82754050998576864524534994342270105663119021798307079456161550250190625

noncomputable def ep471 := nat_lit 248082544106556271858176969559813465577521670263645185922358962499790625

noncomputable def ep472 := BSN.cos_dyadic_bound_f 312005485 268435456 3 2 131072 37601 ep470 ep200 ep466 ep471 ep202 ep466 52064 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 312005485) qz306 0 2 ep470 ep200 ep466 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 312005485) qz307 0 2 ep471 ep202 ep466 rfl rfl rfl rfl) rfl rfl

noncomputable def ep473 := @Enclosure.Real.IsNear.sin_image qz178 qz179 Bool.false 4887757 131072 163 131072 Bool.true 52064 131072 1 18782 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 61096973 1638400 2317 1878200 4887757 131072 163 131072 (@Enclosure.Real.IsNear.mulLit_ff qz133 qz180 23170 1000 0 1 105476 65536 1 18782 61096973 1638400 2317 1878200 qz166 (BSN.isNear_log_sfrac 5 1 105476 65536 1 18782 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 105476 65536 18782 rfl rfl rfl (ep464 rfl))) rfl) rfl) (Enclosure.sfrac_false_div 4887757 131072) (BSN.sin_reduce3 qz179 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 21955434217551507226624) qz314) 226375608064910080 72057594037927936 Bool.false 52064 131072 5 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q3 4887757 131072 226375608064910080 72057594037927936 5 21955434217551507226624 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 52064 131072 21955434217551507226624 18889465931478580854784 312005485 268435456 37601 37564 (ep472 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz181 := (Real.sin qz341)

noncomputable def ep474 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz175 qz176) (@HMul.hMul Real Real Real qz0 qz175 qz177) Bool.false 7050863079 17179869184 94699711459 161336151506944 Bool.false 95369859 536870912 47029514633 80668075753472 (@Enclosure.Real.IsNear.mulLit_ff qz175 qz176 58617 131072 1 131072 120287 131072 1596269 1230897152 7050863079 17179869184 94699711459 161336151506944 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 58617 131072 1 131072 58617 131072 1 131072 (ep461 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 120287 131072 3192538 2461794304 120287 131072 1596269 1230897152 (ep469 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz175 qz177 58617 131072 1 131072 1627 4096 1596269 1230897152 95369859 536870912 47029514633 80668075753472 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 58617 131072 1 131072 58617 131072 1 131072 (ep461 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz181 Bool.true 1627 4096 1596269 1230897152 (@Enclosure.Real.IsNear.recentre' qz181 Bool.true 52064 131072 3192538 2461794304 1627 4096 1596269 1230897152 (ep473 rfl rfl) rfl)) rfl)

noncomputable def ep475 := @ep459 644518680 0 1 58690359001787769 283916579719086080 30742398487140240011 103984163405535557713920 (@Enclosure.Complex.IsNear.re_isNear qz154 Bool.false 7050863079 17179869184 94699711459 161336151506944 Bool.false 95369859 536870912 47029514633 80668075753472 (ep460 ep474))

noncomputable def ep476 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz9 qz155 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))) Bool.false 324630329 644518680 0 1 Bool.false

noncomputable def ep477 := @Enclosure.Complex.IsNear.addLitP qz155 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) Bool.false 5320989 10741978 0 1 Bool.true 1158500

noncomputable def ep478 := @ep477 5370989 0 1 Bool.false 1 120 0 1 Bool.false 2317 6000 0 1 Bool.false 649260658 324630329 644518680 0 1 Bool.false 5493581513 5493581513 32225934000 0 1

noncomputable abbrev qz182 := (@HDiv.hDiv Complex Complex Complex qz265 qz338 (@HSub.hSub Complex Complex Complex qz255 qz320 (1 : Complex)))

noncomputable def ep479 := @Enclosure.Complex.IsNear.addLitP qz182 qz43 Bool.true 10000000 2148395600 0 1 Bool.true 463400000 2148395600 0 1

noncomputable def ep480 := @Enclosure.Complex.IsNear.of_eq qz182 (Complex.mk (Enclosure.sfrac Bool.true 10000000 2148395600) (Enclosure.sfrac Bool.true 463400000 2148395600)) Bool.true 10000000 2148395600 0 1 Bool.true 463400000 2148395600 0 1

noncomputable def ep481 := @ep479 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 2128395600 5320989 10741978 0 1 Bool.true 463400000 1158500 5370989 0 1 (ep480 (BSN.N_div_s_sub_one_mk qz133 23170 1000 5 qz134 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 10000000 2148395600) (Enclosure.sfrac Bool.true 463400000 2148395600) Bool.true 10000000 2148395600 0 1 Bool.true 463400000 2148395600 0 1 (Enclosure.Real.IsNear.const Bool.true 10000000 2148395600) (Enclosure.Real.IsNear.const Bool.true 463400000 2148395600))) qz46 rfl

noncomputable abbrev qz343 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz374 (@Nat.cast Complex Complex.instNatCast 5) 1))

noncomputable abbrev qz183 := qz343

noncomputable def ep482 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz9 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) qz183)) Bool.false 1 120 0 1

noncomputable def ep483 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) qz183) Bool.false 0 1 0 1 Bool.false

noncomputable def ep484 := @ep483 0 1 0 1 Bool.false 1 120 0 1 Bool.false 2317 6000 0 1 Bool.false 1 1 120 0 1 Bool.false 2317 2317 6000 0

noncomputable def ep485 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (Complex.mk qz47 qz47) Bool.false 0 1 0 1 Bool.false

noncomputable def ep486 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) qz183 Bool.false 1 120 0 1 Bool.false 2317 6000 0 1

noncomputable abbrev qz184 := (Complex.re qz343)

noncomputable abbrev qz185 := (Complex.im qz343)

noncomputable def ep487 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)))) qz184) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)))) qz185) 1 120 0 1 0 1 0

noncomputable def ep488 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)))) qz184 1 24 0 1 1 5 0 1 1

noncomputable def ep489 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep490 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep491 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)) qz119 Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 (BSN.ascPochhammer_one_eval qz119)

noncomputable def ep492 := ep491 (@Enclosure.Complex.IsNear.of_eq qz119 (Complex.mk qz33 qz133) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 (BSN.s_crit_mk qz133 Bool.false 23170 1000 qz134) (@Enclosure.Complex.IsNear.mk qz33 qz133 Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 qz34 qz166))

noncomputable def ep493 := @ep490 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep257) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep492)

noncomputable def ep494 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 23170 1000 0 1 0 1 0

noncomputable def ep495 := @ep494 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep257) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep492)

noncomputable def ep496 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)))) 2317 1200 0 1 0 1 0 1 2317

noncomputable def ep497 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 23170 1000 0 1 2317 1200 0

noncomputable def ep498 := @ep497 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep257) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep492)

noncomputable def ep499 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep500 := @ep499 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep257) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep492)

noncomputable def ep501 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 2317 1200 0 1 (@ep489 1 24 0 1 (ep493 rfl) (ep495 rfl) rfl rfl) (@ep496 2317 1200 0 1 (ep498 rfl) (ep500 rfl) rfl rfl)

noncomputable def ep502 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2317 1200 0 1 ep501

noncomputable abbrev qz186 := (@Enclosure.Complex.IsNear.of_eq qz343 (Complex.mk (Enclosure.sfrac Bool.false 1 5) qz281) Bool.false 1 5 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 5 1 5 EMRow02.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 5) qz281 Bool.false 1 5 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 5) qz282))

noncomputable def ep503 := @ep488 120 0 1 ep502 (@Enclosure.Complex.IsNear.re_isNear qz183 Bool.false 1 5 0 1 Bool.false 0 1 0 1 qz186)

noncomputable def ep504 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)))) qz185 2317 1200 0 1 0 1 0 1 0

noncomputable def ep505 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2317 1200 0 1 ep501

noncomputable def ep506 := @ep504 1 0 1 ep505 (@Enclosure.Complex.IsNear.im_isNear qz183 Bool.false 1 5 0 1 Bool.false 0 1 0 1 qz186)

noncomputable def ep507 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)))) qz185) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)))) qz184) 0 1 0 1 2317 6000 0

noncomputable def ep508 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)))) qz185 1 24 0 1 0 1 0 1 0

noncomputable def ep509 := @ep508 1 0 1 ep502 (@Enclosure.Complex.IsNear.im_isNear qz183 Bool.false 1 5 0 1 Bool.false 0 1 0 1 qz186)

noncomputable def ep510 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz49)) ↑qz111) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)))) qz184 2317 1200 0 1 1 5 0 1 2317

noncomputable def ep511 := @ep510 6000 0 1 ep505 (@Enclosure.Complex.IsNear.re_isNear qz183 Bool.false 1 5 0 1 Bool.false 0 1 0 1 qz186)

noncomputable def ep512 := @ep484 1 (@ep485 0 1 0 1 (BSN.bern_sum_base qz119 5) qz64) (ep486 (@ep487 1 1 1 120 0 1 (ep503 rfl) (ep506 rfl) rfl rfl) (@ep507 1 2317 2317 6000 0 1 (ep509 rfl) (ep511 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep513 := ep478 (ep481 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep482 Bool.false 2317 6000 0 1 (BSN.bern_sum_succ qz119 5 0 1 1 rfl rfl) (ep512 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep514 := @Enclosure.Real.IsNear.mulLit_ff qz174 (Complex.im (@HAdd.hAdd Complex Complex Complex qz9 qz155 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))))) 95369859 536870912 47029514633 80668075753472 5493581513

noncomputable def ep515 := @ep514 32225934000 0 1 13433899853841453 443619655811072000 258360472153211779729 ep457 (@Enclosure.Complex.IsNear.im_isNear qz154 Bool.false 7050863079 17179869184 94699711459 161336151506944 Bool.false 95369859 536870912 47029514633 80668075753472 (ep460 ep474))

noncomputable def ep516 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz9 qz155 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))) Bool.false 324630329 644518680 0 1 Bool.false

noncomputable def ep517 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz173 (Complex.im (@HAdd.hAdd Complex Complex Complex qz9 qz155 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz174 (Complex.re (@HAdd.hAdd Complex Complex Complex qz9 qz155 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1))))))) 993192078499709193 14195828985954304000 520240584157596657467

noncomputable def ep518 := nat_lit 5199208170276777885696000

noncomputable def ep519 := nat_lit 20081276129951701216571351283793920

noncomputable def ep520 := @Enclosure.Real.IsNear.mulLit_ff qz173 (Complex.im (@HAdd.hAdd Complex Complex Complex qz9 qz155 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))))) 7050863079 17179869184 94699711459 161336151506944 5493581513

noncomputable def ep521 := @ep520 32225934000 0 1 993192078499709193 14195828985954304000 520240584157596657467 ep518 (@Enclosure.Complex.IsNear.re_isNear qz154 Bool.false 7050863079 17179869184 94699711459 161336151506944 Bool.false 95369859 536870912 47029514633 80668075753472 (ep460 ep474))

noncomputable def ep522 := @Enclosure.Real.IsNear.mulLit_ff qz174 (Complex.re (@HAdd.hAdd Complex Complex Complex qz9 qz155 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz17 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz17 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz75 qz156 (@HSub.hSub Nat Nat Nat qz74 (@HMul.hMul Nat Nat Nat qz17 2 k) 1)))))) 95369859 536870912 47029514633 80668075753472 324630329

noncomputable def ep523 := @ep522 644518680 0 1 793844838560349 8872393116221440 15267206808021104257 51992081702767778856960 (@Enclosure.Complex.IsNear.im_isNear qz154 Bool.false 7050863079 17179869184 94699711459 161336151506944 Bool.false 95369859 536870912 47029514633 80668075753472 (ep460 ep474))

noncomputable abbrev qz344 := (ep513 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep524 := @ep455 2263343820196267593 14195828985954304000 682320421653235694389 ep417 (@ep456 103984163405535557713920 13433899853841453 443619655811072000 258360472153211779729 ep457 ep458 1252316577383230977 7097914492977152000 85576702860976481667 216633673761532411904000 (ep475 (@ep476 5493581513 32225934000 0 1 qz344) rfl) (ep515 (@ep516 5493581513 32225934000 0 1 qz344) rfl) rfl rfl) (@ep517 ep518 793844838560349 8872393116221440 15267206808021104257 51992081702767778856960 ep519 2263343820196267593 14195828985954304000 682320421653235694389 ep417 (ep521 (@ep516 5493581513 32225934000 0 1 qz344) rfl) (ep523 (@ep476 5493581513 32225934000 0 1 qz344) rfl) rfl rfl)

noncomputable def ep525 := @ep422 4714823675498473606389 ep417 (@ep423 40334037876736 (BSN.head_sum_c_eq qz119 5) (ep424 (BSN.head_sum_c_succ qz119 4 5 rfl rfl) (ep454 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep524 rfl rfl rfl

noncomputable def ep526 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz119 1 5) Bool.false 10231070235661647977 7097914492977152000 592835964170235124917 216633673761532411904000 Bool.true 1463063168628148407 14195828985954304000 4714823675498473606389 ep417 (@ep418 216633673761532411904000 Bool.true 1463063168628148407 14195828985954304000 4714823675498473606389 ep417 (BSN.zetaApproximant_eq_folded' qz119 1 5 rfl) (ep525 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep527 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))))) qz118)) (Complex.im (zetaApproximant qz119 1 5)) 29 131072 826207

noncomputable def ep528 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))))) qz118)) Bool.false 29 131072 1652414

noncomputable def ep529 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))))) qz118) qz120 Bool.false 411745 131072 81

noncomputable def ep530 := nat_lit 276583425830994105494346465831810052573023181770965677654272598988634721

noncomputable def ep531 := nat_lit 827754075074713189203216575177542871445546219567441842543164596551760481

noncomputable def ep532 := BSN.cos_dyadic_bound_f 421596331 268435456 3 2 131072 37601 ep530 ep200 ep413 ep531 ep202 ep413 29 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 421596331) qz306 0 2 ep530 ep200 ep413 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 421596331) qz307 0 2 ep531 ep202 ep413 rfl rfl rfl rfl) rfl rfl

noncomputable def ep533 := @ep529 131072 Bool.false 29 131072 1 18782 (@ep315 411745 131072 81 131072 ep411 rfl) (Enclosure.sfrac_false_div 411745 131072) (BSN.sin_reduce1 qz120 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast 29667204414009382010880) qz314) 226375608064910080 72057594037927936 Bool.false 29 131072 0 1000000000000000 37564 18782 (BSN.sin_reduce_arg_pos_rat_q1 411745 131072 226375608064910080 72057594037927936 0 29667204414009382010880 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 29 131072 29667204414009382010880 18889465931478580854784 421596331 268435456 37601 37564 (ep532 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep534 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz119 1 5) Bool.false 10231070235661647977 7097914492977152000 592835964170235124917 216633673761532411904000 Bool.true 1463063168628148407 14195828985954304000 4714823675498473606389 ep417 (@ep418 216633673761532411904000 Bool.true 1463063168628148407 14195828985954304000 4714823675498473606389 ep417 (BSN.zetaApproximant_eq_folded' qz119 1 5 rfl) (ep525 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow02.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 5 qz133) Bool.true ep299 ep300 ep301 ep302 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 5 qz133) ep303 Bool.true ep299 ep300 ep301 ep302 (@Eq.refl Real ep303) (@ep304 Bool.true ep299 ep300 ep301 ep302 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz6 (Complex.im (@HSub.hSub Complex Complex Complex qz7 qz116 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz9 qz117 (@Nat.cast Complex Complex.instNatCast j))))) qz118) (zetaApproximant qz119 1 5)) (@ep306 930337848423501266944000 ep307 ep308 42428831890216303803 ep300 ep309 ep302 ep310 ep299 ep300 ep301 ep302 (@ep311 1230897152 10231070235661647977 7097914492977152000 592835964170235124917 216633673761532411904000 ep305 930337848423501266944000 ep307 ep308 (@ep312 2461794304 131071 131072 826207 1230897152 (ep416 rfl rfl) rfl) ep526 rfl) (@ep527 1230897152 1463063168628148407 14195828985954304000 4714823675498473606389 ep417 42428831890216303803 ep300 ep309 ep302 (@ep528 2461794304 29 131072 826207 1230897152 (ep533 rfl rfl) rfl) ep534 rfl) rfl rfl))

theorem EMRow02.d11 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow02.d12 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow02.d13 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow02.d14 : @Eq Nat (Nat.pow 4 (Nat.succ (Nat.mul 2 3))) 16384 := @Eq.refl Nat 16384

noncomputable abbrev qz384 := (@HAdd.hAdd Complex Complex Complex qz387 qz391 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz345 := qz384

noncomputable abbrev qz187 := (@HDiv.hDiv Real Real Real qz252 (@Norm.norm Complex Complex.instNorm qz345) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz260) qz308))

noncomputable abbrev qz188 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz189 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz346 := (@HPow.hPow Complex Complex Complex qz375 (@Nat.cast Complex Complex.instNatCast 4) (@HSub.hSub Complex Complex Complex qz365 qz376 qz377))

noncomputable abbrev qz190 := qz346

noncomputable def ep535 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 1 4))) (@HMul.hMul Real Real Real qz0 qz187 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190))) 37401963 1073741824 117575 3221225472 5000280909233 15393162788864 52154875

noncomputable def ep536 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 1 4)) 123 8192 1 221184 304081 131072 227 131072 37401963 1073741824

noncomputable abbrev qz347 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz348 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz191 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz347 qz348 2))

noncomputable def ep537 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz191 96 162 0 1 3321 131072 1 131072 123 8192 1 221184

noncomputable def ep538 := nat_lit 781950621441006189802102638025

noncomputable def ep539 := nat_lit 19807040628566084398385987584

noncomputable def ep540 := nat_lit 26986075409044041160201671

noncomputable def ep541 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz192 := qz347

noncomputable abbrev qz193 := qz348

noncomputable def ep542 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz192 qz193 1) qz193 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep538 ep539 ep540 ep541

noncomputable def ep543 := ep542 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz192 qz193 1) qz193 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz193) (@Enclosure.Real.IsNear.of_eq qz193 qz251 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz2)) (@Enclosure.Real.IsNear.of_eq qz193 qz251 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz2) rfl

noncomputable abbrev qz194 := (@HPow.hPow Real Nat Real qz347 qz348 2)

noncomputable def ep544 := @Enclosure.Real.IsNear.inv_image qz194 ep538 ep539 ep540 ep541 1660 1661 65536 (@Enclosure.Real.IsNear.of_eq qz194 (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz192 qz193 1) qz193) Bool.false ep538 ep539 ep540 ep541 (BSN.pow_succ_r qz193 1 2 rfl) ep543) rfl rfl rfl

noncomputable def ep545 := ep537 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz191 Bool.false 3321 131072 1 131072 3321 131072 1 131072 (ep544 rfl rfl rfl) rfl)

noncomputable def ep546 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 1 4)) (Real.sqrt (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 1 4)) (Complex.re (zetaApproximant qz12 1 4))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 1 4)) (Complex.im (zetaApproximant qz12 1 4))))) Bool.false 304081 131072 227 131072

noncomputable def ep547 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 1 4)) (Complex.re (zetaApproximant qz12 1 4))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 1 4)) (Complex.im (zetaApproximant qz12 1 4))))) Bool.false 304081 131072 227 131072

noncomputable def ep548 := nat_lit 81010345955607241982109241918299209

noncomputable def ep549 := nat_lit 15051585279329608839820853903360000

noncomputable def ep550 := nat_lit 846254505227884612476277203445804158577468473487

noncomputable def ep551 := nat_lit 105771457562386290856657600716689138925583728640000

noncomputable def ep552 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 1 4)) (Complex.re (zetaApproximant qz12 1 4))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 1 4)) (Complex.im (zetaApproximant qz12 1 4)))) ep548 ep549 ep550 ep551 151927 152154

noncomputable def ep553 := nat_lit 6444670546750887767425055699393486222485761

noncomputable def ep554 := nat_lit 1199346875357626723976797563873856061440000

noncomputable def ep555 := nat_lit 20338086538332918813076748609045407769759391817579

noncomputable def ep556 := nat_lit 2644286439059657271416440017917228473139593216000000

noncomputable def ep557 := nat_lit 104305931222234437001832400052142994129

noncomputable def ep558 := nat_lit 11993468753576267239767975638738560614400

noncomputable def ep559 := nat_lit 204569023091049124707545369274924048669330004899

noncomputable def ep560 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 1 4)) (Complex.re (zetaApproximant qz12 1 4))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 1 4)) (Complex.im (zetaApproximant qz12 1 4))) ep553 ep554 ep555 ep556 ep557 ep558 ep559

noncomputable def ep561 := nat_lit 661071609764914317854110004479307118284898304000000

noncomputable def ep562 := nat_lit 77419053822242705011822330218328326130306643832497478368372144776835793722697318400

noncomputable def ep563 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz12 1 4)) (Complex.re (zetaApproximant qz12 1 4)) 2538635567928348349569 1095146965186694348800 85279091768549025148507 ep54 2538635567928348349569 1095146965186694348800 85279091768549025148507 ep54 ep553

noncomputable def ep564 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz12 1 4)) (Complex.im (zetaApproximant qz12 1 4)) 10213027524795692873 109514696518669434880 42285438419648151608207 ep177 10213027524795692873 109514696518669434880 42285438419648151608207 ep177 ep557

noncomputable def ep565 := @ep535 15393162788864 5944745249074288001024 5536475450801 15393162788864 1842019825 46179488366592 (@ep536 117575 3221225472 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz191) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow02.d11 EMRow02.d12 rfl) (ep545 rfl)) (ep546 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz12 1 4)) (@ep547 304081 131072 227 131072 (@ep552 65536 (@ep560 ep561 ep562 ep548 ep549 ep550 ep551 (@ep563 ep554 ep555 ep556 ep293 ep293 rfl) (@ep564 ep558 ep559 ep561 ep298 ep298 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz195 := (@Norm.norm Complex Complex.instNorm qz345)

noncomputable abbrev qz349 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep566 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz187 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz195 qz349) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190))) Bool.false 5000280909233 15393162788864 52154875 15393162788864 (BSN.zrb_shape_eq qz195 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) qz38 3)

noncomputable def ep567 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz195 qz349) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) 2383673 458752 1 458752 2097721 33554432 21 33554432

noncomputable def ep568 := @Enclosure.Real.IsNear.mulLit_ff qz195 qz349 2383673 131072 1 131072 2 7 0 1 2383673 458752

noncomputable abbrev qz350 := (Complex.re qz384)

noncomputable abbrev qz351 := (Complex.im qz384)

noncomputable abbrev qz196 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz249 qz350 qz350) (@HMul.hMul Real Real Real qz249 qz351 qz351))

noncomputable abbrev qz197 := qz345

noncomputable def ep569 := @Enclosure.Real.IsNear.of_eq qz195 (Real.sqrt qz196) Bool.false 2383673 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz197)

noncomputable def ep570 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz196) Bool.false 2383673 131072 1 131072 2383673

noncomputable def ep571 := @Enclosure.Real.IsNear.sqrt_image qz196 82682429 250000 0 1 1191836 1191837 65536

noncomputable abbrev qz198 := (@HMul.hMul Real Real Real qz249 qz350 qz350)

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz249 qz351 qz351)

noncomputable def ep572 := @Enclosure.Real.IsNear.addLit_ff qz198 qz199 49 4 0 1 79619929 250000 0 1

noncomputable abbrev qz200 := qz350

noncomputable def ep573 := @Enclosure.Real.IsNear.mulLit_ff qz200 qz200 7 2 0 1 7 2 0 1 49 4

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_eq qz197 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz38) Bool.false 7 2 0 1 Bool.false 17846 1000 0 1 (BSN.s_add_nat_mk qz38 Bool.false 17846 1000 3 qz39)

noncomputable abbrev qz201 := (ep574 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz259 Bool.false 7 2 0 1 Bool.false 17846 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz304))

noncomputable def ep575 := @ep573 0 1 (@Enclosure.Complex.IsNear.re_isNear qz197 Bool.false 7 2 0 1 Bool.false 17846 1000 0 1 qz201)

noncomputable def ep576 := ep575 (@Enclosure.Complex.IsNear.re_isNear qz197 Bool.false 7 2 0 1 Bool.false 17846 1000 0 1 qz201)

noncomputable abbrev qz202 := qz351

noncomputable def ep577 := @Enclosure.Real.IsNear.mulLit_ff qz202 qz202 17846 1000 0 1 17846 1000 0 1 79619929 250000

noncomputable def ep578 := @ep577 0 1 (@Enclosure.Complex.IsNear.im_isNear qz197 Bool.false 7 2 0 1 Bool.false 17846 1000 0 1 qz201)

noncomputable def ep579 := ep578 (@Enclosure.Complex.IsNear.im_isNear qz197 Bool.false 7 2 0 1 Bool.false 17846 1000 0 1 qz201)

noncomputable def ep580 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) (Real.sqrt (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190))))) Bool.false 2097721 33554432

noncomputable def ep581 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190))))) Bool.false 2097721 33554432

noncomputable def ep582 := nat_lit 247722289657750207744633565981739564327351115389

noncomputable def ep583 := nat_lit 63382530011411470074835160268800000000000000000000

noncomputable def ep584 := nat_lit 33545449235592557325963195053555681245372902111337307

noncomputable def ep585 := nat_lit 452770654098940725551792745824415173836800000000000000000000

noncomputable def ep586 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)))) ep582 ep583 ep584 ep585

noncomputable def ep587 := nat_lit 9907338404085880765376372742840564991534168449

noncomputable def ep588 := nat_lit 126765060022822940149670320537600000000000000000000

noncomputable def ep589 := nat_lit 787146082751923562980448663568890892029944329304423

noncomputable def ep590 := nat_lit 100615700910875716789287276849870038630400000000000000000000

noncomputable def ep591 := nat_lit 485537240911414534723890759220638563663168062329

noncomputable def ep592 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190))) ep587 ep588 ep589 ep590 ep591

noncomputable def ep593 := nat_lit 60006583726417802585102352134991344462476305258934807

noncomputable def ep594 := nat_lit 905541308197881451103585491648830347673600000000000000000000

noncomputable def ep595 := nat_lit 62805061834911671080718133386832297935860205484731726053549279270025028226252800000000000000000000

noncomputable def ep596 := nat_lit 11258999068426240000000000

noncomputable def ep597 := nat_lit 317199780754772459520000000000

noncomputable def ep598 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) 99535613747471717518143 ep596 140346918353876071158649 ep597 99535613747471717518143 ep596 140346918353876071158649

noncomputable def ep599 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190) Bool.true 99535613747471717518143 ep596 140346918353876071158649 ep597 Bool.false 696805023598003729779573 ep596 509449810778081326542637

noncomputable def ep600 := nat_lit 951599342264317378560000000000

noncomputable def ep601 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190 Bool.true 99535613747471717518143 ep596 140346918353876071158649 ep597 Bool.false 696805023598003729779573 ep596 509449810778081326542637 ep600

noncomputable def ep602 := nat_lit 1268799123019089838080000000

noncomputable abbrev qz203 := (Complex.re qz346)

noncomputable abbrev qz204 := (Complex.im qz346)

noncomputable def ep603 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz203) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz204) 646122130135920839709 45035996273704960000000 146944962706075446407 ep602 261066146281451927445393 ep596 103610677677357209556899

noncomputable def ep604 := nat_lit 4482685529832072459587414619862629089280000000

noncomputable def ep605 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz203 238547287 120000000 0 1 8125711320321 1125899906842624 615999303761 10573326025159081984 646122130135920839709

noncomputable def ep606 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) 238547287 120000000 0 1 0 1 0 1 238547287

noncomputable def ep607 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 715641861 500000 0 1 238547287 120000000 0

noncomputable def ep608 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz47) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow02.d13 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz47 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz48)

noncomputable abbrev qz352 := (@HAdd.hAdd Complex Complex Complex qz367 qz370 qz378)

noncomputable abbrev qz205 := qz352

noncomputable def ep609 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz5 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) qz205) Bool.true 715641861 500000 0 1 Bool.true 697621813967 125000000 0 1

noncomputable abbrev qz206 := (Complex.re qz352)

noncomputable abbrev qz207 := (Complex.im qz352)

noncomputable def ep610 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz206) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz207) 79432429 100000 0 1 79619929 125000 0 1

noncomputable def ep611 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz206 79432429 250000 0 1 5 2 0 1 79432429 100000

noncomputable abbrev qz353 := (@HAdd.hAdd Complex Complex Complex qz367 qz370 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz208 := qz353

noncomputable def ep612 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz5 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz208) Bool.true 79432429 250000 0 1 Bool.false 8923 250 0 1

noncomputable abbrev qz209 := (Complex.re qz353)

noncomputable abbrev qz210 := (Complex.im qz353)

noncomputable def ep613 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz209) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz210) 3 4 0 1 79619929 250000 0 1

noncomputable def ep614 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz209 1 2 0 1 3 2 0 1 3 4

noncomputable def ep615 := @ep614 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 17846 1000 0 1 ep259)

noncomputable def ep616 := @Enclosure.Complex.IsNear.of_eq qz208 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz38) Bool.false 3 2 0 1 Bool.false 17846 1000 0 1 (BSN.s_add_nat_mk qz38 Bool.false 17846 1000 1 qz39)

noncomputable abbrev qz211 := (ep616 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz259 Bool.false 3 2 0 1 Bool.false 17846 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz304))

noncomputable def ep617 := ep615 (@Enclosure.Complex.IsNear.re_isNear qz208 Bool.false 3 2 0 1 Bool.false 17846 1000 0 1 qz211)

noncomputable def ep618 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz210 17846 1000 0 1 17846 1000 0 1 79619929 250000

noncomputable def ep619 := @ep618 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 17846 1000 0 1 ep259)

noncomputable def ep620 := ep619 (@Enclosure.Complex.IsNear.im_isNear qz208 Bool.false 3 2 0 1 Bool.false 17846 1000 0 1 qz211)

noncomputable def ep621 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz208 Bool.true 79432429 250000 0 1 Bool.false 8923 250 0 1 (@ep613 317729716 79432429 250000 0 1 (ep617 rfl) (ep620 rfl) rfl rfl)

noncomputable def ep622 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz210) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz209) 8923 1000 0 1 26769 1000 0 1

noncomputable def ep623 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz210 1 2 0 1 17846 1000 0 1 8923 1000

noncomputable def ep624 := @ep623 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 17846 1000 0 1 ep259)

noncomputable def ep625 := ep624 (@Enclosure.Complex.IsNear.im_isNear qz208 Bool.false 3 2 0 1 Bool.false 17846 1000 0 1 qz211)

noncomputable def ep626 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz209 17846 1000 0 1 3 2 0 1 26769 1000

noncomputable def ep627 := @ep626 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 17846 1000 0 1 ep259)

noncomputable def ep628 := ep627 (@Enclosure.Complex.IsNear.re_isNear qz208 Bool.false 3 2 0 1 Bool.false 17846 1000 0 1 qz211)

noncomputable abbrev qz212 := (ep612 (BSN.ascPochhammer_succ_eval_c 1 2 qz260 rfl) (ep621 (@ep622 35692000 8923 250 0 1 (ep625 rfl) (ep628 rfl) rfl rfl)))

noncomputable def ep629 := @ep611 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 79432429 250000 0 1 Bool.false 8923 250 0 1 qz212)

noncomputable def ep630 := @Enclosure.Complex.IsNear.of_eq qz205 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz38) Bool.false 5 2 0 1 Bool.false 17846 1000 0 1 (BSN.s_add_nat_mk qz38 Bool.false 17846 1000 2 qz39)

noncomputable abbrev qz213 := (ep630 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz259 Bool.false 5 2 0 1 Bool.false 17846 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz304))

noncomputable def ep631 := ep629 (@Enclosure.Complex.IsNear.re_isNear qz205 Bool.false 5 2 0 1 Bool.false 17846 1000 0 1 qz213)

noncomputable def ep632 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz207 8923 250 0 1 17846 1000 0 1 79619929 125000

noncomputable def ep633 := @ep632 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 79432429 250000 0 1 Bool.false 8923 250 0 1 qz212)

noncomputable def ep634 := ep633 (@Enclosure.Complex.IsNear.im_isNear qz205 Bool.false 5 2 0 1 Bool.false 17846 1000 0 1 qz213)

noncomputable def ep635 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) qz205 Bool.true 715641861 500000 0 1 Bool.true 697621813967 125000000 0 1 (@ep610 17891046525000 715641861 500000 0 1 (ep631 rfl) (ep634 rfl) rfl rfl)

noncomputable def ep636 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz207) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz206) 708775563967 125000000 0 1 8923 100 0 1

noncomputable def ep637 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz207 79432429 250000 0 1 17846 1000 0 1 708775563967 125000000

noncomputable def ep638 := @ep637 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 79432429 250000 0 1 Bool.false 8923 250 0 1 qz212)

noncomputable def ep639 := ep638 (@Enclosure.Complex.IsNear.im_isNear qz205 Bool.false 5 2 0 1 Bool.false 17846 1000 0 1 qz213)

noncomputable def ep640 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz206 8923 250 0 1 5 2 0 1 8923 100

noncomputable def ep641 := @ep640 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 79432429 250000 0 1 Bool.false 8923 250 0 1 qz212)

noncomputable def ep642 := ep641 (@Enclosure.Complex.IsNear.re_isNear qz205 Bool.false 5 2 0 1 Bool.false 17846 1000 0 1 qz213)

noncomputable abbrev qz214 := (ep609 (BSN.ascPochhammer_succ_eval_c 2 3 qz260 rfl) (ep635 (@ep636 69762181396700 697621813967 125000000 0 1 (ep639 rfl) (ep642 rfl) rfl rfl)))

noncomputable def ep643 := @ep607 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep608) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 715641861 500000 0 1 Bool.true 697621813967 125000000 0 1 qz214)

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 697621813967 125000000 0 1 0 1 0

noncomputable def ep645 := @ep644 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep608) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 715641861 500000 0 1 Bool.true 697621813967 125000000 0 1 qz214)

noncomputable def ep646 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) 697621813967 90000000000 0 1 0 1 0 1 697621813967

noncomputable def ep647 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 697621813967 125000000 0 1 697621813967 90000000000 0

noncomputable def ep648 := @ep647 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep608) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 715641861 500000 0 1 Bool.true 697621813967 125000000 0 1 qz214)

noncomputable def ep649 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 715641861 500000 0 1 0 1 0

noncomputable def ep650 := @ep649 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep608) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 715641861 500000 0 1 Bool.true 697621813967 125000000 0 1 qz214)

noncomputable def ep651 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 238547287 120000000 0 1 Bool.false 697621813967 90000000000 0 1 (@ep606 238547287 120000000 0 1 (ep643 rfl) (ep645 rfl) rfl rfl) (@ep646 697621813967 90000000000 0 1 (ep648 rfl) (ep650 rfl) rfl rfl)

noncomputable def ep652 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 238547287 120000000 0 1 Bool.false 697621813967 90000000000 0 1 ep651

noncomputable def ep653 := @Enclosure.Complex.IsNear.re_isNear qz190 Bool.false 8125711320321 1125899906842624 615999303761 10573326025159081984 Bool.false 3368007234711 1125899906842624 445559509191 10573326025159081984

noncomputable abbrev qz215 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 16384)))

noncomputable def ep654 := @Enclosure.Complex.IsNear.of_eq qz190 (Complex.mk (@HMul.hMul Real Real Real qz0 qz215 qz101) (@HMul.hMul Real Real Real qz0 qz215 qz102)) Bool.false 8125711320321 1125899906842624 615999303761 10573326025159081984 Bool.false 3368007234711 1125899906842624 445559509191

noncomputable abbrev qz216 := (@Nat.cast Real Real.instNatCast 16384)

noncomputable def ep655 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz216) 4294967297 33554432 1 33554432 131071 131072 16777216 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz216) (Real.sqrt (@HDiv.hDiv Real Real Real qz3 qz216 qz301)) Bool.false 4294967297 33554432 1 33554432 (BSN.sqrt_natCast_div_one 16384) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz3 qz216 qz301)) Bool.false 4294967297 33554432 1 33554432 4294967297 33554432 1 33554432 (BSN.sqrt_enclosure 16384 1 2147483648 2147483649 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep656 := nat_lit 147443727375074537121690809726715087890625

noncomputable def ep657 := nat_lit 22889945643899497138335355216896171420000

noncomputable def ep658 := nat_lit 355592320898650075318906513310625

noncomputable def ep659 := BSN.log_dyadic_bound 3 5 17 16 ep656 16777216 4808192 ep657 ep658 23258159 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 ep657 ep656 ep658 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep660 := nat_lit 5695797276624766046830592

noncomputable def ep661 := nat_lit 4835703278458516698824704

noncomputable def ep662 := nat_lit 2896519087431887317798030605112799685750122784187097809641919111148347085970719877723930625

noncomputable def ep663 := nat_lit 180468656028383376705345110207518346455653528001341539704795567934989718275908111313435361280

noncomputable def ep664 := nat_lit 1842458796941152946084652216951738092110987054184011845436077650724289233543431812890625

noncomputable def ep665 := nat_lit 7583138390936085870415466909801315410529760931926101101312415451096879233069005552056090625

noncomputable def ep666 := nat_lit 3308592027187028572931327020471169685020314680024594894587918745474811501724982040746314956800

noncomputable def ep667 := BSN.sin_dyadic_bound_f 80942147585 68719476736 3 2 33554432 9625776 ep662 ep663 ep664 ep665 ep666 ep664 30997247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 80942147585) (BSN.sinEvenQ 68719476736) 0 2 ep662 ep663 ep664 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 80942147585) (BSN.sinOddQ 68719476736) 0 2 ep665 ep666 ep664 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz217 := (@HDiv.hDiv Real Real Real qz252 (@Nat.cast Real Real.instNatCast 830130211) (@Nat.cast Real Real.instNatCast 33554432))

noncomputable def ep668 := @Enclosure.Real.IsNear.cos_image qz105 qz217 Bool.false 830130211 33554432 125 33554432 Bool.false 30997247 33554432 1 4808192 (@Enclosure.Real.IsNear.recentre' qz105 Bool.false 207532552757 8388608000 8923 2404096000 830130211 33554432 125 33554432 (@Enclosure.Real.IsNear.mulLit_ff qz38 qz107 17846 1000 0 1 23258159 16777216 1 4808192 207532552757 8388608000 8923 2404096000 qz88 (BSN.isNear_log_sfrac 4 1 23258159 16777216 1 4808192 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 23258159 16777216 4808192 rfl rfl rfl (ep659 rfl))) rfl) rfl) (Enclosure.sfrac_false_div 830130211 33554432) (BSN.cos_reduce3 qz217 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast ep660) (@Nat.cast Real Real.instNatCast ep661)) 226375608064910080 72057594037927936 Bool.false 30997247 33554432 3 1000000000000000 9616384 4808192 (BSN.sin_reduce_arg_pos_rat_q3 830130211 33554432 226375608064910080 72057594037927936 3 ep660 ep661 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 30997247 33554432 ep660 ep661 80942147585 68719476736 9625776 9616384 (ep667 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep669 := nat_lit 1609996141371911244530499070492422820124339763239136121732371096260514731865308123985690625

noncomputable def ep670 := nat_lit 20052072892042597411705012245279816272850392000149059967199507548332190919545345701492817920

noncomputable def ep671 := nat_lit 4826303506521851427699327907043364984188797315609040341506241133480095617128837508331290625

noncomputable def ep672 := nat_lit 902343280141916883526725551037591732278267640006707698523977839674948591379540556567176806400

noncomputable def ep673 := BSN.cos_dyadic_bound_f 80942147585 68719476736 3 2 33554432 9625776 ep669 ep670 ep664 ep671 ep672 ep664 12847977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 80942147585) (BSN.cosEvenQ 68719476736) 0 2 ep669 ep670 ep664 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 80942147585) (BSN.cosOddQ 68719476736) 0 2 ep671 ep672 ep664 rfl rfl rfl rfl) rfl rfl

noncomputable def ep674 := @Enclosure.Real.IsNear.sin_image qz105 qz217 Bool.false 830130211 33554432 125 33554432 Bool.true 12847977 33554432 1 4808192 (@Enclosure.Real.IsNear.recentre' qz105 Bool.false 207532552757 8388608000 8923 2404096000 830130211 33554432 125 33554432 (@Enclosure.Real.IsNear.mulLit_ff qz38 qz107 17846 1000 0 1 23258159 16777216 1 4808192 207532552757 8388608000 8923 2404096000 qz88 (BSN.isNear_log_sfrac 4 1 23258159 16777216 1 4808192 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 23258159 16777216 4808192 rfl rfl rfl (ep659 rfl))) rfl) rfl) (Enclosure.sfrac_false_div 830130211 33554432) (BSN.sin_reduce3 qz217 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast ep660) (@Nat.cast Real Real.instNatCast ep661)) 226375608064910080 72057594037927936 Bool.false 12847977 33554432 3 1000000000000000 9616384 4808192 (BSN.sin_reduce_arg_pos_rat_q3 830130211 33554432 226375608064910080 72057594037927936 3 ep660 ep661 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 12847977 33554432 ep660 ep661 80942147585 68719476736 9625776 9616384 (ep673 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep675 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz215 qz101) (@HMul.hMul Real Real Real qz0 qz215 qz102) Bool.false 8125711320321 1125899906842624 615999303761 10573326025159081984 Bool.false 3368007234711 1125899906842624 445559509191 10573326025159081984 (@Enclosure.Real.IsNear.mulLit_ff qz215 qz101 262143 33554432 1 33554432 30997247 33554432 1239411 315109670912 8125711320321 1125899906842624 615999303761 10573326025159081984 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 262143 33554432 1 33554432 262143 33554432 1 33554432 (ep655 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz101 Bool.false 30997247 33554432 634578432 161336151506944 30997247 33554432 1239411 315109670912 (ep668 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz215 qz102 262143 33554432 1 33554432 12847977 33554432 1239411 315109670912 3368007234711 1125899906842624 445559509191 10573326025159081984 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 262143 33554432 1 33554432 262143 33554432 1 33554432 (ep655 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz109 Bool.true 12847977 33554432 1239411 315109670912 (@Enclosure.Real.IsNear.recentre' qz109 Bool.true 12847977 33554432 634578432 161336151506944 12847977 33554432 1239411 315109670912 (ep674 rfl rfl) rfl)) rfl)

noncomputable def ep676 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz204 697621813967 90000000000 0 1 3368007234711 1125899906842624 445559509191 10573326025159081984 261066146281451927445393

noncomputable def ep677 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 238547287 120000000 0 1 Bool.false 697621813967 90000000000 0 1 ep651

noncomputable def ep678 := @Enclosure.Complex.IsNear.im_isNear qz190 Bool.false 8125711320321 1125899906842624 615999303761 10573326025159081984 Bool.false 3368007234711 1125899906842624 445559509191 10573326025159081984

noncomputable def ep679 := nat_lit 422933041006363279360000000

noncomputable def ep680 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz204) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz203) 267809662812227093019 45035996273704960000000 35429004038188204939 ep679 629852607894946956524823 ep596 429734551692157865429887

noncomputable def ep681 := nat_lit 31381308446258592694028597448876836782080000000

noncomputable def ep682 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz204 238547287 120000000 0 1 3368007234711 1125899906842624 445559509191 10573326025159081984 267809662812227093019

noncomputable def ep683 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz203 697621813967 90000000000 0 1 8125711320321 1125899906842624 615999303761 10573326025159081984 629852607894946956524823

noncomputable abbrev qz218 := (@ep654 10573326025159081984 (BSN.cpow_neg_s_sub_mk qz259 17846 1000 4 3 16384 qz276 rfl EMRow02.d14) ep675)

noncomputable def ep684 := ep601 (@ep603 ep597 ep604 99535613747471717518143 ep596 140346918353876071158649 ep597 (@ep605 45035996273704960000000 146944962706075446407 ep602 ep652 (ep653 qz218) rfl) (@ep676 ep596 103610677677357209556899 ep597 ep677 (ep678 qz218) rfl) rfl rfl) (@ep680 ep600 ep681 696805023598003729779573 ep596 509449810778081326542637 ep600 (@ep682 45035996273704960000000 35429004038188204939 ep679 ep652 (ep678 qz218) rfl) (@ep683 ep596 429734551692157865429887 ep600 ep677 (ep653 qz218) rfl) rfl rfl)

noncomputable def ep685 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) 696805023598003729779573 ep596 509449810778081326542637 ep600 696805023598003729779573 ep596 509449810778081326542637

noncomputable def ep686 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190) Bool.true 99535613747471717518143 ep596 140346918353876071158649 ep597 Bool.false 696805023598003729779573 ep596 509449810778081326542637

noncomputable def ep687 := @ep567 5000280909233 15393162788864 52154875 15393162788864 (@ep568 1 458752 (ep569 (@ep570 131072 1 131072 (ep571 (@ep572 330729716 82682429 250000 0 1 (ep576 rfl) (ep579 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep580 21 33554432 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)) (@ep581 21 33554432 2097721 33554432 21 33554432 (@ep586 1048850 1048871 16777216 (@ep592 ep588 ep593 ep594 ep595 ep582 ep583 ep584 ep585 (@ep598 ep597 ep587 ep588 ep589 ep590 (@ep599 ep600 ep684) (@ep599 ep600 ep684) rfl) (@ep685 ep600 ep591 ep588 ep593 ep594 (@ep686 ep600 ep684) (@ep686 ep600 ep684) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow02.d15 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 1 4))) (@HMul.hMul Real Real Real qz0 qz187 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)))) Bool.false 5536475450801 15393162788864 1842019825 46179488366592 := ep565 (ep566 ep687) rfl rfl

theorem EMRow02.d16 : @Eq Nat (Nat.pow 5 (Nat.succ (Nat.mul 2 3))) 78125 := @Eq.refl Nat 78125

noncomputable abbrev qz385 := (@HAdd.hAdd Complex Complex Complex qz387 qz394 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz354 := qz385

noncomputable abbrev qz219 := (@HDiv.hDiv Real Real Real qz252 (@Norm.norm Complex Complex.instNorm qz354) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz320) qz308))

noncomputable abbrev qz355 := (@HPow.hPow Complex Complex Complex qz375 (@Nat.cast Complex Complex.instNatCast 5) (@HSub.hSub Complex Complex Complex qz365 qz383 qz377))

noncomputable abbrev qz220 := qz355

noncomputable def ep688 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz119 1 5))) (@HMul.hMul Real Real Real qz0 qz219 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220))) 23297553 1073741824 1468381 28991029248 6421796372613 15393162788864 51233115

noncomputable def ep689 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz119 1 5)) 123 8192 1 221184 189411 131072 385 131072 23297553 1073741824

noncomputable def ep690 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz119 1 5)) (Real.sqrt (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz119 1 5)) (Complex.re (zetaApproximant qz119 1 5))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz119 1 5)) (Complex.im (zetaApproximant qz119 1 5))))) Bool.false 189411 131072 385 131072

noncomputable def ep691 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz119 1 5)) (Complex.re (zetaApproximant qz119 1 5))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz119 1 5)) (Complex.im (zetaApproximant qz119 1 5))))) Bool.false 189411 131072 385 131072

noncomputable def ep692 := nat_lit 203721016913135324739767662882801

noncomputable def ep693 := nat_lit 97552993974852126448707174400000

noncomputable def ep694 := nat_lit 25424222295876064257871568283261772549040180139

noncomputable def ep695 := nat_lit 3003529510874755621027616074516705337933824000000

noncomputable def ep696 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz119 1 5)) (Complex.re (zetaApproximant qz119 1 5))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz119 1 5)) (Complex.im (zetaApproximant qz119 1 5)))) ep692 ep693 ep694 ep695 94513 94898

noncomputable def ep697 := nat_lit 104674798167041689072503107235468192529

noncomputable def ep698 := nat_lit 50380390149615100748328394031104000000

noncomputable def ep699 := nat_lit 29647143680181211131674540992080991643074929

noncomputable def ep700 := nat_lit 3754411888593444526284520093145881672417280000

noncomputable def ep701 := nat_lit 2140553835396237821033717173216637649

noncomputable def ep702 := nat_lit 201521560598460402993313576124416000000

noncomputable def ep703 := nat_lit 1706507351731095352531935489596979234580236939

noncomputable def ep704 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz119 1 5)) (Complex.re (zetaApproximant qz119 1 5))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz119 1 5)) (Complex.im (zetaApproximant qz119 1 5))) ep697 ep698 ep699 ep700 ep701 ep702 ep703

noncomputable def ep705 := nat_lit 21202070619314621104913767514966979639890885152725426507957320349122560000000

noncomputable def ep706 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz119 1 5)) (Complex.re (zetaApproximant qz119 1 5)) 10231070235661647977 7097914492977152000 592835964170235124917 216633673761532411904000 10231070235661647977 7097914492977152000 592835964170235124917 216633673761532411904000 ep697

noncomputable def ep707 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz119 1 5)) (Complex.im (zetaApproximant qz119 1 5)) 1463063168628148407 14195828985954304000 4714823675498473606389 ep417 1463063168628148407 14195828985954304000 4714823675498473606389 ep417 ep701

noncomputable def ep708 := @ep688 15393162788864 7253974376397253115904 6755790092421 15393162788864 22434004121 415615395299328 (@ep689 1468381 28991029248 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz191) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow02.d11 EMRow02.d12 rfl) (ep545 rfl)) (ep690 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz119 1 5)) (@ep691 189411 131072 385 131072 (@ep696 65536 (@ep704 ep695 ep705 ep692 ep693 ep694 ep695 (@ep706 ep698 ep699 ep700 ep526 ep526 rfl) (@ep707 ep702 ep703 ep695 ep534 ep534 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz221 := (@Norm.norm Complex Complex.instNorm qz354)

noncomputable def ep709 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz219 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz221 qz349) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220))) Bool.false 6421796372613 15393162788864 51233115 15393162788864 (BSN.zrb_shape_eq qz221 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) qz133 3)

noncomputable def ep710 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz221 qz349) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) 3071391 458752 1 458752 2090843 33554432 1 2097152

noncomputable def ep711 := @Enclosure.Real.IsNear.mulLit_ff qz221 qz349 3071391 131072 1 131072 2 7 0 1 3071391 458752

noncomputable abbrev qz356 := (Complex.re qz385)

noncomputable abbrev qz357 := (Complex.im qz385)

noncomputable abbrev qz222 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz249 qz356 qz356) (@HMul.hMul Real Real Real qz249 qz357 qz357))

noncomputable abbrev qz223 := qz354

noncomputable def ep712 := @Enclosure.Real.IsNear.of_eq qz221 (Real.sqrt qz222) Bool.false 3071391 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz223)

noncomputable def ep713 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz222) Bool.false 3071391 131072 1 131072 3071391

noncomputable def ep714 := @Enclosure.Real.IsNear.sqrt_image qz222 5490989 10000 0 1 1535695 1535696 65536

noncomputable abbrev qz224 := (@HMul.hMul Real Real Real qz249 qz356 qz356)

noncomputable abbrev qz225 := (@HMul.hMul Real Real Real qz249 qz357 qz357)

noncomputable def ep715 := @Enclosure.Real.IsNear.addLit_ff qz224 qz225 49 4 0 1 5368489 10000 0 1

noncomputable abbrev qz226 := qz356

noncomputable def ep716 := @Enclosure.Real.IsNear.mulLit_ff qz226 qz226 7 2 0 1 7 2 0 1 49 4

noncomputable def ep717 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz133) Bool.false 7 2 0 1 Bool.false 23170 1000 0 1 (BSN.s_add_nat_mk qz133 Bool.false 23170 1000 3 qz134)

noncomputable abbrev qz227 := (ep717 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz319 Bool.false 7 2 0 1 Bool.false 23170 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz339))

noncomputable def ep718 := @ep716 0 1 (@Enclosure.Complex.IsNear.re_isNear qz223 Bool.false 7 2 0 1 Bool.false 23170 1000 0 1 qz227)

noncomputable def ep719 := ep718 (@Enclosure.Complex.IsNear.re_isNear qz223 Bool.false 7 2 0 1 Bool.false 23170 1000 0 1 qz227)

noncomputable abbrev qz228 := qz357

noncomputable def ep720 := @Enclosure.Real.IsNear.mulLit_ff qz228 qz228 23170 1000 0 1 23170 1000 0 1 5368489 10000

noncomputable def ep721 := @ep720 0 1 (@Enclosure.Complex.IsNear.im_isNear qz223 Bool.false 7 2 0 1 Bool.false 23170 1000 0 1 qz227)

noncomputable def ep722 := ep721 (@Enclosure.Complex.IsNear.im_isNear qz223 Bool.false 7 2 0 1 Bool.false 23170 1000 0 1 qz227)

noncomputable def ep723 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) (Real.sqrt (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220))))) Bool.false 2090843 33554432

noncomputable def ep724 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220))))) Bool.false 4181686 67108864

noncomputable def ep725 := nat_lit 816502692427666175353858637460731320434106313

noncomputable def ep726 := nat_lit 210288022770660518955485101333413888000000000000

noncomputable def ep727 := nat_lit 10359883770460984380685182146964197336886428521366460071

noncomputable def ep728 := nat_lit 181108261639576290220717098329766069534720000000000000000000000

noncomputable def ep729 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)))) ep725 ep726 ep727 ep728

noncomputable def ep730 := nat_lit 74145215981334411929078277448254658181567401

noncomputable def ep731 := nat_lit 420576045541321037910970202666827776000000000000

noncomputable def ep732 := nat_lit 2868220667622568746427905121992133381687004696089725071

noncomputable def ep733 := nat_lit 362216523279152580441434196659532139069440000000000000000000000

noncomputable def ep734 := nat_lit 6928267417217768616793951099880924367496201

noncomputable def ep735 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220))) ep730 ep731 ep732 ep733 ep734

noncomputable def ep736 := nat_lit 1869226869072537946270978678519234560000000000

noncomputable def ep737 := nat_lit 1983505208144377779438051019104029032453983594071466119

noncomputable def ep738 := nat_lit 40246280364350286715714910739948015452160000000000000000000000

noncomputable def ep739 := nat_lit 3052457542711727764734651253009239304690479488138031562678407914504032828847554560000000000

noncomputable def ep740 := nat_lit 5675109676059035408195861

noncomputable def ep741 := nat_lit 19031986845286347571200000000000

noncomputable def ep742 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) 8610761637702811938701 648518346341351424000000 ep740 ep741 8610761637702811938701 648518346341351424000000 ep740

noncomputable def ep743 := nat_lit 2567779445715800197554037

noncomputable def ep744 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220) Bool.true 8610761637702811938701 648518346341351424000000 ep740 ep741 Bool.false 2632160218759064943101 43234556422756761600000 ep743

noncomputable def ep745 := nat_lit 6343995615095449190400000000000

noncomputable def ep746 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220 Bool.true 8610761637702811938701 648518346341351424000000 ep740 ep741 Bool.false 2632160218759064943101 43234556422756761600000 ep743 ep745

noncomputable def ep747 := nat_lit 42293304100636327936000000000

noncomputable def ep748 := nat_lit 4330617545667945220476011

noncomputable abbrev qz229 := (Complex.re qz355)

noncomputable abbrev qz230 := (Complex.im qz355)

noncomputable def ep749 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)))) qz229) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230) 3172918925991671549 288230376151711744000 2987760289757978194933 ep747 15749829221184072923951 648518346341351424000000 ep748

noncomputable def ep750 := nat_lit 2481883065787810926573267934500349804544000

noncomputable def ep751 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)))) qz229 16092967 4800000 0 1 14787137726025 4503599627370496 556968821801097 26433315062897704960000 3172918925991671549

noncomputable def ep752 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)))) 16092967 4800000 0 1 0 1 0 1 16092967

noncomputable def ep753 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 48278901 20000 0 1 16092967 4800000 0

noncomputable abbrev qz358 := (@HAdd.hAdd Complex Complex Complex qz367 qz382 qz378)

noncomputable abbrev qz231 := qz358

noncomputable def ep754 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz5 (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2)) qz231) Bool.true 48278901 20000 0 1 Bool.true 12305561513 1000000 0 1

noncomputable abbrev qz232 := (Complex.re qz358)

noncomputable abbrev qz233 := (Complex.im qz358)

noncomputable def ep755 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2))) qz233) 5360989 4000 0 1 5368489 5000 0 1

noncomputable def ep756 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2))) qz232 5360989 10000 0 1 5 2 0 1 5360989 4000

noncomputable abbrev qz359 := (@HAdd.hAdd Complex Complex Complex qz367 qz382 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz234 := qz359

noncomputable def ep757 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz5 (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)) qz234) Bool.true 5360989 10000 0 1 Bool.false 2317 50 0 1

noncomputable abbrev qz235 := (Complex.re qz359)

noncomputable abbrev qz236 := (Complex.im qz359)

noncomputable def ep758 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) qz236) 3 4 0 1 5368489 10000 0 1

noncomputable def ep759 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) qz235 1 2 0 1 3 2 0 1 3 4

noncomputable def ep760 := @ep759 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep492)

noncomputable def ep761 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz133) Bool.false 3 2 0 1 Bool.false 23170 1000 0 1 (BSN.s_add_nat_mk qz133 Bool.false 23170 1000 1 qz134)

noncomputable abbrev qz237 := (ep761 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz319 Bool.false 3 2 0 1 Bool.false 23170 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz339))

noncomputable def ep762 := ep760 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 3 2 0 1 Bool.false 23170 1000 0 1 qz237)

noncomputable def ep763 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) qz236 23170 1000 0 1 23170 1000 0 1 5368489 10000

noncomputable def ep764 := @ep763 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep492)

noncomputable def ep765 := ep764 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 3 2 0 1 Bool.false 23170 1000 0 1 qz237)

noncomputable def ep766 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)) qz234 Bool.true 5360989 10000 0 1 Bool.false 2317 50 0 1 (@ep758 21443956 5360989 10000 0 1 (ep762 rfl) (ep765 rfl) rfl rfl)

noncomputable def ep767 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) qz235) 2317 200 0 1 6951 200 0 1

noncomputable def ep768 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) qz236 1 2 0 1 23170 1000 0 1 2317 200

noncomputable def ep769 := @ep768 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep492)

noncomputable def ep770 := ep769 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 3 2 0 1 Bool.false 23170 1000 0 1 qz237)

noncomputable def ep771 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1))) qz235 23170 1000 0 1 3 2 0 1 6951 200

noncomputable def ep772 := @ep771 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 23170 1000 0 1 ep492)

noncomputable def ep773 := ep772 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 3 2 0 1 Bool.false 23170 1000 0 1 qz237)

noncomputable abbrev qz238 := (ep757 (BSN.ascPochhammer_succ_eval_c 1 2 qz320 rfl) (ep766 (@ep767 1853600 2317 50 0 1 (ep770 rfl) (ep773 rfl) rfl rfl)))

noncomputable def ep774 := @ep756 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5360989 10000 0 1 Bool.false 2317 50 0 1 qz238)

noncomputable def ep775 := @Enclosure.Complex.IsNear.of_eq qz231 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz133) Bool.false 5 2 0 1 Bool.false 23170 1000 0 1 (BSN.s_add_nat_mk qz133 Bool.false 23170 1000 2 qz134)

noncomputable abbrev qz239 := (ep775 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz319 Bool.false 5 2 0 1 Bool.false 23170 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz339))

noncomputable def ep776 := ep774 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 5 2 0 1 Bool.false 23170 1000 0 1 qz239)

noncomputable def ep777 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2))) qz233 2317 50 0 1 23170 1000 0 1 5368489 5000

noncomputable def ep778 := @ep777 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5360989 10000 0 1 Bool.false 2317 50 0 1 qz238)

noncomputable def ep779 := ep778 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 5 2 0 1 Bool.false 23170 1000 0 1 qz239)

noncomputable def ep780 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2)) qz231 Bool.true 48278901 20000 0 1 Bool.true 12305561513 1000000 0 1 (@ep755 48278901000 48278901 20000 0 1 (ep776 rfl) (ep779 rfl) rfl rfl)

noncomputable def ep781 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2))) qz232) 12421411513 1000000 0 1 2317 20 0 1

noncomputable def ep782 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2))) qz233 5360989 10000 0 1 23170 1000 0 1 12421411513 1000000

noncomputable def ep783 := @ep782 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5360989 10000 0 1 Bool.false 2317 50 0 1 qz238)

noncomputable def ep784 := ep783 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 5 2 0 1 Bool.false 23170 1000 0 1 qz239)

noncomputable def ep785 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2))) qz232 2317 50 0 1 5 2 0 1 2317 20

noncomputable def ep786 := @ep785 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5360989 10000 0 1 Bool.false 2317 50 0 1 qz238)

noncomputable def ep787 := ep786 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 5 2 0 1 Bool.false 23170 1000 0 1 qz239)

noncomputable abbrev qz240 := (ep754 (BSN.ascPochhammer_succ_eval_c 2 3 qz320 rfl) (ep780 (@ep781 246111230260 12305561513 1000000 0 1 (ep784 rfl) (ep787 rfl) rfl rfl)))

noncomputable def ep788 := @ep753 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep608) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 48278901 20000 0 1 Bool.true 12305561513 1000000 0 1 qz240)

noncomputable def ep789 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 12305561513 1000000 0 1 0 1 0

noncomputable def ep790 := @ep789 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep608) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 48278901 20000 0 1 Bool.true 12305561513 1000000 0 1 qz240)

noncomputable def ep791 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)))) 12305561513 720000000 0 1 0 1 0 1 12305561513

noncomputable def ep792 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 12305561513 1000000 0 1 12305561513 720000000 0

noncomputable def ep793 := @ep792 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep608) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 48278901 20000 0 1 Bool.true 12305561513 1000000 0 1 qz240)

noncomputable def ep794 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 48278901 20000 0 1 0 1 0

noncomputable def ep795 := @ep794 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep608) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 48278901 20000 0 1 Bool.true 12305561513 1000000 0 1 qz240)

noncomputable def ep796 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 16092967 4800000 0 1 Bool.false 12305561513 720000000 0 1 (@ep752 16092967 4800000 0 1 (ep788 rfl) (ep790 rfl) rfl rfl) (@ep791 12305561513 720000000 0 1 (ep793 rfl) (ep795 rfl) rfl rfl)

noncomputable def ep797 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 16092967 4800000 0 1 Bool.false 12305561513 720000000 0 1 ep796

noncomputable def ep798 := @Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 14787137726025 4503599627370496 556968821801097 26433315062897704960000 Bool.false 6399476043635 4503599627370496 351923603087347 26433315062897704960000

noncomputable abbrev qz360 := (@Nat.cast Real Real.instNatCast 78125)

noncomputable abbrev qz241 := (@Inv.inv Real Real.instInv (Real.sqrt qz360))

noncomputable def ep799 := @Enclosure.Complex.IsNear.of_eq qz220 (Complex.mk (@HMul.hMul Real Real Real qz0 qz241 qz176) (@HMul.hMul Real Real Real qz0 qz241 qz177)) Bool.false 14787137726025 4503599627370496 556968821801097 26433315062897704960000 Bool.false 6399476043635 4503599627370496 351923603087347

noncomputable def ep800 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz360) 18757497725 67108864 1 67108864 120047 120048 33554432 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz360) (Real.sqrt (@HDiv.hDiv Real Real Real qz3 qz360 qz301)) Bool.false 18757497725 67108864 1 67108864 (BSN.sqrt_natCast_div_one 78125) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz3 qz360 qz301)) Bool.false 18757497725 67108864 1 67108864 18757497725 67108864 1 67108864 (BSN.sqrt_enclosure 78125 1 9378748862 9378748863 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep801 := nat_lit 24987371385403367883999025651388344673404853859375

noncomputable def ep802 := nat_lit 5174345737036840691400486158476888201456094182500

noncomputable def ep803 := nat_lit 9919565729522841605829928920966758400000

noncomputable def ep804 := nat_lit 1753791174206542693625850900

noncomputable def ep805 := nat_lit 2517933232285674949199829375

noncomputable def ep806 := BSN.log_dyadic_bound 2 3 23 22 ep801 33554432 11738750 ep802 ep803 54003774 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 22 11 2054957030503884950940 9923762498944768499025 57668788341964800 ep804 ep805 172009262110757879808000 ep802 ep801 ep803 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 0 11 2054957030503884950940 9923762498944768499025 57668788341964800 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 11 22 ep804 ep805 172009262110757879808000 rfl rfl rfl rfl)) rfl rfl

noncomputable def ep807 := nat_lit 11241658331852586251976704

noncomputable def ep808 := nat_lit 9671406556917033397649408

noncomputable def ep809 := nat_lit 703210828668724568794617206719393346479641008435514138296316724746086960232381605997320937985

noncomputable def ep810 := nat_lit 46199975943266144436568348213124696692647303168343434164427665391357367878632476496239452487680

noncomputable def ep811 := nat_lit 424233195869482767492424655440778944344486248900804980267325626041726782706639749227553281

noncomputable def ep812 := nat_lit 1841055792767632803314723996727697503441549663404316677950872894749969719150902979922805465601

noncomputable def ep813 := nat_lit 846999558959879314670419717240619439365200558086296293014507198841551744441595402431056628940800

noncomputable def ep814 := BSN.sin_dyadic_bound_f 159753573311 137438953472 3 2 67108864 23500428 ep809 ep810 ep811 ep812 ep813 ep811 61588695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 159753573311) (BSN.sinEvenQ 137438953472) 0 2 ep809 ep810 ep811 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 159753573311) (BSN.sinOddQ 137438953472) 0 2 ep812 ep813 ep811 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz242 := (@HDiv.hDiv Real Real Real qz252 (@Nat.cast Real Real.instNatCast 2502534887) (@Nat.cast Real Real.instNatCast 67108864))

noncomputable def ep815 := @Enclosure.Real.IsNear.cos_image qz178 qz242 Bool.false 2502534887 67108864 133 67108864 Bool.false 61588695 67108864 1 11738750 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 62563372179 1677721600 2317 1173875000 2502534887 67108864 133 67108864 (@Enclosure.Real.IsNear.mulLit_ff qz133 qz180 23170 1000 0 1 54003774 33554432 1 11738750 62563372179 1677721600 2317 1173875000 qz166 (BSN.isNear_log_sfrac 5 1 54003774 33554432 1 11738750 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 54003774 33554432 11738750 rfl rfl rfl (ep806 rfl rfl))) rfl) rfl) (Enclosure.sfrac_false_div 2502534887 67108864) (BSN.cos_reduce3 qz242 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast ep807) (@Nat.cast Real Real.instNatCast ep808)) 226375608064910080 72057594037927936 Bool.false 61588695 67108864 5 1000000000000000 23477500 11738750 (BSN.sin_reduce_arg_pos_rat_q3 2502534887 67108864 226375608064910080 72057594037927936 5 ep807 ep808 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 61588695 67108864 ep807 ep808 159753573311 137438953472 23500428 23477500 (ep814 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep816 := nat_lit 1656831971598980811749951610671140358810580326409100877610604334443405954966951740848241359607303579611530614659095538243611141722684593222401

noncomputable def ep817 := nat_lit 21759806992472160846509436431027924547665573599712653161483140986990306751823661669370177199848368120331884066839754328502985489716814125465600

noncomputable def ep818 := nat_lit 276316597848078055460700180971917035505259502169107523923016241721339707833818058786110550606801393523865935758562264494870986214552321

noncomputable def ep819 := nat_lit 10044172798333166868460657837529480483613409053561573381748744579169407234896762931247199827592414109649187202490501961700762062940190237209345

noncomputable def ep820 := nat_lit 1980142436314966637032358715223541133837567197573851437694965829816117914415953211912686125186201498950201450082417643893771679564230085417369600

noncomputable def ep821 := BSN.cos_dyadic_bound_f 159753573311 137438953472 4 3 67108864 23500428 ep816 ep817 ep818 ep819 ep820 ep818 26653933 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 159753573311) (BSN.cosEvenQ 137438953472) 0 3 ep816 ep817 ep818 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 159753573311) (BSN.cosOddQ 137438953472) 0 3 ep819 ep820 ep818 rfl rfl rfl rfl) rfl rfl

noncomputable def ep822 := @Enclosure.Real.IsNear.sin_image qz178 qz242 Bool.false 2502534887 67108864 133 67108864 Bool.true 26653933 67108864 1 11738750 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 62563372179 1677721600 2317 1173875000 2502534887 67108864 133 67108864 (@Enclosure.Real.IsNear.mulLit_ff qz133 qz180 23170 1000 0 1 54003774 33554432 1 11738750 62563372179 1677721600 2317 1173875000 qz166 (BSN.isNear_log_sfrac 5 1 54003774 33554432 1 11738750 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 54003774 33554432 11738750 rfl rfl rfl (ep806 rfl rfl))) rfl) rfl) (Enclosure.sfrac_false_div 2502534887 67108864) (BSN.sin_reduce3 qz242 (@HDiv.hDiv Real Real Real qz3 (@Nat.cast Real Real.instNatCast ep807) (@Nat.cast Real Real.instNatCast ep808)) 226375608064910080 72057594037927936 Bool.false 26653933 67108864 5 1000000000000000 23477500 11738750 (BSN.sin_reduce_arg_pos_rat_q3 2502534887 67108864 226375608064910080 72057594037927936 5 ep807 ep808 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 26653933 67108864 ep807 ep808 159753573311 137438953472 23500428 23477500 (ep821 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep823 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz241 qz176) (@HMul.hMul Real Real Real qz0 qz241 qz177) Bool.false 14787137726025 4503599627370496 556968821801097 26433315062897704960000 Bool.false 6399476043635 4503599627370496 351923603087347 26433315062897704960000 (@Enclosure.Real.IsNear.mulLit_ff qz241 qz176 240095 67108864 1 67108864 61588695 67108864 814181307 393887088640000 14787137726025 4503599627370496 556968821801097 26433315062897704960000 (@Enclosure.Real.IsNear.recentre' qz241 Bool.false 240095 67108864 1 67108864 240095 67108864 1 67108864 (ep800 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 61588695 67108864 1628362614 787774177280000 61588695 67108864 814181307 393887088640000 (ep815 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz241 qz177 240095 67108864 1 67108864 26653933 67108864 814181307 393887088640000 6399476043635 4503599627370496 351923603087347 26433315062897704960000 (@Enclosure.Real.IsNear.recentre' qz241 Bool.false 240095 67108864 1 67108864 240095 67108864 1 67108864 (ep800 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz181 Bool.true 26653933 67108864 814181307 393887088640000 (@Enclosure.Real.IsNear.recentre' qz181 Bool.true 26653933 67108864 1628362614 787774177280000 26653933 67108864 814181307 393887088640000 (ep822 rfl rfl) rfl)) rfl)

noncomputable def ep824 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230 12305561513 720000000 0 1 6399476043635 4503599627370496 351923603087347 26433315062897704960000 15749829221184072923951

noncomputable def ep825 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 16092967 4800000 0 1 Bool.false 12305561513 720000000 0 1 ep796

noncomputable def ep826 := @Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 14787137726025 4503599627370496 556968821801097 26433315062897704960000 Bool.false 6399476043635 4503599627370496 351923603087347 26433315062897704960000

noncomputable def ep827 := nat_lit 126879912301908983808000000000

noncomputable def ep828 := nat_lit 2284604699165511528126587

noncomputable def ep829 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)))) qz229) 20597311357501723009 4323455642275676160000 5663494931005773388549 ep827 2426187105184047713011 43234556422756761600000 ep828

noncomputable def ep830 := nat_lit 11380027949167457388506686414546702172160000

noncomputable def ep831 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230 16092967 4800000 0 1 6399476043635 4503599627370496 351923603087347 26433315062897704960000 20597311357501723009

noncomputable def ep832 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3)))) qz229 12305561513 720000000 0 1 14787137726025 4503599627370496 556968821801097 26433315062897704960000 2426187105184047713011

noncomputable abbrev qz243 := (@ep799 26433315062897704960000 (BSN.cpow_neg_s_sub_mk qz319 23170 1000 5 3 78125 qz326 rfl EMRow02.d16) ep823)

noncomputable def ep833 := ep746 (@ep749 ep741 ep750 8610761637702811938701 648518346341351424000000 ep740 ep741 (@ep751 288230376151711744000 2987760289757978194933 ep747 ep797 (ep798 qz243) rfl) (@ep824 648518346341351424000000 ep748 ep741 ep825 (ep826 qz243) rfl) rfl rfl) (@ep829 ep745 ep830 2632160218759064943101 43234556422756761600000 ep743 ep745 (@ep831 4323455642275676160000 5663494931005773388549 ep827 ep797 (ep826 qz243) rfl) (@ep832 43234556422756761600000 ep828 ep745 ep825 (ep798 qz243) rfl) rfl rfl)

noncomputable def ep834 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) (Complex.im (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) 2632160218759064943101 43234556422756761600000 ep743 ep745 2632160218759064943101 43234556422756761600000 ep743

noncomputable def ep835 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220) Bool.true 8610761637702811938701 648518346341351424000000 ep740 ep741 Bool.false 2632160218759064943101 43234556422756761600000 ep743

noncomputable def ep836 := @ep710 6421796372613 15393162788864 51233115 15393162788864 (@ep711 1 458752 (ep712 (@ep713 131072 1 131072 (ep714 (@ep715 21963956 5490989 10000 0 1 (ep719 rfl) (ep722 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep723 1 2097152 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)) (@ep724 32 67108864 2090843 33554432 1 2097152 (@ep729 2090827 2090859 33554432 (@ep735 ep736 ep737 ep738 ep739 ep725 ep726 ep727 ep728 (@ep742 ep741 ep730 ep731 ep732 ep733 (@ep744 ep745 ep833) (@ep744 ep745 ep833) rfl) (@ep834 ep745 ep734 ep736 ep737 ep738 (@ep835 ep745 ep833) (@ep835 ep745 ep833) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow02.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz119 1 5))) (@HMul.hMul Real Real Real qz0 qz219 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)))) Bool.false 6755790092421 15393162788864 22434004121 415615395299328 := ep708 (ep709 ep836) rfl rfl

noncomputable def EMRow02.d18 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz361 := (EMRow02.d3 qz369 qz381 (@Enclosure.dec_le_dec qz369 qz381 17846 1000 23170 1000 (@Eq.refl Real qz369) (@Eq.refl Real qz381) rfl rfl rfl) 4 5 1 1)

noncomputable abbrev qz244 := qz361

noncomputable def ep837 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz244 (@Enclosure.dec_nonneg qz38 17846 1000 qz39) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 4 rfl)

noncomputable abbrev qz245 := (Zeta.Certificates.ZIntervalEM.fstVal qz361)

noncomputable def ep838 := @Enclosure.Real.IsNear.pos_val qz245 ep38 ep39

noncomputable def ep839 := @Enclosure.Real.IsNear.of_eq qz245 (hardyZApproximantEM 1 4 qz38) Bool.false

noncomputable abbrev qz246 := (Zeta.Certificates.ZIntervalEM.sndVal qz361)

noncomputable def ep840 := BSN.mul_neg_of_pos_neg_r qz245 qz246 (@ep838 ep40 ep41 (@ep839 ep38 ep39 ep40 ep41 (@Eq.refl Real (hardyZApproximantEM 1 4 qz38)) EMRow02.d8) rfl rfl rfl)

noncomputable def ep841 := @Enclosure.Real.IsNear.neg_val qz246 ep299 ep300

noncomputable def ep842 := @Enclosure.Real.IsNear.of_eq qz246 (hardyZApproximantEM 1 5 qz133) Bool.true

noncomputable def ep843 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz245) (BSN.hardyZErrorBoundStrong 1 4 qz38)

noncomputable def ep844 := @Enclosure.norm_gt_of_isNear qz245 (BSN.hardyZErrorBoundStrong 1 4 qz38) Bool.false

noncomputable def ep845 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 4 qz38) (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 1 4))) (@HMul.hMul Real Real Real qz0 qz187 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)))) Bool.false 5536475450801 15393162788864 1842019825 46179488366592 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 1 4))) (@HMul.hMul Real Real Real qz0 qz187 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz190)))))

noncomputable def ep846 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz246) (BSN.hardyZErrorBoundStrong 1 5 qz133)

noncomputable def ep847 := @Enclosure.norm_gt_of_isNear qz246 (BSN.hardyZErrorBoundStrong 1 5 qz133) Bool.true

noncomputable def ep848 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 5 qz133) (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz119 1 5))) (@HMul.hMul Real Real Real qz0 qz219 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)))) Bool.false 6755790092421 15393162788864 22434004121 415615395299328 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz59 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz119 1 5))) (@HMul.hMul Real Real Real qz0 qz219 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz5 (@HMul.hMul Complex Complex Complex qz5 (@HDiv.hDiv Complex Complex Complex qz16 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz188)) ↑qz189) (@Polynomial.eval Complex Complex.instSemiring qz119 (@ascPochhammer Complex Complex.instSemiring 3))) qz220)))))

noncomputable def ep849 := @List.cons EMRow02.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz244 (ep837 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 5 rfl) (ep840 (@ep841 ep301 ep302 (@ep842 ep299 ep300 ep301 ep302 (@Eq.refl Real (hardyZApproximantEM 1 5 qz133)) EMRow02.d10) rfl rfl rfl)) (ep843 (hardyZErrorBoundEM 1 4 qz38) (BSN.hardyZErrorBoundEM_le_strong 1 4 qz38 rfl) (@ep844 Bool.false ep38 ep39 ep40 ep41 5536475450801 15393162788864 1842019825 46179488366592 (@ep839 ep38 ep39 ep40 ep41 (@Eq.refl Real (hardyZApproximantEM 1 4 qz38)) EMRow02.d8) (ep845 EMRow02.d15) rfl rfl rfl rfl rfl)) (ep846 (hardyZErrorBoundEM 1 5 qz133) (BSN.hardyZErrorBoundEM_le_strong 1 5 qz133 rfl) (@ep847 Bool.false ep299 ep300 ep301 ep302 6755790092421 15393162788864 22434004121 415615395299328 (@ep842 ep299 ep300 ep301 ep302 (@Eq.refl Real (hardyZApproximantEM 1 5 qz133)) EMRow02.d10) (ep848 EMRow02.d17) rfl rfl rfl rfl rfl)))) (@List.nil EMRow02.d0)

noncomputable abbrev qz362 := (@Enclosure.dec_le_dec qz369 qz381 17846 1000 23170 1000 (@Eq.refl Real qz369) (@Eq.refl Real qz381) rfl rfl rfl)

noncomputable abbrev qz247 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep849 (@List.IsChain.singleton EMRow02.d1 EMRow02.d18 (EMRow02.d2 qz259 qz319 qz362))))

noncomputable abbrev qz363 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep850 := And (@Eq (Option Real) (@Option.map qz363 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz363 qz247)) (@Option.some Real qz38))

noncomputable def ep851 := ep850 (@Eq (Option Real) (@Option.map qz363 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz363 qz247)) (@Option.some Real qz133))

noncomputable def ep852 := @And.intro (@Eq Nat (@List.length qz363 qz247) 1) ep851

noncomputable def ep853 := @And.intro (@Eq (Option Real) (@Option.map qz363 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz363 qz247)) (@Option.some Real qz38))

noncomputable def ep854 := @ep853 (@Eq (Option Real) (@Option.map qz363 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz363 qz247)) (@Option.some Real qz133))

noncomputable abbrev qz248 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep849 (@List.IsChain.singleton EMRow02.d1 EMRow02.d18 (EMRow02.d2 qz259 qz319 qz362)))

theorem EMRow02.d19 : Zeta.Certificates.BatchSpec 1 17846 1000 23170 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz363 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz363 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz363 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz38)) (@Eq (Option Real) (@Option.map qz363 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz363 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz133)))) qz248 (ep852 (@Eq.refl Nat 1) (ep854 (@Eq.refl (Option Real) (@Option.some Real qz38)) (@Eq.refl (Option Real) (@Option.some Real qz133))))

theorem solution : Zeta.Certificates.BatchSpec 1 17846 1000 23170 1000 := EMRow02.d19
#print axioms solution
#check solution
