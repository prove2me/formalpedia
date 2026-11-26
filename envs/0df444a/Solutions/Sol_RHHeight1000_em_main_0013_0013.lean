-- Prove2me | solution 1 for RHHeight1000.em_main_0013_0013
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T22:03:51.684242+00:00
-- url     : https://prove2.me/submissions/809d35df-9db4-4922-8926-9d8cf35a3e5f

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow13.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow13.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow13.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow13.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow13.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz263 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz263

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz264 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz264 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138525251149047 2251799813685248 400000000057 28500000000000000 4138525251149047 2251799813685248 400000000057 28500000000000000 240893 131072

noncomputable abbrev qz265 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 131072 qz265 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 779317518150410741488063439345657628452599855445271348474342368876423347582876053728679783827237610085654588674605917415063316248867402488514697634436426745

noncomputable def ep10 := nat_lit 13198325246229587668616048586507268161410801335203869857947191811663857046415771104290097871102374067703089877156867761119753226876438075596795543285583799

noncomputable def ep11 := nat_lit 13338205139369261376383149914767634013226508915861991492218067381232119098362059104733250767410551174650894954010182016771344050520336484956804919489535

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 4 3 ep9 262144 71250 ep10 ep11 118379 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 3 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz266 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz266

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138525251149047 2251799813685248 400000000057 28500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 17358233014995452428288 9444732965739290427392 1000000000142500 71250000000000000000 4138525251149047 2251799813685248 400000000057 28500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 118379 262144 24973259072661432 36028797018963968 71250 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 779317518150412560342812906055656980396982394702499187106382620393032652998517540933158707129341055012778793601285942846917973645097155238594697634436426745

noncomputable def ep18 := nat_lit 13198325246229655554962711811363413523213721429909419700721697472804734044169853548961061453892255410264786862895235075217650796661500958924795543285583799

noncomputable def ep19 := nat_lit 13338205139369401582665284895604560799810298653799657073142644093199656832454717421805370366589019475922075211274104314270069372987910244956804919489535

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 4 3 ep17 262144 71250 ep18 ep19 118379 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 3 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138525251149047 2251799813685248 400000000057 28500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 17358233014995452428288 9444732965739290427392 1000000000142500 71250000000000000000 4138525251149047 2251799813685248 400000000057 28500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 118379 262144 24973259072661432 36028797018963968 71250 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz267 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz3 := (Real.log qz267)

theorem EMRow13.d4 : Enclosure.Real.IsNear qz3 Bool.false 240893 131072 3 131072 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz264) Bool.false 240893 131072 3 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz264) Bool.false 240893 131072 3 131072 240893 131072 3 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 300084 262144 1 71250 300084 262144 1 71250 150042 131072 2 131072 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 5456220599384213465248909714772227496572670538165976141063262914812807742611017753801422503639530882087556452122005170047444298375835020188444492540969863625638808382453421118235702266947370928498132967594635949979551089348001357731941995137847266570621617494261809398531128871567535833923098076891483476912075228072418610430965163137427706923427310178652894498746239459018086669257415154730407592571637957767157504839263249849478535520334507104454135585522664276476675

noncomputable def ep28 := nat_lit 583201912334273870627228188254822588827079241605343036411752047433839590517388190714780374919746279700129906501257101384229175562492847525225536391462542197025353003914524118772974087630067522636400444148635637549655768907025719966434833632093412247469427754039812435067522613541620617101084764807513402584784781490076808276521160080078978009740617112077674385114356333461540984478969922738031393369686631450339262287925718320742111081121726382582016608811398564907105

noncomputable def ep29 := nat_lit 2006268627360805445673839316848610509641534779303135707206598861506426804997221642604762844037348942607248852390277353874343091902420975230792155995982437872051629609224882022549487822374001366578458875613104959699164386313425243185530298109514065278868815165519648262204211929774735225023360668387821809970420335957473972782118680523137645713941929429588852958886338507735711181009301082096313539911189247153419366938656533848809858580689548163599238034961919825

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 10 9 ep27 262144 71250 ep28 ep29 300084 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 9 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 5456220599384260892400251500854699790811159195150212163211869656216336849990273498858157048596616978904240776489460003685239051624059887013466241201881443704542959173524008982544253046253151867013374679201187657749749224297051088632484873343955402287279851789208893474071824987110190207053471018354491495133306616646837230249901879422821128116650397962087630806812522581253210958036113071268120219429850657911869289056672761916619783759890108169949892385522664276476675

noncomputable def ep34 := nat_lit 583201912334279575053067226115417021307550325332234501953544426829928714668898700518418107620762577859683234776628347658361181262145210140271013263714562720079188253110303208819702903278206870150494721073991877864419341163488949363940583288588224434829960190109694548513088121652843287215458036179968684293644459891198769761601084092249455692877745995219003758983943549453190712470220270279351626860119698313725888367584660500821040083453648022042061408811398564907105

noncomputable def ep35 := nat_lit 2006268627360839170887858856494478835319319717359667041823756329478526322484078784125879825811686186445537802910004300367040714583746383402724632880452479311196631191501299191497899488881639138562974769996989848045902383299749709271247360054208480548633525642122514778503225872819822968825602771791453574137145372948950799520945900351638147820910599315255916738483881817718250085827996954508077874524152655659774549924038927632065100609588052048399238034961919825

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 10 9 ep33 262144 71250 ep34 ep35 300084 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 9 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 150042 131072 2 131072 75021 65536 1 65536 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 300084 262144 1 71250 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 300084 262144 71250 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 300084 262144 1 71250 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 300084 262144 71250 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow13.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 65536 := ep37

noncomputable abbrev qz485 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 57545 1000)))

noncomputable abbrev qz463 := qz485

noncomputable abbrev qz268 := qz463

noncomputable abbrev qz4 := (BSN.headSumC qz268 9)

noncomputable abbrev qz486 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz464 := qz486

noncomputable abbrev qz269 := qz464

noncomputable abbrev qz5 := qz269

noncomputable abbrev qz6 := qz268

noncomputable abbrev qz465 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz270 := qz465

noncomputable abbrev qz466 := (@Neg.neg Complex Complex.instNeg qz485)

noncomputable abbrev qz271 := qz466

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 8) qz271)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz4 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 8) qz7) Bool.false 75050675517 68719476736 4555188274101 816043786240000 Bool.false 10086898337 68719476736 4555055844101 816043786240000

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 8) qz7 Bool.false 51707230905 68719476736 12220029127807 2448131358720000 Bool.false 16823118779 68719476736 12232398769057 2448131358720000 Bool.false

noncomputable abbrev qz8 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 7) qz271)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 7) qz8) Bool.false 51707230905 68719476736 12220029127807 2448131358720000 Bool.false 16823118779 68719476736 12232398769057 2448131358720000

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 7) qz8 Bool.false 40399512699 68719476736 3563275410333 816043786240000 Bool.true 3279849989 34359738368 1782975702979 408021893120000 Bool.false

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 6) qz271)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 6) qz9) Bool.false 40399512699 68719476736 3563275410333 816043786240000 Bool.true 3279849989 34359738368 1782975702979 408021893120000

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 6) qz9 Bool.false 64081754459 68719476736 3009812325277 816043786240000 Bool.false 4240231371 34359738368 1507203090451 408021893120000 Bool.true

noncomputable abbrev qz10 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 5) qz271)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 5) qz10) Bool.false 64081754459 68719476736 3009812325277 816043786240000 Bool.false 4240231371 34359738368 1507203090451 408021893120000

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 5) qz10 Bool.false 8248191703 8589934592 1805774858743 612032839680000 Bool.true 11096451329 34359738368 3614069295611 1224065679360000 Bool.true

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 4) qz271)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 4) qz11) Bool.false 8248191703 8589934592 1805774858743 612032839680000 Bool.true 11096451329 34359738368 3614069295611 1224065679360000

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 4) qz11 Bool.false 19332366633 17179869184 650726733013 306016419840000 Bool.true 27312817591 34359738368 2602560550177 1224065679360000 Bool.true

noncomputable abbrev qz467 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz272 := qz467

noncomputable abbrev qz12 := (@HPow.hPow Complex Complex Complex qz270 qz272 qz271)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 3) qz12) Bool.false 19332366633 17179869184 650726733013 306016419840000 Bool.true 27312817591 34359738368 2602560550177 1224065679360000

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 3) qz12 Bool.false 2537392189 4294967296 1432979436727 1224065679360000 Bool.true 1238370543 2147483648 1435190894227 1224065679360000 Bool.false

noncomputable abbrev qz468 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz273 := qz468

noncomputable abbrev qz13 := (@HPow.hPow Complex Complex Complex qz270 qz273 qz271)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 2) qz13) Bool.false 2537392189 4294967296 1432979436727 1224065679360000 Bool.true 1238370543 2147483648 1435190894227 1224065679360000

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 2) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz274 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz14 := qz274

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz6)

noncomputable abbrev qz275 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz15 := (@Inv.inv Real Real.instInv (Real.sqrt qz275))

noncomputable abbrev qz487 := (Enclosure.sfrac Bool.false 57545 1000)

noncomputable abbrev qz469 := qz487

noncomputable abbrev qz276 := qz469

noncomputable abbrev qz16 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz17 := qz276

noncomputable abbrev qz277 := (@Eq.refl Real qz469)

noncomputable abbrev qz18 := qz277

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz13 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)))) Bool.true 1757575107 4294967296 1432979436727 1224065679360000 Bool.true 1238370543 2147483648 1435190894227 1224065679360000 (BSN.cpow_neg_s_mk qz17 57545 1000 2 qz18 rfl)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz275) 370727 262144 1 262144 92681 92683 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz275) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz275 qz19)) Bool.false 370727 262144 1 262144 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz275 qz19)) Bool.false 370727 262144 1 262144 370727 262144 1 262144 (BSN.sqrt_enclosure 2 1 185363 185364 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 131072 35625 24381081 945 90852 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 12052437497006881671176740203042576

noncomputable def ep57 := nat_lit 9969209968386869046778552952102584320

noncomputable def ep58 := nat_lit 69784469778708083327449870664718090240

noncomputable abbrev qz278 := (BSN.sinEvenQ 536870912)

noncomputable abbrev qz279 := (BSN.sinOddQ 536870912)

noncomputable def ep59 := BSN.sin_dyadic_bound_f 331336074 536870912 2 1 262144 71320 ep56 ep57 ep56 ep56 ep58 ep56 151708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 331336074) qz278 0 1 ep56 ep57 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 331336074) qz279 0 1 ep56 ep58 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz20 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz21 := (Enclosure.Real.IsNear.const Bool.false 57545 1000)

noncomputable abbrev qz280 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2614039) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz281 := (BSN.isNear_log_sfrac 2 1 90852 131072 1 35625 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 90852 131072 35625 rfl rfl rfl (ep55 rfl)))

noncomputable abbrev qz282 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep60 := @Enclosure.Real.IsNear.cos_image qz16 qz280 Bool.false 2614039 65536 425 262144 Bool.true 151708 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 261403917 6553600 11509 7125000 2614039 65536 425 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz20 57545 1000 0 1 90852 131072 1 35625 261403917 6553600 11509 7125000 qz21 qz281 rfl) rfl) (Enclosure.sfrac_false_div 2614039 65536) (BSN.cos_reduce1 qz280 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5828925869073532715008) qz282) 226375608064910080 72057594037927936 Bool.false 151708 262144 6 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q1 2614039 65536 226375608064910080 72057594037927936 6 5828925869073532715008 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 151708 262144 5828925869073532715008 9444732965739290427392 331336074 536870912 71320 71250 (ep59 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep61 := nat_lit 1993841993677373809355710590420516864

noncomputable def ep62 := nat_lit 29907629905160607140335658856307752960

noncomputable abbrev qz283 := (BSN.cosEvenQ 536870912)

noncomputable abbrev qz284 := (BSN.cosOddQ 536870912)

noncomputable def ep63 := BSN.cos_dyadic_bound_f 331336074 536870912 2 1 262144 71320 ep56 ep61 ep56 ep56 ep62 ep56 213784 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 331336074) qz283 0 1 ep56 ep61 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 331336074) qz284 0 1 ep56 ep62 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable def ep64 := @Enclosure.Real.IsNear.sin_image qz16 qz280 Bool.false 2614039 65536 425 262144 Bool.false 213784 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 261403917 6553600 11509 7125000 2614039 65536 425 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz20 57545 1000 0 1 90852 131072 1 35625 261403917 6553600 11509 7125000 qz21 qz281 rfl) rfl) (Enclosure.sfrac_false_div 2614039 65536) (BSN.sin_reduce1 qz280 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5828925869073532715008) qz282) 226375608064910080 72057594037927936 Bool.false 213784 262144 6 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q1 2614039 65536 226375608064910080 72057594037927936 6 5828925869073532715008 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 213784 262144 5828925869073532715008 9444732965739290427392 331336074 536870912 71320 71250 (ep63 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz285 := (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 185364 262144 2 262144 46341 65536 1 131072 (ep54 rfl rfl) rfl)

noncomputable def ep65 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16))) Bool.true 1757575107 4294967296 1432979436727 1224065679360000 Bool.true 1238370543 2147483648 1435190894227 1224065679360000 (@Enclosure.Real.IsNear.mulLit_ft qz15 (Real.cos qz16) 46341 65536 1 131072 37927 65536 15402769 9338880000 1757575107 4294967296 1432979436727 1224065679360000 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz16) Bool.true 151708 262144 15402769 9338880000 37927 65536 15402769 9338880000 (ep60 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)) 46341 65536 1 131072 26723 32768 15402769 9338880000 1238370543 2147483648 1435190894227 1224065679360000 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz16) Bool.false 26723 32768 15402769 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz16) Bool.false 213784 262144 15402769 9338880000 26723 32768 15402769 9338880000 (ep64 rfl rfl) rfl)) rfl)

noncomputable abbrev qz286 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz22 := qz286

noncomputable def ep66 := @ep51 1757575107 4294967296 1432979436727 1224065679360000 Bool.true 1238370543 2147483648 1435190894227 1224065679360000 Bool.false 2537392189 2537392189 4294967296 1432979436727 1224065679360000 Bool.true 1238370543 1238370543 2147483648 1435190894227 1224065679360000 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep53 ep65) rfl rfl

noncomputable abbrev qz23 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz24 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep67 := @Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk (@HMul.hMul Real Real Real qz0 qz23 (Real.cos qz24)) (@HMul.hMul Real Real Real qz0 qz23 (@Neg.neg Real Real.instNeg (Real.sin qz24)))) Bool.false 9182797877 17179869184 15599033271 16320875724800 Bool.true 7498888903 34359738368 7782464373 8160437862400 (BSN.cpow_neg_s_mk qz17 57545 1000 3 qz18 rfl)

noncomputable abbrev qz25 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep68 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz25) 454047 262144 1 262144 75674 75675 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz25) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz25 qz19)) Bool.false 454047 262144 1 262144 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz25 qz19)) Bool.false 454047 262144 1 262144 454047 262144 1 262144 (BSN.sqrt_enclosure 3 1 227023 227024 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep69 := BSN.log_dyadic_bound 1 2 9 8 2258332876800 131072 35625 222698787165 2027025 143997 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1) (BSN.artanhQ 2) 0 8 222698787165 2258332876800 2027025 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep70 := nat_lit 1876068427562249951829522780810000

noncomputable def ep71 := BSN.cos_dyadic_bound_f 208119210 536870912 2 1 262144 71320 ep70 ep61 ep70 ep70 ep62 ep70 242692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 208119210) qz283 0 1 ep70 ep61 ep70 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 208119210) qz284 0 1 ep70 ep62 ep70 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz26 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz27 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz28 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable abbrev qz287 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8286307) qz26)

noncomputable abbrev qz288 := (BSN.isNear_log_sfrac 3 1 143997 131072 1 35625 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 143997 131072 35625 rfl rfl rfl (ep69 rfl)))

noncomputable def ep72 := @Enclosure.Real.IsNear.cos_image qz24 qz287 Bool.false 8286307 131072 425 262144 Bool.false 242692 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 1657261473 26214400 11509 7125000 8286307 131072 425 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz27 57545 1000 0 1 143997 131072 1 35625 1657261473 26214400 11509 7125000 qz21 qz288 rfl) rfl) (Enclosure.sfrac_false_div 8286307 131072) (BSN.cos_reduce0 qz287 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7322543747925282914304) qz28) 226375608064910080 72057594037927936 Bool.false 242692 262144 10 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 8286307 131072 226375608064910080 72057594037927936 10 7322543747925282914304 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 242692 262144 7322543747925282914304 18889465931478580854784 208119210 536870912 71320 71250 (ep71 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep73 := BSN.sin_dyadic_bound_f 208119210 536870912 2 1 262144 71320 ep70 ep57 ep70 ep70 ep58 ep70 99094 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 208119210) qz278 0 1 ep70 ep57 ep70 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 208119210) qz279 0 1 ep70 ep58 ep70 rfl rfl rfl rfl) rfl rfl

noncomputable def ep74 := @Enclosure.Real.IsNear.sin_image qz24 qz287 Bool.false 8286307 131072 425 262144 Bool.false 99094 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 1657261473 26214400 11509 7125000 8286307 131072 425 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz27 57545 1000 0 1 143997 131072 1 35625 1657261473 26214400 11509 7125000 qz21 qz288 rfl) rfl) (Enclosure.sfrac_false_div 8286307 131072) (BSN.sin_reduce0 qz287 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7322543747925282914304) qz28) 226375608064910080 72057594037927936 Bool.false 99094 262144 10 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 8286307 131072 226375608064910080 72057594037927936 10 7322543747925282914304 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 99094 262144 7322543747925282914304 18889465931478580854784 208119210 536870912 71320 71250 (ep73 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz289 := (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 151349 262144 1 262144 151349 262144 1 262144 (ep68 rfl rfl) rfl)

noncomputable def ep75 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz23 (Real.cos qz24)) (@HMul.hMul Real Real Real qz0 qz23 (@Neg.neg Real Real.instNeg (Real.sin qz24))) Bool.false 9182797877 17179869184 15599033271 16320875724800 Bool.true 7498888903 34359738368 7782464373 8160437862400 (@Enclosure.Real.IsNear.mulLit_ff qz23 (Real.cos qz24) 151349 262144 1 262144 60673 65536 15402769 9338880000 9182797877 17179869184 15599033271 16320875724800 qz289 (@Enclosure.Real.IsNear.recentre' (Real.cos qz24) Bool.false 242692 262144 15402769 9338880000 60673 65536 15402769 9338880000 (ep72 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz23 (@Neg.neg Real Real.instNeg (Real.sin qz24)) 151349 262144 1 262144 49547 131072 15402769 9338880000 7498888903 34359738368 7782464373 8160437862400 qz289 (@Enclosure.Real.IsNear.neg (Real.sin qz24) Bool.false 49547 131072 15402769 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz24) Bool.false 99094 262144 15402769 9338880000 49547 131072 15402769 9338880000 (ep74 rfl rfl) rfl)) rfl)

noncomputable def ep76 := @ep49 9182797877 17179869184 15599033271 16320875724800 Bool.true 7498888903 34359738368 7782464373 8160437862400 Bool.false 83031882443016634368 19332366633 17179869184 650726733013 306016419840000 Bool.true 58653829157479251968 27312817591 34359738368 2602560550177 1224065679360000 (ep50 (BSN.head_sum_c_succ qz6 2 3 rfl rfl) (ep66 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep67 ep75) rfl rfl

noncomputable abbrev qz290 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz29 := (@Inv.inv Real Real.instInv (Real.sqrt qz290))

noncomputable abbrev qz30 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep77 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz29 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz29 (@Neg.neg Real Real.instNeg (Real.sin qz30)))) Bool.true 2835983227 17179869184 504321392717 612032839680000 Bool.false 8108183131 17179869184 505754372717 612032839680000 (BSN.cpow_neg_s_mk qz17 57545 1000 4 qz18 rfl)

noncomputable def ep78 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz290) 524289 262144 1 262144 65535 65536 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz290) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz290 qz19)) Bool.false 524289 262144 1 262144 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz290 qz19)) Bool.false 524289 262144 1 262144 524289 262144 1 262144 (BSN.sqrt_enclosure 4 1 262144 262145 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep79 := nat_lit 753960950911045074462890625

noncomputable def ep80 := nat_lit 117048680082474133384580175

noncomputable def ep81 := BSN.log_dyadic_bound 3 5 12 11 ep79 131072 35625 ep80 431467934736729065175 181704 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 3) (BSN.artanhQ 5) 0 11 ep80 ep79 431467934736729065175 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep82 := nat_lit 26951855409318088276316338823541383747755363904544239445993877944512774241

noncomputable def ep83 := nat_lit 278278412702595531909369356367009666242828713757909985904152976703587614720

noncomputable def ep84 := nat_lit 37187799775100449360200067829469371462140143737792115138434872351883361

noncomputable def ep85 := nat_lit 80781190628404063930228616334965212500341811426157134107704764088834556001

noncomputable def ep86 := nat_lit 12522528571616798935921621036515434980927292119105949365686883951661442662400

noncomputable def ep87 := BSN.cos_dyadic_bound_f 662674197 536870912 3 2 262144 71320 ep82 ep83 ep84 ep85 ep86 ep84 86548 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 662674197) qz283 0 2 ep82 ep83 ep84 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 662674197) qz284 0 2 ep85 ep86 ep84 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz31 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz32 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz33 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz291 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20912313) qz31)

noncomputable abbrev qz292 := (BSN.isNear_log_sfrac 4 1 181704 131072 1 35625 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 181704 131072 35625 rfl rfl rfl (ep81 rfl)))

noncomputable def ep88 := @Enclosure.Real.IsNear.cos_image qz30 qz291 Bool.false 20912313 262144 53 32768 Bool.true 86548 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 261403917 3276800 11509 7125000 20912313 262144 53 32768 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz32 57545 1000 0 1 181704 131072 1 35625 261403917 3276800 11509 7125000 qz21 qz292 rfl) rfl) (Enclosure.sfrac_false_div 20912313 262144) (BSN.cos_reduce2 qz291 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46631551067776337575936) qz33) 226375608064910080 72057594037927936 Bool.false 86548 262144 12 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q2 20912313 262144 226375608064910080 72057594037927936 12 46631551067776337575936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 86548 262144 46631551067776337575936 37778931862957161709568 662674197 536870912 71320 71250 (ep87 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep89 := nat_lit 48483589496952478537881249828110915248789942913189397310678232402241486945

noncomputable def ep90 := nat_lit 2504505714323359787184324207303086996185458423821189873137376790332288532480

noncomputable def ep91 := nat_lit 126920620816192043062153425630471351431130195016111043817742666498253226081

noncomputable def ep92 := nat_lit 45915938095928262765045943800556594930066737770055147674185241156091956428800

noncomputable def ep93 := BSN.sin_dyadic_bound_f 662674197 536870912 3 2 262144 71320 ep89 ep90 ep84 ep91 ep92 ep84 247444 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 662674197) qz278 0 2 ep89 ep90 ep84 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 662674197) qz279 0 2 ep91 ep92 ep84 rfl rfl rfl rfl) rfl rfl

noncomputable def ep94 := @Enclosure.Real.IsNear.sin_image qz30 qz291 Bool.false 20912313 262144 53 32768 Bool.true 247444 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 261403917 3276800 11509 7125000 20912313 262144 53 32768 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz32 57545 1000 0 1 181704 131072 1 35625 261403917 3276800 11509 7125000 qz21 qz292 rfl) rfl) (Enclosure.sfrac_false_div 20912313 262144) (BSN.sin_reduce2 qz291 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46631551067776337575936) qz33) 226375608064910080 72057594037927936 Bool.false 247444 262144 12 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q2 20912313 262144 226375608064910080 72057594037927936 12 46631551067776337575936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 247444 262144 46631551067776337575936 37778931862957161709568 662674197 536870912 71320 71250 (ep93 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz293 := (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 131071 262144 1 262144 131071 262144 1 262144 (ep78 rfl rfl) rfl)

noncomputable def ep95 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz29 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz29 (@Neg.neg Real Real.instNeg (Real.sin qz30))) Bool.true 2835983227 17179869184 504321392717 612032839680000 Bool.false 8108183131 17179869184 505754372717 612032839680000 (@Enclosure.Real.IsNear.mulLit_ft qz29 (Real.cos qz30) 131071 262144 1 262144 21637 65536 1920893 1167360000 2835983227 17179869184 504321392717 612032839680000 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz30) Bool.true 86548 262144 1920893 1167360000 21637 65536 1920893 1167360000 (ep88 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz29 (@Neg.neg Real Real.instNeg (Real.sin qz30)) 131071 262144 1 262144 61861 65536 1920893 1167360000 8108183131 17179869184 505754372717 612032839680000 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz30) Bool.true 61861 65536 1920893 1167360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz30) Bool.true 247444 262144 1920893 1167360000 61861 65536 1920893 1167360000 (ep94 rfl rfl) rfl)) rfl)

noncomputable def ep96 := @ep47 2835983227 17179869184 504321392717 612032839680000 Bool.false 8108183131 17179869184 505754372717 612032839680000 Bool.false 283405708924188360704 8248191703 8589934592 1805774858743 612032839680000 Bool.true 190635582238842945536 11096451329 34359738368 3614069295611 1224065679360000 (ep48 (BSN.head_sum_c_succ qz6 3 4 rfl rfl) (ep76 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep77 ep95) rfl rfl

noncomputable abbrev qz294 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz294))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep97 := @Enclosure.Complex.IsNear.of_eq qz10 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.true 1903779165 68719476736 1806337540859 2448131358720000 Bool.false 3834170675 8589934592 453769987871 612032839680000 (BSN.cpow_neg_s_mk qz17 57545 1000 5 qz18 rfl)

noncomputable def ep98 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz294) 586171 262144 1 262144 58617 58618 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz294) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz294 qz19)) Bool.false 586171 262144 1 262144 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz294 qz19)) Bool.false 586171 262144 1 262144 586171 262144 1 262144 (BSN.sqrt_enclosure 5 1 293085 293086 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep99 := nat_lit 141613827518379161815574079375

noncomputable def ep100 := nat_lit 29325128709309236875766211300

noncomputable def ep101 := BSN.log_dyadic_bound 2 3 15 14 ep99 131072 35625 ep100 57299708096576225280000 210952 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP 2) (BSN.artanhQ 3) 0 14 ep100 ep99 57299708096576225280000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep102 := nat_lit 60275495759661125375847710745026022215811333525934681629841231597973187201

noncomputable def ep103 := nat_lit 185365426373013983528533378765993182349271735844975564512244849587169921

noncomputable def ep104 := nat_lit 180455756426237348160486065477546080282735457106114093760499205094745221761

noncomputable def ep105 := BSN.cos_dyadic_bound_f 810034641 536870912 3 2 262144 71320 ep102 ep83 ep103 ep104 ep86 ep103 16239 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 810034641) qz283 0 2 ep102 ep83 ep103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 810034641) qz284 0 2 ep104 ep86 ep103 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz36 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz295 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24278465) qz31)

noncomputable abbrev qz296 := (BSN.isNear_log_sfrac 5 1 210952 131072 1 35625 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 210952 131072 35625 rfl rfl rfl (ep101 rfl)))

noncomputable def ep106 := @Enclosure.Real.IsNear.cos_image qz35 qz295 Bool.false 24278465 262144 425 262144 Bool.true 16239 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 303480821 3276800 11509 7125000 24278465 262144 425 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz36 57545 1000 0 1 210952 131072 1 35625 303480821 3276800 11509 7125000 qz21 qz296 rfl) rfl) (Enclosure.sfrac_false_div 24278465 262144) (BSN.cos_reduce2 qz295 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 57001120435152428728320) qz33) 226375608064910080 72057594037927936 Bool.false 16239 262144 14 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q2 24278465 262144 226375608064910080 72057594037927936 14 57001120435152428728320 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16239 262144 57001120435152428728320 37778931862957161709568 810034641 536870912 71320 71250 (ep105 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep107 := nat_lit 108347600026291614489703052638034045442580982958006446482104420996682001025

noncomputable def ep108 := nat_lit 283467408426159824833033226676848987197241848746267875586777468091978394241

noncomputable def ep109 := BSN.sin_dyadic_bound_f 810034641 536870912 3 2 262144 71320 ep107 ep90 ep103 ep108 ep92 ep103 261640 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 810034641) qz278 0 2 ep107 ep90 ep103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 810034641) qz279 0 2 ep108 ep92 ep103 rfl rfl rfl rfl) rfl rfl

noncomputable def ep110 := @Enclosure.Real.IsNear.sin_image qz35 qz295 Bool.false 24278465 262144 425 262144 Bool.true 261640 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 303480821 3276800 11509 7125000 24278465 262144 425 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz36 57545 1000 0 1 210952 131072 1 35625 303480821 3276800 11509 7125000 qz21 qz296 rfl) rfl) (Enclosure.sfrac_false_div 24278465 262144) (BSN.sin_reduce2 qz295 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 57001120435152428728320) qz33) 226375608064910080 72057594037927936 Bool.false 261640 262144 14 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q2 24278465 262144 226375608064910080 72057594037927936 14 57001120435152428728320 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 261640 262144 57001120435152428728320 37778931862957161709568 810034641 536870912 71320 71250 (ep109 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz297 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 117235 262144 1 262144 117235 262144 1 262144 (ep98 rfl rfl) rfl)

noncomputable def ep111 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.true 1903779165 68719476736 1806337540859 2448131358720000 Bool.false 3834170675 8589934592 453769987871 612032839680000 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz35) 117235 262144 1 262144 16239 262144 15402769 9338880000 1903779165 68719476736 1806337540859 2448131358720000 qz297 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.true 16239 262144 15402769 9338880000 16239 262144 15402769 9338880000 (ep106 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 117235 262144 1 262144 32705 32768 15402769 9338880000 3834170675 8589934592 453769987871 612032839680000 qz297 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.true 32705 32768 15402769 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.true 261640 262144 15402769 9338880000 32705 32768 15402769 9338880000 (ep110 rfl rfl) rfl)) rfl)

noncomputable def ep112 := @ep45 1903779165 68719476736 1806337540859 2448131358720000 Bool.false 3834170675 8589934592 453769987871 612032839680000 Bool.false 550458079343414345728 64081754459 68719476736 3009812325277 816043786240000 Bool.false 36423310131836485632 4240231371 34359738368 1507203090451 408021893120000 (ep46 (BSN.head_sum_c_succ qz6 4 5 rfl rfl) (ep96 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep97 ep111) rfl rfl

noncomputable abbrev qz298 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz37 := (@Inv.inv Real Real.instInv (Real.sqrt qz298))

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep113 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)))) Bool.true 740070055 2147483648 270245647 398458880000 Bool.true 470005085 2147483648 17235788283 25501368320000 (BSN.cpow_neg_s_mk qz17 57545 1000 6 qz18 rfl)

noncomputable abbrev qz299 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz19)

noncomputable def ep114 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz298) 642119 262144 1 262144 53509 53511 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz298) (Real.sqrt qz299) Bool.false 642119 262144 1 262144 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz299) Bool.false 642119 262144 1 262144 642119 262144 1 262144 (BSN.sqrt_enclosure 6 1 321059 321060 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep115 := BSN.log_dyadic_bound 2 10 4 3 105000000 131072 35625 1434560 960 53145 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz39 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep116 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz39 57545 1000 0 1 4034681531866359 2251799813685248 800000000057 28500000000000000 46435149750249925731 450359962737049600 9207200000656013 5700000000000000000 qz21 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 800000000057 28500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz299) Bool.false 8461340443916598509568 4722366482869645213696 1000000000071250 35625000000000000000 4034681531866359 2251799813685248 800000000057 28500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 53145 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep115 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep117 := nat_lit 84744586949080420343618935063736881

noncomputable def ep118 := BSN.sin_dyadic_bound_f 539545397 536870912 2 1 262144 71320 ep117 ep57 ep117 ep117 ep58 ep117 221288 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 539545397) qz278 0 1 ep117 ep57 ep117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 539545397) qz279 0 1 ep117 ep58 ep117 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz300 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13514407) qz26)

noncomputable def ep119 := @Enclosure.Real.IsNear.cos_image qz38 qz300 Bool.false 13514407 131072 53 32768 Bool.true 221288 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 46435149750249925731 450359962737049600 9207200000656013 5700000000000000000 13514407 131072 53 32768 (ep116 rfl) rfl) (Enclosure.sfrac_false_div 13514407 131072) (BSN.cos_reduce1 qz300 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18983566020210017173504) qz28) 226375608064910080 72057594037927936 Bool.false 221288 262144 16 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q1 13514407 131072 226375608064910080 72057594037927936 16 18983566020210017173504 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 221288 262144 18983566020210017173504 18889465931478580854784 539545397 536870912 71320 71250 (ep118 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep120 := nat_lit 11834893778731574346448368965853898654363033098222335630393390292347891041

noncomputable def ep121 := nat_lit 7181645017170251506205573067094937725114756112276663342945859999608161

noncomputable def ep122 := nat_lit 35490318046160382536332695751427506087638869782442453564494279157044456801

noncomputable def ep123 := BSN.cos_dyadic_bound_f 539545397 536870912 3 2 262144 71320 ep120 ep83 ep121 ep122 ep86 ep121 140536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 539545397) qz283 0 2 ep120 ep83 ep121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 539545397) qz284 0 2 ep122 ep86 ep121 rfl rfl rfl rfl) rfl rfl

noncomputable def ep124 := @Enclosure.Real.IsNear.sin_image qz38 qz300 Bool.false 13514407 131072 53 32768 Bool.false 140536 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 46435149750249925731 450359962737049600 9207200000656013 5700000000000000000 13514407 131072 53 32768 (ep116 rfl) rfl) (Enclosure.sfrac_false_div 13514407 131072) (BSN.sin_reduce1 qz300 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18983566020210017173504) qz28) 226375608064910080 72057594037927936 Bool.false 140536 262144 16 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q1 13514407 131072 226375608064910080 72057594037927936 16 18983566020210017173504 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 140536 262144 18983566020210017173504 18889465931478580854784 539545397 536870912 71320 71250 (ep123 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz301 := (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 107020 262144 2 262144 26755 65536 1 131072 (ep114 rfl rfl) rfl)

noncomputable def ep125 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38))) Bool.true 740070055 2147483648 270245647 398458880000 Bool.true 470005085 2147483648 17235788283 25501368320000 (@Enclosure.Real.IsNear.mulLit_ft qz37 (Real.cos qz38) 26755 65536 1 131072 27661 32768 1920893 1167360000 740070055 2147483648 270245647 398458880000 qz301 (@Enclosure.Real.IsNear.recentre' (Real.cos qz38) Bool.true 221288 262144 1920893 1167360000 27661 32768 1920893 1167360000 (ep119 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)) 26755 65536 1 131072 17567 32768 1920893 1167360000 470005085 2147483648 17235788283 25501368320000 qz301 (@Enclosure.Real.IsNear.neg (Real.sin qz38) Bool.false 17567 32768 1920893 1167360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz38) Bool.false 140536 262144 1920893 1167360000 17567 32768 1920893 1167360000 (ep124 rfl rfl) rfl)) rfl)

noncomputable def ep126 := @ep43 740070055 2147483648 270245647 398458880000 Bool.true 470005085 2147483648 17235788283 25501368320000 Bool.false 86757292908270845952 40399512699 68719476736 3563275410333 816043786240000 Bool.true 7043424219270479872 3279849989 34359738368 1782975702979 408021893120000 (ep44 (BSN.head_sum_c_succ qz6 5 6 rfl rfl) (ep112 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep113 ep125) rfl rfl

noncomputable abbrev qz302 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz40 := (@Inv.inv Real Real.instInv (Real.sqrt qz302))

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep127 := @Enclosure.Complex.IsNear.of_eq qz8 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)))) Bool.false 5653859103 34359738368 191275362101 306016419840000 Bool.false 23382818757 68719476736 1534544551183 2448131358720000 (BSN.cpow_neg_s_mk qz17 57545 1000 7 qz18 rfl)

noncomputable abbrev qz303 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) qz19)

noncomputable def ep128 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz302) 693567 262144 1 262144 49540 49541 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz302) (Real.sqrt qz303) Bool.false 693567 262144 1 262144 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz303) Bool.false 693567 262144 1 262144 693567 262144 1 262144 (BSN.sqrt_enclosure 7 1 346783 346784 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep129 := BSN.log_dyadic_bound 3 11 5 4 202569142545 131072 35625 5259111624 688905 73349 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz42 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep130 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz42 57545 1000 0 1 4381783608859895 2251799813685248 800000000057 28500000000000000 10085989510873706311 90071992547409920 9207200000656013 5700000000000000000 qz21 (BSN.isNear_log_sfrac 7 1 4381783608859895 2251799813685248 800000000057 28500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz303) Bool.false 9189266258887746519040 4722366482869645213696 1000000000071250 35625000000000000000 4381783608859895 2251799813685248 800000000057 28500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 73349 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep129 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep131 := nat_lit 3419866163843243126298206635059216

noncomputable def ep132 := BSN.sin_dyadic_bound_f 241825602 536870912 2 1 262144 71320 ep131 ep57 ep131 ep131 ep58 ep131 114126 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 241825602) qz278 0 1 ep131 ep57 ep131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 241825602) qz279 0 1 ep131 ep58 ep131 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz304 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7338523) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep133 := @Enclosure.Real.IsNear.cos_image qz41 qz304 Bool.false 7338523 65536 425 262144 Bool.false 114126 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 10085989510873706311 90071992547409920 9207200000656013 5700000000000000000 7338523 65536 425 262144 (ep130 rfl) rfl) (Enclosure.sfrac_false_div 7338523 65536) (BSN.cos_reduce3 qz304 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4254240983915824152576) qz282) 226375608064910080 72057594037927936 Bool.false 114126 262144 17 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q3 7338523 65536 226375608064910080 72057594037927936 17 4254240983915824152576 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 114126 262144 4254240983915824152576 9444732965739290427392 241825602 536870912 71320 71250 (ep132 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep134 := BSN.cos_dyadic_bound_f 241825602 536870912 2 1 262144 71320 ep131 ep61 ep131 ep131 ep62 ep131 235997 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 241825602) qz283 0 1 ep131 ep61 ep131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 241825602) qz284 0 1 ep131 ep62 ep131 rfl rfl rfl rfl) rfl rfl

noncomputable def ep135 := @Enclosure.Real.IsNear.sin_image qz41 qz304 Bool.false 7338523 65536 425 262144 Bool.true 235997 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 10085989510873706311 90071992547409920 9207200000656013 5700000000000000000 7338523 65536 425 262144 (ep130 rfl) rfl) (Enclosure.sfrac_false_div 7338523 65536) (BSN.sin_reduce3 qz304 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4254240983915824152576) qz282) 226375608064910080 72057594037927936 Bool.false 235997 262144 17 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q3 7338523 65536 226375608064910080 72057594037927936 17 4254240983915824152576 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 235997 262144 4254240983915824152576 9444732965739290427392 241825602 536870912 71320 71250 (ep134 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz305 := (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 99081 262144 1 262144 99081 262144 1 262144 (ep128 rfl rfl) rfl)

noncomputable def ep136 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41))) Bool.false 5653859103 34359738368 191275362101 306016419840000 Bool.false 23382818757 68719476736 1534544551183 2448131358720000 (@Enclosure.Real.IsNear.mulLit_ff qz40 (Real.cos qz41) 99081 262144 1 262144 57063 131072 15402769 9338880000 5653859103 34359738368 191275362101 306016419840000 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz41) Bool.false 114126 262144 15402769 9338880000 57063 131072 15402769 9338880000 (ep133 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)) 99081 262144 1 262144 235997 262144 15402769 9338880000 23382818757 68719476736 1534544551183 2448131358720000 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz41) Bool.true 235997 262144 15402769 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz41) Bool.true 235997 262144 15402769 9338880000 235997 262144 15402769 9338880000 (ep135 rfl rfl) rfl)) rfl)

noncomputable def ep137 := @ep41 5653859103 34359738368 191275362101 306016419840000 Bool.false 23382818757 68719476736 1534544551183 2448131358720000 Bool.false 1776646925629563863040 51707230905 68719476736 12220029127807 2448131358720000 Bool.false 578037959780227612672 16823118779 68719476736 12232398769057 2448131358720000 (ep42 (BSN.head_sum_c_succ qz6 6 7 rfl rfl) (ep126 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep127 ep136) rfl rfl

noncomputable abbrev qz306 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz43 := (@Inv.inv Real Real.instInv (Real.sqrt qz306))

noncomputable abbrev qz44 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep138 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)))) Bool.false 5835861153 17179869184 45172990453 76504104960000 Bool.true 3368110221 34359738368 716384381623 1224065679360000 (BSN.cpow_neg_s_mk qz17 57545 1000 8 qz18 rfl)

noncomputable abbrev qz307 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz19)

noncomputable def ep139 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz306) 741455 262144 1 262144 46340 46342 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz306) (Real.sqrt qz307) Bool.false 741455 262144 1 262144 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz307) Bool.false 741455 262144 1 262144 741455 262144 1 262144 (BSN.sqrt_enclosure 8 1 370727 370728 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep140 := BSN.log_dyadic_bound 0 16 1 0 1 131072 35625 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz45 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep141 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz45 57545 1000 0 1 9364972152248037 4503599627370496 1600000000171 57000000000000000 107781464500222657833 900719925474099200 18414400001968039 11400000000000000000 qz21 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz307) Bool.false 9819885039515637645312 4722366482869645213696 1000000000106875 35625000000000000000 9364972152248037 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep140 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep142 := nat_lit 517528237713257047570437126750625

noncomputable def ep143 := BSN.cos_dyadic_bound_f 150828535 536870912 2 1 262144 71320 ep142 ep61 ep142 ep142 ep62 ep142 251866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 150828535) qz283 0 1 ep142 ep61 ep142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 150828535) qz284 0 1 ep142 ep62 ep142 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15684267) qz26)

noncomputable def ep144 := @Enclosure.Real.IsNear.cos_image qz44 qz308 Bool.false 15684267 131072 425 262144 Bool.false 251866 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 107781464500222657833 900719925474099200 18414400001968039 11400000000000000000 15684267 131072 425 262144 (ep141 rfl) rfl) (Enclosure.sfrac_false_div 15684267 131072) (BSN.cos_reduce0 qz308 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5306807315363805528064) qz28) 226375608064910080 72057594037927936 Bool.false 251866 262144 19 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 15684267 131072 226375608064910080 72057594037927936 19 5306807315363805528064 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 251866 262144 5306807315363805528064 18889465931478580854784 150828535 536870912 71320 71250 (ep143 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep145 := BSN.sin_dyadic_bound_f 150828535 536870912 2 1 262144 71320 ep142 ep57 ep142 ep142 ep58 ep142 72681 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 150828535) qz278 0 1 ep142 ep57 ep142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 150828535) qz279 0 1 ep142 ep58 ep142 rfl rfl rfl rfl) rfl rfl

noncomputable def ep146 := @Enclosure.Real.IsNear.sin_image qz44 qz308 Bool.false 15684267 131072 425 262144 Bool.false 72681 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 107781464500222657833 900719925474099200 18414400001968039 11400000000000000000 15684267 131072 425 262144 (ep141 rfl) rfl) (Enclosure.sfrac_false_div 15684267 131072) (BSN.sin_reduce0 qz308 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5306807315363805528064) qz28) 226375608064910080 72057594037927936 Bool.false 72681 262144 19 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 15684267 131072 226375608064910080 72057594037927936 19 5306807315363805528064 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 72681 262144 5306807315363805528064 18889465931478580854784 150828535 536870912 71320 71250 (ep145 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz309 := (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 92682 262144 2 262144 46341 131072 1 131072 (ep139 rfl rfl) rfl)

noncomputable def ep147 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44))) Bool.false 5835861153 17179869184 45172990453 76504104960000 Bool.true 3368110221 34359738368 716384381623 1224065679360000 (@Enclosure.Real.IsNear.mulLit_ff qz43 (Real.cos qz44) 46341 131072 1 131072 125933 131072 15402769 9338880000 5835861153 17179869184 45172990453 76504104960000 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz44) Bool.false 251866 262144 15402769 9338880000 125933 131072 15402769 9338880000 (ep144 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)) 46341 131072 1 131072 72681 262144 15402769 9338880000 3368110221 34359738368 716384381623 1224065679360000 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz44) Bool.false 72681 262144 15402769 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz44) Bool.false 72681 262144 15402769 9338880000 72681 262144 15402769 9338880000 (ep146 rfl rfl) rfl)) rfl)

noncomputable def ep148 := @ep39 5835861153 17179869184 45172990453 76504104960000 Bool.true 3368110221 34359738368 716384381623 1224065679360000 Bool.false 1289360787552891568128 75050675517 68719476736 4555188274101 816043786240000 Bool.false 346583187803934294016 10086898337 68719476736 4555055844101 816043786240000 (ep40 (BSN.head_sum_c_succ qz6 7 8 rfl rfl) (ep137 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep138 ep147) rfl rfl

theorem EMRow13.d6 : Enclosure.Complex.IsNear qz4 Bool.false 75050675517 68719476736 4555188274101 816043786240000 Bool.false 10086898337 68719476736 4555055844101 816043786240000 := ep38 (BSN.head_sum_c_succ qz6 8 9 rfl rfl) (ep148 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow13.d7 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow13.d8 : @Eq Nat (Nat.pow 15 1) 15 := @Eq.refl Nat 15

noncomputable def ep149 := nat_lit 30671813266111334610772212953

noncomputable def ep150 := nat_lit 17181466462957170546494668800

noncomputable def ep151 := nat_lit 366969096024652463001879249345581731

noncomputable def ep152 := nat_lit 36342828475356671292683059200000000000

noncomputable abbrev qz488 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz470 := qz488

noncomputable abbrev qz310 := qz470

noncomputable abbrev qz46 := qz310

noncomputable abbrev qz471 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz311 := qz471

noncomputable abbrev qz47 := qz311

noncomputable abbrev qz489 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz490 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz472 := (@HAdd.hAdd Complex Complex Complex qz486 (@HAdd.hAdd Complex Complex Complex qz486 qz489 (@HMul.hMul Complex Complex Complex qz488 Complex.I (@HDiv.hDiv Complex Complex Complex qz490 (↑qz487) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz312 := qz472

noncomputable abbrev qz48 := (Complex.Stirling.logGammaStirling 1 qz312)

noncomputable abbrev qz473 := (@HAdd.hAdd Complex Complex Complex qz486 qz489 (@HMul.hMul Complex Complex Complex qz488 Complex.I (@HDiv.hDiv Complex Complex Complex qz490 (↑qz487) (2 : Complex))))

noncomputable abbrev qz313 := qz473

noncomputable abbrev qz49 := qz313

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz263 (@HDiv.hDiv Real Real Real qz266 qz276 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz314 := (@instHSub Real Real.instSub)

noncomputable def ep153 := Complex.re (@HMul.hMul Complex Complex Complex qz46 (Complex.exp (@HMul.hMul Complex Complex Complex qz46 Complex.I ↑(@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50))) (zetaApproximant qz6 1 15))

noncomputable def ep154 := @Enclosure.Real.IsNear.of_eq ep153 (@HSub.hSub Real Real Real qz314 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.re (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.im (zetaApproximant qz6 1 15))))

noncomputable def ep155 := nat_lit 3407984686052564237838642249

noncomputable def ep156 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.re (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.im (zetaApproximant qz6 1 15))) ep155

noncomputable def ep157 := nat_lit 1909051829217463394054963200

noncomputable def ep158 := nat_lit 366295558754950591541105047722683053

noncomputable def ep159 := nat_lit 2147683307869646318311833600

noncomputable def ep160 := nat_lit 112256211616978576795700270483113

noncomputable def ep161 := nat_lit 6057138079226111882113843200000000000

noncomputable def ep162 := nat_lit 7319260152635787958874289156692283241641117222122291200

noncomputable def ep163 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.re (zetaApproximant qz6 1 15)) 262143 262144 6781519

noncomputable def ep164 := nat_lit 34153245602122312767182437

noncomputable def ep165 := nat_lit 3891561779930427555840000000

noncomputable def ep166 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) Bool.true 262143 262144 6781519

noncomputable abbrev qz315 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4529497) qz26)

noncomputable def ep167 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) qz315 Bool.false 4529497 131072 183

noncomputable def ep168 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) Bool.false 373517622279590641201 10808639105689190400 86365368586131038113 124518400000000000000000

noncomputable def ep169 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50 29180755228753940953 432345564227567616 31697618586131038113 124518400000000000000000 863416689 26214400

noncomputable def ep170 := nat_lit 391661614299444036187979776

noncomputable def ep171 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 40637558024882755859 900719925474099200 41239171665565934999 93388800000000000000000 Bool.false 29180755228753940953 432345564227567616

noncomputable def ep172 := @Enclosure.Complex.IsNear.subLitP qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 34584882679879200859 900719925474099200 13309483888241811933 31129600000000000000000 Bool.false 30516483182425154521 432345564227567616 84607095758019559139

noncomputable def ep173 := nat_lit 183015291178108888703311426107736064

noncomputable def ep174 := nat_lit 8213652398412868827496452789895168

noncomputable abbrev qz491 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz474 := qz491

noncomputable abbrev qz316 := (@HSub.hSub Complex Complex Complex qz471 qz472 qz474)

noncomputable abbrev qz317 := (Complex.log qz472)

noncomputable abbrev qz51 := (@HSub.hSub Complex Complex Complex qz311 (@HMul.hMul Complex Complex Complex qz310 qz316 qz317) qz312)

noncomputable abbrev qz318 := qz474

noncomputable abbrev qz52 := (@HMul.hMul Complex Complex Complex qz310 qz318 ↑(Real.log qz267))

noncomputable abbrev qz475 := qz490

noncomputable abbrev qz319 := qz475

noncomputable abbrev qz53 := qz319

noncomputable abbrev qz54 := (@instHMul Nat instMulNat)

noncomputable abbrev qz476 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz320 := qz476

noncomputable abbrev qz55 := qz320

noncomputable abbrev qz56 := qz312

noncomputable abbrev qz321 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz57 := qz321

noncomputable abbrev qz322 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz58 := qz322

noncomputable abbrev qz323 := (@instHSub Int Int.instSub)

noncomputable abbrev qz324 := (@instHMul Int Int.instMul)

noncomputable def ep175 := @Enclosure.Complex.IsNear.of_eq qz48 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz51 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz323 qz57 (@HMul.hMul Int Int Int qz324 qz58 (@Nat.cast Int instNatCastInt k)))))) Bool.true 34584882679879200859

noncomputable def ep176 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz51 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz323 qz57 (@HMul.hMul Int Int Int qz324 qz58 (@Nat.cast Int instNatCastInt k))))) Bool.true 34585085442181460059 900719925474099200

noncomputable def ep177 := nat_lit 74270470023039002460010053632

noncomputable def ep178 := nat_lit 163834121571812550794301931520000

noncomputable def ep179 := @ep176 6498750195650871 15200000000000000000 Bool.false 254314398037261626043 3602879701896396800 3442400001981339 15200000000000000000 Bool.false 483423 2147483648 3 2147483648 Bool.true 1854571769 644245094400 11509 644245094400 Bool.true ep177 34584882679879200859 900719925474099200 13309483888241811933 31129600000000000000000 Bool.false ep178

noncomputable def ep180 := @Enclosure.Complex.IsNear.addLitP qz51 qz52 Bool.true 35412787487649722459 900719925474099200 6324800000338371 15200000000000000000

noncomputable def ep181 := nat_lit 9066272638155216665706496

noncomputable def ep182 := @ep180 Bool.false 254314398037261626043 3602879701896396800 3442400001981339 15200000000000000000 Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 Bool.true ep181 34585085442181460059 900719925474099200 6498750195650871 15200000000000000000 Bool.false 254314398037261626043 254314398037261626043 3602879701896396800

noncomputable abbrev qz59 := (@HMul.hMul Complex Complex Complex qz310 qz316 qz317)

noncomputable def ep183 := @Enclosure.Complex.IsNear.subLitP qz59 qz56 Bool.true 33386167655332999259 900719925474099200 6324800000338371 15200000000000000000 Bool.false 357978254260075702971

noncomputable def ep184 := @ep183 3602879701896396800 3442400001981339 15200000000000000000 Bool.false 9000 4000 0 1 Bool.false 115090 4000 0 1 Bool.true 141651149950598889836000 35412787487649722459 900719925474099200 6324800000338371 15200000000000000000 Bool.false 1017257592149046504172000 254314398037261626043 3602879701896396800 3442400001981339 15200000000000000000

noncomputable abbrev qz60 := qz316

noncomputable abbrev qz61 := qz317

noncomputable def ep185 := @Enclosure.Complex.IsNear.mul qz60 qz61 Bool.true 33386167655332999259 900719925474099200 6324800000338371 15200000000000000000 Bool.false 357978254260075702971 3602879701896396800 3442400001981339

noncomputable abbrev qz62 := (Complex.re qz316)

noncomputable abbrev qz63 := (Complex.re qz317)

noncomputable abbrev qz64 := (Complex.im qz316)

noncomputable abbrev qz65 := (Complex.im qz317)

noncomputable def ep186 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz62 qz63) (@HMul.hMul Real Real Real qz0 qz64 qz65) 212004904507154633 36028797018963968 5600000003591 456000000000000000 9671572567002966271 225179981368524800

noncomputable def ep187 := nat_lit 300715864423773203190507862572924928

noncomputable def ep188 := @Enclosure.Real.IsNear.mulLit_ff qz62 qz63 7000 4000 0 1 30286414929593519 9007199254740992 800000000513 114000000000000000

noncomputable def ep189 := @Enclosure.Complex.IsNear.re_isNear qz60 Bool.false 7000 4000 0 1 Bool.false 115090 4000 0 1

noncomputable abbrev qz325 := (Enclosure.sfrac Bool.false 115090 4000)

noncomputable abbrev qz66 := qz325

noncomputable def ep190 := @Enclosure.Complex.IsNear.of_eq qz60 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz66) Bool.false 7000 4000 0 1 Bool.false 115090 4000 0

noncomputable abbrev qz326 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz67 := (Complex.mk qz326 qz325)

noncomputable def ep191 := @Enclosure.Complex.IsNear.of_eq qz61 (Complex.log qz67) Bool.false 30286414929593519 9007199254740992 800000000513 114000000000000000 Bool.false 840348646016419 562949953421312 1600000000057 114000000000000000

noncomputable def ep192 := nat_lit 43447157053633374337220821503477884676713266079454298422806702699097450000000000000000

noncomputable def ep193 := nat_lit 853958821669552308494234019387637543735546774558449708923750971937040000000000000000

noncomputable def ep194 := nat_lit 50735900916461061740904300231654401198656130636737805643617233050000000000000000

noncomputable def ep195 := BSN.log_dyadic_bound 5134708100 21518708100 5 4 ep192 262144 71250 ep193 ep194 127562 26653416200 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5134708100) (BSN.artanhQ 21518708100) 0 4 ep193 ep192 ep194 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz68 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz327 := (Real.log (Enclosure.sfrac Bool.false 13326708100 16000000))

noncomputable abbrev qz328 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz329 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep196 := @Enclosure.Real.IsNear.mulLit_ff qz68 qz327 1 2 0 1 30286414929593519 4503599627370496 800000000513 57000000000000000 30286414929593519 9007199254740992 800000000513 114000000000000000 qz328 (BSN.isNear_log_sfrac 13326708100 16000000 30286414929593519 4503599627370496 800000000513 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13326708100) qz329)) Bool.false 63515215642426907557888 9444732965739290427392 1000000000641250 71250000000000000000 30286414929593519 4503599627370496 800000000513 57000000000000000 (BSN.log_rat_reduce_isNear 13326708100 16000000 9 26653416200 16384000000 127562 262144 24973259072661432 36028797018963968 71250 1000000000000000 rfl rfl rfl rfl (ep195 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep197 := BSN.arctan_dyadic_bound_f 9000 115090 1 0 262144 71250 0 1 1 0 1 1 20457 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 115090) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 115090) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz263 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz70 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz328 BSN.pi_near_15 rfl)

noncomputable abbrev qz330 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 115090)))

noncomputable def ep198 := @Enclosure.Real.IsNear.subLit_ff_p qz69 qz330 884279719003555 562949953421312 1 2000000000000000 20457 262144 1 71250 220292355461328142336 840348646016419 562949953421312 1600000000057 114000000000000000 qz70 (ep197 rfl) rfl rfl

noncomputable abbrev qz331 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 115090) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep199 := @Enclosure.Complex.IsNear.re_isNear qz61 Bool.false 30286414929593519 9007199254740992 800000000513 114000000000000000 Bool.false 840348646016419 562949953421312 1600000000057 114000000000000000 (ep191 (@congrArg Complex Complex qz56 qz67 Complex.log (BSN.w_shift_mk qz17 Bool.false 57545 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz67) Bool.false 30286414929593519 9007199254740992 800000000513 114000000000000000 Bool.false 840348646016419 562949953421312 1600000000057 114000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz67)) (@HMul.hMul Real Real Real qz0 qz68 qz327) Bool.false 30286414929593519 9007199254740992 800000000513 114000000000000000 (Enclosure.clog_re_eq 9000 115090 4000 13326708100 16000000 rfl rfl rfl) (ep196 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz67)) qz331 Bool.false 840348646016419 562949953421312 1600000000057 114000000000000000 (Enclosure.clog_im_eq 9000 115090 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz331 (@HSub.hSub Real Real Real qz314 qz69 qz330) Bool.false 840348646016419 562949953421312 1600000000057 114000000000000000 (BSN.arctan_recip 115090 9000 rfl rfl) ep198))))

noncomputable def ep200 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz65 115090 4000 0 1 840348646016419 562949953421312 1600000000057 114000000000000000

noncomputable def ep201 := @Enclosure.Complex.IsNear.im_isNear qz60 Bool.false 7000 4000 0 1 Bool.false 115090 4000 0 1

noncomputable def ep202 := @Enclosure.Complex.IsNear.im_isNear qz61 Bool.false 30286414929593519 9007199254740992 800000000513 114000000000000000 Bool.false 840348646016419 562949953421312 1600000000057 114000000000000000 (ep191 (@congrArg Complex Complex qz56 qz67 Complex.log (BSN.w_shift_mk qz17 Bool.false 57545 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz67) Bool.false 30286414929593519 9007199254740992 800000000513 114000000000000000 Bool.false 840348646016419 562949953421312 1600000000057 114000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz67)) (@HMul.hMul Real Real Real qz0 qz68 qz327) Bool.false 30286414929593519 9007199254740992 800000000513 114000000000000000 (Enclosure.clog_re_eq 9000 115090 4000 13326708100 16000000 rfl rfl rfl) (ep196 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz67)) qz331 Bool.false 840348646016419 562949953421312 1600000000057 114000000000000000 (Enclosure.clog_im_eq 9000 115090 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz331 (@HSub.hSub Real Real Real qz314 qz69 qz330) Bool.false 840348646016419 562949953421312 1600000000057 114000000000000000 (BSN.arctan_recip 115090 9000 rfl rfl) ep198))))

noncomputable abbrev qz332 := (Enclosure.Real.IsNear.const Bool.false 115090 4000)

noncomputable abbrev qz71 := (@ep190 1 (BSN.w_sub_half_mk qz276 Bool.false 57545 1000 2 qz277 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz325 Bool.false 7000 4000 0 1 Bool.false 115090 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz332))

noncomputable def ep203 := @ep186 18414400000656013 45600000000000000000 ep187 33386167655332999259 900719925474099200 6324800000338371 15200000000000000000 (@ep188 212004904507154633 36028797018963968 5600000003591 456000000000000000 (ep189 qz71) ep199 rfl) (@ep200 9671572567002966271 225179981368524800 18414400000656013 45600000000000000000 (ep201 qz71) ep202 rfl) rfl

noncomputable def ep204 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz62 qz65) (@HMul.hMul Real Real Real qz0 qz64 qz63) 5882440522114933 2251799813685248 11200000000399 456000000000000000 348566349424691810171 3602879701896396800

noncomputable def ep205 := nat_lit 806095366246208804091149699732471808

noncomputable def ep206 := @Enclosure.Real.IsNear.mulLit_ff qz62 qz65 7000 4000 0 1 840348646016419 562949953421312 1600000000057 114000000000000000

noncomputable def ep207 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz63 115090 4000 0 1 30286414929593519 9007199254740992 800000000513 114000000000000000

noncomputable def ep208 := @ep204 9207200005904117 45600000000000000000 ep205 357978254260075702971 3602879701896396800 3442400001981339 15200000000000000000 (@ep206 5882440522114933 2251799813685248 11200000000399 456000000000000000 (ep189 qz71) ep202 rfl) (@ep207 348566349424691810171 3602879701896396800 9207200005904117 45600000000000000000 (ep201 qz71) ep199 rfl) rfl

noncomputable def ep209 := @Enclosure.Complex.IsNear.of_eq qz56 qz67 Bool.false 9000 4000 0 1 Bool.false 115090 4000 0 1 (BSN.w_shift_mk qz17 Bool.false 57545 1000 2 qz18 rfl)

noncomputable abbrev qz333 := (ep209 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 115090 4000) Bool.false 9000 4000 0 1 Bool.false 115090 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 115090 4000)))

noncomputable abbrev qz72 := qz333

noncomputable def ep210 := ep184 (@ep185 15200000000000000000 (ep203 rfl) (ep208 rfl)) qz72 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz73 := qz318

noncomputable def ep211 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz73) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz73) (Complex.im ↑qz3)) 240893 262144 3 262144 0 1 0 1 240893 240893

noncomputable def ep212 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz73) (Complex.re ↑qz3) 1 2 0 1 240893 131072 3 131072 240893 262144 3 262144

noncomputable abbrev qz74 := (@Enclosure.Complex.IsNear.of_eq qz318 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz274) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz274 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz328 qz286))

noncomputable def ep213 := ep212 (@Enclosure.Complex.IsNear.re_isNear qz73 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz74) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 240893 131072 3 131072 (Complex.ofReal_re qz3) EMRow13.d4)

noncomputable def ep214 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz73) (Complex.im ↑qz3) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep215 := ep214 (@Enclosure.Complex.IsNear.im_isNear qz73 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz74) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep216 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz73) (Complex.im ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz73) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep217 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz73) (Complex.im ↑qz3) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep218 := ep217 (@Enclosure.Complex.IsNear.re_isNear qz73 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz74) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep219 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz73) (Complex.re ↑qz3) 0 1 0 1 240893 131072 3 131072 0 1 0 1

noncomputable def ep220 := ep219 (@Enclosure.Complex.IsNear.im_isNear qz73 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz74) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 240893 131072 3 131072 (Complex.ofReal_re qz3) EMRow13.d4)

noncomputable def ep221 := @ep182 3442400001981339 15200000000000000000 (ep210 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz73 (↑qz3) Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 (@ep211 262144 3 262144 (ep213 rfl) (ep215 rfl) rfl rfl) (@ep216 1 0 1 (ep218 rfl) (ep220 rfl) rfl rfl))

noncomputable abbrev qz75 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz334 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz76 := (@HMul.hMul Complex Complex Complex qz310 (@HMul.hMul Complex Complex Complex qz310 (2 : Complex) qz334) (@HSub.hSub Complex Complex Complex qz311 (@HMul.hMul Complex Complex Complex qz310 (2 : Complex) qz334) (1 : Complex)))

noncomputable abbrev qz335 := (@HPow.hPow Complex Int Complex qz476 qz472 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz77 := qz335

noncomputable def ep222 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz323 qz57 (@HMul.hMul Int Int Int qz324 qz58 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz323 qz57 (@HMul.hMul Int Int Int qz324 qz58 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76) qz77)) Bool.false 483423 2147483648 3 2147483648

noncomputable def ep223 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz323 qz57 (@HMul.hMul Int Int Int qz324 qz58 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76) qz77) Bool.false 0 1 0 1 Bool.false

noncomputable def ep224 := @ep223 0 1 0 1 Bool.false 483423 2147483648 3 2147483648 Bool.true 1854571769 644245094400 11509 644245094400 Bool.false 483423 483423 2147483648 3 2147483648 Bool.true 1854571769 1854571769 644245094400 11509

noncomputable def ep225 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz323 qz57 (@HMul.hMul Int Int Int qz324 qz58 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep226 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76) qz77 Bool.false 483423 2147483648 3 2147483648 Bool.true 1854571769 644245094400 11509 644245094400

noncomputable abbrev qz78 := (Complex.re qz335)

noncomputable abbrev qz79 := (Complex.im qz335)

noncomputable def ep227 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz78) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz79) 483423 2147483648 3 2147483648 0 1 0

noncomputable def ep228 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz78 1 12 0 1 1450269 536870912 9 536870912 483423

noncomputable def ep229 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz336 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz14 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz22)

noncomputable def ep230 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep229 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz336)

noncomputable def ep231 := @Enclosure.Complex.IsNear.re_isNear qz77 Bool.false 1450269 536870912 9 536870912 Bool.true 1854571769 53687091200 11509 53687091200

noncomputable abbrev qz477 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz337 := (@HPow.hPow Complex Nat Complex qz477 qz472 1)

noncomputable abbrev qz80 := (@Inv.inv Complex Complex.instInv qz337)

noncomputable def ep232 := @Enclosure.Complex.IsNear.of_eq qz77 qz80 Bool.false 1450269 536870912 9 536870912 Bool.true 1854571769 53687091200 11509

noncomputable def ep233 := @Enclosure.Complex.IsNear.of_parts qz80 Bool.false 1450269 536870912 9 536870912 Bool.true 1854571769 53687091200 11509

noncomputable abbrev qz81 := (Complex.re qz337)

noncomputable abbrev qz82 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz83 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz84 := qz337

noncomputable def ep234 := @Enclosure.Real.IsNear.mulLit_ff qz81 (@Inv.inv Real Real.instInv (@DFunLike.coe qz82 Complex (fun (x : Complex) => Real) qz83 Complex.normSq qz84)) 9000 4000 0 1 161141 134217728 1 134217728

noncomputable def ep235 := @Enclosure.Complex.IsNear.re_isNear qz84 Bool.false 9000 4000 0 1 Bool.false 115090 4000 0 1

noncomputable def ep236 := @Enclosure.Complex.IsNear.of_eq qz84 qz56 Bool.false 9000 4000 0 1 Bool.false 115090 4000 0

noncomputable def ep237 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz82 Complex (fun (x : Complex) => Real) qz83 Complex.normSq qz84)) Bool.false 161141 134217728 1 134217728 161141 134217728 1

noncomputable abbrev qz85 := (Complex.im qz337)

noncomputable abbrev qz338 := (@instHAdd Real Real.instAdd)

noncomputable def ep238 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz82 Complex (fun (x : Complex) => Real) qz83 Complex.normSq qz84) (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 qz81 qz81) (@HMul.hMul Real Real Real qz0 qz85 qz85)) Bool.false 133267081 160000 0 1

noncomputable def ep239 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz81 qz81) (@HMul.hMul Real Real Real qz0 qz85 qz85) 81 16 0 1 132457081 160000

noncomputable def ep240 := @Enclosure.Real.IsNear.mulLit_ff qz81 qz81 9000 4000 0 1 9000 4000 0 1

noncomputable def ep241 := @Enclosure.Real.IsNear.mulLit_ff qz85 qz85 115090 4000 0 1 115090 4000 0 1

noncomputable def ep242 := @Enclosure.Complex.IsNear.im_isNear qz84 Bool.false 9000 4000 0 1 Bool.false 115090 4000 0 1

noncomputable abbrev qz86 := (ep235 (@ep236 1 (BSN.pow_one_c qz312) qz333))

noncomputable abbrev qz87 := (ep242 (@ep236 1 (BSN.pow_one_c qz312) qz333))

noncomputable def ep243 := @ep239 0 1 2132273296 133267081 160000 0 1 (@ep240 81 16 0 1 qz86 qz86 rfl) (@ep241 132457081 160000 0 1 qz87 qz87 rfl)

noncomputable def ep244 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz82 Complex (fun (x : Complex) => Real) qz83 Complex.normSq qz84) 133267081 160000 0 1 80570 80571 67108864 (ep238 (Enclosure.Complex.normSq_eq_mul_add_mul qz84) (ep243 rfl rfl)) rfl

noncomputable def ep245 := @Enclosure.Real.IsNear.of_eq (Complex.re qz80) (@HMul.hMul Real Real Real qz0 qz81 (@Inv.inv Real Real.instInv (@DFunLike.coe qz82 Complex (fun (x : Complex) => Real) qz83 Complex.normSq qz84))) Bool.false 1450269 536870912 9 536870912 (Enclosure.Complex.inv_re_eq_mul qz84) (@ep234 1450269 536870912 9 536870912 qz86 (@ep237 134217728 (ep244 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep246 := @Enclosure.Real.IsNear.of_eq (Complex.im qz80) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz85) (@Inv.inv Real Real.instInv (@DFunLike.coe qz82 Complex (fun (x : Complex) => Real) qz83 Complex.normSq qz84))) Bool.true 1854571769 53687091200 11509 53687091200 (Enclosure.Complex.inv_im_eq_mul qz84)

noncomputable def ep247 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz85) (@Inv.inv Real Real.instInv (@DFunLike.coe qz82 Complex (fun (x : Complex) => Real) qz83 Complex.normSq qz84)) 115090 4000 0 1 161141 134217728 1

noncomputable def ep248 := @ep247 134217728 1854571769 53687091200 11509 53687091200 (@Enclosure.Real.IsNear.neg qz85 Bool.false 115090 4000 0 1 qz87) (@ep237 134217728 (ep244 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep249 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz79 0 1 0 1 1854571769 53687091200 11509 53687091200 0

noncomputable def ep250 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep229 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz336)

noncomputable def ep251 := @Enclosure.Complex.IsNear.im_isNear qz77 Bool.false 1450269 536870912 9 536870912 Bool.true 1854571769 53687091200 11509 53687091200

noncomputable abbrev qz88 := (@ep232 53687091200 (BSN.zpow_one_sub_two_mul qz312 1 1 rfl rfl) (@ep233 53687091200 ep245 (ep246 ep248)))

noncomputable def ep252 := @ep227 1 483423 483423 2147483648 3 2147483648 (@ep228 2147483648 3 2147483648 ep230 (ep231 qz88) rfl) (@ep249 1 0 1 ep250 (ep251 qz88) rfl) rfl

noncomputable def ep253 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz79) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz78) 1854571769 644245094400 11509 644245094400 0 1 0

noncomputable def ep254 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz79 1 12 0 1 1854571769 53687091200 11509 53687091200 1854571769

noncomputable def ep255 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz78 0 1 0 1 1450269 536870912 9 536870912 0

noncomputable def ep256 := @ep253 1 1854571769 1854571769 644245094400 11509 644245094400 (@ep254 644245094400 11509 644245094400 ep230 (ep251 qz88) rfl) (@ep255 1 0 1 ep250 (ep231 qz88) rfl) rfl

noncomputable abbrev qz89 := (@Enclosure.Complex.IsNear.mk qz274 qz274 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz286 qz286)

noncomputable def ep257 := @ep224 644245094400 (@ep225 0 1 0 1 (BSN.stirling_sum_base qz56) qz89) (ep226 (ep252 rfl) (ep256 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep258 := @ep179 30516483182425154521 432345564227567616 84607095758019559139 373555200000000000000000 (ep221 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep222 Bool.true 1854571769 644245094400 11509 644245094400 (BSN.stirling_sum_succ qz56 0 1 rfl) (ep257 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep259 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz17 2) Bool.false 30263376725017775 4503599627370496 800000000513 57000000000000000 Bool.false 869614553171363 281474976710656

noncomputable abbrev qz90 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz269 qz313 qz334))

noncomputable def ep260 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 1) qz90) Bool.false 30263376725017775 4503599627370496 800000000513 57000000000000000 Bool.false 869614553171363 281474976710656 1600000000057 57000000000000000

noncomputable def ep261 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 1) qz90 Bool.false 30259305096021167 9007199254740992 800000000513 114000000000000000 Bool.false 879389898737059 562949953421312 1600000000057 114000000000000000 Bool.false

noncomputable def ep262 := nat_lit 545176528567051972325928442265600

noncomputable def ep263 := nat_lit 979098944404627696843344576512

noncomputable abbrev qz91 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz269 qz313 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep264 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 0) qz91) Bool.false 30259305096021167 9007199254740992 800000000513 114000000000000000 Bool.false 879389898737059 562949953421312 1600000000057 114000000000000000

noncomputable def ep265 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 0) qz91 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz339 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz66))

noncomputable def ep266 := @Enclosure.Complex.IsNear.of_eq qz91 qz339 Bool.false 30259305096021167 9007199254740992 800000000513 114000000000000000 Bool.false 879389898737059 562949953421312 1600000000057 114000000000000000

noncomputable def ep267 := nat_lit 42171660124929041200885682068730736286360057344953487552192741419097450000000000000000

noncomputable def ep268 := nat_lit 808581379654474309534998627062331541479088935839685148187303995937040000000000000000

noncomputable def ep269 := nat_lit 44746384142770308535470490247394323903757780040467699025697233050000000000000000

noncomputable def ep270 := BSN.log_dyadic_bound 5054708100 21438708100 5 4 ep267 262144 71250 ep268 ep269 125984 26493416200 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5054708100) (BSN.artanhQ 21438708100) 0 4 ep268 ep267 ep269 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep271 := @Enclosure.Real.IsNear.mulLit_ff qz68 (Real.log (Enclosure.sfrac Bool.false 13246708100 16000000)) 1 2 0 1 30259305096021167 4503599627370496 800000000513 57000000000000000 30259305096021167 9007199254740992 800000000513 114000000000000000 qz328 (BSN.isNear_log_sfrac 13246708100 16000000 30259305096021167 4503599627370496 800000000513 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13246708100) qz329)) Bool.false 63458362200730982416384 9444732965739290427392 1000000000641250 71250000000000000000 30259305096021167 4503599627370496 800000000513 57000000000000000 (BSN.log_rat_reduce_isNear 13246708100 16000000 9 26493416200 16384000000 125984 262144 24973259072661432 36028797018963968 71250 1000000000000000 rfl rfl rfl rfl (ep270 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep272 := BSN.arctan_dyadic_bound_f 1000 115090 1 0 262144 71250 0 1 1 0 1 1 2277 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 115090) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 115090) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz340 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz341 := (@Nat.cast Real Real.instNatCast 115090)

noncomputable def ep273 := @Enclosure.Real.IsNear.subLit_ff_p qz69 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz340 qz341)) 884279719003555 562949953421312 1 2000000000000000 2277 262144 1 71250 230526785614527594496 879389898737059 562949953421312 1600000000057 114000000000000000 qz70 (ep272 rfl) rfl rfl

noncomputable abbrev qz92 := (@HAdd.hAdd Complex Complex Complex qz269 qz313 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz342 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz66)

noncomputable def ep274 := @ep265 30259305096021167 9007199254740992 800000000513 114000000000000000 Bool.false 879389898737059 562949953421312 1600000000057 114000000000000000 Bool.false 30259305096021167 30259305096021167 9007199254740992 800000000513 114000000000000000 Bool.false 879389898737059 879389898737059 562949953421312 1600000000057 114000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz17) qz89) (ep266 (@congrArg Complex Complex qz92 qz342 Complex.log (BSN.w_shift_mk qz17 Bool.false 57545 1000 0 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz339 Bool.false 30259305096021167 9007199254740992 800000000513 114000000000000000 Bool.false 879389898737059 562949953421312 1600000000057 114000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz339) (@HMul.hMul Real Real Real qz0 qz68 (Real.log (Enclosure.sfrac Bool.false 13246708100 16000000))) Bool.false 30259305096021167 9007199254740992 800000000513 114000000000000000 (Enclosure.clog_re_eq 1000 115090 4000 13246708100 16000000 rfl rfl rfl) (ep271 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz339) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz340)) Bool.false 879389898737059 562949953421312 1600000000057 114000000000000000 (Enclosure.clog_im_eq 1000 115090 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz340)) (@HSub.hSub Real Real Real qz314 qz69 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz340 qz341))) Bool.false 879389898737059 562949953421312 1600000000057 114000000000000000 (BSN.arctan_recip 115090 1000 rfl rfl) ep273)))) rfl rfl

noncomputable abbrev qz343 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz66))

noncomputable def ep275 := @Enclosure.Complex.IsNear.of_eq qz90 qz343 Bool.false 30267448354014383 9007199254740992 800000000513 114000000000000000 Bool.false 859839207605667 562949953421312 1600000000057 114000000000000000

noncomputable def ep276 := nat_lit 42550822661543373552496001066440356485667592073193599334819489803097450000000000000000

noncomputable def ep277 := nat_lit 821984837926485448186605537502880719766641356428834073526190088737040000000000000000

noncomputable def ep278 := nat_lit 46474563340594859346688478176677222487391512201478846851073233050000000000000000

noncomputable def ep279 := BSN.log_dyadic_bound 5078708100 21462708100 5 4 ep276 262144 71250 ep277 ep278 126458 26541416200 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5078708100) (BSN.artanhQ 21462708100) 0 4 ep277 ep276 ep278 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep280 := @Enclosure.Real.IsNear.mulLit_ff qz68 (Real.log (Enclosure.sfrac Bool.false 13270708100 16000000)) 1 2 0 1 30267448354014383 4503599627370496 800000000513 57000000000000000 30267448354014383 9007199254740992 800000000513 114000000000000000 qz328 (BSN.isNear_log_sfrac 13270708100 16000000 30267448354014383 4503599627370496 800000000513 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13270708100) qz329)) Bool.false 63475439850517971337216 9444732965739290427392 1000000000641250 71250000000000000000 30267448354014383 4503599627370496 800000000513 57000000000000000 (BSN.log_rat_reduce_isNear 13270708100 16000000 9 26541416200 16384000000 126458 262144 24973259072661432 36028797018963968 71250 1000000000000000 rfl rfl rfl rfl (ep279 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep281 := BSN.arctan_dyadic_bound_f 5000 115090 1 0 262144 71250 0 1 1 0 1 1 11381 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 115090) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 115090) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz344 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep282 := @Enclosure.Real.IsNear.subLit_ff_p qz69 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz344 qz341)) 884279719003555 562949953421312 1 2000000000000000 11381 262144 1 71250 225401689238579970048 859839207605667 562949953421312 1600000000057 114000000000000000 qz70 (ep281 rfl) rfl rfl

noncomputable abbrev qz93 := (@HAdd.hAdd Complex Complex Complex qz269 qz313 qz334)

noncomputable abbrev qz345 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz66)

noncomputable def ep283 := @ep261 30267448354014383 9007199254740992 800000000513 114000000000000000 Bool.false 859839207605667 562949953421312 1600000000057 114000000000000000 Bool.false ep262 30263376725017775 4503599627370496 800000000513 57000000000000000 Bool.false ep263 869614553171363 281474976710656 1600000000057 57000000000000000 (ep264 (BSN.log_sum_c_succ qz17 0 1 rfl) (ep274 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep275 (@congrArg Complex Complex qz93 qz345 Complex.log (BSN.w_shift_mk qz17 Bool.false 57545 1000 1 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz343 Bool.false 30267448354014383 9007199254740992 800000000513 114000000000000000 Bool.false 859839207605667 562949953421312 1600000000057 114000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz343) (@HMul.hMul Real Real Real qz0 qz68 (Real.log (Enclosure.sfrac Bool.false 13270708100 16000000))) Bool.false 30267448354014383 9007199254740992 800000000513 114000000000000000 (Enclosure.clog_re_eq 5000 115090 4000 13270708100 16000000 rfl rfl rfl) (ep280 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz343) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz344)) Bool.false 859839207605667 562949953421312 1600000000057 114000000000000000 (Enclosure.clog_im_eq 5000 115090 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz341 qz344)) (@HSub.hSub Real Real Real qz314 qz69 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz344 qz341))) Bool.false 859839207605667 562949953421312 1600000000057 114000000000000000 (BSN.arctan_recip 115090 5000 rfl rfl) ep282)))) rfl rfl

noncomputable def ep284 := @ep172 373555200000000000000000 Bool.false 30263376725017775 4503599627370496 800000000513 57000000000000000 Bool.false 869614553171363 281474976710656 1600000000057 57000000000000000 Bool.true ep173 40637558024882755859 900719925474099200 41239171665565934999 93388800000000000000000 Bool.false ep174 29180755228753940953 432345564227567616 31697618586131038113 124518400000000000000000 (@ep175 900719925474099200 13309483888241811933 31129600000000000000000 Bool.false 30516483182425154521 432345564227567616 84607095758019559139 373555200000000000000000 (BSN.logGammaStirling_unfold 1 qz56) (ep258 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep259 1600000000057 57000000000000000 (BSN.log_sum_c_eq qz17 2) (ep260 (BSN.log_sum_c_succ qz17 1 2 rfl) (ep283 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz94 := (@HDiv.hDiv Real Real Real qz266 qz276 (2 : Real))

noncomputable def ep285 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log Real.pi) 57545 2000 0 1 75021 65536 1 65536 863416689 26214400 11509 26214400 (@Enclosure.Real.IsNear.of_eq qz94 (Enclosure.sfrac Bool.false 57545 2000) Bool.false 57545 2000 0 1 (BSN.t_half_eq qz17 Bool.false 57545 1000 qz18) (Enclosure.Real.IsNear.const Bool.false 57545 2000)) EMRow13.d5 rfl

noncomputable def ep286 := @ep169 11509 26214400 ep170 373517622279590641201 10808639105689190400 86365368586131038113 124518400000000000000000 (@ep171 31697618586131038113 124518400000000000000000 (ep284 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep285 rfl rfl

noncomputable def ep287 := nat_lit 127254341953890948240996398458388897521509147394011069735960924013203619840

noncomputable def ep288 := nat_lit 255550425901093362390410389747241401050481368941796840648927831958552576

noncomputable def ep289 := nat_lit 332871432999207856139691807712380150287966035244123225852180346401886109696

noncomputable def ep290 := BSN.sin_dyadic_bound_f 843207724 536870912 3 2 262144 71320 ep287 ep90 ep288 ep289 ep92 ep288 262143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 843207724) qz278 0 2 ep287 ep90 ep288 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 843207724) qz279 0 2 ep289 ep92 ep288 rfl rfl rfl rfl) rfl rfl

noncomputable def ep291 := @ep167 262144 Bool.true 262143 262144 1 35625 (@ep168 4529497 131072 183 262144 ep286 rfl) (Enclosure.sfrac_false_div 4529497 131072) (BSN.cos_reduce1 qz315 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29667734338063170535424) qz28) 226375608064910080 72057594037927936 Bool.false 262143 262144 5 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q1 4529497 131072 226375608064910080 72057594037927936 5 29667734338063170535424 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 262143 262144 29667734338063170535424 18889465931478580854784 843207724 536870912 71320 71250 (ep290 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep292 := nat_lit 2134175046629868180796207

noncomputable def ep293 := nat_lit 243222611245651722240000000

noncomputable abbrev qz95 := qz270

noncomputable abbrev qz96 := qz271

noncomputable abbrev qz346 := (@HPow.hPow Complex Complex Complex qz465 (@Nat.cast Complex Complex.instNatCast 15) qz466)

noncomputable abbrev qz97 := qz346

noncomputable abbrev qz347 := (@Nat.cast Complex Complex.instNatCast 15)

noncomputable abbrev qz98 := (@HAdd.hAdd Complex Complex Complex qz269 (@HDiv.hDiv Complex Complex Complex qz319 qz347 (@HSub.hSub Complex Complex Complex qz311 qz268 (1 : Complex))) qz318)

noncomputable abbrev qz99 := (@instHSub Nat instSubNat)

noncomputable abbrev qz348 := qz477

noncomputable abbrev qz100 := qz348

noncomputable abbrev qz101 := qz347

noncomputable def ep294 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz6 1 15) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 15, @HPow.hPow Complex Complex Complex qz95 (@Nat.cast Complex Complex.instNatCast n) qz96) (@HMul.hMul Complex Complex Complex qz46 qz97 (@HAdd.hAdd Complex Complex Complex qz5 qz98 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) Bool.false 39001438368210071272229 21847364378556786278400 ep164

noncomputable def ep295 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 15, @HPow.hPow Complex Complex Complex qz95 (@Nat.cast Complex Complex.instNatCast n) qz96) (@HMul.hMul Complex Complex Complex qz46 qz97 (@HAdd.hAdd Complex Complex Complex qz5 qz98 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) Bool.false 120829558825 68719476736 20899977524569 2448131358720000

noncomputable def ep296 := nat_lit 2680158436614749794752842688364544

noncomputable def ep297 := nat_lit 32316894490676603948264893448192

noncomputable def ep298 := @ep295 Bool.true 9735612639 68719476736 20893335100819 2448131358720000 Bool.false 587184873652775692229 21847364378556786278400 930537414379178210114437 ep165 Bool.false 4172460767853730644253 32771046567835179417600 58415711759617951291957 ep293 Bool.false ep296 39001438368210071272229 21847364378556786278400 ep164 ep165 Bool.true ep297 470272709072401688147 32771046567835179417600

noncomputable def ep299 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 15, @HPow.hPow Complex Complex Complex qz95 (@Nat.cast Complex Complex.instNatCast n) qz96) (BSN.headSumC qz6 15) Bool.false 120829558825 68719476736 20899977524569 2448131358720000 Bool.true 9735612639 68719476736 20893335100819

noncomputable abbrev qz102 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 14) qz271)

noncomputable def ep300 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 15) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 14) qz102) Bool.false 120829558825 68719476736 20899977524569 2448131358720000 Bool.true 9735612639 68719476736 20893335100819 2448131358720000

noncomputable def ep301 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 14) qz102 Bool.false 27993584713 17179869184 2477352741377 306016419840000 Bool.false 6354596621 68719476736 19808500620391 2448131358720000 Bool.false

noncomputable abbrev qz103 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 13) qz271)

noncomputable def ep302 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 14) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 13) qz103) Bool.false 27993584713 17179869184 2477352741377 306016419840000 Bool.false 6354596621 68719476736 19808500620391 2448131358720000

noncomputable def ep303 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 13) qz103 Bool.false 65502290891 34359738368 1557468625571 204010946560000 Bool.false 3701683123 34359738368 1557342750571 204010946560000 Bool.true

noncomputable abbrev qz104 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 12) qz271)

noncomputable def ep304 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 13) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 12) qz104) Bool.false 65502290891 34359738368 1557468625571 204010946560000 Bool.false 3701683123 34359738368 1557342750571 204010946560000

noncomputable def ep305 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 12) qz104 Bool.false 64992392741 34359738368 4380880869377 612032839680000 Bool.true 12408121729 68719476736 17513166541883 2448131358720000 Bool.false

noncomputable abbrev qz105 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 11) qz271)

noncomputable def ep306 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 11) qz105) Bool.false 64992392741 34359738368 4380880869377 612032839680000 Bool.true 12408121729 68719476736 17513166541883 2448131358720000

noncomputable def ep307 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 11) qz105 Bool.false 109875762141 68719476736 5433280246291 816043786240000 Bool.true 17400699203 68719476736 5432099063791 816043786240000 Bool.false

noncomputable abbrev qz106 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 10) qz271)

noncomputable def ep308 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 10) qz106) Bool.false 109875762141 68719476736 5433280246291 816043786240000 Bool.true 17400699203 68719476736 5432099063791 816043786240000

noncomputable def ep309 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 10) qz106 Bool.false 91406476335 68719476736 15015044815561 2448131358720000 Bool.true 5950136593 68719476736 15014517565561 2448131358720000 Bool.false

noncomputable abbrev qz107 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 9) qz271)

noncomputable def ep310 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 10) (@HAdd.hAdd Complex Complex Complex qz5 qz4 qz107) Bool.false 91406476335 68719476736 15015044815561 2448131358720000 Bool.true 5950136593 68719476736 15014517565561 2448131358720000

noncomputable def ep311 := @Enclosure.Complex.IsNear.addLitP qz4 qz107 Bool.false 75050675517 68719476736 4555188274101 816043786240000 Bool.false 10086898337 68719476736 4555055844101 816043786240000 Bool.false

noncomputable abbrev qz349 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz108 := (@Inv.inv Real Real.instInv (Real.sqrt qz349))

noncomputable abbrev qz109 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep312 := @Enclosure.Complex.IsNear.of_eq qz107 (Complex.mk (@HMul.hMul Real Real Real qz0 qz108 (Real.cos qz109)) (@HMul.hMul Real Real Real qz0 qz108 (@Neg.neg Real Real.instNeg (Real.sin qz109)))) Bool.false 8177900409 34359738368 674739996629 1224065679360000 Bool.true 8018517465 34359738368 674675016629 1224065679360000 (BSN.cpow_neg_s_mk qz17 57545 1000 9 qz18 rfl)

noncomputable abbrev qz350 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9) qz19)

noncomputable def ep313 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz349) 786433 262144 1 262144 43690 43691 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz349) (Real.sqrt qz350) Bool.false 786433 262144 1 262144 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz350) Bool.false 786433 262144 1 262144 786433 262144 1 262144 (BSN.sqrt_enclosure 9 1 393216 393217 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep314 := BSN.log_dyadic_bound 1 17 2 1 867 131072 35625 1 1 15438 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz110 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep315 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz110 57545 1000 0 1 9895417793173221 4503599627370496 1600000000171 57000000000000000 113886363381630600489 900719925474099200 18414400001968039 11400000000000000000 qz21 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz350) Bool.false 10376097607894403383296 4722366482869645213696 1000000000106875 35625000000000000000 9895417793173221 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 15438 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep314 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep316 := nat_lit 30056104767156228710518893635928241

noncomputable def ep317 := BSN.cos_dyadic_bound_f 416373589 536870912 2 1 262144 71320 ep316 ep61 ep316 ep316 ep62 ep316 187178 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 416373589) qz283 0 1 ep316 ep61 ep316 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 416373589) qz284 0 1 ep316 ep62 ep316 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16572647) qz26)

noncomputable def ep318 := @Enclosure.Real.IsNear.cos_image qz109 qz351 Bool.false 16572647 131072 53 32768 Bool.false 187178 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz109 Bool.false 113886363381630600489 900719925474099200 18414400001968039 11400000000000000000 16572647 131072 53 32768 (ep315 rfl) rfl) (Enclosure.sfrac_false_div 16572647 131072) (BSN.cos_reduce0 qz351 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14649843297057069072384) qz28) 226375608064910080 72057594037927936 Bool.false 187178 262144 20 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 16572647 131072 226375608064910080 72057594037927936 20 14649843297057069072384 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 187178 262144 14649843297057069072384 18889465931478580854784 416373589 536870912 71320 71250 (ep317 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep319 := BSN.sin_dyadic_bound_f 416373589 536870912 2 1 262144 71320 ep316 ep57 ep316 ep316 ep58 ep316 183530 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 416373589) qz278 0 1 ep316 ep57 ep316 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 416373589) qz279 0 1 ep316 ep58 ep316 rfl rfl rfl rfl) rfl rfl

noncomputable def ep320 := @Enclosure.Real.IsNear.sin_image qz109 qz351 Bool.false 16572647 131072 53 32768 Bool.false 183530 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz109 Bool.false 113886363381630600489 900719925474099200 18414400001968039 11400000000000000000 16572647 131072 53 32768 (ep315 rfl) rfl) (Enclosure.sfrac_false_div 16572647 131072) (BSN.sin_reduce0 qz351 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14649843297057069072384) qz28) 226375608064910080 72057594037927936 Bool.false 183530 262144 20 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 16572647 131072 226375608064910080 72057594037927936 20 14649843297057069072384 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 183530 262144 14649843297057069072384 18889465931478580854784 416373589 536870912 71320 71250 (ep319 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz352 := (@Enclosure.Real.IsNear.recentre' qz108 Bool.false 87381 262144 1 262144 87381 262144 1 262144 (ep313 rfl rfl) rfl)

noncomputable def ep321 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz108 (Real.cos qz109)) (@HMul.hMul Real Real Real qz0 qz108 (@Neg.neg Real Real.instNeg (Real.sin qz109))) Bool.false 8177900409 34359738368 674739996629 1224065679360000 Bool.true 8018517465 34359738368 674675016629 1224065679360000 (@Enclosure.Real.IsNear.mulLit_ff qz108 (Real.cos qz109) 87381 262144 1 262144 93589 131072 1920893 1167360000 8177900409 34359738368 674739996629 1224065679360000 qz352 (@Enclosure.Real.IsNear.recentre' (Real.cos qz109) Bool.false 187178 262144 1920893 1167360000 93589 131072 1920893 1167360000 (ep318 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz108 (@Neg.neg Real Real.instNeg (Real.sin qz109)) 87381 262144 1 262144 91765 131072 1920893 1167360000 8018517465 34359738368 674675016629 1224065679360000 qz352 (@Enclosure.Real.IsNear.neg (Real.sin qz109) Bool.false 91765 131072 1920893 1167360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz109) Bool.false 183530 262144 1920893 1167360000 91765 131072 1920893 1167360000 (ep320 rfl rfl) rfl)) rfl)

noncomputable def ep322 := @ep311 8177900409 34359738368 674739996629 1224065679360000 Bool.true 8018517465 34359738368 674675016629 1224065679360000 Bool.false 3140702612011383521280 91406476335 68719476736 15015044815561 2448131358720000 Bool.true 204445136589342900224 5950136593 68719476736 15014517565561 2448131358720000 EMRow13.d6 (ep312 ep321) rfl rfl

noncomputable abbrev qz353 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz111 := (@Inv.inv Real Real.instInv (Real.sqrt qz353))

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep323 := @Enclosure.Complex.IsNear.of_eq qz106 (Complex.mk (@HMul.hMul Real Real Real qz0 qz111 (Real.cos qz112)) (@HMul.hMul Real Real Real qz0 qz111 (@Neg.neg Real Real.instNeg (Real.sin qz112)))) Bool.false 9234642903 34359738368 80299745207 153008209920000 Bool.true 5725281305 34359738368 320444906453 612032839680000 (BSN.cpow_neg_s_mk qz17 57545 1000 10 qz18 rfl)

noncomputable abbrev qz354 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10) qz19)

noncomputable def ep324 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz353) 828973 262144 1 262144 41448 41449 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz353) (Real.sqrt qz354) Bool.false 828973 262144 1 262144 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz354) Bool.false 828973 262144 1 262144 828973 262144 1 262144 (BSN.sqrt_enclosure 10 1 414486 414487 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep325 := BSN.log_dyadic_bound 2 18 3 2 1574640 131072 35625 6528 48 29247 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz113 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep326 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz113 57545 1000 0 1 10369891420296933 4503599627370496 1600000000171 57000000000000000 119347080356197401897 900719925474099200 18414400001968039 11400000000000000000 qz21 (BSN.isNear_log_sfrac 10 1 10369891420296933 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz354) Bool.false 10873619265929276817408 4722366482869645213696 1000000000106875 35625000000000000000 10369891420296933 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 29247 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep325 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep327 := nat_lit 7881225001869997787928644443631761

noncomputable def ep328 := BSN.cos_dyadic_bound_f 297953459 536870912 2 1 262144 71320 ep327 ep61 ep327 ep327 ep62 ep327 222798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 297953459) qz283 0 1 ep327 ep61 ep327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 297953459) qz284 0 1 ep327 ep62 ep327 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 34734571) qz31)

noncomputable def ep329 := @Enclosure.Real.IsNear.cos_image qz112 qz355 Bool.false 34734571 262144 425 262144 Bool.false 222798 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz112 Bool.false 119347080356197401897 900719925474099200 18414400001968039 11400000000000000000 34734571 262144 425 262144 (ep326 rfl) rfl) (Enclosure.sfrac_false_div 34734571 262144) (BSN.cos_reduce0 qz355 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20966610751474978783232) qz33) 226375608064910080 72057594037927936 Bool.false 222798 262144 21 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 34734571 262144 226375608064910080 72057594037927936 21 20966610751474978783232 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 222798 262144 20966610751474978783232 37778931862957161709568 297953459 536870912 71320 71250 (ep328 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep330 := BSN.sin_dyadic_bound_f 297953459 536870912 2 1 262144 71320 ep327 ep57 ep327 ep327 ep58 ep327 138130 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 297953459) qz278 0 1 ep327 ep57 ep327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 297953459) qz279 0 1 ep327 ep58 ep327 rfl rfl rfl rfl) rfl rfl

noncomputable def ep331 := @Enclosure.Real.IsNear.sin_image qz112 qz355 Bool.false 34734571 262144 425 262144 Bool.false 138130 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz112 Bool.false 119347080356197401897 900719925474099200 18414400001968039 11400000000000000000 34734571 262144 425 262144 (ep326 rfl) rfl) (Enclosure.sfrac_false_div 34734571 262144) (BSN.sin_reduce0 qz355 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20966610751474978783232) qz33) 226375608064910080 72057594037927936 Bool.false 138130 262144 21 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 34734571 262144 226375608064910080 72057594037927936 21 20966610751474978783232 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 138130 262144 20966610751474978783232 37778931862957161709568 297953459 536870912 71320 71250 (ep330 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz356 := (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 82897 262144 1 262144 82897 262144 1 262144 (ep324 rfl rfl) rfl)

noncomputable def ep332 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz111 (Real.cos qz112)) (@HMul.hMul Real Real Real qz0 qz111 (@Neg.neg Real Real.instNeg (Real.sin qz112))) Bool.false 9234642903 34359738368 80299745207 153008209920000 Bool.true 5725281305 34359738368 320444906453 612032839680000 (@Enclosure.Real.IsNear.mulLit_ff qz111 (Real.cos qz112) 82897 262144 1 262144 111399 131072 15402769 9338880000 9234642903 34359738368 80299745207 153008209920000 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz112) Bool.false 222798 262144 15402769 9338880000 111399 131072 15402769 9338880000 (ep329 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz111 (@Neg.neg Real Real.instNeg (Real.sin qz112)) 82897 262144 1 262144 69065 131072 15402769 9338880000 5725281305 34359738368 320444906453 612032839680000 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz112) Bool.false 69065 131072 15402769 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz112) Bool.false 138130 262144 15402769 9338880000 69065 131072 15402769 9338880000 (ep331 rfl rfl) rfl)) rfl)

noncomputable def ep333 := @ep309 9234642903 34359738368 80299745207 153008209920000 Bool.true 5725281305 34359738368 320444906453 612032839680000 Bool.false 3775302440149359525888 109875762141 68719476736 5433280246291 816043786240000 Bool.true 597883472035346120704 17400699203 68719476736 5432099063791 816043786240000 (ep310 (BSN.head_sum_c_succ qz6 9 10 rfl rfl) (ep322 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep323 ep332) rfl rfl

noncomputable abbrev qz357 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz114 := (@Inv.inv Real Real.instInv (Real.sqrt qz357))

noncomputable abbrev qz115 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep334 := @Enclosure.Complex.IsNear.of_eq qz105 (Complex.mk (@HMul.hMul Real Real Real qz0 qz114 (Real.cos qz115)) (@HMul.hMul Real Real Real qz0 qz114 (@Neg.neg Real Real.instNeg (Real.sin qz115)))) Bool.false 20109023341 68719476736 12880870933 25769803776000 Bool.false 2496288737 34359738368 6404575529 12884901888000 (BSN.cpow_neg_s_mk qz17 57545 1000 11 qz18 rfl)

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11) qz19)

noncomputable def ep335 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz357) 869433 262144 1 262144 39519 39520 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz357) (Real.sqrt qz358) Bool.false 869433 262144 1 262144 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz358) Bool.false 869433 262144 1 262144 869433 262144 1 262144 (BSN.sqrt_enclosure 11 1 434716 434717 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep336 := BSN.log_dyadic_bound 3 19 3 2 1954815 131072 35625 16488 243 41740 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 19) 0 2 16488 1954815 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz116 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep337 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz116 57545 1000 0 1 10799147631728357 4503599627370496 1600000000171 57000000000000000 124287390093561660713 900719925474099200 18414400001968039 11400000000000000000 qz21 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz358) Bool.false 11323727027087193669632 4722366482869645213696 1000000000106875 35625000000000000000 10799147631728357 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 41740 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep336 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep338 := nat_lit 64870444318161960128684768534958664218029271773582238547051106531072412865

noncomputable def ep339 := nat_lit 66539538243354448119275713232811898330467241908471151770368191746936001

noncomputable def ep340 := nat_lit 169791052057077797897219375960610044164208288634387385758458016223313661121

noncomputable def ep341 := BSN.sin_dyadic_bound_f 712664249 536870912 3 2 262144 71320 ep338 ep90 ep339 ep340 ep92 ep339 254419 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 712664249) qz278 0 2 ep338 ep90 ep339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 712664249) qz279 0 2 ep340 ep92 ep339 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 36172391) qz31)

noncomputable def ep342 := @Enclosure.Real.IsNear.cos_image qz115 qz359 Bool.false 36172391 262144 53 32768 Bool.false 254419 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz115 Bool.false 124287390093561660713 900719925474099200 18414400001968039 11400000000000000000 36172391 262144 53 32768 (ep337 rfl) rfl) (Enclosure.sfrac_false_div 36172391 262144) (BSN.cos_reduce3 qz359 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 50149288268998704627712) qz33) 226375608064910080 72057594037927936 Bool.false 254419 262144 21 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q3 36172391 262144 226375608064910080 72057594037927936 21 50149288268998704627712 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 254419 262144 50149288268998704627712 37778931862957161709568 712664249 536870912 71320 71250 (ep341 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep343 := nat_lit 36068708860420357603988993947524952075940914203949453038037445046927756481

noncomputable def ep344 := nat_lit 108073047504774363915728430416109232431161808128031416810571598757289397441

noncomputable def ep345 := BSN.cos_dyadic_bound_f 712664249 536870912 3 2 262144 71320 ep343 ep83 ep339 ep344 ep86 ep339 63166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 712664249) qz283 0 2 ep343 ep83 ep339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 712664249) qz284 0 2 ep344 ep86 ep339 rfl rfl rfl rfl) rfl rfl

noncomputable def ep346 := @Enclosure.Real.IsNear.sin_image qz115 qz359 Bool.false 36172391 262144 53 32768 Bool.true 63166 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz115 Bool.false 124287390093561660713 900719925474099200 18414400001968039 11400000000000000000 36172391 262144 53 32768 (ep337 rfl) rfl) (Enclosure.sfrac_false_div 36172391 262144) (BSN.sin_reduce3 qz359 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 50149288268998704627712) qz33) 226375608064910080 72057594037927936 Bool.false 63166 262144 21 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q3 36172391 262144 226375608064910080 72057594037927936 21 50149288268998704627712 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 63166 262144 50149288268998704627712 37778931862957161709568 712664249 536870912 71320 71250 (ep345 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz360 := (@Enclosure.Real.IsNear.recentre' qz114 Bool.false 79039 262144 1 262144 79039 262144 1 262144 (ep335 rfl rfl) rfl)

noncomputable def ep347 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz114 (Real.cos qz115)) (@HMul.hMul Real Real Real qz0 qz114 (@Neg.neg Real Real.instNeg (Real.sin qz115))) Bool.false 20109023341 68719476736 12880870933 25769803776000 Bool.false 2496288737 34359738368 6404575529 12884901888000 (@Enclosure.Real.IsNear.mulLit_ff qz114 (Real.cos qz115) 79039 262144 1 262144 254419 262144 1920893 1167360000 20109023341 68719476736 12880870933 25769803776000 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz115) Bool.false 254419 262144 1920893 1167360000 254419 262144 1920893 1167360000 (ep342 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz114 (@Neg.neg Real Real.instNeg (Real.sin qz115)) 79039 262144 1 262144 31583 131072 1920893 1167360000 2496288737 34359738368 6404575529 12884901888000 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz115) Bool.true 31583 131072 1920893 1167360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz115) Bool.true 63166 262144 1920893 1167360000 31583 131072 1920893 1167360000 (ep346 rfl rfl) rfl)) rfl)

noncomputable def ep348 := @ep307 20109023341 68719476736 12880870933 25769803776000 Bool.false 2496288737 34359738368 6404575529 12884901888000 Bool.false 8932486441964249546752 64992392741 34359738368 4380880869377 612032839680000 Bool.true 426339816246735798272 12408121729 68719476736 17513166541883 2448131358720000 (ep308 (BSN.head_sum_c_succ qz6 10 11 rfl rfl) (ep333 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep334 ep347) rfl rfl

noncomputable abbrev qz361 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz117 := (@Inv.inv Real Real.instInv (Real.sqrt qz361))

noncomputable abbrev qz118 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep349 := @Enclosure.Complex.IsNear.of_eq qz104 (Complex.mk (@HMul.hMul Real Real Real qz0 qz117 (Real.cos qz118)) (@HMul.hMul Real Real Real qz0 qz117 (@Neg.neg Real Real.instNeg (Real.sin qz118)))) Bool.false 254949075 17179869184 36440625917 76504104960000 Bool.false 19811487975 68719476736 1174946464969 2448131358720000 (BSN.cpow_neg_s_mk qz17 57545 1000 12 qz18 rfl)

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12) qz19)

noncomputable def ep350 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz361) 908093 262144 1 262144 37837 37838 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz361) (Real.sqrt qz362) Bool.false 908093 262144 1 262144 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz362) Bool.false 908093 262144 1 262144 908093 262144 1 262144 (BSN.sqrt_enclosure 12 1 454046 454047 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep351 := BSN.log_dyadic_bound 4 20 4 3 6720000000 131072 35625 91811840 61440 53145 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz119 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep352 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz119 57545 1000 0 1 11191020447815397 4503599627370496 1600000000171 57000000000000000 128797454333907404073 900719925474099200 18414400001968039 11400000000000000000 qz21 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz362) Bool.false 11734635457088477724672 4722366482869645213696 1000000000106875 35625000000000000000 11191020447815397 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 53145 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep351 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep353 := BSN.sin_dyadic_bound_f 27611671 536870912 1 0 262144 71320 0 1 1 0 1 1 13476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 27611671) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 27611671) qz279 0 0 rfl) rfl rfl

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 585703) (@Nat.cast Real Real.instNatCast 4096))

noncomputable def ep354 := @Enclosure.Real.IsNear.cos_image qz118 qz363 Bool.false 585703 4096 425 262144 Bool.false 13476 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 128797454333907404073 900719925474099200 18414400001968039 11400000000000000000 585703 4096 425 262144 (ep352 rfl) rfl) (Enclosure.sfrac_false_div 585703 4096) (BSN.cos_reduce3 qz363 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 30359353910688219136) (@Nat.cast Real Real.instNatCast 590295810358705651712)) 226375608064910080 72057594037927936 Bool.false 13476 262144 22 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q3 585703 4096 226375608064910080 72057594037927936 22 30359353910688219136 590295810358705651712 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13476 262144 30359353910688219136 590295810358705651712 27611671 536870912 71320 71250 (ep353 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep355 := BSN.cos_dyadic_bound_f 27611671 536870912 1 0 262144 71320 0 1 1 0 1 1 261797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 27611671) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 27611671) qz284 0 0 rfl) rfl rfl

noncomputable def ep356 := @Enclosure.Real.IsNear.sin_image qz118 qz363 Bool.false 585703 4096 425 262144 Bool.true 261797 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 128797454333907404073 900719925474099200 18414400001968039 11400000000000000000 585703 4096 425 262144 (ep352 rfl) rfl) (Enclosure.sfrac_false_div 585703 4096) (BSN.sin_reduce3 qz363 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 30359353910688219136) (@Nat.cast Real Real.instNatCast 590295810358705651712)) 226375608064910080 72057594037927936 Bool.false 261797 262144 22 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q3 585703 4096 226375608064910080 72057594037927936 22 30359353910688219136 590295810358705651712 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 261797 262144 30359353910688219136 590295810358705651712 27611671 536870912 71320 71250 (ep355 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz364 := (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 75675 262144 1 262144 75675 262144 1 262144 (ep350 rfl rfl) rfl)

noncomputable def ep357 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz117 (Real.cos qz118)) (@HMul.hMul Real Real Real qz0 qz117 (@Neg.neg Real Real.instNeg (Real.sin qz118))) Bool.false 254949075 17179869184 36440625917 76504104960000 Bool.false 19811487975 68719476736 1174946464969 2448131358720000 (@Enclosure.Real.IsNear.mulLit_ff qz117 (Real.cos qz118) 75675 262144 1 262144 3369 65536 15402769 9338880000 254949075 17179869184 36440625917 76504104960000 qz364 (@Enclosure.Real.IsNear.recentre' (Real.cos qz118) Bool.false 13476 262144 15402769 9338880000 3369 65536 15402769 9338880000 (ep354 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz117 (@Neg.neg Real Real.instNeg (Real.sin qz118)) 75675 262144 1 262144 261797 262144 15402769 9338880000 19811487975 68719476736 1174946464969 2448131358720000 qz364 (@Enclosure.Real.IsNear.neg (Real.sin qz118) Bool.true 261797 262144 15402769 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz118) Bool.true 261797 262144 15402769 9338880000 261797 262144 15402769 9338880000 (ep356 rfl rfl) rfl)) rfl)

noncomputable def ep358 := @ep305 254949075 17179869184 36440625917 76504104960000 Bool.false 19811487975 68719476736 1174946464969 2448131358720000 Bool.false 1125320788759694802944 65502290891 34359738368 1557468625571 204010946560000 Bool.false 508755454510084653056 3701683123 34359738368 1557342750571 204010946560000 (ep306 (BSN.head_sum_c_succ qz6 11 12 rfl rfl) (ep348 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep349 ep357) rfl rfl

noncomputable abbrev qz365 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz120 := (@Inv.inv Real Real.instInv (Real.sqrt qz365))

noncomputable abbrev qz121 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep359 := @Enclosure.Complex.IsNear.of_eq qz103 (Complex.mk (@HMul.hMul Real Real Real qz0 qz120 (Real.cos qz121)) (@HMul.hMul Real Real Real qz0 qz120 (@Neg.neg Real Real.instNeg (Real.sin qz121)))) Bool.true 9515121465 34359738368 282299606041 612032839680000 Bool.true 1048769625 68719476736 1120387613539 2448131358720000 (BSN.cpow_neg_s_mk qz17 57545 1000 13 qz18 rfl)

noncomputable abbrev qz366 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13) qz19)

noncomputable def ep360 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz365) 945173 262144 1 262144 36352 36353 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz365) (Real.sqrt qz366) Bool.false 945173 262144 1 262144 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz366) Bool.false 945173 262144 1 262144 945173 262144 1 262144 (BSN.sqrt_enclosure 13 1 472586 472587 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep361 := BSN.log_dyadic_bound 5 21 4 3 9005442705 131072 35625 176193375 234375 63636 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5) (BSN.artanhQ 21) 0 3 176193375 9005442705 234375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz122 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep362 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz122 57545 1000 0 1 11551488463034085 4503599627370496 1600000000171 57000000000000000 26589216144211856853 180143985094819840 18414400001968039 11400000000000000000 qz21 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz366) Bool.false 12112613566614428712960 4722366482869645213696 1000000000106875 35625000000000000000 11551488463034085 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 63636 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep361 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep363 := nat_lit 110355660558625152444679619582899567669907504735712934762845716012859040000

noncomputable def ep364 := nat_lit 192287865863812335308551655667683211028998980127215746303288032100000000

noncomputable def ep365 := nat_lit 288715406823095893574137539084132142508091752149518384599152504172183200000

noncomputable def ep366 := BSN.sin_dyadic_bound_f 813755590 536870912 3 2 262144 71320 ep363 ep90 ep364 ep365 ep92 ep364 261746 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 813755590) qz278 0 2 ep363 ep90 ep364 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 813755590) qz279 0 2 ep365 ep92 ep364 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 38692401) qz31)

noncomputable def ep367 := @Enclosure.Real.IsNear.cos_image qz121 qz367 Bool.false 38692401 262144 425 262144 Bool.true 261746 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 26589216144211856853 180143985094819840 18414400001968039 11400000000000000000 38692401 262144 425 262144 (ep362 rfl) rfl) (Enclosure.sfrac_false_div 38692401 262144) (BSN.cos_reduce1 qz367 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 57262958968629532557312) qz33) 226375608064910080 72057594037927936 Bool.false 261746 262144 23 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q1 38692401 262144 226375608064910080 72057594037927936 23 57262958968629532557312 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 261746 262144 57262958968629532557312 37778931862957161709568 813755590 536870912 71320 71250 (ep366 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep368 := nat_lit 61394161584064556840514700504129841243739279955452615199937970243632800000

noncomputable def ep369 := nat_lit 183797909020466045850926998201054157309159841906103414107207334666698400000

noncomputable def ep370 := BSN.cos_dyadic_bound_f 813755590 536870912 3 2 262144 71320 ep368 ep83 ep364 ep369 ep86 ep364 14425 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 813755590) qz283 0 2 ep368 ep83 ep364 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 813755590) qz284 0 2 ep369 ep86 ep364 rfl rfl rfl rfl) rfl rfl

noncomputable def ep371 := @Enclosure.Real.IsNear.sin_image qz121 qz367 Bool.false 38692401 262144 425 262144 Bool.false 14425 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 26589216144211856853 180143985094819840 18414400001968039 11400000000000000000 38692401 262144 425 262144 (ep362 rfl) rfl) (Enclosure.sfrac_false_div 38692401 262144) (BSN.sin_reduce1 qz367 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 57262958968629532557312) qz33) 226375608064910080 72057594037927936 Bool.false 14425 262144 23 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q1 38692401 262144 226375608064910080 72057594037927936 23 57262958968629532557312 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 14425 262144 57262958968629532557312 37778931862957161709568 813755590 536870912 71320 71250 (ep370 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz368 := (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 72705 262144 1 262144 72705 262144 1 262144 (ep360 rfl rfl) rfl)

noncomputable def ep372 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz120 (Real.cos qz121)) (@HMul.hMul Real Real Real qz0 qz120 (@Neg.neg Real Real.instNeg (Real.sin qz121))) Bool.true 9515121465 34359738368 282299606041 612032839680000 Bool.true 1048769625 68719476736 1120387613539 2448131358720000 (@Enclosure.Real.IsNear.mulLit_ft qz120 (Real.cos qz121) 72705 262144 1 262144 130873 131072 15402769 9338880000 9515121465 34359738368 282299606041 612032839680000 qz368 (@Enclosure.Real.IsNear.recentre' (Real.cos qz121) Bool.true 261746 262144 15402769 9338880000 130873 131072 15402769 9338880000 (ep367 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz120 (@Neg.neg Real Real.instNeg (Real.sin qz121)) 72705 262144 1 262144 14425 262144 15402769 9338880000 1048769625 68719476736 1120387613539 2448131358720000 qz368 (@Enclosure.Real.IsNear.neg (Real.sin qz121) Bool.false 14425 262144 15402769 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz121) Bool.false 14425 262144 15402769 9338880000 14425 262144 15402769 9338880000 (ep371 rfl rfl) rfl)) rfl)

noncomputable def ep373 := @ep303 9515121465 34359738368 282299606041 612032839680000 Bool.true 1048769625 68719476736 1120387613539 2448131358720000 Bool.false 1923704493442248736768 27993584713 17179869184 2477352741377 306016419840000 Bool.false 218342277331736854528 6354596621 68719476736 19808500620391 2448131358720000 (ep304 (BSN.head_sum_c_succ qz6 12 13 rfl rfl) (ep358 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep359 ep372) rfl rfl

noncomputable abbrev qz369 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz123 := (@Inv.inv Real Real.instInv (Real.sqrt qz369))

noncomputable abbrev qz124 := (@HMul.hMul Real Real Real qz263 qz276 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep374 := @Enclosure.Complex.IsNear.of_eq qz102 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124)))) Bool.false 8855219973 68719476736 360385197851 816043786240000 Bool.true 4022552315 17179869184 90402873369 204010946560000 (BSN.cpow_neg_s_mk qz17 57545 1000 14 qz18 rfl)

noncomputable abbrev qz370 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14) qz19)

noncomputable def ep375 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz369) 980853 262144 1 262144 35030 35031 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz369) (Real.sqrt qz370) Bool.false 980853 262144 1 262144 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz370) Bool.false 980853 262144 1 262144 980853 262144 1 262144 (BSN.sqrt_enclosure 14 1 490426 490427 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep376 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 131072 35625 1346332575744 176359680 73349 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz125 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable def ep377 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz125 57545 1000 0 1 11885224601802469 4503599627370496 1600000000171 57000000000000000 136787049942144615721 900719925474099200 18414400001968039 11400000000000000000 qz21 (BSN.isNear_log_sfrac 14 1 11885224601802469 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz370) Bool.false 12462561272059625734144 4722366482869645213696 1000000000106875 35625000000000000000 11885224601802469 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 73349 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep376 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep378 := nat_lit 15079117083623555838557288927979107613093867420301618911646507741388800000

noncomputable def ep379 := nat_lit 11654742211227284133985892623617312047882924996024363034451993600000000

noncomputable def ep380 := nat_lit 45214041766448212947403894998690088215185836410912808008870619236966400000

noncomputable def ep381 := BSN.cos_dyadic_bound_f 573208780 536870912 3 2 262144 71320 ep378 ep83 ep379 ep380 ep86 ep379 126393 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 573208780) qz283 0 2 ep378 ep83 ep379 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 573208780) qz284 0 2 ep380 ep86 ep379 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz371 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39810271) qz31)

noncomputable def ep382 := @Enclosure.Real.IsNear.cos_image qz124 qz371 Bool.false 39810271 262144 53 32768 Bool.false 126393 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 136787049942144615721 900719925474099200 18414400001968039 11400000000000000000 39810271 262144 53 32768 (ep377 rfl) rfl) (Enclosure.sfrac_false_div 39810271 262144) (BSN.cos_reduce0 qz371 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 40335982061283172155392) qz33) 226375608064910080 72057594037927936 Bool.false 126393 262144 24 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 39810271 262144 226375608064910080 72057594037927936 24 40335982061283172155392 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 126393 262144 40335982061283172155392 37778931862957161709568 573208780 536870912 71320 71250 (ep381 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep383 := nat_lit 27133086956753418682095931356263499853930655016546094550536152339619840000

noncomputable def ep384 := nat_lit 71043977208869347612129557345013785874121809831436684377919857661747200000

noncomputable def ep385 := BSN.sin_dyadic_bound_f 573208780 536870912 3 2 262144 71320 ep383 ep90 ep379 ep384 ep92 ep379 229660 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 573208780) qz278 0 2 ep383 ep90 ep379 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 573208780) qz279 0 2 ep384 ep92 ep379 rfl rfl rfl rfl) rfl rfl

noncomputable def ep386 := @Enclosure.Real.IsNear.sin_image qz124 qz371 Bool.false 39810271 262144 53 32768 Bool.false 229660 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 136787049942144615721 900719925474099200 18414400001968039 11400000000000000000 39810271 262144 53 32768 (ep377 rfl) rfl) (Enclosure.sfrac_false_div 39810271 262144) (BSN.sin_reduce0 qz371 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 40335982061283172155392) qz33) 226375608064910080 72057594037927936 Bool.false 229660 262144 24 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 39810271 262144 226375608064910080 72057594037927936 24 40335982061283172155392 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 229660 262144 40335982061283172155392 37778931862957161709568 573208780 536870912 71320 71250 (ep385 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz372 := (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 70061 262144 1 262144 70061 262144 1 262144 (ep375 rfl rfl) rfl)

noncomputable def ep387 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124))) Bool.false 8855219973 68719476736 360385197851 816043786240000 Bool.true 4022552315 17179869184 90402873369 204010946560000 (@Enclosure.Real.IsNear.mulLit_ff qz123 (Real.cos qz124) 70061 262144 1 262144 126393 262144 1920893 1167360000 8855219973 68719476736 360385197851 816043786240000 qz372 (@Enclosure.Real.IsNear.recentre' (Real.cos qz124) Bool.false 126393 262144 1920893 1167360000 126393 262144 1920893 1167360000 (ep382 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124)) 70061 262144 1 262144 57415 65536 1920893 1167360000 4022552315 17179869184 90402873369 204010946560000 qz372 (@Enclosure.Real.IsNear.neg (Real.sin qz124) Bool.false 57415 65536 1920893 1167360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz124) Bool.false 229660 262144 1920893 1167360000 57415 65536 1920893 1167360000 (ep386 rfl rfl) rfl)) rfl)

noncomputable def ep388 := @ep301 8855219973 68719476736 360385197851 816043786240000 Bool.true 4022552315 17179869184 90402873369 204010946560000 Bool.false 2075836014173932748800 120829558825 68719476736 20899977524569 2448131358720000 Bool.true 167256551564117016576 9735612639 68719476736 20893335100819 2448131358720000 (ep302 (BSN.head_sum_c_succ qz6 13 14 rfl rfl) (ep373 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep374 ep387) rfl rfl

noncomputable def ep389 := @Enclosure.Complex.IsNear.mul qz97 (@HAdd.hAdd Complex Complex Complex qz5 qz98 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 587184873652775692229 21847364378556786278400 930537414379178210114437 ep165 Bool.false

noncomputable abbrev qz126 := (Complex.re qz346)

noncomputable abbrev qz127 := (Complex.im qz346)

noncomputable def ep390 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz126 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz98 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz127 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz98 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 13541798183614812827 327710465678351794176 2079622238702916022727

noncomputable def ep391 := nat_lit 9728904449826068889600000

noncomputable def ep392 := nat_lit 4213721789431429559045928572650128408576

noncomputable def ep393 := @Enclosure.Real.IsNear.mulLit_ff qz126 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz98 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 2836746035 34359738368 87128165107 204010946560000 23868541661

noncomputable abbrev qz373 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz128 := (@Inv.inv Real Real.instInv (Real.sqrt qz373))

noncomputable abbrev qz374 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz469 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable abbrev qz129 := (Real.cos qz374)

noncomputable abbrev qz130 := (@Neg.neg Real Real.instNeg (Real.sin qz374))

noncomputable def ep394 := @Enclosure.Complex.IsNear.of_eq qz97 (Complex.mk (@HMul.hMul Real Real Real qz0 qz128 qz129) (@HMul.hMul Real Real Real qz0 qz128 qz130)) Bool.false 2836746035 34359738368 87128165107 204010946560000 Bool.false 16811667985 68719476736 350466798553 816043786240000 (BSN.cpow_neg_s_mk qz17 57545 1000 15 qz18 rfl)

noncomputable abbrev qz375 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15) qz19)

noncomputable def ep395 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz373) 1015279 262144 1 262144 33842 33843 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz373) (Real.sqrt qz375) Bool.false 1015279 262144 1 262144 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz375) Bool.false 1015279 262144 1 262144 1015279 262144 1 262144 (BSN.sqrt_enclosure 15 1 507639 507640 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep396 := BSN.log_dyadic_bound 7 23 5 4 74003881090545 131072 35625 2420929921704 605304105 82392 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 7) (BSN.artanhQ 23) 0 4 2420929921704 74003881090545 605304105 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz376 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz131 := qz376

noncomputable abbrev qz377 := (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15) qz19))

noncomputable def ep397 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz131 57545 1000 0 1 12195939715864293 4503599627370496 1600000000171 57000000000000000 140363070189882148137 900719925474099200 18414400001968039 11400000000000000000 qz21 (BSN.isNear_log_sfrac 15 1 12195939715864293 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 12788369683502116896768 4722366482869645213696 1000000000106875 35625000000000000000 12195939715864293 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 82392 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep396 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep398 := nat_lit 932256616502534210589135245700625

noncomputable def ep399 := BSN.sin_dyadic_bound_f 174736595 536870912 2 1 262144 71320 ep398 ep57 ep398 ep398 ep58 ep398 83822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 174736595) qz278 0 1 ep398 ep57 ep398 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 174736595) qz279 0 1 ep398 ep58 ep398 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz132 := qz374

noncomputable abbrev qz378 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 40851029) qz31)

noncomputable def ep400 := @Enclosure.Real.IsNear.cos_image qz132 qz378 Bool.false 40851029 262144 425 262144 Bool.false 83822 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 140363070189882148137 900719925474099200 18414400001968039 11400000000000000000 40851029 262144 425 262144 (ep397 rfl) rfl) (Enclosure.sfrac_false_div 40851029 262144) (BSN.cos_reduce3 qz378 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12295994771031413751808) qz33) 226375608064910080 72057594037927936 Bool.false 83822 262144 24 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q3 40851029 262144 226375608064910080 72057594037927936 24 12295994771031413751808 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 83822 262144 12295994771031413751808 37778931862957161709568 174736595 536870912 71320 71250 (ep399 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep401 := BSN.cos_dyadic_bound_f 174736595 536870912 2 1 262144 71320 ep398 ep61 ep398 ep398 ep62 ep398 248381 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 174736595) qz283 0 1 ep398 ep61 ep398 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 174736595) qz284 0 1 ep398 ep62 ep398 rfl rfl rfl rfl) rfl rfl

noncomputable def ep402 := @Enclosure.Real.IsNear.sin_image qz132 qz378 Bool.false 40851029 262144 425 262144 Bool.true 248381 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 140363070189882148137 900719925474099200 18414400001968039 11400000000000000000 40851029 262144 425 262144 (ep397 rfl) rfl) (Enclosure.sfrac_false_div 40851029 262144) (BSN.sin_reduce3 qz378 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12295994771031413751808) qz33) 226375608064910080 72057594037927936 Bool.false 248381 262144 24 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q3 40851029 262144 226375608064910080 72057594037927936 24 12295994771031413751808 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 248381 262144 12295994771031413751808 37778931862957161709568 174736595 536870912 71320 71250 (ep401 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz133 := (Real.sin qz374)

noncomputable abbrev qz379 := (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 67685 262144 1 262144 67685 262144 1 262144 (ep395 rfl rfl) rfl)

noncomputable def ep403 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz128 qz129) (@HMul.hMul Real Real Real qz0 qz128 qz130) Bool.false 2836746035 34359738368 87128165107 204010946560000 Bool.false 16811667985 68719476736 350466798553 816043786240000 (@Enclosure.Real.IsNear.mulLit_ff qz128 qz129 67685 262144 1 262144 41911 131072 15402769 9338880000 2836746035 34359738368 87128165107 204010946560000 qz379 (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 83822 262144 15402769 9338880000 41911 131072 15402769 9338880000 (ep400 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz128 qz130 67685 262144 1 262144 248381 262144 15402769 9338880000 16811667985 68719476736 350466798553 816043786240000 qz379 (@Enclosure.Real.IsNear.neg qz133 Bool.true 248381 262144 15402769 9338880000 (@Enclosure.Real.IsNear.recentre' qz133 Bool.true 248381 262144 15402769 9338880000 248381 262144 15402769 9338880000 (ep402 rfl rfl) rfl)) rfl)

noncomputable def ep404 := @ep393 47688149160 0 1 13541798183614812827 327710465678351794176 2079622238702916022727 ep391 (@Enclosure.Complex.IsNear.re_isNear qz97 Bool.false 2836746035 34359738368 87128165107 204010946560000 Bool.false 16811667985 68719476736 350466798553 816043786240000 (ep394 ep403))

noncomputable def ep405 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz98 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 23868541661 47688149160 0 1 Bool.false

noncomputable def ep406 := @Enclosure.Complex.IsNear.addLitP qz98 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) Bool.false 131867081 264934162 0 1 Bool.true 34527000

noncomputable def ep407 := @ep406 132467081 0 1 Bool.false 1 360 0 1 Bool.false 11509 36000 0 1 Bool.false 47737083322 23868541661 47688149160 0 1 Bool.false 281591635229 281591635229 4768814916000 0 1

noncomputable abbrev qz134 := (@HDiv.hDiv Complex Complex Complex qz319 qz347 (@HSub.hSub Complex Complex Complex qz311 qz268 (1 : Complex)))

noncomputable def ep408 := @Enclosure.Complex.IsNear.addLitP qz134 qz73 Bool.true 30000000 13246708100 0 1 Bool.true 3452700000 13246708100 0 1

noncomputable def ep409 := @Enclosure.Complex.IsNear.of_eq qz134 (Complex.mk (Enclosure.sfrac Bool.true 30000000 13246708100) (Enclosure.sfrac Bool.true 3452700000 13246708100)) Bool.true 30000000 13246708100 0 1 Bool.true 3452700000 13246708100 0 1

noncomputable def ep410 := @ep408 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 13186708100 131867081 264934162 0 1 Bool.true 3452700000 34527000 132467081 0 1 (ep409 (BSN.N_div_s_sub_one_mk qz17 57545 1000 15 qz18 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 30000000 13246708100) (Enclosure.sfrac Bool.true 3452700000 13246708100) Bool.true 30000000 13246708100 0 1 Bool.true 3452700000 13246708100 0 1 (Enclosure.Real.IsNear.const Bool.true 30000000 13246708100) (Enclosure.Real.IsNear.const Bool.true 3452700000 13246708100))) qz74 rfl

noncomputable abbrev qz135 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz136 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz348 qz347 1))

noncomputable def ep411 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz136)) Bool.false 1 360 0 1

noncomputable def ep412 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz136) Bool.false 0 1 0 1 Bool.false

noncomputable def ep413 := @ep412 0 1 0 1 Bool.false 1 360 0 1 Bool.false 11509 36000 0 1 Bool.false 1 1 360 0 1 Bool.false 11509 11509 36000 0

noncomputable def ep414 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep415 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz136 Bool.false 1 360 0 1 Bool.false 11509 36000 0 1

noncomputable def ep416 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz136)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz136)) 1 360 0 1 0 1 0

noncomputable def ep417 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz136) 1 24 0 1 1 15 0 1 1

noncomputable def ep418 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep419 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep420 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow13.d7 rfl) qz336

noncomputable def ep421 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz6 Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 (BSN.ascPochhammer_one_eval qz6)

noncomputable def ep422 := ep421 (@Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk qz68 qz17) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 (BSN.s_crit_mk qz17 Bool.false 57545 1000 qz18) (@Enclosure.Complex.IsNear.mk qz68 qz17 Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 qz328 qz21))

noncomputable def ep423 := @ep419 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep420) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep422)

noncomputable def ep424 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 57545 1000 0 1 0 1 0

noncomputable def ep425 := @ep424 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep420) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep422)

noncomputable def ep426 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 11509 2400 0 1 0 1 0 1 11509

noncomputable def ep427 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 57545 1000 0 1 11509 2400 0

noncomputable def ep428 := @ep427 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep420) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep422)

noncomputable def ep429 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep430 := @ep429 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep420) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep422)

noncomputable def ep431 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 11509 2400 0 1 (@ep418 1 24 0 1 (ep423 rfl) (ep425 rfl) rfl rfl) (@ep426 11509 2400 0 1 (ep428 rfl) (ep430 rfl) rfl rfl)

noncomputable def ep432 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 11509 2400 0 1 ep431

noncomputable abbrev qz137 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz348 qz347 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 15) qz274) Bool.false 1 15 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 15 1 15 EMRow13.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 15) qz274 Bool.false 1 15 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 15) qz286))

noncomputable def ep433 := @ep417 360 0 1 ep432 (@Enclosure.Complex.IsNear.re_isNear qz136 Bool.false 1 15 0 1 Bool.false 0 1 0 1 qz137)

noncomputable def ep434 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz136) 11509 2400 0 1 0 1 0 1 0

noncomputable def ep435 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 11509 2400 0 1 ep431

noncomputable def ep436 := @ep434 1 0 1 ep435 (@Enclosure.Complex.IsNear.im_isNear qz136 Bool.false 1 15 0 1 Bool.false 0 1 0 1 qz137)

noncomputable def ep437 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz136)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz136)) 0 1 0 1 11509 36000 0

noncomputable def ep438 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz136) 1 24 0 1 0 1 0 1 0

noncomputable def ep439 := @ep438 1 0 1 ep432 (@Enclosure.Complex.IsNear.im_isNear qz136 Bool.false 1 15 0 1 Bool.false 0 1 0 1 qz137)

noncomputable def ep440 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz136) 11509 2400 0 1 1 15 0 1 11509

noncomputable def ep441 := @ep440 36000 0 1 ep435 (@Enclosure.Complex.IsNear.re_isNear qz136 Bool.false 1 15 0 1 Bool.false 0 1 0 1 qz137)

noncomputable def ep442 := @ep413 1 (@ep414 0 1 0 1 (BSN.bern_sum_base qz6 15) qz89) (ep415 (@ep416 1 1 1 360 0 1 (ep433 rfl) (ep436 rfl) rfl rfl) (@ep437 1 11509 11509 36000 0 1 (ep439 rfl) (ep441 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep443 := ep407 (ep410 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep411 Bool.false 11509 36000 0 1 (BSN.bern_sum_succ qz6 15 0 1 1 rfl rfl) (ep442 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep444 := @Enclosure.Real.IsNear.mulLit_ff qz127 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz98 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 16811667985 68719476736 350466798553 816043786240000 281591635229

noncomputable def ep445 := @ep444 4768814916000 0 1 6910985516530186049 478409438946498969600 98688518898011801023637 ep165 (@Enclosure.Complex.IsNear.im_isNear qz97 Bool.false 2836746035 34359738368 87128165107 204010946560000 Bool.false 16811667985 68719476736 350466798553 816043786240000 (ep394 ep403))

noncomputable def ep446 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz98 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 23868541661 47688149160 0 1 Bool.false

noncomputable def ep447 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz126 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz98 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz127 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz98 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 159760790945006413403 32771046567835179417600 24534562486982429754503

noncomputable def ep448 := nat_lit 972890444982606888960000000

noncomputable def ep449 := nat_lit 38915617799304275558400000

noncomputable def ep450 := nat_lit 19961446149751815611904365181154086617088

noncomputable def ep451 := @Enclosure.Real.IsNear.mulLit_ff qz126 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz98 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 2836746035 34359738368 87128165107 204010946560000 281591635229

noncomputable def ep452 := @ep451 4768814916000 0 1 159760790945006413403 32771046567835179417600 24534562486982429754503 ep448 (@Enclosure.Complex.IsNear.re_isNear qz97 Bool.false 2836746035 34359738368 87128165107 204010946560000 Bool.false 16811667985 68719476736 350466798553 816043786240000 (ep394 ep403))

noncomputable def ep453 := @Enclosure.Real.IsNear.mulLit_ff qz127 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz98 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz101 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 16811667985 68719476736 350466798553 816043786240000 23868541661

noncomputable def ep454 := @ep453 47688149160 0 1 585795617066967041 4784094389464989696 8365131382059575016533 ep449 (@Enclosure.Complex.IsNear.im_isNear qz97 Bool.false 2836746035 34359738368 87128165107 204010946560000 Bool.false 16811667985 68719476736 350466798553 816043786240000 (ep394 ep403))

noncomputable abbrev qz380 := (ep443 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep455 := @ep389 4172460767853730644253 32771046567835179417600 58415711759617951291957 ep293 (@ep390 ep391 6910985516530186049 478409438946498969600 98688518898011801023637 ep165 ep392 587184873652775692229 21847364378556786278400 930537414379178210114437 ep165 (ep404 (@ep405 281591635229 4768814916000 0 1 qz380) rfl) (ep445 (@ep446 281591635229 4768814916000 0 1 qz380) rfl) rfl rfl) (@ep447 ep448 585795617066967041 4784094389464989696 8365131382059575016533 ep449 ep450 4172460767853730644253 32771046567835179417600 58415711759617951291957 ep293 (ep452 (@ep446 281591635229 4768814916000 0 1 qz380) rfl) (ep454 (@ep405 281591635229 4768814916000 0 1 qz380) rfl) rfl rfl)

noncomputable def ep456 := @ep298 ep292 ep293 (@ep299 2448131358720000 (BSN.head_sum_c_eq qz6 15) (ep300 (BSN.head_sum_c_succ qz6 14 15 rfl rfl) (ep388 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep455 rfl rfl rfl

noncomputable def ep457 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz6 1 15) Bool.false 39001438368210071272229 21847364378556786278400 ep164 ep165 Bool.true 470272709072401688147 32771046567835179417600 ep292 ep293 (@ep294 ep165 Bool.true 470272709072401688147 32771046567835179417600 ep292 ep293 (BSN.zetaApproximant_eq_folded' qz6 1 15 rfl) (ep456 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep458 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.im (zetaApproximant qz6 1 15)) 13 65536 6781519

noncomputable def ep459 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) Bool.false 52 262144 6781519

noncomputable def ep460 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) qz315 Bool.false 4529497 131072 183

noncomputable def ep461 := nat_lit 70810434608117679406060403761214828134638629160646948449155592377094701056

noncomputable def ep462 := nat_lit 211920202972550851493400390504150001601814924744057251666168921467366998016

noncomputable def ep463 := BSN.cos_dyadic_bound_f 843207724 536870912 3 2 262144 71320 ep461 ep83 ep288 ep462 ep86 ep288 52 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 843207724) qz283 0 2 ep461 ep83 ep288 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 843207724) qz284 0 2 ep462 ep86 ep288 rfl rfl rfl rfl) rfl rfl

noncomputable def ep464 := @ep460 262144 Bool.false 52 262144 1 35625 (@ep168 4529497 131072 183 262144 ep286 rfl) (Enclosure.sfrac_false_div 4529497 131072) (BSN.sin_reduce1 qz315 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29667734338063170535424) qz28) 226375608064910080 72057594037927936 Bool.false 52 262144 5 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q1 4529497 131072 226375608064910080 72057594037927936 5 29667734338063170535424 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 52 262144 29667734338063170535424 18889465931478580854784 843207724 536870912 71320 71250 (ep463 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep465 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz6 1 15) Bool.false 39001438368210071272229 21847364378556786278400 ep164 ep165 Bool.true 470272709072401688147 32771046567835179417600 ep292 ep293 (@ep294 ep165 Bool.true 470272709072401688147 32771046567835179417600 ep292 ep293 (BSN.zetaApproximant_eq_folded' qz6 1 15 rfl) (ep456 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow13.d9 : Enclosure.Real.IsNear (hardyZApproximantEM 1 15 qz17) Bool.true ep149 ep150 ep151 ep152 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 15 qz17) ep153 Bool.true ep149 ep150 ep151 ep152 (@Eq.refl Real ep153) (@ep154 Bool.true ep149 ep150 ep151 ep152 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) (zetaApproximant qz6 1 15)) (@ep156 ep157 ep158 ep152 6113545217941221945911 ep159 ep160 ep161 ep162 ep149 ep150 ep151 ep152 (@ep163 9338880000 39001438368210071272229 21847364378556786278400 ep164 ep165 ep155 ep157 ep158 ep152 (@ep166 9338880000 262143 262144 6781519 9338880000 (ep291 rfl rfl) rfl) ep457 rfl) (@ep458 9338880000 470272709072401688147 32771046567835179417600 ep292 ep293 6113545217941221945911 ep159 ep160 ep161 (@ep459 9338880000 13 65536 6781519 9338880000 (ep464 rfl rfl) rfl) ep465 rfl) rfl rfl))

noncomputable abbrev qz492 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 60352 1000)))

noncomputable abbrev qz478 := qz492

noncomputable abbrev qz381 := qz478

noncomputable abbrev qz138 := (BSN.headSumC qz381 9)

noncomputable abbrev qz139 := qz381

noncomputable abbrev qz479 := (@Neg.neg Complex Complex.instNeg qz492)

noncomputable abbrev qz382 := qz479

noncomputable abbrev qz140 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 8) qz382)

noncomputable def ep466 := @Enclosure.Complex.IsNear.of_eq qz138 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz139 8) qz140) Bool.true 8727816397 34359738368 2383517848613 408021893120000 Bool.false 7637605233 34359738368 297965263811 51002736640000

noncomputable def ep467 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz139 8) qz140 Bool.true 20710301449 34359738368 6394528122341 1224065679360000 Bool.false 5639288631 34359738368 800352039277 153008209920000 Bool.false

noncomputable abbrev qz141 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 7) qz382)

noncomputable def ep468 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz139 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz139 7) qz141) Bool.true 20710301449 34359738368 6394528122341 1224065679360000 Bool.false 5639288631 34359738368 800352039277 153008209920000

noncomputable def ep469 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz139 7) qz141 Bool.true 32013753677 68719476736 3729646962833 816043786240000 Bool.true 12931567845 68719476736 3733398227833 816043786240000 Bool.true

noncomputable abbrev qz142 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 6) qz382)

noncomputable def ep470 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz139 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz139 6) qz142) Bool.true 32013753677 68719476736 3729646962833 816043786240000 Bool.true 12931567845 68719476736 3733398227833 816043786240000

noncomputable def ep471 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz139 6) qz142 Bool.true 38920289377 68719476736 3153218150277 816043786240000 Bool.false 14259645675 68719476736 3152467816527 816043786240000 Bool.false

noncomputable abbrev qz143 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 5) qz382)

noncomputable def ep472 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz139 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz139 5) qz143) Bool.true 38920289377 68719476736 3153218150277 816043786240000 Bool.false 14259645675 68719476736 3152467816527 816043786240000

noncomputable def ep473 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz139 5) qz143 Bool.true 1149346119 8589934592 236291621171 76504104960000 Bool.false 11030993315 34359738368 945717852809 306016419840000 Bool.true

noncomputable abbrev qz144 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 4) qz382)

noncomputable def ep474 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz139 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz139 4) qz144) Bool.true 1149346119 8589934592 236291621171 76504104960000 Bool.false 11030993315 34359738368 945717852809 306016419840000

noncomputable def ep475 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz139 4) qz144 Bool.false 4603730573 68719476736 5445320917229 2448131358720000 Bool.false 26764494013 34359738368 1361232394151 612032839680000 Bool.true

noncomputable abbrev qz145 := (@HPow.hPow Complex Complex Complex qz270 qz272 qz382)

noncomputable def ep476 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz139 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz139 3) qz145) Bool.false 4603730573 68719476736 5445320917229 2448131358720000 Bool.false 26764494013 34359738368 1361232394151 612032839680000

noncomputable def ep477 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz139 3) qz145 Bool.false 10534986853 17179869184 749359890551 612032839680000 Bool.false 10169486109 17179869184 187678668419 153008209920000 Bool.true

noncomputable abbrev qz146 := (@HPow.hPow Complex Complex Complex qz270 qz273 qz382)

noncomputable def ep478 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz139 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz139 2) qz146) Bool.false 10534986853 17179869184 749359890551 612032839680000 Bool.false 10169486109 17179869184 187678668419 153008209920000

noncomputable def ep479 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz139 2) qz146 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep480 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz139 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz139)

noncomputable abbrev qz493 := (Enclosure.sfrac Bool.false 60352 1000)

noncomputable abbrev qz480 := qz493

noncomputable abbrev qz383 := qz480

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz263 qz383 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz148 := qz383

noncomputable abbrev qz384 := (@Eq.refl Real qz480)

noncomputable abbrev qz149 := qz384

noncomputable def ep481 := @Enclosure.Complex.IsNear.of_eq qz146 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz147)))) Bool.true 6644882331 17179869184 749359890551 612032839680000 Bool.false 10169486109 17179869184 187678668419 153008209920000 (BSN.cpow_neg_s_mk qz148 60352 1000 2 qz149 rfl)

noncomputable def ep482 := nat_lit 11235923043758625464599610947068610660094574452930780324080952487161856256

noncomputable def ep483 := nat_lit 6473503370519902060565305142431643868134357708636075168718429094379776

noncomputable def ep484 := nat_lit 33694822124534836589677702230920968692547454643375068821905420603296809216

noncomputable def ep485 := BSN.cos_dyadic_bound_f 532589282 536870912 3 2 262144 71320 ep482 ep83 ep483 ep484 ep86 ep483 143391 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 532589282) qz283 0 2 ep482 ep83 ep483 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 532589282) qz284 0 2 ep484 ep86 ep483 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz150 := (Enclosure.Real.IsNear.const Bool.false 60352 1000)

noncomputable abbrev qz385 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10966199) qz31)

noncomputable def ep486 := @Enclosure.Real.IsNear.cos_image qz147 qz385 Bool.false 10966199 262144 445 262144 Bool.true 143391 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 21418359 512000 7544 4453125 10966199 262144 445 262144 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz20 60352 1000 0 1 90852 131072 1 35625 21418359 512000 7544 4453125 qz150 qz281 rfl) rfl) (Enclosure.sfrac_false_div 10966199 262144) (BSN.cos_reduce2 qz385 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 37477638947500099371008) qz33) 226375608064910080 72057594037927936 Bool.false 143391 262144 6 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q2 10966199 262144 226375608064910080 72057594037927936 6 37477638947500099371008 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 143391 262144 37477638947500099371008 37778931862957161709568 532589282 536870912 71320 71250 (ep485 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep487 := nat_lit 80458084556618063082024405361474576

noncomputable def ep488 := BSN.sin_dyadic_bound_f 532589282 536870912 2 1 262144 71320 ep487 ep57 ep487 ep487 ep58 ep487 219449 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 532589282) qz278 0 1 ep487 ep57 ep487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 532589282) qz279 0 1 ep487 ep58 ep487 rfl rfl rfl rfl) rfl rfl

noncomputable def ep489 := @Enclosure.Real.IsNear.sin_image qz147 qz385 Bool.false 10966199 262144 445 262144 Bool.true 219449 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 21418359 512000 7544 4453125 10966199 262144 445 262144 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz20 60352 1000 0 1 90852 131072 1 35625 21418359 512000 7544 4453125 qz150 qz281 rfl) rfl) (Enclosure.sfrac_false_div 10966199 262144) (BSN.sin_reduce2 qz385 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 37477638947500099371008) qz33) 226375608064910080 72057594037927936 Bool.false 219449 262144 6 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q2 10966199 262144 226375608064910080 72057594037927936 6 37477638947500099371008 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 219449 262144 37477638947500099371008 37778931862957161709568 532589282 536870912 71320 71250 (ep488 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep490 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz147))) Bool.true 6644882331 17179869184 749359890551 612032839680000 Bool.false 10169486109 17179869184 187678668419 153008209920000 (@Enclosure.Real.IsNear.mulLit_ft qz15 (Real.cos qz147) 46341 65536 1 131072 143391 262144 16115269 9338880000 6644882331 17179869184 749359890551 612032839680000 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz147) Bool.true 143391 262144 16115269 9338880000 143391 262144 16115269 9338880000 (ep486 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz15 (@Neg.neg Real Real.instNeg (Real.sin qz147)) 46341 65536 1 131072 219449 262144 16115269 9338880000 10169486109 17179869184 187678668419 153008209920000 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz147) Bool.true 219449 262144 16115269 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz147) Bool.true 219449 262144 16115269 9338880000 219449 262144 16115269 9338880000 (ep489 rfl rfl) rfl)) rfl)

noncomputable def ep491 := @ep479 6644882331 17179869184 749359890551 612032839680000 Bool.false 10169486109 17179869184 187678668419 153008209920000 Bool.false 10534986853 10534986853 17179869184 749359890551 612032839680000 Bool.false 10169486109 10169486109 17179869184 187678668419 153008209920000 (ep480 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep481 ep490) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz263 qz383 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep492 := @Enclosure.Complex.IsNear.of_eq qz145 (Complex.mk (@HMul.hMul Real Real Real qz0 qz23 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz23 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.true 37536216839 68719476736 32638418067 32641751449600 Bool.false 6425521795 34359738368 8140236273 8160437862400 (BSN.cpow_neg_s_mk qz148 60352 1000 3 qz149 rfl)

noncomputable def ep493 := nat_lit 983518465460011405748605303922401

noncomputable def ep494 := BSN.cos_dyadic_bound_f 177090649 536870912 2 1 262144 71320 ep493 ep61 ep493 ep493 ep62 ep493 248011 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 177090649) qz283 0 1 ep493 ep61 ep493 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 177090649) qz284 0 1 ep493 ep62 ep493 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz386 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17381013) qz31)

noncomputable def ep495 := @Enclosure.Real.IsNear.cos_image qz151 qz386 Bool.false 17381013 262144 445 262144 Bool.true 248011 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 135789171 2048000 7544 4453125 17381013 262144 445 262144 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz27 60352 1000 0 1 143997 131072 1 35625 135789171 2048000 7544 4453125 qz150 qz288 rfl) rfl) (Enclosure.sfrac_false_div 17381013 262144) (BSN.cos_reduce2 qz386 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12461646620048800874496) qz33) 226375608064910080 72057594037927936 Bool.false 248011 262144 10 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q2 17381013 262144 226375608064910080 72057594037927936 10 12461646620048800874496 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 248011 262144 12461646620048800874496 37778931862957161709568 177090649 536870912 71320 71250 (ep494 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep496 := BSN.sin_dyadic_bound_f 177090649 536870912 2 1 262144 71320 ep493 ep57 ep493 ep493 ep58 ep493 84910 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 177090649) qz278 0 1 ep493 ep57 ep493 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 177090649) qz279 0 1 ep493 ep58 ep493 rfl rfl rfl rfl) rfl rfl

noncomputable def ep497 := @Enclosure.Real.IsNear.sin_image qz151 qz386 Bool.false 17381013 262144 445 262144 Bool.true 84910 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 135789171 2048000 7544 4453125 17381013 262144 445 262144 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz27 60352 1000 0 1 143997 131072 1 35625 135789171 2048000 7544 4453125 qz150 qz288 rfl) rfl) (Enclosure.sfrac_false_div 17381013 262144) (BSN.sin_reduce2 qz386 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12461646620048800874496) qz33) 226375608064910080 72057594037927936 Bool.false 84910 262144 10 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q2 17381013 262144 226375608064910080 72057594037927936 10 12461646620048800874496 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 84910 262144 12461646620048800874496 37778931862957161709568 177090649 536870912 71320 71250 (ep496 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep498 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz23 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz23 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.true 37536216839 68719476736 32638418067 32641751449600 Bool.false 6425521795 34359738368 8140236273 8160437862400 (@Enclosure.Real.IsNear.mulLit_ft qz23 (Real.cos qz151) 151349 262144 1 262144 248011 262144 16115269 9338880000 37536216839 68719476736 32638418067 32641751449600 qz289 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.true 248011 262144 16115269 9338880000 248011 262144 16115269 9338880000 (ep495 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz23 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 151349 262144 1 262144 42455 131072 16115269 9338880000 6425521795 34359738368 8140236273 8160437862400 qz289 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.true 42455 131072 16115269 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.true 84910 262144 16115269 9338880000 42455 131072 16115269 9338880000 (ep497 rfl rfl) rfl)) rfl)

noncomputable def ep499 := @ep477 37536216839 68719476736 32638418067 32641751449600 Bool.false 6425521795 34359738368 8140236273 8160437862400 Bool.false 79091489002521362432 4603730573 68719476736 5445320917229 2448131358720000 Bool.false 459810505919291195392 26764494013 34359738368 1361232394151 612032839680000 (ep478 (BSN.head_sum_c_succ qz139 2 3 rfl rfl) (ep491 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep492 ep498) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz263 qz383 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep500 := @Enclosure.Complex.IsNear.of_eq qz144 (Complex.mk (@HMul.hMul Real Real Real qz0 qz29 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz29 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.true 13798499525 68719476736 2116010960243 2448131358720000 Bool.true 7866750349 17179869184 530203311467 612032839680000 (BSN.cpow_neg_s_mk qz148 60352 1000 4 qz149 rfl)

noncomputable def ep501 := nat_lit 2423042858991621740369220486000625

noncomputable def ep502 := BSN.sin_dyadic_bound_f 221865755 536870912 2 1 262144 71320 ep501 ep57 ep501 ep501 ep58 ep501 105275 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 221865755) qz278 0 1 ep501 ep57 ep501 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 221865755) qz279 0 1 ep501 ep58 ep501 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz387 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21932399) qz31)

noncomputable def ep503 := @Enclosure.Real.IsNear.cos_image qz152 qz387 Bool.false 21932399 262144 445 262144 Bool.true 105275 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 21418359 256000 7544 4453125 21932399 262144 445 262144 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz32 60352 1000 0 1 181704 131072 1 35625 21418359 256000 7544 4453125 qz150 qz292 rfl) rfl) (Enclosure.sfrac_false_div 21932399 262144) (BSN.cos_reduce1 qz387 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15612414609620486586368) qz33) 226375608064910080 72057594037927936 Bool.false 105275 262144 13 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q1 21932399 262144 226375608064910080 72057594037927936 13 15612414609620486586368 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 105275 262144 15612414609620486586368 37778931862957161709568 221865755 536870912 71320 71250 (ep502 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep504 := BSN.cos_dyadic_bound_f 221865755 536870912 2 1 262144 71320 ep501 ep61 ep501 ep501 ep62 ep501 240076 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 221865755) qz283 0 1 ep501 ep61 ep501 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 221865755) qz284 0 1 ep501 ep62 ep501 rfl rfl rfl rfl) rfl rfl

noncomputable def ep505 := @Enclosure.Real.IsNear.sin_image qz152 qz387 Bool.false 21932399 262144 445 262144 Bool.false 240076 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 21418359 256000 7544 4453125 21932399 262144 445 262144 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz32 60352 1000 0 1 181704 131072 1 35625 21418359 256000 7544 4453125 qz150 qz292 rfl) rfl) (Enclosure.sfrac_false_div 21932399 262144) (BSN.sin_reduce1 qz387 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15612414609620486586368) qz33) 226375608064910080 72057594037927936 Bool.false 240076 262144 13 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q1 21932399 262144 226375608064910080 72057594037927936 13 15612414609620486586368 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 240076 262144 15612414609620486586368 37778931862957161709568 221865755 536870912 71320 71250 (ep504 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep506 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz29 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz29 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.true 13798499525 68719476736 2116010960243 2448131358720000 Bool.true 7866750349 17179869184 530203311467 612032839680000 (@Enclosure.Real.IsNear.mulLit_ft qz29 (Real.cos qz152) 131071 262144 1 262144 105275 262144 16115269 9338880000 13798499525 68719476736 2116010960243 2448131358720000 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.true 105275 262144 16115269 9338880000 105275 262144 16115269 9338880000 (ep503 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz29 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 131071 262144 1 262144 60019 65536 16115269 9338880000 7866750349 17179869184 530203311467 612032839680000 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.false 60019 65536 16115269 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.false 240076 262144 16115269 9338880000 60019 65536 16115269 9338880000 (ep505 rfl rfl) rfl)) rfl)

noncomputable def ep507 := @ep475 13798499525 68719476736 2116010960243 2448131358720000 Bool.true 7866750349 17179869184 530203311467 612032839680000 Bool.true 631859711089859100672 1149346119 8589934592 236291621171 76504104960000 Bool.false 189511022121278504960 11030993315 34359738368 945717852809 306016419840000 (ep476 (BSN.head_sum_c_succ qz139 3 4 rfl rfl) (ep499 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep500 ep506) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz263 qz383 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep508 := @Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.true 29725520425 68719476736 1898322573359 2448131358720000 Bool.true 7802340955 68719476736 1891660627109 2448131358720000 (BSN.cpow_neg_s_mk qz148 60352 1000 5 qz149 rfl)

noncomputable def ep509 := nat_lit 62300507367984417894509560191108813939979349844445947932738644077593292865

noncomputable def ep510 := nat_lit 61376831728082480700343076389871254742428132120700225292942659632296001

noncomputable def ep511 := nat_lit 163068623474304199040676864091129959239886746902496348982888827325720621121

noncomputable def ep512 := BSN.sin_dyadic_bound_f 705505751 536870912 3 2 262144 71320 ep509 ep90 ep510 ep511 ep92 ep510 253555 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 705505751) qz278 0 2 ep509 ep90 ep510 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 705505751) qz279 0 2 ep511 ep92 ep510 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz388 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12731375) qz26)

noncomputable def ep513 := @Enclosure.Real.IsNear.cos_image qz153 qz388 Bool.false 12731375 131072 445 262144 Bool.true 253555 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 24865967 256000 7544 4453125 12731375 131072 445 262144 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz36 60352 1000 0 1 210952 131072 1 35625 24865967 256000 7544 4453125 qz150 qz296 rfl) rfl) (Enclosure.sfrac_false_div 12731375 131072) (BSN.cos_reduce1 qz388 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24822776871932018032640) qz28) 226375608064910080 72057594037927936 Bool.false 253555 262144 15 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q1 12731375 131072 226375608064910080 72057594037927936 15 24822776871932018032640 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 253555 262144 24822776871932018032640 18889465931478580854784 705505751 536870912 71320 71250 (ep512 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep514 := nat_lit 34638671574092713266149908140122617190985162416745837840540554558499516481

noncomputable def ep515 := nat_lit 103793261058821974837049038267588109063470630985996113071035778356233957441

noncomputable def ep516 := BSN.cos_dyadic_bound_f 705505751 536870912 3 2 262144 71320 ep514 ep83 ep510 ep515 ep86 ep510 66553 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 705505751) qz283 0 2 ep514 ep83 ep510 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 705505751) qz284 0 2 ep515 ep86 ep510 rfl rfl rfl rfl) rfl rfl

noncomputable def ep517 := @Enclosure.Real.IsNear.sin_image qz153 qz388 Bool.false 12731375 131072 445 262144 Bool.false 66553 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 24865967 256000 7544 4453125 12731375 131072 445 262144 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz36 60352 1000 0 1 210952 131072 1 35625 24865967 256000 7544 4453125 qz150 qz296 rfl) rfl) (Enclosure.sfrac_false_div 12731375 131072) (BSN.sin_reduce1 qz388 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24822776871932018032640) qz28) 226375608064910080 72057594037927936 Bool.false 66553 262144 15 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q1 12731375 131072 226375608064910080 72057594037927936 15 24822776871932018032640 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 66553 262144 24822776871932018032640 18889465931478580854784 705505751 536870912 71320 71250 (ep516 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep518 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.true 29725520425 68719476736 1898322573359 2448131358720000 Bool.true 7802340955 68719476736 1891660627109 2448131358720000 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz153) 117235 262144 1 262144 253555 262144 16115269 9338880000 29725520425 68719476736 1898322573359 2448131358720000 qz297 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.true 253555 262144 16115269 9338880000 253555 262144 16115269 9338880000 (ep513 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 117235 262144 1 262144 66553 262144 16115269 9338880000 7802340955 68719476736 1891660627109 2448131358720000 qz297 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.false 66553 262144 16115269 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.false 66553 262144 16115269 9338880000 66553 262144 16115269 9338880000 (ep517 rfl rfl) rfl)) rfl)

noncomputable def ep519 := @ep473 29725520425 68719476736 1898322573359 2448131358720000 Bool.true 7802340955 68719476736 1891660627109 2448131358720000 Bool.true 334322740050142429184 38920289377 68719476736 3153218150277 816043786240000 Bool.false 489957694613382758400 14259645675 68719476736 3152467816527 816043786240000 (ep474 (BSN.head_sum_c_succ qz139 4 5 rfl rfl) (ep507 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep508 ep518) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz263 qz383 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep520 := @Enclosure.Complex.IsNear.of_eq qz142 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 1726633925 17179869184 144107203139 204010946560000 Bool.true 1699450845 4294967296 290465205653 408021893120000 (BSN.cpow_neg_s_mk qz148 60352 1000 6 qz149 rfl)

noncomputable def ep521 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz39 60352 1000 0 1 4034681531866359 2251799813685248 800000000057 28500000000000000 3804704684549976537 35184372088832000 754400000053751 445312500000000000 qz150 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 800000000057 28500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz299) Bool.false 8461340443916598509568 4722366482869645213696 1000000000071250 35625000000000000000 4034681531866359 2251799813685248 800000000057 28500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 53145 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep115 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep522 := nat_lit 35486116451037912261595096406233424913576684607670951579031905824273851361

noncomputable def ep523 := nat_lit 64411197348001461506419573543519144599440126498849092995466830222451681

noncomputable def ep524 := nat_lit 106329526958417733861772450071613236451531173570015156551104783812376650721

noncomputable def ep525 := BSN.cos_dyadic_bound_f 709774139 536870912 3 2 262144 71320 ep522 ep83 ep523 ep524 ep86 ep523 64535 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 709774139) qz283 0 2 ep522 ep83 ep523 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 709774139) qz284 0 2 ep524 ep86 ep523 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz389 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14173629) qz26)

noncomputable def ep526 := @Enclosure.Real.IsNear.cos_image qz154 qz389 Bool.false 14173629 131072 445 262144 Bool.false 64535 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 3804704684549976537 35184372088832000 754400000053751 445312500000000000 14173629 131072 445 262144 (ep521 rfl) rfl) (Enclosure.sfrac_false_div 14173629 131072) (BSN.cos_reduce0 qz389 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24972957433100194807808) qz28) 226375608064910080 72057594037927936 Bool.false 64535 262144 17 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 14173629 131072 226375608064910080 72057594037927936 17 24972957433100194807808 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 64535 262144 24972957433100194807808 18889465931478580854784 709774139 536870912 71320 71250 (ep525 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep527 := nat_lit 63823480653989840901666037872385349528758480192608633567861057019514971105

noncomputable def ep528 := nat_lit 167052450250457580947638753213367360626920735537738760812881536373607621601

noncomputable def ep529 := BSN.sin_dyadic_bound_f 709774139 536870912 3 2 262144 71320 ep527 ep90 ep523 ep528 ep92 ep523 254076 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 709774139) qz278 0 2 ep527 ep90 ep523 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 709774139) qz279 0 2 ep528 ep92 ep523 rfl rfl rfl rfl) rfl rfl

noncomputable def ep530 := @Enclosure.Real.IsNear.sin_image qz154 qz389 Bool.false 14173629 131072 445 262144 Bool.false 254076 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 3804704684549976537 35184372088832000 754400000053751 445312500000000000 14173629 131072 445 262144 (ep521 rfl) rfl) (Enclosure.sfrac_false_div 14173629 131072) (BSN.sin_reduce0 qz389 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24972957433100194807808) qz28) 226375608064910080 72057594037927936 Bool.false 254076 262144 17 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 14173629 131072 226375608064910080 72057594037927936 17 24972957433100194807808 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 254076 262144 24972957433100194807808 18889465931478580854784 709774139 536870912 71320 71250 (ep529 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep531 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 1726633925 17179869184 144107203139 204010946560000 Bool.true 1699450845 4294967296 290465205653 408021893120000 (@Enclosure.Real.IsNear.mulLit_ff qz37 (Real.cos qz154) 26755 65536 1 131072 64535 262144 16115269 9338880000 1726633925 17179869184 144107203139 204010946560000 qz301 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 64535 262144 16115269 9338880000 64535 262144 16115269 9338880000 (ep526 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz37 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 26755 65536 1 131072 63519 65536 16115269 9338880000 1699450845 4294967296 290465205653 408021893120000 qz301 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.false 63519 65536 16115269 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.false 254076 262144 16115269 9338880000 63519 65536 16115269 9338880000 (ep530 rfl rfl) rfl)) rfl)

noncomputable def ep532 := @ep471 1726633925 17179869184 144107203139 204010946560000 Bool.true 1699450845 4294967296 290465205653 408021893120000 Bool.true 549992100259658989568 32013753677 68719476736 3729646962833 816043786240000 Bool.true 55540660980280197120 12931567845 68719476736 3733398227833 816043786240000 (ep472 (BSN.head_sum_c_succ qz139 5 6 rfl rfl) (ep519 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep520 ep531) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz263 qz383 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep533 := @Enclosure.Complex.IsNear.of_eq qz141 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.true 9406849221 68719476736 1600115356183 2448131358720000 Bool.false 24210145107 68719476736 1605437944933 2448131358720000 (BSN.cpow_neg_s_mk qz148 60352 1000 7 qz149 rfl)

noncomputable def ep534 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz42 60352 1000 0 1 4381783608859895 2251799813685248 800000000057 28500000000000000 826404388630976197 7036874417766400 754400000053751 445312500000000000 qz150 (BSN.isNear_log_sfrac 7 1 4381783608859895 2251799813685248 800000000057 28500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz303) Bool.false 9189266258887746519040 4722366482869645213696 1000000000071250 35625000000000000000 4381783608859895 2251799813685248 800000000057 28500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 73349 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep129 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep535 := nat_lit 24088752515896983713353931441654498994335959435837546195045899300027498496

noncomputable def ep536 := nat_lit 29715218861907275627979755975073081635343857197786101893320007709884416

noncomputable def ep537 := nat_lit 72206827109967136588805834813013350819737190593117066381351057884662726656

noncomputable def ep538 := BSN.cos_dyadic_bound_f 644350792 536870912 3 2 262144 71320 ep535 ep83 ep536 ep537 ep86 ep536 94941 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 644350792) qz283 0 2 ep535 ep83 ep536 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 644350792) qz284 0 2 ep537 ep86 ep536 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz390 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15392981) qz26)

noncomputable def ep539 := @Enclosure.Real.IsNear.cos_image qz155 qz390 Bool.false 15392981 131072 445 262144 Bool.true 94941 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 826404388630976197 7036874417766400 754400000053751 445312500000000000 15392981 131072 445 262144 (ep534 rfl) rfl) (Enclosure.sfrac_false_div 15392981 131072) (BSN.cos_reduce2 qz390 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 22671078042067840008192) qz28) 226375608064910080 72057594037927936 Bool.false 94941 262144 18 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q2 15392981 131072 226375608064910080 72057594037927936 18 22671078042067840008192 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 94941 262144 22671078042067840008192 18889465931478580854784 644350792 536870912 71320 71250 (ep538 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep540 := nat_lit 43335982353525044863534692790198039724496451898749354269567962733881589760

noncomputable def ep541 := nat_lit 113450891047741553339193180559892366670081103013642369398184050957207207936

noncomputable def ep542 := BSN.sin_dyadic_bound_f 644350792 536870912 3 2 262144 71320 ep540 ep90 ep536 ep541 ep92 ep536 244347 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 644350792) qz278 0 2 ep540 ep90 ep536 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 644350792) qz279 0 2 ep541 ep92 ep536 rfl rfl rfl rfl) rfl rfl

noncomputable def ep543 := @Enclosure.Real.IsNear.sin_image qz155 qz390 Bool.false 15392981 131072 445 262144 Bool.true 244347 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 826404388630976197 7036874417766400 754400000053751 445312500000000000 15392981 131072 445 262144 (ep534 rfl) rfl) (Enclosure.sfrac_false_div 15392981 131072) (BSN.sin_reduce2 qz390 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 22671078042067840008192) qz28) 226375608064910080 72057594037927936 Bool.false 244347 262144 18 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q2 15392981 131072 226375608064910080 72057594037927936 18 22671078042067840008192 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 244347 262144 22671078042067840008192 18889465931478580854784 644350792 536870912 71320 71250 (ep542 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep544 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.true 9406849221 68719476736 1600115356183 2448131358720000 Bool.false 24210145107 68719476736 1605437944933 2448131358720000 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz155) 99081 262144 1 262144 94941 262144 16115269 9338880000 9406849221 68719476736 1600115356183 2448131358720000 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.true 94941 262144 16115269 9338880000 94941 262144 16115269 9338880000 (ep539 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz40 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 99081 262144 1 262144 244347 262144 16115269 9338880000 24210145107 68719476736 1605437944933 2448131358720000 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.true 244347 262144 16115269 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.true 244347 262144 16115269 9338880000 244347 262144 16115269 9338880000 (ep543 rfl rfl) rfl)) rfl)

noncomputable def ep545 := @ep469 9406849221 68719476736 1600115356183 2448131358720000 Bool.false 24210145107 68719476736 1605437944933 2448131358720000 Bool.true 2846402157240205180928 20710301449 34359738368 6394528122341 1224065679360000 Bool.false 775057927771187576832 5639288631 34359738368 800352039277 153008209920000 (ep470 (BSN.head_sum_c_succ qz139 6 7 rfl rfl) (ep532 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep533 ep544) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz263 qz383 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep546 := @Enclosure.Complex.IsNear.of_eq qz140 (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.false 2995621263 8589934592 378012711749 612032839680000 Bool.false 999158301 17179869184 23385938039 38252052480000 (BSN.cpow_neg_s_mk qz148 60352 1000 8 qz149 rfl)

noncomputable def ep547 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz45 60352 1000 0 1 9364972152248037 4503599627370496 1600000000171 57000000000000000 8831168739569898891 70368744177664000 1508800000161253 890625000000000000 qz150 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz307) Bool.false 9819885039515637645312 4722366482869645213696 1000000000106875 35625000000000000000 9364972152248037 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep140 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep548 := nat_lit 81560565610127085520032974579836938624954848990734988935855127078491138465

noncomputable def ep549 := nat_lit 105127805022666813318471890726872842854598961706842029698059187152759201

noncomputable def ep550 := nat_lit 213440798246962811045189788457443711795974301418685322022014189378753276321

noncomputable def ep551 := BSN.sin_dyadic_bound_f 754596349 536870912 3 2 262144 71320 ep548 ep90 ep549 ep550 ep92 ep549 258572 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 754596349) qz278 0 2 ep548 ep90 ep549 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 754596349) qz279 0 2 ep550 ep92 ep549 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz391 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 32898667) qz31)

noncomputable def ep552 := @Enclosure.Real.IsNear.cos_image qz156 qz391 Bool.false 32898667 262144 445 262144 Bool.false 258572 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 8831168739569898891 70368744177664000 1508800000161253 890625000000000000 32898667 262144 445 262144 (ep547 rfl) rfl) (Enclosure.sfrac_false_div 32898667 262144) (BSN.cos_reduce3 qz391 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 53099997505097820012544) qz33) 226375608064910080 72057594037927936 Bool.false 258572 262144 19 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q3 32898667 262144 226375608064910080 72057594037927936 19 53099997505097820012544 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 258572 262144 53099997505097820012544 37778931862957161709568 754596349 536870912 71320 71250 (ep551 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep553 := nat_lit 45358148807858454983715417829121353832910293422278034755340874682340747681

noncomputable def ep554 := nat_lit 135864190813530031324509309705910315813021682343420420206626505672716724641

noncomputable def ep555 := BSN.cos_dyadic_bound_f 754596349 536870912 3 2 262144 71320 ep553 ep83 ep549 ep554 ep86 ep549 43122 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 754596349) qz283 0 2 ep553 ep83 ep549 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 754596349) qz284 0 2 ep554 ep86 ep549 rfl rfl rfl rfl) rfl rfl

noncomputable def ep556 := @Enclosure.Real.IsNear.sin_image qz156 qz391 Bool.false 32898667 262144 445 262144 Bool.true 43122 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 8831168739569898891 70368744177664000 1508800000161253 890625000000000000 32898667 262144 445 262144 (ep547 rfl) rfl) (Enclosure.sfrac_false_div 32898667 262144) (BSN.sin_reduce3 qz391 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 53099997505097820012544) qz33) 226375608064910080 72057594037927936 Bool.false 43122 262144 19 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q3 32898667 262144 226375608064910080 72057594037927936 19 53099997505097820012544 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 43122 262144 53099997505097820012544 37778931862957161709568 754596349 536870912 71320 71250 (ep555 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep557 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.false 2995621263 8589934592 378012711749 612032839680000 Bool.false 999158301 17179869184 23385938039 38252052480000 (@Enclosure.Real.IsNear.mulLit_ff qz43 (Real.cos qz156) 46341 131072 1 131072 64643 65536 16115269 9338880000 2995621263 8589934592 378012711749 612032839680000 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.false 258572 262144 16115269 9338880000 64643 65536 16115269 9338880000 (ep552 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz43 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 46341 131072 1 131072 21561 131072 16115269 9338880000 999158301 17179869184 23385938039 38252052480000 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.true 21561 131072 16115269 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.true 43122 262144 16115269 9338880000 21561 131072 16115269 9338880000 (ep556 rfl rfl) rfl)) rfl)

noncomputable def ep558 := @ep467 2995621263 8589934592 378012711749 612032839680000 Bool.false 999158301 17179869184 23385938039 38252052480000 Bool.true 74971371981215105024 8727816397 34359738368 2383517848613 408021893120000 Bool.false 131213058781973839872 7637605233 34359738368 297965263811 51002736640000 (ep468 (BSN.head_sum_c_succ qz139 7 8 rfl rfl) (ep545 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep546 ep557) rfl rfl

theorem EMRow13.d10 : Enclosure.Complex.IsNear qz138 Bool.true 8727816397 34359738368 2383517848613 408021893120000 Bool.false 7637605233 34359738368 297965263811 51002736640000 := ep466 (BSN.head_sum_c_succ qz139 8 9 rfl rfl) (ep558 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow13.d11 : @Eq Nat (Nat.pow 16 1) 16 := @Eq.refl Nat 16

noncomputable def ep559 := nat_lit 7375300663860543220469285337

noncomputable def ep560 := nat_lit 13123899696567190151181107200

noncomputable def ep561 := nat_lit 839515145785659222466757756410763533

noncomputable def ep562 := nat_lit 83280371316692970314819174400000000000

noncomputable abbrev qz481 := (@HAdd.hAdd Complex Complex Complex qz486 (@HAdd.hAdd Complex Complex Complex qz486 qz489 (@HMul.hMul Complex Complex Complex qz488 Complex.I (@HDiv.hDiv Complex Complex Complex qz490 (↑qz493) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz392 := qz481

noncomputable abbrev qz157 := (Complex.Stirling.logGammaStirling 1 qz392)

noncomputable abbrev qz482 := (@HAdd.hAdd Complex Complex Complex qz486 qz489 (@HMul.hMul Complex Complex Complex qz488 Complex.I (@HDiv.hDiv Complex Complex Complex qz490 (↑qz493) (2 : Complex))))

noncomputable abbrev qz393 := qz482

noncomputable abbrev qz158 := qz393

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz263 (@HDiv.hDiv Real Real Real qz266 qz383 (2 : Real)) (Real.log Real.pi))

noncomputable def ep563 := Complex.re (@HMul.hMul Complex Complex Complex qz46 (Complex.exp (@HMul.hMul Complex Complex Complex qz46 Complex.I ↑(@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))))) qz159))) (zetaApproximant qz139 1 16))

noncomputable def ep564 := @Enclosure.Real.IsNear.of_eq ep563 (@HSub.hSub Real Real Real qz314 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))))) qz159)) (Complex.re (zetaApproximant qz139 1 16))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))))) qz159)) (Complex.im (zetaApproximant qz139 1 16))))

noncomputable def ep565 := nat_lit 115239609396593690031805383

noncomputable def ep566 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))))) qz159)) (Complex.re (zetaApproximant qz139 1 16))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))))) qz159)) (Complex.im (zetaApproximant qz139 1 16))) ep565

noncomputable def ep567 := nat_lit 205060932758862346112204800

noncomputable def ep568 := nat_lit 13090792879681802964218836925696761

noncomputable def ep569 := nat_lit 1301255801823327661169049600000000000

noncomputable def ep570 := nat_lit 524955987862687606047244288

noncomputable def ep571 := nat_lit 568133828674610918917397722056943

noncomputable def ep572 := nat_lit 27760123772230990104939724800000000000

noncomputable def ep573 := nat_lit 60495441340331987035033060385088426228933306775240704

noncomputable def ep574 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))))) qz159)) (Complex.re (zetaApproximant qz139 1 16)) 262143 262144 7066519

noncomputable def ep575 := nat_lit 1341490482681669174332869

noncomputable def ep576 := nat_lit 139337458220185681920000000

noncomputable def ep577 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))))) qz159)) Bool.false 262143 262144 7066519

noncomputable abbrev qz394 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9882641) qz31)

noncomputable def ep578 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))))) qz159) qz394 Bool.false 9882641 262144 191

noncomputable def ep579 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))))) qz159) Bool.false 15917109015208984591 422212465065984000 7051447195821646451 9728000000000000000000

noncomputable def ep580 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))))) qz159 6100349309412638723 84442493013196800 2572197195821646451 9728000000000000000000 70744803 2048000

noncomputable def ep581 := nat_lit 6519647852629600088473600

noncomputable def ep582 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 213170176867559519859 4503599627370496000 215393835928157352947 466944000000000000000000 Bool.false 6100349309412638723 84442493013196800

noncomputable def ep583 := @Enclosure.Complex.IsNear.subLitP qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 182478222535943088859 4503599627370496000 208840235923954856947 466944000000000000000000 Bool.false 6361438223181519623 84442493013196800 6897391587435755353

noncomputable def ep584 := nat_lit 960033129107243779886014824462680064

noncomputable def ep585 := nat_lit 1717095679793788897483043832332288

noncomputable abbrev qz395 := (@HSub.hSub Complex Complex Complex qz471 qz481 qz474)

noncomputable abbrev qz396 := (Complex.log qz481)

noncomputable abbrev qz160 := (@HSub.hSub Complex Complex Complex qz311 (@HMul.hMul Complex Complex Complex qz310 qz395 qz396) qz392)

noncomputable abbrev qz161 := qz392

noncomputable def ep586 := @Enclosure.Complex.IsNear.of_eq qz157 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz160 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz161 (@HSub.hSub Int Int Int qz323 qz57 (@HMul.hMul Int Int Int qz324 qz58 (@Nat.cast Int instNatCastInt k)))))) Bool.true 182478222535943088859

noncomputable def ep587 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz160 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz161 (@HSub.hSub Int Int Int qz323 qz57 (@HMul.hMul Int Int Int qz324 qz58 (@Nat.cast Int instNatCastInt k))))) Bool.true 182479144743855024859 4503599627370496000

noncomputable def ep588 := nat_lit 391868999012042875583313477632

noncomputable def ep589 := nat_lit 533636115704862809616547840000

noncomputable def ep590 := @ep587 12746556616865383 28500000000000000000 Bool.false 10602783546218512993 140737488355328000 13470400007790019 57000000000000000000 Bool.false 439743 2147483648 3 2147483648 Bool.true 138225883 50331648000 943 50331648000 Bool.true ep588 182478222535943088859 4503599627370496000 208840235923954856947 466944000000000000000000 Bool.false ep589

noncomputable def ep591 := @Enclosure.Complex.IsNear.addLitP qz160 qz52 Bool.true 186617654971196336859 4503599627370496000 24840800001308891 57000000000000000000

noncomputable def ep592 := nat_lit 47835812919733131636637696

noncomputable def ep593 := @ep591 Bool.false 10602783546218512993 140737488355328000 13470400007790019 57000000000000000000 Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 Bool.true ep592 182479144743855024859 4503599627370496000 12746556616865383 28500000000000000000 Bool.false 10602783546218512993 10602783546218512993 140737488355328000

noncomputable abbrev qz162 := (@HMul.hMul Complex Complex Complex qz310 qz395 qz396)

noncomputable def ep594 := @Enclosure.Complex.IsNear.subLitP qz162 qz161 Bool.true 176484555809612720859 4503599627370496000 24840800001308891 57000000000000000000 Bool.false 14849677994828890721

noncomputable def ep595 := @ep594 140737488355328000 13470400007790019 57000000000000000000 Bool.false 9000 4000 0 1 Bool.false 120704 4000 0 1 Bool.true 746470619884785347436000 186617654971196336859 4503599627370496000 24840800001308891 57000000000000000000 Bool.false 42411134184874051972000 10602783546218512993 140737488355328000 13470400007790019 57000000000000000000

noncomputable abbrev qz163 := qz395

noncomputable abbrev qz164 := qz396

noncomputable def ep596 := @Enclosure.Complex.IsNear.mul qz163 qz164 Bool.true 176484555809612720859 4503599627370496000 24840800001308891 57000000000000000000 Bool.false 14849677994828890721 140737488355328000 13470400007790019

noncomputable abbrev qz165 := (Complex.re qz395)

noncomputable abbrev qz166 := (Complex.re qz396)

noncomputable abbrev qz167 := (Complex.im qz395)

noncomputable abbrev qz168 := (Complex.im qz396)

noncomputable def ep597 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz165 qz166) (@HMul.hMul Real Real Real qz0 qz167 qz168) 214990336274604233 36028797018963968 5600000003591 456000000000000000 794368546265383789 17592186044416000

noncomputable def ep598 := nat_lit 24837993118150604833258931069386752

noncomputable def ep599 := @Enclosure.Real.IsNear.mulLit_ff qz165 qz166 7000 4000 0 1 30712905182086319 9007199254740992 800000000513 114000000000000000

noncomputable def ep600 := @Enclosure.Complex.IsNear.re_isNear qz163 Bool.false 7000 4000 0 1 Bool.false 120704 4000 0 1

noncomputable abbrev qz397 := (Enclosure.sfrac Bool.false 120704 4000)

noncomputable abbrev qz169 := qz397

noncomputable def ep601 := @Enclosure.Complex.IsNear.of_eq qz163 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz169) Bool.false 7000 4000 0 1 Bool.false 120704 4000 0

noncomputable abbrev qz170 := (Complex.mk qz326 qz397)

noncomputable def ep602 := @Enclosure.Complex.IsNear.of_eq qz164 (Complex.log qz170) Bool.false 30712905182086319 9007199254740992 800000000513 114000000000000000 Bool.false 842384460514723 562949953421312 1600000000057 114000000000000000

noncomputable def ep603 := nat_lit 70044514006292494308787536216287854286302457778651301070069269638514463015946650910720

noncomputable def ep604 := nat_lit 1961441175906334297906739912218334170892126658221926912557152580303764517871549415424

noncomputable def ep605 := nat_lit 317847451701823660274950183208426566247826609520192757647478870590511701378990080

noncomputable def ep606 := BSN.log_dyadic_bound 6458455616 22842455616 5 4 ep603 262144 71250 ep604 ep605 152387 29300911232 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6458455616) (BSN.artanhQ 22842455616) 0 4 ep604 ep603 ep605 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz398 := (Real.log (Enclosure.sfrac Bool.false 14650455616 16000000))

noncomputable def ep607 := @Enclosure.Real.IsNear.mulLit_ff qz68 qz398 1 2 0 1 30712905182086319 4503599627370496 800000000513 57000000000000000 30712905182086319 9007199254740992 800000000513 114000000000000000 qz328 (BSN.isNear_log_sfrac 14650455616 16000000 30712905182086319 4503599627370496 800000000513 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14650455616) qz329)) Bool.false 64409630528422688063488 9444732965739290427392 1000000000641250 71250000000000000000 30712905182086319 4503599627370496 800000000513 57000000000000000 (BSN.log_rat_reduce_isNear 14650455616 16000000 9 29300911232 16384000000 152387 262144 24973259072661432 36028797018963968 71250 1000000000000000 rfl rfl rfl rfl (ep606 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep608 := BSN.arctan_dyadic_bound_f 9000 120704 1 0 262144 71250 0 1 1 0 1 1 19509 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 120704) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 120704) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz399 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 120704)))

noncomputable def ep609 := @Enclosure.Real.IsNear.subLit_ff_p qz69 qz399 884279719003555 562949953421312 1 2000000000000000 19509 262144 1 71250 220826032017171546112 842384460514723 562949953421312 1600000000057 114000000000000000 qz70 (ep608 rfl) rfl rfl

noncomputable abbrev qz400 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 120704) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep610 := @Enclosure.Complex.IsNear.re_isNear qz164 Bool.false 30712905182086319 9007199254740992 800000000513 114000000000000000 Bool.false 842384460514723 562949953421312 1600000000057 114000000000000000 (ep602 (@congrArg Complex Complex qz161 qz170 Complex.log (BSN.w_shift_mk qz148 Bool.false 60352 1000 2 qz149 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz170) Bool.false 30712905182086319 9007199254740992 800000000513 114000000000000000 Bool.false 842384460514723 562949953421312 1600000000057 114000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz170)) (@HMul.hMul Real Real Real qz0 qz68 qz398) Bool.false 30712905182086319 9007199254740992 800000000513 114000000000000000 (Enclosure.clog_re_eq 9000 120704 4000 14650455616 16000000 rfl rfl rfl) (ep607 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz170)) qz400 Bool.false 842384460514723 562949953421312 1600000000057 114000000000000000 (Enclosure.clog_im_eq 9000 120704 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz400 (@HSub.hSub Real Real Real qz314 qz69 qz399) Bool.false 842384460514723 562949953421312 1600000000057 114000000000000000 (BSN.arctan_recip 120704 9000 rfl rfl) ep609))))

noncomputable def ep611 := @Enclosure.Real.IsNear.mulLit_ff qz167 qz168 120704 4000 0 1 842384460514723 562949953421312 1600000000057 114000000000000000

noncomputable def ep612 := @Enclosure.Complex.IsNear.im_isNear qz163 Bool.false 7000 4000 0 1 Bool.false 120704 4000 0 1

noncomputable def ep613 := @Enclosure.Complex.IsNear.im_isNear qz164 Bool.false 30712905182086319 9007199254740992 800000000513 114000000000000000 Bool.false 842384460514723 562949953421312 1600000000057 114000000000000000 (ep602 (@congrArg Complex Complex qz161 qz170 Complex.log (BSN.w_shift_mk qz148 Bool.false 60352 1000 2 qz149 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz170) Bool.false 30712905182086319 9007199254740992 800000000513 114000000000000000 Bool.false 842384460514723 562949953421312 1600000000057 114000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz170)) (@HMul.hMul Real Real Real qz0 qz68 qz398) Bool.false 30712905182086319 9007199254740992 800000000513 114000000000000000 (Enclosure.clog_re_eq 9000 120704 4000 14650455616 16000000 rfl rfl rfl) (ep607 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz170)) qz400 Bool.false 842384460514723 562949953421312 1600000000057 114000000000000000 (Enclosure.clog_im_eq 9000 120704 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz400 (@HSub.hSub Real Real Real qz314 qz69 qz399) Bool.false 842384460514723 562949953421312 1600000000057 114000000000000000 (BSN.arctan_recip 120704 9000 rfl rfl) ep609))))

noncomputable abbrev qz401 := (Enclosure.Real.IsNear.const Bool.false 120704 4000)

noncomputable abbrev qz171 := (@ep601 1 (BSN.w_sub_half_mk qz383 Bool.false 60352 1000 2 qz384 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz397 Bool.false 7000 4000 0 1 Bool.false 120704 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz401))

noncomputable def ep614 := @ep597 1508800000053751 3562500000000000000 ep598 176484555809612720859 4503599627370496000 24840800001308891 57000000000000000000 (@ep599 214990336274604233 36028797018963968 5600000003591 456000000000000000 (ep600 qz171) ep610 rfl) (@ep611 794368546265383789 17592186044416000 1508800000053751 3562500000000000000 (ep612 qz171) ep613 rfl) rfl

noncomputable def ep615 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz165 qz168) (@HMul.hMul Real Real Real qz0 qz167 qz166) 5896691223603061 2251799813685248 11200000000399 456000000000000000 28962269586707398817 281474976710656000

noncomputable def ep616 := nat_lit 66877004284083246478291485763567616

noncomputable def ep617 := @Enclosure.Real.IsNear.mulLit_ff qz165 qz168 7000 4000 0 1 842384460514723 562949953421312 1600000000057 114000000000000000

noncomputable def ep618 := @Enclosure.Real.IsNear.mulLit_ff qz167 qz166 120704 4000 0 1 30712905182086319 9007199254740992 800000000513 114000000000000000

noncomputable def ep619 := @ep615 754400000483759 3562500000000000000 ep616 14849677994828890721 140737488355328000 13470400007790019 57000000000000000000 (@ep617 5896691223603061 2251799813685248 11200000000399 456000000000000000 (ep600 qz171) ep613 rfl) (@ep618 28962269586707398817 281474976710656000 754400000483759 3562500000000000000 (ep612 qz171) ep610 rfl) rfl

noncomputable def ep620 := @Enclosure.Complex.IsNear.of_eq qz161 qz170 Bool.false 9000 4000 0 1 Bool.false 120704 4000 0 1 (BSN.w_shift_mk qz148 Bool.false 60352 1000 2 qz149 rfl)

noncomputable abbrev qz402 := (ep620 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 120704 4000) Bool.false 9000 4000 0 1 Bool.false 120704 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 120704 4000)))

noncomputable abbrev qz172 := qz402

noncomputable def ep621 := ep595 (@ep596 57000000000000000000 (ep614 rfl) (ep619 rfl)) qz172 rfl rfl rfl rfl rfl rfl

noncomputable def ep622 := @ep593 13470400007790019 57000000000000000000 (ep621 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz73 (↑qz3) Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 (@ep211 262144 3 262144 (ep213 rfl) (ep215 rfl) rfl rfl) (@ep216 1 0 1 (ep218 rfl) (ep220 rfl) rfl rfl))

noncomputable abbrev qz403 := (@HPow.hPow Complex Int Complex qz476 qz481 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz173 := qz403

noncomputable def ep623 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz161 (@HSub.hSub Int Int Int qz323 qz57 (@HMul.hMul Int Int Int qz324 qz58 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz161 (@HSub.hSub Int Int Int qz323 qz57 (@HMul.hMul Int Int Int qz324 qz58 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76) qz173)) Bool.false 439743 2147483648 3 2147483648

noncomputable def ep624 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz161 (@HSub.hSub Int Int Int qz323 qz57 (@HMul.hMul Int Int Int qz324 qz58 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76) qz173) Bool.false 0 1 0 1 Bool.false

noncomputable def ep625 := @ep624 0 1 0 1 Bool.false 439743 2147483648 3 2147483648 Bool.true 138225883 50331648000 943 50331648000 Bool.false 439743 439743 2147483648 3 2147483648 Bool.true 138225883 138225883 50331648000 943

noncomputable def ep626 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz161 (@HSub.hSub Int Int Int qz323 qz57 (@HMul.hMul Int Int Int qz324 qz58 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep627 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76) qz173 Bool.false 439743 2147483648 3 2147483648 Bool.true 138225883 50331648000 943 50331648000

noncomputable abbrev qz174 := (Complex.re qz403)

noncomputable abbrev qz175 := (Complex.im qz403)

noncomputable def ep628 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz174) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz175) 439743 2147483648 3 2147483648 0 1 0

noncomputable def ep629 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz174 1 12 0 1 1319229 536870912 9 536870912 439743

noncomputable def ep630 := @Enclosure.Complex.IsNear.re_isNear qz173 Bool.false 1319229 536870912 9 536870912 Bool.true 138225883 4194304000 943 4194304000

noncomputable abbrev qz404 := (@HPow.hPow Complex Nat Complex qz477 qz481 1)

noncomputable abbrev qz176 := (@Inv.inv Complex Complex.instInv qz404)

noncomputable def ep631 := @Enclosure.Complex.IsNear.of_eq qz173 qz176 Bool.false 1319229 536870912 9 536870912 Bool.true 138225883 4194304000 943

noncomputable def ep632 := @Enclosure.Complex.IsNear.of_parts qz176 Bool.false 1319229 536870912 9 536870912 Bool.true 138225883 4194304000 943

noncomputable abbrev qz177 := (Complex.re qz404)

noncomputable abbrev qz178 := qz404

noncomputable def ep633 := @Enclosure.Real.IsNear.mulLit_ff qz177 (@Inv.inv Real Real.instInv (@DFunLike.coe qz82 Complex (fun (x : Complex) => Real) qz83 Complex.normSq qz178)) 9000 4000 0 1 146581 134217728 1 134217728

noncomputable def ep634 := @Enclosure.Complex.IsNear.re_isNear qz178 Bool.false 9000 4000 0 1 Bool.false 120704 4000 0 1

noncomputable def ep635 := @Enclosure.Complex.IsNear.of_eq qz178 qz161 Bool.false 9000 4000 0 1 Bool.false 120704 4000 0

noncomputable def ep636 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz82 Complex (fun (x : Complex) => Real) qz83 Complex.normSq qz178)) Bool.false 146581 134217728 1 134217728 146581 134217728 1

noncomputable abbrev qz179 := (Complex.im qz404)

noncomputable def ep637 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz82 Complex (fun (x : Complex) => Real) qz83 Complex.normSq qz178) (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 qz177 qz177) (@HMul.hMul Real Real Real qz0 qz179 qz179)) Bool.false 228913369 250000 0 1

noncomputable def ep638 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz177 qz177) (@HMul.hMul Real Real Real qz0 qz179 qz179) 81 16 0 1 14227984 15625

noncomputable def ep639 := @Enclosure.Real.IsNear.mulLit_ff qz177 qz177 9000 4000 0 1 9000 4000 0 1

noncomputable def ep640 := @Enclosure.Real.IsNear.mulLit_ff qz179 qz179 120704 4000 0 1 120704 4000 0 1

noncomputable def ep641 := @Enclosure.Complex.IsNear.im_isNear qz178 Bool.false 9000 4000 0 1 Bool.false 120704 4000 0 1

noncomputable abbrev qz180 := (ep634 (@ep635 1 (BSN.pow_one_c qz392) qz402))

noncomputable abbrev qz181 := (ep641 (@ep635 1 (BSN.pow_one_c qz392) qz402))

noncomputable def ep642 := @ep638 0 1 228913369 228913369 250000 0 1 (@ep639 81 16 0 1 qz180 qz180 rfl) (@ep640 14227984 15625 0 1 qz181 qz181 rfl)

noncomputable def ep643 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz82 Complex (fun (x : Complex) => Real) qz83 Complex.normSq qz178) 228913369 250000 0 1 73290 73291 67108864 (ep637 (Enclosure.Complex.normSq_eq_mul_add_mul qz178) (ep642 rfl rfl)) rfl

noncomputable def ep644 := @Enclosure.Real.IsNear.of_eq (Complex.re qz176) (@HMul.hMul Real Real Real qz0 qz177 (@Inv.inv Real Real.instInv (@DFunLike.coe qz82 Complex (fun (x : Complex) => Real) qz83 Complex.normSq qz178))) Bool.false 1319229 536870912 9 536870912 (Enclosure.Complex.inv_re_eq_mul qz178) (@ep633 1319229 536870912 9 536870912 qz180 (@ep636 134217728 (ep643 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep645 := @Enclosure.Real.IsNear.of_eq (Complex.im qz176) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz179) (@Inv.inv Real Real.instInv (@DFunLike.coe qz82 Complex (fun (x : Complex) => Real) qz83 Complex.normSq qz178))) Bool.true 138225883 4194304000 943 4194304000 (Enclosure.Complex.inv_im_eq_mul qz178)

noncomputable def ep646 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz179) (@Inv.inv Real Real.instInv (@DFunLike.coe qz82 Complex (fun (x : Complex) => Real) qz83 Complex.normSq qz178)) 120704 4000 0 1 146581 134217728 1

noncomputable def ep647 := @ep646 134217728 138225883 4194304000 943 4194304000 (@Enclosure.Real.IsNear.neg qz179 Bool.false 120704 4000 0 1 qz181) (@ep636 134217728 (ep643 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep648 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz175 0 1 0 1 138225883 4194304000 943 4194304000 0

noncomputable def ep649 := @Enclosure.Complex.IsNear.im_isNear qz173 Bool.false 1319229 536870912 9 536870912 Bool.true 138225883 4194304000 943 4194304000

noncomputable abbrev qz182 := (@ep631 4194304000 (BSN.zpow_one_sub_two_mul qz392 1 1 rfl rfl) (@ep632 4194304000 ep644 (ep645 ep647)))

noncomputable def ep650 := @ep628 1 439743 439743 2147483648 3 2147483648 (@ep629 2147483648 3 2147483648 ep230 (ep630 qz182) rfl) (@ep648 1 0 1 ep250 (ep649 qz182) rfl) rfl

noncomputable def ep651 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz175) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz174) 138225883 50331648000 943 50331648000 0 1 0

noncomputable def ep652 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz175 1 12 0 1 138225883 4194304000 943 4194304000 138225883

noncomputable def ep653 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz75)) qz76)) qz174 0 1 0 1 1319229 536870912 9 536870912 0

noncomputable def ep654 := @ep651 1 138225883 138225883 50331648000 943 50331648000 (@ep652 50331648000 943 50331648000 ep230 (ep649 qz182) rfl) (@ep653 1 0 1 ep250 (ep630 qz182) rfl) rfl

noncomputable def ep655 := @ep625 50331648000 (@ep626 0 1 0 1 (BSN.stirling_sum_base qz161) qz89) (ep627 (ep650 rfl) (ep654 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep656 := @ep590 6361438223181519623 84442493013196800 6897391587435755353 29184000000000000000000 (ep622 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep623 Bool.true 138225883 50331648000 943 50331648000 (BSN.stirling_sum_succ qz161 0 1 rfl) (ep655 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep657 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz148 2) Bool.false 30691954331616431 4503599627370496 800000000513 57000000000000000 Bool.false 870296379229603 281474976710656

noncomputable abbrev qz183 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz269 qz393 qz334))

noncomputable def ep658 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz148 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz148 1) qz183) Bool.false 30691954331616431 4503599627370496 800000000513 57000000000000000 Bool.false 870296379229603 281474976710656 1600000000057 57000000000000000

noncomputable def ep659 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz148 1) qz183 Bool.false 30688252069807279 9007199254740992 800000000513 114000000000000000 Bool.false 879617532003747 562949953421312 1600000000057 114000000000000000 Bool.false

noncomputable def ep660 := nat_lit 552897096364560157082871192879104

noncomputable def ep661 := nat_lit 979866612300082986369282998272

noncomputable abbrev qz184 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz269 qz393 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep662 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz148 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz148 0) qz184) Bool.false 30688252069807279 9007199254740992 800000000513 114000000000000000 Bool.false 879617532003747 562949953421312 1600000000057 114000000000000000

noncomputable def ep663 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz148 0) qz184 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz405 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz169))

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq qz184 qz405 Bool.false 30688252069807279 9007199254740992 800000000513 114000000000000000 Bool.false 879617532003747 562949953421312 1600000000057 114000000000000000

noncomputable def ep665 := nat_lit 68105894979878015064403015378539144402432005356431442138364854372822784161597850910720

noncomputable def ep666 := nat_lit 1871592755267475423265824118880388963416370740797488330739904986419950491590589415424

noncomputable def ep667 := nat_lit 287682604574346103404375002279557290027675582567839773770070896710461218178990080

noncomputable def ep668 := BSN.log_dyadic_bound 6378455616 22762455616 5 4 ep665 262144 71250 ep666 ep667 150952 29140911232 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6378455616) (BSN.artanhQ 22762455616) 0 4 ep666 ep665 ep667 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep669 := @Enclosure.Real.IsNear.mulLit_ff qz68 (Real.log (Enclosure.sfrac Bool.false 14570455616 16000000)) 1 2 0 1 30688252069807279 4503599627370496 800000000513 57000000000000000 30688252069807279 9007199254740992 800000000513 114000000000000000 qz328 (BSN.isNear_log_sfrac 14570455616 16000000 30688252069807279 4503599627370496 800000000513 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14570455616) qz329)) Bool.false 64357929204700474769408 9444732965739290427392 1000000000641250 71250000000000000000 30688252069807279 4503599627370496 800000000513 57000000000000000 (BSN.log_rat_reduce_isNear 14570455616 16000000 9 29140911232 16384000000 150952 262144 24973259072661432 36028797018963968 71250 1000000000000000 rfl rfl rfl rfl (ep668 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep670 := BSN.arctan_dyadic_bound_f 1000 120704 1 0 262144 71250 0 1 1 0 1 1 2171 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 120704) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 120704) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz406 := (@Nat.cast Real Real.instNatCast 120704)

noncomputable def ep671 := @Enclosure.Real.IsNear.subLit_ff_p qz69 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz340 qz406)) 884279719003555 562949953421312 1 2000000000000000 2171 262144 1 71250 230586458309590253568 879617532003747 562949953421312 1600000000057 114000000000000000 qz70 (ep670 rfl) rfl rfl

noncomputable abbrev qz185 := (@HAdd.hAdd Complex Complex Complex qz269 qz393 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz407 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz169)

noncomputable def ep672 := @ep663 30688252069807279 9007199254740992 800000000513 114000000000000000 Bool.false 879617532003747 562949953421312 1600000000057 114000000000000000 Bool.false 30688252069807279 30688252069807279 9007199254740992 800000000513 114000000000000000 Bool.false 879617532003747 879617532003747 562949953421312 1600000000057 114000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz148 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz148) qz89) (ep664 (@congrArg Complex Complex qz185 qz407 Complex.log (BSN.w_shift_mk qz148 Bool.false 60352 1000 0 qz149 rfl)) (@Enclosure.Complex.IsNear.of_parts qz405 Bool.false 30688252069807279 9007199254740992 800000000513 114000000000000000 Bool.false 879617532003747 562949953421312 1600000000057 114000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz405) (@HMul.hMul Real Real Real qz0 qz68 (Real.log (Enclosure.sfrac Bool.false 14570455616 16000000))) Bool.false 30688252069807279 9007199254740992 800000000513 114000000000000000 (Enclosure.clog_re_eq 1000 120704 4000 14570455616 16000000 rfl rfl rfl) (ep669 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz405) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz406 qz340)) Bool.false 879617532003747 562949953421312 1600000000057 114000000000000000 (Enclosure.clog_im_eq 1000 120704 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz406 qz340)) (@HSub.hSub Real Real Real qz314 qz69 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz340 qz406))) Bool.false 879617532003747 562949953421312 1600000000057 114000000000000000 (BSN.arctan_recip 120704 1000 rfl rfl) ep671)))) rfl rfl

noncomputable abbrev qz408 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz169))

noncomputable def ep673 := @Enclosure.Complex.IsNear.of_eq qz183 qz408 Bool.false 30695656593425583 9007199254740992 800000000513 114000000000000000 Bool.false 860975226455459 562949953421312 1600000000057 114000000000000000

noncomputable def ep674 := nat_lit 68682488708186560100061200588533924680627170577258276164041487366404299977902490910720

noncomputable def ep675 := nat_lit 1898182499635882510605279578334478209367970719490997723528825173760316971474877415424

noncomputable def ep676 := nat_lit 296457137488278651601100652164901512274914944052175586279089603764716363138990080

noncomputable def ep677 := BSN.log_dyadic_bound 6402455616 22786455616 5 4 ep674 262144 71250 ep675 ep676 151383 29188911232 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6402455616) (BSN.artanhQ 22786455616) 0 4 ep675 ep674 ep676 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep678 := @Enclosure.Real.IsNear.mulLit_ff qz68 (Real.log (Enclosure.sfrac Bool.false 14594455616 16000000)) 1 2 0 1 30695656593425583 4503599627370496 800000000513 57000000000000000 30695656593425583 9007199254740992 800000000513 114000000000000000 qz328 (BSN.isNear_log_sfrac 14594455616 16000000 30695656593425583 4503599627370496 800000000513 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14594455616) qz329)) Bool.false 64373457616215648239616 9444732965739290427392 1000000000641250 71250000000000000000 30695656593425583 4503599627370496 800000000513 57000000000000000 (BSN.log_rat_reduce_isNear 14594455616 16000000 9 29188911232 16384000000 151383 262144 24973259072661432 36028797018963968 71250 1000000000000000 rfl rfl rfl rfl (ep677 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep679 := BSN.arctan_dyadic_bound_f 5000 120704 1 0 262144 71250 0 1 1 0 1 1 10852 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 120704) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 120704) 0 0 rfl) rfl rfl rfl

noncomputable def ep680 := @Enclosure.Real.IsNear.subLit_ff_p qz69 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz344 qz406)) 884279719003555 562949953421312 1 2000000000000000 10852 262144 1 71250 225699489763939844096 860975226455459 562949953421312 1600000000057 114000000000000000 qz70 (ep679 rfl) rfl rfl

noncomputable abbrev qz186 := (@HAdd.hAdd Complex Complex Complex qz269 qz393 qz334)

noncomputable abbrev qz409 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz169)

noncomputable def ep681 := @ep659 30695656593425583 9007199254740992 800000000513 114000000000000000 Bool.false 860975226455459 562949953421312 1600000000057 114000000000000000 Bool.false ep660 30691954331616431 4503599627370496 800000000513 57000000000000000 Bool.false ep661 870296379229603 281474976710656 1600000000057 57000000000000000 (ep662 (BSN.log_sum_c_succ qz148 0 1 rfl) (ep672 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep673 (@congrArg Complex Complex qz186 qz409 Complex.log (BSN.w_shift_mk qz148 Bool.false 60352 1000 1 qz149 rfl)) (@Enclosure.Complex.IsNear.of_parts qz408 Bool.false 30695656593425583 9007199254740992 800000000513 114000000000000000 Bool.false 860975226455459 562949953421312 1600000000057 114000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz408) (@HMul.hMul Real Real Real qz0 qz68 (Real.log (Enclosure.sfrac Bool.false 14594455616 16000000))) Bool.false 30695656593425583 9007199254740992 800000000513 114000000000000000 (Enclosure.clog_re_eq 5000 120704 4000 14594455616 16000000 rfl rfl rfl) (ep678 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz408) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz406 qz344)) Bool.false 860975226455459 562949953421312 1600000000057 114000000000000000 (Enclosure.clog_im_eq 5000 120704 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz406 qz344)) (@HSub.hSub Real Real Real qz314 qz69 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz344 qz406))) Bool.false 860975226455459 562949953421312 1600000000057 114000000000000000 (BSN.arctan_recip 120704 5000 rfl rfl) ep680)))) rfl rfl

noncomputable def ep682 := @ep583 29184000000000000000000 Bool.false 30691954331616431 4503599627370496 800000000513 57000000000000000 Bool.false 870296379229603 281474976710656 1600000000057 57000000000000000 Bool.true ep584 213170176867559519859 4503599627370496000 215393835928157352947 466944000000000000000000 Bool.false ep585 6100349309412638723 84442493013196800 2572197195821646451 9728000000000000000000 (@ep586 4503599627370496000 208840235923954856947 466944000000000000000000 Bool.false 6361438223181519623 84442493013196800 6897391587435755353 29184000000000000000000 (BSN.logGammaStirling_unfold 1 qz161) (ep656 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep657 1600000000057 57000000000000000 (BSN.log_sum_c_eq qz148 2) (ep658 (BSN.log_sum_c_succ qz148 1 2 rfl) (ep681 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz187 := (@HDiv.hDiv Real Real Real qz266 qz383 (2 : Real))

noncomputable def ep683 := @Enclosure.Real.IsNear.mulLit_ff qz187 (Real.log Real.pi) 60352 2000 0 1 75021 65536 1 65536 70744803 2048000 943 2048000 (@Enclosure.Real.IsNear.of_eq qz187 (Enclosure.sfrac Bool.false 60352 2000) Bool.false 60352 2000 0 1 (BSN.t_half_eq qz148 Bool.false 60352 1000 qz149) (Enclosure.Real.IsNear.const Bool.false 60352 2000)) EMRow13.d5 rfl

noncomputable def ep684 := @ep580 943 2048000 ep581 15917109015208984591 422212465065984000 7051447195821646451 9728000000000000000000 (@ep582 2572197195821646451 9728000000000000000000 (ep682 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep683 rfl rfl

noncomputable def ep685 := BSN.cos_dyadic_bound_f 92211 536870912 1 0 262144 71320 0 1 1 0 1 1 262143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 92211) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 92211) qz284 0 0 rfl) rfl rfl

noncomputable def ep686 := @ep578 262144 Bool.false 262143 262144 1 35625 (@ep579 9882641 262144 191 262144 ep684 rfl) (Enclosure.sfrac_false_div 9882641 262144) (BSN.cos_reduce0 qz394 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6488787537438441472) qz33) 226375608064910080 72057594037927936 Bool.false 262143 262144 6 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 9882641 262144 226375608064910080 72057594037927936 6 6488787537438441472 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 262143 262144 6488787537438441472 37778931862957161709568 92211 536870912 71320 71250 (ep685 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep687 := nat_lit 28602665274376804628969747

noncomputable def ep688 := nat_lit 2972532442030627880960000000

noncomputable abbrev qz188 := qz382

noncomputable abbrev qz410 := (@HPow.hPow Complex Complex Complex qz465 (@Nat.cast Complex Complex.instNatCast 16) qz479)

noncomputable abbrev qz189 := qz410

noncomputable abbrev qz411 := (@Nat.cast Complex Complex.instNatCast 16)

noncomputable abbrev qz190 := (@HAdd.hAdd Complex Complex Complex qz269 (@HDiv.hDiv Complex Complex Complex qz319 qz411 (@HSub.hSub Complex Complex Complex qz311 qz381 (1 : Complex))) qz318)

noncomputable abbrev qz191 := qz411

noncomputable def ep689 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz139 1 16) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 16, @HPow.hPow Complex Complex Complex qz95 (@Nat.cast Complex Complex.instNatCast n) qz188) (@HMul.hMul Complex Complex Complex qz46 qz189 (@HAdd.hAdd Complex Complex Complex qz5 qz190 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) Bool.false 439605899820303002681 782245379481744179200 ep575

noncomputable def ep690 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 16, @HPow.hPow Complex Complex Complex qz95 (@Nat.cast Complex Complex.instNatCast n) qz188) (@HMul.hMul Complex Complex Complex qz46 qz189 (@HAdd.hAdd Complex Complex Complex qz5 qz190 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) Bool.false 45063010267 68719476736 1209774593137 128849018880000

noncomputable def ep691 := nat_lit 2128197266659862986797241

noncomputable def ep692 := nat_lit 8917597326091883642880000000

noncomputable def ep693 := nat_lit 30209487405709658773207925129216

noncomputable def ep694 := nat_lit 10487362251810306139176795373568

noncomputable def ep695 := @ep690 Bool.true 4705330649 68719476736 1209076789387 128849018880000 Bool.true 73353936913037473469 782245379481744179200 33239024561844106206119 ep576 Bool.false 838199320256107820103 10012740857366325493760 ep691 ep692 Bool.false ep693 439605899820303002681 782245379481744179200 ep575 ep576 Bool.false ep694 152611206457518072263 10012740857366325493760

noncomputable def ep696 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 16, @HPow.hPow Complex Complex Complex qz95 (@Nat.cast Complex Complex.instNatCast n) qz188) (BSN.headSumC qz139 16) Bool.false 45063010267 68719476736 1209774593137 128849018880000 Bool.true 4705330649 68719476736 1209076789387

noncomputable abbrev qz192 := (@HPow.hPow Complex Complex Complex qz270 qz347 qz382)

noncomputable def ep697 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz139 16) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz139 15) qz192) Bool.false 45063010267 68719476736 1209774593137 128849018880000 Bool.true 4705330649 68719476736 1209076789387 128849018880000

noncomputable def ep698 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz139 15) qz192 Bool.false 27367037757 68719476736 21885625158319 2448131358720000 Bool.true 1705901307 34359738368 5470250017861 612032839680000 Bool.false

noncomputable abbrev qz193 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 14) qz382)

noncomputable def ep699 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz139 15) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz139 14) qz193) Bool.false 27367037757 68719476736 21885625158319 2448131358720000 Bool.true 1705901307 34359738368 5470250017861 612032839680000

noncomputable def ep700 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz139 14) qz193 Bool.false 19030469307 34359738368 10374311764883 1224065679360000 Bool.false 2879934457 17179869184 10370921832383 1224065679360000 Bool.true

noncomputable abbrev qz194 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 13) qz382)

noncomputable def ep701 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz139 14) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz139 13) qz194) Bool.false 19030469307 34359738368 10374311764883 1224065679360000 Bool.false 2879934457 17179869184 10370921832383 1224065679360000

noncomputable def ep702 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz139 13) qz194 Bool.false 6309160203 8589934592 815344777473 102005473280000 Bool.true 1471733911 34359738368 101877551481 12750684160000 Bool.true

noncomputable abbrev qz195 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 12) qz382)

noncomputable def ep703 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz139 13) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz139 12) qz195) Bool.false 6309160203 8589934592 815344777473 102005473280000 Bool.true 1471733911 34359738368 101877551481 12750684160000

noncomputable def ep704 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz139 12) qz195 Bool.false 37047552849 68719476736 18342415224383 2448131358720000 Bool.true 4386920843 17179869184 9167037830629 1224065679360000 Bool.false

noncomputable abbrev qz196 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 11) qz382)

noncomputable def ep705 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz139 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz139 11) qz196) Bool.false 37047552849 68719476736 18342415224383 2448131358720000 Bool.true 4386920843 17179869184 9167037830629 1224065679360000

noncomputable def ep706 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz139 11) qz196 Bool.false 8379555489 34359738368 2843253302833 408021893120000 Bool.true 6671641403 34359738368 355383953401 51002736640000 Bool.false

noncomputable abbrev qz197 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 10) qz382)

noncomputable def ep707 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz139 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz139 10) qz197) Bool.false 8379555489 34359738368 2843253302833 408021893120000 Bool.true 6671641403 34359738368 355383953401 51002736640000

noncomputable def ep708 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz139 10) qz197 Bool.false 640535401 68719476736 15716669286811 2448131358720000 Bool.false 615668073 34359738368 7858121374343 1224065679360000 Bool.false

noncomputable abbrev qz198 := (@HPow.hPow Complex Complex Complex qz270 (@Nat.cast Complex Complex.instNatCast 9) qz382)

noncomputable def ep709 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz139 10) (@HAdd.hAdd Complex Complex Complex qz5 qz138 qz198) Bool.false 640535401 68719476736 15716669286811 2448131358720000 Bool.false 615668073 34359738368 7858121374343 1224065679360000

noncomputable def ep710 := @Enclosure.Complex.IsNear.addLitP qz138 qz198 Bool.true 8727816397 34359738368 2383517848613 408021893120000 Bool.false 7637605233 34359738368 297965263811 51002736640000 Bool.false

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz263 qz383 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep711 := @Enclosure.Complex.IsNear.of_eq qz198 (Complex.mk (@HMul.hMul Real Real Real qz0 qz108 (Real.cos qz199)) (@HMul.hMul Real Real Real qz0 qz108 (@Neg.neg Real Real.instNeg (Real.sin qz199)))) Bool.false 18096168195 68719476736 1415562195133 2448131358720000 Bool.true 877742145 4294967296 706955042879 1224065679360000 (BSN.cpow_neg_s_mk qz148 60352 1000 9 qz149 rfl)

noncomputable def ep712 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz110 60352 1000 0 1 9895417793173221 4503599627370496 1600000000171 57000000000000000 9331378978962347403 70368744177664000 1508800000161253 890625000000000000 qz150 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz350) Bool.false 10376097607894403383296 4722366482869645213696 1000000000106875 35625000000000000000 9895417793173221 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 15438 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep314 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep713 := nat_lit 15761424660507609296510675929297041

noncomputable def ep714 := BSN.cos_dyadic_bound_f 354322611 536870912 2 1 262144 71320 ep713 ep61 ep713 ep713 ep62 ep713 207095 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 354322611) qz283 0 1 ep713 ep61 ep713 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 354322611) qz284 0 1 ep713 ep62 ep713 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz412 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 34762095) qz31)

noncomputable def ep715 := @Enclosure.Real.IsNear.cos_image qz199 qz412 Bool.false 34762095 262144 445 262144 Bool.false 207095 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz199 Bool.false 9331378978962347403 70368744177664000 1508800000161253 890625000000000000 34762095 262144 445 262144 (ep712 rfl) rfl) (Enclosure.sfrac_false_div 34762095 262144) (BSN.cos_reduce0 qz412 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24933237188074835804160) qz33) 226375608064910080 72057594037927936 Bool.false 207095 262144 21 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 34762095 262144 226375608064910080 72057594037927936 21 24933237188074835804160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 207095 262144 24933237188074835804160 37778931862957161709568 354322611 536870912 71320 71250 (ep714 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep716 := BSN.sin_dyadic_bound_f 354322611 536870912 2 1 262144 71320 ep713 ep57 ep713 ep713 ep58 ep713 160720 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 354322611) qz278 0 1 ep713 ep57 ep713 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 354322611) qz279 0 1 ep713 ep58 ep713 rfl rfl rfl rfl) rfl rfl

noncomputable def ep717 := @Enclosure.Real.IsNear.sin_image qz199 qz412 Bool.false 34762095 262144 445 262144 Bool.false 160720 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz199 Bool.false 9331378978962347403 70368744177664000 1508800000161253 890625000000000000 34762095 262144 445 262144 (ep712 rfl) rfl) (Enclosure.sfrac_false_div 34762095 262144) (BSN.sin_reduce0 qz412 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24933237188074835804160) qz33) 226375608064910080 72057594037927936 Bool.false 160720 262144 21 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 34762095 262144 226375608064910080 72057594037927936 21 24933237188074835804160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 160720 262144 24933237188074835804160 37778931862957161709568 354322611 536870912 71320 71250 (ep716 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep718 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz108 (Real.cos qz199)) (@HMul.hMul Real Real Real qz0 qz108 (@Neg.neg Real Real.instNeg (Real.sin qz199))) Bool.false 18096168195 68719476736 1415562195133 2448131358720000 Bool.true 877742145 4294967296 706955042879 1224065679360000 (@Enclosure.Real.IsNear.mulLit_ff qz108 (Real.cos qz199) 87381 262144 1 262144 207095 262144 16115269 9338880000 18096168195 68719476736 1415562195133 2448131358720000 qz352 (@Enclosure.Real.IsNear.recentre' (Real.cos qz199) Bool.false 207095 262144 16115269 9338880000 207095 262144 16115269 9338880000 (ep715 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz108 (@Neg.neg Real Real.instNeg (Real.sin qz199)) 87381 262144 1 262144 10045 16384 16115269 9338880000 877742145 4294967296 706955042879 1224065679360000 qz352 (@Enclosure.Real.IsNear.neg (Real.sin qz199) Bool.false 10045 16384 16115269 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz199) Bool.false 160720 262144 16115269 9338880000 10045 16384 16115269 9338880000 (ep717 rfl rfl) rfl)) rfl)

noncomputable def ep719 := @ep710 18096168195 68719476736 1415562195133 2448131358720000 Bool.true 877742145 4294967296 706955042879 1224065679360000 Bool.false 22008628793801965568 640535401 68719476736 15716669286811 2448131358720000 Bool.false 2644274238726340608 615668073 34359738368 7858121374343 1224065679360000 EMRow13.d10 (ep711 ep718) rfl rfl

noncomputable abbrev qz200 := (@HMul.hMul Real Real Real qz263 qz383 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep720 := @Enclosure.Complex.IsNear.of_eq qz197 (Complex.mk (@HMul.hMul Real Real Real qz0 qz111 (Real.cos qz200)) (@HMul.hMul Real Real Real qz0 qz111 (@Neg.neg Real Real.instNeg (Real.sin qz200)))) Bool.false 16118575577 68719476736 1342850530187 2448131358720000 Bool.true 1821827369 8589934592 671093507281 1224065679360000 (BSN.cpow_neg_s_mk qz148 60352 1000 10 qz149 rfl)

noncomputable def ep721 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz113 60352 1000 0 1 10369891420296933 4503599627370496 1600000000171 57000000000000000 9778807609340007819 70368744177664000 1508800000161253 890625000000000000 qz150 (BSN.isNear_log_sfrac 10 1 10369891420296933 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz354) Bool.false 10873619265929276817408 4722366482869645213696 1000000000106875 35625000000000000000 10369891420296933 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 29247 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep325 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep722 := nat_lit 24263456258469973556505009485037121

noncomputable def ep723 := BSN.cos_dyadic_bound_f 394673681 536870912 2 1 262144 71320 ep722 ep61 ep722 ep722 ep62 ep722 194441 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 394673681) qz283 0 1 ep722 ep61 ep722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 394673681) qz284 0 1 ep722 ep62 ep722 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz413 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 36428897) qz31)

noncomputable def ep724 := @Enclosure.Real.IsNear.cos_image qz200 qz413 Bool.false 36428897 262144 445 262144 Bool.false 194441 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz200 Bool.false 9778807609340007819 70368744177664000 1508800000161253 890625000000000000 36428897 262144 445 262144 (ep721 rfl) rfl) (Enclosure.sfrac_false_div 36428897 262144) (BSN.cos_reduce0 qz413 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 27772691301016402919424) qz33) 226375608064910080 72057594037927936 Bool.false 194441 262144 22 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 36428897 262144 226375608064910080 72057594037927936 22 27772691301016402919424 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 194441 262144 27772691301016402919424 37778931862957161709568 394673681 536870912 71320 71250 (ep723 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep725 := BSN.sin_dyadic_bound_f 394673681 536870912 2 1 262144 71320 ep722 ep57 ep722 ep722 ep58 ep722 175816 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 394673681) qz278 0 1 ep722 ep57 ep722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 394673681) qz279 0 1 ep722 ep58 ep722 rfl rfl rfl rfl) rfl rfl

noncomputable def ep726 := @Enclosure.Real.IsNear.sin_image qz200 qz413 Bool.false 36428897 262144 445 262144 Bool.false 175816 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz200 Bool.false 9778807609340007819 70368744177664000 1508800000161253 890625000000000000 36428897 262144 445 262144 (ep721 rfl) rfl) (Enclosure.sfrac_false_div 36428897 262144) (BSN.sin_reduce0 qz413 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 27772691301016402919424) qz33) 226375608064910080 72057594037927936 Bool.false 175816 262144 22 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 36428897 262144 226375608064910080 72057594037927936 22 27772691301016402919424 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 175816 262144 27772691301016402919424 37778931862957161709568 394673681 536870912 71320 71250 (ep725 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep727 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz111 (Real.cos qz200)) (@HMul.hMul Real Real Real qz0 qz111 (@Neg.neg Real Real.instNeg (Real.sin qz200))) Bool.false 16118575577 68719476736 1342850530187 2448131358720000 Bool.true 1821827369 8589934592 671093507281 1224065679360000 (@Enclosure.Real.IsNear.mulLit_ff qz111 (Real.cos qz200) 82897 262144 1 262144 194441 262144 16115269 9338880000 16118575577 68719476736 1342850530187 2448131358720000 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz200) Bool.false 194441 262144 16115269 9338880000 194441 262144 16115269 9338880000 (ep724 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz111 (@Neg.neg Real Real.instNeg (Real.sin qz200)) 82897 262144 1 262144 21977 32768 16115269 9338880000 1821827369 8589934592 671093507281 1224065679360000 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz200) Bool.false 21977 32768 16115269 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz200) Bool.false 175816 262144 16115269 9338880000 21977 32768 16115269 9338880000 (ep726 rfl rfl) rfl)) rfl)

noncomputable def ep728 := @ep708 16118575577 68719476736 1342850530187 2448131358720000 Bool.true 1821827369 8589934592 671093507281 1224065679360000 Bool.false 1151677336968713207808 8379555489 34359738368 2843253302833 408021893120000 Bool.true 57308963273049112576 6671641403 34359738368 355383953401 51002736640000 (ep709 (BSN.head_sum_c_succ qz139 9 10 rfl rfl) (ep719 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep720 ep727) rfl rfl

noncomputable abbrev qz201 := (@HMul.hMul Real Real Real qz263 qz383 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep729 := @Enclosure.Complex.IsNear.of_eq qz196 (Complex.mk (@HMul.hMul Real Real Real qz0 qz114 (Real.cos qz201)) (@HMul.hMul Real Real Real qz0 qz114 (@Neg.neg Real Real.instNeg (Real.sin qz201)))) Bool.false 20288441871 68719476736 13504162183 25769803776000 Bool.true 2102200283 34359738368 6713925779 12884901888000 (BSN.cpow_neg_s_mk qz148 60352 1000 11 qz149 rfl)

noncomputable def ep730 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz116 60352 1000 0 1 10799147631728357 4503599627370496 1600000000171 57000000000000000 10183596216719840651 70368744177664000 1508800000161253 890625000000000000 qz150 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz358) Bool.false 11323727027087193669632 4722366482869645213696 1000000000106875 35625000000000000000 10799147631728357 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 41740 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep336 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep731 := nat_lit 144851504534316515466907247290896

noncomputable def ep732 := BSN.cos_dyadic_bound_f 109706094 536870912 2 1 262144 71320 ep731 ep61 ep731 ep731 ep62 ep731 256689 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 109706094) qz283 0 1 ep731 ep61 ep731 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 109706094) qz284 0 1 ep731 ep62 ep731 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz414 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9484213) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep733 := @Enclosure.Real.IsNear.cos_image qz201 qz414 Bool.false 9484213 65536 445 262144 Bool.false 256689 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz201 Bool.false 10183596216719840651 70368744177664000 1508800000161253 890625000000000000 9484213 65536 445 262144 (ep730 rfl) rfl) (Enclosure.sfrac_false_div 9484213 65536) (BSN.cos_reduce0 qz414 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1929970033418123083776) qz282) 226375608064910080 72057594037927936 Bool.false 256689 262144 23 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 9484213 65536 226375608064910080 72057594037927936 23 1929970033418123083776 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 256689 262144 1929970033418123083776 9444732965739290427392 109706094 536870912 71320 71250 (ep732 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep734 := BSN.sin_dyadic_bound_f 109706094 536870912 1 0 262144 71320 0 1 1 0 1 1 53194 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 109706094) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 109706094) qz279 0 0 rfl) rfl rfl

noncomputable def ep735 := @Enclosure.Real.IsNear.sin_image qz201 qz414 Bool.false 9484213 65536 445 262144 Bool.false 53194 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz201 Bool.false 10183596216719840651 70368744177664000 1508800000161253 890625000000000000 9484213 65536 445 262144 (ep730 rfl) rfl) (Enclosure.sfrac_false_div 9484213 65536) (BSN.sin_reduce0 qz414 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1929970033418123083776) qz282) 226375608064910080 72057594037927936 Bool.false 53194 262144 23 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 9484213 65536 226375608064910080 72057594037927936 23 1929970033418123083776 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 53194 262144 1929970033418123083776 9444732965739290427392 109706094 536870912 71320 71250 (ep734 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep736 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz114 (Real.cos qz201)) (@HMul.hMul Real Real Real qz0 qz114 (@Neg.neg Real Real.instNeg (Real.sin qz201))) Bool.false 20288441871 68719476736 13504162183 25769803776000 Bool.true 2102200283 34359738368 6713925779 12884901888000 (@Enclosure.Real.IsNear.mulLit_ff qz114 (Real.cos qz201) 79039 262144 1 262144 256689 262144 16115269 9338880000 20288441871 68719476736 13504162183 25769803776000 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz201) Bool.false 256689 262144 16115269 9338880000 256689 262144 16115269 9338880000 (ep733 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz114 (@Neg.neg Real Real.instNeg (Real.sin qz201)) 79039 262144 1 262144 26597 131072 16115269 9338880000 2102200283 34359738368 6713925779 12884901888000 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz201) Bool.false 26597 131072 16115269 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz201) Bool.false 53194 262144 16115269 9338880000 26597 131072 16115269 9338880000 (ep735 rfl rfl) rfl)) rfl)

noncomputable def ep737 := @ep706 20288441871 68719476736 13504162183 25769803776000 Bool.true 2102200283 34359738368 6713925779 12884901888000 Bool.false 1272944223066293010432 37047552849 68719476736 18342415224383 2448131358720000 Bool.true 301466904813212008448 4386920843 17179869184 9167037830629 1224065679360000 (ep707 (BSN.head_sum_c_succ qz139 10 11 rfl rfl) (ep728 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep729 ep736) rfl rfl

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz263 qz383 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep738 := @Enclosure.Complex.IsNear.of_eq qz195 (Complex.mk (@HMul.hMul Real Real Real qz0 qz117 (Real.cos qz202)) (@HMul.hMul Real Real Real qz0 qz117 (@Neg.neg Real Real.instNeg (Real.sin qz202)))) Bool.false 13425728775 68719476736 1225859434969 2448131358720000 Bool.false 7302107775 34359738368 613207111547 1224065679360000 (BSN.cpow_neg_s_mk qz148 60352 1000 12 qz149 rfl)

noncomputable def ep739 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz119 60352 1000 0 1 11191020447815397 4503599627370496 1600000000171 57000000000000000 10553132282289919371 70368744177664000 1508800000161253 890625000000000000 qz150 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz362) Bool.false 11734635457088477724672 4722366482869645213696 1000000000106875 35625000000000000000 11191020447815397 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 53145 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep351 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep740 := nat_lit 25369795927391548778418123744943921

noncomputable def ep741 := BSN.sin_dyadic_bound_f 399097717 536870912 2 1 262144 71320 ep740 ep57 ep740 ep740 ep58 ep740 177413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 399097717) qz278 0 1 ep740 ep57 ep740 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 399097717) qz279 0 1 ep740 ep58 ep740 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz415 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39313481) qz31)

noncomputable def ep742 := @Enclosure.Real.IsNear.cos_image qz202 qz415 Bool.false 39313481 262144 445 262144 Bool.false 177413 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz202 Bool.false 10553132282289919371 70368744177664000 1508800000161253 890625000000000000 39313481 262144 445 262144 (ep739 rfl) rfl) (Enclosure.sfrac_false_div 39313481 262144) (BSN.cos_reduce3 qz415 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28084005177646521516032) qz33) 226375608064910080 72057594037927936 Bool.false 177413 262144 23 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q3 39313481 262144 226375608064910080 72057594037927936 23 28084005177646521516032 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 177413 262144 28084005177646521516032 37778931862957161709568 399097717 536870912 71320 71250 (ep741 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep743 := BSN.cos_dyadic_bound_f 399097717 536870912 2 1 262144 71320 ep740 ep61 ep740 ep740 ep62 ep740 192986 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 399097717) qz283 0 1 ep740 ep61 ep740 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 399097717) qz284 0 1 ep740 ep62 ep740 rfl rfl rfl rfl) rfl rfl

noncomputable def ep744 := @Enclosure.Real.IsNear.sin_image qz202 qz415 Bool.false 39313481 262144 445 262144 Bool.true 192986 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz202 Bool.false 10553132282289919371 70368744177664000 1508800000161253 890625000000000000 39313481 262144 445 262144 (ep739 rfl) rfl) (Enclosure.sfrac_false_div 39313481 262144) (BSN.sin_reduce3 qz415 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28084005177646521516032) qz33) 226375608064910080 72057594037927936 Bool.false 192986 262144 23 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q3 39313481 262144 226375608064910080 72057594037927936 23 28084005177646521516032 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 192986 262144 28084005177646521516032 37778931862957161709568 399097717 536870912 71320 71250 (ep743 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep745 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz117 (Real.cos qz202)) (@HMul.hMul Real Real Real qz0 qz117 (@Neg.neg Real Real.instNeg (Real.sin qz202))) Bool.false 13425728775 68719476736 1225859434969 2448131358720000 Bool.false 7302107775 34359738368 613207111547 1224065679360000 (@Enclosure.Real.IsNear.mulLit_ff qz117 (Real.cos qz202) 75675 262144 1 262144 177413 262144 16115269 9338880000 13425728775 68719476736 1225859434969 2448131358720000 qz364 (@Enclosure.Real.IsNear.recentre' (Real.cos qz202) Bool.false 177413 262144 16115269 9338880000 177413 262144 16115269 9338880000 (ep742 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz117 (@Neg.neg Real Real.instNeg (Real.sin qz202)) 75675 262144 1 262144 96493 131072 16115269 9338880000 7302107775 34359738368 613207111547 1224065679360000 qz364 (@Enclosure.Real.IsNear.neg (Real.sin qz202) Bool.true 96493 131072 16115269 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz202) Bool.true 192986 262144 16115269 9338880000 96493 131072 16115269 9338880000 (ep744 rfl rfl) rfl)) rfl)

noncomputable def ep746 := @ep704 13425728775 68719476736 1225859434969 2448131358720000 Bool.false 7302107775 34359738368 613207111547 1224065679360000 Bool.false 3468497502350044299264 6309160203 8589934592 815344777473 102005473280000 Bool.true 25284196064636698624 1471733911 34359738368 101877551481 12750684160000 (ep705 (BSN.head_sum_c_succ qz139 11 12 rfl rfl) (ep737 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep738 ep745) rfl rfl

noncomputable abbrev qz203 := (@HMul.hMul Real Real Real qz263 qz383 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep747 := @Enclosure.Complex.IsNear.of_eq qz194 (Complex.mk (@HMul.hMul Real Real Real qz0 qz120 (Real.cos qz203)) (@HMul.hMul Real Real Real qz0 qz120 (@Neg.neg Real Real.instNeg (Real.sin qz203)))) Bool.true 6206171505 34359738368 590174435207 1224065679360000 Bool.false 7231602825 34359738368 590676890207 1224065679360000 (BSN.cpow_neg_s_mk qz148 60352 1000 13 qz149 rfl)

noncomputable def ep748 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz122 60352 1000 0 1 11551488463034085 4503599627370496 1600000000171 57000000000000000 2178610724128228431 14073748835532800 1508800000161253 890625000000000000 qz150 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz366) Bool.false 12112613566614428712960 4722366482869645213696 1000000000106875 35625000000000000000 11551488463034085 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 63636 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep361 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep749 := nat_lit 6390724682154478853726424004310135535690738798517395050971266453928479201

noncomputable def ep750 := nat_lit 2095259589769147882335479776926303050084920354114506451112678424381921

noncomputable def ep751 := nat_lit 19167983527283898265414601053376554000972046554843956140011574004936673761

noncomputable def ep752 := BSN.cos_dyadic_bound_f 462545787 536870912 3 2 262144 71320 ep749 ep83 ep750 ep751 ep86 ep750 170722 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 462545787) qz283 0 2 ep749 ep83 ep750 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 462545787) qz284 0 2 ep751 ep86 ep750 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz416 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20289893) qz26)

noncomputable def ep753 := @Enclosure.Real.IsNear.cos_image qz203 qz416 Bool.false 20289893 131072 223 131072 Bool.true 170722 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz203 Bool.false 2178610724128228431 14073748835532800 1508800000161253 890625000000000000 20289893 131072 223 131072 (ep748 rfl) rfl) (Enclosure.sfrac_false_div 20289893 131072) (BSN.cos_reduce2 qz416 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16274383106169913737216) qz28) 226375608064910080 72057594037927936 Bool.false 170722 262144 24 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q2 20289893 131072 226375608064910080 72057594037927936 24 16274383106169913737216 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 170722 262144 16274383106169913737216 18889465931478580854784 462545787 536870912 71320 71250 (ep752 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep754 := nat_lit 45774005612019010656465502330498161

noncomputable def ep755 := BSN.sin_dyadic_bound_f 462545787 536870912 2 1 262144 71320 ep754 ep57 ep754 ep754 ep58 ep754 198930 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 462545787) qz278 0 1 ep754 ep57 ep754 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 462545787) qz279 0 1 ep754 ep58 ep754 rfl rfl rfl rfl) rfl rfl

noncomputable def ep756 := @Enclosure.Real.IsNear.sin_image qz203 qz416 Bool.false 20289893 131072 223 131072 Bool.true 198930 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz203 Bool.false 2178610724128228431 14073748835532800 1508800000161253 890625000000000000 20289893 131072 223 131072 (ep748 rfl) rfl) (Enclosure.sfrac_false_div 20289893 131072) (BSN.sin_reduce2 qz416 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16274383106169913737216) qz28) 226375608064910080 72057594037927936 Bool.false 198930 262144 24 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q2 20289893 131072 226375608064910080 72057594037927936 24 16274383106169913737216 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 198930 262144 16274383106169913737216 18889465931478580854784 462545787 536870912 71320 71250 (ep755 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep757 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz120 (Real.cos qz203)) (@HMul.hMul Real Real Real qz0 qz120 (@Neg.neg Real Real.instNeg (Real.sin qz203))) Bool.true 6206171505 34359738368 590174435207 1224065679360000 Bool.false 7231602825 34359738368 590676890207 1224065679360000 (@Enclosure.Real.IsNear.mulLit_ft qz120 (Real.cos qz203) 72705 262144 1 262144 85361 131072 8075447 4669440000 6206171505 34359738368 590174435207 1224065679360000 qz368 (@Enclosure.Real.IsNear.recentre' (Real.cos qz203) Bool.true 170722 262144 8075447 4669440000 85361 131072 8075447 4669440000 (ep753 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz120 (@Neg.neg Real Real.instNeg (Real.sin qz203)) 72705 262144 1 262144 99465 131072 8075447 4669440000 7231602825 34359738368 590676890207 1224065679360000 qz368 (@Enclosure.Real.IsNear.neg (Real.sin qz203) Bool.true 99465 131072 8075447 4669440000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz203) Bool.true 198930 262144 8075447 4669440000 99465 131072 8075447 4669440000 (ep756 rfl rfl) rfl)) rfl)

noncomputable def ep758 := @ep702 6206171505 34359738368 590174435207 1224065679360000 Bool.false 7231602825 34359738368 590676890207 1224065679360000 Bool.false 163470486602193567744 19030469307 34359738368 10374311764883 1224065679360000 Bool.false 197907588919016292352 2879934457 17179869184 10370921832383 1224065679360000 (ep703 (BSN.head_sum_c_succ qz139 12 13 rfl rfl) (ep746 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep747 ep757) rfl rfl

noncomputable abbrev qz204 := (@HMul.hMul Real Real Real qz263 qz383 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep759 := @Enclosure.Complex.IsNear.of_eq qz193 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz204)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz204)))) Bool.true 10693900857 68719476736 379000542851 816043786240000 Bool.true 7465770221 34359738368 189859401113 408021893120000 (BSN.cpow_neg_s_mk qz148 60352 1000 14 qz149 rfl)

noncomputable def ep760 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz125 60352 1000 0 1 11885224601802469 4503599627370496 1600000000171 57000000000000000 11207766799499728267 70368744177664000 1508800000161253 890625000000000000 qz150 (BSN.isNear_log_sfrac 14 1 11885224601802469 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz370) Bool.false 12462561272059625734144 4722366482869645213696 1000000000106875 35625000000000000000 11885224601802469 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 73349 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep376 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep761 := nat_lit 12395976216385262010910880056995856

noncomputable def ep762 := BSN.sin_dyadic_bound_f 333672322 536870912 2 1 262144 71320 ep761 ep57 ep761 ep761 ep58 ep761 152637 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 333672322) qz278 0 1 ep761 ep57 ep761 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 333672322) qz279 0 1 ep761 ep58 ep761 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz417 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5219023) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep763 := @Enclosure.Real.IsNear.cos_image qz204 qz417 Bool.false 5219023 32768 223 131072 Bool.true 152637 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz204 Bool.false 11207766799499728267 70368744177664000 1508800000161253 890625000000000000 5219023 32768 223 131072 (ep760 rfl) rfl) (Enclosure.sfrac_false_div 5219023 32768) (BSN.cos_reduce1 qz417 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2935012785049217007616) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 152637 262144 25 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q1 5219023 32768 226375608064910080 72057594037927936 25 2935012785049217007616 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 152637 262144 2935012785049217007616 4722366482869645213696 333672322 536870912 71320 71250 (ep762 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep764 := BSN.cos_dyadic_bound_f 333672322 536870912 2 1 262144 71320 ep761 ep61 ep761 ep761 ep62 ep761 213122 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 333672322) qz283 0 1 ep761 ep61 ep761 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 333672322) qz284 0 1 ep761 ep62 ep761 rfl rfl rfl rfl) rfl rfl

noncomputable def ep765 := @Enclosure.Real.IsNear.sin_image qz204 qz417 Bool.false 5219023 32768 223 131072 Bool.false 213122 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz204 Bool.false 11207766799499728267 70368744177664000 1508800000161253 890625000000000000 5219023 32768 223 131072 (ep760 rfl) rfl) (Enclosure.sfrac_false_div 5219023 32768) (BSN.sin_reduce1 qz417 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2935012785049217007616) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 213122 262144 25 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q1 5219023 32768 226375608064910080 72057594037927936 25 2935012785049217007616 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 213122 262144 2935012785049217007616 4722366482869645213696 333672322 536870912 71320 71250 (ep764 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep766 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz204)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz204))) Bool.true 10693900857 68719476736 379000542851 816043786240000 Bool.true 7465770221 34359738368 189859401113 408021893120000 (@Enclosure.Real.IsNear.mulLit_ft qz123 (Real.cos qz204) 70061 262144 1 262144 152637 262144 8075447 4669440000 10693900857 68719476736 379000542851 816043786240000 qz372 (@Enclosure.Real.IsNear.recentre' (Real.cos qz204) Bool.true 152637 262144 8075447 4669440000 152637 262144 8075447 4669440000 (ep763 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz123 (@Neg.neg Real Real.instNeg (Real.sin qz204)) 70061 262144 1 262144 106561 131072 8075447 4669440000 7465770221 34359738368 189859401113 408021893120000 qz372 (@Enclosure.Real.IsNear.neg (Real.sin qz204) Bool.false 106561 131072 8075447 4669440000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz204) Bool.false 213122 262144 8075447 4669440000 106561 131072 8075447 4669440000 (ep765 rfl rfl) rfl)) rfl)

noncomputable def ep767 := @ep700 10693900857 68719476736 379000542851 816043786240000 Bool.true 7465770221 34359738368 189859401113 408021893120000 Bool.false 940324257237697560576 27367037757 68719476736 21885625158319 2448131358720000 Bool.true 29307161295074623488 1705901307 34359738368 5470250017861 612032839680000 (ep701 (BSN.head_sum_c_succ qz139 13 14 rfl rfl) (ep758 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep759 ep766) rfl rfl

noncomputable abbrev qz205 := (@HMul.hMul Real Real Real qz263 qz383 qz376)

noncomputable def ep768 := @Enclosure.Complex.IsNear.of_eq qz192 (Complex.mk (@HMul.hMul Real Real Real qz0 qz128 (Real.cos qz205)) (@HMul.hMul Real Real Real qz0 qz128 (@Neg.neg Real Real.instNeg (Real.sin qz205)))) Bool.false 8847986255 34359738368 91674342607 204010946560000 Bool.true 1293528035 68719476736 363819642303 816043786240000 (BSN.cpow_neg_s_mk qz148 60352 1000 15 qz149 rfl)

noncomputable def ep769 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz131 60352 1000 0 1 12195939715864293 4503599627370496 1600000000171 57000000000000000 11500771152060028299 70368744177664000 1508800000161253 890625000000000000 qz150 (BSN.isNear_log_sfrac 15 1 12195939715864293 4503599627370496 1600000000171 57000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 12788369683502116896768 4722366482869645213696 1000000000106875 35625000000000000000 12195939715864293 4503599627370496 1600000000171 57000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 82392 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep396 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep770 := BSN.cos_dyadic_bound_f 39175048 536870912 1 0 262144 71320 0 1 1 0 1 1 261446 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 39175048) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 39175048) qz284 0 0 rfl) rfl rfl

noncomputable abbrev qz418 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 42843711) qz31)

noncomputable def ep771 := @Enclosure.Real.IsNear.cos_image qz205 qz418 Bool.false 42843711 262144 445 262144 Bool.false 261446 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz205 Bool.false 11500771152060028299 70368744177664000 1508800000161253 890625000000000000 42843711 262144 445 262144 (ep769 rfl) rfl) (Enclosure.sfrac_false_div 42843711 262144) (BSN.cos_reduce0 qz418 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2756698973565104422912) qz33) 226375608064910080 72057594037927936 Bool.false 261446 262144 26 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 42843711 262144 226375608064910080 72057594037927936 26 2756698973565104422912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 261446 262144 2756698973565104422912 37778931862957161709568 39175048 536870912 71320 71250 (ep770 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep772 := BSN.sin_dyadic_bound_f 39175048 536870912 1 0 262144 71320 0 1 1 0 1 1 19111 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 39175048) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 39175048) qz279 0 0 rfl) rfl rfl

noncomputable def ep773 := @Enclosure.Real.IsNear.sin_image qz205 qz418 Bool.false 42843711 262144 445 262144 Bool.false 19111 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz205 Bool.false 11500771152060028299 70368744177664000 1508800000161253 890625000000000000 42843711 262144 445 262144 (ep769 rfl) rfl) (Enclosure.sfrac_false_div 42843711 262144) (BSN.sin_reduce0 qz418 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2756698973565104422912) qz33) 226375608064910080 72057594037927936 Bool.false 19111 262144 26 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 42843711 262144 226375608064910080 72057594037927936 26 2756698973565104422912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 19111 262144 2756698973565104422912 37778931862957161709568 39175048 536870912 71320 71250 (ep772 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep774 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz128 (Real.cos qz205)) (@HMul.hMul Real Real Real qz0 qz128 (@Neg.neg Real Real.instNeg (Real.sin qz205))) Bool.false 8847986255 34359738368 91674342607 204010946560000 Bool.true 1293528035 68719476736 363819642303 816043786240000 (@Enclosure.Real.IsNear.mulLit_ff qz128 (Real.cos qz205) 67685 262144 1 262144 130723 131072 16115269 9338880000 8847986255 34359738368 91674342607 204010946560000 qz379 (@Enclosure.Real.IsNear.recentre' (Real.cos qz205) Bool.false 261446 262144 16115269 9338880000 130723 131072 16115269 9338880000 (ep771 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz128 (@Neg.neg Real Real.instNeg (Real.sin qz205)) 67685 262144 1 262144 19111 262144 16115269 9338880000 1293528035 68719476736 363819642303 816043786240000 qz379 (@Enclosure.Real.IsNear.neg (Real.sin qz205) Bool.false 19111 262144 16115269 9338880000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz205) Bool.false 19111 262144 16115269 9338880000 19111 262144 16115269 9338880000 (ep773 rfl rfl) rfl)) rfl)

noncomputable def ep775 := @ep698 8847986255 34359738368 91674342607 204010946560000 Bool.true 1293528035 68719476736 363819642303 816043786240000 Bool.false 1548353242848617824256 45063010267 68719476736 1209774593137 128849018880000 Bool.true 161673930034571640832 4705330649 68719476736 1209076789387 128849018880000 (ep699 (BSN.head_sum_c_succ qz139 14 15 rfl rfl) (ep767 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep768 ep774) rfl rfl

noncomputable def ep776 := @Enclosure.Complex.IsNear.mul qz189 (@HAdd.hAdd Complex Complex Complex qz5 qz190 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.true 73353936913037473469 782245379481744179200 33239024561844106206119 ep576 Bool.false

noncomputable abbrev qz206 := (Complex.re qz410)

noncomputable abbrev qz207 := (Complex.im qz410)

noncomputable def ep777 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz206 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz190 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz207 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz190 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 10602979744127599675 125159260717079068672 2904951598764227030183

noncomputable def ep778 := nat_lit 13376395989137825464320000

noncomputable def ep779 := nat_lit 1672049498642228183040000000

noncomputable def ep780 := nat_lit 36723698058892109186700908279145716252672

noncomputable def ep781 := @Enclosure.Real.IsNear.mulLit_tf qz206 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz190 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 727110825 4294967296 66403401199 153008209920000 43747030217

noncomputable abbrev qz419 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz480 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable abbrev qz208 := (Real.cos qz419)

noncomputable abbrev qz209 := (@Neg.neg Real Real.instNeg (Real.sin qz419))

noncomputable abbrev qz420 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 16)))

noncomputable def ep782 := @Enclosure.Complex.IsNear.of_eq qz189 (Complex.mk (@HMul.hMul Real Real Real qz0 qz420 qz208) (@HMul.hMul Real Real Real qz0 qz420 qz209)) Bool.true 727110825 4294967296 66403401199 153008209920000 Bool.false 12640849545 68719476736 1063001868559 2448131358720000 (BSN.cpow_neg_s_mk qz148 60352 1000 16 qz149 rfl)

noncomputable abbrev qz421 := (Real.sqrt (@Nat.cast Real Real.instNatCast 16))

noncomputable abbrev qz422 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16) qz19)

noncomputable def ep783 := @Enclosure.Real.IsNear.inv_image qz421 1048577 262144 1 262144 32767 32768 131072 (@Enclosure.Real.IsNear.of_eq qz421 (Real.sqrt qz422) Bool.false 1048577 262144 1 262144 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz422) Bool.false 1048577 262144 1 262144 1048577 262144 1 262144 (BSN.sqrt_enclosure 16 1 524288 524289 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep784 := BSN.log_dyadic_bound 0 32 1 0 1 131072 35625 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz423 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz210 := qz423

noncomputable def ep785 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz210 60352 1000 0 1 3121657384082679 1125899906842624 400000000057 14250000000000000 2943722913189966297 17592186044416000 377200000053751 222656250000000000 qz150 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 400000000057 14250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz422) Bool.false 13093180052687516860416 4722366482869645213696 1000000000142500 35625000000000000000 3121657384082679 1125899906842624 400000000057 14250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 131072 24973259072661432 36028797018963968 35625 1000000000000000 rfl rfl rfl rfl (ep784 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep786 := nat_lit 5421508559958287042012043984500811626857215602612999726963957397800351041

noncomputable def ep787 := nat_lit 1508068589148479205476541996743627253271640339253264872150904549668161

noncomputable def ep788 := nat_lit 16261509542696564167625178869508947626065103527160492651147570384301716801

noncomputable def ep789 := BSN.cos_dyadic_bound_f 443917879 536870912 3 2 262144 71320 ep786 ep83 ep787 ep788 ep86 ep787 177520 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 443917879) qz283 0 2 ep786 ep83 ep787 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 443917879) qz284 0 2 ep788 ep86 ep787 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz211 := qz419

noncomputable abbrev qz424 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 43864889) qz31)

noncomputable def ep790 := @Enclosure.Real.IsNear.cos_image qz211 qz424 Bool.false 43864889 262144 445 262144 Bool.true 177520 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 2943722913189966297 17592186044416000 377200000053751 222656250000000000 43864889 262144 445 262144 (ep785 rfl) rfl) (Enclosure.sfrac_false_div 43864889 262144) (BSN.cos_reduce2 qz424 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 31237943701355876057088) qz33) 226375608064910080 72057594037927936 Bool.false 177520 262144 26 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q2 43864889 262144 226375608064910080 72057594037927936 26 31237943701355876057088 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 177520 262144 31237943701355876057088 37778931862957161709568 443917879 536870912 71320 71250 (ep789 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep791 := nat_lit 38833858798070520942832741454366881

noncomputable def ep792 := BSN.sin_dyadic_bound_f 443917879 536870912 2 1 262144 71320 ep791 ep57 ep791 ep791 ep58 ep791 192887 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 443917879) qz278 0 1 ep791 ep57 ep791 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 443917879) qz279 0 1 ep791 ep58 ep791 rfl rfl rfl rfl) rfl rfl

noncomputable def ep793 := @Enclosure.Real.IsNear.sin_image qz211 qz424 Bool.false 43864889 262144 445 262144 Bool.true 192887 262144 1 35625 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 2943722913189966297 17592186044416000 377200000053751 222656250000000000 43864889 262144 445 262144 (ep785 rfl) rfl) (Enclosure.sfrac_false_div 43864889 262144) (BSN.sin_reduce2 qz424 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 31237943701355876057088) qz33) 226375608064910080 72057594037927936 Bool.false 192887 262144 26 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q2 43864889 262144 226375608064910080 72057594037927936 26 31237943701355876057088 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 192887 262144 31237943701355876057088 37778931862957161709568 443917879 536870912 71320 71250 (ep792 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz212 := (Real.sin qz419)

noncomputable def ep794 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz420 qz208) (@HMul.hMul Real Real Real qz0 qz420 qz209) Bool.true 727110825 4294967296 66403401199 153008209920000 Bool.false 12640849545 68719476736 1063001868559 2448131358720000 (@Enclosure.Real.IsNear.mulLit_ft qz420 qz208 65535 262144 1 262144 11095 16384 16115269 9338880000 727110825 4294967296 66403401199 153008209920000 (@Enclosure.Real.IsNear.recentre' qz420 Bool.false 65535 262144 1 262144 65535 262144 1 262144 (ep783 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz208 Bool.true 177520 262144 16115269 9338880000 11095 16384 16115269 9338880000 (ep790 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz420 qz209 65535 262144 1 262144 192887 262144 16115269 9338880000 12640849545 68719476736 1063001868559 2448131358720000 (@Enclosure.Real.IsNear.recentre' qz420 Bool.false 65535 262144 1 262144 65535 262144 1 262144 (ep783 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz212 Bool.true 192887 262144 16115269 9338880000 (@Enclosure.Real.IsNear.recentre' qz212 Bool.true 192887 262144 16115269 9338880000 192887 262144 16115269 9338880000 (ep793 rfl rfl) rfl)) rfl)

noncomputable def ep795 := @ep781 87422733696 0 1 10602979744127599675 125159260717079068672 2904951598764227030183 ep778 (@Enclosure.Complex.IsNear.re_isNear qz189 Bool.true 727110825 4294967296 66403401199 153008209920000 Bool.false 12640849545 68719476736 1063001868559 2448131358720000 (ep782 ep794))

noncomputable def ep796 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz190 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 43747030217 87422733696 0 1 Bool.false

noncomputable def ep797 := @Enclosure.Complex.IsNear.addLitP qz190 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) Bool.false 226663369 455326738 0 1 Bool.true 60352000

noncomputable def ep798 := @ep797 227663369 0 1 Bool.false 1 384 0 1 Bool.false 943 3000 0 1 Bool.false 87494060434 43747030217 87422733696 0 1 Bool.false 33630556967 33630556967 682990107000 0 1

noncomputable abbrev qz213 := (@HDiv.hDiv Complex Complex Complex qz319 qz411 (@HSub.hSub Complex Complex Complex qz311 qz381 (1 : Complex)))

noncomputable def ep799 := @Enclosure.Complex.IsNear.addLitP qz213 qz73 Bool.true 32000000 14570455616 0 1 Bool.true 3862528000 14570455616 0 1

noncomputable def ep800 := @Enclosure.Complex.IsNear.of_eq qz213 (Complex.mk (Enclosure.sfrac Bool.true 32000000 14570455616) (Enclosure.sfrac Bool.true 3862528000 14570455616)) Bool.true 32000000 14570455616 0 1 Bool.true 3862528000 14570455616 0 1

noncomputable def ep801 := @ep799 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 14506455616 226663369 455326738 0 1 Bool.true 3862528000 60352000 227663369 0 1 (ep800 (BSN.N_div_s_sub_one_mk qz148 60352 1000 16 qz149 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 32000000 14570455616) (Enclosure.sfrac Bool.true 3862528000 14570455616) Bool.true 32000000 14570455616 0 1 Bool.true 3862528000 14570455616 0 1 (Enclosure.Real.IsNear.const Bool.true 32000000 14570455616) (Enclosure.Real.IsNear.const Bool.true 3862528000 14570455616))) qz74 rfl

noncomputable abbrev qz214 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz348 qz411 1))

noncomputable def ep802 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) qz214)) Bool.false 1 384 0 1

noncomputable def ep803 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) qz214) Bool.false 0 1 0 1 Bool.false

noncomputable def ep804 := @ep803 0 1 0 1 Bool.false 1 384 0 1 Bool.false 943 3000 0 1 Bool.false 1 1 384 0 1 Bool.false 943 943 3000 0

noncomputable def ep805 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep806 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) qz214 Bool.false 1 384 0 1 Bool.false 943 3000 0 1

noncomputable def ep807 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz214)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz214)) 1 384 0 1 0 1 0

noncomputable def ep808 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz214) 1 24 0 1 1 16 0 1 1

noncomputable def ep809 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep810 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep811 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)) qz139 Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 (BSN.ascPochhammer_one_eval qz139)

noncomputable def ep812 := ep811 (@Enclosure.Complex.IsNear.of_eq qz139 (Complex.mk qz68 qz148) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 (BSN.s_crit_mk qz148 Bool.false 60352 1000 qz149) (@Enclosure.Complex.IsNear.mk qz68 qz148 Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 qz328 qz150))

noncomputable def ep813 := @ep810 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep420) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep812)

noncomputable def ep814 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 60352 1000 0 1 0 1 0

noncomputable def ep815 := @ep814 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep420) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep812)

noncomputable def ep816 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)))) 1886 375 0 1 0 1 0 1 1886

noncomputable def ep817 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 60352 1000 0 1 1886 375 0

noncomputable def ep818 := @ep817 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep420) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep812)

noncomputable def ep819 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep820 := @ep819 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep420) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep812)

noncomputable def ep821 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 1886 375 0 1 (@ep809 1 24 0 1 (ep813 rfl) (ep815 rfl) rfl rfl) (@ep816 1886 375 0 1 (ep818 rfl) (ep820 rfl) rfl rfl)

noncomputable def ep822 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 1886 375 0 1 ep821

noncomputable abbrev qz215 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz348 qz411 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 16) qz274) Bool.false 1 16 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 16 1 16 EMRow13.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 16) qz274 Bool.false 1 16 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 16) qz286))

noncomputable def ep823 := @ep808 384 0 1 ep822 (@Enclosure.Complex.IsNear.re_isNear qz214 Bool.false 1 16 0 1 Bool.false 0 1 0 1 qz215)

noncomputable def ep824 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz214) 1886 375 0 1 0 1 0 1 0

noncomputable def ep825 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 1886 375 0 1 ep821

noncomputable def ep826 := @ep824 1 0 1 ep825 (@Enclosure.Complex.IsNear.im_isNear qz214 Bool.false 1 16 0 1 Bool.false 0 1 0 1 qz215)

noncomputable def ep827 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz214)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz214)) 0 1 0 1 943 3000 0

noncomputable def ep828 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz214) 1 24 0 1 0 1 0 1 0

noncomputable def ep829 := @ep828 1 0 1 ep822 (@Enclosure.Complex.IsNear.im_isNear qz214 Bool.false 1 16 0 1 Bool.false 0 1 0 1 qz215)

noncomputable def ep830 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz75)) ↑qz135) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz214) 1886 375 0 1 1 16 0 1 943

noncomputable def ep831 := @ep830 3000 0 1 ep825 (@Enclosure.Complex.IsNear.re_isNear qz214 Bool.false 1 16 0 1 Bool.false 0 1 0 1 qz215)

noncomputable def ep832 := @ep804 1 (@ep805 0 1 0 1 (BSN.bern_sum_base qz139 16) qz89) (ep806 (@ep807 1 1 1 384 0 1 (ep823 rfl) (ep826 rfl) rfl rfl) (@ep827 1 943 943 3000 0 1 (ep829 rfl) (ep831 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep833 := ep798 (ep801 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep802 Bool.false 943 3000 0 1 (BSN.bern_sum_succ qz139 16 0 1 1 rfl rfl) (ep832 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep834 := @Enclosure.Real.IsNear.mulLit_ff qz207 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz190 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 12640849545 68719476736 1063001868559 2448131358720000 33630556967

noncomputable def ep835 := @ep834 682990107000 0 1 28341254048959902001 3128981517926976716800 35749344896600895700553 ep779 (@Enclosure.Complex.IsNear.im_isNear qz189 Bool.true 727110825 4294967296 66403401199 153008209920000 Bool.false 12640849545 68719476736 1063001868559 2448131358720000 (ep782 ep794))

noncomputable def ep836 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz190 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 43747030217 87422733696 0 1 Bool.false

noncomputable def ep837 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz206 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz190 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz207 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz190 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 326041893619798237 39112268974087208960 2233183366825525603433

noncomputable def ep838 := nat_lit 104503093665139261440000000

noncomputable def ep839 := nat_lit 214022335826205207429120000

noncomputable def ep840 := nat_lit 6556775453550790823441116496192209944576

noncomputable def ep841 := @Enclosure.Real.IsNear.mulLit_tf qz206 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz190 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 727110825 4294967296 66403401199 153008209920000 33630556967

noncomputable def ep842 := @ep841 682990107000 0 1 326041893619798237 39112268974087208960 2233183366825525603433 ep838 (@Enclosure.Complex.IsNear.re_isNear qz189 Bool.true 727110825 4294967296 66403401199 153008209920000 Bool.false 12640849545 68719476736 1063001868559 2448131358720000 (ep782 ep794))

noncomputable def ep843 := @Enclosure.Real.IsNear.mulLit_ff qz207 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz190 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz100 qz191 (@HSub.hSub Nat Nat Nat qz99 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 12640849545 68719476736 1063001868559 2448131358720000 43747030217

noncomputable def ep844 := @ep843 87422733696 0 1 184333209004555233755 2002548171473265098752 46503174864578035247303 ep839 (@Enclosure.Complex.IsNear.im_isNear qz189 Bool.true 727110825 4294967296 66403401199 153008209920000 Bool.false 12640849545 68719476736 1063001868559 2448131358720000 (ep782 ep794))

noncomputable abbrev qz425 := (ep833 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep845 := @ep776 838199320256107820103 10012740857366325493760 ep691 ep692 (@ep777 ep778 28341254048959902001 3128981517926976716800 35749344896600895700553 ep779 ep780 73353936913037473469 782245379481744179200 33239024561844106206119 ep576 (ep795 (@ep796 33630556967 682990107000 0 1 qz425) rfl) (ep835 (@ep836 33630556967 682990107000 0 1 qz425) rfl) rfl rfl) (@ep837 ep838 184333209004555233755 2002548171473265098752 46503174864578035247303 ep839 ep840 838199320256107820103 10012740857366325493760 ep691 ep692 (ep842 (@ep836 33630556967 682990107000 0 1 qz425) rfl) (ep844 (@ep796 33630556967 682990107000 0 1 qz425) rfl) rfl rfl)

noncomputable def ep846 := @ep695 ep687 ep688 (@ep696 128849018880000 (BSN.head_sum_c_eq qz139 16) (ep697 (BSN.head_sum_c_succ qz139 15 16 rfl rfl) (ep775 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep845 rfl rfl rfl

noncomputable def ep847 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz139 1 16) Bool.false 439605899820303002681 782245379481744179200 ep575 ep576 Bool.false 152611206457518072263 10012740857366325493760 ep687 ep688 (@ep689 ep576 Bool.false 152611206457518072263 10012740857366325493760 ep687 ep688 (BSN.zetaApproximant_eq_folded' qz139 1 16 rfl) (ep846 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep848 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))))) qz159)) (Complex.im (zetaApproximant qz139 1 16)) 45 262144 7066519

noncomputable def ep849 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))))) qz159)) Bool.false 45 262144 7066519

noncomputable def ep850 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))))) qz159) qz394 Bool.false 9882641 262144 191

noncomputable def ep851 := BSN.sin_dyadic_bound_f 92211 536870912 1 0 262144 71320 0 1 1 0 1 1 45 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 92211) qz278 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 92211) qz279 0 0 rfl) rfl rfl

noncomputable def ep852 := @ep850 262144 Bool.false 45 262144 1 35625 (@ep579 9882641 262144 191 262144 ep684 rfl) (Enclosure.sfrac_false_div 9882641 262144) (BSN.sin_reduce0 qz394 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6488787537438441472) qz33) 226375608064910080 72057594037927936 Bool.false 45 262144 6 1000000000000000 71250 35625 (BSN.sin_reduce_arg_pos_rat_q0 9882641 262144 226375608064910080 72057594037927936 6 6488787537438441472 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 45 262144 6488787537438441472 37778931862957161709568 92211 536870912 71320 71250 (ep851 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep853 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz139 1 16) Bool.false 439605899820303002681 782245379481744179200 ep575 ep576 Bool.false 152611206457518072263 10012740857366325493760 ep687 ep688 (@ep689 ep576 Bool.false 152611206457518072263 10012740857366325493760 ep687 ep688 (BSN.zetaApproximant_eq_folded' qz139 1 16 rfl) (ep846 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow13.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 16 qz148) Bool.false ep559 ep560 ep561 ep562 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 16 qz148) ep563 Bool.false ep559 ep560 ep561 ep562 (@Eq.refl Real ep563) (@ep564 Bool.false ep559 ep560 ep561 ep562 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz314 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz157 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz158 (@Nat.cast Complex Complex.instNatCast j))))) qz159) (zetaApproximant qz139 1 16)) (@ep566 ep567 ep568 ep569 1373500858117662650367 ep570 ep571 ep572 ep573 ep559 ep560 ep561 ep562 (@ep574 9338880000 439605899820303002681 782245379481744179200 ep575 ep576 ep565 ep567 ep568 ep569 (@ep577 9338880000 262143 262144 7066519 9338880000 (ep686 rfl rfl) rfl) ep847 rfl) (@ep848 9338880000 152611206457518072263 10012740857366325493760 ep687 ep688 1373500858117662650367 ep570 ep571 ep572 (@ep849 9338880000 45 262144 7066519 9338880000 (ep852 rfl rfl) rfl) ep853 rfl) rfl rfl))

theorem EMRow13.d13 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow13.d14 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow13.d15 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow13.d16 : @Eq Nat (Nat.pow 15 (Nat.succ (Nat.mul 2 3))) 170859375 := @Eq.refl Nat 170859375

noncomputable abbrev qz483 := (@HAdd.hAdd Complex Complex Complex qz486 qz485 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz426 := qz483

noncomputable abbrev qz216 := (@HDiv.hDiv Real Real Real qz266 (@Norm.norm Complex Complex.instNorm qz426) (@HAdd.hAdd Real Real Real qz338 (Complex.re qz268) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz217 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz218 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz427 := (@HPow.hPow Complex Complex Complex qz465 (@Nat.cast Complex Complex.instNatCast 15) (@HSub.hSub Complex Complex Complex qz471 qz466 qz467))

noncomputable abbrev qz219 := qz427

noncomputable def ep854 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 qz216 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) 3107875103 115964116992 15950485 115964116992 164499067854873 492581209243648 160587825

noncomputable def ep855 := nat_lit 20606870026211406129397760

noncomputable def ep856 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 15)) 6641 442368 1 442368 467983 262144 2331 262144 3107875103 115964116992

noncomputable abbrev qz428 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz220 := (@HPow.hPow Real Nat Real qz428 qz267 2)

noncomputable def ep857 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz220) 96 162 0 1 6641 262144 1 262144 6641 442368 1 442368

noncomputable def ep858 := nat_lit 781950621441006189802102638025

noncomputable def ep859 := nat_lit 19807040628566084398385987584

noncomputable def ep860 := nat_lit 26986075409044041160201671

noncomputable def ep861 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz221 := qz267

noncomputable abbrev qz429 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz221 1)

noncomputable def ep862 := @Enclosure.Real.IsNear.mulLit_ff qz429 qz221 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep858 ep859 ep860 ep861

noncomputable def ep863 := ep862 (@Enclosure.Real.IsNear.of_eq qz429 qz221 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz221) (@Enclosure.Real.IsNear.of_eq qz221 qz264 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz265)) (@Enclosure.Real.IsNear.of_eq qz221 qz264 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz265) rfl

noncomputable def ep864 := @Enclosure.Real.IsNear.inv_image qz220 ep858 ep859 ep860 ep861 3320 3321 131072 (@Enclosure.Real.IsNear.of_eq qz220 (@HMul.hMul Real Real Real qz0 qz429 qz221) Bool.false ep858 ep859 ep860 ep861 (BSN.pow_succ_r qz221 1 2 rfl) ep863) rfl rfl rfl

noncomputable def ep865 := ep857 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz220) Bool.false 6641 262144 1 262144 6641 262144 1 262144 (ep864 rfl rfl rfl) rfl)

noncomputable def ep866 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 15)) (Real.sqrt (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 15)) (Complex.re (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 15)) (Complex.im (zetaApproximant qz6 1 15))))) Bool.false 467983 262144 2331 262144

noncomputable def ep867 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 15)) (Complex.re (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 15)) (Complex.im (zetaApproximant qz6 1 15))))) Bool.false 467983 262144 2331 262144

noncomputable def ep868 := nat_lit 20670636471241019020907793874004379001

noncomputable def ep869 := nat_lit 6485786416030240102666029779386368000

noncomputable def ep870 := nat_lit 160226817766260562670286873689361549198703859033399521

noncomputable def ep871 := nat_lit 5048084362338425823578786638462132106035200000000000000

noncomputable def ep872 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 15)) (Complex.re (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 15)) (Complex.im (zetaApproximant qz6 1 15)))) ep868 ep869 ep870 ep871 232826 235157

noncomputable def ep873 := nat_lit 1521112194789288666977497516903959910626628441

noncomputable def ep874 := nat_lit 477307330289431952294060712630214522306560000

noncomputable def ep875 := nat_lit 475700601030498622642438092330852567230281795879765219

noncomputable def ep876 := nat_lit 15144253087015277470736359915386396318105600000000000000

noncomputable def ep877 := nat_lit 221156420898295757047367764892535440293609

noncomputable def ep878 := nat_lit 1073941493151221892661636603417982675189760000

noncomputable def ep879 := nat_lit 77810191691922896381602011519251255716090331569271

noncomputable def ep880 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 15)) (Complex.re (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 15)) (Complex.im (zetaApproximant qz6 1 15))) ep873 ep874 ep875 ep876 ep877 ep878 ep879

noncomputable def ep881 := nat_lit 236628954484613710480255623677912442470400000000000000

noncomputable def ep882 := nat_lit 1633691061303376287952535328780740900563857652936607471146884364208068197640934994739200000

noncomputable def ep883 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz6 1 15)) (Complex.re (zetaApproximant qz6 1 15)) 39001438368210071272229 21847364378556786278400 ep164 ep165 39001438368210071272229 21847364378556786278400 ep164 ep165 ep873

noncomputable def ep884 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz6 1 15)) (Complex.im (zetaApproximant qz6 1 15)) 470272709072401688147 32771046567835179417600 ep292 ep293 470272709072401688147 32771046567835179417600 ep292 ep293 ep877

noncomputable def ep885 := @ep854 281474976710656 ep855 4797910811894435 13299692649578496 1049666856235 7599824371187712 (@ep856 15950485 115964116992 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz220)) Bool.false 6641 442368 1 442368 (BSN.theta_err_eq 1 2 96 162 EMRow13.d13 EMRow13.d14 rfl) (ep865 rfl)) (ep866 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz6 1 15)) (@ep867 467983 262144 2331 262144 (@ep872 131072 (@ep880 ep881 ep882 ep868 ep869 ep870 ep871 (@ep883 ep874 ep875 ep876 ep457 ep457 rfl) (@ep884 ep878 ep879 ep881 ep465 ep465 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz222 := (@Norm.norm Complex Complex.instNorm qz426)

noncomputable abbrev qz430 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep886 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz216 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz222 qz430) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) Bool.false 164499067854873 492581209243648 160587825 281474976710656 (BSN.zrb_shape_eq qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) qz17 3)

noncomputable def ep887 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz222 qz430) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) 15112953 917504 1 917504 10884641 536870912 143 4294967296

noncomputable def ep888 := @Enclosure.Real.IsNear.mulLit_ff qz222 qz430 15112953 262144 1 262144 2 7 0 1 15112953 917504

noncomputable abbrev qz431 := (Complex.re qz483)

noncomputable abbrev qz432 := (Complex.im qz483)

noncomputable abbrev qz223 := (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz263 qz431 qz431) (@HMul.hMul Real Real Real qz263 qz432 qz432))

noncomputable abbrev qz224 := qz426

noncomputable def ep889 := @Enclosure.Real.IsNear.of_eq qz222 (Real.sqrt qz223) Bool.false 15112953 262144 1 262144 (BSN.norm_eq_sqrt_mul_add qz224)

noncomputable def ep890 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz223) Bool.false 15112953 262144 1 262144 15112953

noncomputable def ep891 := @Enclosure.Real.IsNear.sqrt_image qz223 132947081 40000 0 1 7556476 7556477 131072

noncomputable abbrev qz225 := (@HMul.hMul Real Real Real qz263 qz431 qz431)

noncomputable abbrev qz226 := (@HMul.hMul Real Real Real qz263 qz432 qz432)

noncomputable def ep892 := @Enclosure.Real.IsNear.addLit_ff qz225 qz226 49 4 0 1 132457081 40000 0 1

noncomputable abbrev qz227 := qz431

noncomputable def ep893 := @Enclosure.Real.IsNear.mulLit_ff qz227 qz227 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz433 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep894 := @Enclosure.Complex.IsNear.of_eq qz224 (Complex.mk qz433 qz17) Bool.false 7 2 0 1 Bool.false 57545 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 57545 1000 3 qz18)

noncomputable abbrev qz434 := (ep894 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz17 Bool.false 7 2 0 1 Bool.false 57545 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz21))

noncomputable def ep895 := @ep893 0 1 (@Enclosure.Complex.IsNear.re_isNear qz224 Bool.false 7 2 0 1 Bool.false 57545 1000 0 1 qz434)

noncomputable def ep896 := ep895 (@Enclosure.Complex.IsNear.re_isNear qz224 Bool.false 7 2 0 1 Bool.false 57545 1000 0 1 qz434)

noncomputable abbrev qz228 := qz432

noncomputable def ep897 := @Enclosure.Real.IsNear.mulLit_ff qz228 qz228 57545 1000 0 1 57545 1000 0 1 132457081 40000

noncomputable def ep898 := @ep897 0 1 (@Enclosure.Complex.IsNear.im_isNear qz224 Bool.false 7 2 0 1 Bool.false 57545 1000 0 1 qz434)

noncomputable def ep899 := ep898 (@Enclosure.Complex.IsNear.im_isNear qz224 Bool.false 7 2 0 1 Bool.false 57545 1000 0 1 qz434)

noncomputable def ep900 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Real.sqrt (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))))) Bool.false 10884641 536870912

noncomputable def ep901 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))))) Bool.false 174154256 8589934592

noncomputable def ep902 := nat_lit 8249931746448430536965015064096931572799625811382974341

noncomputable def ep903 := nat_lit 20070670678677560827382146445383525355382374400000000000000

noncomputable def ep904 := nat_lit 31640006960449327672252800725164364874328695196223198434323108500027

noncomputable def ep905 := nat_lit 23501966576593606316668646846669097055167876956160000000000000000000000000000

noncomputable def ep906 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)))) ep902 ep903 ep904 ep905

noncomputable def ep907 := nat_lit 278984940722967747247954100232920989515510819834919561

noncomputable def ep908 := nat_lit 802826827147102433095285857815341014215294976000000000000

noncomputable def ep909 := nat_lit 26829212570999667931042015436147691355134002106001872265099573585951

noncomputable def ep910 := nat_lit 318827057093559213941540639568476708727963828877496329

noncomputable def ep911 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) ep907 ep908 ep909 ep905 ep910

noncomputable def ep912 := nat_lit 5017667669669390206845536611345881338845593600000000000000

noncomputable def ep913 := nat_lit 1202698597362414935302696322254168379798673272555331542305883728519

noncomputable def ep914 := nat_lit 5875491644148401579167161711667274263791969239040000000000000000000000000000

noncomputable def ep915 := nat_lit 1655816632045336759973533579578386118553264357151123552228917018993516947701074992599399940388552704000000000000

noncomputable def ep916 := nat_lit 528190250499730208005755331

noncomputable def ep917 := nat_lit 28334198897217871282176000000

noncomputable def ep918 := nat_lit 4694031823006588573857634922351

noncomputable def ep919 := nat_lit 153303511298970599659929600000000000000

noncomputable def ep920 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) ep916 ep917 ep918 ep919 ep916 ep917 ep918

noncomputable def ep921 := nat_lit 564647728317009360074008573

noncomputable def ep922 := nat_lit 70835497243044678205440000000

noncomputable def ep923 := nat_lit 984187203938473652450817422113

noncomputable def ep924 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219) Bool.true ep916 ep917 ep918 ep919 Bool.false ep921 ep922 ep923

noncomputable def ep925 := nat_lit 76651755649485299829964800000000000000

noncomputable def ep926 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219 Bool.true ep916 ep917 ep918 ep919 Bool.false ep921 ep922 ep923 ep925

noncomputable def ep927 := nat_lit 236118324143482260684800000

noncomputable def ep928 := nat_lit 210251519069165079075173021

noncomputable def ep929 := nat_lit 255505852164950999433216000000000000

noncomputable def ep930 := nat_lit 542552328528208157602568251

noncomputable def ep931 := nat_lit 4567880911565089526412531109751

noncomputable abbrev qz229 := (Complex.re qz427)

noncomputable abbrev qz230 := (Complex.im qz427)

noncomputable def ep932 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz229) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230) 119683983570649579973441 ep927 ep928 ep929 ep930 ep917 ep931

noncomputable def ep933 := nat_lit 124715396776922390379862434286936358341269310668800000

noncomputable def ep934 := nat_lit 13307596466924531220480000000

noncomputable def ep935 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz229 397321243 19200000 0 1 903681736221561 36893488147419103232 529172609754382247 ep934 119683983570649579973441

noncomputable def ep936 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 397321243 19200000 0 1 0 1 0 1 397321243

noncomputable def ep937 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1191963729 80000 0 1 397321243 19200000 0

noncomputable def ep938 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz14) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow13.d15 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz14 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz22)

noncomputable abbrev qz435 := (@HAdd.hAdd Complex Complex Complex qz464 qz463 qz468)

noncomputable abbrev qz231 := qz435

noncomputable def ep939 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz46 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz231) Bool.true 1191963729 80000 0 1 Bool.true 1521801475229 8000000 0 1

noncomputable abbrev qz232 := (Complex.re qz435)

noncomputable abbrev qz233 := (Complex.im qz435)

noncomputable def ep940 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz233) 132427081 16000 0 1 132457081 20000 0 1

noncomputable def ep941 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz232 132427081 40000 0 1 5 2 0 1 132427081 16000

noncomputable abbrev qz436 := (@HAdd.hAdd Complex Complex Complex qz464 qz463 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz234 := qz436

noncomputable def ep942 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz46 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz234) Bool.true 132427081 40000 0 1 Bool.false 11509 100 0 1

noncomputable abbrev qz235 := (Complex.re qz436)

noncomputable abbrev qz236 := (Complex.im qz436)

noncomputable def ep943 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz236) 3 4 0 1 132457081 40000 0 1

noncomputable def ep944 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz235 1 2 0 1 3 2 0 1 3 4

noncomputable def ep945 := @ep944 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep422)

noncomputable abbrev qz437 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep946 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz437 qz17) Bool.false 3 2 0 1 Bool.false 57545 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 57545 1000 1 qz18)

noncomputable abbrev qz438 := (ep946 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz17 Bool.false 3 2 0 1 Bool.false 57545 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz21))

noncomputable def ep947 := ep945 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 3 2 0 1 Bool.false 57545 1000 0 1 qz438)

noncomputable def ep948 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz236 57545 1000 0 1 57545 1000 0 1 132457081 40000

noncomputable def ep949 := @ep948 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep422)

noncomputable def ep950 := ep949 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 3 2 0 1 Bool.false 57545 1000 0 1 qz438)

noncomputable def ep951 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz234 Bool.true 132427081 40000 0 1 Bool.false 11509 100 0 1 (@ep943 529708324 132427081 40000 0 1 (ep947 rfl) (ep950 rfl) rfl rfl)

noncomputable def ep952 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz235) 11509 400 0 1 34527 400 0 1

noncomputable def ep953 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz236 1 2 0 1 57545 1000 0 1 11509 400

noncomputable def ep954 := @ep953 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep422)

noncomputable def ep955 := ep954 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 3 2 0 1 Bool.false 57545 1000 0 1 qz438)

noncomputable def ep956 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz235 57545 1000 0 1 3 2 0 1 34527 400

noncomputable def ep957 := @ep956 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep422)

noncomputable def ep958 := ep957 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 3 2 0 1 Bool.false 57545 1000 0 1 qz438)

noncomputable abbrev qz237 := (ep942 (BSN.ascPochhammer_succ_eval_c 1 2 qz268 rfl) (ep951 (@ep952 18414400 11509 100 0 1 (ep955 rfl) (ep958 rfl) rfl rfl)))

noncomputable def ep959 := @ep941 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 132427081 40000 0 1 Bool.false 11509 100 0 1 qz237)

noncomputable abbrev qz439 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep960 := @Enclosure.Complex.IsNear.of_eq qz231 (Complex.mk qz439 qz17) Bool.false 5 2 0 1 Bool.false 57545 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 57545 1000 2 qz18)

noncomputable abbrev qz440 := (ep960 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz17 Bool.false 5 2 0 1 Bool.false 57545 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz21))

noncomputable def ep961 := ep959 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 5 2 0 1 Bool.false 57545 1000 0 1 qz440)

noncomputable def ep962 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz233 11509 100 0 1 57545 1000 0 1 132457081 20000

noncomputable def ep963 := @ep962 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 132427081 40000 0 1 Bool.false 11509 100 0 1 qz237)

noncomputable def ep964 := ep963 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 5 2 0 1 Bool.false 57545 1000 0 1 qz440)

noncomputable def ep965 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz231 Bool.true 1191963729 80000 0 1 Bool.true 1521801475229 8000000 0 1 (@ep940 4767854916000 1191963729 80000 0 1 (ep961 rfl) (ep964 rfl) rfl rfl)

noncomputable def ep966 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz232) 1524103275229 8000000 0 1 11509 40 0 1

noncomputable def ep967 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz233 132427081 40000 0 1 57545 1000 0 1 1524103275229 8000000

noncomputable def ep968 := @ep967 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 132427081 40000 0 1 Bool.false 11509 100 0 1 qz237)

noncomputable def ep969 := ep968 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 5 2 0 1 Bool.false 57545 1000 0 1 qz440)

noncomputable def ep970 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz232 11509 100 0 1 5 2 0 1 11509 40

noncomputable def ep971 := @ep970 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 132427081 40000 0 1 Bool.false 11509 100 0 1 qz237)

noncomputable def ep972 := ep971 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 5 2 0 1 Bool.false 57545 1000 0 1 qz440)

noncomputable abbrev qz238 := (ep939 (BSN.ascPochhammer_succ_eval_c 2 3 qz268 rfl) (ep965 (@ep966 60872059009160 1521801475229 8000000 0 1 (ep969 rfl) (ep972 rfl) rfl rfl)))

noncomputable def ep973 := @ep937 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep938) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1191963729 80000 0 1 Bool.true 1521801475229 8000000 0 1 qz238)

noncomputable def ep974 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1521801475229 8000000 0 1 0 1 0

noncomputable def ep975 := @ep974 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep938) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1191963729 80000 0 1 Bool.true 1521801475229 8000000 0 1 qz238)

noncomputable def ep976 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 1521801475229 5760000000 0 1 0 1 0 1 1521801475229

noncomputable def ep977 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1521801475229 8000000 0 1 1521801475229 5760000000 0

noncomputable def ep978 := @ep977 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep938) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1191963729 80000 0 1 Bool.true 1521801475229 8000000 0 1 qz238)

noncomputable def ep979 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1191963729 80000 0 1 0 1 0

noncomputable def ep980 := @ep979 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep938) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1191963729 80000 0 1 Bool.true 1521801475229 8000000 0 1 qz238)

noncomputable def ep981 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 397321243 19200000 0 1 Bool.false 1521801475229 5760000000 0 1 (@ep936 397321243 19200000 0 1 (ep973 rfl) (ep975 rfl) rfl rfl) (@ep976 1521801475229 5760000000 0 1 (ep978 rfl) (ep980 rfl) rfl rfl)

noncomputable def ep982 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 397321243 19200000 0 1 Bool.false 1521801475229 5760000000 0 1 ep981

noncomputable def ep983 := nat_lit 26615192933849062440960000000

noncomputable def ep984 := @Enclosure.Complex.IsNear.re_isNear qz219 Bool.false 903681736221561 36893488147419103232 529172609754382247 ep934 Bool.false 5347796713561785 73786976294838206464 3001627338334467619 ep983

noncomputable abbrev qz441 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 170859375)))

noncomputable def ep985 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (@HMul.hMul Real Real Real qz0 qz441 qz129) (@HMul.hMul Real Real Real qz0 qz441 qz130)) Bool.false 903681736221561 36893488147419103232 529172609754382247 ep934 Bool.false 5347796713561785 73786976294838206464 3001627338334467619

noncomputable abbrev qz442 := (Real.sqrt (@Nat.cast Real Real.instNatCast 170859375))

noncomputable abbrev qz443 := (@Nat.cast Real Real.instNatCast 170859375)

noncomputable def ep986 := @Enclosure.Real.IsNear.inv_image qz442 112281773466917 8589934592 1 8589934592 328579 328580 4294967296 (@Enclosure.Real.IsNear.of_eq qz442 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz443 qz19)) Bool.false 112281773466917 8589934592 1 8589934592 (BSN.sqrt_natCast_div_one 170859375) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz443 qz19)) Bool.false 112281773466917 8589934592 1 8589934592 112281773466917 8589934592 1 8589934592 (BSN.sqrt_enclosure 170859375 1 56140886733458 56140886733459 4294967296 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep987 := nat_lit 419050471535146650281443328

noncomputable def ep988 := nat_lit 154742504910672534362390528

noncomputable def ep989 := nat_lit 1803515625000000000000000

noncomputable def ep990 := nat_lit 2124039924396124256730046692528675

noncomputable def ep991 := nat_lit 69486322526432349988248161643105

noncomputable def ep992 := BSN.log_dyadic_bound 7 23 10 9 ep990 4294967296 1803515625 ep991 56114196246175274031825 2699853634 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 7) (BSN.artanhQ 23) 0 9 ep991 ep990 56114196246175274031825 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep993 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz131 57545 1000 0 1 12195973876373221 4503599627370496 2560013851 4617000000000000000 140363463343179400489 900719925474099200 29463199411159 923400000000000000000 qz21 (BSN.isNear_log_sfrac 15 1 12195973876373221 4503599627370496 2560013851 4617000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz377 Bool.false ep987 ep988 1000005410546875 ep989 12195973876373221 4503599627370496 2560013851 4617000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 2699853634 4294967296 24973259072661432 36028797018963968 1803515625 1000000000000000 rfl rfl rfl rfl (ep992 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep994 := nat_lit 201730046106034597917622272

noncomputable def ep995 := nat_lit 618970019642690137449562112

noncomputable def ep996 := nat_lit 313001036449982902696862276675380057721420599442188288453468597722656628672580634536971922603838146260027265

noncomputable def ep997 := nat_lit 3329059111081908600533338745948885236305030013077543416727584952146906293099957468609793330210409636547767828480

noncomputable def ep998 := nat_lit 1167794063633257869772685227901379989893446166989137396037524822217934645723298882914582474774495152001

noncomputable def ep999 := nat_lit 819762728559566481788564425992769263226594123435746582584252742804864722248284776541496983209855033879349121

noncomputable def ep1000 := nat_lit 61032750369834991009777877009062895998925550239754962640005724122693282040165886924512877720524176670042410188800

noncomputable def ep1001 := BSN.sin_dyadic_bound_f 5733512753807 17592186044416 3 2 8589934592 3610553742 ep996 ep997 ep998 ep999 ep1000 ep998 2750268158 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 5733512753807) (BSN.sinEvenQ 17592186044416) 0 2 ep996 ep997 ep998 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 5733512753807) (BSN.sinOddQ 17592186044416) 0 2 ep999 ep1000 ep998 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 669305149761) (@Nat.cast Real Real.instNatCast 4294967296))

noncomputable def ep1002 := @Enclosure.Real.IsNear.cos_image qz132 qz444 Bool.false 669305149761 4294967296 275 8589934592 Bool.false 2750268158 8589934592 1 1803515625 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 140363463343179400489 900719925474099200 29463199411159 923400000000000000000 669305149761 4294967296 275 8589934592 (ep993 rfl) rfl) (Enclosure.sfrac_false_div 669305149761 4294967296) (BSN.cos_reduce3 qz444 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep994) (@Nat.cast Real Real.instNatCast ep995)) 226375608064910080 72057594037927936 Bool.false 2750268158 8589934592 24 1000000000000000 3607031250 1803515625 (BSN.sin_reduce_arg_pos_rat_q3 669305149761 4294967296 226375608064910080 72057594037927936 24 ep994 ep995 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2750268158 8589934592 ep994 ep995 5733512753807 17592186044416 3610553742 3607031250 (ep1001 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1003 := nat_lit 173889983714018782946198941568645766014118063443956599868547459856952446122387340653376807927676647697860481

noncomputable def ep1004 := nat_lit 369895456786878733392593193994320581811670001453060379636398328016322921455550829845532592245601070727529758720

noncomputable def ep1005 := nat_lit 521667615553929082322857279335481495282374403439535821330850304521212902497870575362364594618080394103277441

noncomputable def ep1006 := nat_lit 16645295555409543002666693729744426181525150065387717083637924760734531465499787343048966651052048182738839142400

noncomputable def ep1007 := BSN.cos_dyadic_bound_f 5733512753807 17592186044416 3 2 8589934592 3610553742 ep1003 ep1004 ep998 ep1005 ep1006 ep998 8137751615 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 5733512753807) (BSN.cosEvenQ 17592186044416) 0 2 ep1003 ep1004 ep998 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 5733512753807) (BSN.cosOddQ 17592186044416) 0 2 ep1005 ep1006 ep998 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1008 := @Enclosure.Real.IsNear.sin_image qz132 qz444 Bool.false 669305149761 4294967296 275 8589934592 Bool.true 8137751615 8589934592 1 1803515625 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 140363463343179400489 900719925474099200 29463199411159 923400000000000000000 669305149761 4294967296 275 8589934592 (ep993 rfl) rfl) (Enclosure.sfrac_false_div 669305149761 4294967296) (BSN.sin_reduce3 qz444 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep994) (@Nat.cast Real Real.instNatCast ep995)) 226375608064910080 72057594037927936 Bool.false 8137751615 8589934592 24 1000000000000000 3607031250 1803515625 (BSN.sin_reduce_arg_pos_rat_q3 669305149761 4294967296 226375608064910080 72057594037927936 24 ep994 ep995 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8137751615 8589934592 ep994 ep995 5733512753807 17592186044416 3610553742 3607031250 (ep1007 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1009 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz441 qz129) (@HMul.hMul Real Real Real qz0 qz441 qz130) Bool.false 903681736221561 36893488147419103232 529172609754382247 ep934 Bool.false 5347796713561785 73786976294838206464 3001627338334467619 ep983 (@Enclosure.Real.IsNear.mulLit_ff qz441 qz129 657159 8589934592 1 8589934592 1375134079 4294967296 504556731467 15492081254400000000 903681736221561 36893488147419103232 529172609754382247 ep934 (@Enclosure.Real.IsNear.recentre' qz441 Bool.false 657159 8589934592 1 8589934592 657159 8589934592 1 8589934592 (ep986 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 2750268158 8589934592 504556731467 15492081254400000000 1375134079 4294967296 504556731467 15492081254400000000 (ep1002 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz441 qz130 657159 8589934592 1 8589934592 8137751615 8589934592 504556731467 15492081254400000000 5347796713561785 73786976294838206464 3001627338334467619 ep983 (@Enclosure.Real.IsNear.recentre' qz441 Bool.false 657159 8589934592 1 8589934592 657159 8589934592 1 8589934592 (ep986 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz133 Bool.true 8137751615 8589934592 504556731467 15492081254400000000 (@Enclosure.Real.IsNear.recentre' qz133 Bool.true 8137751615 8589934592 504556731467 15492081254400000000 8137751615 8589934592 504556731467 15492081254400000000 (ep1008 rfl rfl) rfl)) rfl)

noncomputable def ep1010 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230 1521801475229 5760000000 0 1 5347796713561785 73786976294838206464 3001627338334467619 ep983 ep930

noncomputable def ep1011 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 397321243 19200000 0 1 Bool.false 1521801475229 5760000000 0 1 ep981

noncomputable def ep1012 := @Enclosure.Complex.IsNear.im_isNear qz219 Bool.false 903681736221561 36893488147419103232 529172609754382247 ep934 Bool.false 5347796713561785 73786976294838206464 3001627338334467619 ep983

noncomputable def ep1013 := nat_lit 94447329657392904273920000

noncomputable def ep1014 := nat_lit 1192610305089832224124330417

noncomputable def ep1015 := nat_lit 511011704329901998866432000000000000

noncomputable def ep1016 := nat_lit 458408066439825191399070823

noncomputable def ep1017 := nat_lit 805295658174998818832167859563

noncomputable def ep1018 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz229) 141652882502912224899917 ep1013 ep1014 ep1015 ep1016 ep922 ep1017

noncomputable def ep1019 := nat_lit 53329470136654609336979473597780871636838420316160000

noncomputable def ep1020 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230 397321243 19200000 0 1 5347796713561785 73786976294838206464 3001627338334467619 ep983 141652882502912224899917

noncomputable def ep1021 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz229 1521801475229 5760000000 0 1 903681736221561 36893488147419103232 529172609754382247 ep934 ep1016

noncomputable abbrev qz445 := (@ep985 ep983 (BSN.cpow_neg_s_sub_mk qz17 57545 1000 15 3 170859375 qz18 rfl EMRow13.d16) ep1009)

noncomputable def ep1022 := ep926 (@ep932 ep919 ep933 ep916 ep917 ep918 ep919 (@ep935 ep927 ep928 ep929 ep982 (ep984 qz445) rfl) (@ep1010 ep917 ep931 ep919 ep1011 (ep1012 qz445) rfl) rfl rfl) (@ep1018 ep925 ep1019 ep921 ep922 ep923 ep925 (@ep1020 ep1013 ep1014 ep1015 ep982 (ep1012 qz445) rfl) (@ep1021 ep922 ep1017 ep925 ep1011 (ep984 qz445) rfl) rfl rfl)

noncomputable def ep1023 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) ep921 ep922 ep923 ep925 ep921 ep922 ep923

noncomputable def ep1024 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219) Bool.true ep916 ep917 ep918 ep919 Bool.false ep921 ep922 ep923

noncomputable def ep1025 := @ep887 164499067854873 492581209243648 160587825 281474976710656 (@ep888 1 917504 (ep889 (@ep890 262144 1 262144 (ep891 (@ep892 531788324 132947081 40000 0 1 (ep896 rfl) (ep899 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep900 143 4294967296 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (@ep901 286 8589934592 10884641 536870912 143 4294967296 (@ep906 87076985 87077271 4294967296 (@ep911 ep912 ep913 ep914 ep915 ep902 ep903 ep904 ep905 (@ep920 ep919 ep907 ep908 ep909 ep905 (@ep924 ep925 ep1022) (@ep924 ep925 ep1022) rfl) (@ep1023 ep925 ep910 ep912 ep913 ep914 (@ep1024 ep925 ep1022) (@ep1024 ep925 ep1022) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow13.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 qz216 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)))) Bool.false 4797910811894435 13299692649578496 1049666856235 7599824371187712 := ep885 (ep886 ep1025) rfl rfl

theorem EMRow13.d18 : @Eq Nat (Nat.pow 16 (Nat.succ (Nat.mul 2 3))) 268435456 := @Eq.refl Nat 268435456

noncomputable abbrev qz484 := (@HAdd.hAdd Complex Complex Complex qz486 qz492 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz446 := qz484

noncomputable abbrev qz239 := (@HDiv.hDiv Real Real Real qz266 (@Norm.norm Complex Complex.instNorm qz446) (@HAdd.hAdd Real Real Real qz338 (Complex.re qz381) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz447 := (@HPow.hPow Complex Complex Complex qz465 (@Nat.cast Complex Complex.instNatCast 16) (@HSub.hSub Complex Complex Complex qz471 qz479 qz467))

noncomputable abbrev qz240 := qz447

noncomputable def ep1026 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz139 1 16))) (@HMul.hMul Real Real Real qz0 qz239 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240))) 489275675 57982058496 8827831 57982058496 1269883785092985 3940649673949184 1427168835

noncomputable def ep1027 := nat_lit 75558539939543365986549760

noncomputable def ep1028 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz139 1 16)) 6641 442368 1 442368 73675 131072 659 65536 489275675 57982058496

noncomputable def ep1029 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz139 1 16)) (Real.sqrt (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz139 1 16)) (Complex.re (zetaApproximant qz139 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz139 1 16)) (Complex.im (zetaApproximant qz139 1 16))))) Bool.false 73675 131072 659 65536

noncomputable def ep1030 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz139 1 16)) (Complex.re (zetaApproximant qz139 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz139 1 16)) (Complex.im (zetaApproximant qz139 1 16))))) Bool.false 147350 262144 2636 262144

noncomputable def ep1031 := nat_lit 3479470447715012744284010786469142849

noncomputable def ep1032 := nat_lit 11009124998582110383971904530677760000

noncomputable def ep1033 := nat_lit 898589924488798176852711699237390576944579043131390287

noncomputable def ep1034 := nat_lit 79523542070321112932108096481588899374694400000000000000

noncomputable def ep1035 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz139 1 16)) (Complex.re (zetaApproximant qz139 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz139 1 16)) (Complex.im (zetaApproximant qz139 1 16)))) ep1031 ep1032 ep1033 ep1034 72357 74993

noncomputable def ep1036 := nat_lit 193253347156818279564857846645464693187761

noncomputable def ep1037 := nat_lit 611907833720537957310773287793081712640000

noncomputable def ep1038 := nat_lit 211889887041125019088269818553891404189452726102411

noncomputable def ep1039 := nat_lit 19414927263261990461940453242575414886400000000000000

noncomputable def ep1040 := nat_lit 23290180336419205759025944803251689941169

noncomputable def ep1041 := nat_lit 100254979476772938925797095472018507798937600

noncomputable def ep1042 := nat_lit 3409883018705566518573169160072376153842297446212759

noncomputable def ep1043 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz139 1 16)) (Complex.re (zetaApproximant qz139 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz139 1 16)) (Complex.im (zetaApproximant qz139 1 16))) ep1036 ep1037 ep1038 ep1039 ep1040 ep1041 ep1042

noncomputable def ep1044 := nat_lit 8835949118924568103567566275732099930521600000000000000

noncomputable def ep1045 := nat_lit 19388861796821111551935127640901898894463333308448064147483010378942650324356798873600

noncomputable def ep1046 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz139 1 16)) (Complex.re (zetaApproximant qz139 1 16)) 439605899820303002681 782245379481744179200 ep575 ep576 439605899820303002681 782245379481744179200 ep575 ep576 ep1036

noncomputable def ep1047 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz139 1 16)) (Complex.im (zetaApproximant qz139 1 16)) 152611206457518072263 10012740857366325493760 ep687 ep688 152611206457518072263 10012740857366325493760 ep687 ep688 ep1040

noncomputable def ep1048 := @ep1026 3940649673949184 ep1027 35184686975340995 106397541196627968 16237674066193 106397541196627968 (@ep1028 8827831 57982058496 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz220)) Bool.false 6641 442368 1 442368 (BSN.theta_err_eq 1 2 96 162 EMRow13.d13 EMRow13.d14 rfl) (ep865 rfl)) (ep1029 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz139 1 16)) (@ep1030 73675 131072 659 65536 (@ep1035 131072 (@ep1043 ep1044 ep1045 ep1031 ep1032 ep1033 ep1034 (@ep1046 ep1037 ep1038 ep1039 ep847 ep847 rfl) (@ep1047 ep1041 ep1042 ep1044 ep853 ep853 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz241 := (@Norm.norm Complex Complex.instNorm qz446)

noncomputable def ep1049 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz239 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz241 qz430) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240))) Bool.false 1269883785092985 3940649673949184 1427168835 3940649673949184 (BSN.zrb_shape_eq qz241 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) qz148 3)

noncomputable def ep1050 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz241 qz430) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) 15847497 917504 1 917504 80131505 4294967296 85 4294967296

noncomputable def ep1051 := @Enclosure.Real.IsNear.mulLit_ff qz241 qz430 15847497 262144 1 262144 2 7 0 1 15847497 917504

noncomputable abbrev qz448 := (Complex.re qz484)

noncomputable abbrev qz449 := (Complex.im qz484)

noncomputable abbrev qz242 := (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz263 qz448 qz448) (@HMul.hMul Real Real Real qz263 qz449 qz449))

noncomputable abbrev qz243 := qz446

noncomputable def ep1052 := @Enclosure.Real.IsNear.of_eq qz241 (Real.sqrt qz242) Bool.false 15847497 262144 1 262144 (BSN.norm_eq_sqrt_mul_add qz243)

noncomputable def ep1053 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz242) Bool.false 15847497 262144 1 262144 15847497

noncomputable def ep1054 := @Enclosure.Real.IsNear.sqrt_image qz242 228413369 62500 0 1 7923748 7923749 131072

noncomputable abbrev qz244 := (@HMul.hMul Real Real Real qz263 qz448 qz448)

noncomputable abbrev qz245 := (@HMul.hMul Real Real Real qz263 qz449 qz449)

noncomputable def ep1055 := @Enclosure.Real.IsNear.addLit_ff qz244 qz245 49 4 0 1 56911936 15625 0 1

noncomputable abbrev qz246 := qz448

noncomputable def ep1056 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz246 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1057 := @Enclosure.Complex.IsNear.of_eq qz243 (Complex.mk qz433 qz148) Bool.false 7 2 0 1 Bool.false 60352 1000 0 1 (BSN.s_add_nat_mk qz148 Bool.false 60352 1000 3 qz149)

noncomputable abbrev qz450 := (ep1057 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz148 Bool.false 7 2 0 1 Bool.false 60352 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz150))

noncomputable def ep1058 := @ep1056 0 1 (@Enclosure.Complex.IsNear.re_isNear qz243 Bool.false 7 2 0 1 Bool.false 60352 1000 0 1 qz450)

noncomputable def ep1059 := ep1058 (@Enclosure.Complex.IsNear.re_isNear qz243 Bool.false 7 2 0 1 Bool.false 60352 1000 0 1 qz450)

noncomputable abbrev qz247 := qz449

noncomputable def ep1060 := @Enclosure.Real.IsNear.mulLit_ff qz247 qz247 60352 1000 0 1 60352 1000 0 1 56911936 15625

noncomputable def ep1061 := @ep1060 0 1 (@Enclosure.Complex.IsNear.im_isNear qz243 Bool.false 7 2 0 1 Bool.false 60352 1000 0 1 qz450)

noncomputable def ep1062 := ep1061 (@Enclosure.Complex.IsNear.im_isNear qz243 Bool.false 7 2 0 1 Bool.false 60352 1000 0 1 qz450)

noncomputable def ep1063 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) (Real.sqrt (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240))))) Bool.false 80131505 4294967296

noncomputable def ep1064 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240))))) Bool.false 320526020 17179869184

noncomputable def ep1065 := nat_lit 682258265753083801919663398969163696277229762352590133

noncomputable def ep1066 := nat_lit 1960026433464605549549037738806984897986560000000000000000

noncomputable def ep1067 := nat_lit 10307741821644129189114428767194242188367860159711378009407623

noncomputable def ep1068 := nat_lit 13992464096908821014248880009876720068853760000000000000000000000000000

noncomputable def ep1069 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)))) ep1065 ep1066 ep1067 ep1068

noncomputable def ep1070 := nat_lit 104890653544646839030156410924350637200431100656721161

noncomputable def ep1071 := nat_lit 490006608366151387387259434701746224496640000000000000000

noncomputable def ep1072 := nat_lit 1482125196317617856592698042845132907578089038452462979706031

noncomputable def ep1073 := nat_lit 3498116024227205253562220002469180017213440000000000000000000000000000

noncomputable def ep1074 := nat_lit 262695651574496445799037755271761147475505359725705489

noncomputable def ep1075 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240))) ep1070 ep1071 ep1072 ep1073 ep1074

noncomputable def ep1076 := nat_lit 4379241036373657762743636595813710558055504005901526090583499

noncomputable def ep1077 := nat_lit 334311058831440969880315334546881594525070021920607002525345775861557335370035593627198155653120000000000000000

noncomputable def ep1078 := nat_lit 323868265726432108904607869

noncomputable def ep1079 := nat_lit 22136092888451461939200000000

noncomputable def ep1080 := nat_lit 856387161050311331115990409

noncomputable def ep1081 := nat_lit 59144873186331249868800000000000000

noncomputable def ep1082 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) ep1078 ep1079 ep1080 ep1081 ep1078 ep1079 ep1080

noncomputable def ep1083 := nat_lit 512538439118956663058092183

noncomputable def ep1084 := nat_lit 44272185776902923878400000000

noncomputable def ep1085 := nat_lit 1598917375872415616968802693

noncomputable def ep1086 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240) Bool.true ep1078 ep1079 ep1080 ep1081 Bool.true ep1083 ep1084 ep1085

noncomputable def ep1087 := nat_lit 118289746372662499737600000000000000

noncomputable def ep1088 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240 Bool.true ep1078 ep1079 ep1080 ep1081 Bool.true ep1083 ep1084 ep1085 ep1087

noncomputable def ep1089 := nat_lit 59029581035870565171200000

noncomputable def ep1090 := nat_lit 157719661830216666316800000000000

noncomputable def ep1091 := nat_lit 37880302376593265620258843

noncomputable def ep1092 := nat_lit 2767011611056432742400000000

noncomputable def ep1093 := nat_lit 100144652100770086916098223

noncomputable abbrev qz248 := (Complex.re qz447)

noncomputable abbrev qz249 := (Complex.im qz447)

noncomputable def ep1094 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)))) qz248) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)))) qz249) 55535591236495957180099 ep1089 147279851317735028765879 ep1090 ep1091 ep1092 ep1093

noncomputable def ep1095 := nat_lit 7393109148291406233600000000000000

noncomputable def ep1096 := nat_lit 2389726004580660718276109218660985176118106521600000

noncomputable def ep1097 := nat_lit 5257322061007222210560000

noncomputable def ep1098 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)))) qz248 682865107 30000000 0 1 6099549237529275 147573952589676412928 215679275171597 ep1097 55535591236495957180099

noncomputable def ep1099 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)))) 682865107 30000000 0 1 0 1 0 1 682865107

noncomputable def ep1100 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 2048595321 125000 0 1 682865107 30000000 0

noncomputable abbrev qz451 := (@HAdd.hAdd Complex Complex Complex qz464 qz478 qz468)

noncomputable abbrev qz250 := qz451

noncomputable def ep1101 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz46 (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2)) qz250) Bool.true 2048595321 125000 0 1 Bool.true 428665863934 1953125 0 1

noncomputable abbrev qz251 := (Complex.re qz451)

noncomputable abbrev qz252 := (Complex.im qz451)

noncomputable def ep1102 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2))) qz251) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2))) qz252) 227600869 25000 0 1 113823872 15625 0 1

noncomputable def ep1103 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2))) qz251 227600869 62500 0 1 5 2 0 1 227600869 25000

noncomputable abbrev qz452 := (@HAdd.hAdd Complex Complex Complex qz464 qz478 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz253 := qz452

noncomputable def ep1104 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz46 (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)) qz253) Bool.true 227600869 62500 0 1 Bool.false 15088 125 0 1

noncomputable abbrev qz254 := (Complex.re qz452)

noncomputable abbrev qz255 := (Complex.im qz452)

noncomputable def ep1105 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) qz255) 3 4 0 1 56911936 15625 0 1

noncomputable def ep1106 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) qz254 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1107 := @ep1106 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep812)

noncomputable def ep1108 := @Enclosure.Complex.IsNear.of_eq qz253 (Complex.mk qz437 qz148) Bool.false 3 2 0 1 Bool.false 60352 1000 0 1 (BSN.s_add_nat_mk qz148 Bool.false 60352 1000 1 qz149)

noncomputable abbrev qz453 := (ep1108 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz148 Bool.false 3 2 0 1 Bool.false 60352 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz150))

noncomputable def ep1109 := ep1107 (@Enclosure.Complex.IsNear.re_isNear qz253 Bool.false 3 2 0 1 Bool.false 60352 1000 0 1 qz453)

noncomputable def ep1110 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) qz255 60352 1000 0 1 60352 1000 0 1 56911936 15625

noncomputable def ep1111 := @ep1110 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep812)

noncomputable def ep1112 := ep1111 (@Enclosure.Complex.IsNear.im_isNear qz253 Bool.false 3 2 0 1 Bool.false 60352 1000 0 1 qz453)

noncomputable def ep1113 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)) qz253 Bool.true 227600869 62500 0 1 Bool.false 15088 125 0 1 (@ep1105 227600869 227600869 62500 0 1 (ep1109 rfl) (ep1112 rfl) rfl rfl)

noncomputable def ep1114 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) qz254) 3772 125 0 1 11316 125 0 1

noncomputable def ep1115 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) qz255 1 2 0 1 60352 1000 0 1 3772 125

noncomputable def ep1116 := @ep1115 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep812)

noncomputable def ep1117 := ep1116 (@Enclosure.Complex.IsNear.im_isNear qz253 Bool.false 3 2 0 1 Bool.false 60352 1000 0 1 qz453)

noncomputable def ep1118 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1))) qz254 60352 1000 0 1 3 2 0 1 11316 125

noncomputable def ep1119 := @ep1118 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep812)

noncomputable def ep1120 := ep1119 (@Enclosure.Complex.IsNear.re_isNear qz253 Bool.false 3 2 0 1 Bool.false 60352 1000 0 1 qz453)

noncomputable abbrev qz256 := (ep1104 (BSN.ascPochhammer_succ_eval_c 1 2 qz381 rfl) (ep1113 (@ep1114 1886000 15088 125 0 1 (ep1117 rfl) (ep1120 rfl) rfl rfl)))

noncomputable def ep1121 := @ep1103 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 227600869 62500 0 1 Bool.false 15088 125 0 1 qz256)

noncomputable def ep1122 := @Enclosure.Complex.IsNear.of_eq qz250 (Complex.mk qz439 qz148) Bool.false 5 2 0 1 Bool.false 60352 1000 0 1 (BSN.s_add_nat_mk qz148 Bool.false 60352 1000 2 qz149)

noncomputable abbrev qz454 := (ep1122 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz148 Bool.false 5 2 0 1 Bool.false 60352 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz150))

noncomputable def ep1123 := ep1121 (@Enclosure.Complex.IsNear.re_isNear qz250 Bool.false 5 2 0 1 Bool.false 60352 1000 0 1 qz454)

noncomputable def ep1124 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2))) qz252 15088 125 0 1 60352 1000 0 1 113823872 15625

noncomputable def ep1125 := @ep1124 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 227600869 62500 0 1 Bool.false 15088 125 0 1 qz256)

noncomputable def ep1126 := ep1125 (@Enclosure.Complex.IsNear.im_isNear qz250 Bool.false 5 2 0 1 Bool.false 60352 1000 0 1 qz454)

noncomputable def ep1127 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2)) qz250 Bool.true 2048595321 125000 0 1 Bool.true 428665863934 1953125 0 1 (@ep1102 6401860378125 2048595321 125000 0 1 (ep1123 rfl) (ep1126 rfl) rfl rfl)

noncomputable def ep1128 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2))) qz251) 429255238934 1953125 0 1 7544 25 0 1

noncomputable def ep1129 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2))) qz252 227600869 62500 0 1 60352 1000 0 1 429255238934 1953125

noncomputable def ep1130 := @ep1129 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 227600869 62500 0 1 Bool.false 15088 125 0 1 qz256)

noncomputable def ep1131 := ep1130 (@Enclosure.Complex.IsNear.im_isNear qz250 Bool.false 5 2 0 1 Bool.false 60352 1000 0 1 qz454)

noncomputable def ep1132 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2))) qz251 15088 125 0 1 5 2 0 1 7544 25

noncomputable def ep1133 := @ep1132 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 227600869 62500 0 1 Bool.false 15088 125 0 1 qz256)

noncomputable def ep1134 := ep1133 (@Enclosure.Complex.IsNear.re_isNear qz250 Bool.false 5 2 0 1 Bool.false 60352 1000 0 1 qz454)

noncomputable abbrev qz257 := (ep1101 (BSN.ascPochhammer_succ_eval_c 2 3 qz381 rfl) (ep1127 (@ep1128 10716646598350 428665863934 1953125 0 1 (ep1131 rfl) (ep1134 rfl) rfl rfl)))

noncomputable def ep1135 := @ep1100 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep938) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2048595321 125000 0 1 Bool.true 428665863934 1953125 0 1 qz257)

noncomputable def ep1136 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 428665863934 1953125 0 1 0 1 0

noncomputable def ep1137 := @ep1136 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep938) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2048595321 125000 0 1 Bool.true 428665863934 1953125 0 1 qz257)

noncomputable def ep1138 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)))) 214332931967 703125000 0 1 0 1 0 1 214332931967

noncomputable def ep1139 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 428665863934 1953125 0 1 214332931967 703125000 0

noncomputable def ep1140 := @ep1139 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep938) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2048595321 125000 0 1 Bool.true 428665863934 1953125 0 1 qz257)

noncomputable def ep1141 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 2048595321 125000 0 1 0 1 0

noncomputable def ep1142 := @ep1141 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep938) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2048595321 125000 0 1 Bool.true 428665863934 1953125 0 1 qz257)

noncomputable def ep1143 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 682865107 30000000 0 1 Bool.false 214332931967 703125000 0 1 (@ep1099 682865107 30000000 0 1 (ep1135 rfl) (ep1137 rfl) rfl rfl) (@ep1138 214332931967 703125000 0 1 (ep1140 rfl) (ep1142 rfl) rfl rfl)

noncomputable def ep1144 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 682865107 30000000 0 1 Bool.false 214332931967 703125000 0 1 ep1143

noncomputable def ep1145 := nat_lit 10514644122014444421120000

noncomputable def ep1146 := @Enclosure.Complex.IsNear.re_isNear qz240 Bool.true 6099549237529275 147573952589676412928 215679275171597 ep1097 Bool.false 13255185062657175 295147905179352825856 467238754127569 ep1145

noncomputable abbrev qz455 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 268435456)))

noncomputable def ep1147 := @Enclosure.Complex.IsNear.of_eq qz240 (Complex.mk (@HMul.hMul Real Real Real qz0 qz455 qz208) (@HMul.hMul Real Real Real qz0 qz455 qz209)) Bool.true 6099549237529275 147573952589676412928 215679275171597 ep1097 Bool.false 13255185062657175 295147905179352825856 467238754127569

noncomputable abbrev qz456 := (Real.sqrt (@Nat.cast Real Real.instNatCast 268435456))

noncomputable abbrev qz457 := (@Nat.cast Real Real.instNatCast 268435456)

noncomputable def ep1148 := @Enclosure.Real.IsNear.inv_image qz456 281474976710657 17179869184 1 17179869184 524287 524288 8589934592 (@Enclosure.Real.IsNear.of_eq qz456 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz457 qz19)) Bool.false 281474976710657 17179869184 1 17179869184 (BSN.sqrt_natCast_div_one 268435456) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz457 qz19)) Bool.false 281474976710657 17179869184 1 17179869184 281474976710657 17179869184 1 17179869184 (BSN.sqrt_enclosure 268435456 1 140737488355328 140737488355329 8589934592 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1149 := nat_lit 858074647932929104964222976

noncomputable def ep1150 := nat_lit 309485009821345068724781056

noncomputable def ep1151 := nat_lit 2334720000000000000000000

noncomputable def ep1152 := BSN.log_dyadic_bound 0 32 1 0 1 8589934592 2334720000 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep1153 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz210 60352 1000 0 1 3121657384082679 1125899906842624 48828581 114000000000000000 2943722913189966297 17592186044416000 46045351883 1781250000000000000 qz150 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 48828581 114000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz422) Bool.false ep1149 ep1150 1000009338880000 ep1151 3121657384082679 1125899906842624 48828581 114000000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 8589934592 24973259072661432 36028797018963968 2334720000 1000000000000000 rfl rfl rfl rfl (ep1152 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1154 := nat_lit 511803979497840144061300736

noncomputable def ep1155 := nat_lit 33587709335684471407700363734118263044721862751915043312315476315012047980959601528248132546473332102321210891263820291324061444398023873763477300724898292733535590547456

noncomputable def ep1156 := nat_lit 1723989524678609869184368353634558086375647288945605880257499904391989104065417411410730399287089189440146844853530817917959165259045966673531664948206962296697359276441600

noncomputable def ep1157 := nat_lit 367625975670813176803774542510305323123374124156306465458991418946269728454244185500535720474957779539730276260719115926518408728612269141405662784623186255282176

noncomputable def ep1158 := nat_lit 203727647520290666739149394883560741581847822689255521265241191857118164420822485605261094180345896192750577531330877126889573619804125312639692804904567050162776739676160

noncomputable def ep1159 := nat_lit 156883046745753498095777520180744785860183903294050135103432491299671008469952984438376466335125116239053362881671304430534284038573182967291381510286833568999459694156185600

noncomputable def ep1160 := BSN.cos_dyadic_bound_f 29092687981224 35184372088832 4 3 17179869184 4674000001 ep1155 ep1156 ep1157 ep1158 ep1159 ep1157 11633977994 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 29092687981224) (BSN.cosEvenQ 35184372088832) 0 3 ep1155 ep1156 ep1157 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 29092687981224) (BSN.cosOddQ 35184372088832) 0 3 ep1158 ep1159 ep1157 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 718682351853) (@Nat.cast Real Real.instNatCast 4294967296))

noncomputable def ep1161 := @Enclosure.Real.IsNear.cos_image qz211 qz458 Bool.false 718682351853 4294967296 445 17179869184 Bool.true 11633977994 17179869184 1 2334720000 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 2943722913189966297 17592186044416000 46045351883 1781250000000000000 718682351853 4294967296 445 17179869184 (ep1153 rfl) rfl) (Enclosure.sfrac_false_div 718682351853 4294967296) (BSN.cos_reduce2 qz458 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1154) (@Nat.cast Real Real.instNatCast ep995)) 226375608064910080 72057594037927936 Bool.false 11633977994 17179869184 26 1000000000000000 4669440000 2334720000 (BSN.sin_reduce_arg_pos_rat_q2 718682351853 4294967296 226375608064910080 72057594037927936 26 ep1154 ep995 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 11633977994 17179869184 ep1154 ep995 29092687981224 35184372088832 4674000001 4669440000 (ep1160 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1162 := nat_lit 3320347445883114619391895030897749663756809299909698604574229726726906001622005101126472289723874028937229107200

noncomputable def ep1163 := nat_lit 852239132436968601736534718962914620494087683347851114682261747749608011033589111964107092533864866956228564090880

noncomputable def ep1164 := nat_lit 513181265542592234073029010757235084154964730522591579296143551826914910181428721114269262445569193149464576

noncomputable def ep1165 := nat_lit 8695317207644897901456940176810023119703011556866459768470788861391319761060195808830385275232853439951453290496

noncomputable def ep1166 := nat_lit 15624384094677757698503136514320101375724940861377270435841465375409480202282467052675296696454189227530857008332800

noncomputable def ep1167 := BSN.sin_dyadic_bound_f 29092687981224 35184372088832 3 2 17179869184 4674000001 ep1162 ep1163 ep1164 ep1165 ep1166 ep1164 12641141609 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 29092687981224) (BSN.sinEvenQ 35184372088832) 0 2 ep1162 ep1163 ep1164 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 29092687981224) (BSN.sinOddQ 35184372088832) 0 2 ep1165 ep1166 ep1164 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1168 := @Enclosure.Real.IsNear.sin_image qz211 qz458 Bool.false 718682351853 4294967296 445 17179869184 Bool.true 12641141609 17179869184 1 2334720000 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 2943722913189966297 17592186044416000 46045351883 1781250000000000000 718682351853 4294967296 445 17179869184 (ep1153 rfl) rfl) (Enclosure.sfrac_false_div 718682351853 4294967296) (BSN.sin_reduce2 qz458 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1154) (@Nat.cast Real Real.instNatCast ep995)) 226375608064910080 72057594037927936 Bool.false 12641141609 17179869184 26 1000000000000000 4669440000 2334720000 (BSN.sin_reduce_arg_pos_rat_q2 718682351853 4294967296 226375608064910080 72057594037927936 26 ep1154 ep995 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 12641141609 17179869184 ep1154 ep995 29092687981224 35184372088832 4674000001 4669440000 (ep1167 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1169 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz455 qz208) (@HMul.hMul Real Real Real qz0 qz455 qz209) Bool.true 6099549237529275 147573952589676412928 215679275171597 ep1097 Bool.false 13255185062657175 295147905179352825856 467238754127569 ep1145 (@Enclosure.Real.IsNear.mulLit_ft qz455 qz208 1048575 17179869184 1 17179869184 5816988997 8589934592 16115269 612032839680000 6099549237529275 147573952589676412928 215679275171597 ep1097 (@Enclosure.Real.IsNear.recentre' qz455 Bool.false 1048575 17179869184 1 17179869184 1048575 17179869184 1 17179869184 (ep1148 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz208 Bool.true 11633977994 17179869184 1056130269184 40110184181268480000 5816988997 8589934592 16115269 612032839680000 (ep1161 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz455 qz209 1048575 17179869184 1 17179869184 12641141609 17179869184 16115269 612032839680000 13255185062657175 295147905179352825856 467238754127569 ep1145 (@Enclosure.Real.IsNear.recentre' qz455 Bool.false 1048575 17179869184 1 17179869184 1048575 17179869184 1 17179869184 (ep1148 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz212 Bool.true 12641141609 17179869184 16115269 612032839680000 (@Enclosure.Real.IsNear.recentre' qz212 Bool.true 12641141609 17179869184 1056130269184 40110184181268480000 12641141609 17179869184 16115269 612032839680000 (ep1168 rfl rfl) rfl)) rfl)

noncomputable def ep1170 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)))) qz249 214332931967 703125000 0 1 13255185062657175 295147905179352825856 467238754127569 ep1145 ep1091

noncomputable def ep1171 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 682865107 30000000 0 1 Bool.false 214332931967 703125000 0 1 ep1143

noncomputable def ep1172 := @Enclosure.Complex.IsNear.im_isNear qz240 Bool.true 6099549237529275 147573952589676412928 215679275171597 ep1097 Bool.false 13255185062657175 295147905179352825856 467238754127569 ep1145

noncomputable def ep1173 := nat_lit 118059162071741130342400000

noncomputable def ep1174 := nat_lit 315439323660433332633600000000000

noncomputable def ep1175 := nat_lit 17431123623423050956611119

noncomputable def ep1176 := nat_lit 1383505805528216371200000000

noncomputable def ep1177 := nat_lit 46227171412045772051741299

noncomputable def ep1178 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)))) qz249) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)))) qz248) 120686711548215913475903 ep1173 319061041831869096834883 ep1174 ep1175 ep1176 ep1177

noncomputable def ep1179 := nat_lit 3696554574145703116800000000000000

noncomputable def ep1180 := nat_lit 1890933082873191528789938669589943633864923545600000

noncomputable def ep1181 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)))) qz249 682865107 30000000 0 1 13255185062657175 295147905179352825856 467238754127569 ep1145 120686711548215913475903

noncomputable def ep1182 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3)))) qz248 214332931967 703125000 0 1 6099549237529275 147573952589676412928 215679275171597 ep1097 ep1175

noncomputable abbrev qz459 := (@ep1147 ep1145 (BSN.cpow_neg_s_sub_mk qz148 60352 1000 16 3 268435456 qz149 rfl EMRow13.d18) ep1169)

noncomputable def ep1183 := ep1088 (@ep1094 ep1095 ep1096 ep1078 ep1079 ep1080 ep1081 (@ep1098 ep1089 147279851317735028765879 ep1090 ep1144 (ep1146 qz459) rfl) (@ep1170 ep1092 ep1093 ep1095 ep1171 (ep1172 qz459) rfl) rfl rfl) (@ep1178 ep1179 ep1180 ep1083 ep1084 ep1085 ep1087 (@ep1181 ep1173 319061041831869096834883 ep1174 ep1144 (ep1172 qz459) rfl) (@ep1182 ep1176 ep1177 ep1179 ep1171 (ep1146 qz459) rfl) rfl rfl)

noncomputable def ep1184 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) ep1083 ep1084 ep1085 ep1087 ep1083 ep1084 ep1085

noncomputable def ep1185 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240) Bool.true ep1078 ep1079 ep1080 ep1081 Bool.true ep1083 ep1084 ep1085

noncomputable def ep1186 := @ep1050 1269883785092985 3940649673949184 1427168835 3940649673949184 (@ep1051 1 917504 (ep1052 (@ep1053 262144 1 262144 (ep1054 (@ep1055 228413369 228413369 62500 0 1 (ep1059 rfl) (ep1062 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1063 85 4294967296 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)) (@ep1064 340 17179869184 80131505 4294967296 85 4294967296 (@ep1069 160262840 160263180 8589934592 (@ep1075 ep1066 ep1076 ep1068 ep1077 ep1065 ep1066 ep1067 ep1068 (@ep1082 ep1081 ep1070 ep1071 ep1072 ep1073 (@ep1086 ep1087 ep1183) (@ep1086 ep1087 ep1183) rfl) (@ep1184 ep1087 ep1074 ep1066 ep1076 ep1068 (@ep1185 ep1087 ep1183) (@ep1185 ep1087 ep1183) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow13.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz139 1 16))) (@HMul.hMul Real Real Real qz0 qz239 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)))) Bool.false 35184686975340995 106397541196627968 16237674066193 106397541196627968 := ep1048 (ep1049 ep1186) rfl rfl

noncomputable def EMRow13.d20 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz460 := (EMRow13.d3 qz469 qz480 (@Enclosure.dec_le_dec qz469 qz480 57545 1000 60352 1000 (@Eq.refl Real qz469) (@Eq.refl Real qz480) rfl rfl rfl) 15 16 1 1)

noncomputable abbrev qz258 := qz460

noncomputable def ep1187 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz258 (@Enclosure.dec_nonneg qz17 57545 1000 qz18) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 15 rfl)

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalEM.fstVal qz460)

noncomputable def ep1188 := @Enclosure.Real.IsNear.neg_val qz259 ep149 ep150

noncomputable def ep1189 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantEM 1 15 qz17) Bool.true

noncomputable abbrev qz260 := (Zeta.Certificates.ZIntervalEM.sndVal qz460)

noncomputable def ep1190 := BSN.mul_neg_of_neg_pos_r qz259 qz260 (@ep1188 ep151 ep152 (@ep1189 ep149 ep150 ep151 ep152 (@Eq.refl Real (hardyZApproximantEM 1 15 qz17)) EMRow13.d9) rfl rfl rfl)

noncomputable def ep1191 := @Enclosure.Real.IsNear.pos_val qz260 ep559 ep560

noncomputable def ep1192 := @Enclosure.Real.IsNear.of_eq qz260 (hardyZApproximantEM 1 16 qz148) Bool.false

noncomputable def ep1193 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz259) (BSN.hardyZErrorBoundStrong 1 15 qz17)

noncomputable def ep1194 := @Enclosure.norm_gt_of_isNear qz259 (BSN.hardyZErrorBoundStrong 1 15 qz17) Bool.true

noncomputable def ep1195 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 15 qz17) (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 qz216 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)))) Bool.false 4797910811894435 13299692649578496 1049666856235 7599824371187712 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 15))) (@HMul.hMul Real Real Real qz0 qz216 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)))))

noncomputable def ep1196 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz260) (BSN.hardyZErrorBoundStrong 1 16 qz148)

noncomputable def ep1197 := @Enclosure.norm_gt_of_isNear qz260 (BSN.hardyZErrorBoundStrong 1 16 qz148) Bool.false

noncomputable def ep1198 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 16 qz148) (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz139 1 16))) (@HMul.hMul Real Real Real qz0 qz239 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)))) Bool.false 35184686975340995 106397541196627968 16237674066193 106397541196627968 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz338 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz139 1 16))) (@HMul.hMul Real Real Real qz0 qz239 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz139 (@ascPochhammer Complex Complex.instSemiring 3))) qz240)))))

noncomputable def ep1199 := @List.cons EMRow13.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz258 (ep1187 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 16 rfl) (ep1190 (@ep1191 ep561 ep562 (@ep1192 ep559 ep560 ep561 ep562 (@Eq.refl Real (hardyZApproximantEM 1 16 qz148)) EMRow13.d12) rfl rfl rfl)) (ep1193 (hardyZErrorBoundEM 1 15 qz17) (BSN.hardyZErrorBoundEM_le_strong 1 15 qz17 rfl) (@ep1194 Bool.false ep149 ep150 ep151 ep152 4797910811894435 13299692649578496 1049666856235 7599824371187712 (@ep1189 ep149 ep150 ep151 ep152 (@Eq.refl Real (hardyZApproximantEM 1 15 qz17)) EMRow13.d9) (ep1195 EMRow13.d17) rfl rfl rfl rfl rfl)) (ep1196 (hardyZErrorBoundEM 1 16 qz148) (BSN.hardyZErrorBoundEM_le_strong 1 16 qz148 rfl) (@ep1197 Bool.false ep559 ep560 ep561 ep562 35184686975340995 106397541196627968 16237674066193 106397541196627968 (@ep1192 ep559 ep560 ep561 ep562 (@Eq.refl Real (hardyZApproximantEM 1 16 qz148)) EMRow13.d12) (ep1198 EMRow13.d19) rfl rfl rfl rfl rfl)))) (@List.nil EMRow13.d0)

noncomputable abbrev qz461 := (@Enclosure.dec_le_dec qz469 qz480 57545 1000 60352 1000 (@Eq.refl Real qz469) (@Eq.refl Real qz480) rfl rfl rfl)

noncomputable abbrev qz261 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1199 (@List.IsChain.singleton EMRow13.d1 EMRow13.d20 (EMRow13.d2 qz276 qz383 qz461))))

noncomputable abbrev qz462 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1200 := And (@Eq (Option Real) (@Option.map qz462 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz462 qz261)) (@Option.some Real qz17))

noncomputable def ep1201 := ep1200 (@Eq (Option Real) (@Option.map qz462 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz462 qz261)) (@Option.some Real qz148))

noncomputable def ep1202 := @And.intro (@Eq Nat (@List.length qz462 qz261) 1) ep1201

noncomputable def ep1203 := @And.intro (@Eq (Option Real) (@Option.map qz462 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz462 qz261)) (@Option.some Real qz17))

noncomputable def ep1204 := @ep1203 (@Eq (Option Real) (@Option.map qz462 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz462 qz261)) (@Option.some Real qz148))

noncomputable abbrev qz262 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1199 (@List.IsChain.singleton EMRow13.d1 EMRow13.d20 (EMRow13.d2 qz276 qz383 qz461)))

theorem EMRow13.d21 : Zeta.Certificates.BatchSpec 1 57545 1000 60352 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz462 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz462 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz462 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz17)) (@Eq (Option Real) (@Option.map qz462 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz462 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz148)))) qz262 (ep1202 (@Eq.refl Nat 1) (ep1204 (@Eq.refl (Option Real) (@Option.some Real qz17)) (@Eq.refl (Option Real) (@Option.some Real qz148))))

theorem solution : Zeta.Certificates.BatchSpec 1 57545 1000 60352 1000 := EMRow13.d21
#print axioms solution
#check solution
