-- Prove2me | solution 1 for RHHeight1000.em_main_0010_0010
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:54:35.694175+00:00
-- url     : https://prove2.me/submissions/9b8b8c80-4951-4fa4-be6d-967edf1b1774

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow10.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow10.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow10.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow10.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow10.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz254 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz254

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz255 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz255 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138525251149047 2251799813685248 250000000033079 16539500000000000000 4138525251149047 2251799813685248 250000000033079 16539500000000000000 240893 131072

noncomputable abbrev qz256 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 131072 qz256 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 779317518150410741488063439345657628452599855445271348474342368876423347582876053728679783827237610085654588674605917415063316248867402488514697634436426745

noncomputable def ep10 := nat_lit 13198325246229587668616048586507268161410801335203869857947191811663857046415771104290097871102374067703089877156867761119753226876438075596795543285583799

noncomputable def ep11 := nat_lit 13338205139369261376383149914767634013226508915861991492218067381232119098362059104733250767410551174650894954010182016771344050520336484956804919489535

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 4 3 ep9 262144 66158 ep10 ep11 118379 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 3 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz257 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz257

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138525251149047 2251799813685248 250000000033079 16539500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 17358233014995452428288 9444732965739290427392 1000000000132316 66158000000000000000 4138525251149047 2251799813685248 250000000033079 16539500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 118379 262144 24973259072661432 36028797018963968 66158 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 779317518150412560342812906055656980396982394702499187106382620393032652998517540933158707129341055012778793601285942846917973645097155238594697634436426745

noncomputable def ep18 := nat_lit 13198325246229655554962711811363413523213721429909419700721697472804734044169853548961061453892255410264786862895235075217650796661500958924795543285583799

noncomputable def ep19 := nat_lit 13338205139369401582665284895604560799810298653799657073142644093199656832454717421805370366589019475922075211274104314270069372987910244956804919489535

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 4 3 ep17 262144 66158 ep18 ep19 118379 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 3 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138525251149047 2251799813685248 250000000033079 16539500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 17358233014995452428288 9444732965739290427392 1000000000132316 66158000000000000000 4138525251149047 2251799813685248 250000000033079 16539500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 118379 262144 24973259072661432 36028797018963968 66158 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz258 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz3 := (Real.log qz258)

theorem EMRow10.d4 : Enclosure.Real.IsNear qz3 Bool.false 240893 131072 3 131072 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz255) Bool.false 240893 131072 3 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz255) Bool.false 240893 131072 3 131072 240893 131072 3 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 300084 262144 1 66158 300084 262144 1 66158 150042 131072 2 131072 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 5456220599384213465248909714772227496572670538165976141063262914812807742611017753801422503639530882087556452122005170047444298375835020188444492540969863625638808382453421118235702266947370928498132967594635949979551089348001357731941995137847266570621617494261809398531128871567535833923098076891483476912075228072418610430965163137427706923427310178652894498746239459018086669257415154730407592571637957767157504839263249849478535520334507104454135585522664276476675

noncomputable def ep28 := nat_lit 583201912334273870627228188254822588827079241605343036411752047433839590517388190714780374919746279700129906501257101384229175562492847525225536391462542197025353003914524118772974087630067522636400444148635637549655768907025719966434833632093412247469427754039812435067522613541620617101084764807513402584784781490076808276521160080078978009740617112077674385114356333461540984478969922738031393369686631450339262287925718320742111081121726382582016608811398564907105

noncomputable def ep29 := nat_lit 2006268627360805445673839316848610509641534779303135707206598861506426804997221642604762844037348942607248852390277353874343091902420975230792155995982437872051629609224882022549487822374001366578458875613104959699164386313425243185530298109514065278868815165519648262204211929774735225023360668387821809970420335957473972782118680523137645713941929429588852958886338507735711181009301082096313539911189247153419366938656533848809858580689548163599238034961919825

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 10 9 ep27 262144 66158 ep28 ep29 300084 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 9 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 5456220599384260892400251500854699790811159195150212163211869656216336849990273498858157048596616978904240776489460003685239051624059887013466241201881443704542959173524008982544253046253151867013374679201187657749749224297051088632484873343955402287279851789208893474071824987110190207053471018354491495133306616646837230249901879422821128116650397962087630806812522581253210958036113071268120219429850657911869289056672761916619783759890108169949892385522664276476675

noncomputable def ep34 := nat_lit 583201912334279575053067226115417021307550325332234501953544426829928714668898700518418107620762577859683234776628347658361181262145210140271013263714562720079188253110303208819702903278206870150494721073991877864419341163488949363940583288588224434829960190109694548513088121652843287215458036179968684293644459891198769761601084092249455692877745995219003758983943549453190712470220270279351626860119698313725888367584660500821040083453648022042061408811398564907105

noncomputable def ep35 := nat_lit 2006268627360839170887858856494478835319319717359667041823756329478526322484078784125879825811686186445537802910004300367040714583746383402724632880452479311196631191501299191497899488881639138562974769996989848045902383299749709271247360054208480548633525642122514778503225872819822968825602771791453574137145372948950799520945900351638147820910599315255916738483881817718250085827996954508077874524152655659774549924038927632065100609588052048399238034961919825

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 10 9 ep33 262144 66158 ep34 ep35 300084 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 9 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 150042 131072 2 131072 75021 65536 1 65536 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 300084 262144 1 66158 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 300084 262144 66158 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 300084 262144 1 66158 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 300084 262144 66158 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow10.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 65536 := ep37

noncomputable abbrev qz446 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 48711 1000)))

noncomputable abbrev qz422 := qz446

noncomputable abbrev qz259 := qz422

noncomputable abbrev qz4 := (BSN.headSumC qz259 9)

noncomputable abbrev qz447 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz423 := qz447

noncomputable abbrev qz260 := qz423

noncomputable abbrev qz5 := qz260

noncomputable abbrev qz6 := (BSN.headSumC qz259 8)

noncomputable abbrev qz424 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz261 := qz424

noncomputable abbrev qz425 := (@Neg.neg Complex Complex.instNeg qz446)

noncomputable abbrev qz262 := qz425

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 8) qz262)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz4 (@HAdd.hAdd Complex Complex Complex qz5 qz6 qz7) Bool.false 12900430697 34359738368 5804400297903 1136585785475072 Bool.true 12714296203 68719476736 11596463021939 2273171570950144

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP qz6 qz7 Bool.false 4101108935 34359738368 5192720418011 1136585785475072 Bool.false 4036214339 68719476736 10373708674013 2273171570950144 Bool.false

noncomputable abbrev qz8 := (BSN.headSumC qz259 7)

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 7) qz262)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq qz6 (@HAdd.hAdd Complex Complex Complex qz5 qz8 qz9) Bool.false 4101108935 34359738368 5192720418011 1136585785475072 Bool.false 4036214339 68719476736 10373708674013 2273171570950144

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP qz8 qz9 Bool.true 14087539295 68719476736 9083620010993 2273171570950144 Bool.false 17369742671 68719476736 9074877959031 2273171570950144 Bool.false

noncomputable abbrev qz10 := (BSN.headSumC qz259 6)

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 6) qz262)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq qz8 (@HAdd.hAdd Complex Complex Complex qz5 qz10 qz11) Bool.true 14087539295 68719476736 9083620010993 2273171570950144 Bool.false 17369742671 68719476736 9074877959031 2273171570950144

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP qz10 qz11 Bool.true 35791409335 68719476736 7672097915503 2273171570950144 Bool.true 406707409 68719476736 7665783729825 2273171570950144 Bool.false

noncomputable abbrev qz12 := (BSN.headSumC qz259 5)

noncomputable abbrev qz13 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 5) qz262)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq qz10 (@HAdd.hAdd Complex Complex Complex qz5 qz12 qz13) Bool.true 35791409335 68719476736 7672097915503 2273171570950144 Bool.true 406707409 68719476736 7665783729825 2273171570950144

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP qz12 qz13 Bool.true 2685459915 34359738368 3065988275567 1136585785475072 Bool.false 3960296341 68719476736 6133013610863 2273171570950144 Bool.true

noncomputable abbrev qz14 := (BSN.headSumC qz259 4)

noncomputable abbrev qz15 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 4) qz262)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq qz12 (@HAdd.hAdd Complex Complex Complex qz5 qz14 qz15) Bool.true 2685459915 34359738368 3065988275567 1136585785475072 Bool.false 3960296341 68719476736 6133013610863 2273171570950144

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP qz14 qz15 Bool.true 1200190245 17179869184 1104886285715 568292892737536 Bool.true 1899645641 4294967296 2206027929393 1136585785475072 Bool.true

noncomputable abbrev qz16 := (BSN.headSumC qz259 3)

noncomputable abbrev qz426 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz263 := qz426

noncomputable abbrev qz17 := (@HPow.hPow Complex Complex Complex qz261 qz263 qz262)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq qz14 (@HAdd.hAdd Complex Complex Complex qz5 qz16 qz17) Bool.true 1200190245 17179869184 1104886285715 568292892737536 Bool.true 1899645641 4294967296 2206027929393 1136585785475072

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP qz16 qz17 Bool.false 4330779623 8589934592 1216864998333 1136585785475072 Bool.true 8660901195 17179869184 76060423901 71036611592192 Bool.true

noncomputable abbrev qz18 := (BSN.headSumC qz259 2)

noncomputable abbrev qz427 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz264 := qz427

noncomputable abbrev qz19 := (@HPow.hPow Complex Complex Complex qz261 qz264 qz262)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq qz16 (@HAdd.hAdd Complex Complex Complex qz5 qz18 qz19) Bool.false 4330779623 8589934592 1216864998333 1136585785475072 Bool.true 8660901195 17179869184 76060423901 71036611592192

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP qz18 qz19 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz265 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz20 := qz265

noncomputable abbrev qz21 := qz259

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq qz18 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz20) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz21)

noncomputable abbrev qz266 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz22 := (@Inv.inv Real Real.instInv (Real.sqrt qz266))

noncomputable abbrev qz448 := (Enclosure.sfrac Bool.false 48711 1000)

noncomputable abbrev qz428 := qz448

noncomputable abbrev qz267 := qz428

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz24 := qz267

noncomputable abbrev qz268 := (@Eq.refl Real qz428)

noncomputable abbrev qz25 := qz268

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz19 (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.true 4259154969 8589934592 1216864998333 1136585785475072 Bool.true 8660901195 17179869184 76060423901 71036611592192 (BSN.cpow_neg_s_mk qz24 48711 1000 2 qz25 rfl)

noncomputable abbrev qz26 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz266) 370727 262144 1 262144 92681 92683 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz266) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz266 qz26)) Bool.false 370727 262144 1 262144 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz266 qz26)) Bool.false 370727 262144 1 262144 370727 262144 1 262144 (BSN.sqrt_enclosure 2 1 185363 185364 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 131072 33079 24381081 945 90852 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 30295782835004843637524238166733056

noncomputable def ep57 := nat_lit 9969209968386869046778552952102584320

noncomputable def ep58 := nat_lit 69784469778708083327449870664718090240

noncomputable abbrev qz269 := (BSN.sinEvenQ 536870912)

noncomputable abbrev qz270 := (BSN.sinOddQ 536870912)

noncomputable def ep59 := BSN.sin_dyadic_bound_f 417201196 536870912 2 1 262144 66223 ep56 ep57 ep56 ep56 ep58 ep56 183818 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 417201196) qz269 0 1 ep56 ep57 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 417201196) qz270 0 1 ep56 ep58 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz27 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz28 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz271 := (Enclosure.Real.IsNear.const Bool.false 48711 1000)

noncomputable abbrev qz29 := qz271

noncomputable abbrev qz30 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz272 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8850983) qz27)

noncomputable abbrev qz273 := (BSN.isNear_log_sfrac 2 1 90852 131072 1 33079 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 90852 131072 33079 rfl rfl rfl (ep55 rfl)))

noncomputable def ep60 := @Enclosure.Real.IsNear.cos_image qz23 qz272 Bool.false 8850983 262144 387 262144 Bool.true 183818 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 1106372943 32768000 48711 33079000 8850983 262144 387 262144 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz28 48711 1000 0 1 90852 131072 1 33079 1106372943 32768000 48711 33079000 qz29 qz273 rfl) rfl) (Enclosure.sfrac_false_div 8850983 262144) (BSN.cos_reduce1 qz272 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29357924289279485280256) qz30) 226375608064910080 72057594037927936 Bool.false 183818 262144 5 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q1 8850983 262144 226375608064910080 72057594037927936 5 29357924289279485280256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 183818 262144 29357924289279485280256 37778931862957161709568 417201196 536870912 66223 66158 (ep59 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep61 := nat_lit 1993841993677373809355710590420516864

noncomputable def ep62 := nat_lit 29907629905160607140335658856307752960

noncomputable abbrev qz274 := (BSN.cosEvenQ 536870912)

noncomputable abbrev qz275 := (BSN.cosOddQ 536870912)

noncomputable def ep63 := BSN.cos_dyadic_bound_f 417201196 536870912 2 1 262144 66223 ep56 ep61 ep56 ep56 ep62 ep56 186895 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 417201196) qz274 0 1 ep56 ep61 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 417201196) qz275 0 1 ep56 ep62 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable def ep64 := @Enclosure.Real.IsNear.sin_image qz23 qz272 Bool.false 8850983 262144 387 262144 Bool.false 186895 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 1106372943 32768000 48711 33079000 8850983 262144 387 262144 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz28 48711 1000 0 1 90852 131072 1 33079 1106372943 32768000 48711 33079000 qz29 qz273 rfl) rfl) (Enclosure.sfrac_false_div 8850983 262144) (BSN.sin_reduce1 qz272 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29357924289279485280256) qz30) 226375608064910080 72057594037927936 Bool.false 186895 262144 5 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q1 8850983 262144 226375608064910080 72057594037927936 5 29357924289279485280256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 186895 262144 29357924289279485280256 37778931862957161709568 417201196 536870912 66223 66158 (ep63 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz276 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 185364 262144 2 262144 46341 65536 1 131072 (ep54 rfl rfl) rfl)

noncomputable def ep65 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.true 4259154969 8589934592 1216864998333 1136585785475072 Bool.true 8660901195 17179869184 76060423901 71036611592192 (@Enclosure.Real.IsNear.mulLit_ft qz22 (Real.cos qz23) 46341 65536 1 131072 91909 131072 13063717 8671461376 4259154969 8589934592 1216864998333 1136585785475072 qz276 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.true 183818 262144 13063717 8671461376 91909 131072 13063717 8671461376 (ep60 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 46341 65536 1 131072 186895 262144 13063717 8671461376 8660901195 17179869184 76060423901 71036611592192 qz276 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.false 186895 262144 13063717 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.false 186895 262144 13063717 8671461376 186895 262144 13063717 8671461376 (ep64 rfl rfl) rfl)) rfl)

noncomputable abbrev qz277 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz31 := qz277

noncomputable def ep66 := @ep51 4259154969 8589934592 1216864998333 1136585785475072 Bool.true 8660901195 17179869184 76060423901 71036611592192 Bool.false 4330779623 4330779623 8589934592 1216864998333 1136585785475072 Bool.true 8660901195 8660901195 17179869184 76060423901 71036611592192 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz20 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz31)) (ep53 ep65) rfl rfl

noncomputable abbrev qz32 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz33 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep67 := @Enclosure.Complex.IsNear.of_eq qz17 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)))) Bool.true 9861749491 17179869184 992907573097 1136585785475072 Bool.false 1062318631 17179869184 989061146977 1136585785475072 (BSN.cpow_neg_s_mk qz24 48711 1000 3 qz25 rfl)

noncomputable abbrev qz34 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep68 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz34) 454047 262144 1 262144 75674 75675 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz34) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz34 qz26)) Bool.false 454047 262144 1 262144 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz34 qz26)) Bool.false 454047 262144 1 262144 454047 262144 1 262144 (BSN.sqrt_enclosure 3 1 227023 227024 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep69 := BSN.log_dyadic_bound 1 2 9 8 2258332876800 131072 33079 222698787165 2027025 143997 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1) (BSN.artanhQ 2) 0 8 222698787165 2258332876800 2027025 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep70 := nat_lit 11016460170075684658174506924241

noncomputable def ep71 := BSN.cos_dyadic_bound_f 57611677 536870912 2 1 262144 66223 ep70 ep61 ep70 ep70 ep62 ep70 260636 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 57611677) qz274 0 1 ep70 ep61 ep70 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 57611677) qz275 0 1 ep70 ep62 ep70 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz35 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz278 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14028475) qz27)

noncomputable abbrev qz279 := (BSN.isNear_log_sfrac 3 1 143997 131072 1 33079 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 143997 131072 33079 rfl rfl rfl (ep69 rfl)))

noncomputable def ep72 := @Enclosure.Real.IsNear.cos_image qz33 qz278 Bool.false 14028475 262144 387 262144 Bool.true 260636 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 7014237867 131072000 48711 33079000 14028475 262144 387 262144 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz35 48711 1000 0 1 143997 131072 1 33079 7014237867 131072000 48711 33079000 qz29 qz279 rfl) rfl) (Enclosure.sfrac_false_div 14028475 262144) (BSN.cos_reduce2 qz278 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4054061423137411563520) qz30) 226375608064910080 72057594037927936 Bool.false 260636 262144 8 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q2 14028475 262144 226375608064910080 72057594037927936 8 4054061423137411563520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 260636 262144 4054061423137411563520 37778931862957161709568 57611677 536870912 66223 66158 (ep71 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep73 := BSN.sin_dyadic_bound_f 57611677 536870912 1 0 262144 66223 0 1 1 0 1 1 28076 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 57611677) qz269 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 57611677) qz270 0 0 rfl) rfl rfl

noncomputable def ep74 := @Enclosure.Real.IsNear.sin_image qz33 qz278 Bool.false 14028475 262144 387 262144 Bool.true 28076 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 7014237867 131072000 48711 33079000 14028475 262144 387 262144 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz35 48711 1000 0 1 143997 131072 1 33079 7014237867 131072000 48711 33079000 qz29 qz279 rfl) rfl) (Enclosure.sfrac_false_div 14028475 262144) (BSN.sin_reduce2 qz278 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4054061423137411563520) qz30) 226375608064910080 72057594037927936 Bool.false 28076 262144 8 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q2 14028475 262144 226375608064910080 72057594037927936 8 4054061423137411563520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 28076 262144 4054061423137411563520 37778931862957161709568 57611677 536870912 66223 66158 (ep73 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz280 := (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 151349 262144 1 262144 151349 262144 1 262144 (ep68 rfl rfl) rfl)

noncomputable def ep75 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33))) Bool.true 9861749491 17179869184 992907573097 1136585785475072 Bool.false 1062318631 17179869184 989061146977 1136585785475072 (@Enclosure.Real.IsNear.mulLit_ft qz32 (Real.cos qz33) 151349 262144 1 262144 65159 65536 13063717 8671461376 9861749491 17179869184 992907573097 1136585785475072 qz280 (@Enclosure.Real.IsNear.recentre' (Real.cos qz33) Bool.true 260636 262144 13063717 8671461376 65159 65536 13063717 8671461376 (ep72 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)) 151349 262144 1 262144 7019 65536 13063717 8671461376 1062318631 17179869184 989061146977 1136585785475072 qz280 (@Enclosure.Real.IsNear.neg (Real.sin qz33) Bool.true 7019 65536 13063717 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz33) Bool.true 28076 262144 13063717 8671461376 7019 65536 13063717 8671461376 (ep74 rfl rfl) rfl)) rfl)

noncomputable def ep76 := @ep49 9861749491 17179869184 992907573097 1136585785475072 Bool.false 1062318631 17179869184 989061146977 1136585785475072 Bool.true 10309555702506455040 1200190245 17179869184 1104886285715 568292892737536 Bool.true 130542654433343307776 1899645641 4294967296 2206027929393 1136585785475072 (ep50 (BSN.head_sum_c_succ qz21 2 3 rfl rfl) (ep66 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep67 ep75) rfl rfl

noncomputable abbrev qz281 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz281))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep77 := @Enclosure.Complex.IsNear.of_eq qz15 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.true 285079425 34359738368 856215704137 1136585785475072 Bool.false 34354626597 68719476736 1720957752077 2273171570950144 (BSN.cpow_neg_s_mk qz24 48711 1000 4 qz25 rfl)

noncomputable def ep78 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz281) 524289 262144 1 262144 65535 65536 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz281) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz281 qz26)) Bool.false 524289 262144 1 262144 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz281 qz26)) Bool.false 524289 262144 1 262144 524289 262144 1 262144 (BSN.sqrt_enclosure 4 1 262144 262145 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep79 := nat_lit 753960950911045074462890625

noncomputable def ep80 := nat_lit 117048680082474133384580175

noncomputable def ep81 := BSN.log_dyadic_bound 3 5 12 11 ep79 131072 33079 ep80 431467934736729065175 181704 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 3) (BSN.artanhQ 5) 0 11 ep80 ep79 431467934736729065175 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep82 := nat_lit 67889239307289906481233664450419613746013955067799410130480627219073073601

noncomputable def ep83 := nat_lit 278278412702595531909369356367009666242828713757909985904152976703587614720

noncomputable def ep84 := nat_lit 234970237127724882757719173368781340200468514015535357908739846442320321

noncomputable def ep85 := nat_lit 203197777447614269678185555004521278557640928175367159675624401964334580161

noncomputable def ep86 := nat_lit 12522528571616798935921621036515434980927292119105949365686883951661442662400

noncomputable def ep87 := BSN.cos_dyadic_bound_f 834404441 536870912 3 2 262144 66223 ep82 ep83 ep84 ep85 ep86 ep84 4350 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 834404441) qz274 0 2 ep82 ep83 ep84 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 834404441) qz275 0 2 ep85 ep86 ep84 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz38 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz282 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17701967) qz27)

noncomputable abbrev qz283 := (BSN.isNear_log_sfrac 4 1 181704 131072 1 33079 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 181704 131072 33079 rfl rfl rfl (ep81 rfl)))

noncomputable def ep88 := @Enclosure.Real.IsNear.cos_image qz37 qz282 Bool.false 17701967 262144 387 262144 Bool.true 4350 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 1106372943 16384000 48711 33079000 17701967 262144 387 262144 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz38 48711 1000 0 1 181704 131072 1 33079 1106372943 16384000 48711 33079000 qz29 qz283 rfl) rfl) (Enclosure.sfrac_false_div 17701967 262144) (BSN.cos_reduce2 qz282 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 58715992693747046416384) qz30) 226375608064910080 72057594037927936 Bool.false 4350 262144 10 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q2 17701967 262144 226375608064910080 72057594037927936 10 58715992693747046416384 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 4350 262144 58715992693747046416384 37778931862957161709568 834404441 536870912 66223 66158 (ep87 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep89 := nat_lit 122012654563419651760014420672060279670664744310826509948538137117177676225

noncomputable def ep90 := nat_lit 2504505714323359787184324207303086996185458423821189873137376790332288532480

noncomputable def ep91 := nat_lit 319176524425035152418430032622322705539035476553282373571461923174558728641

noncomputable def ep92 := nat_lit 45915938095928262765045943800556594930066737770055147674185241156091956428800

noncomputable def ep93 := BSN.sin_dyadic_bound_f 834404441 536870912 3 2 262144 66223 ep89 ep90 ep84 ep91 ep92 ep84 262107 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 834404441) qz269 0 2 ep89 ep90 ep84 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 834404441) qz270 0 2 ep91 ep92 ep84 rfl rfl rfl rfl) rfl rfl

noncomputable def ep94 := @Enclosure.Real.IsNear.sin_image qz37 qz282 Bool.false 17701967 262144 387 262144 Bool.true 262107 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 1106372943 16384000 48711 33079000 17701967 262144 387 262144 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz38 48711 1000 0 1 181704 131072 1 33079 1106372943 16384000 48711 33079000 qz29 qz283 rfl) rfl) (Enclosure.sfrac_false_div 17701967 262144) (BSN.sin_reduce2 qz282 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 58715992693747046416384) qz30) 226375608064910080 72057594037927936 Bool.false 262107 262144 10 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q2 17701967 262144 226375608064910080 72057594037927936 10 58715992693747046416384 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 262107 262144 58715992693747046416384 37778931862957161709568 834404441 536870912 66223 66158 (ep93 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz284 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 131071 262144 1 262144 131071 262144 1 262144 (ep78 rfl rfl) rfl)

noncomputable def ep95 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.true 285079425 34359738368 856215704137 1136585785475072 Bool.false 34354626597 68719476736 1720957752077 2273171570950144 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz37) 131071 262144 1 262144 2175 131072 13063717 8671461376 285079425 34359738368 856215704137 1136585785475072 qz284 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.true 4350 262144 13063717 8671461376 2175 131072 13063717 8671461376 (ep88 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 131071 262144 1 262144 262107 262144 13063717 8671461376 34354626597 68719476736 1720957752077 2273171570950144 qz284 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.true 262107 262144 13063717 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.true 262107 262144 13063717 8671461376 262107 262144 13063717 8671461376 (ep94 rfl rfl) rfl)) rfl)

noncomputable def ep96 := @ep47 285079425 34359738368 856215704137 1136585785475072 Bool.false 34354626597 68719476736 1720957752077 2273171570950144 Bool.true 46135850038575759360 2685459915 34359738368 3065988275567 1136585785475072 Bool.false 17009343267063463936 3960296341 68719476736 6133013610863 2273171570950144 (ep48 (BSN.head_sum_c_succ qz21 3 4 rfl rfl) (ep76 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep77 ep95) rfl rfl

noncomputable abbrev qz285 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz39 := (@Inv.inv Real Real.instInv (Real.sqrt qz285))

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep97 := @Enclosure.Complex.IsNear.of_eq qz13 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)))) Bool.true 30420489505 68719476736 1540121364369 2273171570950144 Bool.true 2183501875 34359738368 766385059481 1136585785475072 (BSN.cpow_neg_s_mk qz24 48711 1000 5 qz25 rfl)

noncomputable def ep98 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz285) 586171 262144 1 262144 58617 58618 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz285) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz285 qz26)) Bool.false 586171 262144 1 262144 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz285 qz26)) Bool.false 586171 262144 1 262144 586171 262144 1 262144 (BSN.sqrt_enclosure 5 1 293085 293086 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep99 := nat_lit 141613827518379161815574079375

noncomputable def ep100 := nat_lit 29325128709309236875766211300

noncomputable def ep101 := BSN.log_dyadic_bound 2 3 15 14 ep99 131072 33079 ep100 57299708096576225280000 210952 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP 2) (BSN.artanhQ 3) 0 14 ep100 ep99 57299708096576225280000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep102 := nat_lit 86958757555364823654312879930296619917907109746642456755453051994915061665

noncomputable def ep103 := nat_lit 119484011696107114415170074738328121704221004918057033252424232470429601

noncomputable def ep104 := nat_lit 227555676626066555195099648267867187587949881995148627734254068372206370721

noncomputable def ep105 := BSN.sin_dyadic_bound_f 766767549 536870912 3 2 262144 66223 ep102 ep90 ep103 ep104 ep92 ep103 259483 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 766767549) qz269 0 2 ep102 ep90 ep103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 766767549) qz270 0 2 ep104 ep92 ep103 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz41 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz286 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20551365) qz27)

noncomputable abbrev qz287 := (BSN.isNear_log_sfrac 5 1 210952 131072 1 33079 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 210952 131072 33079 rfl rfl rfl (ep101 rfl)))

noncomputable def ep106 := @Enclosure.Real.IsNear.cos_image qz40 qz286 Bool.false 20551365 262144 387 262144 Bool.true 259483 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 1284460359 16384000 48711 33079000 20551365 262144 387 262144 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz41 48711 1000 0 1 210952 131072 1 33079 1284460359 16384000 48711 33079000 qz29 qz287 rfl) rfl) (Enclosure.sfrac_false_div 20551365 262144) (BSN.cos_reduce1 qz286 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 53956469562740100300800) qz30) 226375608064910080 72057594037927936 Bool.false 259483 262144 12 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q1 20551365 262144 226375608064910080 72057594037927936 12 53956469562740100300800 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 259483 262144 53956469562740100300800 37778931862957161709568 766767549 536870912 66223 66158 (ep105 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep107 := nat_lit 48363524869289838525469453327826268008483603639209390212252772989384114081

noncomputable def ep108 := nat_lit 144851606584477301347578019834002147782042368907792056570253470503211483041

noncomputable def ep109 := BSN.cos_dyadic_bound_f 766767549 536870912 3 2 262144 66223 ep107 ep83 ep103 ep108 ep86 ep103 37250 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 766767549) qz274 0 2 ep107 ep83 ep103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 766767549) qz275 0 2 ep108 ep86 ep103 rfl rfl rfl rfl) rfl rfl

noncomputable def ep110 := @Enclosure.Real.IsNear.sin_image qz40 qz286 Bool.false 20551365 262144 387 262144 Bool.false 37250 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 1284460359 16384000 48711 33079000 20551365 262144 387 262144 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz41 48711 1000 0 1 210952 131072 1 33079 1284460359 16384000 48711 33079000 qz29 qz287 rfl) rfl) (Enclosure.sfrac_false_div 20551365 262144) (BSN.sin_reduce1 qz286 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 53956469562740100300800) qz30) 226375608064910080 72057594037927936 Bool.false 37250 262144 12 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q1 20551365 262144 226375608064910080 72057594037927936 12 53956469562740100300800 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 37250 262144 53956469562740100300800 37778931862957161709568 766767549 536870912 66223 66158 (ep109 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz288 := (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 117235 262144 1 262144 117235 262144 1 262144 (ep98 rfl rfl) rfl)

noncomputable def ep111 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40))) Bool.true 30420489505 68719476736 1540121364369 2273171570950144 Bool.true 2183501875 34359738368 766385059481 1136585785475072 (@Enclosure.Real.IsNear.mulLit_ft qz39 (Real.cos qz40) 117235 262144 1 262144 259483 262144 13063717 8671461376 30420489505 68719476736 1540121364369 2273171570950144 qz288 (@Enclosure.Real.IsNear.recentre' (Real.cos qz40) Bool.true 259483 262144 13063717 8671461376 259483 262144 13063717 8671461376 (ep106 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)) 117235 262144 1 262144 18625 131072 13063717 8671461376 2183501875 34359738368 766385059481 1136585785475072 qz288 (@Enclosure.Real.IsNear.neg (Real.sin qz40) Bool.false 18625 131072 13063717 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz40) Bool.false 37250 262144 13063717 8671461376 18625 131072 13063717 8671461376 (ep110 rfl rfl) rfl)) rfl)

noncomputable def ep112 := @ep45 30420489505 68719476736 1540121364369 2273171570950144 Bool.true 2183501875 34359738368 766385059481 1136585785475072 Bool.true 1229783460572592865280 35791409335 68719476736 7672097915503 2273171570950144 Bool.true 13974360165567168512 406707409 68719476736 7665783729825 2273171570950144 (ep46 (BSN.head_sum_c_succ qz21 4 5 rfl rfl) (ep96 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep97 ep111) rfl rfl

noncomputable abbrev qz289 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt qz289))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep113 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.false 2712983755 8589934592 705761047745 1136585785475072 Bool.false 555514065 2147483648 704547114603 1136585785475072 (BSN.cpow_neg_s_mk qz24 48711 1000 6 qz25 rfl)

noncomputable abbrev qz290 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz26)

noncomputable def ep114 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz289) 642119 262144 1 262144 53509 53511 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz289) (Real.sqrt qz290) Bool.false 642119 262144 1 262144 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz290) Bool.false 642119 262144 1 262144 642119 262144 1 262144 (BSN.sqrt_enclosure 6 1 321059 321060 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep115 := BSN.log_dyadic_bound 2 10 4 3 105000000 131072 33079 1434560 960 53145 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz44 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep116 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz44 48711 1000 0 1 4034681531866359 2251799813685248 500000000033079 16539500000000000000 196533372098742213249 2251799813685248000 24355500001611311169 16539500000000000000000 qz29 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000033079 16539500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz290) Bool.false 8461340443916598509568 4722366482869645213696 1000000000066158 33079000000000000000 4034681531866359 2251799813685248 500000000033079 16539500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 53145 131072 24973259072661432 36028797018963968 33079 1000000000000000 rfl rfl rfl rfl (ep115 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep117 := nat_lit 50858923054157956223586886506250000

noncomputable def ep118 := BSN.sin_dyadic_bound_f 474888650 536870912 2 1 262144 66223 ep117 ep57 ep117 ep117 ep58 ep117 202802 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 474888650) qz269 0 1 ep117 ep57 ep117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 474888650) qz270 0 1 ep117 ep58 ep117 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz291 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 22879495) qz27)

noncomputable def ep119 := @Enclosure.Real.IsNear.cos_image qz43 qz291 Bool.false 22879495 262144 387 262144 Bool.false 202802 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 196533372098742213249 2251799813685248000 24355500001611311169 16539500000000000000000 22879495 262144 387 262144 (ep116 rfl) rfl) (Enclosure.sfrac_false_div 22879495 262144) (BSN.cos_reduce3 qz291 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 33417317974375703511040) qz30) 226375608064910080 72057594037927936 Bool.false 202802 262144 13 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q3 22879495 262144 226375608064910080 72057594037927936 13 33417317974375703511040 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 202802 262144 33417317974375703511040 37778931862957161709568 474888650 536870912 66223 66158 (ep118 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep120 := nat_lit 7100912587755280177233461029711692440256069440608587375615540710500000000

noncomputable def ep121 := nat_lit 2586630054228759653758636711578169110656058267558718331289062500000000

noncomputable def ep122 := nat_lit 21297564503157383012392865815711920982546896205290644690184044006500000000

noncomputable def ep123 := BSN.cos_dyadic_bound_f 474888650 536870912 3 2 262144 66223 ep120 ep83 ep121 ep122 ep86 ep121 166104 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 474888650) qz274 0 2 ep120 ep83 ep121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 474888650) qz275 0 2 ep122 ep86 ep121 rfl rfl rfl rfl) rfl rfl

noncomputable def ep124 := @Enclosure.Real.IsNear.sin_image qz43 qz291 Bool.false 22879495 262144 387 262144 Bool.true 166104 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 196533372098742213249 2251799813685248000 24355500001611311169 16539500000000000000000 22879495 262144 387 262144 (ep116 rfl) rfl) (Enclosure.sfrac_false_div 22879495 262144) (BSN.sin_reduce3 qz291 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 33417317974375703511040) qz30) 226375608064910080 72057594037927936 Bool.false 166104 262144 13 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q3 22879495 262144 226375608064910080 72057594037927936 13 33417317974375703511040 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 166104 262144 33417317974375703511040 37778931862957161709568 474888650 536870912 66223 66158 (ep123 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz292 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 107020 262144 2 262144 26755 65536 1 131072 (ep114 rfl rfl) rfl)

noncomputable def ep125 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.false 2712983755 8589934592 705761047745 1136585785475072 Bool.false 555514065 2147483648 704547114603 1136585785475072 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz43) 26755 65536 1 131072 101401 131072 13063717 8671461376 2712983755 8589934592 705761047745 1136585785475072 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.false 202802 262144 13063717 8671461376 101401 131072 13063717 8671461376 (ep119 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 26755 65536 1 131072 20763 32768 13063717 8671461376 555514065 2147483648 704547114603 1136585785475072 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.true 20763 32768 13063717 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.true 166104 262144 13063717 8671461376 20763 32768 13063717 8671461376 (ep124 rfl rfl) rfl)) rfl)

noncomputable def ep126 := @ep43 2712983755 8589934592 705761047745 1136585785475072 Bool.false 555514065 2147483648 704547114603 1136585785475072 Bool.true 121011041106279792640 14087539295 68719476736 9083620010993 2273171570950144 Bool.false 37301238355940343808 17369742671 68719476736 9074877959031 2273171570950144 (ep44 (BSN.head_sum_c_succ qz21 5 6 rfl rfl) (ep112 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep113 ep125) rfl rfl

noncomputable abbrev qz293 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv (Real.sqrt qz293))

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep127 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)))) Bool.false 22289757165 68719476736 1301820825029 2273171570950144 Bool.true 3333382083 17179869184 649415357491 1136585785475072 (BSN.cpow_neg_s_mk qz24 48711 1000 7 qz25 rfl)

noncomputable abbrev qz294 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) qz26)

noncomputable def ep128 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz293) 693567 262144 1 262144 49540 49541 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz293) (Real.sqrt qz294) Bool.false 693567 262144 1 262144 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz294) Bool.false 693567 262144 1 262144 693567 262144 1 262144 (BSN.sqrt_enclosure 7 1 346783 346784 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep129 := BSN.log_dyadic_bound 3 11 5 4 202569142545 131072 33079 5259111624 688905 73349 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz47 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep130 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz47 48711 1000 0 1 4381783608859895 2251799813685248 500000000033079 16539500000000000000 42688212274234869069 450359962737049600 24355500001611311169 16539500000000000000000 qz29 (BSN.isNear_log_sfrac 7 1 4381783608859895 2251799813685248 500000000033079 16539500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz294) Bool.false 9189266258887746519040 4722366482869645213696 1000000000066158 33079000000000000000 4381783608859895 2251799813685248 500000000033079 16539500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 73349 131072 24973259072661432 36028797018963968 33079 1000000000000000 rfl rfl rfl rfl (ep129 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep131 := nat_lit 7016536681706209642812496936960000

noncomputable def ep132 := BSN.cos_dyadic_bound_f 289421440 536870912 2 1 262144 66223 ep131 ep61 ep131 ep131 ep62 ep131 224965 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 289421440) qz274 0 1 ep131 ep61 ep131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 289421440) qz275 0 1 ep131 ep62 ep131 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz295 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24847809) qz27)

noncomputable def ep133 := @Enclosure.Real.IsNear.cos_image qz46 qz295 Bool.false 24847809 262144 387 262144 Bool.false 224965 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 42688212274234869069 450359962737049600 24355500001611311169 16539500000000000000000 24847809 262144 387 262144 (ep130 rfl) rfl) (Enclosure.sfrac_false_div 24847809 262144) (BSN.cos_reduce0 qz295 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20366223273876938293248) qz30) 226375608064910080 72057594037927936 Bool.false 224965 262144 15 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 24847809 262144 226375608064910080 72057594037927936 15 20366223273876938293248 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 224965 262144 20366223273876938293248 37778931862957161709568 289421440 536870912 66223 66158 (ep132 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep134 := BSN.sin_dyadic_bound_f 289421440 536870912 2 1 262144 66223 ep131 ep57 ep131 ep131 ep58 ep131 134572 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 289421440) qz269 0 1 ep131 ep57 ep131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 289421440) qz270 0 1 ep131 ep58 ep131 rfl rfl rfl rfl) rfl rfl

noncomputable def ep135 := @Enclosure.Real.IsNear.sin_image qz46 qz295 Bool.false 24847809 262144 387 262144 Bool.false 134572 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 42688212274234869069 450359962737049600 24355500001611311169 16539500000000000000000 24847809 262144 387 262144 (ep130 rfl) rfl) (Enclosure.sfrac_false_div 24847809 262144) (BSN.sin_reduce0 qz295 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20366223273876938293248) qz30) 226375608064910080 72057594037927936 Bool.false 134572 262144 15 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 24847809 262144 226375608064910080 72057594037927936 15 20366223273876938293248 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 134572 262144 20366223273876938293248 37778931862957161709568 289421440 536870912 66223 66158 (ep134 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz296 := (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 99081 262144 1 262144 99081 262144 1 262144 (ep128 rfl rfl) rfl)

noncomputable def ep136 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46))) Bool.false 22289757165 68719476736 1301820825029 2273171570950144 Bool.true 3333382083 17179869184 649415357491 1136585785475072 (@Enclosure.Real.IsNear.mulLit_ff qz45 (Real.cos qz46) 99081 262144 1 262144 224965 262144 13063717 8671461376 22289757165 68719476736 1301820825029 2273171570950144 qz296 (@Enclosure.Real.IsNear.recentre' (Real.cos qz46) Bool.false 224965 262144 13063717 8671461376 224965 262144 13063717 8671461376 (ep133 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)) 99081 262144 1 262144 33643 65536 13063717 8671461376 3333382083 17179869184 649415357491 1136585785475072 qz296 (@Enclosure.Real.IsNear.neg (Real.sin qz46) Bool.false 33643 65536 13063717 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz46) Bool.false 134572 262144 13063717 8671461376 33643 65536 13063717 8671461376 (ep135 rfl rfl) rfl)) rfl)

noncomputable def ep137 := @ep41 22289757165 68719476736 1301820825029 2273171570950144 Bool.true 3333382083 17179869184 649415357491 1136585785475072 Bool.false 563652120101068472320 4101108935 34359738368 5192720418011 1136585785475072 Bool.false 69341634342605029376 4036214339 68719476736 10373708674013 2273171570950144 (ep42 (BSN.head_sum_c_succ qz21 6 7 rfl rfl) (ep126 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep127 ep136) rfl rfl

noncomputable abbrev qz297 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz48 := (@Inv.inv Real Real.instInv (Real.sqrt qz297))

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep138 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)))) Bool.false 4399660881 17179869184 152919969973 284146446368768 Bool.true 8375255271 34359738368 611377173963 1136585785475072 (BSN.cpow_neg_s_mk qz24 48711 1000 8 qz25 rfl)

noncomputable abbrev qz298 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz26)

noncomputable def ep139 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz297) 741455 262144 1 262144 46340 46342 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz297) (Real.sqrt qz298) Bool.false 741455 262144 1 262144 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz298) Bool.false 741455 262144 1 262144 741455 262144 1 262144 (BSN.sqrt_enclosure 8 1 370727 370728 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep140 := BSN.log_dyadic_bound 0 16 1 0 1 131072 33079 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz50 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep141 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz50 48711 1000 0 1 9364972152248037 4503599627370496 1000000000099237 33079000000000000000 456177158508154130307 4503599627370496000 48711000004833933507 33079000000000000000000 qz29 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000099237 33079000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz298) Bool.false 9819885039515637645312 4722366482869645213696 1000000000099237 33079000000000000000 9364972152248037 4503599627370496 1000000000099237 33079000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 131072 24973259072661432 36028797018963968 33079 1000000000000000 rfl rfl rfl rfl (ep140 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep142 := nat_lit 27820023033475815661462722139504081

noncomputable def ep143 := BSN.cos_dyadic_bound_f 408403421 536870912 2 1 262144 66223 ep142 ep61 ep142 ep142 ep62 ep142 189882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 408403421) qz274 0 1 ep142 ep61 ep142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 408403421) qz275 0 1 ep142 ep62 ep142 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz299 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 26553005) qz27)

noncomputable def ep144 := @Enclosure.Real.IsNear.cos_image qz49 qz299 Bool.false 26553005 262144 387 262144 Bool.false 189882 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 456177158508154130307 4503599627370496000 48711000004833933507 33079000000000000000000 26553005 262144 387 262144 (ep141 rfl) rfl) (Enclosure.sfrac_false_div 26553005 262144) (BSN.cos_reduce0 qz299 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28738835917802915758080) qz30) 226375608064910080 72057594037927936 Bool.false 189882 262144 16 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 26553005 262144 226375608064910080 72057594037927936 16 28738835917802915758080 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 189882 262144 28738835917802915758080 37778931862957161709568 408403421 536870912 66223 66158 (ep143 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep145 := BSN.sin_dyadic_bound_f 408403421 536870912 2 1 262144 66223 ep142 ep57 ep142 ep142 ep58 ep142 180731 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 408403421) qz269 0 1 ep142 ep57 ep142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 408403421) qz270 0 1 ep142 ep58 ep142 rfl rfl rfl rfl) rfl rfl

noncomputable def ep146 := @Enclosure.Real.IsNear.sin_image qz49 qz299 Bool.false 26553005 262144 387 262144 Bool.false 180731 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 456177158508154130307 4503599627370496000 48711000004833933507 33079000000000000000000 26553005 262144 387 262144 (ep141 rfl) rfl) (Enclosure.sfrac_false_div 26553005 262144) (BSN.sin_reduce0 qz299 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28738835917802915758080) qz30) 226375608064910080 72057594037927936 Bool.false 180731 262144 16 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 26553005 262144 226375608064910080 72057594037927936 16 28738835917802915758080 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 180731 262144 28738835917802915758080 37778931862957161709568 408403421 536870912 66223 66158 (ep145 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz300 := (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 92682 262144 2 262144 46341 131072 1 131072 (ep139 rfl rfl) rfl)

noncomputable def ep147 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49))) Bool.false 4399660881 17179869184 152919969973 284146446368768 Bool.true 8375255271 34359738368 611377173963 1136585785475072 (@Enclosure.Real.IsNear.mulLit_ff qz48 (Real.cos qz49) 46341 131072 1 131072 94941 131072 13063717 8671461376 4399660881 17179869184 152919969973 284146446368768 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz49) Bool.false 189882 262144 13063717 8671461376 94941 131072 13063717 8671461376 (ep144 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)) 46341 131072 1 131072 180731 262144 13063717 8671461376 8375255271 34359738368 611377173963 1136585785475072 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz49) Bool.false 180731 262144 13063717 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz49) Bool.false 180731 262144 13063717 8671461376 180731 262144 13063717 8671461376 (ep146 rfl rfl) rfl)) rfl)

noncomputable def ep148 := @ep39 4399660881 17179869184 152919969973 284146446368768 Bool.true 8375255271 34359738368 611377173963 1136585785475072 Bool.false 221627711791717941248 12900430697 34359738368 5804400297903 1136585785475072 Bool.true 436859891068335816704 12714296203 68719476736 11596463021939 2273171570950144 (ep40 (BSN.head_sum_c_succ qz21 7 8 rfl rfl) (ep137 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep138 ep147) rfl rfl

theorem EMRow10.d6 : Enclosure.Complex.IsNear qz4 Bool.false 12900430697 34359738368 5804400297903 1136585785475072 Bool.true 12714296203 68719476736 11596463021939 2273171570950144 := ep38 (BSN.head_sum_c_succ qz21 8 9 rfl rfl) (ep148 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow10.d7 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow10.d8 : @Eq Nat (Nat.pow 10 1) 10 := @Eq.refl Nat 10

noncomputable def ep149 := nat_lit 954298247351906560079956113989

noncomputable def ep150 := nat_lit 1282451256206579273218129920000

noncomputable def ep151 := nat_lit 6077117716807647867288338207733974363

noncomputable def ep152 := nat_lit 935522748424743945417564644421140480000

noncomputable abbrev qz449 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz429 := qz449

noncomputable abbrev qz301 := qz429

noncomputable abbrev qz51 := qz301

noncomputable abbrev qz52 := (@instHSub Real Real.instSub)

noncomputable abbrev qz430 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz302 := qz430

noncomputable abbrev qz53 := qz302

noncomputable abbrev qz450 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz451 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz431 := (@HAdd.hAdd Complex Complex Complex qz447 (@HAdd.hAdd Complex Complex Complex qz447 qz450 (@HMul.hMul Complex Complex Complex qz449 Complex.I (@HDiv.hDiv Complex Complex Complex qz451 (↑qz448) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz303 := qz431

noncomputable abbrev qz54 := (Complex.Stirling.logGammaStirling 1 qz303)

noncomputable abbrev qz432 := (@HAdd.hAdd Complex Complex Complex qz447 qz450 (@HMul.hMul Complex Complex Complex qz449 Complex.I (@HDiv.hDiv Complex Complex Complex qz451 (↑qz448) (2 : Complex))))

noncomputable abbrev qz304 := qz432

noncomputable abbrev qz55 := qz304

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz254 (@HDiv.hDiv Real Real Real qz257 qz267 (2 : Real)) (Real.log Real.pi))

noncomputable def ep153 := Complex.re (@HMul.hMul Complex Complex Complex qz51 (Complex.exp (@HMul.hMul Complex Complex Complex qz51 Complex.I ↑(@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56))) (zetaApproximant qz21 1 10))

noncomputable def ep154 := @Enclosure.Real.IsNear.of_eq ep153 (@HSub.hSub Real Real Real qz52 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) (Complex.re (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) (Complex.im (zetaApproximant qz21 1 10))))

noncomputable def ep155 := nat_lit 79523007239669586563399062347

noncomputable def ep156 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) (Complex.re (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) (Complex.im (zetaApproximant qz21 1 10))) ep155

noncomputable def ep157 := nat_lit 106870938017214939434844160000

noncomputable def ep158 := nat_lit 44248973793581962433165976561260369

noncomputable def ep159 := nat_lit 6878843738417234892776210620743680000

noncomputable def ep160 := nat_lit 51298050248263170928725196800

noncomputable def ep161 := nat_lit 59257280880500976377765395402564179

noncomputable def ep162 := nat_lit 4079469953707298267801570705021106552938229235816438169600

noncomputable def ep163 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) (Complex.re (zetaApproximant qz21 1 10)) 262143 262144 5587863

noncomputable def ep164 := nat_lit 1223040825087146065920000

noncomputable def ep165 := nat_lit 641842484949383878625499717

noncomputable def ep166 := nat_lit 107885246541487212572180480000

noncomputable def ep167 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) Bool.false 262143 262144 5587863

noncomputable abbrev qz305 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 205889) (@Nat.cast Real Real.instNatCast 8192))

noncomputable def ep168 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56) qz305 Bool.false 205889 8192 161

noncomputable def ep169 := nat_lit 1083932672000000000000000000

noncomputable def ep170 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56) Bool.false 452754715946624813257 18014398509481984000 663804439475659004487407 ep169

noncomputable def ep171 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56 955004471205833279689 18014398509481984000 260976647225659004487407 ep169 3654347931 131072000

noncomputable def ep172 := nat_lit 59343466128556007523221504000

noncomputable def ep173 := nat_lit 270983168000000000000000000

noncomputable def ep174 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 171753063415298421319 4503599627370496000 110541662816985355062237 ep173 Bool.false 955004471205833279689 18014398509481984000

noncomputable def ep175 := @Enclosure.Complex.IsNear.subLitP qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 142989111312921798319 4503599627370496000 106445662814546506550237 ep173 Bool.false 1010489790623355647689 18014398509481984000 228208647224575071815407

noncomputable def ep176 := nat_lit 773507032396879139329051651918004224

noncomputable def ep177 := nat_lit 268809861291234270949715217674665984

noncomputable abbrev qz452 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz433 := qz452

noncomputable abbrev qz306 := (@HSub.hSub Complex Complex Complex qz430 qz431 qz433)

noncomputable abbrev qz307 := (Complex.log qz431)

noncomputable abbrev qz57 := (@HSub.hSub Complex Complex Complex qz302 (@HMul.hMul Complex Complex Complex qz301 qz306 qz307) qz303)

noncomputable abbrev qz308 := qz433

noncomputable abbrev qz58 := (@HMul.hMul Complex Complex Complex qz301 qz308 ↑(Real.log qz258))

noncomputable abbrev qz434 := qz451

noncomputable abbrev qz309 := qz434

noncomputable abbrev qz59 := qz309

noncomputable abbrev qz60 := (@instHMul Nat instMulNat)

noncomputable abbrev qz435 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz310 := qz435

noncomputable abbrev qz61 := qz310

noncomputable abbrev qz62 := qz303

noncomputable abbrev qz311 := (@instHSub Int Int.instSub)

noncomputable abbrev qz63 := qz311

noncomputable abbrev qz312 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz64 := qz312

noncomputable abbrev qz313 := (@instHMul Int Int.instMul)

noncomputable abbrev qz65 := qz313

noncomputable abbrev qz314 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz66 := qz314

noncomputable def ep178 := @Enclosure.Complex.IsNear.of_eq qz54 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz57 qz58) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz61 qz62 (@HSub.hSub Int Int Int qz63 qz64 (@HMul.hMul Int Int Int qz65 qz66 (@Nat.cast Int instNatCastInt k)))))) Bool.true 142989111312921798319

noncomputable def ep179 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz57 qz58) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz61 qz62 (@HSub.hSub Int Int Int qz63 qz64 (@HMul.hMul Int Int Int qz65 qz66 (@Nat.cast Int instNatCastInt k))))) Bool.true 142990522794783942319 4503599627370496000

noncomputable def ep180 := nat_lit 307066778386551372992806387712

noncomputable def ep181 := nat_lit 1085005150917299990150288244736000

noncomputable def ep182 := @ep179 51975236452848612169 132316000000000000000000 Bool.false 1010550905906010666697 18014398509481984000 27855500014617577021 132316000000000000000000 Bool.false 673047 2147483648 3 2147483648 Bool.true 3642754713 1073741824000 16237 1073741824000 Bool.true ep180 142989111312921798319 4503599627370496000 106445662814546506550237 ep173 Bool.false ep181

noncomputable def ep183 := @Enclosure.Complex.IsNear.addLitP qz57 qz58 Bool.true 147129033022125254319 4503599627370496000 50461000002653299669 132316000000000000000000

noncomputable def ep184 := nat_lit 37484107607515841775271936

noncomputable def ep185 := @ep183 Bool.false 1010550905906010666697 18014398509481984000 27855500014617577021 132316000000000000000000 Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 Bool.true ep184 142990522794783942319 4503599627370496000 51975236452848612169 132316000000000000000000 Bool.false 1010550905906010666697 1010550905906010666697 18014398509481984000

noncomputable abbrev qz67 := (@HMul.hMul Complex Complex Complex qz301 qz306 qz307)

noncomputable def ep186 := @Enclosure.Complex.IsNear.subLitP qz67 qz62 Bool.true 136995933860541638319 4503599627370496000 50461000002653299669 132316000000000000000000 Bool.false 1449300588803699128009

noncomputable def ep187 := nat_lit 4042203623624042666788000

noncomputable def ep188 := @ep186 18014398509481984000 27855500014617577021 132316000000000000000000 Bool.false 9000 4000 0 1 Bool.false 97422 4000 0 1 Bool.true 588516132088501017276000 147129033022125254319 4503599627370496000 50461000002653299669 132316000000000000000000 Bool.false ep187 1010550905906010666697 18014398509481984000 27855500014617577021 132316000000000000000000

noncomputable abbrev qz68 := qz306

noncomputable abbrev qz69 := qz307

noncomputable def ep189 := @Enclosure.Complex.IsNear.mul qz68 qz69 Bool.true 136995933860541638319 4503599627370496000 50461000002653299669 132316000000000000000000 Bool.false 1449300588803699128009 18014398509481984000 27855500014617577021

noncomputable abbrev qz70 := (Complex.re qz306)

noncomputable abbrev qz71 := (Complex.re qz307)

noncomputable abbrev qz72 := (Complex.im qz306)

noncomputable abbrev qz73 := (Complex.im qz307)

noncomputable def ep190 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz70 qz71) (@HMul.hMul Real Real Real qz0 qz72 qz73) 201572428945170633 36028797018963968 3500000002083977 264632000000000000000 40548121869671991861 1125899906842624000

noncomputable def ep191 := nat_lit 1233949673371216875726025083687272448

noncomputable def ep192 := @Enclosure.Real.IsNear.mulLit_ff qz70 qz71 7000 4000 0 1 28796061277881519 9007199254740992 500000000297711 66158000000000000000

noncomputable def ep193 := @Enclosure.Complex.IsNear.re_isNear qz68 Bool.false 7000 4000 0 1 Bool.false 97422 4000 0 1

noncomputable abbrev qz315 := (Enclosure.sfrac Bool.false 97422 4000)

noncomputable abbrev qz74 := qz315

noncomputable def ep194 := @Enclosure.Complex.IsNear.of_eq qz68 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz74) Bool.false 7000 4000 0 1 Bool.false 97422 4000 0

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz75 := (Complex.mk qz316 qz315)

noncomputable def ep195 := @Enclosure.Complex.IsNear.of_eq qz69 (Complex.log qz75) Bool.false 28796061277881519 9007199254740992 500000000297711 66158000000000000000 Bool.false 832422283871651 562949953421312 1000000000033079 66158000000000000000

noncomputable def ep196 := nat_lit 1493684325869471201042839626457972609847040

noncomputable def ep197 := nat_lit 3015857374421103582613417191136666585088

noncomputable def ep198 := nat_lit 10881671497642135475782622622489969408

noncomputable def ep199 := BSN.log_dyadic_bound 1380046084 17764046084 3 2 ep196 262144 66158 ep197 ep198 40812 19144092168 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1380046084) (BSN.artanhQ 17764046084) 0 2 ep197 ep196 ep198 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz76 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz317 := (Real.log (Enclosure.sfrac Bool.false 9572046084 16000000))

noncomputable abbrev qz318 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep200 := @Enclosure.Real.IsNear.mulLit_ff qz76 qz317 1 2 0 1 28796061277881519 4503599627370496 500000000297711 33079000000000000000 28796061277881519 9007199254740992 500000000297711 66158000000000000000 qz318 (BSN.isNear_log_sfrac 9572046084 16000000 28796061277881519 4503599627370496 500000000297711 33079000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9572046084) qz319)) Bool.false 60389717501031783333888 9444732965739290427392 1000000000595422 66158000000000000000 28796061277881519 4503599627370496 500000000297711 33079000000000000000 (BSN.log_rat_reduce_isNear 9572046084 16000000 9 19144092168 16384000000 40812 262144 24973259072661432 36028797018963968 66158 1000000000000000 rfl rfl rfl rfl (ep199 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep201 := BSN.arctan_dyadic_bound_f 9000 97422 1 0 262144 66158 0 1 1 0 1 1 24148 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 97422) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 97422) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz77 := (@HMul.hMul Real Real Real qz254 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz78 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz318 BSN.pi_near_15 rfl)

noncomputable abbrev qz320 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 97422)))

noncomputable def ep202 := @Enclosure.Real.IsNear.subLit_ff_p qz77 qz320 884279719003555 562949953421312 1 2000000000000000 24148 262144 1 66158 218214507183250079744 832422283871651 562949953421312 1000000000033079 66158000000000000000 qz78 (ep201 rfl) rfl rfl

noncomputable abbrev qz321 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 97422) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep203 := @Enclosure.Complex.IsNear.re_isNear qz69 Bool.false 28796061277881519 9007199254740992 500000000297711 66158000000000000000 Bool.false 832422283871651 562949953421312 1000000000033079 66158000000000000000 (ep195 (@congrArg Complex Complex qz62 qz75 Complex.log (BSN.w_shift_mk qz24 Bool.false 48711 1000 2 qz25 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz75) Bool.false 28796061277881519 9007199254740992 500000000297711 66158000000000000000 Bool.false 832422283871651 562949953421312 1000000000033079 66158000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz75)) (@HMul.hMul Real Real Real qz0 qz76 qz317) Bool.false 28796061277881519 9007199254740992 500000000297711 66158000000000000000 (Enclosure.clog_re_eq 9000 97422 4000 9572046084 16000000 rfl rfl rfl) (ep200 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz75)) qz321 Bool.false 832422283871651 562949953421312 1000000000033079 66158000000000000000 (Enclosure.clog_im_eq 9000 97422 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz321 (@HSub.hSub Real Real Real qz52 qz77 qz320) Bool.false 832422283871651 562949953421312 1000000000033079 66158000000000000000 (BSN.arctan_recip 97422 9000 rfl rfl) ep202))))

noncomputable def ep204 := @Enclosure.Real.IsNear.mulLit_ff qz72 qz73 97422 4000 0 1 832422283871651 562949953421312 1000000000033079 66158000000000000000

noncomputable def ep205 := @Enclosure.Complex.IsNear.im_isNear qz68 Bool.false 7000 4000 0 1 Bool.false 97422 4000 0 1

noncomputable def ep206 := @Enclosure.Complex.IsNear.im_isNear qz69 Bool.false 28796061277881519 9007199254740992 500000000297711 66158000000000000000 Bool.false 832422283871651 562949953421312 1000000000033079 66158000000000000000 (ep195 (@congrArg Complex Complex qz62 qz75 Complex.log (BSN.w_shift_mk qz24 Bool.false 48711 1000 2 qz25 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz75) Bool.false 28796061277881519 9007199254740992 500000000297711 66158000000000000000 Bool.false 832422283871651 562949953421312 1000000000033079 66158000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz75)) (@HMul.hMul Real Real Real qz0 qz76 qz317) Bool.false 28796061277881519 9007199254740992 500000000297711 66158000000000000000 (Enclosure.clog_re_eq 9000 97422 4000 9572046084 16000000 rfl rfl rfl) (ep200 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz75)) qz321 Bool.false 832422283871651 562949953421312 1000000000033079 66158000000000000000 (Enclosure.clog_im_eq 9000 97422 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz321 (@HSub.hSub Real Real Real qz52 qz77 qz320) Bool.false 832422283871651 562949953421312 1000000000033079 66158000000000000000 (BSN.arctan_recip 97422 9000 rfl rfl) ep202))))

noncomputable abbrev qz322 := (Enclosure.Real.IsNear.const Bool.false 97422 4000)

noncomputable abbrev qz79 := (@ep194 1 (BSN.w_sub_half_mk qz267 Bool.false 48711 1000 2 qz268 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz315 Bool.false 7000 4000 0 1 Bool.false 97422 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz322))

noncomputable def ep207 := @ep190 48711000001611311169 132316000000000000000000 ep191 136995933860541638319 4503599627370496000 50461000002653299669 132316000000000000000000 (@ep192 201572428945170633 36028797018963968 3500000002083977 264632000000000000000 (ep193 qz79) ep203 rfl) (@ep204 40548121869671991861 1125899906842624000 48711000001611311169 132316000000000000000000 (ep205 qz79) ep206 rfl) rfl

noncomputable def ep208 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz70 qz73) (@HMul.hMul Real Real Real qz0 qz72 qz71) 5826955987101557 2251799813685248 7000000000231553 264632000000000000000 1402684940906886672009 18014398509481984000

noncomputable def ep209 := nat_lit 3263534795842089920035486482386911232

noncomputable def ep210 := @Enclosure.Real.IsNear.mulLit_ff qz70 qz73 7000 4000 0 1 832422283871651 562949953421312 1000000000033079 66158000000000000000

noncomputable def ep211 := @Enclosure.Real.IsNear.mulLit_ff qz72 qz71 97422 4000 0 1 28796061277881519 9007199254740992 500000000297711 66158000000000000000

noncomputable def ep212 := @ep208 24355500014501800521 132316000000000000000000 ep209 1449300588803699128009 18014398509481984000 27855500014617577021 132316000000000000000000 (@ep210 5826955987101557 2251799813685248 7000000000231553 264632000000000000000 (ep193 qz79) ep206 rfl) (@ep211 1402684940906886672009 18014398509481984000 24355500014501800521 132316000000000000000000 (ep205 qz79) ep203 rfl) rfl

noncomputable def ep213 := @Enclosure.Complex.IsNear.of_eq qz62 qz75 Bool.false 9000 4000 0 1 Bool.false 97422 4000 0 1 (BSN.w_shift_mk qz24 Bool.false 48711 1000 2 qz25 rfl)

noncomputable abbrev qz323 := (ep213 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 97422 4000) Bool.false 9000 4000 0 1 Bool.false 97422 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 97422 4000)))

noncomputable abbrev qz80 := qz323

noncomputable def ep214 := ep188 (@ep189 132316000000000000000000 (ep207 rfl) (ep212 rfl)) qz80 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz81 := qz308

noncomputable def ep215 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz81) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz81) (Complex.im ↑qz3)) 240893 262144 3 262144 0 1 0 1 240893 240893

noncomputable def ep216 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz81) (Complex.re ↑qz3) 1 2 0 1 240893 131072 3 131072 240893 262144 3 262144

noncomputable abbrev qz82 := (@Enclosure.Complex.IsNear.of_eq qz308 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz265) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz265 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz318 qz277))

noncomputable def ep217 := ep216 (@Enclosure.Complex.IsNear.re_isNear qz81 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz82) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 240893 131072 3 131072 (Complex.ofReal_re qz3) EMRow10.d4)

noncomputable def ep218 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz81) (Complex.im ↑qz3) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep219 := ep218 (@Enclosure.Complex.IsNear.im_isNear qz81 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz82) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz20 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz20 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz31)

noncomputable def ep220 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz81) (Complex.im ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz81) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep221 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz81) (Complex.im ↑qz3) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep222 := ep221 (@Enclosure.Complex.IsNear.re_isNear qz81 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz82) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz20 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz20 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz31)

noncomputable def ep223 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz81) (Complex.re ↑qz3) 0 1 0 1 240893 131072 3 131072 0 1 0 1

noncomputable def ep224 := ep223 (@Enclosure.Complex.IsNear.im_isNear qz81 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz82) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 240893 131072 3 131072 (Complex.ofReal_re qz3) EMRow10.d4)

noncomputable def ep225 := @ep185 27855500014617577021 132316000000000000000000 (ep214 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz81 (↑qz3) Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 (@ep215 262144 3 262144 (ep217 rfl) (ep219 rfl) rfl rfl) (@ep220 1 0 1 (ep222 rfl) (ep224 rfl) rfl rfl))

noncomputable abbrev qz83 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz324 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz84 := (@HMul.hMul Complex Complex Complex qz301 (@HMul.hMul Complex Complex Complex qz301 (2 : Complex) qz324) (@HSub.hSub Complex Complex Complex qz302 (@HMul.hMul Complex Complex Complex qz301 (2 : Complex) qz324) (1 : Complex)))

noncomputable abbrev qz325 := (@HPow.hPow Complex Int Complex qz435 qz431 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz85 := qz325

noncomputable def ep226 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz61 qz62 (@HSub.hSub Int Int Int qz63 qz64 (@HMul.hMul Int Int Int qz65 qz66 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz61 qz62 (@HSub.hSub Int Int Int qz63 qz64 (@HMul.hMul Int Int Int qz65 qz66 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84) qz85)) Bool.false 673047 2147483648 3 2147483648

noncomputable def ep227 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz61 qz62 (@HSub.hSub Int Int Int qz63 qz64 (@HMul.hMul Int Int Int qz65 qz66 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84) qz85) Bool.false 0 1 0 1 Bool.false

noncomputable def ep228 := @ep227 0 1 0 1 Bool.false 673047 2147483648 3 2147483648 Bool.true 3642754713 1073741824000 16237 1073741824000 Bool.false 673047 673047 2147483648 3 2147483648 Bool.true 3642754713 3642754713 1073741824000 16237

noncomputable def ep229 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz61 qz62 (@HSub.hSub Int Int Int qz63 qz64 (@HMul.hMul Int Int Int qz65 qz66 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false

noncomputable def ep230 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84) qz85 Bool.false 673047 2147483648 3 2147483648 Bool.true 3642754713 1073741824000 16237 1073741824000

noncomputable abbrev qz86 := (Complex.re qz325)

noncomputable abbrev qz87 := (Complex.im qz325)

noncomputable def ep231 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz86) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz87) 673047 2147483648 3 2147483648 0 1 0

noncomputable def ep232 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz86 1 12 0 1 2019141 536870912 9 536870912 673047

noncomputable def ep233 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz20) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz326 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz20 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz31)

noncomputable def ep234 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep233 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz326)

noncomputable def ep235 := @Enclosure.Complex.IsNear.re_isNear qz85 Bool.false 2019141 536870912 9 536870912 Bool.true 10928264139 268435456000 48711 268435456000

noncomputable abbrev qz436 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz327 := (@HPow.hPow Complex Nat Complex qz436 qz431 1)

noncomputable abbrev qz88 := (@Inv.inv Complex Complex.instInv qz327)

noncomputable def ep236 := @Enclosure.Complex.IsNear.of_eq qz85 qz88 Bool.false 2019141 536870912 9 536870912 Bool.true 10928264139 268435456000 48711

noncomputable def ep237 := @Enclosure.Complex.IsNear.of_parts qz88 Bool.false 2019141 536870912 9 536870912 Bool.true 10928264139 268435456000 48711

noncomputable abbrev qz89 := (Complex.re qz327)

noncomputable abbrev qz90 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz91 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz92 := qz327

noncomputable def ep238 := @Enclosure.Real.IsNear.mulLit_ff qz89 (@Inv.inv Real Real.instInv (@DFunLike.coe qz90 Complex (fun (x : Complex) => Real) qz91 Complex.normSq qz92)) 9000 4000 0 1 224349 134217728 1 134217728

noncomputable def ep239 := @Enclosure.Complex.IsNear.re_isNear qz92 Bool.false 9000 4000 0 1 Bool.false 97422 4000 0 1

noncomputable def ep240 := @Enclosure.Complex.IsNear.of_eq qz92 qz62 Bool.false 9000 4000 0 1 Bool.false 97422 4000 0

noncomputable def ep241 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz90 Complex (fun (x : Complex) => Real) qz91 Complex.normSq qz92)) Bool.false 224349 134217728 1 134217728 224349 134217728 1

noncomputable abbrev qz93 := (@instHAdd Real Real.instAdd)

noncomputable abbrev qz94 := (Complex.im qz327)

noncomputable def ep242 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz90 Complex (fun (x : Complex) => Real) qz91 Complex.normSq qz92) (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 qz89 qz89) (@HMul.hMul Real Real Real qz0 qz94 qz94)) Bool.false 2393011521 4000000 0 1

noncomputable def ep243 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz89 qz89) (@HMul.hMul Real Real Real qz0 qz94 qz94) 81 16 0 1 2372761521 4000000

noncomputable def ep244 := @Enclosure.Real.IsNear.mulLit_ff qz89 qz89 9000 4000 0 1 9000 4000 0 1

noncomputable def ep245 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz94 97422 4000 0 1 97422 4000 0 1

noncomputable def ep246 := @Enclosure.Complex.IsNear.im_isNear qz92 Bool.false 9000 4000 0 1 Bool.false 97422 4000 0 1

noncomputable abbrev qz95 := (ep239 (@ep240 1 (BSN.pow_one_c qz303) qz323))

noncomputable abbrev qz96 := (ep246 (@ep240 1 (BSN.pow_one_c qz303) qz323))

noncomputable def ep247 := @ep243 0 1 38288184336 2393011521 4000000 0 1 (@ep244 81 16 0 1 qz95 qz95 rfl) (@ep245 2372761521 4000000 0 1 qz96 qz96 rfl)

noncomputable def ep248 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz90 Complex (fun (x : Complex) => Real) qz91 Complex.normSq qz92) 2393011521 4000000 0 1 112174 112175 67108864 (ep242 (Enclosure.Complex.normSq_eq_mul_add_mul qz92) (ep247 rfl rfl)) rfl

noncomputable def ep249 := @Enclosure.Real.IsNear.of_eq (Complex.re qz88) (@HMul.hMul Real Real Real qz0 qz89 (@Inv.inv Real Real.instInv (@DFunLike.coe qz90 Complex (fun (x : Complex) => Real) qz91 Complex.normSq qz92))) Bool.false 2019141 536870912 9 536870912 (Enclosure.Complex.inv_re_eq_mul qz92) (@ep238 2019141 536870912 9 536870912 qz95 (@ep241 134217728 (ep248 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep250 := @Enclosure.Real.IsNear.of_eq (Complex.im qz88) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz94) (@Inv.inv Real Real.instInv (@DFunLike.coe qz90 Complex (fun (x : Complex) => Real) qz91 Complex.normSq qz92))) Bool.true 10928264139 268435456000 48711 268435456000 (Enclosure.Complex.inv_im_eq_mul qz92)

noncomputable def ep251 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz94) (@Inv.inv Real Real.instInv (@DFunLike.coe qz90 Complex (fun (x : Complex) => Real) qz91 Complex.normSq qz92)) 97422 4000 0 1 224349 134217728 1

noncomputable def ep252 := @ep251 134217728 10928264139 268435456000 48711 268435456000 (@Enclosure.Real.IsNear.neg qz94 Bool.false 97422 4000 0 1 qz96) (@ep241 134217728 (ep248 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep253 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz87 0 1 0 1 10928264139 268435456000 48711 268435456000 0

noncomputable def ep254 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep233 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz326)

noncomputable def ep255 := @Enclosure.Complex.IsNear.im_isNear qz85 Bool.false 2019141 536870912 9 536870912 Bool.true 10928264139 268435456000 48711 268435456000

noncomputable abbrev qz97 := (@ep236 268435456000 (BSN.zpow_one_sub_two_mul qz303 1 1 rfl rfl) (@ep237 268435456000 ep249 (ep250 ep252)))

noncomputable def ep256 := @ep231 1 673047 673047 2147483648 3 2147483648 (@ep232 2147483648 3 2147483648 ep234 (ep235 qz97) rfl) (@ep253 1 0 1 ep254 (ep255 qz97) rfl) rfl

noncomputable def ep257 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz87) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz86) 3642754713 1073741824000 16237 1073741824000 0 1 0

noncomputable def ep258 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz87 1 12 0 1 10928264139 268435456000 48711 268435456000 3642754713

noncomputable def ep259 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz86 0 1 0 1 2019141 536870912 9 536870912 0

noncomputable def ep260 := @ep257 1 3642754713 3642754713 1073741824000 16237 1073741824000 (@ep258 1073741824000 16237 1073741824000 ep234 (ep255 qz97) rfl) (@ep259 1 0 1 ep254 (ep235 qz97) rfl) rfl

noncomputable abbrev qz98 := (@Enclosure.Complex.IsNear.mk qz265 qz265 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz277 qz277)

noncomputable def ep261 := @ep228 1073741824000 (@ep229 0 1 0 1 (BSN.stirling_sum_base qz62) qz98) (ep230 (ep256 rfl) (ep260 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep262 := @ep182 1010489790623355647689 18014398509481984000 228208647224575071815407 ep169 (ep225 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep226 Bool.true 3642754713 1073741824000 16237 1073741824000 (BSN.stirling_sum_succ qz62 0 1 rfl) (ep261 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep263 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz24 2) Bool.false 28763952102376623 4503599627370496 500000000297711 33079000000000000000 Bool.false 866958115898787 281474976710656

noncomputable abbrev qz99 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz260 qz304 qz324))

noncomputable def ep264 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz24 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz24 1) qz99) Bool.false 28763952102376623 4503599627370496 500000000297711 33079000000000000000 Bool.false 866958115898787 281474976710656 1000000000033079 33079000000000000000

noncomputable def ep265 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz24 1) qz99 Bool.false 28758265565676719 9007199254740992 500000000297711 66158000000000000000 Bool.false 878502987990435 562949953421312 1000000000033079 66158000000000000000 Bool.false

noncomputable def ep266 := nat_lit 518165295879864617417767001260032

noncomputable def ep267 := nat_lit 976108061926901104265121497088

noncomputable abbrev qz100 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz260 qz304 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep268 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz24 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz24 0) qz100) Bool.false 28758265565676719 9007199254740992 500000000297711 66158000000000000000 Bool.false 878502987990435 562949953421312 1000000000033079 66158000000000000000

noncomputable def ep269 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz24 0) qz100 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz328 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz74))

noncomputable def ep270 := @Enclosure.Complex.IsNear.of_eq qz100 qz328 Bool.false 28758265565676719 9007199254740992 500000000297711 66158000000000000000 Bool.false 878502987990435 562949953421312 1000000000033079 66158000000000000000

noncomputable def ep271 := nat_lit 1466958442980583504609554002518593409847040

noncomputable def ep272 := nat_lit 2651287225544463318279372210134426585088

noncomputable def ep273 := nat_lit 8569515023181547192269354746649969408

noncomputable def ep274 := BSN.log_dyadic_bound 1300046084 17684046084 3 2 ep271 262144 66158 ep272 ep273 38612 18984092168 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1300046084) (BSN.artanhQ 17684046084) 0 2 ep272 ep271 ep273 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep275 := @Enclosure.Real.IsNear.mulLit_ff qz76 (Real.log (Enclosure.sfrac Bool.false 9492046084 16000000)) 1 2 0 1 28758265565676719 4503599627370496 500000000297711 33079000000000000000 28758265565676719 9007199254740992 500000000297711 66158000000000000000 qz318 (BSN.isNear_log_sfrac 9492046084 16000000 28758265565676719 4503599627370496 500000000297711 33079000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9492046084) qz319)) Bool.false 60310454147590062604288 9444732965739290427392 1000000000595422 66158000000000000000 28758265565676719 4503599627370496 500000000297711 33079000000000000000 (BSN.log_rat_reduce_isNear 9492046084 16000000 9 18984092168 16384000000 38612 262144 24973259072661432 36028797018963968 66158 1000000000000000 rfl rfl rfl rfl (ep274 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep276 := BSN.arctan_dyadic_bound_f 1000 97422 1 0 262144 66158 0 1 1 0 1 1 2690 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 97422) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 97422) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz329 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz330 := (@Nat.cast Real Real.instNatCast 97422)

noncomputable def ep277 := @Enclosure.Real.IsNear.subLit_ff_p qz77 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz329 qz330)) 884279719003555 562949953421312 1 2000000000000000 2690 262144 1 66158 230294287283764592640 878502987990435 562949953421312 1000000000033079 66158000000000000000 qz78 (ep276 rfl) rfl rfl

noncomputable abbrev qz101 := (@HAdd.hAdd Complex Complex Complex qz260 qz304 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz331 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz74)

noncomputable def ep278 := @ep269 28758265565676719 9007199254740992 500000000297711 66158000000000000000 Bool.false 878502987990435 562949953421312 1000000000033079 66158000000000000000 Bool.false 28758265565676719 28758265565676719 9007199254740992 500000000297711 66158000000000000000 Bool.false 878502987990435 878502987990435 562949953421312 1000000000033079 66158000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz24 0) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz24) qz98) (ep270 (@congrArg Complex Complex qz101 qz331 Complex.log (BSN.w_shift_mk qz24 Bool.false 48711 1000 0 qz25 rfl)) (@Enclosure.Complex.IsNear.of_parts qz328 Bool.false 28758265565676719 9007199254740992 500000000297711 66158000000000000000 Bool.false 878502987990435 562949953421312 1000000000033079 66158000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz328) (@HMul.hMul Real Real Real qz0 qz76 (Real.log (Enclosure.sfrac Bool.false 9492046084 16000000))) Bool.false 28758265565676719 9007199254740992 500000000297711 66158000000000000000 (Enclosure.clog_re_eq 1000 97422 4000 9492046084 16000000 rfl rfl rfl) (ep275 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz328) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz329)) Bool.false 878502987990435 562949953421312 1000000000033079 66158000000000000000 (Enclosure.clog_im_eq 1000 97422 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz329)) (@HSub.hSub Real Real Real qz52 qz77 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz329 qz330))) Bool.false 878502987990435 562949953421312 1000000000033079 66158000000000000000 (BSN.arctan_recip 97422 1000 rfl rfl) ep277)))) rfl rfl

noncomputable abbrev qz332 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz74))

noncomputable def ep279 := @Enclosure.Complex.IsNear.of_eq qz99 qz332 Bool.false 28769638639076527 9007199254740992 500000000297711 66158000000000000000 Bool.false 855413243807139 562949953421312 1000000000033079 66158000000000000000

noncomputable def ep280 := nat_lit 1474938232084818338025987315940407169847040

noncomputable def ep281 := nat_lit 2757857725308692658575653032435098585088

noncomputable def ep282 := nat_lit 9220058135252367270848583109401969408

noncomputable def ep283 := BSN.log_dyadic_bound 1324046084 17708046084 3 2 ep280 262144 66158 ep281 ep282 39274 19032092168 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1324046084) (BSN.artanhQ 17708046084) 0 2 ep281 ep280 ep282 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep284 := @Enclosure.Real.IsNear.mulLit_ff qz76 (Real.log (Enclosure.sfrac Bool.false 9516046084 16000000)) 1 2 0 1 28769638639076527 4503599627370496 500000000297711 33079000000000000000 28769638639076527 9007199254740992 500000000297711 66158000000000000000 qz318 (BSN.isNear_log_sfrac 9516046084 16000000 28769638639076527 4503599627370496 500000000297711 33079000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9516046084) qz319)) Bool.false 60334305211216616751104 9444732965739290427392 1000000000595422 66158000000000000000 28769638639076527 4503599627370496 500000000297711 33079000000000000000 (BSN.log_rat_reduce_isNear 9516046084 16000000 9 19032092168 16384000000 39274 262144 24973259072661432 36028797018963968 66158 1000000000000000 rfl rfl rfl rfl (ep283 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep285 := BSN.arctan_dyadic_bound_f 5000 97422 1 0 262144 66158 0 1 1 0 1 1 13442 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 97422) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 97422) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz333 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep286 := @Enclosure.Real.IsNear.subLit_ff_p qz77 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz333 qz330)) 884279719003555 562949953421312 1 2000000000000000 13442 262144 1 66158 224241449384578646016 855413243807139 562949953421312 1000000000033079 66158000000000000000 qz78 (ep285 rfl) rfl rfl

noncomputable abbrev qz102 := (@HAdd.hAdd Complex Complex Complex qz260 qz304 qz324)

noncomputable abbrev qz334 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz74)

noncomputable def ep287 := @ep265 28769638639076527 9007199254740992 500000000297711 66158000000000000000 Bool.false 855413243807139 562949953421312 1000000000033079 66158000000000000000 Bool.false ep266 28763952102376623 4503599627370496 500000000297711 33079000000000000000 Bool.false ep267 866958115898787 281474976710656 1000000000033079 33079000000000000000 (ep268 (BSN.log_sum_c_succ qz24 0 1 rfl) (ep278 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep279 (@congrArg Complex Complex qz102 qz334 Complex.log (BSN.w_shift_mk qz24 Bool.false 48711 1000 1 qz25 rfl)) (@Enclosure.Complex.IsNear.of_parts qz332 Bool.false 28769638639076527 9007199254740992 500000000297711 66158000000000000000 Bool.false 855413243807139 562949953421312 1000000000033079 66158000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz332) (@HMul.hMul Real Real Real qz0 qz76 (Real.log (Enclosure.sfrac Bool.false 9516046084 16000000))) Bool.false 28769638639076527 9007199254740992 500000000297711 66158000000000000000 (Enclosure.clog_re_eq 5000 97422 4000 9516046084 16000000 rfl rfl rfl) (ep284 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz332) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz333)) Bool.false 855413243807139 562949953421312 1000000000033079 66158000000000000000 (Enclosure.clog_im_eq 5000 97422 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz333)) (@HSub.hSub Real Real Real qz52 qz77 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz333 qz330))) Bool.false 855413243807139 562949953421312 1000000000033079 66158000000000000000 (BSN.arctan_recip 97422 5000 rfl rfl) ep286)))) rfl rfl

noncomputable def ep288 := @ep175 ep169 Bool.false 28763952102376623 4503599627370496 500000000297711 33079000000000000000 Bool.false 866958115898787 281474976710656 1000000000033079 33079000000000000000 Bool.true ep176 171753063415298421319 4503599627370496000 110541662816985355062237 ep173 Bool.false ep177 955004471205833279689 18014398509481984000 260976647225659004487407 ep169 (@ep178 4503599627370496000 106445662814546506550237 ep173 Bool.false 1010489790623355647689 18014398509481984000 228208647224575071815407 ep169 (BSN.logGammaStirling_unfold 1 qz62) (ep262 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep263 1000000000033079 33079000000000000000 (BSN.log_sum_c_eq qz24 2) (ep264 (BSN.log_sum_c_succ qz24 1 2 rfl) (ep287 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz103 := (@HDiv.hDiv Real Real Real qz257 qz267 (2 : Real))

noncomputable def ep289 := @Enclosure.Real.IsNear.mulLit_ff qz103 (Real.log Real.pi) 48711 2000 0 1 75021 65536 1 65536 3654347931 131072000 48711 131072000 (@Enclosure.Real.IsNear.of_eq qz103 (Enclosure.sfrac Bool.false 48711 2000) Bool.false 48711 2000 0 1 (BSN.t_half_eq qz24 Bool.false 48711 1000 qz25) (Enclosure.Real.IsNear.const Bool.false 48711 2000)) EMRow10.d5 rfl

noncomputable def ep290 := @ep171 48711 131072000 ep172 452754715946624813257 18014398509481984000 663804439475659004487407 ep169 (@ep174 260976647225659004487407 ep169 (ep288 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep289 rfl rfl

noncomputable def ep291 := BSN.cos_dyadic_bound_f 103799 536870912 1 0 262144 66223 0 1 1 0 1 1 262143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 103799) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 103799) qz275 0 0 rfl) rfl rfl

noncomputable def ep292 := @ep168 262144 Bool.false 262143 262144 1 33079 (@ep170 205889 8192 161 262144 ep290 rfl) (Enclosure.sfrac_false_div 205889 8192) (BSN.cos_reduce0 qz305 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 228257465995624448) (@Nat.cast Real Real.instNatCast 1180591620717411303424)) 226375608064910080 72057594037927936 Bool.false 262143 262144 4 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 205889 8192 226375608064910080 72057594037927936 4 228257465995624448 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 262143 262144 228257465995624448 1180591620717411303424 103799 536870912 66223 66158 (ep291 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep293 := nat_lit 9784326600697168527360000

noncomputable def ep294 := nat_lit 20030280768168054312020927

noncomputable def ep295 := nat_lit 3371413954421475392880640000

noncomputable abbrev qz104 := qz261

noncomputable abbrev qz105 := qz262

noncomputable abbrev qz437 := (@Nat.cast Complex Complex.instNatCast 10)

noncomputable abbrev qz335 := (@HPow.hPow Complex Complex Complex qz424 qz437 qz425)

noncomputable abbrev qz106 := qz335

noncomputable abbrev qz336 := qz437

noncomputable abbrev qz107 := (@HAdd.hAdd Complex Complex Complex qz260 (@HDiv.hDiv Complex Complex Complex qz309 qz336 (@HSub.hSub Complex Complex Complex qz302 qz259 (1 : Complex))) qz308)

noncomputable abbrev qz108 := (@instHSub Nat instSubNat)

noncomputable abbrev qz337 := qz436

noncomputable abbrev qz109 := qz337

noncomputable abbrev qz110 := qz336

noncomputable def ep296 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz21 1 10) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 10, @HPow.hPow Complex Complex Complex qz104 (@Nat.cast Complex Complex.instNatCast n) qz105) (@HMul.hMul Complex Complex Complex qz51 qz106 (@HAdd.hAdd Complex Complex Complex qz5 qz107 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))))) Bool.false 910072066463757413664287 ep164 ep165

noncomputable def ep297 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 10, @HPow.hPow Complex Complex Complex qz104 (@Nat.cast Complex Complex.instNatCast n) qz105) (@HMul.hMul Complex Complex Complex qz51 qz106 (@HAdd.hAdd Complex Complex Complex qz5 qz107 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))))) Bool.false 48180620971 68719476736 12758806408943 2273171570950144

noncomputable def ep298 := nat_lit 36306592896776349979439717

noncomputable def ep299 := nat_lit 1619137052428080022185367

noncomputable def ep300 := nat_lit 62539676199439623375450499010527232

noncomputable def ep301 := nat_lit 15228563061116986174498267014889472

noncomputable def ep302 := @ep297 Bool.true 4399395847 17179869184 3184961340187 568292892737536 Bool.false 52573301565378361981787 ep164 ep298 ep166 Bool.false ep299 ep293 1135405882659676075953427 ep295 Bool.false ep300 910072066463757413664287 ep164 ep165 ep166 Bool.true ep301 886419034860852766694633 ep293

noncomputable def ep303 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 10, @HPow.hPow Complex Complex Complex qz104 (@Nat.cast Complex Complex.instNatCast n) qz105) (BSN.headSumC qz21 10) Bool.false 48180620971 68719476736 12758806408943 2273171570950144 Bool.true 4399395847 17179869184 3184961340187

noncomputable abbrev qz111 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 9) qz262)

noncomputable def ep304 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz21 10) (@HAdd.hAdd Complex Complex Complex qz5 qz4 qz111) Bool.false 48180620971 68719476736 12758806408943 2273171570950144 Bool.true 4399395847 17179869184 3184961340187 568292892737536

noncomputable def ep305 := @Enclosure.Complex.IsNear.addLitP qz4 qz111 Bool.false 12900430697 34359738368 5804400297903 1136585785475072 Bool.true 12714296203 68719476736 11596463021939 2273171570950144 Bool.false

noncomputable abbrev qz338 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz112 := (@Inv.inv Real Real.instInv (Real.sqrt qz338))

noncomputable abbrev qz113 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep306 := @Enclosure.Complex.IsNear.of_eq qz111 (Complex.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz113)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz113)))) Bool.false 22379759577 68719476736 1150005813137 2273171570950144 Bool.true 4883287185 68719476736 1143382338809 2273171570950144 (BSN.cpow_neg_s_mk qz24 48711 1000 9 qz25 rfl)

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9) qz26)

noncomputable def ep307 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz338) 786433 262144 1 262144 43690 43691 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz338) (Real.sqrt qz339) Bool.false 786433 262144 1 262144 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 786433 262144 1 262144 786433 262144 1 262144 (BSN.sqrt_enclosure 9 1 393216 393217 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep308 := BSN.log_dyadic_bound 1 17 2 1 867 131072 33079 1 1 15438 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz114 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep309 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz114 48711 1000 0 1 9895417793173221 4503599627370496 1000000000099237 33079000000000000000 482015696123260768131 4503599627370496000 48711000004833933507 33079000000000000000000 qz29 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000099237 33079000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false 10376097607894403383296 4722366482869645213696 1000000000099237 33079000000000000000 9895417793173221 4503599627370496 1000000000099237 33079000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 15438 131072 24973259072661432 36028797018963968 33079 1000000000000000 rfl rfl rfl rfl (ep308 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep310 := nat_lit 176966194941088074086847652882801

noncomputable def ep311 := BSN.cos_dyadic_bound_f 115338043 536870912 2 1 262144 66223 ep310 ep61 ep310 ep310 ep62 ep310 256117 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 115338043) qz274 0 1 ep310 ep61 ep310 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 115338043) qz275 0 1 ep310 ep62 ep310 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz115 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14028503) qz115)

noncomputable abbrev qz341 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep312 := @Enclosure.Real.IsNear.cos_image qz113 qz340 Bool.false 14028503 131072 387 262144 Bool.false 256117 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 482015696123260768131 4503599627370496000 48711000004833933507 33079000000000000000000 14028503 131072 387 262144 (ep309 rfl) rfl) (Enclosure.sfrac_false_div 14028503 131072) (BSN.cos_reduce0 qz340 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4058096648403535527936) qz341) 226375608064910080 72057594037927936 Bool.false 256117 262144 17 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 14028503 131072 226375608064910080 72057594037927936 17 4058096648403535527936 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 256117 262144 4058096648403535527936 18889465931478580854784 115338043 536870912 66223 66158 (ep311 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep313 := BSN.sin_dyadic_bound_f 115338043 536870912 2 1 262144 66223 ep310 ep57 ep310 ep310 ep58 ep310 55885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 115338043) qz269 0 1 ep310 ep57 ep310 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 115338043) qz270 0 1 ep310 ep58 ep310 rfl rfl rfl rfl) rfl rfl

noncomputable def ep314 := @Enclosure.Real.IsNear.sin_image qz113 qz340 Bool.false 14028503 131072 387 262144 Bool.false 55885 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 482015696123260768131 4503599627370496000 48711000004833933507 33079000000000000000000 14028503 131072 387 262144 (ep309 rfl) rfl) (Enclosure.sfrac_false_div 14028503 131072) (BSN.sin_reduce0 qz340 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4058096648403535527936) qz341) 226375608064910080 72057594037927936 Bool.false 55885 262144 17 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 14028503 131072 226375608064910080 72057594037927936 17 4058096648403535527936 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 55885 262144 4058096648403535527936 18889465931478580854784 115338043 536870912 66223 66158 (ep313 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz342 := (@Enclosure.Real.IsNear.recentre' qz112 Bool.false 87381 262144 1 262144 87381 262144 1 262144 (ep307 rfl rfl) rfl)

noncomputable def ep315 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz113)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz113))) Bool.false 22379759577 68719476736 1150005813137 2273171570950144 Bool.true 4883287185 68719476736 1143382338809 2273171570950144 (@Enclosure.Real.IsNear.mulLit_ff qz112 (Real.cos qz113) 87381 262144 1 262144 256117 262144 13063717 8671461376 22379759577 68719476736 1150005813137 2273171570950144 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz113) Bool.false 256117 262144 13063717 8671461376 256117 262144 13063717 8671461376 (ep312 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz112 (@Neg.neg Real Real.instNeg (Real.sin qz113)) 87381 262144 1 262144 55885 262144 13063717 8671461376 4883287185 68719476736 1143382338809 2273171570950144 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz113) Bool.false 55885 262144 13063717 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz113) Bool.false 55885 262144 13063717 8671461376 55885 262144 13063717 8671461376 (ep314 rfl rfl) rfl)) rfl)

noncomputable def ep316 := @ep305 22379759577 68719476736 1150005813137 2273171570950144 Bool.true 4883287185 68719476736 1143382338809 2273171570950144 Bool.false 1655473530971334115328 48180620971 68719476736 12758806408943 2273171570950144 Bool.true 1209296722241486061568 4399395847 17179869184 3184961340187 568292892737536 EMRow10.d6 (ep306 ep315) rfl rfl

noncomputable def ep317 := @Enclosure.Complex.IsNear.mul qz106 (@HAdd.hAdd Complex Complex Complex qz5 qz107 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))) Bool.false 52573301565378361981787 ep164 ep298 ep166 Bool.false

noncomputable abbrev qz116 := (Complex.re qz335)

noncomputable abbrev qz117 := (Complex.im qz335)

noncomputable def ep318 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz116 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz107 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz117 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz107 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))))) 1841280780095070054137 19568653201394337054720 12963493777815019887751

noncomputable def ep319 := nat_lit 53942623270743606286090240

noncomputable def ep320 := nat_lit 10379605341146310203937717

noncomputable def ep321 := nat_lit 685859137323474129911487033357668605241589760

noncomputable def ep322 := @Enclosure.Real.IsNear.mulLit_ff qz116 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz107 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))))) 6439521857 34359738368 136011903933 284146446368768 285934394041

noncomputable abbrev qz343 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz118 := (@Inv.inv Real Real.instInv (Real.sqrt qz343))

noncomputable abbrev qz344 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz428 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz119 := (Real.cos qz344)

noncomputable abbrev qz120 := (@Neg.neg Real Real.instNeg (Real.sin qz344))

noncomputable def ep323 := @Enclosure.Complex.IsNear.of_eq qz106 (Complex.mk (@HMul.hMul Real Real Real qz0 qz118 qz119) (@HMul.hMul Real Real Real qz0 qz118 qz120)) Bool.false 6439521857 34359738368 136011903933 284146446368768 Bool.false 2187900521 8589934592 544970222121 1136585785475072 (BSN.cpow_neg_s_mk qz24 48711 1000 10 qz25 rfl)

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10) qz26)

noncomputable def ep324 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz343) 828973 262144 1 262144 41448 41449 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz343) (Real.sqrt qz345) Bool.false 828973 262144 1 262144 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz345) Bool.false 828973 262144 1 262144 828973 262144 1 262144 (BSN.sqrt_enclosure 10 1 414486 414487 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep325 := BSN.log_dyadic_bound 2 18 3 2 1574640 131072 33079 6528 48 29247 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz346 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz121 := qz346

noncomputable abbrev qz347 := (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10) qz26))

noncomputable def ep326 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz121 48711 1000 0 1 10369891420296933 4503599627370496 1000000000099237 33079000000000000000 505127780974083903363 4503599627370496000 48711000004833933507 33079000000000000000000 qz29 (BSN.isNear_log_sfrac 10 1 10369891420296933 4503599627370496 1000000000099237 33079000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz347 Bool.false 10873619265929276817408 4722366482869645213696 1000000000099237 33079000000000000000 10369891420296933 4503599627370496 1000000000099237 33079000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 29247 131072 24973259072661432 36028797018963968 33079 1000000000000000 rfl rfl rfl rfl (ep325 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep327 := nat_lit 13452862800681045674522527781775376

noncomputable def ep328 := BSN.sin_dyadic_bound_f 340567874 536870912 2 1 262144 66223 ep327 ep57 ep327 ep327 ep58 ep327 155362 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 340567874) qz269 0 1 ep327 ep57 ep327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 340567874) qz270 0 1 ep327 ep58 ep327 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz122 := qz344

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14701153) qz115)

noncomputable def ep329 := @Enclosure.Real.IsNear.cos_image qz122 qz348 Bool.false 14701153 131072 387 262144 Bool.false 155362 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 505127780974083903363 4503599627370496000 48711000004833933507 33079000000000000000000 14701153 131072 387 262144 (ep326 rfl) rfl) (Enclosure.sfrac_false_div 14701153 131072) (BSN.cos_reduce3 qz348 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11982666806776305811456) qz341) 226375608064910080 72057594037927936 Bool.false 155362 262144 17 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q3 14701153 131072 226375608064910080 72057594037927936 17 11982666806776305811456 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 155362 262144 11982666806776305811456 18889465931478580854784 340567874 536870912 66223 66158 (ep328 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep330 := BSN.cos_dyadic_bound_f 340567874 536870912 2 1 262144 66223 ep327 ep61 ep327 ep327 ep62 ep327 211144 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 340567874) qz274 0 1 ep327 ep61 ep327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 340567874) qz275 0 1 ep327 ep62 ep327 rfl rfl rfl rfl) rfl rfl

noncomputable def ep331 := @Enclosure.Real.IsNear.sin_image qz122 qz348 Bool.false 14701153 131072 387 262144 Bool.true 211144 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 505127780974083903363 4503599627370496000 48711000004833933507 33079000000000000000000 14701153 131072 387 262144 (ep326 rfl) rfl) (Enclosure.sfrac_false_div 14701153 131072) (BSN.sin_reduce3 qz348 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11982666806776305811456) qz341) 226375608064910080 72057594037927936 Bool.false 211144 262144 17 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q3 14701153 131072 226375608064910080 72057594037927936 17 11982666806776305811456 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 211144 262144 11982666806776305811456 18889465931478580854784 340567874 536870912 66223 66158 (ep330 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz123 := (Real.sin qz344)

noncomputable abbrev qz349 := (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 82897 262144 1 262144 82897 262144 1 262144 (ep324 rfl rfl) rfl)

noncomputable def ep332 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz118 qz119) (@HMul.hMul Real Real Real qz0 qz118 qz120) Bool.false 6439521857 34359738368 136011903933 284146446368768 Bool.false 2187900521 8589934592 544970222121 1136585785475072 (@Enclosure.Real.IsNear.mulLit_ff qz118 qz119 82897 262144 1 262144 77681 131072 13063717 8671461376 6439521857 34359738368 136011903933 284146446368768 qz349 (@Enclosure.Real.IsNear.recentre' qz119 Bool.false 155362 262144 13063717 8671461376 77681 131072 13063717 8671461376 (ep329 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz118 qz120 82897 262144 1 262144 26393 32768 13063717 8671461376 2187900521 8589934592 544970222121 1136585785475072 qz349 (@Enclosure.Real.IsNear.neg qz123 Bool.true 26393 32768 13063717 8671461376 (@Enclosure.Real.IsNear.recentre' qz123 Bool.true 211144 262144 13063717 8671461376 26393 32768 13063717 8671461376 (ep331 rfl rfl) rfl)) rfl)

noncomputable def ep333 := @ep322 569522765040 0 1 1841280780095070054137 19568653201394337054720 12963493777815019887751 ep319 (@Enclosure.Complex.IsNear.re_isNear qz106 Bool.false 6439521857 34359738368 136011903933 284146446368768 Bool.false 2187900521 8589934592 544970222121 1136585785475072 (ep323 ep332))

noncomputable def ep334 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz107 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))) Bool.false 285934394041 569522765040 0 1 Bool.false

noncomputable def ep335 := @Enclosure.Complex.IsNear.addLitP qz107 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) Bool.false 2363011521 4746023042 0 1 Bool.true 487110000

noncomputable def ep336 := @ep335 2373011521 0 1 Bool.false 1 240 0 1 Bool.false 16237 40000 0 1 Bool.false 571868788082 285934394041 569522765040 0 1 Bool.false 19046188066477 19046188066477 94920460840000 0 1

noncomputable abbrev qz124 := (@HDiv.hDiv Complex Complex Complex qz309 qz336 (@HSub.hSub Complex Complex Complex qz302 qz259 (1 : Complex)))

noncomputable def ep337 := @Enclosure.Complex.IsNear.addLitP qz124 qz81 Bool.true 20000000 9492046084 0 1 Bool.true 1948440000 9492046084 0 1

noncomputable def ep338 := @Enclosure.Complex.IsNear.of_eq qz124 (Complex.mk (Enclosure.sfrac Bool.true 20000000 9492046084) (Enclosure.sfrac Bool.true 1948440000 9492046084)) Bool.true 20000000 9492046084 0 1 Bool.true 1948440000 9492046084 0 1

noncomputable def ep339 := @ep337 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 9452046084 2363011521 4746023042 0 1 Bool.true 1948440000 487110000 2373011521 0 1 (ep338 (BSN.N_div_s_sub_one_mk qz24 48711 1000 10 qz25 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 20000000 9492046084) (Enclosure.sfrac Bool.true 1948440000 9492046084) Bool.true 20000000 9492046084 0 1 Bool.true 1948440000 9492046084 0 1 (Enclosure.Real.IsNear.const Bool.true 20000000 9492046084) (Enclosure.Real.IsNear.const Bool.true 1948440000 9492046084))) qz82 rfl

noncomputable abbrev qz125 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz350 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz436 qz437 1))

noncomputable abbrev qz126 := qz350

noncomputable def ep340 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz126)) Bool.false 1 240 0 1

noncomputable def ep341 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz126) Bool.false 0 1 0 1 Bool.false

noncomputable def ep342 := @ep341 0 1 0 1 Bool.false 1 240 0 1 Bool.false 16237 40000 0 1 Bool.false 1 1 240 0 1 Bool.false 16237 16237 40000 0

noncomputable def ep343 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false

noncomputable def ep344 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz126 Bool.false 1 240 0 1 Bool.false 16237 40000 0 1

noncomputable abbrev qz127 := (Complex.re qz350)

noncomputable abbrev qz128 := (Complex.im qz350)

noncomputable def ep345 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz128) 1 240 0 1 0 1 0

noncomputable def ep346 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127 1 24 0 1 1 10 0 1 1

noncomputable def ep347 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep348 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep349 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz20) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow10.d7 rfl) qz326

noncomputable def ep350 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) qz21 Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 (BSN.ascPochhammer_one_eval qz21)

noncomputable def ep351 := ep350 (@Enclosure.Complex.IsNear.of_eq qz21 (Complex.mk qz76 qz24) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 (BSN.s_crit_mk qz24 Bool.false 48711 1000 qz25) (@Enclosure.Complex.IsNear.mk qz76 qz24 Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 qz318 qz29))

noncomputable def ep352 := @ep348 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep351)

noncomputable def ep353 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 48711 1000 0 1 0 1 0

noncomputable def ep354 := @ep353 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep351)

noncomputable def ep355 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) 16237 4000 0 1 0 1 0 1 16237

noncomputable def ep356 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 48711 1000 0 1 16237 4000 0

noncomputable def ep357 := @ep356 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep351)

noncomputable def ep358 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep359 := @ep358 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep351)

noncomputable def ep360 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 16237 4000 0 1 (@ep347 1 24 0 1 (ep352 rfl) (ep354 rfl) rfl rfl) (@ep355 16237 4000 0 1 (ep357 rfl) (ep359 rfl) rfl rfl)

noncomputable def ep361 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 16237 4000 0 1 ep360

noncomputable abbrev qz129 := (@Enclosure.Complex.IsNear.of_eq qz350 (Complex.mk (Enclosure.sfrac Bool.false 1 10) qz265) Bool.false 1 10 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 10 1 10 EMRow10.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 10) qz265 Bool.false 1 10 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 10) qz277))

noncomputable def ep362 := @ep346 240 0 1 ep361 (@Enclosure.Complex.IsNear.re_isNear qz126 Bool.false 1 10 0 1 Bool.false 0 1 0 1 qz129)

noncomputable def ep363 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz128 16237 4000 0 1 0 1 0 1 0

noncomputable def ep364 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 16237 4000 0 1 ep360

noncomputable def ep365 := @ep363 1 0 1 ep364 (@Enclosure.Complex.IsNear.im_isNear qz126 Bool.false 1 10 0 1 Bool.false 0 1 0 1 qz129)

noncomputable def ep366 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz128) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127) 0 1 0 1 16237 40000 0

noncomputable def ep367 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz128 1 24 0 1 0 1 0 1 0

noncomputable def ep368 := @ep367 1 0 1 ep361 (@Enclosure.Complex.IsNear.im_isNear qz126 Bool.false 1 10 0 1 Bool.false 0 1 0 1 qz129)

noncomputable def ep369 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127 16237 4000 0 1 1 10 0 1 16237

noncomputable def ep370 := @ep369 40000 0 1 ep364 (@Enclosure.Complex.IsNear.re_isNear qz126 Bool.false 1 10 0 1 Bool.false 0 1 0 1 qz129)

noncomputable def ep371 := @ep342 1 (@ep343 0 1 0 1 (BSN.bern_sum_base qz21 10) qz98) (ep344 (@ep345 1 1 1 240 0 1 (ep362 rfl) (ep365 rfl) rfl rfl) (@ep366 1 16237 16237 40000 0 1 (ep368 rfl) (ep370 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep372 := ep336 (ep339 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep340 Bool.false 16237 40000 0 1 (BSN.bern_sum_succ qz21 10 0 1 1 rfl rfl) (ep371 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep373 := @Enclosure.Real.IsNear.mulLit_ff qz117 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz107 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))))) 2187900521 8589934592 544970222121 1136585785475072 19046188066477

noncomputable def ep374 := @ep373 94920460840000 0 1 41671164793709010934517 815360550058097377280000 ep320 ep166 (@Enclosure.Complex.IsNear.im_isNear qz106 Bool.false 6439521857 34359738368 136011903933 284146446368768 Bool.false 2187900521 8589934592 544970222121 1136585785475072 (ep323 ep332))

noncomputable def ep375 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz107 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))) Bool.false 285934394041 569522765040 0 1 Bool.false

noncomputable def ep376 := nat_lit 3261442200232389509120000

noncomputable def ep377 := nat_lit 2590508301587520741754041

noncomputable def ep378 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz116 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz107 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz117 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz107 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))))) 122648344346611210487789 ep376 ep377

noncomputable def ep379 := nat_lit 26971311635371803143045120000

noncomputable def ep380 := nat_lit 215770493082974425144360960

noncomputable def ep381 := nat_lit 2640360955374411557072028688373568073388523520

noncomputable def ep382 := @Enclosure.Real.IsNear.mulLit_ff qz116 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz107 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))))) 6439521857 34359738368 136011903933 284146446368768 19046188066477

noncomputable def ep383 := @ep382 94920460840000 0 1 122648344346611210487789 ep376 ep377 ep379 (@Enclosure.Complex.IsNear.re_isNear qz106 Bool.false 6439521857 34359738368 136011903933 284146446368768 Bool.false 2187900521 8589934592 544970222121 1136585785475072 (ep323 ep332))

noncomputable def ep384 := @Enclosure.Real.IsNear.mulLit_ff qz117 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz107 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz110 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))))) 2187900521 8589934592 544970222121 1136585785475072 285934394041

noncomputable def ep385 := @ep384 569522765040 0 1 625596009694123195361 4892163300348584263680 51941910077519102926987 ep380 (@Enclosure.Complex.IsNear.im_isNear qz106 Bool.false 6439521857 34359738368 136011903933 284146446368768 Bool.false 2187900521 8589934592 544970222121 1136585785475072 (ep323 ep332))

noncomputable abbrev qz351 := (ep372 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep386 := @ep317 ep299 ep293 1135405882659676075953427 ep295 (@ep318 ep319 41671164793709010934517 815360550058097377280000 ep320 ep166 ep321 52573301565378361981787 ep164 ep298 ep166 (ep333 (@ep334 19046188066477 94920460840000 0 1 qz351) rfl) (ep374 (@ep375 19046188066477 94920460840000 0 1 qz351) rfl) rfl rfl) (@ep378 ep379 625596009694123195361 4892163300348584263680 51941910077519102926987 ep380 ep381 ep299 ep293 1135405882659676075953427 ep295 (ep383 (@ep375 19046188066477 94920460840000 0 1 qz351) rfl) (ep385 (@ep334 19046188066477 94920460840000 0 1 qz351) rfl) rfl rfl)

noncomputable def ep387 := @ep302 ep294 ep295 (@ep303 568292892737536 (BSN.head_sum_c_eq qz21 10) (ep304 (BSN.head_sum_c_succ qz21 9 10 rfl rfl) (ep316 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep386 rfl rfl rfl

noncomputable def ep388 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz21 1 10) Bool.false 910072066463757413664287 ep164 ep165 ep166 Bool.true 886419034860852766694633 ep293 ep294 ep295 (@ep296 ep166 Bool.true 886419034860852766694633 ep293 ep294 ep295 (BSN.zetaApproximant_eq_folded' qz21 1 10 rfl) (ep387 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep389 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) (Complex.im (zetaApproximant qz21 1 10)) 25 131072 5587863

noncomputable def ep390 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56)) Bool.false 50 262144 5587863

noncomputable def ep391 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56) qz305 Bool.false 205889 8192 161

noncomputable def ep392 := BSN.sin_dyadic_bound_f 103799 536870912 1 0 262144 66223 0 1 1 0 1 1 50 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 103799) qz269 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 103799) qz270 0 0 rfl) rfl rfl

noncomputable def ep393 := @ep391 262144 Bool.false 50 262144 1 33079 (@ep170 205889 8192 161 262144 ep290 rfl) (Enclosure.sfrac_false_div 205889 8192) (BSN.sin_reduce0 qz305 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 228257465995624448) (@Nat.cast Real Real.instNatCast 1180591620717411303424)) 226375608064910080 72057594037927936 Bool.false 50 262144 4 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 205889 8192 226375608064910080 72057594037927936 4 228257465995624448 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 50 262144 228257465995624448 1180591620717411303424 103799 536870912 66223 66158 (ep392 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep394 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz21 1 10) Bool.false 910072066463757413664287 ep164 ep165 ep166 Bool.true 886419034860852766694633 ep293 ep294 ep295 (@ep296 ep166 Bool.true 886419034860852766694633 ep293 ep294 ep295 (BSN.zetaApproximant_eq_folded' qz21 1 10 rfl) (ep387 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow10.d9 : Enclosure.Real.IsNear (hardyZApproximantEM 1 10 qz24) Bool.false ep149 ep150 ep151 ep152 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 10 qz24) ep153 Bool.false ep149 ep150 ep151 ep152 (@Eq.refl Real ep153) (@ep154 Bool.false ep149 ep150 ep151 ep152 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz54 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz55 (@Nat.cast Complex Complex.instNatCast j))))) qz56) (zetaApproximant qz21 1 10)) (@ep156 ep157 ep158 ep159 886419034860852766694633 ep160 ep161 ep152 ep162 ep149 ep150 ep151 ep152 (@ep163 8671461376 910072066463757413664287 ep164 ep165 ep166 ep155 ep157 ep158 ep159 (@ep167 8671461376 262143 262144 5587863 8671461376 (ep292 rfl rfl) rfl) ep388 rfl) (@ep389 8671461376 886419034860852766694633 ep293 ep294 ep295 886419034860852766694633 ep160 ep161 ep152 (@ep390 8671461376 25 131072 5587863 8671461376 (ep393 rfl rfl) rfl) ep394 rfl) rfl rfl))

noncomputable abbrev qz453 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 51734 1000)))

noncomputable abbrev qz438 := qz453

noncomputable abbrev qz352 := qz438

noncomputable abbrev qz130 := (BSN.headSumC qz352 9)

noncomputable abbrev qz131 := qz352

noncomputable abbrev qz439 := (@Neg.neg Complex Complex.instNeg qz453)

noncomputable abbrev qz353 := qz439

noncomputable abbrev qz132 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 8) qz353)

noncomputable def ep395 := @Enclosure.Complex.IsNear.of_eq qz130 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz131 8) qz132) Bool.false 107809588557 68719476736 12289412962325 2273171570950144 Bool.true 632483307 8589934592 3077585685071 568292892737536

noncomputable def ep396 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz131 8) qz132 Bool.false 90260715267 68719476736 10992507272523 2273171570950144 Bool.false 2935706013 17179869184 2753492422135 568292892737536 Bool.false

noncomputable abbrev qz133 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 7) qz353)

noncomputable def ep397 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz131 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz131 7) qz133) Bool.false 90260715267 68719476736 10992507272523 2273171570950144 Bool.false 2935706013 17179869184 2753492422135 568292892737536

noncomputable def ep398 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz131 7) qz133 Bool.false 64535522589 68719476736 9610878695855 2273171570950144 Bool.false 957824793 4294967296 4819866836475 1136585785475072 Bool.false

noncomputable abbrev qz134 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 6) qz353)

noncomputable def ep399 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz131 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz131 6) qz134) Bool.false 64535522589 68719476736 9610878695855 2273171570950144 Bool.false 957824793 4294967296 4819866836475 1136585785475072

noncomputable def ep400 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz131 6) qz134 Bool.false 64034776009 68719476736 8127499684087 2273171570950144 Bool.true 1590619919 8589934592 2034831017587 568292892737536 Bool.false

noncomputable abbrev qz135 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 5) qz353)

noncomputable def ep401 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz131 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz131 5) qz135) Bool.false 64034776009 68719476736 8127499684087 2273171570950144 Bool.true 1590619919 8589934592 2034831017587 568292892737536

noncomputable def ep402 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz131 5) qz135 Bool.false 64352951799 68719476736 6502798790013 2273171570950144 Bool.false 18005733963 68719476736 6506041987489 2273171570950144 Bool.true

noncomputable abbrev qz136 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 4) qz353)

noncomputable def ep403 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz131 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz131 4) qz136) Bool.false 64352951799 68719476736 6502798790013 2273171570950144 Bool.false 18005733963 68719476736 6506041987489 2273171570950144

noncomputable def ep404 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz131 4) qz136 Bool.false 93854412479 68719476736 4679008317557 2273171570950144 Bool.false 1113091371 2147483648 1171312953353 568292892737536 Bool.true

noncomputable abbrev qz137 := (@HPow.hPow Complex Complex Complex qz261 qz263 qz353)

noncomputable def ep405 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz131 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz131 3) qz137) Bool.false 93854412479 68719476736 4679008317557 2273171570950144 Bool.false 1113091371 2147483648 1171312953353 568292892737536

noncomputable def ep406 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz131 3) qz137 Bool.false 6974997083 8589934592 1286670685821 1136585785475072 Bool.false 2927685357 4294967296 1292724473611 1136585785475072 Bool.false

noncomputable abbrev qz138 := (@HPow.hPow Complex Complex Complex qz261 qz264 qz353)

noncomputable def ep407 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz131 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz131 2) qz138) Bool.false 6974997083 8589934592 1286670685821 1136585785475072 Bool.false 2927685357 4294967296 1292724473611 1136585785475072

noncomputable def ep408 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz131 2) qz138 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep409 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz131 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz20) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz131)

noncomputable abbrev qz454 := (Enclosure.sfrac Bool.false 51734 1000)

noncomputable abbrev qz440 := qz454

noncomputable abbrev qz354 := qz440

noncomputable abbrev qz139 := (@HMul.hMul Real Real Real qz254 qz354 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz140 := qz354

noncomputable abbrev qz355 := (@Eq.refl Real qz440)

noncomputable abbrev qz141 := qz355

noncomputable def ep410 := @Enclosure.Complex.IsNear.of_eq qz138 (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz139)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz139)))) Bool.true 1614937509 8589934592 1286670685821 1136585785475072 Bool.false 2927685357 4294967296 1292724473611 1136585785475072 (BSN.cpow_neg_s_mk qz140 51734 1000 2 qz141 rfl)

noncomputable def ep411 := nat_lit 33344727106225854184049430854220366908217921472152042082544039615854084096

noncomputable def ep412 := nat_lit 56884473378795079798521525313522711896915882172859997698460047879766016

noncomputable def ep413 := nat_lit 99920412371919972392551249512034055300859932652110406252235198751802720256

noncomputable def ep414 := BSN.cos_dyadic_bound_f 698834308 536870912 3 2 262144 66223 ep411 ep83 ep412 ep413 ep86 ep412 69698 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 698834308) qz274 0 2 ep411 ep83 ep412 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 698834308) qz275 0 2 ep413 ep86 ep412 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz356 := (Enclosure.Real.IsNear.const Bool.false 51734 1000)

noncomputable abbrev qz142 := qz356

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4700137) qz115)

noncomputable def ep415 := @Enclosure.Real.IsNear.cos_image qz139 qz357 Bool.false 4700137 131072 411 262144 Bool.true 69698 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 587517171 16384000 25867 16539500 4700137 131072 411 262144 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz28 51734 1000 0 1 90852 131072 1 33079 587517171 16384000 25867 16539500 qz142 qz273 rfl) rfl) (Enclosure.sfrac_false_div 4700137 131072) (BSN.cos_reduce2 qz357 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24588046331043322527744) qz341) 226375608064910080 72057594037927936 Bool.false 69698 262144 5 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q2 4700137 131072 226375608064910080 72057594037927936 5 24588046331043322527744 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 69698 262144 24588046331043322527744 18889465931478580854784 698834308 536870912 66223 66158 (ep414 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep416 := nat_lit 59975001212503501467450158317345842265274725944135387750420503270233538560

noncomputable def ep417 := nat_lit 156985285456800645142695665504445788208838799377789004111970478011187265536

noncomputable def ep418 := BSN.sin_dyadic_bound_f 698834308 536870912 3 2 262144 66223 ep416 ep90 ep412 ep417 ep92 ep412 252708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 698834308) qz269 0 2 ep416 ep90 ep412 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 698834308) qz270 0 2 ep417 ep92 ep412 rfl rfl rfl rfl) rfl rfl

noncomputable def ep419 := @Enclosure.Real.IsNear.sin_image qz139 qz357 Bool.false 4700137 131072 411 262144 Bool.true 252708 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 587517171 16384000 25867 16539500 4700137 131072 411 262144 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz28 51734 1000 0 1 90852 131072 1 33079 587517171 16384000 25867 16539500 qz142 qz273 rfl) rfl) (Enclosure.sfrac_false_div 4700137 131072) (BSN.sin_reduce2 qz357 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24588046331043322527744) qz341) 226375608064910080 72057594037927936 Bool.false 252708 262144 5 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q2 4700137 131072 226375608064910080 72057594037927936 5 24588046331043322527744 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 252708 262144 24588046331043322527744 18889465931478580854784 698834308 536870912 66223 66158 (ep418 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep420 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz139)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz139))) Bool.true 1614937509 8589934592 1286670685821 1136585785475072 Bool.false 2927685357 4294967296 1292724473611 1136585785475072 (@Enclosure.Real.IsNear.mulLit_ft qz22 (Real.cos qz139) 46341 65536 1 131072 34849 131072 13857613 8671461376 1614937509 8589934592 1286670685821 1136585785475072 qz276 (@Enclosure.Real.IsNear.recentre' (Real.cos qz139) Bool.true 69698 262144 13857613 8671461376 34849 131072 13857613 8671461376 (ep415 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz22 (@Neg.neg Real Real.instNeg (Real.sin qz139)) 46341 65536 1 131072 63177 65536 13857613 8671461376 2927685357 4294967296 1292724473611 1136585785475072 qz276 (@Enclosure.Real.IsNear.neg (Real.sin qz139) Bool.true 63177 65536 13857613 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz139) Bool.true 252708 262144 13857613 8671461376 63177 65536 13857613 8671461376 (ep419 rfl rfl) rfl)) rfl)

noncomputable def ep421 := @ep408 1614937509 8589934592 1286670685821 1136585785475072 Bool.false 2927685357 4294967296 1292724473611 1136585785475072 Bool.false 6974997083 6974997083 8589934592 1286670685821 1136585785475072 Bool.false 2927685357 2927685357 4294967296 1292724473611 1136585785475072 (ep409 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz20 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz31)) (ep410 ep420) rfl rfl

noncomputable abbrev qz143 := (@HMul.hMul Real Real Real qz254 qz354 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep422 := @Enclosure.Complex.IsNear.of_eq qz137 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz143)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz143)))) Bool.false 38054435815 68719476736 2105666945915 2273171570950144 Bool.true 701502615 4294967296 1049901433095 1136585785475072 (BSN.cpow_neg_s_mk qz140 51734 1000 3 qz141 rfl)

noncomputable def ep423 := nat_lit 562201102588262801769525709967616

noncomputable def ep424 := BSN.cos_dyadic_bound_f 153983052 536870912 2 1 262144 66223 ep423 ep61 ep423 ep423 ep62 ep423 251435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 153983052) qz274 0 1 ep423 ep61 ep423 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 153983052) qz275 0 1 ep423 ep62 ep423 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14899081) qz27)

noncomputable def ep425 := @Enclosure.Real.IsNear.cos_image qz143 qz358 Bool.false 14899081 262144 411 262144 Bool.false 251435 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 3724770399 65536000 25867 16539500 14899081 262144 411 262144 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz35 51734 1000 0 1 143997 131072 1 33079 3724770399 65536000 25867 16539500 qz142 qz279 rfl) rfl) (Enclosure.sfrac_false_div 14899081 262144) (BSN.cos_reduce0 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10835594051970412838912) qz30) 226375608064910080 72057594037927936 Bool.false 251435 262144 9 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 14899081 262144 226375608064910080 72057594037927936 9 10835594051970412838912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 251435 262144 10835594051970412838912 37778931862957161709568 153983052 536870912 66223 66158 (ep424 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep426 := BSN.sin_dyadic_bound_f 153983052 536870912 2 1 262144 66223 ep423 ep57 ep423 ep423 ep58 ep423 74160 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 153983052) qz269 0 1 ep423 ep57 ep423 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 153983052) qz270 0 1 ep423 ep58 ep423 rfl rfl rfl rfl) rfl rfl

noncomputable def ep427 := @Enclosure.Real.IsNear.sin_image qz143 qz358 Bool.false 14899081 262144 411 262144 Bool.false 74160 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 3724770399 65536000 25867 16539500 14899081 262144 411 262144 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz35 51734 1000 0 1 143997 131072 1 33079 3724770399 65536000 25867 16539500 qz142 qz279 rfl) rfl) (Enclosure.sfrac_false_div 14899081 262144) (BSN.sin_reduce0 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10835594051970412838912) qz30) 226375608064910080 72057594037927936 Bool.false 74160 262144 9 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 14899081 262144 226375608064910080 72057594037927936 9 10835594051970412838912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 74160 262144 10835594051970412838912 37778931862957161709568 153983052 536870912 66223 66158 (ep426 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep428 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz143)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz143))) Bool.false 38054435815 68719476736 2105666945915 2273171570950144 Bool.true 701502615 4294967296 1049901433095 1136585785475072 (@Enclosure.Real.IsNear.mulLit_ff qz32 (Real.cos qz143) 151349 262144 1 262144 251435 262144 13857613 8671461376 38054435815 68719476736 2105666945915 2273171570950144 qz280 (@Enclosure.Real.IsNear.recentre' (Real.cos qz143) Bool.false 251435 262144 13857613 8671461376 251435 262144 13857613 8671461376 (ep425 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz32 (@Neg.neg Real Real.instNeg (Real.sin qz143)) 151349 262144 1 262144 4635 16384 13857613 8671461376 701502615 4294967296 1049901433095 1136585785475072 qz280 (@Enclosure.Real.IsNear.neg (Real.sin qz143) Bool.false 4635 16384 13857613 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz143) Bool.false 74160 262144 13857613 8671461376 4635 16384 13857613 8671461376 (ep427 rfl rfl) rfl)) rfl)

noncomputable def ep429 := @ep406 38054435815 68719476736 2105666945915 2273171570950144 Bool.true 701502615 4294967296 1049901433095 1136585785475072 Bool.false 806203264365198573568 93854412479 68719476736 4679008317557 2273171570950144 Bool.false 9561382071809605632 1113091371 2147483648 1171312953353 568292892737536 (ep407 (BSN.head_sum_c_succ qz131 2 3 rfl rfl) (ep421 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep422 ep428) rfl rfl

noncomputable abbrev qz144 := (@HMul.hMul Real Real Real qz254 qz354 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep430 := @Enclosure.Complex.IsNear.of_eq qz136 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz144)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz144)))) Bool.true 3687682585 8589934592 227973809057 284146446368768 Bool.true 17613189909 68719476736 1820790174077 2273171570950144 (BSN.cpow_neg_s_mk qz140 51734 1000 4 qz141 rfl)

noncomputable def ep431 := nat_lit 94439658508572589943351442062442496

noncomputable def ep432 := BSN.sin_dyadic_bound_f 554355808 536870912 2 1 262144 66223 ep431 ep57 ep431 ep431 ep58 ep431 225080 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 554355808) qz269 0 1 ep431 ep57 ep431 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 554355808) qz270 0 1 ep431 ep58 ep431 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18800549) qz27)

noncomputable def ep433 := @Enclosure.Real.IsNear.cos_image qz144 qz359 Bool.false 18800549 262144 411 262144 Bool.true 225080 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 587517171 8192000 25867 16539500 18800549 262144 411 262144 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz38 51734 1000 0 1 181704 131072 1 33079 587517171 8192000 25867 16539500 qz142 qz283 rfl) rfl) (Enclosure.sfrac_false_div 18800549 262144) (BSN.cos_reduce1 qz359 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39009322038793577955328) qz30) 226375608064910080 72057594037927936 Bool.false 225080 262144 11 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q1 18800549 262144 226375608064910080 72057594037927936 11 39009322038793577955328 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 225080 262144 39009322038793577955328 37778931862957161709568 554355808 536870912 66223 66158 (ep432 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep434 := nat_lit 13189761839305207016105444798558720819026208601169365190435863071184388096

noncomputable def ep435 := nat_lit 8918849099215807183494778366056060276884438949974089291257529306710016

noncomputable def ep436 := nat_lit 39551447819717189433949344838944050336524856925608147392725074154939744256

noncomputable def ep437 := BSN.cos_dyadic_bound_f 554355808 536870912 3 2 262144 66223 ep434 ep83 ep435 ep436 ep86 ep435 134379 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 554355808) qz274 0 2 ep434 ep83 ep435 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 554355808) qz275 0 2 ep436 ep86 ep435 rfl rfl rfl rfl) rfl rfl

noncomputable def ep438 := @Enclosure.Real.IsNear.sin_image qz144 qz359 Bool.false 18800549 262144 411 262144 Bool.false 134379 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 587517171 8192000 25867 16539500 18800549 262144 411 262144 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz38 51734 1000 0 1 181704 131072 1 33079 587517171 8192000 25867 16539500 qz142 qz283 rfl) rfl) (Enclosure.sfrac_false_div 18800549 262144) (BSN.sin_reduce1 qz359 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39009322038793577955328) qz30) 226375608064910080 72057594037927936 Bool.false 134379 262144 11 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q1 18800549 262144 226375608064910080 72057594037927936 11 39009322038793577955328 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 134379 262144 39009322038793577955328 37778931862957161709568 554355808 536870912 66223 66158 (ep437 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep439 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz144)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz144))) Bool.true 3687682585 8589934592 227973809057 284146446368768 Bool.true 17613189909 68719476736 1820790174077 2273171570950144 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz144) 131071 262144 1 262144 28135 32768 13857613 8671461376 3687682585 8589934592 227973809057 284146446368768 qz284 (@Enclosure.Real.IsNear.recentre' (Real.cos qz144) Bool.true 225080 262144 13857613 8671461376 28135 32768 13857613 8671461376 (ep433 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz144)) 131071 262144 1 262144 134379 262144 13857613 8671461376 17613189909 68719476736 1820790174077 2273171570950144 qz284 (@Enclosure.Real.IsNear.neg (Real.sin qz144) Bool.false 134379 262144 13857613 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz144) Bool.false 134379 262144 13857613 8671461376 134379 262144 13857613 8671461376 (ep438 rfl rfl) rfl)) rfl)

noncomputable def ep440 := @ep404 3687682585 8589934592 227973809057 284146446368768 Bool.true 17613189909 68719476736 1820790174077 2273171570950144 Bool.false 552787646755538731008 64352951799 68719476736 6502798790013 2273171570950144 Bool.false 38667019255780737024 18005733963 68719476736 6506041987489 2273171570950144 (ep405 (BSN.head_sum_c_succ qz131 3 4 rfl rfl) (ep429 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep430 ep439) rfl rfl

noncomputable abbrev qz145 := (@HMul.hMul Real Real Real qz254 qz354 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep441 := @Enclosure.Complex.IsNear.of_eq qz135 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz145)))) Bool.true 159087895 34359738368 812350447037 1136585785475072 Bool.true 30730693315 68719476736 1633282082859 2273171570950144 (BSN.cpow_neg_s_mk qz140 51734 1000 5 qz141 rfl)

noncomputable def ep442 := BSN.sin_dyadic_bound_f 5560091 536870912 1 0 262144 66223 0 1 1 0 1 1 2714 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 5560091) qz269 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 5560091) qz270 0 0 rfl) rfl rfl

noncomputable abbrev qz360 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21826781) qz27)

noncomputable def ep443 := @Enclosure.Real.IsNear.cos_image qz145 qz360 Bool.false 21826781 262144 411 262144 Bool.true 2714 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 682086923 8192000 25867 16539500 21826781 262144 411 262144 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz41 51734 1000 0 1 210952 131072 1 33079 682086923 8192000 25867 16539500 qz142 qz287 rfl) rfl) (Enclosure.sfrac_false_div 21826781 262144) (BSN.cos_reduce1 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 391256675424741097472) qz30) 226375608064910080 72057594037927936 Bool.false 2714 262144 13 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q1 21826781 262144 226375608064910080 72057594037927936 13 391256675424741097472 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2714 262144 391256675424741097472 37778931862957161709568 5560091 536870912 66223 66158 (ep442 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep444 := BSN.cos_dyadic_bound_f 5560091 536870912 1 0 262144 66223 0 1 1 0 1 1 262129 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 5560091) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 5560091) qz275 0 0 rfl) rfl rfl

noncomputable def ep445 := @Enclosure.Real.IsNear.sin_image qz145 qz360 Bool.false 21826781 262144 411 262144 Bool.false 262129 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 682086923 8192000 25867 16539500 21826781 262144 411 262144 (@Enclosure.Real.IsNear.mulLit_ff qz140 qz41 51734 1000 0 1 210952 131072 1 33079 682086923 8192000 25867 16539500 qz142 qz287 rfl) rfl) (Enclosure.sfrac_false_div 21826781 262144) (BSN.sin_reduce1 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 391256675424741097472) qz30) 226375608064910080 72057594037927936 Bool.false 262129 262144 13 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q1 21826781 262144 226375608064910080 72057594037927936 13 391256675424741097472 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 262129 262144 391256675424741097472 37778931862957161709568 5560091 536870912 66223 66158 (ep444 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep446 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz145))) Bool.true 159087895 34359738368 812350447037 1136585785475072 Bool.true 30730693315 68719476736 1633282082859 2273171570950144 (@Enclosure.Real.IsNear.mulLit_ft qz39 (Real.cos qz145) 117235 262144 1 262144 1357 131072 13857613 8671461376 159087895 34359738368 812350447037 1136585785475072 qz288 (@Enclosure.Real.IsNear.recentre' (Real.cos qz145) Bool.true 2714 262144 13857613 8671461376 1357 131072 13857613 8671461376 (ep443 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz39 (@Neg.neg Real Real.instNeg (Real.sin qz145)) 117235 262144 1 262144 262129 262144 13857613 8671461376 30730693315 68719476736 1633282082859 2273171570950144 qz288 (@Enclosure.Real.IsNear.neg (Real.sin qz145) Bool.false 262129 262144 13857613 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz145) Bool.false 262129 262144 13857613 8671461376 262129 262144 13857613 8671461376 (ep445 rfl rfl) rfl)) rfl)

noncomputable def ep447 := @ep402 159087895 34359738368 812350447037 1136585785475072 Bool.true 30730693315 68719476736 1633282082859 2273171570950144 Bool.false 2200218150122723213312 64034776009 68719476736 8127499684087 2273171570950144 Bool.true 874452548156309635072 1590619919 8589934592 2034831017587 568292892737536 (ep403 (BSN.head_sum_c_succ qz131 4 5 rfl rfl) (ep440 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep441 ep446) rfl rfl

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz254 qz354 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep448 := @Enclosure.Complex.IsNear.of_eq qz134 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz146)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz146)))) Bool.false 125186645 17179869184 185422376471 284146446368768 Bool.false 3506269505 8589934592 750204801301 1136585785475072 (BSN.cpow_neg_s_mk qz140 51734 1000 6 qz141 rfl)

noncomputable def ep449 := @Enclosure.Real.IsNear.mulLit_ff qz140 qz44 51734 1000 0 1 4034681531866359 2251799813685248 500000000033079 16539500000000000000 104365107184787108253 1125899906842624000 12933500000855654493 8269750000000000000000 qz142 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000033079 16539500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz290) Bool.false 8461340443916598509568 4722366482869645213696 1000000000066158 33079000000000000000 4034681531866359 2251799813685248 500000000033079 16539500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 53145 131072 24973259072661432 36028797018963968 33079 1000000000000000 rfl rfl rfl rfl (ep115 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep450 := BSN.sin_dyadic_bound_f 9584424 536870912 1 0 262144 66223 0 1 1 0 1 1 4679 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 9584424) qz269 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 9584424) qz270 0 0 rfl) rfl rfl

noncomputable abbrev qz361 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24299395) qz27)

noncomputable def ep451 := @Enclosure.Real.IsNear.cos_image qz146 qz361 Bool.false 24299395 262144 411 262144 Bool.false 4679 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 104365107184787108253 1125899906842624000 12933500000855654493 8269750000000000000000 24299395 262144 411 262144 (ep449 rfl) rfl) (Enclosure.sfrac_false_div 24299395 262144) (BSN.cos_reduce3 qz361 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 674443921012304117760) qz30) 226375608064910080 72057594037927936 Bool.false 4679 262144 14 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q3 24299395 262144 226375608064910080 72057594037927936 14 674443921012304117760 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4679 262144 674443921012304117760 37778931862957161709568 9584424 536870912 66223 66158 (ep450 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep452 := BSN.cos_dyadic_bound_f 9584424 536870912 1 0 262144 66223 0 1 1 0 1 1 262102 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 9584424) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 9584424) qz275 0 0 rfl) rfl rfl

noncomputable def ep453 := @Enclosure.Real.IsNear.sin_image qz146 qz361 Bool.false 24299395 262144 411 262144 Bool.true 262102 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 104365107184787108253 1125899906842624000 12933500000855654493 8269750000000000000000 24299395 262144 411 262144 (ep449 rfl) rfl) (Enclosure.sfrac_false_div 24299395 262144) (BSN.sin_reduce3 qz361 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 674443921012304117760) qz30) 226375608064910080 72057594037927936 Bool.false 262102 262144 14 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q3 24299395 262144 226375608064910080 72057594037927936 14 674443921012304117760 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 262102 262144 674443921012304117760 37778931862957161709568 9584424 536870912 66223 66158 (ep452 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep454 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz146)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz146))) Bool.false 125186645 17179869184 185422376471 284146446368768 Bool.false 3506269505 8589934592 750204801301 1136585785475072 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz146) 26755 65536 1 131072 4679 262144 13857613 8671461376 125186645 17179869184 185422376471 284146446368768 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz146) Bool.false 4679 262144 13857613 8671461376 4679 262144 13857613 8671461376 (ep451 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz42 (@Neg.neg Real Real.instNeg (Real.sin qz146)) 26755 65536 1 131072 131051 131072 13857613 8671461376 3506269505 8589934592 750204801301 1136585785475072 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz146) Bool.true 131051 131072 13857613 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz146) Bool.true 262102 262144 13857613 8671461376 131051 131072 13857613 8671461376 (ep453 rfl rfl) rfl)) rfl)

noncomputable def ep455 := @ep400 125186645 17179869184 185422376471 284146446368768 Bool.false 3506269505 8589934592 750204801301 1136585785475072 Bool.false 1108711835800096997376 64535522589 68719476736 9610878695855 2273171570950144 Bool.false 16455304644931878912 957824793 4294967296 4819866836475 1136585785475072 (ep401 (BSN.head_sum_c_succ qz131 5 6 rfl rfl) (ep447 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep448 ep454) rfl rfl

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz254 qz354 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep456 := @Enclosure.Complex.IsNear.of_eq qz133 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz147)))) Bool.false 12862596339 34359738368 345407144167 568292892737536 Bool.true 895593159 17179869184 687118007795 1136585785475072 (BSN.cpow_neg_s_mk qz140 51734 1000 7 qz141 rfl)

noncomputable def ep457 := @Enclosure.Real.IsNear.mulLit_ff qz140 qz47 51734 1000 0 1 4381783608859895 2251799813685248 500000000033079 16539500000000000000 22668719322075780793 225179981368524800 12933500000855654493 8269750000000000000000 qz142 (BSN.isNear_log_sfrac 7 1 4381783608859895 2251799813685248 500000000033079 16539500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz294) Bool.false 9189266258887746519040 4722366482869645213696 1000000000066158 33079000000000000000 4381783608859895 2251799813685248 500000000033079 16539500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 73349 131072 24973259072661432 36028797018963968 33079 1000000000000000 rfl rfl rfl rfl (ep129 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep458 := nat_lit 30453760034496055091525751234001

noncomputable def ep459 := BSN.cos_dyadic_bound_f 74286557 536870912 2 1 262144 66223 ep458 ep61 ep458 ep458 ep62 ep458 259638 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 74286557) qz274 0 1 ep458 ep61 ep458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 74286557) qz275 0 1 ep458 ep62 ep458 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13194931) qz115)

noncomputable def ep460 := @Enclosure.Real.IsNear.cos_image qz147 qz362 Bool.false 13194931 131072 411 262144 Bool.false 259638 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 22668719322075780793 225179981368524800 12933500000855654493 8269750000000000000000 13194931 131072 411 262144 (ep457 rfl) rfl) (Enclosure.sfrac_false_div 13194931 131072) (BSN.cos_reduce0 qz362 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2613725894771780616192) qz341) 226375608064910080 72057594037927936 Bool.false 259638 262144 16 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 13194931 131072 226375608064910080 72057594037927936 16 2613725894771780616192 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 259638 262144 2613725894771780616192 18889465931478580854784 74286557 536870912 66223 66158 (ep459 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep461 := BSN.sin_dyadic_bound_f 74286557 536870912 1 0 262144 66223 0 1 1 0 1 1 36156 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 74286557) qz269 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 74286557) qz270 0 0 rfl) rfl rfl

noncomputable def ep462 := @Enclosure.Real.IsNear.sin_image qz147 qz362 Bool.false 13194931 131072 411 262144 Bool.false 36156 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 22668719322075780793 225179981368524800 12933500000855654493 8269750000000000000000 13194931 131072 411 262144 (ep457 rfl) rfl) (Enclosure.sfrac_false_div 13194931 131072) (BSN.sin_reduce0 qz362 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2613725894771780616192) qz341) 226375608064910080 72057594037927936 Bool.false 36156 262144 16 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 13194931 131072 226375608064910080 72057594037927936 16 2613725894771780616192 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 36156 262144 2613725894771780616192 18889465931478580854784 74286557 536870912 66223 66158 (ep461 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep463 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz147))) Bool.false 12862596339 34359738368 345407144167 568292892737536 Bool.true 895593159 17179869184 687118007795 1136585785475072 (@Enclosure.Real.IsNear.mulLit_ff qz45 (Real.cos qz147) 99081 262144 1 262144 129819 131072 13857613 8671461376 12862596339 34359738368 345407144167 568292892737536 qz296 (@Enclosure.Real.IsNear.recentre' (Real.cos qz147) Bool.false 259638 262144 13857613 8671461376 129819 131072 13857613 8671461376 (ep460 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz147)) 99081 262144 1 262144 9039 65536 13857613 8671461376 895593159 17179869184 687118007795 1136585785475072 qz296 (@Enclosure.Real.IsNear.neg (Real.sin qz147) Bool.false 9039 65536 13857613 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz147) Bool.false 36156 262144 13857613 8671461376 9039 65536 13857613 8671461376 (ep462 rfl rfl) rfl)) rfl)

noncomputable def ep464 := @ep398 12862596339 34359738368 345407144167 568292892737536 Bool.true 895593159 17179869184 687118007795 1136585785475072 Bool.false 3101334561482663264256 90260715267 68719476736 10992507272523 2273171570950144 Bool.false 12608761316505550848 2935706013 17179869184 2753492422135 568292892737536 (ep399 (BSN.head_sum_c_succ qz131 6 7 rfl rfl) (ep455 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep456 ep463) rfl rfl

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz254 qz354 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep465 := @Enclosure.Complex.IsNear.of_eq qz132 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz148)))) Bool.false 8774436645 34359738368 648452844901 1136585785475072 Bool.true 4200672627 17179869184 40511657867 71036611592192 (BSN.cpow_neg_s_mk qz140 51734 1000 8 qz141 rfl)

noncomputable def ep466 := @Enclosure.Real.IsNear.mulLit_ff qz140 qz50 51734 1000 0 1 9364972152248037 4503599627370496 1000000000099237 33079000000000000000 242243734662199973079 2251799813685248000 25867000002566963479 16539500000000000000000 qz142 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000099237 33079000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz298) Bool.false 9819885039515637645312 4722366482869645213696 1000000000099237 33079000000000000000 9364972152248037 4503599627370496 1000000000099237 33079000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 131072 24973259072661432 36028797018963968 33079 1000000000000000 rfl rfl rfl rfl (ep140 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep467 := nat_lit 28256532366655593458619263427438961

noncomputable def ep468 := BSN.cos_dyadic_bound_f 409996091 536870912 2 1 262144 66223 ep467 ep61 ep467 ep467 ep62 ep467 189345 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 409996091) qz274 0 1 ep467 ep61 ep467 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 409996091) qz275 0 1 ep467 ep62 ep467 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14100441) qz115)

noncomputable def ep469 := @Enclosure.Real.IsNear.cos_image qz148 qz363 Bool.false 14100441 131072 411 262144 Bool.false 189345 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 242243734662199973079 2251799813685248000 25867000002566963479 16539500000000000000000 14100441 131072 411 262144 (ep466 rfl) rfl) (Enclosure.sfrac_false_div 14100441 131072) (BSN.cos_reduce0 qz363 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14425455048204455247872) qz341) 226375608064910080 72057594037927936 Bool.false 189345 262144 17 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 14100441 131072 226375608064910080 72057594037927936 17 14425455048204455247872 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 189345 262144 14425455048204455247872 18889465931478580854784 409996091 536870912 66223 66158 (ep468 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep470 := BSN.sin_dyadic_bound_f 409996091 536870912 2 1 262144 66223 ep467 ep57 ep467 ep467 ep58 ep467 181294 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 409996091) qz269 0 1 ep467 ep57 ep467 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 409996091) qz270 0 1 ep467 ep58 ep467 rfl rfl rfl rfl) rfl rfl

noncomputable def ep471 := @Enclosure.Real.IsNear.sin_image qz148 qz363 Bool.false 14100441 131072 411 262144 Bool.false 181294 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 242243734662199973079 2251799813685248000 25867000002566963479 16539500000000000000000 14100441 131072 411 262144 (ep466 rfl) rfl) (Enclosure.sfrac_false_div 14100441 131072) (BSN.sin_reduce0 qz363 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14425455048204455247872) qz341) 226375608064910080 72057594037927936 Bool.false 181294 262144 17 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 14100441 131072 226375608064910080 72057594037927936 17 14425455048204455247872 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 181294 262144 14425455048204455247872 18889465931478580854784 409996091 536870912 66223 66158 (ep470 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep472 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz148))) Bool.false 8774436645 34359738368 648452844901 1136585785475072 Bool.true 4200672627 17179869184 40511657867 71036611592192 (@Enclosure.Real.IsNear.mulLit_ff qz48 (Real.cos qz148) 46341 131072 1 131072 189345 262144 13857613 8671461376 8774436645 34359738368 648452844901 1136585785475072 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz148) Bool.false 189345 262144 13857613 8671461376 189345 262144 13857613 8671461376 (ep469 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz148)) 46341 131072 1 131072 90647 131072 13857613 8671461376 4200672627 17179869184 40511657867 71036611592192 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz148) Bool.false 90647 131072 13857613 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz148) Bool.false 181294 262144 13857613 8671461376 90647 131072 13857613 8671461376 (ep471 rfl rfl) rfl)) rfl)

noncomputable def ep473 := @ep396 8774436645 34359738368 648452844901 1136585785475072 Bool.true 4200672627 17179869184 40511657867 71036611592192 Bool.false 3704309256380246654976 107809588557 68719476736 12289412962325 2273171570950144 Bool.true 21731960950647422976 632483307 8589934592 3077585685071 568292892737536 (ep397 (BSN.head_sum_c_succ qz131 7 8 rfl rfl) (ep464 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep465 ep472) rfl rfl

theorem EMRow10.d10 : Enclosure.Complex.IsNear qz130 Bool.false 107809588557 68719476736 12289412962325 2273171570950144 Bool.true 632483307 8589934592 3077585685071 568292892737536 := ep395 (BSN.head_sum_c_succ qz131 8 9 rfl rfl) (ep473 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow10.d11 : @Eq Nat (Nat.pow 11 1) 11 := @Eq.refl Nat 11

noncomputable def ep474 := nat_lit 277709233513406241496822809803

noncomputable def ep475 := nat_lit 132600494058123526968180736000

noncomputable def ep476 := nat_lit 108644350935311010917095452711449627

noncomputable def ep477 := nat_lit 13190376778636272153353884025225216000

noncomputable abbrev qz441 := (@HAdd.hAdd Complex Complex Complex qz447 (@HAdd.hAdd Complex Complex Complex qz447 qz450 (@HMul.hMul Complex Complex Complex qz449 Complex.I (@HDiv.hDiv Complex Complex Complex qz451 (↑qz454) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz364 := qz441

noncomputable abbrev qz149 := (Complex.Stirling.logGammaStirling 1 qz364)

noncomputable abbrev qz442 := (@HAdd.hAdd Complex Complex Complex qz447 qz450 (@HMul.hMul Complex Complex Complex qz449 Complex.I (@HDiv.hDiv Complex Complex Complex qz451 (↑qz454) (2 : Complex))))

noncomputable abbrev qz365 := qz442

noncomputable abbrev qz150 := qz365

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz254 (@HDiv.hDiv Real Real Real qz257 qz354 (2 : Real)) (Real.log Real.pi))

noncomputable def ep478 := Complex.re (@HMul.hMul Complex Complex Complex qz51 (Complex.exp (@HMul.hMul Complex Complex Complex qz51 Complex.I ↑(@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))))) qz151))) (zetaApproximant qz131 1 11))

noncomputable def ep479 := @Enclosure.Real.IsNear.of_eq ep478 (@HSub.hSub Real Real Real qz52 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))))) qz151)) (Complex.re (zetaApproximant qz131 1 11))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))))) qz151)) (Complex.im (zetaApproximant qz131 1 11))))

noncomputable def ep480 := nat_lit 55541754450682305334737888519

noncomputable def ep481 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))))) qz151)) (Complex.re (zetaApproximant qz131 1 11))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))))) qz151)) (Complex.im (zetaApproximant qz131 1 11))) ep480

noncomputable def ep482 := nat_lit 26520098811624705393636147200

noncomputable def ep483 := nat_lit 715101623899464954746412773978763863

noncomputable def ep484 := nat_lit 87056486738999396212135634566486425600

noncomputable def ep485 := nat_lit 1506823796115040079183872000

noncomputable def ep486 := nat_lit 1219432670992323316510758698002297

noncomputable def ep487 := nat_lit 54410304211874622632584771604054016000

noncomputable def ep488 := nat_lit 83691776291773780383161984394441415782648579624219443200

noncomputable def ep489 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))))) qz151)) (Complex.re (zetaApproximant qz131 1 11)) 262143 262144 5918653

noncomputable def ep490 := nat_lit 68068790809184280068019437

noncomputable def ep491 := nat_lit 10039425070835879856675225600

noncomputable def ep492 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))))) qz151)) Bool.true 262143 262144 5918653

noncomputable abbrev qz366 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 463249) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep493 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))))) qz151) qz366 Bool.false 463249 16384 171

noncomputable def ep494 := nat_lit 1625899008000000000000000000

noncomputable def ep495 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))))) qz151) Bool.false 152804312459693804899 5404319552844595200 1051780678445143778785337 ep494

noncomputable def ep496 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))))) qz151 1564150552831815418607 27021597764222976000 410039808695143778785337 ep494 1940568207 65536000

noncomputable def ep497 := nat_lit 50070917106792465989304320000

noncomputable def ep498 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 182513682660249350523 4503599627370496000 116732766817190150591453 ep173 Bool.false 1564150552831815418607 27021597764222976000

noncomputable def ep499 := @Enclosure.Complex.IsNear.subLitP qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 153208092232174167523 4503599627370496000 112636766814751302079453 ep173 Bool.false 1647475529499511834607 27021597764222976000 360887808693517879777337

noncomputable def ep500 := nat_lit 821968553218715932113266798292369408

noncomputable def ep501 := nat_lit 440269240430294952262081896557576192

noncomputable abbrev qz367 := (@HSub.hSub Complex Complex Complex qz430 qz441 qz433)

noncomputable abbrev qz368 := (Complex.log qz441)

noncomputable abbrev qz152 := (@HSub.hSub Complex Complex Complex qz302 (@HMul.hMul Complex Complex Complex qz301 qz367 qz368) qz364)

noncomputable abbrev qz153 := qz364

noncomputable def ep502 := @Enclosure.Complex.IsNear.of_eq qz149 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz152 qz58) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz61 qz153 (@HSub.hSub Int Int Int qz63 qz64 (@HMul.hMul Int Int Int qz65 qz66 (@Nat.cast Int instNatCastInt k)))))) Bool.true 153208092232174167523

noncomputable def ep503 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz152 qz58) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz61 qz153 (@HSub.hSub Int Int Int qz63 qz64 (@HMul.hMul Int Int Int qz65 qz66 (@Nat.cast Int instNatCastInt k))))) Bool.true 153209344779274839523 4503599627370496000

noncomputable def ep504 := nat_lit 329011872809869844243655163904

noncomputable def ep505 := nat_lit 884481690020085822200253251584000

noncomputable def ep506 := @ep503 27499118226474304993 66158000000000000000000 Bool.false 549187309509484462757 9007199254740992000 14683500007758778687 66158000000000000000000 Bool.false 597261 2147483648 3 2147483648 Bool.true 5149783429 1610612736000 25867 1610612736000 Bool.true ep504 153208092232174167523 4503599627370496000 112636766814751302079453 ep173 Bool.false ep505

noncomputable def ep507 := @Enclosure.Complex.IsNear.addLitP qz152 qz58 Bool.true 157347855006616151523 4503599627370496000 26742000001376648743 66158000000000000000000

noncomputable def ep508 := nat_lit 40162910477818223531917312

noncomputable def ep509 := @ep507 Bool.false 549187309509484462757 9007199254740992000 14683500007758778687 66158000000000000000000 Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 Bool.true ep508 153209344779274839523 4503599627370496000 27499118226474304993 66158000000000000000000 Bool.false 549187309509484462757 549187309509484462757 9007199254740992000

noncomputable abbrev qz154 := (@HMul.hMul Complex Complex Complex qz301 qz367 qz368)

noncomputable def ep510 := @Enclosure.Complex.IsNear.subLitP qz154 qz153 Bool.true 147214755845032535523 4503599627370496000 26742000001376648743 66158000000000000000000 Bool.false 782176532631869702821

noncomputable def ep511 := nat_lit 2196749238037937851028000

noncomputable def ep512 := @ep510 9007199254740992000 14683500007758778687 66158000000000000000000 Bool.false 9000 4000 0 1 Bool.false 103468 4000 0 1 Bool.true 629391420026464606092000 157347855006616151523 4503599627370496000 26742000001376648743 66158000000000000000000 Bool.false ep511 549187309509484462757 9007199254740992000 14683500007758778687 66158000000000000000000

noncomputable abbrev qz155 := qz367

noncomputable abbrev qz156 := qz368

noncomputable def ep513 := @Enclosure.Complex.IsNear.mul qz155 qz156 Bool.true 147214755845032535523 4503599627370496000 26742000001376648743 66158000000000000000000 Bool.false 782176532631869702821 9007199254740992000 14683500007758778687

noncomputable abbrev qz157 := (Complex.re qz367)

noncomputable abbrev qz158 := (Complex.re qz368)

noncomputable abbrev qz159 := (Complex.im qz367)

noncomputable abbrev qz160 := (Complex.im qz368)

noncomputable def ep514 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz157 qz158) (@HMul.hMul Real Real Real qz0 qz159 qz160) 205338462428733641 36028797018963968 3500000002083977 264632000000000000000 21610257956078030081 562949953421312000

noncomputable def ep515 := nat_lit 662996319567127074965808224202129408

noncomputable def ep516 := @Enclosure.Real.IsNear.mulLit_ff qz157 qz158 7000 4000 0 1 29334066061247663 9007199254740992 500000000297711 66158000000000000000

noncomputable def ep517 := @Enclosure.Complex.IsNear.re_isNear qz155 Bool.false 7000 4000 0 1 Bool.false 103468 4000 0 1

noncomputable abbrev qz369 := (Enclosure.sfrac Bool.false 103468 4000)

noncomputable abbrev qz161 := qz369

noncomputable def ep518 := @Enclosure.Complex.IsNear.of_eq qz155 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz161) Bool.false 7000 4000 0 1 Bool.false 103468 4000 0

noncomputable abbrev qz162 := (Complex.mk qz316 qz369)

noncomputable def ep519 := @Enclosure.Complex.IsNear.of_eq qz156 (Complex.log qz162) Bool.false 29334066061247663 9007199254740992 500000000297711 66158000000000000000 Bool.false 835437350913443 562949953421312 1000000000033079 66158000000000000000

noncomputable def ep520 := nat_lit 1946033995895279686892833244126039743856640

noncomputable def ep521 := nat_lit 12260061705462003636548848234766711390208

noncomputable def ep522 := nat_lit 135963082813136618194160422050956771328

noncomputable def ep523 := BSN.log_dyadic_bound 2594627024 18978627024 3 2 ep520 262144 66158 ep521 ep522 72128 21573254048 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2594627024) (BSN.artanhQ 18978627024) 0 2 ep521 ep520 ep522 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz370 := (Real.log (Enclosure.sfrac Bool.false 10786627024 16000000))

noncomputable def ep524 := @Enclosure.Real.IsNear.mulLit_ff qz76 qz370 1 2 0 1 29334066061247663 4503599627370496 500000000297711 33079000000000000000 29334066061247663 9007199254740992 500000000297711 66158000000000000000 qz318 (BSN.isNear_log_sfrac 10786627024 16000000 29334066061247663 4503599627370496 500000000297711 33079000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10786627024) qz319)) Bool.false 61517995308477658955776 9444732965739290427392 1000000000595422 66158000000000000000 29334066061247663 4503599627370496 500000000297711 33079000000000000000 (BSN.log_rat_reduce_isNear 10786627024 16000000 9 21573254048 16384000000 72128 262144 24973259072661432 36028797018963968 66158 1000000000000000 rfl rfl rfl rfl (ep523 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep525 := BSN.arctan_dyadic_bound_f 9000 103468 1 0 262144 66158 0 1 1 0 1 1 22744 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 103468) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 103468) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz371 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 103468)))

noncomputable def ep526 := @Enclosure.Real.IsNear.subLit_ff_p qz77 qz371 884279719003555 562949953421312 1 2000000000000000 22744 262144 1 66158 219004888917853601792 835437350913443 562949953421312 1000000000033079 66158000000000000000 qz78 (ep525 rfl) rfl rfl

noncomputable abbrev qz372 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 103468) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep527 := @Enclosure.Complex.IsNear.re_isNear qz156 Bool.false 29334066061247663 9007199254740992 500000000297711 66158000000000000000 Bool.false 835437350913443 562949953421312 1000000000033079 66158000000000000000 (ep519 (@congrArg Complex Complex qz153 qz162 Complex.log (BSN.w_shift_mk qz140 Bool.false 51734 1000 2 qz141 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz162) Bool.false 29334066061247663 9007199254740992 500000000297711 66158000000000000000 Bool.false 835437350913443 562949953421312 1000000000033079 66158000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz162)) (@HMul.hMul Real Real Real qz0 qz76 qz370) Bool.false 29334066061247663 9007199254740992 500000000297711 66158000000000000000 (Enclosure.clog_re_eq 9000 103468 4000 10786627024 16000000 rfl rfl rfl) (ep524 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz162)) qz372 Bool.false 835437350913443 562949953421312 1000000000033079 66158000000000000000 (Enclosure.clog_im_eq 9000 103468 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz372 (@HSub.hSub Real Real Real qz52 qz77 qz371) Bool.false 835437350913443 562949953421312 1000000000033079 66158000000000000000 (BSN.arctan_recip 103468 9000 rfl rfl) ep526))))

noncomputable def ep528 := @Enclosure.Real.IsNear.mulLit_ff qz159 qz160 103468 4000 0 1 835437350913443 562949953421312 1000000000033079 66158000000000000000

noncomputable def ep529 := @Enclosure.Complex.IsNear.im_isNear qz155 Bool.false 7000 4000 0 1 Bool.false 103468 4000 0 1

noncomputable def ep530 := @Enclosure.Complex.IsNear.im_isNear qz156 Bool.false 29334066061247663 9007199254740992 500000000297711 66158000000000000000 Bool.false 835437350913443 562949953421312 1000000000033079 66158000000000000000 (ep519 (@congrArg Complex Complex qz153 qz162 Complex.log (BSN.w_shift_mk qz140 Bool.false 51734 1000 2 qz141 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz162) Bool.false 29334066061247663 9007199254740992 500000000297711 66158000000000000000 Bool.false 835437350913443 562949953421312 1000000000033079 66158000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz162)) (@HMul.hMul Real Real Real qz0 qz76 qz370) Bool.false 29334066061247663 9007199254740992 500000000297711 66158000000000000000 (Enclosure.clog_re_eq 9000 103468 4000 10786627024 16000000 rfl rfl rfl) (ep524 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz162)) qz372 Bool.false 835437350913443 562949953421312 1000000000033079 66158000000000000000 (Enclosure.clog_im_eq 9000 103468 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz372 (@HSub.hSub Real Real Real qz52 qz77 qz371) Bool.false 835437350913443 562949953421312 1000000000033079 66158000000000000000 (BSN.arctan_recip 103468 9000 rfl rfl) ep526))))

noncomputable abbrev qz373 := (Enclosure.Real.IsNear.const Bool.false 103468 4000)

noncomputable abbrev qz163 := (@ep518 1 (BSN.w_sub_half_mk qz354 Bool.false 51734 1000 2 qz355 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz369 Bool.false 7000 4000 0 1 Bool.false 103468 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz373))

noncomputable def ep531 := @ep514 25867000000855654493 66158000000000000000000 ep515 147214755845032535523 4503599627370496000 26742000001376648743 66158000000000000000000 (@ep516 205338462428733641 36028797018963968 3500000002083977 264632000000000000000 (ep517 qz163) ep527 rfl) (@ep528 21610257956078030081 562949953421312000 25867000000855654493 66158000000000000000000 (ep529 qz163) ep530 rfl) rfl

noncomputable def ep532 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz157 qz160) (@HMul.hMul Real Real Real qz0 qz159 qz158) 5848061456394101 2251799813685248 7000000000231553 264632000000000000000 758784286806293298821 9007199254740992000

noncomputable def ep533 := nat_lit 1761304970449417499285616822591684608

noncomputable def ep534 := @Enclosure.Real.IsNear.mulLit_ff qz157 qz160 7000 4000 0 1 835437350913443 562949953421312 1000000000033079 66158000000000000000

noncomputable def ep535 := @Enclosure.Real.IsNear.mulLit_ff qz159 qz158 103468 4000 0 1 29334066061247663 9007199254740992 500000000297711 66158000000000000000

noncomputable def ep536 := @ep532 12933500007700890437 66158000000000000000000 ep533 782176532631869702821 9007199254740992000 14683500007758778687 66158000000000000000000 (@ep534 5848061456394101 2251799813685248 7000000000231553 264632000000000000000 (ep517 qz163) ep530 rfl) (@ep535 758784286806293298821 9007199254740992000 12933500007700890437 66158000000000000000000 (ep529 qz163) ep527 rfl) rfl

noncomputable def ep537 := @Enclosure.Complex.IsNear.of_eq qz153 qz162 Bool.false 9000 4000 0 1 Bool.false 103468 4000 0 1 (BSN.w_shift_mk qz140 Bool.false 51734 1000 2 qz141 rfl)

noncomputable abbrev qz374 := (ep537 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 103468 4000) Bool.false 9000 4000 0 1 Bool.false 103468 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 103468 4000)))

noncomputable abbrev qz164 := qz374

noncomputable def ep538 := ep512 (@ep513 66158000000000000000000 (ep531 rfl) (ep536 rfl)) qz164 rfl rfl rfl rfl rfl rfl

noncomputable def ep539 := @ep509 14683500007758778687 66158000000000000000000 (ep538 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz81 (↑qz3) Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 (@ep215 262144 3 262144 (ep217 rfl) (ep219 rfl) rfl rfl) (@ep220 1 0 1 (ep222 rfl) (ep224 rfl) rfl rfl))

noncomputable abbrev qz375 := (@HPow.hPow Complex Int Complex qz435 qz441 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz165 := qz375

noncomputable def ep540 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz61 qz153 (@HSub.hSub Int Int Int qz63 qz64 (@HMul.hMul Int Int Int qz65 qz66 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz61 qz153 (@HSub.hSub Int Int Int qz63 qz64 (@HMul.hMul Int Int Int qz65 qz66 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84) qz165)) Bool.false 597261 2147483648 3 2147483648

noncomputable def ep541 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz61 qz153 (@HSub.hSub Int Int Int qz63 qz64 (@HMul.hMul Int Int Int qz65 qz66 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84) qz165) Bool.false 0 1 0 1 Bool.false

noncomputable def ep542 := @ep541 0 1 0 1 Bool.false 597261 2147483648 3 2147483648 Bool.true 5149783429 1610612736000 25867 1610612736000 Bool.false 597261 597261 2147483648 3 2147483648 Bool.true 5149783429 5149783429 1610612736000 25867

noncomputable def ep543 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz53 (@HMul.hMul Complex Complex Complex qz51 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz61 qz153 (@HSub.hSub Int Int Int qz63 qz64 (@HMul.hMul Int Int Int qz65 qz66 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false

noncomputable def ep544 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84) qz165 Bool.false 597261 2147483648 3 2147483648 Bool.true 5149783429 1610612736000 25867 1610612736000

noncomputable abbrev qz166 := (Complex.re qz375)

noncomputable abbrev qz167 := (Complex.im qz375)

noncomputable def ep545 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz166) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz167) 597261 2147483648 3 2147483648 0 1 0

noncomputable def ep546 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz166 1 12 0 1 1791783 536870912 9 536870912 597261

noncomputable def ep547 := @Enclosure.Complex.IsNear.re_isNear qz165 Bool.false 1791783 536870912 9 536870912 Bool.true 5149783429 134217728000 25867 134217728000

noncomputable abbrev qz376 := (@HPow.hPow Complex Nat Complex qz436 qz441 1)

noncomputable abbrev qz168 := (@Inv.inv Complex Complex.instInv qz376)

noncomputable def ep548 := @Enclosure.Complex.IsNear.of_eq qz165 qz168 Bool.false 1791783 536870912 9 536870912 Bool.true 5149783429 134217728000 25867

noncomputable def ep549 := @Enclosure.Complex.IsNear.of_parts qz168 Bool.false 1791783 536870912 9 536870912 Bool.true 5149783429 134217728000 25867

noncomputable abbrev qz169 := (Complex.re qz376)

noncomputable abbrev qz170 := qz376

noncomputable def ep550 := @Enclosure.Real.IsNear.mulLit_ff qz169 (@Inv.inv Real Real.instInv (@DFunLike.coe qz90 Complex (fun (x : Complex) => Real) qz91 Complex.normSq qz170)) 9000 4000 0 1 199087 134217728 1 134217728

noncomputable def ep551 := @Enclosure.Complex.IsNear.re_isNear qz170 Bool.false 9000 4000 0 1 Bool.false 103468 4000 0 1

noncomputable def ep552 := @Enclosure.Complex.IsNear.of_eq qz170 qz153 Bool.false 9000 4000 0 1 Bool.false 103468 4000 0

noncomputable def ep553 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz90 Complex (fun (x : Complex) => Real) qz91 Complex.normSq qz170)) Bool.false 199087 134217728 1 134217728 199087 134217728 1

noncomputable abbrev qz171 := (Complex.im qz376)

noncomputable def ep554 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz90 Complex (fun (x : Complex) => Real) qz91 Complex.normSq qz170) (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 qz169 qz169) (@HMul.hMul Real Real Real qz0 qz171 qz171)) Bool.false 674164189 1000000 0 1

noncomputable def ep555 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz169 qz169) (@HMul.hMul Real Real Real qz0 qz171 qz171) 81 16 0 1 669101689 1000000

noncomputable def ep556 := @Enclosure.Real.IsNear.mulLit_ff qz169 qz169 9000 4000 0 1 9000 4000 0 1

noncomputable def ep557 := @Enclosure.Real.IsNear.mulLit_ff qz171 qz171 103468 4000 0 1 103468 4000 0 1

noncomputable def ep558 := @Enclosure.Complex.IsNear.im_isNear qz170 Bool.false 9000 4000 0 1 Bool.false 103468 4000 0 1

noncomputable abbrev qz172 := (ep551 (@ep552 1 (BSN.pow_one_c qz364) qz374))

noncomputable abbrev qz173 := (ep558 (@ep552 1 (BSN.pow_one_c qz364) qz374))

noncomputable def ep559 := @ep555 0 1 10786627024 674164189 1000000 0 1 (@ep556 81 16 0 1 qz172 qz172 rfl) (@ep557 669101689 1000000 0 1 qz173 qz173 rfl)

noncomputable def ep560 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz90 Complex (fun (x : Complex) => Real) qz91 Complex.normSq qz170) 674164189 1000000 0 1 99543 99544 67108864 (ep554 (Enclosure.Complex.normSq_eq_mul_add_mul qz170) (ep559 rfl rfl)) rfl

noncomputable def ep561 := @Enclosure.Real.IsNear.of_eq (Complex.re qz168) (@HMul.hMul Real Real Real qz0 qz169 (@Inv.inv Real Real.instInv (@DFunLike.coe qz90 Complex (fun (x : Complex) => Real) qz91 Complex.normSq qz170))) Bool.false 1791783 536870912 9 536870912 (Enclosure.Complex.inv_re_eq_mul qz170) (@ep550 1791783 536870912 9 536870912 qz172 (@ep553 134217728 (ep560 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep562 := @Enclosure.Real.IsNear.of_eq (Complex.im qz168) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz171) (@Inv.inv Real Real.instInv (@DFunLike.coe qz90 Complex (fun (x : Complex) => Real) qz91 Complex.normSq qz170))) Bool.true 5149783429 134217728000 25867 134217728000 (Enclosure.Complex.inv_im_eq_mul qz170)

noncomputable def ep563 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz171) (@Inv.inv Real Real.instInv (@DFunLike.coe qz90 Complex (fun (x : Complex) => Real) qz91 Complex.normSq qz170)) 103468 4000 0 1 199087 134217728 1

noncomputable def ep564 := @ep563 134217728 5149783429 134217728000 25867 134217728000 (@Enclosure.Real.IsNear.neg qz171 Bool.false 103468 4000 0 1 qz173) (@ep553 134217728 (ep560 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep565 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz167 0 1 0 1 5149783429 134217728000 25867 134217728000 0

noncomputable def ep566 := @Enclosure.Complex.IsNear.im_isNear qz165 Bool.false 1791783 536870912 9 536870912 Bool.true 5149783429 134217728000 25867 134217728000

noncomputable abbrev qz174 := (@ep548 134217728000 (BSN.zpow_one_sub_two_mul qz364 1 1 rfl rfl) (@ep549 134217728000 ep561 (ep562 ep564)))

noncomputable def ep567 := @ep545 1 597261 597261 2147483648 3 2147483648 (@ep546 2147483648 3 2147483648 ep234 (ep547 qz174) rfl) (@ep565 1 0 1 ep254 (ep566 qz174) rfl) rfl

noncomputable def ep568 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz167) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz166) 5149783429 1610612736000 25867 1610612736000 0 1 0

noncomputable def ep569 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz167 1 12 0 1 5149783429 134217728000 25867 134217728000 5149783429

noncomputable def ep570 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 (@Rat.cast Complex Complex.instRatCast (bernoulli qz83)) qz84)) qz166 0 1 0 1 1791783 536870912 9 536870912 0

noncomputable def ep571 := @ep568 1 5149783429 5149783429 1610612736000 25867 1610612736000 (@ep569 1610612736000 25867 1610612736000 ep234 (ep566 qz174) rfl) (@ep570 1 0 1 ep254 (ep547 qz174) rfl) rfl

noncomputable def ep572 := @ep542 1610612736000 (@ep543 0 1 0 1 (BSN.stirling_sum_base qz153) qz98) (ep544 (ep567 rfl) (ep571 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep573 := @ep506 1647475529499511834607 27021597764222976000 360887808693517879777337 ep494 (ep539 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep540 Bool.true 5149783429 1610612736000 25867 1610612736000 (BSN.stirling_sum_succ qz153 0 1 rfl) (ep572 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz140 2) Bool.false 29305590428075183 4503599627370496 500000000297711 33079000000000000000 Bool.false 867968506955171 281474976710656

noncomputable abbrev qz175 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz260 qz365 qz324))

noncomputable def ep575 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz140 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz140 1) qz175) Bool.false 29305590428075183 4503599627370496 500000000297711 33079000000000000000 Bool.false 867968506955171 281474976710656 1000000000033079 33079000000000000000

noncomputable def ep576 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz140 1) qz175 Bool.false 29300548136469679 9007199254740992 500000000297711 66158000000000000000 Bool.false 878840142923171 562949953421312 1000000000033079 66158000000000000000 Bool.false

noncomputable def ep577 := nat_lit 527922584527007074071987536003072

noncomputable def ep578 := nat_lit 977245661123158470318520008704

noncomputable abbrev qz176 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz260 qz365 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep579 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz140 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz140 0) qz176) Bool.false 29300548136469679 9007199254740992 500000000297711 66158000000000000000 Bool.false 878840142923171 562949953421312 1000000000033079 66158000000000000000

noncomputable def ep580 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz140 0) qz176 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz377 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz161))

noncomputable def ep581 := @Enclosure.Complex.IsNear.of_eq qz176 qz377 Bool.false 29300548136469679 9007199254740992 500000000297711 66158000000000000000 Bool.false 878840142923171 562949953421312 1000000000033079 66158000000000000000

noncomputable def ep582 := nat_lit 1913428662281377440807753713870884543856640

noncomputable def ep583 := nat_lit 11412131034717328734630016952017271390208

noncomputable def ep584 := nat_lit 119954230376801382845664291019916771328

noncomputable def ep585 := BSN.log_dyadic_bound 2514627024 18898627024 3 2 ep582 262144 66158 ep583 ep584 70177 21413254048 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2514627024) (BSN.artanhQ 18898627024) 0 2 ep583 ep582 ep584 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep586 := @Enclosure.Real.IsNear.mulLit_ff qz76 (Real.log (Enclosure.sfrac Bool.false 10706627024 16000000)) 1 2 0 1 29300548136469679 4503599627370496 500000000297711 33079000000000000000 29300548136469679 9007199254740992 500000000297711 66158000000000000000 qz318 (BSN.isNear_log_sfrac 10706627024 16000000 29300548136469679 4503599627370496 500000000297711 33079000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10706627024) qz319)) Bool.false 61447703125493660254208 9444732965739290427392 1000000000595422 66158000000000000000 29300548136469679 4503599627370496 500000000297711 33079000000000000000 (BSN.log_rat_reduce_isNear 10706627024 16000000 9 21413254048 16384000000 70177 262144 24973259072661432 36028797018963968 66158 1000000000000000 rfl rfl rfl rfl (ep585 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep587 := BSN.arctan_dyadic_bound_f 1000 103468 1 0 262144 66158 0 1 1 0 1 1 2533 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 103468) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 103468) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz378 := (@Nat.cast Real Real.instNatCast 103468)

noncomputable def ep588 := @Enclosure.Real.IsNear.subLit_ff_p qz77 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz329 qz378)) 884279719003555 562949953421312 1 2000000000000000 2533 262144 1 66158 230382670426451738624 878840142923171 562949953421312 1000000000033079 66158000000000000000 qz78 (ep587 rfl) rfl rfl

noncomputable abbrev qz177 := (@HAdd.hAdd Complex Complex Complex qz260 qz365 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz379 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz161)

noncomputable def ep589 := @ep580 29300548136469679 9007199254740992 500000000297711 66158000000000000000 Bool.false 878840142923171 562949953421312 1000000000033079 66158000000000000000 Bool.false 29300548136469679 29300548136469679 9007199254740992 500000000297711 66158000000000000000 Bool.false 878840142923171 878840142923171 562949953421312 1000000000033079 66158000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz140 0) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz140) qz98) (ep581 (@congrArg Complex Complex qz177 qz379 Complex.log (BSN.w_shift_mk qz140 Bool.false 51734 1000 0 qz141 rfl)) (@Enclosure.Complex.IsNear.of_parts qz377 Bool.false 29300548136469679 9007199254740992 500000000297711 66158000000000000000 Bool.false 878840142923171 562949953421312 1000000000033079 66158000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz377) (@HMul.hMul Real Real Real qz0 qz76 (Real.log (Enclosure.sfrac Bool.false 10706627024 16000000))) Bool.false 29300548136469679 9007199254740992 500000000297711 66158000000000000000 (Enclosure.clog_re_eq 1000 103468 4000 10706627024 16000000 rfl rfl rfl) (ep586 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz377) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz378 qz329)) Bool.false 878840142923171 562949953421312 1000000000033079 66158000000000000000 (Enclosure.clog_im_eq 1000 103468 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz378 qz329)) (@HSub.hSub Real Real Real qz52 qz77 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz329 qz378))) Bool.false 878840142923171 562949953421312 1000000000033079 66158000000000000000 (BSN.arctan_recip 103468 1000 rfl rfl) ep588)))) rfl rfl

noncomputable abbrev qz380 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz161))

noncomputable def ep590 := @Enclosure.Complex.IsNear.of_eq qz175 qz380 Bool.false 29310632719680687 9007199254740992 500000000297711 66158000000000000000 Bool.false 857096870987171 562949953421312 1000000000033079 66158000000000000000

noncomputable def ep591 := nat_lit 1923166901847548972091675739987431103856640

noncomputable def ep592 := nat_lit 11662603003873185020415355424842103390208

noncomputable def ep593 := nat_lit 124599657964249720073846538329228771328

noncomputable def ep594 := BSN.log_dyadic_bound 2538627024 18922627024 3 2 ep591 262144 66158 ep592 ep593 70764 21461254048 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2538627024) (BSN.artanhQ 18922627024) 0 2 ep592 ep591 ep593 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep595 := @Enclosure.Real.IsNear.mulLit_ff qz76 (Real.log (Enclosure.sfrac Bool.false 10730627024 16000000)) 1 2 0 1 29310632719680687 4503599627370496 500000000297711 33079000000000000000 29310632719680687 9007199254740992 500000000297711 66158000000000000000 qz318 (BSN.isNear_log_sfrac 10730627024 16000000 29310632719680687 4503599627370496 500000000297711 33079000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10730627024) qz319)) Bool.false 61468852029343792103424 9444732965739290427392 1000000000595422 66158000000000000000 29310632719680687 4503599627370496 500000000297711 33079000000000000000 (BSN.log_rat_reduce_isNear 10730627024 16000000 9 21461254048 16384000000 70764 262144 24973259072661432 36028797018963968 66158 1000000000000000 rfl rfl rfl rfl (ep594 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep596 := BSN.arctan_dyadic_bound_f 5000 103468 1 0 262144 66158 0 1 1 0 1 1 12658 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 103468) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 103468) 0 0 rfl) rfl rfl rfl

noncomputable def ep597 := @Enclosure.Real.IsNear.subLit_ff_p qz77 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz333 qz378)) 884279719003555 562949953421312 1 2000000000000000 12658 262144 1 66158 224682802148060954624 857096870987171 562949953421312 1000000000033079 66158000000000000000 qz78 (ep596 rfl) rfl rfl

noncomputable abbrev qz178 := (@HAdd.hAdd Complex Complex Complex qz260 qz365 qz324)

noncomputable abbrev qz381 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz161)

noncomputable def ep598 := @ep576 29310632719680687 9007199254740992 500000000297711 66158000000000000000 Bool.false 857096870987171 562949953421312 1000000000033079 66158000000000000000 Bool.false ep577 29305590428075183 4503599627370496 500000000297711 33079000000000000000 Bool.false ep578 867968506955171 281474976710656 1000000000033079 33079000000000000000 (ep579 (BSN.log_sum_c_succ qz140 0 1 rfl) (ep589 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep590 (@congrArg Complex Complex qz178 qz381 Complex.log (BSN.w_shift_mk qz140 Bool.false 51734 1000 1 qz141 rfl)) (@Enclosure.Complex.IsNear.of_parts qz380 Bool.false 29310632719680687 9007199254740992 500000000297711 66158000000000000000 Bool.false 857096870987171 562949953421312 1000000000033079 66158000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz380) (@HMul.hMul Real Real Real qz0 qz76 (Real.log (Enclosure.sfrac Bool.false 10730627024 16000000))) Bool.false 29310632719680687 9007199254740992 500000000297711 66158000000000000000 (Enclosure.clog_re_eq 5000 103468 4000 10730627024 16000000 rfl rfl rfl) (ep595 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz380) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz378 qz333)) Bool.false 857096870987171 562949953421312 1000000000033079 66158000000000000000 (Enclosure.clog_im_eq 5000 103468 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz378 qz333)) (@HSub.hSub Real Real Real qz52 qz77 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz333 qz378))) Bool.false 857096870987171 562949953421312 1000000000033079 66158000000000000000 (BSN.arctan_recip 103468 5000 rfl rfl) ep597)))) rfl rfl

noncomputable def ep599 := @ep499 ep494 Bool.false 29305590428075183 4503599627370496 500000000297711 33079000000000000000 Bool.false 867968506955171 281474976710656 1000000000033079 33079000000000000000 Bool.true ep500 182513682660249350523 4503599627370496000 116732766817190150591453 ep173 Bool.false ep501 1564150552831815418607 27021597764222976000 410039808695143778785337 ep494 (@ep502 4503599627370496000 112636766814751302079453 ep173 Bool.false 1647475529499511834607 27021597764222976000 360887808693517879777337 ep494 (BSN.logGammaStirling_unfold 1 qz153) (ep573 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep574 1000000000033079 33079000000000000000 (BSN.log_sum_c_eq qz140 2) (ep575 (BSN.log_sum_c_succ qz140 1 2 rfl) (ep598 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz179 := (@HDiv.hDiv Real Real Real qz257 qz354 (2 : Real))

noncomputable def ep600 := @Enclosure.Real.IsNear.mulLit_ff qz179 (Real.log Real.pi) 51734 2000 0 1 75021 65536 1 65536 1940568207 65536000 25867 65536000 (@Enclosure.Real.IsNear.of_eq qz179 (Enclosure.sfrac Bool.false 51734 2000) Bool.false 51734 2000 0 1 (BSN.t_half_eq qz140 Bool.false 51734 1000 qz141) (Enclosure.Real.IsNear.const Bool.false 51734 2000)) EMRow10.d5 rfl

noncomputable def ep601 := @ep496 25867 65536000 ep497 152804312459693804899 5404319552844595200 1051780678445143778785337 ep494 (@ep498 410039808695143778785337 ep494 (ep599 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep600 rfl rfl

noncomputable def ep602 := BSN.cos_dyadic_bound_f 75814 536870912 1 0 262144 66223 0 1 1 0 1 1 262143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 75814) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 75814) qz275 0 0 rfl) rfl rfl

noncomputable def ep603 := @ep493 262144 Bool.true 262143 262144 1 33079 (@ep495 463249 16384 171 262144 ep601 rfl) (Enclosure.sfrac_false_div 463249 16384) (BSN.cos_reduce2 qz366 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 333435313395335168) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 262143 262144 4 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q2 463249 16384 226375608064910080 72057594037927936 4 333435313395335168 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 262143 262144 333435313395335168 2361183241434822606848 75814 536870912 66223 66158 (ep602 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep604 := nat_lit 85168099569336742291896313

noncomputable def ep605 := nat_lit 12549281338544849820844032000

noncomputable abbrev qz180 := qz353

noncomputable abbrev qz443 := (@Nat.cast Complex Complex.instNatCast 11)

noncomputable abbrev qz382 := (@HPow.hPow Complex Complex Complex qz424 qz443 qz439)

noncomputable abbrev qz181 := qz382

noncomputable abbrev qz383 := qz443

noncomputable abbrev qz182 := (@HAdd.hAdd Complex Complex Complex qz260 (@HDiv.hDiv Complex Complex Complex qz309 qz383 (@HSub.hSub Complex Complex Complex qz302 qz352 (1 : Complex))) qz308)

noncomputable abbrev qz183 := qz383

noncomputable def ep606 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz131 1 11) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 11, @HPow.hPow Complex Complex Complex qz104 (@Nat.cast Complex Complex.instNatCast n) qz180) (@HMul.hMul Complex Complex Complex qz51 qz181 (@HAdd.hAdd Complex Complex Complex qz5 qz182 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))))) Bool.false 211875787073018563664633 101166148420809575628800 ep490

noncomputable def ep607 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 11, @HPow.hPow Complex Complex Complex qz104 (@Nat.cast Complex Complex.instNatCast n) qz180) (@HMul.hMul Complex Complex Complex qz51 qz181 (@HAdd.hAdd Complex Complex Complex qz5 qz182 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))))) Bool.false 74026602377 34359738368 458273502999 71036611592192

noncomputable def ep608 := nat_lit 528390793201888413509222400

noncomputable def ep609 := nat_lit 660488491502360516886528000

noncomputable def ep610 := nat_lit 7279996610342994359523941174738944

noncomputable def ep611 := nat_lit 4867559194725548413357259751424

noncomputable def ep612 := @ep607 Bool.true 5965507205 34359738368 3669236220763 568292892737536 Bool.true 6082398840716416248567 101166148420809575628800 173797525482459610228223 ep608 Bool.false 856311330160462840007 5748076614818725888000 218025828005205949319227 ep609 Bool.false ep610 211875787073018563664633 101166148420809575628800 ep490 ep491 Bool.true ep611 141664617541407596243 5748076614818725888000

noncomputable def ep613 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 11, @HPow.hPow Complex Complex Complex qz104 (@Nat.cast Complex Complex.instNatCast n) qz180) (BSN.headSumC qz131 11) Bool.false 74026602377 34359738368 458273502999 71036611592192 Bool.true 5965507205 34359738368 3669236220763

noncomputable abbrev qz184 := (BSN.headSumC qz352 10)

noncomputable abbrev qz185 := (@HPow.hPow Complex Complex Complex qz261 qz336 qz353)

noncomputable def ep614 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz131 11) (@HAdd.hAdd Complex Complex Complex qz5 qz184 qz185) Bool.false 74026602377 34359738368 458273502999 71036611592192 Bool.true 5965507205 34359738368 3669236220763 568292892737536

noncomputable def ep615 := @Enclosure.Complex.IsNear.addLitP qz184 qz185 Bool.false 127046690469 68719476736 13507601309499 2273171570950144 Bool.true 17495143947 68719476736 13525956185019 2273171570950144 Bool.false

noncomputable abbrev qz186 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 9) qz353)

noncomputable def ep616 := @Enclosure.Complex.IsNear.of_eq qz184 (@HAdd.hAdd Complex Complex Complex qz5 qz130 qz186) Bool.false 127046690469 68719476736 13507601309499 2273171570950144 Bool.true 17495143947 68719476736 13525956185019 2273171570950144

noncomputable def ep617 := @Enclosure.Complex.IsNear.addLitP qz130 qz186 Bool.false 107809588557 68719476736 12289412962325 2273171570950144 Bool.true 632483307 8589934592 3077585685071 568292892737536 Bool.false

noncomputable abbrev qz187 := (@HMul.hMul Real Real Real qz254 qz354 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep618 := @Enclosure.Complex.IsNear.of_eq qz186 (Complex.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz187)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz187)))) Bool.false 2404637739 8589934592 609094173587 1136585785475072 Bool.true 12435277491 68719476736 1215613444735 2273171570950144 (BSN.cpow_neg_s_mk qz140 51734 1000 9 qz141 rfl)

noncomputable def ep619 := @Enclosure.Real.IsNear.mulLit_ff qz140 qz114 51734 1000 0 1 9895417793173221 4503599627370496 1000000000099237 33079000000000000000 255964772056011707607 2251799813685248000 25867000002566963479 16539500000000000000000 qz142 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000099237 33079000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false 10376097607894403383296 4722366482869645213696 1000000000099237 33079000000000000000 9895417793173221 4503599627370496 1000000000099237 33079000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 15438 131072 24973259072661432 36028797018963968 33079 1000000000000000 rfl rfl rfl rfl (ep308 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep620 := nat_lit 9009343338737907752714235261396961

noncomputable def ep621 := BSN.cos_dyadic_bound_f 308086937 536870912 2 1 262144 66223 ep620 ep61 ep620 ep620 ep62 ep620 220152 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 308086937) qz274 0 1 ep620 ep61 ep620 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 308086937) qz275 0 1 ep620 ep62 ep620 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz384 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29798221) qz27)

noncomputable def ep622 := @Enclosure.Real.IsNear.cos_image qz187 qz384 Bool.false 29798221 262144 411 262144 Bool.false 220152 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz187 Bool.false 255964772056011707607 2251799813685248000 25867000002566963479 16539500000000000000000 29798221 262144 411 262144 (ep619 rfl) rfl) (Enclosure.sfrac_false_div 29798221 262144) (BSN.cos_reduce0 qz384 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21679690900037301174272) qz30) 226375608064910080 72057594037927936 Bool.false 220152 262144 18 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 29798221 262144 226375608064910080 72057594037927936 18 21679690900037301174272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 220152 262144 21679690900037301174272 37778931862957161709568 308086937 536870912 66223 66158 (ep621 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep623 := BSN.sin_dyadic_bound_f 308086937 536870912 2 1 262144 66223 ep620 ep57 ep620 ep620 ep58 ep620 142311 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 308086937) qz269 0 1 ep620 ep57 ep620 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 308086937) qz270 0 1 ep620 ep58 ep620 rfl rfl rfl rfl) rfl rfl

noncomputable def ep624 := @Enclosure.Real.IsNear.sin_image qz187 qz384 Bool.false 29798221 262144 411 262144 Bool.false 142311 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz187 Bool.false 255964772056011707607 2251799813685248000 25867000002566963479 16539500000000000000000 29798221 262144 411 262144 (ep619 rfl) rfl) (Enclosure.sfrac_false_div 29798221 262144) (BSN.sin_reduce0 qz384 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21679690900037301174272) qz30) 226375608064910080 72057594037927936 Bool.false 142311 262144 18 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q0 29798221 262144 226375608064910080 72057594037927936 18 21679690900037301174272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 142311 262144 21679690900037301174272 37778931862957161709568 308086937 536870912 66223 66158 (ep623 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep625 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz187)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz187))) Bool.false 2404637739 8589934592 609094173587 1136585785475072 Bool.true 12435277491 68719476736 1215613444735 2273171570950144 (@Enclosure.Real.IsNear.mulLit_ff qz112 (Real.cos qz187) 87381 262144 1 262144 27519 32768 13857613 8671461376 2404637739 8589934592 609094173587 1136585785475072 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz187) Bool.false 220152 262144 13857613 8671461376 27519 32768 13857613 8671461376 (ep622 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz112 (@Neg.neg Real Real.instNeg (Real.sin qz187)) 87381 262144 1 262144 142311 262144 13857613 8671461376 12435277491 68719476736 1215613444735 2273171570950144 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz187) Bool.false 142311 262144 13857613 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz187) Bool.false 142311 262144 13857613 8671461376 142311 262144 13857613 8671461376 (ep624 rfl rfl) rfl)) rfl)

noncomputable def ep626 := @ep617 2404637739 8589934592 609094173587 1136585785475072 Bool.true 12435277491 68719476736 1215613444735 2273171570950144 Bool.false 1091322761258779803648 127046690469 68719476736 13507601309499 2273171570950144 Bool.true 150282142182354714624 17495143947 68719476736 13525956185019 2273171570950144 EMRow10.d10 (ep618 ep625) rfl rfl

noncomputable abbrev qz188 := (@HMul.hMul Real Real Real qz254 qz354 qz346)

noncomputable def ep627 := @Enclosure.Complex.IsNear.of_eq qz185 (Complex.mk (@HMul.hMul Real Real Real qz0 qz118 (Real.cos qz188)) (@HMul.hMul Real Real Real qz0 qz118 (@Neg.neg Real Real.instNeg (Real.sin qz188)))) Bool.false 21006514285 68719476736 1157150786469 2273171570950144 Bool.false 5564129537 68719476736 1150988698033 2273171570950144 (BSN.cpow_neg_s_mk qz140 51734 1000 10 qz141 rfl)

noncomputable def ep628 := @Enclosure.Real.IsNear.mulLit_ff qz140 qz121 51734 1000 0 1 10369891420296933 4503599627370496 1000000000099237 33079000000000000000 268237981368820765911 2251799813685248000 25867000002566963479 16539500000000000000000 qz142 (BSN.isNear_log_sfrac 10 1 10369891420296933 4503599627370496 1000000000099237 33079000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz347 Bool.false 10873619265929276817408 4722366482869645213696 1000000000099237 33079000000000000000 10369891420296933 4503599627370496 1000000000099237 33079000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 29247 131072 24973259072661432 36028797018963968 33079 1000000000000000 rfl rfl rfl rfl (ep325 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep629 := nat_lit 61876069255385930657447954568942620694613894270751587859929271778672640000

noncomputable def ep630 := nat_lit 60544201694743786646679112343518018825922383854293172446927257600000000

noncomputable def ep631 := nat_lit 161958347913743090353030971974864977407794420182871017353948305765171200000

noncomputable def ep632 := BSN.sin_dyadic_bound_f 704302240 536870912 3 2 262144 66223 ep629 ep90 ep630 ep631 ep92 ep630 253405 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 704302240) qz269 0 2 ep629 ep90 ep630 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 704302240) qz270 0 2 ep631 ep92 ep630 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz385 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15613505) qz115)

noncomputable def ep633 := @Enclosure.Real.IsNear.cos_image qz188 qz385 Bool.false 15613505 131072 411 262144 Bool.false 253405 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz188 Bool.false 268237981368820765911 2251799813685248000 25867000002566963479 16539500000000000000000 15613505 131072 411 262144 (ep628 rfl) rfl) (Enclosure.sfrac_false_div 15613505 131072) (BSN.cos_reduce3 qz385 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24780432077023986319360) qz341) 226375608064910080 72057594037927936 Bool.false 253405 262144 18 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q3 15613505 131072 226375608064910080 72057594037927936 18 24780432077023986319360 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 253405 262144 24780432077023986319360 18889465931478580854784 704302240 536870912 66223 66158 (ep632 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep634 := nat_lit 34402502564856514270425165477120797283152573432130567998826007547084800000

noncomputable def ep635 := nat_lit 103086419291180055237982138206675355811805875528683117651584168126054400000

noncomputable def ep636 := BSN.cos_dyadic_bound_f 704302240 536870912 3 2 262144 66223 ep634 ep83 ep630 ep635 ep86 ep630 67121 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 704302240) qz274 0 2 ep634 ep83 ep630 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 704302240) qz275 0 2 ep635 ep86 ep630 rfl rfl rfl rfl) rfl rfl

noncomputable def ep637 := @Enclosure.Real.IsNear.sin_image qz188 qz385 Bool.false 15613505 131072 411 262144 Bool.true 67121 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz188 Bool.false 268237981368820765911 2251799813685248000 25867000002566963479 16539500000000000000000 15613505 131072 411 262144 (ep628 rfl) rfl) (Enclosure.sfrac_false_div 15613505 131072) (BSN.sin_reduce3 qz385 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24780432077023986319360) qz341) 226375608064910080 72057594037927936 Bool.false 67121 262144 18 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q3 15613505 131072 226375608064910080 72057594037927936 18 24780432077023986319360 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67121 262144 24780432077023986319360 18889465931478580854784 704302240 536870912 66223 66158 (ep636 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep638 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz118 (Real.cos qz188)) (@HMul.hMul Real Real Real qz0 qz118 (@Neg.neg Real Real.instNeg (Real.sin qz188))) Bool.false 21006514285 68719476736 1157150786469 2273171570950144 Bool.false 5564129537 68719476736 1150988698033 2273171570950144 (@Enclosure.Real.IsNear.mulLit_ff qz118 (Real.cos qz188) 82897 262144 1 262144 253405 262144 13857613 8671461376 21006514285 68719476736 1157150786469 2273171570950144 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz188) Bool.false 253405 262144 13857613 8671461376 253405 262144 13857613 8671461376 (ep633 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz118 (@Neg.neg Real Real.instNeg (Real.sin qz188)) 82897 262144 1 262144 67121 262144 13857613 8671461376 5564129537 68719476736 1150988698033 2273171570950144 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz188) Bool.true 67121 262144 13857613 8671461376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz188) Bool.true 67121 262144 13857613 8671461376 67121 262144 13857613 8671461376 (ep637 rfl rfl) rfl)) rfl)

noncomputable def ep639 := @ep615 21006514285 68719476736 1157150786469 2273171570950144 Bool.false 5564129537 68719476736 1150988698033 2273171570950144 Bool.false 10174138759782747602944 74026602377 34359738368 458273502999 71036611592192 Bool.true 819893067184875765760 5965507205 34359738368 3669236220763 568292892737536 (ep616 (BSN.head_sum_c_succ qz131 9 10 rfl rfl) (ep626 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep627 ep638) rfl rfl

noncomputable def ep640 := @Enclosure.Complex.IsNear.mul qz181 (@HAdd.hAdd Complex Complex Complex qz5 qz182 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))) Bool.true 6082398840716416248567 101166148420809575628800 173797525482459610228223 ep608 Bool.false

noncomputable abbrev qz189 := (Complex.re qz382)

noncomputable abbrev qz190 := (Complex.im qz382)

noncomputable def ep641 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz189 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz182 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz190 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz182 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))))) 6172011067626253183 1011661484208095756288 1277820228659656871671

noncomputable def ep642 := nat_lit 5283907932018884135092224

noncomputable def ep643 := nat_lit 6153328638744770671991141180410561661239296

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_tf qz189 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz182 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))))) 208900077 17179869184 14416518983 29910152249344 88635837137

noncomputable abbrev qz386 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz440 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable abbrev qz191 := (Real.cos qz386)

noncomputable abbrev qz192 := (@Neg.neg Real Real.instNeg (Real.sin qz386))

noncomputable abbrev qz387 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

noncomputable def ep645 := @Enclosure.Complex.IsNear.of_eq qz181 (Complex.mk (@HMul.hMul Real Real Real qz0 qz387 qz191) (@HMul.hMul Real Real Real qz0 qz387 qz192)) Bool.true 208900077 17179869184 14416518983 29910152249344 Bool.false 10351342635 34359738368 29051845105 59820304498688 (BSN.cpow_neg_s_mk qz140 51734 1000 11 qz141 rfl)

noncomputable abbrev qz388 := (Real.sqrt (@Nat.cast Real Real.instNatCast 11))

noncomputable abbrev qz389 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11) qz26)

noncomputable def ep646 := @Enclosure.Real.IsNear.inv_image qz388 869433 262144 1 262144 39519 39520 131072 (@Enclosure.Real.IsNear.of_eq qz388 (Real.sqrt qz389) Bool.false 869433 262144 1 262144 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz389) Bool.false 869433 262144 1 262144 869433 262144 1 262144 (BSN.sqrt_enclosure 11 1 434716 434717 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep647 := BSN.log_dyadic_bound 3 19 3 2 1954815 131072 33079 16488 243 41740 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 19) 0 2 16488 1954815 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz390 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz193 := qz390

noncomputable def ep648 := @Enclosure.Real.IsNear.mulLit_ff qz140 qz193 51734 1000 0 1 10799147631728357 4503599627370496 1000000000099237 33079000000000000000 279341551789917410519 2251799813685248000 25867000002566963479 16539500000000000000000 qz142 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 1000000000099237 33079000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz389) Bool.false 11323727027087193669632 4722366482869645213696 1000000000099237 33079000000000000000 10799147631728357 4503599627370496 1000000000099237 33079000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 41740 131072 24973259072661432 36028797018963968 33079 1000000000000000 rfl rfl rfl rfl (ep647 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep649 := nat_lit 63821095259460165875020912777042244907225308373735265798523531694437376256

noncomputable def ep650 := nat_lit 207739487192423230292277722859917619651021578283524626462054462277099776

noncomputable def ep651 := nat_lit 191047806803995651164478182885406899482373881964638748142646486158757929216

noncomputable def ep652 := BSN.cos_dyadic_bound_f 821655718 536870912 3 2 262144 66223 ep649 ep83 ep650 ep651 ep86 ep650 10572 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 821655718) qz274 0 2 ep649 ep83 ep650 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 821655718) qz275 0 2 ep651 ep86 ep650 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz194 := qz386

noncomputable abbrev qz391 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8129909) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep653 := @Enclosure.Real.IsNear.cos_image qz194 qz391 Bool.false 8129909 65536 411 262144 Bool.true 10572 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 279341551789917410519 2251799813685248000 25867000002566963479 16539500000000000000000 8129909 65536 411 262144 (ep648 rfl) rfl) (Enclosure.sfrac_false_div 8129909 65536) (BSN.cos_reduce2 qz391 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14454720263521470251008) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 10572 262144 19 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q2 8129909 65536 226375608064910080 72057594037927936 19 14454720263521470251008 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 10572 262144 14454720263521470251008 9444732965739290427392 821655718 536870912 66223 66158 (ep652 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep654 := nat_lit 114711779877274359990803820820388106737284737810096658736172713480165597440

noncomputable def ep655 := nat_lit 300099273842168924269727271549719460546786945042556018723323304271032688896

noncomputable def ep656 := BSN.sin_dyadic_bound_f 821655718 536870912 3 2 262144 66223 ep654 ep90 ep650 ep655 ep92 ep650 261930 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 821655718) qz269 0 2 ep654 ep90 ep650 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 821655718) qz270 0 2 ep655 ep92 ep650 rfl rfl rfl rfl) rfl rfl

noncomputable def ep657 := @Enclosure.Real.IsNear.sin_image qz194 qz391 Bool.false 8129909 65536 411 262144 Bool.true 261930 262144 1 33079 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 279341551789917410519 2251799813685248000 25867000002566963479 16539500000000000000000 8129909 65536 411 262144 (ep648 rfl) rfl) (Enclosure.sfrac_false_div 8129909 65536) (BSN.sin_reduce2 qz391 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14454720263521470251008) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 261930 262144 19 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q2 8129909 65536 226375608064910080 72057594037927936 19 14454720263521470251008 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 261930 262144 14454720263521470251008 9444732965739290427392 821655718 536870912 66223 66158 (ep656 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz195 := (Real.sin qz386)

noncomputable def ep658 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz387 qz191) (@HMul.hMul Real Real Real qz0 qz387 qz192) Bool.true 208900077 17179869184 14416518983 29910152249344 Bool.false 10351342635 34359738368 29051845105 59820304498688 (@Enclosure.Real.IsNear.mulLit_ft qz387 qz191 79039 262144 1 262144 2643 65536 13857613 8671461376 208900077 17179869184 14416518983 29910152249344 (@Enclosure.Real.IsNear.recentre' qz387 Bool.false 79039 262144 1 262144 79039 262144 1 262144 (ep646 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz191 Bool.true 10572 262144 13857613 8671461376 2643 65536 13857613 8671461376 (ep653 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz387 qz192 79039 262144 1 262144 130965 131072 13857613 8671461376 10351342635 34359738368 29051845105 59820304498688 (@Enclosure.Real.IsNear.recentre' qz387 Bool.false 79039 262144 1 262144 79039 262144 1 262144 (ep646 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz195 Bool.true 130965 131072 13857613 8671461376 (@Enclosure.Real.IsNear.recentre' qz195 Bool.true 261930 262144 13857613 8671461376 130965 131072 13857613 8671461376 (ep657 rfl rfl) rfl)) rfl)

noncomputable def ep659 := @ep644 176659345896 0 1 6172011067626253183 1011661484208095756288 1277820228659656871671 ep642 (@Enclosure.Complex.IsNear.re_isNear qz181 Bool.true 208900077 17179869184 14416518983 29910152249344 Bool.false 10351342635 34359738368 29051845105 59820304498688 (ep645 ep658))

noncomputable def ep660 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz182 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))) Bool.false 88635837137 176659345896 0 1 Bool.false

noncomputable def ep661 := @Enclosure.Complex.IsNear.addLitP qz182 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) Bool.false 666414189 1338328378 0 1 Bool.true 142268500

noncomputable def ep662 := @ep661 669164189 0 1 Bool.false 1 264 0 1 Bool.false 25867 66000 0 1 Bool.false 177271674274 88635837137 176659345896 0 1 Bool.false 7919549076863 7919549076863 44164836474000 0 1

noncomputable abbrev qz196 := (@HDiv.hDiv Complex Complex Complex qz309 qz383 (@HSub.hSub Complex Complex Complex qz302 qz352 (1 : Complex)))

noncomputable def ep663 := @Enclosure.Complex.IsNear.addLitP qz196 qz81 Bool.true 22000000 10706627024 0 1 Bool.true 2276296000 10706627024 0 1

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq qz196 (Complex.mk (Enclosure.sfrac Bool.true 22000000 10706627024) (Enclosure.sfrac Bool.true 2276296000 10706627024)) Bool.true 22000000 10706627024 0 1 Bool.true 2276296000 10706627024 0 1

noncomputable def ep665 := @ep663 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 10662627024 666414189 1338328378 0 1 Bool.true 2276296000 142268500 669164189 0 1 (ep664 (BSN.N_div_s_sub_one_mk qz140 51734 1000 11 qz141 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 22000000 10706627024) (Enclosure.sfrac Bool.true 2276296000 10706627024) Bool.true 22000000 10706627024 0 1 Bool.true 2276296000 10706627024 0 1 (Enclosure.Real.IsNear.const Bool.true 22000000 10706627024) (Enclosure.Real.IsNear.const Bool.true 2276296000 10706627024))) qz82 rfl

noncomputable abbrev qz392 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz436 qz443 1))

noncomputable abbrev qz197 := qz392

noncomputable def ep666 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) qz197)) Bool.false 1 264 0 1

noncomputable def ep667 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) qz197) Bool.false 0 1 0 1 Bool.false

noncomputable def ep668 := @ep667 0 1 0 1 Bool.false 1 264 0 1 Bool.false 25867 66000 0 1 Bool.false 1 1 264 0 1 Bool.false 25867 25867 66000 0

noncomputable def ep669 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false

noncomputable def ep670 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) qz197 Bool.false 1 264 0 1 Bool.false 25867 66000 0 1

noncomputable abbrev qz198 := (Complex.re qz392)

noncomputable abbrev qz199 := (Complex.im qz392)

noncomputable def ep671 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199) 1 264 0 1 0 1 0

noncomputable def ep672 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198 1 24 0 1 1 11 0 1 1

noncomputable def ep673 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep674 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep675 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)) qz131 Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 (BSN.ascPochhammer_one_eval qz131)

noncomputable def ep676 := ep675 (@Enclosure.Complex.IsNear.of_eq qz131 (Complex.mk qz76 qz140) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 (BSN.s_crit_mk qz140 Bool.false 51734 1000 qz141) (@Enclosure.Complex.IsNear.mk qz76 qz140 Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 qz318 qz142))

noncomputable def ep677 := @ep674 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep676)

noncomputable def ep678 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 51734 1000 0 1 0 1 0

noncomputable def ep679 := @ep678 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep676)

noncomputable def ep680 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)))) 25867 6000 0 1 0 1 0 1 25867

noncomputable def ep681 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 51734 1000 0 1 25867 6000 0

noncomputable def ep682 := @ep681 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep676)

noncomputable def ep683 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep684 := @ep683 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep676)

noncomputable def ep685 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 25867 6000 0 1 (@ep673 1 24 0 1 (ep677 rfl) (ep679 rfl) rfl rfl) (@ep680 25867 6000 0 1 (ep682 rfl) (ep684 rfl) rfl rfl)

noncomputable def ep686 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 25867 6000 0 1 ep685

noncomputable abbrev qz200 := (@Enclosure.Complex.IsNear.of_eq qz392 (Complex.mk (Enclosure.sfrac Bool.false 1 11) qz265) Bool.false 1 11 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 11 1 11 EMRow10.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 11) qz265 Bool.false 1 11 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 11) qz277))

noncomputable def ep687 := @ep672 264 0 1 ep686 (@Enclosure.Complex.IsNear.re_isNear qz197 Bool.false 1 11 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep688 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199 25867 6000 0 1 0 1 0 1 0

noncomputable def ep689 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 25867 6000 0 1 ep685

noncomputable def ep690 := @ep688 1 0 1 ep689 (@Enclosure.Complex.IsNear.im_isNear qz197 Bool.false 1 11 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep691 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198) 0 1 0 1 25867 66000 0

noncomputable def ep692 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199 1 24 0 1 0 1 0 1 0

noncomputable def ep693 := @ep692 1 0 1 ep686 (@Enclosure.Complex.IsNear.im_isNear qz197 Bool.false 1 11 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep694 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz83)) ↑qz125) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198 25867 6000 0 1 1 11 0 1 25867

noncomputable def ep695 := @ep694 66000 0 1 ep689 (@Enclosure.Complex.IsNear.re_isNear qz197 Bool.false 1 11 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep696 := @ep668 1 (@ep669 0 1 0 1 (BSN.bern_sum_base qz131 11) qz98) (ep670 (@ep671 1 1 1 264 0 1 (ep687 rfl) (ep690 rfl) rfl rfl) (@ep691 1 25867 25867 66000 0 1 (ep693 rfl) (ep695 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep697 := ep662 (ep665 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep666 Bool.false 25867 66000 0 1 (BSN.bern_sum_succ qz131 11 0 1 1 rfl rfl) (ep696 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep698 := @Enclosure.Real.IsNear.mulLit_ff qz190 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz182 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))))) 10351342635 34359738368 29051845105 59820304498688 7919549076863

noncomputable def ep699 := @ep698 44164836474000 0 1 5465197733953790930267 101166148420809575628800 46015502616493923061123 ep608 (@Enclosure.Complex.IsNear.im_isNear qz181 Bool.true 208900077 17179869184 14416518983 29910152249344 Bool.false 10351342635 34359738368 29051845105 59820304498688 (ep645 ep658))

noncomputable def ep700 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz182 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))) Bool.false 88635837137 176659345896 0 1 Bool.false

noncomputable def ep701 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz189 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz182 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz190 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz182 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1))))))) 551464803987319872817 252915371052023939072000 114172329603395565590329

noncomputable def ep702 := nat_lit 1320976983004721033773056000

noncomputable def ep703 := nat_lit 10567815864037768270184448

noncomputable def ep704 := nat_lit 76234152826862144287013365313833176722833408

noncomputable def ep705 := @Enclosure.Real.IsNear.mulLit_tf qz189 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz182 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))))) 208900077 17179869184 14416518983 29910152249344 7919549076863

noncomputable def ep706 := @ep705 44164836474000 0 1 551464803987319872817 252915371052023939072000 114172329603395565590329 ep702 (@Enclosure.Complex.IsNear.re_isNear qz181 Bool.true 208900077 17179869184 14416518983 29910152249344 Bool.false 10351342635 34359738368 29051845105 59820304498688 (ep645 ep658))

noncomputable def ep707 := @Enclosure.Real.IsNear.mulLit_ff qz190 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz182 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz60 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz60 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz109 qz183 (@HSub.hSub Nat Nat Nat qz108 (@HMul.hMul Nat Nat Nat qz60 2 k) 1)))))) 10351342635 34359738368 29051845105 59820304498688 88635837137

noncomputable def ep708 := @ep707 176659345896 0 1 305833306648381478665 2023322968416191512576 2575034611256130664385 ep703 (@Enclosure.Complex.IsNear.im_isNear qz181 Bool.true 208900077 17179869184 14416518983 29910152249344 Bool.false 10351342635 34359738368 29051845105 59820304498688 (ep645 ep658))

noncomputable abbrev qz393 := (ep697 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep709 := @ep640 856311330160462840007 5748076614818725888000 218025828005205949319227 ep609 (@ep641 ep642 5465197733953790930267 101166148420809575628800 46015502616493923061123 ep608 ep643 6082398840716416248567 101166148420809575628800 173797525482459610228223 ep608 (ep659 (@ep660 7919549076863 44164836474000 0 1 qz393) rfl) (ep699 (@ep700 7919549076863 44164836474000 0 1 qz393) rfl) rfl rfl) (@ep701 ep702 305833306648381478665 2023322968416191512576 2575034611256130664385 ep703 ep704 856311330160462840007 5748076614818725888000 218025828005205949319227 ep609 (ep706 (@ep700 7919549076863 44164836474000 0 1 qz393) rfl) (ep708 (@ep660 7919549076863 44164836474000 0 1 qz393) rfl) rfl rfl)

noncomputable def ep710 := @ep612 ep604 ep605 (@ep613 568292892737536 (BSN.head_sum_c_eq qz131 11) (ep614 (BSN.head_sum_c_succ qz131 10 11 rfl rfl) (ep639 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep709 rfl rfl rfl

noncomputable def ep711 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz131 1 11) Bool.false 211875787073018563664633 101166148420809575628800 ep490 ep491 Bool.true 141664617541407596243 5748076614818725888000 ep604 ep605 (@ep606 ep491 Bool.true 141664617541407596243 5748076614818725888000 ep604 ep605 (BSN.zetaApproximant_eq_folded' qz131 1 11 rfl) (ep710 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep712 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))))) qz151)) (Complex.im (zetaApproximant qz131 1 11)) 37 262144 5918653

noncomputable def ep713 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))))) qz151)) Bool.true 37 262144 5918653

noncomputable def ep714 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))))) qz151) qz366 Bool.false 463249 16384 171

noncomputable def ep715 := BSN.sin_dyadic_bound_f 75814 536870912 1 0 262144 66223 0 1 1 0 1 1 37 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 75814) qz269 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 75814) qz270 0 0 rfl) rfl rfl

noncomputable def ep716 := @ep714 262144 Bool.true 37 262144 1 33079 (@ep495 463249 16384 171 262144 ep601 rfl) (Enclosure.sfrac_false_div 463249 16384) (BSN.sin_reduce2 qz366 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 333435313395335168) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 37 262144 4 1000000000000000 66158 33079 (BSN.sin_reduce_arg_pos_rat_q2 463249 16384 226375608064910080 72057594037927936 4 333435313395335168 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 37 262144 333435313395335168 2361183241434822606848 75814 536870912 66223 66158 (ep715 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep717 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz131 1 11) Bool.false 211875787073018563664633 101166148420809575628800 ep490 ep491 Bool.true 141664617541407596243 5748076614818725888000 ep604 ep605 (@ep606 ep491 Bool.true 141664617541407596243 5748076614818725888000 ep604 ep605 (BSN.zetaApproximant_eq_folded' qz131 1 11 rfl) (ep710 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow10.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 11 qz140) Bool.true ep474 ep475 ep476 ep477 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 11 qz140) ep478 Bool.true ep474 ep475 ep476 ep477 (@Eq.refl Real ep478) (@ep479 Bool.true ep474 ep475 ep476 ep477 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz52 (Complex.im (@HSub.hSub Complex Complex Complex qz53 qz149 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz150 (@Nat.cast Complex Complex.instNatCast j))))) qz151) (zetaApproximant qz131 1 11)) (@ep481 ep482 ep483 ep484 5241590849032081060991 ep485 ep486 ep487 ep488 ep474 ep475 ep476 ep477 (@ep489 8671461376 211875787073018563664633 101166148420809575628800 ep490 ep491 ep480 ep482 ep483 ep484 (@ep492 8671461376 262143 262144 5918653 8671461376 (ep603 rfl rfl) rfl) ep711 rfl) (@ep712 8671461376 141664617541407596243 5748076614818725888000 ep604 ep605 5241590849032081060991 ep485 ep486 ep487 (@ep713 8671461376 37 262144 5918653 8671461376 (ep716 rfl rfl) rfl) ep717 rfl) rfl rfl))

theorem EMRow10.d13 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow10.d14 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow10.d15 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow10.d16 : @Eq Nat (Nat.pow 10 (Nat.succ (Nat.mul 2 3))) 10000000 := @Eq.refl Nat 10000000

noncomputable abbrev qz444 := (@HAdd.hAdd Complex Complex Complex qz447 qz446 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz394 := qz444

noncomputable abbrev qz201 := (@HDiv.hDiv Real Real Real qz257 (@Norm.norm Complex Complex.instNorm qz394) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz259) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz202 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz203 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz395 := (@HPow.hPow Complex Complex Complex qz424 qz437 (@HSub.hSub Complex Complex Complex qz430 qz425 qz426))

noncomputable abbrev qz204 := qz395

noncomputable def ep718 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) 81558121 7247757312 2954999 28991029248 99869979597047 140737488355328 1334828737

noncomputable def ep719 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 10)) 6641 442368 1 442368 12281 16384 875 131072 81558121 7247757312

noncomputable abbrev qz396 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz205 := (@HPow.hPow Real Nat Real qz396 qz258 2)

noncomputable def ep720 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz205) 96 162 0 1 6641 262144 1 262144 6641 442368 1 442368

noncomputable def ep721 := nat_lit 781950621441006189802102638025

noncomputable def ep722 := nat_lit 19807040628566084398385987584

noncomputable def ep723 := nat_lit 26986075409044041160201671

noncomputable def ep724 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz206 := qz258

noncomputable abbrev qz397 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz206 1)

noncomputable def ep725 := @Enclosure.Real.IsNear.mulLit_ff qz397 qz206 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep721 ep722 ep723 ep724

noncomputable def ep726 := ep725 (@Enclosure.Real.IsNear.of_eq qz397 qz206 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz206) (@Enclosure.Real.IsNear.of_eq qz206 qz255 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz256)) (@Enclosure.Real.IsNear.of_eq qz206 qz255 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz256) rfl

noncomputable def ep727 := @Enclosure.Real.IsNear.inv_image qz205 ep721 ep722 ep723 ep724 3320 3321 131072 (@Enclosure.Real.IsNear.of_eq qz205 (@HMul.hMul Real Real Real qz0 qz397 qz206) Bool.false ep721 ep722 ep723 ep724 (BSN.pow_succ_r qz206 1 2 rfl) ep726) rfl rfl rfl

noncomputable def ep728 := ep720 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz205) Bool.false 6641 262144 1 262144 6641 262144 1 262144 (ep727 rfl rfl rfl) rfl)

noncomputable def ep729 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 10)) (Real.sqrt (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz21 1 10)) (Complex.re (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz21 1 10)) (Complex.im (zetaApproximant qz21 1 10))))) Bool.false 12281 16384 875 131072

noncomputable def ep730 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz21 1 10)) (Complex.re (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz21 1 10)) (Complex.im (zetaApproximant qz21 1 10))))) Bool.false 196496 262144 1750 262144

noncomputable def ep731 := nat_lit 4533693398739375269978563744455844579741

noncomputable def ep732 := nat_lit 8068485650568420407963842793963520000000

noncomputable def ep733 := nat_lit 20541908233161051919453689298823937395857638724365296171

noncomputable def ep734 := nat_lit 2053981133173672687344065128515164131664827357593600000000

noncomputable def ep735 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz21 1 10)) (Complex.re (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz21 1 10)) (Complex.im (zetaApproximant qz21 1 10)))) ep731 ep732 ep733 ep734 97373 99123

noncomputable def ep736 := nat_lit 828231166157613691367619539742472610660339218369

noncomputable def ep737 := nat_lit 1495828859829847017724196804805332985446400000000

noncomputable def ep738 := nat_lit 103463705556515713034413882375956935479451336048728373641

noncomputable def ep739 := nat_lit 11639226421317478561616369061585930079434021693030400000000

noncomputable def ep740 := nat_lit 785738705363645712480435399614848235292271004689

noncomputable def ep741 := nat_lit 95733047029110209134348595507541311068569600000000

noncomputable def ep742 := nat_lit 606583176471730367616735483627127020175403908875389281

noncomputable def ep743 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz21 1 10)) (Complex.re (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz21 1 10)) (Complex.im (zetaApproximant qz21 1 10))) ep736 ep737 ep738 ep739 ep740 ep741 ep742

noncomputable def ep744 := nat_lit 545588738499256807575767299761840472473469766860800000000

noncomputable def ep745 := nat_lit 80464423812509905649509715600317926537059932603886735890243323592988552096478348970033152000000000

noncomputable def ep746 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz21 1 10)) (Complex.re (zetaApproximant qz21 1 10)) 910072066463757413664287 ep164 ep165 ep166 910072066463757413664287 ep164 ep165 ep166 ep736

noncomputable def ep747 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz21 1 10)) (Complex.im (zetaApproximant qz21 1 10)) 886419034860852766694633 ep293 ep294 ep295 886419034860852766694633 ep293 ep294 ep295 ep740

noncomputable def ep748 := @ep718 985162418487296 735311659978308139876352 2739249393263117 3799912185593856 2747263778395 26599385299156992 (@ep719 2954999 28991029248 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz205)) Bool.false 6641 442368 1 442368 (BSN.theta_err_eq 1 2 96 162 EMRow10.d13 EMRow10.d14 rfl) (ep728 rfl)) (ep729 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz21 1 10)) (@ep730 12281 16384 875 131072 (@ep735 131072 (@ep743 ep744 ep745 ep731 ep732 ep733 ep734 (@ep746 ep737 ep738 ep739 ep388 ep388 rfl) (@ep747 ep741 ep742 ep744 ep394 ep394 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz207 := (@Norm.norm Complex Complex.instNorm qz394)

noncomputable abbrev qz398 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep749 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz207 qz398) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) Bool.false 99869979597047 140737488355328 1334828737 985162418487296 (BSN.zrb_shape_eq qz207 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) qz24 3)

noncomputable def ep750 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz207 qz398) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) 12802217 917504 1 917504 54606937 1073741824 25 268435456

noncomputable def ep751 := @Enclosure.Real.IsNear.mulLit_ff qz207 qz398 12802217 262144 1 262144 2 7 0 1 12802217 917504

noncomputable abbrev qz399 := (Complex.re qz444)

noncomputable abbrev qz400 := (Complex.im qz444)

noncomputable abbrev qz208 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz254 qz399 qz399) (@HMul.hMul Real Real Real qz254 qz400 qz400))

noncomputable abbrev qz209 := qz394

noncomputable def ep752 := @Enclosure.Real.IsNear.of_eq qz207 (Real.sqrt qz208) Bool.false 12802217 262144 1 262144 (BSN.norm_eq_sqrt_mul_add qz209)

noncomputable def ep753 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz208) Bool.false 12802217 262144 1 262144 12802217

noncomputable def ep754 := @Enclosure.Real.IsNear.sqrt_image qz208 2385011521 1000000 0 1 6401108 6401109 131072

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz254 qz399 qz399)

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz254 qz400 qz400)

noncomputable def ep755 := @Enclosure.Real.IsNear.addLit_ff qz210 qz211 49 4 0 1 2372761521 1000000 0 1

noncomputable abbrev qz212 := qz399

noncomputable def ep756 := @Enclosure.Real.IsNear.mulLit_ff qz212 qz212 7 2 0 1 7 2 0 1 49 4

noncomputable def ep757 := @Enclosure.Complex.IsNear.of_eq qz209 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz24) Bool.false 7 2 0 1 Bool.false 48711 1000 0 1 (BSN.s_add_nat_mk qz24 Bool.false 48711 1000 3 qz25)

noncomputable abbrev qz213 := (ep757 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz267 Bool.false 7 2 0 1 Bool.false 48711 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz271))

noncomputable def ep758 := @ep756 0 1 (@Enclosure.Complex.IsNear.re_isNear qz209 Bool.false 7 2 0 1 Bool.false 48711 1000 0 1 qz213)

noncomputable def ep759 := ep758 (@Enclosure.Complex.IsNear.re_isNear qz209 Bool.false 7 2 0 1 Bool.false 48711 1000 0 1 qz213)

noncomputable abbrev qz214 := qz400

noncomputable def ep760 := @Enclosure.Real.IsNear.mulLit_ff qz214 qz214 48711 1000 0 1 48711 1000 0 1 2372761521 1000000

noncomputable def ep761 := @ep760 0 1 (@Enclosure.Complex.IsNear.im_isNear qz209 Bool.false 7 2 0 1 Bool.false 48711 1000 0 1 qz213)

noncomputable def ep762 := ep761 (@Enclosure.Complex.IsNear.im_isNear qz209 Bool.false 7 2 0 1 Bool.false 48711 1000 0 1 qz213)

noncomputable def ep763 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Real.sqrt (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))))) Bool.false 54606937 1073741824

noncomputable def ep764 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))))) Bool.false 109213874 2147483648

noncomputable def ep765 := nat_lit 198024013854331862380785868029089629298714879993689263437

noncomputable def ep766 := nat_lit 76563532557211154279259286672147847577600000000000000000000

noncomputable def ep767 := nat_lit 102976403943829986725753031912867135238207280192175810149757266879

noncomputable def ep768 := nat_lit 10908511334187882229601468484880951271353221120000000000000000000000000000

noncomputable def ep769 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))) ep765 ep766 ep767 ep768

noncomputable def ep770 := nat_lit 27637013828146583472544254426701301935571669433507736569

noncomputable def ep771 := nat_lit 19140883139302788569814821668036961894400000000000000000000

noncomputable def ep772 := nat_lit 60105400608620407217675291259923303387108338378231985032946608127

noncomputable def ep773 := nat_lit 87475958541745528490608850322284421556428202259658317161

noncomputable def ep774 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) ep770 ep771 ep772 ep768 ep773

noncomputable def ep775 := nat_lit 223286475704216559937904899234082457557806988614290755816722181

noncomputable def ep776 := nat_lit 56815163198895219945840981692088287871631360000000000000000000000000000

noncomputable def ep777 := nat_lit 3790354507961442554698796195269025072858889283485878225088682465628905212210463168137572175052800000000000000000000

noncomputable def ep778 := nat_lit 5257091765239273761991008587

noncomputable def ep779 := nat_lit 138350580552821637120000000000

noncomputable def ep780 := nat_lit 414759553091543690125475221141

noncomputable def ep781 := nat_lit 5720623567633483667865600000000000000

noncomputable def ep782 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) ep778 ep779 ep780 ep781 ep778 ep779 ep780

noncomputable def ep783 := nat_lit 9352858308653324642784806381

noncomputable def ep784 := nat_lit 276701161105643274240000000000

noncomputable def ep785 := nat_lit 166282977755564223153592242133

noncomputable def ep786 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204) Bool.true ep778 ep779 ep780 ep781 Bool.false ep783 ep784 ep785

noncomputable def ep787 := nat_lit 2860311783816741833932800000000000000

noncomputable def ep788 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204 Bool.true ep778 ep779 ep780 ep781 Bool.false ep783 ep784 ep785 ep787

noncomputable def ep789 := nat_lit 184467440737095516160000000

noncomputable def ep790 := nat_lit 27472036618305782684348777

noncomputable def ep791 := nat_lit 5720623567633483667865600000000000

noncomputable def ep792 := nat_lit 5641715528094306705741943337

noncomputable def ep793 := nat_lit 387287516473237907441126444141

noncomputable abbrev qz215 := (Complex.re qz395)

noncomputable abbrev qz216 := (Complex.im qz395)

noncomputable def ep794 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216) 512831683806710591667913 ep789 ep790 ep791 ep792 ep779 ep793

noncomputable def ep795 := nat_lit 969762263653748586533178696560214743713757265920000000

noncomputable def ep796 := nat_lit 11917965765903090974720000

noncomputable def ep797 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215 7117034563 480000000 0 1 216170799481353 1152921504606846976 3860039792574179 ep796 512831683806710591667913

noncomputable def ep798 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) 7117034563 480000000 0 1 0 1 0 1 7117034563

noncomputable def ep799 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 21351103689 2000000 0 1 7117034563 480000000 0

noncomputable def ep800 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz20) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow10.d15 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz20 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz31)

noncomputable abbrev qz401 := (@HAdd.hAdd Complex Complex Complex qz423 qz422 qz427)

noncomputable abbrev qz217 := qz401

noncomputable def ep801 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz51 (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) qz217) Bool.true 21351103689 2000000 0 1 Bool.true 115299498199431 1000000000 0 1

noncomputable abbrev qz218 := (Complex.re qz401)

noncomputable abbrev qz219 := (Complex.im qz401)

noncomputable def ep802 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz218) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz219) 2372011521 400000 0 1 2372761521 500000 0 1

noncomputable def ep803 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz218 2372011521 1000000 0 1 5 2 0 1 2372011521 400000

noncomputable abbrev qz402 := (@HAdd.hAdd Complex Complex Complex qz423 qz422 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz220 := qz402

noncomputable def ep804 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz51 (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) qz220) Bool.true 2372011521 1000000 0 1 Bool.false 48711 500 0 1

noncomputable abbrev qz221 := (Complex.re qz402)

noncomputable abbrev qz222 := (Complex.im qz402)

noncomputable def ep805 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz221) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz222) 3 4 0 1 2372761521 1000000 0 1

noncomputable def ep806 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz221 1 2 0 1 3 2 0 1 3 4

noncomputable def ep807 := @ep806 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep351)

noncomputable def ep808 := @Enclosure.Complex.IsNear.of_eq qz220 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz24) Bool.false 3 2 0 1 Bool.false 48711 1000 0 1 (BSN.s_add_nat_mk qz24 Bool.false 48711 1000 1 qz25)

noncomputable abbrev qz223 := (ep808 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz267 Bool.false 3 2 0 1 Bool.false 48711 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz271))

noncomputable def ep809 := ep807 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 3 2 0 1 Bool.false 48711 1000 0 1 qz223)

noncomputable def ep810 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz222 48711 1000 0 1 48711 1000 0 1 2372761521 1000000

noncomputable def ep811 := @ep810 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep351)

noncomputable def ep812 := ep811 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 3 2 0 1 Bool.false 48711 1000 0 1 qz223)

noncomputable def ep813 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) qz220 Bool.true 2372011521 1000000 0 1 Bool.false 48711 500 0 1 (@ep805 9488046084 2372011521 1000000 0 1 (ep809 rfl) (ep812 rfl) rfl rfl)

noncomputable def ep814 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz222) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz221) 48711 2000 0 1 146133 2000 0 1

noncomputable def ep815 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz222 1 2 0 1 48711 1000 0 1 48711 2000

noncomputable def ep816 := @ep815 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep351)

noncomputable def ep817 := ep816 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 3 2 0 1 Bool.false 48711 1000 0 1 qz223)

noncomputable def ep818 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz221 48711 1000 0 1 3 2 0 1 146133 2000

noncomputable def ep819 := @ep818 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep351)

noncomputable def ep820 := ep819 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 3 2 0 1 Bool.false 48711 1000 0 1 qz223)

noncomputable abbrev qz224 := (ep804 (BSN.ascPochhammer_succ_eval_c 1 2 qz259 rfl) (ep813 (@ep814 389688000 48711 500 0 1 (ep817 rfl) (ep820 rfl) rfl rfl)))

noncomputable def ep821 := @ep803 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2372011521 1000000 0 1 Bool.false 48711 500 0 1 qz224)

noncomputable def ep822 := @Enclosure.Complex.IsNear.of_eq qz217 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz24) Bool.false 5 2 0 1 Bool.false 48711 1000 0 1 (BSN.s_add_nat_mk qz24 Bool.false 48711 1000 2 qz25)

noncomputable abbrev qz225 := (ep822 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz267 Bool.false 5 2 0 1 Bool.false 48711 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz271))

noncomputable def ep823 := ep821 (@Enclosure.Complex.IsNear.re_isNear qz217 Bool.false 5 2 0 1 Bool.false 48711 1000 0 1 qz225)

noncomputable def ep824 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz219 48711 500 0 1 48711 1000 0 1 2372761521 500000

noncomputable def ep825 := @ep824 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2372011521 1000000 0 1 Bool.false 48711 500 0 1 qz224)

noncomputable def ep826 := ep825 (@Enclosure.Complex.IsNear.im_isNear qz217 Bool.false 5 2 0 1 Bool.false 48711 1000 0 1 qz225)

noncomputable def ep827 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) qz217 Bool.true 21351103689 2000000 0 1 Bool.true 115299498199431 1000000000 0 1 (@ep802 2135110368900000 21351103689 2000000 0 1 (ep823 rfl) (ep826 rfl) rfl rfl)

noncomputable def ep828 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz219) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz218) 115543053199431 1000000000 0 1 48711 200 0 1

noncomputable def ep829 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz219 2372011521 1000000 0 1 48711 1000 0 1 115543053199431 1000000000

noncomputable def ep830 := @ep829 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2372011521 1000000 0 1 Bool.false 48711 500 0 1 qz224)

noncomputable def ep831 := ep830 (@Enclosure.Complex.IsNear.im_isNear qz217 Bool.false 5 2 0 1 Bool.false 48711 1000 0 1 qz225)

noncomputable def ep832 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz218 48711 500 0 1 5 2 0 1 48711 200

noncomputable def ep833 := @ep832 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2372011521 1000000 0 1 Bool.false 48711 500 0 1 qz224)

noncomputable def ep834 := ep833 (@Enclosure.Complex.IsNear.re_isNear qz217 Bool.false 5 2 0 1 Bool.false 48711 1000 0 1 qz225)

noncomputable abbrev qz226 := (ep801 (BSN.ascPochhammer_succ_eval_c 2 3 qz259 rfl) (ep827 (@ep828 23059899639886200 115299498199431 1000000000 0 1 (ep831 rfl) (ep834 rfl) rfl rfl)))

noncomputable def ep835 := @ep799 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep800) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21351103689 2000000 0 1 Bool.true 115299498199431 1000000000 0 1 qz226)

noncomputable def ep836 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 115299498199431 1000000000 0 1 0 1 0

noncomputable def ep837 := @ep836 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep800) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21351103689 2000000 0 1 Bool.true 115299498199431 1000000000 0 1 qz226)

noncomputable def ep838 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) 38433166066477 240000000000 0 1 0 1 0 1 38433166066477

noncomputable def ep839 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 115299498199431 1000000000 0 1 38433166066477 240000000000 0

noncomputable def ep840 := @ep839 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep800) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21351103689 2000000 0 1 Bool.true 115299498199431 1000000000 0 1 qz226)

noncomputable def ep841 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 21351103689 2000000 0 1 0 1 0

noncomputable def ep842 := @ep841 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep800) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21351103689 2000000 0 1 Bool.true 115299498199431 1000000000 0 1 qz226)

noncomputable def ep843 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 7117034563 480000000 0 1 Bool.false 38433166066477 240000000000 0 1 (@ep798 7117034563 480000000 0 1 (ep835 rfl) (ep837 rfl) rfl rfl) (@ep838 38433166066477 240000000000 0 1 (ep840 rfl) (ep842 rfl) rfl rfl)

noncomputable def ep844 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 7117034563 480000000 0 1 Bool.false 38433166066477 240000000000 0 1 ep843

noncomputable def ep845 := nat_lit 23835931531806181949440000

noncomputable def ep846 := @Enclosure.Complex.IsNear.re_isNear qz204 Bool.false 216170799481353 1152921504606846976 3860039792574179 ep796 Bool.false 146792890243181 576460752303423488 10076908985415233 ep845

noncomputable abbrev qz403 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10000000)))

noncomputable def ep847 := @Enclosure.Complex.IsNear.of_eq qz204 (Complex.mk (@HMul.hMul Real Real Real qz0 qz403 qz119) (@HMul.hMul Real Real Real qz0 qz403 qz120)) Bool.false 216170799481353 1152921504606846976 3860039792574179 ep796 Bool.false 146792890243181 576460752303423488 10076908985415233

noncomputable abbrev qz404 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10000000))

noncomputable abbrev qz405 := (@Nat.cast Real Real.instNatCast 10000000)

noncomputable def ep848 := @Enclosure.Real.IsNear.inv_image qz404 6790939565647 2147483648 1 2147483648 339546 339547 1073741824 (@Enclosure.Real.IsNear.of_eq qz404 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz405 qz26)) Bool.false 6790939565647 2147483648 1 2147483648 (BSN.sqrt_natCast_div_one 10000000) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz405 qz26)) Bool.false 6790939565647 2147483648 1 2147483648 6790939565647 2147483648 1 2147483648 (BSN.sqrt_enclosure 10000000 1 3395469782823 3395469782824 1073741824 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep849 := nat_lit 89076946236074554071973888

noncomputable def ep850 := nat_lit 38685626227668133590597632

noncomputable def ep851 := BSN.log_dyadic_bound 2 18 5 4 10413862744320 1073741824 330790000 43175675904 26880 239598563 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 18) 0 4 43175675904 10413862744320 26880 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep852 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz121 48711 1000 0 1 10369921363433189 4503599627370496 100000099237 33079000000000000000 505129239534194069379 4503599627370496000 4871104833933507 33079000000000000000000 qz29 (BSN.isNear_log_sfrac 10 1 10369921363433189 4503599627370496 100000099237 33079000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz347 Bool.false ep849 ep850 1000000992370000 330790000000000000000000 10369921363433189 4503599627370496 100000099237 33079000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 239598563 1073741824 24973259072661432 36028797018963968 330790000 1000000000000000 rfl rfl rfl rfl (ep851 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep853 := nat_lit 3069139755037848378540032

noncomputable def ep854 := nat_lit 4835703278458516698824704

noncomputable def ep855 := nat_lit 68692878349772278780038385232515052882709012744281971383148987746815642957963859343412524911123003097345

noncomputable def ep856 := nat_lit 50797410752592599495442790923292316227798919877281851451531752809858799638366050241238301547400049385799680

noncomputable def ep857 := nat_lit 3685824948625278990866995234560969331152971093825688978166289753724815497947906227585443592494137601

noncomputable def ep858 := nat_lit 179903951961391527305543890950016801694844595234205635840377936772534938998146763575045284049029541413121

noncomputable def ep859 := nat_lit 931285863797530990749784500260359130842980197750167276611415468180744660036710921089368861702334238739660800

noncomputable def ep860 := BSN.sin_dyadic_bound_f 2791366346207 4398046511104 3 2 2147483648 662226075 ep855 ep856 ep857 ep858 ep859 ep857 1273291284 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2791366346207) (BSN.sinEvenQ 4398046511104) 0 2 ep855 ep856 ep857 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2791366346207) (BSN.sinOddQ 4398046511104) 0 2 ep858 ep859 ep857 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz406 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3763506111) (@Nat.cast Real Real.instNatCast 33554432))

noncomputable def ep861 := @Enclosure.Real.IsNear.cos_image qz122 qz406 Bool.false 3763506111 33554432 159 1073741824 Bool.false 1273291284 2147483648 1 330790000 (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 505129239534194069379 4503599627370496000 4871104833933507 33079000000000000000000 3763506111 33554432 159 1073741824 (ep852 rfl) rfl) (Enclosure.sfrac_false_div 3763506111 33554432) (BSN.cos_reduce3 qz406 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep853) (@Nat.cast Real Real.instNatCast ep854)) 226375608064910080 72057594037927936 Bool.false 1273291284 2147483648 17 1000000000000000 661580000 330790000 (BSN.sin_reduce_arg_pos_rat_q3 3763506111 33554432 226375608064910080 72057594037927936 17 ep853 ep854 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1273291284 2147483648 ep853 ep854 2791366346207 4398046511104 662226075 661580000 (ep860 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep862 := nat_lit 38164348338739543890683932682612612032318852845087239963517511543677012672423454260219218481109443559681

noncomputable def ep863 := nat_lit 5644156750288066610604754547032479580866546653031316827947972534428755515374005582359811283044449931755520

noncomputable def ep864 := nat_lit 114485673366321381114070064057368714158294252593074068512596202051523588386274466968202484556143342403841

noncomputable def ep865 := nat_lit 253987053762962997477213954616461581138994599386409257257658764049293998191830251206191507737000246928998400

noncomputable def ep866 := BSN.cos_dyadic_bound_f 2791366346207 4398046511104 3 2 2147483648 662226075 ep862 ep863 ep857 ep864 ep865 ep857 1729281736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2791366346207) (BSN.cosEvenQ 4398046511104) 0 2 ep862 ep863 ep857 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2791366346207) (BSN.cosOddQ 4398046511104) 0 2 ep864 ep865 ep857 rfl rfl rfl rfl) rfl rfl

noncomputable def ep867 := @Enclosure.Real.IsNear.sin_image qz122 qz406 Bool.false 3763506111 33554432 159 1073741824 Bool.true 1729281736 2147483648 1 330790000 (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 505129239534194069379 4503599627370496000 4871104833933507 33079000000000000000000 3763506111 33554432 159 1073741824 (ep852 rfl) rfl) (Enclosure.sfrac_false_div 3763506111 33554432) (BSN.sin_reduce3 qz406 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep853) (@Nat.cast Real Real.instNatCast ep854)) 226375608064910080 72057594037927936 Bool.false 1729281736 2147483648 17 1000000000000000 661580000 330790000 (BSN.sin_reduce_arg_pos_rat_q3 3763506111 33554432 226375608064910080 72057594037927936 17 ep853 ep854 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1729281736 2147483648 ep853 ep854 2791366346207 4398046511104 662226075 661580000 (ep866 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep868 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz403 qz119) (@HMul.hMul Real Real Real qz0 qz403 qz120) Bool.false 216170799481353 1152921504606846976 3860039792574179 ep796 Bool.false 146792890243181 576460752303423488 10076908985415233 ep845 (@Enclosure.Real.IsNear.mulLit_ff qz403 qz119 679093 2147483648 1 2147483648 318322821 536870912 3354334489 22198941122560000 216170799481353 1152921504606846976 3860039792574179 ep796 (@Enclosure.Real.IsNear.recentre' qz403 Bool.false 679093 2147483648 1 2147483648 679093 2147483648 1 2147483648 (ep848 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz119 Bool.false 1273291284 2147483648 53669351824 355183057960960000 318322821 536870912 3354334489 22198941122560000 (ep861 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz403 qz120 679093 2147483648 1 2147483648 216160217 268435456 3354334489 22198941122560000 146792890243181 576460752303423488 10076908985415233 ep845 (@Enclosure.Real.IsNear.recentre' qz403 Bool.false 679093 2147483648 1 2147483648 679093 2147483648 1 2147483648 (ep848 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz123 Bool.true 216160217 268435456 3354334489 22198941122560000 (@Enclosure.Real.IsNear.recentre' qz123 Bool.true 1729281736 2147483648 53669351824 355183057960960000 216160217 268435456 3354334489 22198941122560000 (ep867 rfl rfl) rfl)) rfl)

noncomputable def ep869 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216 38433166066477 240000000000 0 1 146792890243181 576460752303423488 10076908985415233 ep845 ep792

noncomputable def ep870 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 7117034563 480000000 0 1 Bool.false 38433166066477 240000000000 0 1 ep843

noncomputable def ep871 := @Enclosure.Complex.IsNear.im_isNear qz204 Bool.false 216170799481353 1152921504606846976 3860039792574179 ep796 Bool.false 146792890243181 576460752303423488 10076908985415233 ep845

noncomputable def ep872 := nat_lit 276701161105643274240000000

noncomputable def ep873 := nat_lit 71717709537405476167698179

noncomputable def ep874 := nat_lit 11441247135266967335731200000000000

noncomputable def ep875 := nat_lit 2769376078396646663573301127

noncomputable def ep876 := nat_lit 92233720368547758080000000000

noncomputable def ep877 := nat_lit 148353550371212854111667697383

noncomputable def ep878 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215) 1044730073463384652064903 ep872 ep873 ep874 ep875 ep876 ep877

noncomputable def ep879 := nat_lit 862648917886979283465797313036124559604428308480000000

noncomputable def ep880 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216 7117034563 480000000 0 1 146792890243181 576460752303423488 10076908985415233 ep845 1044730073463384652064903

noncomputable def ep881 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215 38433166066477 240000000000 0 1 216170799481353 1152921504606846976 3860039792574179 ep796 ep875

noncomputable abbrev qz407 := (@ep847 ep845 (BSN.cpow_neg_s_sub_mk qz24 48711 1000 10 3 10000000 qz25 rfl EMRow10.d16) ep868)

noncomputable def ep882 := ep788 (@ep794 ep781 ep795 ep778 ep779 ep780 ep781 (@ep797 ep789 ep790 ep791 ep844 (ep846 qz407) rfl) (@ep869 ep779 ep793 ep781 ep870 (ep871 qz407) rfl) rfl rfl) (@ep878 ep787 ep879 ep783 ep784 ep785 ep787 (@ep880 ep872 ep873 ep874 ep844 (ep871 qz407) rfl) (@ep881 ep876 ep877 ep787 ep870 (ep846 qz407) rfl) rfl rfl)

noncomputable def ep883 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) ep783 ep784 ep785 ep787 ep783 ep784 ep785

noncomputable def ep884 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204) Bool.true ep778 ep779 ep780 ep781 Bool.false ep783 ep784 ep785

noncomputable def ep885 := @ep750 99869979597047 140737488355328 1334828737 985162418487296 (@ep751 1 917504 (ep752 (@ep753 262144 1 262144 (ep754 (@ep755 9540046084 2385011521 1000000 0 1 (ep759 rfl) (ep762 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep763 25 268435456 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (@ep764 200 2147483648 54606937 1073741824 25 268435456 (@ep769 54606837 54607037 1073741824 (@ep774 ep766 ep775 ep776 ep777 ep765 ep766 ep767 ep768 (@ep782 ep781 ep770 ep771 ep772 ep768 (@ep786 ep787 ep882) (@ep786 ep787 ep882) rfl) (@ep883 ep787 ep773 ep766 ep775 ep776 (@ep884 ep787 ep882) (@ep884 ep787 ep882) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow10.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))) Bool.false 2739249393263117 3799912185593856 2747263778395 26599385299156992 := ep748 (ep749 ep885) rfl rfl

theorem EMRow10.d18 : @Eq Nat (Nat.pow 11 (Nat.succ (Nat.mul 2 3))) 19487171 := @Eq.refl Nat 19487171

noncomputable abbrev qz445 := (@HAdd.hAdd Complex Complex Complex qz447 qz453 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz408 := qz445

noncomputable abbrev qz227 := (@HDiv.hDiv Real Real Real qz257 (@Norm.norm Complex Complex.instNorm qz408) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz352) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz409 := (@HPow.hPow Complex Complex Complex qz424 qz443 (@HSub.hSub Complex Complex Complex qz430 qz439 qz426))

noncomputable abbrev qz228 := qz409

noncomputable def ep886 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz131 1 11))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) 3646260973 115964116992 12537863 115964116992 636850839925667 985162418487296 1446906493

noncomputable def ep887 := nat_lit 77444004586190033672732672

noncomputable def ep888 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz131 1 11)) 6641 442368 1 442368 549053 262144 1805 262144 3646260973 115964116992

noncomputable def ep889 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz131 1 11)) (Real.sqrt (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz131 1 11)) (Complex.re (zetaApproximant qz131 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz131 1 11)) (Complex.im (zetaApproximant qz131 1 11))))) Bool.false 549053 262144 1805 262144

noncomputable def ep890 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz131 1 11)) (Complex.re (zetaApproximant qz131 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz131 1 11)) (Complex.im (zetaApproximant qz131 1 11))))) Bool.false 549053 262144 1805 262144

noncomputable def ep891 := nat_lit 1677374791460984422620662319267585396829

noncomputable def ep892 := nat_lit 382364663058100072389014479437824000000

noncomputable def ep893 := nat_lit 72635247278647963142368539365559362625221547265291890611

noncomputable def ep894 := nat_lit 2519751393823200281948130715197174492276173920272384000000

noncomputable def ep895 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz131 1 11)) (Complex.re (zetaApproximant qz131 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz131 1 11)) (Complex.im (zetaApproximant qz131 1 11)))) ep891 ep892 ep893 ep894 273624 275429

noncomputable def ep896 := nat_lit 44891349147811100289439152521988062606495024689

noncomputable def ep897 := nat_lit 10234589586301271792841446665690746915389440000

noncomputable def ep898 := nat_lit 2867050917557109014747146394103913356905173886096303323

noncomputable def ep899 := nat_lit 100790055752928011277925228607886979691046956810895360000

noncomputable def ep900 := nat_lit 20068863863153288818432653131623307715049

noncomputable def ep901 := nat_lit 33040384769825903256848678543681388544000000

noncomputable def ep902 := nat_lit 59935896232514860855617469560095543912012507055269221

noncomputable def ep903 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz131 1 11)) (Complex.re (zetaApproximant qz131 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz131 1 11)) (Complex.im (zetaApproximant qz131 1 11))) ep896 ep897 ep898 ep899 ep900 ep901 ep902

noncomputable def ep904 := nat_lit 157484462113950017621758169699823405767260870017024000000

noncomputable def ep905 := nat_lit 1483432845265377645719284328549667863909662439569260179872264130291173468119862146498560000

noncomputable def ep906 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz131 1 11)) (Complex.re (zetaApproximant qz131 1 11)) 211875787073018563664633 101166148420809575628800 ep490 ep491 211875787073018563664633 101166148420809575628800 ep490 ep491 ep896

noncomputable def ep907 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz131 1 11)) (Complex.im (zetaApproximant qz131 1 11)) 141664617541407596243 5748076614818725888000 ep604 ep605 141664617541407596243 5748076614818725888000 ep604 ep605 ep900

noncomputable def ep908 := @ep886 985162418487296 ep887 18031337434935857 26599385299156992 2914951338799 26599385299156992 (@ep888 12537863 115964116992 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz205)) Bool.false 6641 442368 1 442368 (BSN.theta_err_eq 1 2 96 162 EMRow10.d13 EMRow10.d14 rfl) (ep728 rfl)) (ep889 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz131 1 11)) (@ep890 549053 262144 1805 262144 (@ep895 131072 (@ep903 ep904 ep905 ep891 ep892 ep893 ep894 (@ep906 ep897 ep898 ep899 ep711 ep711 rfl) (@ep907 ep901 ep902 ep904 ep717 ep717 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz229 := (@Norm.norm Complex Complex.instNorm qz408)

noncomputable def ep909 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz229 qz398) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) Bool.false 636850839925667 985162418487296 1446906493 985162418487296 (BSN.zrb_shape_eq qz229 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) qz140 3)

noncomputable def ep910 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz229 qz398) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) 13592759 917504 1 917504 46852213 1073741824 103 1073741824

noncomputable def ep911 := @Enclosure.Real.IsNear.mulLit_ff qz229 qz398 13592759 262144 1 262144 2 7 0 1 13592759 917504

noncomputable abbrev qz410 := (Complex.re qz445)

noncomputable abbrev qz411 := (Complex.im qz445)

noncomputable abbrev qz230 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz254 qz410 qz410) (@HMul.hMul Real Real Real qz254 qz411 qz411))

noncomputable abbrev qz231 := qz408

noncomputable def ep912 := @Enclosure.Real.IsNear.of_eq qz229 (Real.sqrt qz230) Bool.false 13592759 262144 1 262144 (BSN.norm_eq_sqrt_mul_add qz231)

noncomputable def ep913 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz230) Bool.false 13592759 262144 1 262144 13592759

noncomputable def ep914 := @Enclosure.Real.IsNear.sqrt_image qz230 672164189 250000 0 1 6796379 6796380 131072

noncomputable abbrev qz232 := (@HMul.hMul Real Real Real qz254 qz410 qz410)

noncomputable abbrev qz233 := (@HMul.hMul Real Real Real qz254 qz411 qz411)

noncomputable def ep915 := @Enclosure.Real.IsNear.addLit_ff qz232 qz233 49 4 0 1 669101689 250000 0 1

noncomputable abbrev qz234 := qz410

noncomputable def ep916 := @Enclosure.Real.IsNear.mulLit_ff qz234 qz234 7 2 0 1 7 2 0 1 49 4

noncomputable def ep917 := @Enclosure.Complex.IsNear.of_eq qz231 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz140) Bool.false 7 2 0 1 Bool.false 51734 1000 0 1 (BSN.s_add_nat_mk qz140 Bool.false 51734 1000 3 qz141)

noncomputable abbrev qz235 := (ep917 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz354 Bool.false 7 2 0 1 Bool.false 51734 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz356))

noncomputable def ep918 := @ep916 0 1 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 7 2 0 1 Bool.false 51734 1000 0 1 qz235)

noncomputable def ep919 := ep918 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 7 2 0 1 Bool.false 51734 1000 0 1 qz235)

noncomputable abbrev qz236 := qz411

noncomputable def ep920 := @Enclosure.Real.IsNear.mulLit_ff qz236 qz236 51734 1000 0 1 51734 1000 0 1 669101689 250000

noncomputable def ep921 := @ep920 0 1 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 7 2 0 1 Bool.false 51734 1000 0 1 qz235)

noncomputable def ep922 := ep921 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 7 2 0 1 Bool.false 51734 1000 0 1 qz235)

noncomputable def ep923 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Real.sqrt (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))))) Bool.false 46852213 1073741824

noncomputable def ep924 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))))) Bool.false 93704426 2147483648

noncomputable def ep925 := nat_lit 20499580444203159300560963631791409757534915234741553833

noncomputable def ep926 := nat_lit 10766746765857818570520837188270791065600000000000000000000

noncomputable def ep927 := nat_lit 42072173967107697590622746081061624317863420611602287025176876387571

noncomputable def ep928 := nat_lit 5050806371220235993553856658411827646724456283662136115200000000000000000000

noncomputable def ep929 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))) ep925 ep926 ep927 ep928

noncomputable def ep930 := nat_lit 20454825938508997852139947547860526525553384967448248729

noncomputable def ep931 := nat_lit 9273609709937040463621728009858180388918828193457354587869039149221

noncomputable def ep932 := nat_lit 1122401415826719109678634812980406143716545840813808025600000000000000000000

noncomputable def ep933 := nat_lit 310795178431676725145945027297800222093960189536841

noncomputable def ep934 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) ep930 ep926 ep931 ep932 ep933

noncomputable def ep935 := nat_lit 74769074762901517850839147140769382400000000000000000000

noncomputable def ep936 := nat_lit 681860544782031008649940073399625135457387482088382759532400432153

noncomputable def ep937 := nat_lit 10101612742440471987107713316823655293448912567324272230400000000000000000000

noncomputable def ep938 := nat_lit 1532734662840739924965400559776749206984949379202315606489925022371196853755220007687762739200000000000000000000

noncomputable def ep939 := nat_lit 4522701177229045922116587973

noncomputable def ep940 := nat_lit 103762935414616227840000000000

noncomputable def ep941 := nat_lit 1058442680265034420497833307929

noncomputable def ep942 := nat_lit 11167419953829577917496033280000000000

noncomputable def ep943 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) ep939 ep940 ep941 ep942 ep939 ep940 ep941

noncomputable def ep944 := nat_lit 17629383949295469500664221

noncomputable def ep945 := nat_lit 8646911284551352320000000000

noncomputable def ep946 := nat_lit 1663766255220858841958787062611

noncomputable def ep947 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228) Bool.true ep939 ep940 ep941 ep942 Bool.false ep944 ep945 ep946

noncomputable def ep948 := nat_lit 100506779584466201257464299520000000000

noncomputable def ep949 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228 Bool.true ep939 ep940 ep941 ep942 Bool.false ep944 ep945 ep946 ep948

noncomputable def ep950 := nat_lit 23058430092136939520000000

noncomputable def ep951 := nat_lit 97603077081815825298062849

noncomputable def ep952 := nat_lit 134009039445954935009952399360000000

noncomputable def ep953 := nat_lit 4506903415123787408884826473

noncomputable def ep954 := nat_lit 3150927271524649305168984211537

noncomputable abbrev qz237 := (Complex.re qz409)

noncomputable abbrev qz238 := (Complex.im qz409)

noncomputable def ep955 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238) 3510613801168558495947 ep950 ep951 ep952 ep953 ep940 ep954

noncomputable def ep956 := nat_lit 33502259861488733752488099840000000000

noncomputable def ep957 := nat_lit 104286388922761394195296200927621086457060392960000000

noncomputable def ep958 := nat_lit 1116741995382957791749603328

noncomputable def ep959 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237 2006992567 120000000 0 1 5247573696423 576460752303423488 48631508998416647 ep958 3510613801168558495947

noncomputable def ep960 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)))) 2006992567 120000000 0 1 0 1 0 1 2006992567

noncomputable def ep961 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 6020977701 500000 0 1 2006992567 120000000 0

noncomputable abbrev qz412 := (@HAdd.hAdd Complex Complex Complex qz423 qz438 qz427)

noncomputable abbrev qz239 := qz412

noncomputable def ep962 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz51 (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2)) qz239) Bool.true 6020977701 500000 0 1 Bool.true 17270469576863 125000000 0 1

noncomputable abbrev qz240 := (Complex.re qz412)

noncomputable abbrev qz241 := (Complex.im qz412)

noncomputable def ep963 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2))) qz240) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2))) qz241) 668914189 100000 0 1 669101689 125000 0 1

noncomputable def ep964 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2))) qz240 668914189 250000 0 1 5 2 0 1 668914189 100000

noncomputable abbrev qz413 := (@HAdd.hAdd Complex Complex Complex qz423 qz438 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz242 := qz413

noncomputable def ep965 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz51 (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)) qz242) Bool.true 668914189 250000 0 1 Bool.false 25867 250 0 1

noncomputable abbrev qz243 := (Complex.re qz413)

noncomputable abbrev qz244 := (Complex.im qz413)

noncomputable def ep966 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) qz243) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) qz244) 3 4 0 1 669101689 250000 0 1

noncomputable def ep967 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) qz243 1 2 0 1 3 2 0 1 3 4

noncomputable def ep968 := @ep967 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep676)

noncomputable def ep969 := @Enclosure.Complex.IsNear.of_eq qz242 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz140) Bool.false 3 2 0 1 Bool.false 51734 1000 0 1 (BSN.s_add_nat_mk qz140 Bool.false 51734 1000 1 qz141)

noncomputable abbrev qz245 := (ep969 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz354 Bool.false 3 2 0 1 Bool.false 51734 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz356))

noncomputable def ep970 := ep968 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 3 2 0 1 Bool.false 51734 1000 0 1 qz245)

noncomputable def ep971 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) qz244 51734 1000 0 1 51734 1000 0 1 669101689 250000

noncomputable def ep972 := @ep971 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep676)

noncomputable def ep973 := ep972 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 3 2 0 1 Bool.false 51734 1000 0 1 qz245)

noncomputable def ep974 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)) qz242 Bool.true 668914189 250000 0 1 Bool.false 25867 250 0 1 (@ep966 2675656756 668914189 250000 0 1 (ep970 rfl) (ep973 rfl) rfl rfl)

noncomputable def ep975 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) qz244) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) qz243) 25867 1000 0 1 77601 1000 0 1

noncomputable def ep976 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) qz244 1 2 0 1 51734 1000 0 1 25867 1000

noncomputable def ep977 := @ep976 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep676)

noncomputable def ep978 := ep977 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 3 2 0 1 Bool.false 51734 1000 0 1 qz245)

noncomputable def ep979 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1))) qz243 51734 1000 0 1 3 2 0 1 77601 1000

noncomputable def ep980 := @ep979 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep676)

noncomputable def ep981 := ep980 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 3 2 0 1 Bool.false 51734 1000 0 1 qz245)

noncomputable abbrev qz246 := (ep965 (BSN.ascPochhammer_succ_eval_c 1 2 qz352 rfl) (ep974 (@ep975 103468000 25867 250 0 1 (ep978 rfl) (ep981 rfl) rfl rfl)))

noncomputable def ep982 := @ep964 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 668914189 250000 0 1 Bool.false 25867 250 0 1 qz246)

noncomputable def ep983 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz140) Bool.false 5 2 0 1 Bool.false 51734 1000 0 1 (BSN.s_add_nat_mk qz140 Bool.false 51734 1000 2 qz141)

noncomputable abbrev qz247 := (ep983 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz354 Bool.false 5 2 0 1 Bool.false 51734 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz356))

noncomputable def ep984 := ep982 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 5 2 0 1 Bool.false 51734 1000 0 1 qz247)

noncomputable def ep985 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2))) qz241 25867 250 0 1 51734 1000 0 1 669101689 125000

noncomputable def ep986 := @ep985 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 668914189 250000 0 1 Bool.false 25867 250 0 1 qz246)

noncomputable def ep987 := ep986 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 5 2 0 1 Bool.false 51734 1000 0 1 qz247)

noncomputable def ep988 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2)) qz239 Bool.true 6020977701 500000 0 1 Bool.true 17270469576863 125000000 0 1 (@ep963 150524442525000 6020977701 500000 0 1 (ep984 rfl) (ep987 rfl) rfl rfl)

noncomputable def ep989 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2))) qz240) 17302803326863 125000000 0 1 25867 100 0 1

noncomputable def ep990 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2))) qz241 668914189 250000 0 1 51734 1000 0 1 17302803326863 125000000

noncomputable def ep991 := @ep990 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 668914189 250000 0 1 Bool.false 25867 250 0 1 qz246)

noncomputable def ep992 := ep991 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 5 2 0 1 Bool.false 51734 1000 0 1 qz247)

noncomputable def ep993 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2))) qz240 25867 250 0 1 5 2 0 1 25867 100

noncomputable def ep994 := @ep993 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 668914189 250000 0 1 Bool.false 25867 250 0 1 qz246)

noncomputable def ep995 := ep994 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 5 2 0 1 Bool.false 51734 1000 0 1 qz247)

noncomputable abbrev qz248 := (ep962 (BSN.ascPochhammer_succ_eval_c 2 3 qz352 rfl) (ep988 (@ep989 1727046957686300 17270469576863 125000000 0 1 (ep992 rfl) (ep995 rfl) rfl rfl)))

noncomputable def ep996 := @ep961 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep800) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6020977701 500000 0 1 Bool.true 17270469576863 125000000 0 1 qz248)

noncomputable def ep997 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 17270469576863 125000000 0 1 0 1 0

noncomputable def ep998 := @ep997 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep800) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6020977701 500000 0 1 Bool.true 17270469576863 125000000 0 1 qz248)

noncomputable def ep999 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)))) 17270469576863 90000000000 0 1 0 1 0 1 17270469576863

noncomputable def ep1000 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 17270469576863 125000000 0 1 17270469576863 90000000000 0

noncomputable def ep1001 := @ep1000 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep800) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6020977701 500000 0 1 Bool.true 17270469576863 125000000 0 1 qz248)

noncomputable def ep1002 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 6020977701 500000 0 1 0 1 0

noncomputable def ep1003 := @ep1002 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep800) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6020977701 500000 0 1 Bool.true 17270469576863 125000000 0 1 qz248)

noncomputable def ep1004 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 2006992567 120000000 0 1 Bool.false 17270469576863 90000000000 0 1 (@ep960 2006992567 120000000 0 1 (ep996 rfl) (ep998 rfl) rfl rfl) (@ep999 17270469576863 90000000000 0 1 (ep1001 rfl) (ep1003 rfl) rfl rfl)

noncomputable def ep1005 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2006992567 120000000 0 1 Bool.false 17270469576863 90000000000 0 1 ep1004

noncomputable def ep1006 := @Enclosure.Complex.IsNear.re_isNear qz228 Bool.true 5247573696423 576460752303423488 48631508998416647 ep958 Bool.false 260960096948471 1152921504606846976 547337857404740397 ep958

noncomputable abbrev qz414 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 19487171)))

noncomputable def ep1007 := @Enclosure.Complex.IsNear.of_eq qz228 (Complex.mk (@HMul.hMul Real Real Real qz0 qz414 qz191) (@HMul.hMul Real Real Real qz0 qz414 qz192)) Bool.true 5247573696423 576460752303423488 48631508998416647 ep958 Bool.false 260960096948471 1152921504606846976 547337857404740397

noncomputable abbrev qz415 := (Real.sqrt (@Nat.cast Real Real.instNatCast 19487171))

noncomputable abbrev qz416 := (@Nat.cast Real Real.instNatCast 19487171)

noncomputable def ep1008 := @Enclosure.Real.IsNear.inv_image qz415 9479911077611 2147483648 1 2147483648 243234 243235 1073741824 (@Enclosure.Real.IsNear.of_eq qz415 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz416 qz26)) Bool.false 9479911077611 2147483648 1 2147483648 (BSN.sqrt_natCast_div_one 19487171) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz416 qz26)) Bool.false 9479911077611 2147483648 1 2147483648 9479911077611 2147483648 1 2147483648 (BSN.sqrt_enclosure 19487171 1 4739955538805 4739955538806 1073741824 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1009 := nat_lit 242154819500000000000000000

noncomputable def ep1010 := nat_lit 92764080252577317623169024

noncomputable def ep1011 := BSN.log_dyadic_bound 3 19 6 5 63732433749841395 1073741824 484309639 537698765144529 55801305 341937090 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 3) (BSN.artanhQ 19) 0 5 537698765144529 63732433749841395 55801305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1012 := @Enclosure.Real.IsNear.mulLit_ff qz140 qz193 51734 1000 0 1 10799160256583397 4503599627370496 1000001452928917 484309639000000000000000 279341878357042730199 2251799813685248000 25867037582912296039 ep1009 qz142 (BSN.isNear_log_sfrac 11 1 10799160256583397 4503599627370496 1000001452928917 484309639000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz389) Bool.false ep1010 ep850 1000001452928917 484309639000000000000000 10799160256583397 4503599627370496 1000001452928917 484309639000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 341937090 1073741824 24973259072661432 36028797018963968 484309639 1000000000000000 rfl rfl rfl rfl (ep1011 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1013 := nat_lit 473697925395543890277171200

noncomputable def ep1014 := nat_lit 309485009821345068724781056

noncomputable def ep1015 := nat_lit 5755832395196602538607613296454508186038450188279521161437803998500484461026008536538623333869753351943074337851669309263112519971151814302523048060490231054336

noncomputable def ep1016 := nat_lit 25087349417715593433012958174142958689126641386910427249058555817347792676670613748293986999300093003550818609852734049752458890129433227026772000655283952025600

noncomputable def ep1017 := nat_lit 8658849393474002540778769845719567678768647755596692187448272243484523966329475582582175836559363199161353084643244858827729694653698029629041486443053056

noncomputable def ep1018 := nat_lit 34842869371373434882131557070381171793203112575834849108379681960961208809004001990007330185985454217560988191639450244820810481443369743143943276589243579760640

noncomputable def ep1019 := nat_lit 2282948797012119002404179193847009240710524366208848879664328579378649133577025851094752816936308463323124493496598798527473759001778423659436252059630839634329600

noncomputable def ep1020 := BSN.cos_dyadic_bound_f 6731652396688 4398046511104 4 3 2147483648 969565196 ep1015 ep1016 ep1017 ep1018 ep1019 ep1017 86296536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6731652396688) (BSN.cosEvenQ 4398046511104) 0 3 ep1015 ep1016 ep1017 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6731652396688) (BSN.cosOddQ 4398046511104) 0 3 ep1018 ep1019 ep1017 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz417 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 266401174885) (@Nat.cast Real Real.instNatCast 2147483648))

noncomputable def ep1021 := @Enclosure.Real.IsNear.cos_image qz194 qz417 Bool.false 266401174885 2147483648 231 2147483648 Bool.true 86296536 2147483648 1 484309639 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 279341878357042730199 2251799813685248000 25867037582912296039 ep1009 266401174885 2147483648 231 2147483648 (ep1012 rfl) rfl) (Enclosure.sfrac_false_div 266401174885 2147483648) (BSN.cos_reduce2 qz417 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1013) (@Nat.cast Real Real.instNatCast ep1014)) 226375608064910080 72057594037927936 Bool.false 86296536 2147483648 19 1000000000000000 968619278 484309639 (BSN.sin_reduce_arg_pos_rat_q2 266401174885 2147483648 226375608064910080 72057594037927936 19 ep1013 ep1014 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 86296536 2147483648 ep1013 ep1014 6731652396688 4398046511104 969565196 968619278 (ep1020 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1022 := nat_lit 14943492291071462684697132091699789211547709372477312470430053557333566233058127383367860072827598062893697370590819620910950595400007551777899253395410812665856

noncomputable def ep1023 := nat_lit 326135542430302714629168456263858462958646338029835554237761225625521304796717978727821830990901209046160641928085542646781965571682631951348036008518691376332800

noncomputable def ep1024 := nat_lit 74633747865693497692535462579362053712570655314472455622605943524023001673488060772569314607300285742467505379315407800283669223654648409697190135669459848790016

noncomputable def ep1025 := nat_lit 11414743985060595012020895969235046203552621831044244398321642896893245667885129255473764084681542316615622467482993992637368795008892118297181260298154198171648000

noncomputable def ep1026 := BSN.sin_dyadic_bound_f 6731652396688 4398046511104 4 3 2147483648 969565196 ep1022 ep1023 ep1017 ep1024 ep1025 ep1017 2145749036 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 6731652396688) (BSN.sinEvenQ 4398046511104) 0 3 ep1022 ep1023 ep1017 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 6731652396688) (BSN.sinOddQ 4398046511104) 0 3 ep1024 ep1025 ep1017 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1027 := @Enclosure.Real.IsNear.sin_image qz194 qz417 Bool.false 266401174885 2147483648 231 2147483648 Bool.true 2145749036 2147483648 1 484309639 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 279341878357042730199 2251799813685248000 25867037582912296039 ep1009 266401174885 2147483648 231 2147483648 (ep1012 rfl) rfl) (Enclosure.sfrac_false_div 266401174885 2147483648) (BSN.sin_reduce2 qz417 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1013) (@Nat.cast Real Real.instNatCast ep1014)) 226375608064910080 72057594037927936 Bool.false 2145749036 2147483648 19 1000000000000000 968619278 484309639 (BSN.sin_reduce_arg_pos_rat_q2 266401174885 2147483648 226375608064910080 72057594037927936 19 ep1013 ep1014 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2145749036 2147483648 ep1013 ep1014 6731652396688 4398046511104 969565196 968619278 (ep1026 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1028 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz414 qz191) (@HMul.hMul Real Real Real qz0 qz414 qz192) Bool.true 5247573696423 576460752303423488 48631508998416647 ep958 Bool.false 260960096948471 1152921504606846976 547337857404740397 ep958 (@Enclosure.Real.IsNear.mulLit_ft qz414 qz191 486469 2147483648 1 2147483648 10787067 268435456 114023010257 1040047030321283072 5247573696423 576460752303423488 48631508998416647 ep958 (@Enclosure.Real.IsNear.recentre' qz414 Bool.false 486469 2147483648 1 2147483648 486469 2147483648 1 2147483648 (ep1008 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz191 Bool.true 86296536 2147483648 114023010257 1040047030321283072 10787067 268435456 114023010257 1040047030321283072 (ep1021 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz414 qz192 486469 2147483648 1 2147483648 536437259 536870912 114023010257 1040047030321283072 260960096948471 1152921504606846976 547337857404740397 ep958 (@Enclosure.Real.IsNear.recentre' qz414 Bool.false 486469 2147483648 1 2147483648 486469 2147483648 1 2147483648 (ep1008 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz195 Bool.true 536437259 536870912 114023010257 1040047030321283072 (@Enclosure.Real.IsNear.recentre' qz195 Bool.true 2145749036 2147483648 114023010257 1040047030321283072 536437259 536870912 114023010257 1040047030321283072 (ep1027 rfl rfl) rfl)) rfl)

noncomputable def ep1029 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238 17270469576863 90000000000 0 1 260960096948471 1152921504606846976 547337857404740397 ep958 ep953

noncomputable def ep1030 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2006992567 120000000 0 1 Bool.false 17270469576863 90000000000 0 1 ep1004

noncomputable def ep1031 := @Enclosure.Complex.IsNear.im_isNear qz228 Bool.true 5247573696423 576460752303423488 48631508998416647 ep958 Bool.false 260960096948471 1152921504606846976 547337857404740397 ep958

noncomputable def ep1032 := nat_lit 138350580552821637120000000

noncomputable def ep1033 := nat_lit 366167670483006629114543033

noncomputable def ep1034 := nat_lit 44669679815318311669984133120000000

noncomputable def ep1035 := nat_lit 10069784652935548625184561

noncomputable def ep1036 := nat_lit 5764607523034234880000000000

noncomputable def ep1037 := nat_lit 839888996634093926451065238361

noncomputable def ep1038 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237) 523744974859180679015057 ep1032 ep1033 ep1034 ep1035 ep1036 ep1037

noncomputable def ep1039 := nat_lit 1626023669449082462037185253702935720419655680000000

noncomputable def ep1040 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238 2006992567 120000000 0 1 260960096948471 1152921504606846976 547337857404740397 ep958 523744974859180679015057

noncomputable def ep1041 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237 17270469576863 90000000000 0 1 5247573696423 576460752303423488 48631508998416647 ep958 ep1035

noncomputable abbrev qz418 := (@ep1007 ep958 (BSN.cpow_neg_s_sub_mk qz140 51734 1000 11 3 19487171 qz141 rfl EMRow10.d18) ep1028)

noncomputable def ep1042 := ep949 (@ep955 ep956 ep957 ep939 ep940 ep941 ep942 (@ep959 ep950 ep951 ep952 ep1005 (ep1006 qz418) rfl) (@ep1029 ep940 ep954 ep956 ep1030 (ep1031 qz418) rfl) rfl rfl) (@ep1038 ep948 ep1039 ep944 ep945 ep946 ep948 (@ep1040 ep1032 ep1033 ep1034 ep1005 (ep1031 qz418) rfl) (@ep1041 ep1036 ep1037 ep948 ep1030 (ep1006 qz418) rfl) rfl rfl)

noncomputable def ep1043 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) ep944 ep945 ep946 ep948 ep944 ep945 ep946

noncomputable def ep1044 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228) Bool.true ep939 ep940 ep941 ep942 Bool.false ep944 ep945 ep946

noncomputable def ep1045 := @ep910 636850839925667 985162418487296 1446906493 985162418487296 (@ep911 1 917504 (ep912 (@ep913 262144 1 262144 (ep914 (@ep915 2688656756 672164189 250000 0 1 (ep919 rfl) (ep922 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep923 103 1073741824 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (@ep924 206 2147483648 46852213 1073741824 103 1073741824 (@ep929 46852110 46852316 1073741824 (@ep934 ep935 ep936 ep937 ep938 ep925 ep926 ep927 ep928 (@ep943 ep942 ep930 ep926 ep931 ep932 (@ep947 ep948 ep1042) (@ep947 ep948 ep1042) rfl) (@ep1043 ep948 ep933 ep935 ep936 ep937 (@ep1044 ep948 ep1042) (@ep1044 ep948 ep1042) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow10.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz131 1 11))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))) Bool.false 18031337434935857 26599385299156992 2914951338799 26599385299156992 := ep908 (ep909 ep1045) rfl rfl

noncomputable def EMRow10.d20 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz419 := (EMRow10.d3 qz428 qz440 (@Enclosure.dec_le_dec qz428 qz440 48711 1000 51734 1000 (@Eq.refl Real qz428) (@Eq.refl Real qz440) rfl rfl rfl) 10 11 1 1)

noncomputable abbrev qz249 := qz419

noncomputable def ep1046 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz249 (@Enclosure.dec_nonneg qz24 48711 1000 qz25) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 10 rfl)

noncomputable abbrev qz250 := (Zeta.Certificates.ZIntervalEM.fstVal qz419)

noncomputable def ep1047 := @Enclosure.Real.IsNear.pos_val qz250 ep149 ep150

noncomputable def ep1048 := @Enclosure.Real.IsNear.of_eq qz250 (hardyZApproximantEM 1 10 qz24) Bool.false

noncomputable abbrev qz251 := (Zeta.Certificates.ZIntervalEM.sndVal qz419)

noncomputable def ep1049 := BSN.mul_neg_of_pos_neg_r qz250 qz251 (@ep1047 ep151 ep152 (@ep1048 ep149 ep150 ep151 ep152 (@Eq.refl Real (hardyZApproximantEM 1 10 qz24)) EMRow10.d9) rfl rfl rfl)

noncomputable def ep1050 := @Enclosure.Real.IsNear.neg_val qz251 ep474 ep475

noncomputable def ep1051 := @Enclosure.Real.IsNear.of_eq qz251 (hardyZApproximantEM 1 11 qz140) Bool.true

noncomputable def ep1052 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz250) (BSN.hardyZErrorBoundStrong 1 10 qz24)

noncomputable def ep1053 := @Enclosure.norm_gt_of_isNear qz250 (BSN.hardyZErrorBoundStrong 1 10 qz24) Bool.false

noncomputable def ep1054 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 10 qz24) (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))) Bool.false 2739249393263117 3799912185593856 2747263778395 26599385299156992 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))))

noncomputable def ep1055 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz251) (BSN.hardyZErrorBoundStrong 1 11 qz140)

noncomputable def ep1056 := @Enclosure.norm_gt_of_isNear qz251 (BSN.hardyZErrorBoundStrong 1 11 qz140) Bool.true

noncomputable def ep1057 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 11 qz140) (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz131 1 11))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))) Bool.false 18031337434935857 26599385299156992 2914951338799 26599385299156992 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz93 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz131 1 11))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz51 (@HMul.hMul Complex Complex Complex qz51 (@HDiv.hDiv Complex Complex Complex qz59 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz131 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))))

noncomputable def ep1058 := @List.cons EMRow10.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz249 (ep1046 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 11 rfl) (ep1049 (@ep1050 ep476 ep477 (@ep1051 ep474 ep475 ep476 ep477 (@Eq.refl Real (hardyZApproximantEM 1 11 qz140)) EMRow10.d12) rfl rfl rfl)) (ep1052 (hardyZErrorBoundEM 1 10 qz24) (BSN.hardyZErrorBoundEM_le_strong 1 10 qz24 rfl) (@ep1053 Bool.false ep149 ep150 ep151 ep152 2739249393263117 3799912185593856 2747263778395 26599385299156992 (@ep1048 ep149 ep150 ep151 ep152 (@Eq.refl Real (hardyZApproximantEM 1 10 qz24)) EMRow10.d9) (ep1054 EMRow10.d17) rfl rfl rfl rfl rfl)) (ep1055 (hardyZErrorBoundEM 1 11 qz140) (BSN.hardyZErrorBoundEM_le_strong 1 11 qz140 rfl) (@ep1056 Bool.false ep474 ep475 ep476 ep477 18031337434935857 26599385299156992 2914951338799 26599385299156992 (@ep1051 ep474 ep475 ep476 ep477 (@Eq.refl Real (hardyZApproximantEM 1 11 qz140)) EMRow10.d12) (ep1057 EMRow10.d19) rfl rfl rfl rfl rfl)))) (@List.nil EMRow10.d0)

noncomputable abbrev qz420 := (@Enclosure.dec_le_dec qz428 qz440 48711 1000 51734 1000 (@Eq.refl Real qz428) (@Eq.refl Real qz440) rfl rfl rfl)

noncomputable abbrev qz252 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1058 (@List.IsChain.singleton EMRow10.d1 EMRow10.d20 (EMRow10.d2 qz267 qz354 qz420))))

noncomputable abbrev qz421 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1059 := And (@Eq (Option Real) (@Option.map qz421 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz421 qz252)) (@Option.some Real qz24))

noncomputable def ep1060 := ep1059 (@Eq (Option Real) (@Option.map qz421 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz421 qz252)) (@Option.some Real qz140))

noncomputable def ep1061 := @And.intro (@Eq Nat (@List.length qz421 qz252) 1) ep1060

noncomputable def ep1062 := @And.intro (@Eq (Option Real) (@Option.map qz421 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz421 qz252)) (@Option.some Real qz24))

noncomputable def ep1063 := @ep1062 (@Eq (Option Real) (@Option.map qz421 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz421 qz252)) (@Option.some Real qz140))

noncomputable abbrev qz253 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1058 (@List.IsChain.singleton EMRow10.d1 EMRow10.d20 (EMRow10.d2 qz267 qz354 qz420)))

theorem EMRow10.d21 : Zeta.Certificates.BatchSpec 1 48711 1000 51734 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz421 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz421 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz421 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz24)) (@Eq (Option Real) (@Option.map qz421 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz421 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz140)))) qz253 (ep1061 (@Eq.refl Nat 1) (ep1063 (@Eq.refl (Option Real) (@Option.some Real qz24)) (@Eq.refl (Option Real) (@Option.some Real qz140))))

theorem solution : Zeta.Certificates.BatchSpec 1 48711 1000 51734 1000 := EMRow10.d21
#print axioms solution
#check solution
