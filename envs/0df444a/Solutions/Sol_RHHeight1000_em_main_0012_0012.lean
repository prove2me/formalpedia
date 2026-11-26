-- Prove2me | solution 1 for RHHeight1000.em_main_0012_0012
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:58:57.683069+00:00
-- url     : https://prove2.me/submissions/69a6c684-e085-456f-9d23-f46402dbcfa1

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow12.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow12.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow12.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow12.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow12.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz254 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz254

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz255 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz255 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138525251149047 2251799813685248 250000000034843 17421500000000000000 4138525251149047 2251799813685248 250000000034843 17421500000000000000 240893 131072

noncomputable abbrev qz256 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 131072 qz256 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 779317518150410741488063439345657628452599855445271348474342368876423347582876053728679783827237610085654588674605917415063316248867402488514697634436426745

noncomputable def ep10 := nat_lit 13198325246229587668616048586507268161410801335203869857947191811663857046415771104290097871102374067703089877156867761119753226876438075596795543285583799

noncomputable def ep11 := nat_lit 13338205139369261376383149914767634013226508915861991492218067381232119098362059104733250767410551174650894954010182016771344050520336484956804919489535

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 4 3 ep9 262144 69686 ep10 ep11 118379 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 3 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz257 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz257

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138525251149047 2251799813685248 250000000034843 17421500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 17358233014995452428288 9444732965739290427392 1000000000139372 69686000000000000000 4138525251149047 2251799813685248 250000000034843 17421500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 118379 262144 24973259072661432 36028797018963968 69686 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 779317518150412560342812906055656980396982394702499187106382620393032652998517540933158707129341055012778793601285942846917973645097155238594697634436426745

noncomputable def ep18 := nat_lit 13198325246229655554962711811363413523213721429909419700721697472804734044169853548961061453892255410264786862895235075217650796661500958924795543285583799

noncomputable def ep19 := nat_lit 13338205139369401582665284895604560799810298653799657073142644093199656832454717421805370366589019475922075211274104314270069372987910244956804919489535

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 4 3 ep17 262144 69686 ep18 ep19 118379 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 3 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138525251149047 2251799813685248 250000000034843 17421500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 17358233014995452428288 9444732965739290427392 1000000000139372 69686000000000000000 4138525251149047 2251799813685248 250000000034843 17421500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 118379 262144 24973259072661432 36028797018963968 69686 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz258 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz3 := (Real.log qz258)

theorem EMRow12.d4 : Enclosure.Real.IsNear qz3 Bool.false 240893 131072 3 131072 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz255) Bool.false 240893 131072 3 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz255) Bool.false 240893 131072 3 131072 240893 131072 3 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 300084 262144 1 69686 300084 262144 1 69686 150042 131072 2 131072 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 5456220599384213465248909714772227496572670538165976141063262914812807742611017753801422503639530882087556452122005170047444298375835020188444492540969863625638808382453421118235702266947370928498132967594635949979551089348001357731941995137847266570621617494261809398531128871567535833923098076891483476912075228072418610430965163137427706923427310178652894498746239459018086669257415154730407592571637957767157504839263249849478535520334507104454135585522664276476675

noncomputable def ep28 := nat_lit 583201912334273870627228188254822588827079241605343036411752047433839590517388190714780374919746279700129906501257101384229175562492847525225536391462542197025353003914524118772974087630067522636400444148635637549655768907025719966434833632093412247469427754039812435067522613541620617101084764807513402584784781490076808276521160080078978009740617112077674385114356333461540984478969922738031393369686631450339262287925718320742111081121726382582016608811398564907105

noncomputable def ep29 := nat_lit 2006268627360805445673839316848610509641534779303135707206598861506426804997221642604762844037348942607248852390277353874343091902420975230792155995982437872051629609224882022549487822374001366578458875613104959699164386313425243185530298109514065278868815165519648262204211929774735225023360668387821809970420335957473972782118680523137645713941929429588852958886338507735711181009301082096313539911189247153419366938656533848809858580689548163599238034961919825

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 10 9 ep27 262144 69686 ep28 ep29 300084 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 9 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 5456220599384260892400251500854699790811159195150212163211869656216336849990273498858157048596616978904240776489460003685239051624059887013466241201881443704542959173524008982544253046253151867013374679201187657749749224297051088632484873343955402287279851789208893474071824987110190207053471018354491495133306616646837230249901879422821128116650397962087630806812522581253210958036113071268120219429850657911869289056672761916619783759890108169949892385522664276476675

noncomputable def ep34 := nat_lit 583201912334279575053067226115417021307550325332234501953544426829928714668898700518418107620762577859683234776628347658361181262145210140271013263714562720079188253110303208819702903278206870150494721073991877864419341163488949363940583288588224434829960190109694548513088121652843287215458036179968684293644459891198769761601084092249455692877745995219003758983943549453190712470220270279351626860119698313725888367584660500821040083453648022042061408811398564907105

noncomputable def ep35 := nat_lit 2006268627360839170887858856494478835319319717359667041823756329478526322484078784125879825811686186445537802910004300367040714583746383402724632880452479311196631191501299191497899488881639138562974769996989848045902383299749709271247360054208480548633525642122514778503225872819822968825602771791453574137145372948950799520945900351638147820910599315255916738483881817718250085827996954508077874524152655659774549924038927632065100609588052048399238034961919825

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 10 9 ep33 262144 69686 ep34 ep35 300084 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 9 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 150042 131072 2 131072 75021 65536 1 65536 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 300084 262144 1 69686 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 300084 262144 69686 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 300084 262144 1 69686 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 300084 262144 69686 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow12.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 65536 := ep37

noncomputable abbrev qz452 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 54675 1000)))

noncomputable abbrev qz428 := qz452

noncomputable abbrev qz259 := qz428

noncomputable abbrev qz4 := (BSN.headSumC qz259 9)

noncomputable abbrev qz453 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz429 := qz453

noncomputable abbrev qz260 := qz429

noncomputable abbrev qz5 := qz260

noncomputable abbrev qz6 := qz259

noncomputable abbrev qz430 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz261 := qz430

noncomputable abbrev qz431 := (@Neg.neg Complex Complex.instNeg qz452)

noncomputable abbrev qz262 := qz431

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 8) qz262)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz4 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 8) qz7) Bool.false 162115029093 68719476736 13007095062657 2394392727912448 Bool.false 2986270211 68719476736 12959072210105 2394392727912448

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 8) qz7 Bool.false 142009800879 68719476736 11637173625095 2394392727912448 Bool.false 16627114289 68719476736 11594011231671 2394392727912448 Bool.false

noncomputable abbrev qz8 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 7) qz262)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 7) qz8) Bool.false 142009800879 68719476736 11637173625095 2394392727912448 Bool.false 16627114289 68719476736 11594011231671 2394392727912448

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 7) qz8 Bool.false 29578521081 17179869184 5090256787855 1197196363956224 Bool.false 5990768939 68719476736 10141943663901 2394392727912448 Bool.false

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 6) qz262)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 6) qz9) Bool.false 29578521081 17179869184 5090256787855 1197196363956224 Bool.false 5990768939 68719476736 10141943663901 2394392727912448

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 6) qz9 Bool.false 8866054939 4294967296 537549618555 149649545494528 Bool.true 9266858421 68719476736 8567618866133 2394392727912448 Bool.true

noncomputable abbrev qz10 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 5) qz262)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 5) qz10) Bool.false 8866054939 4294967296 537549618555 149649545494528 Bool.true 9266858421 68719476736 8567618866133 2394392727912448

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 5) qz10 Bool.false 111139550499 68719476736 6877971967675 2394392727912448 Bool.true 4152238153 34359738368 3426820149693 1197196363956224 Bool.false

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 4) qz262)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 4) qz11) Bool.false 111139550499 68719476736 6877971967675 2394392727912448 Bool.true 4152238153 34359738368 3426820149693 1197196363956224

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 4) qz11 Bool.false 19863972185 17179869184 154800302719 74824772747264 Bool.false 77953229 1073741824 154192710485 74824772747264 Bool.false

noncomputable abbrev qz432 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz263 := qz432

noncomputable abbrev qz12 := (@HPow.hPow Complex Complex Complex qz261 qz263 qz262)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 3) qz12) Bool.false 19863972185 17179869184 154800302719 74824772747264 Bool.false 77953229 1073741824 154192710485 74824772747264

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 3) qz12 Bool.false 29088996433 17179869184 1363744312907 1197196363956224 Bool.true 2397080907 17179869184 1356592369041 1197196363956224 Bool.true

noncomputable abbrev qz433 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz264 := qz433

noncomputable abbrev qz13 := (@HPow.hPow Complex Complex Complex qz261 qz264 qz262)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 2) qz13) Bool.false 29088996433 17179869184 1363744312907 1197196363956224 Bool.true 2397080907 17179869184 1356592369041 1197196363956224

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 2) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz265 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz14 := qz265

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz6)

noncomputable abbrev qz266 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz15 := (@Inv.inv Real Real.instInv (Real.sqrt qz266))

noncomputable abbrev qz454 := (Enclosure.sfrac Bool.false 54675 1000)

noncomputable abbrev qz434 := qz454

noncomputable abbrev qz267 := qz434

noncomputable abbrev qz16 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz17 := qz267

noncomputable abbrev qz268 := (@Eq.refl Real qz434)

noncomputable abbrev qz18 := qz268

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz13 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)))) Bool.false 11909127249 17179869184 1363744312907 1197196363956224 Bool.true 2397080907 17179869184 1356592369041 1197196363956224 (BSN.cpow_neg_s_mk qz17 54675 1000 2 qz18 rfl)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz266) 370727 262144 1 262144 92681 92683 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz266) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz266 qz19)) Bool.false 370727 262144 1 262144 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz266 qz19)) Bool.false 370727 262144 1 262144 370727 262144 1 262144 (BSN.sqrt_enclosure 2 1 185363 185364 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 131072 34843 24381081 945 90852 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 129321564726639444951085737540241

noncomputable def ep57 := nat_lit 1993841993677373809355710590420516864

noncomputable def ep58 := nat_lit 29907629905160607140335658856307752960

noncomputable abbrev qz269 := (BSN.cosEvenQ 536870912)

noncomputable abbrev qz270 := (BSN.cosOddQ 536870912)

noncomputable def ep59 := BSN.cos_dyadic_bound_f 106639411 536870912 2 1 262144 69755 ep56 ep57 ep56 ep56 ep58 ep56 256989 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 106639411) qz269 0 1 ep56 ep57 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 106639411) qz270 0 1 ep56 ep58 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz20 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz21 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz271 := (Enclosure.Real.IsNear.const Bool.false 54675 1000)

noncomputable abbrev qz22 := qz271

noncomputable abbrev qz272 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4967333) qz20)

noncomputable abbrev qz273 := (BSN.isNear_log_sfrac 2 1 90852 131072 1 34843 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 90852 131072 34843 rfl rfl rfl (ep55 rfl)))

noncomputable abbrev qz274 := (@Nat.cast Real Real.instNatCast 3752040723591920091136)

noncomputable abbrev qz275 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep60 := @Enclosure.Real.IsNear.cos_image qz16 qz272 Bool.false 4967333 131072 103 65536 Bool.false 256989 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 49673331 1310720 2187 1393720 4967333 131072 103 65536 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz21 54675 1000 0 1 90852 131072 1 34843 49673331 1310720 2187 1393720 qz22 qz273 rfl) rfl) (Enclosure.sfrac_false_div 4967333 131072) (BSN.cos_reduce0 qz272 (@HDiv.hDiv Real Real Real qz2 qz274 qz275) 226375608064910080 72057594037927936 Bool.false 256989 262144 6 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 4967333 131072 226375608064910080 72057594037927936 6 3752040723591920091136 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 256989 262144 3752040723591920091136 18889465931478580854784 106639411 536870912 69755 69686 (ep59 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz276 := (BSN.sinEvenQ 536870912)

noncomputable abbrev qz277 := (BSN.sinOddQ 536870912)

noncomputable def ep61 := BSN.sin_dyadic_bound_f 106639411 536870912 1 0 262144 69755 0 1 1 0 1 1 51727 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 106639411) qz276 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 106639411) qz277 0 0 rfl) rfl rfl

noncomputable def ep62 := @Enclosure.Real.IsNear.sin_image qz16 qz272 Bool.false 4967333 131072 103 65536 Bool.false 51727 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 49673331 1310720 2187 1393720 4967333 131072 103 65536 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz21 54675 1000 0 1 90852 131072 1 34843 49673331 1310720 2187 1393720 qz22 qz273 rfl) rfl) (Enclosure.sfrac_false_div 4967333 131072) (BSN.sin_reduce0 qz272 (@HDiv.hDiv Real Real Real qz2 qz274 qz275) 226375608064910080 72057594037927936 Bool.false 51727 262144 6 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 4967333 131072 226375608064910080 72057594037927936 6 3752040723591920091136 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 51727 262144 3752040723591920091136 18889465931478580854784 106639411 536870912 69755 69686 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz278 := (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 185364 262144 2 262144 46341 65536 1 131072 (ep54 rfl rfl) rfl)

noncomputable def ep63 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16))) Bool.false 11909127249 17179869184 1363744312907 1197196363956224 Bool.true 2397080907 17179869184 1356592369041 1197196363956224 (@Enclosure.Real.IsNear.mulLit_ff qz15 (Real.cos qz16) 46341 65536 1 131072 256989 262144 3654365 2283470848 11909127249 17179869184 1363744312907 1197196363956224 qz278 (@Enclosure.Real.IsNear.recentre' (Real.cos qz16) Bool.false 256989 262144 3654365 2283470848 256989 262144 3654365 2283470848 (ep60 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)) 46341 65536 1 131072 51727 262144 3654365 2283470848 2397080907 17179869184 1356592369041 1197196363956224 qz278 (@Enclosure.Real.IsNear.neg (Real.sin qz16) Bool.false 51727 262144 3654365 2283470848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz16) Bool.false 51727 262144 3654365 2283470848 51727 262144 3654365 2283470848 (ep62 rfl rfl) rfl)) rfl)

noncomputable abbrev qz279 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz23 := qz279

noncomputable def ep64 := @ep51 11909127249 17179869184 1363744312907 1197196363956224 Bool.true 2397080907 17179869184 1356592369041 1197196363956224 Bool.false 29088996433 29088996433 17179869184 1363744312907 1197196363956224 Bool.true 2397080907 2397080907 17179869184 1356592369041 1197196363956224 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz23)) (ep53 ep63) rfl rfl

noncomputable abbrev qz24 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep65 := @Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)))) Bool.true 1153128031 2147483648 1113060530597 1197196363956224 Bool.false 3644332571 17179869184 1110490998719 1197196363956224 (BSN.cpow_neg_s_mk qz17 54675 1000 3 qz18 rfl)

noncomputable abbrev qz26 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep66 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz26) 454047 262144 1 262144 75674 75675 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz26) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz26 qz19)) Bool.false 454047 262144 1 262144 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz26 qz19)) Bool.false 454047 262144 1 262144 454047 262144 1 262144 (BSN.sqrt_enclosure 3 1 227023 227024 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep67 := BSN.log_dyadic_bound 1 2 9 8 2258332876800 131072 34843 222698787165 2027025 143997 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1) (BSN.artanhQ 2) 0 8 222698787165 2258332876800 2027025 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep68 := nat_lit 1664599131716786073114254774978161

noncomputable def ep69 := BSN.cos_dyadic_bound_f 201988859 536870912 2 1 262144 69755 ep68 ep57 ep68 ep68 ep58 ep68 243808 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 201988859) qz269 0 1 ep68 ep57 ep68 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 201988859) qz270 0 1 ep68 ep58 ep68 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz27 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz28 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz29 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz280 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15746071) qz27)

noncomputable abbrev qz281 := (BSN.isNear_log_sfrac 3 1 143997 131072 1 34843 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 143997 131072 34843 rfl rfl rfl (ep67 rfl)))

noncomputable def ep70 := @Enclosure.Real.IsNear.cos_image qz25 qz280 Bool.false 15746071 262144 413 262144 Bool.true 243808 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 314921439 5242880 2187 1393720 15746071 262144 413 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz28 54675 1000 0 1 143997 131072 1 34843 314921439 5242880 2187 1393720 qz22 qz281 rfl) rfl) (Enclosure.sfrac_false_div 15746071 262144) (BSN.cos_reduce2 qz280 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14213702399204001841152) qz29) 226375608064910080 72057594037927936 Bool.false 243808 262144 9 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q2 15746071 262144 226375608064910080 72057594037927936 9 14213702399204001841152 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 243808 262144 14213702399204001841152 37778931862957161709568 201988859 536870912 69755 69686 (ep69 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep71 := nat_lit 9969209968386869046778552952102584320

noncomputable def ep72 := nat_lit 69784469778708083327449870664718090240

noncomputable def ep73 := BSN.sin_dyadic_bound_f 201988859 536870912 2 1 262144 69755 ep68 ep71 ep68 ep68 ep72 ep68 96316 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 201988859) qz276 0 1 ep68 ep71 ep68 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 201988859) qz277 0 1 ep68 ep72 ep68 rfl rfl rfl rfl) rfl rfl

noncomputable def ep74 := @Enclosure.Real.IsNear.sin_image qz25 qz280 Bool.false 15746071 262144 413 262144 Bool.true 96316 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 314921439 5242880 2187 1393720 15746071 262144 413 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz28 54675 1000 0 1 143997 131072 1 34843 314921439 5242880 2187 1393720 qz22 qz281 rfl) rfl) (Enclosure.sfrac_false_div 15746071 262144) (BSN.sin_reduce2 qz280 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14213702399204001841152) qz29) 226375608064910080 72057594037927936 Bool.false 96316 262144 9 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q2 15746071 262144 226375608064910080 72057594037927936 9 14213702399204001841152 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 96316 262144 14213702399204001841152 37778931862957161709568 201988859 536870912 69755 69686 (ep73 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz282 := (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 151349 262144 1 262144 151349 262144 1 262144 (ep66 rfl rfl) rfl)

noncomputable def ep75 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25))) Bool.true 1153128031 2147483648 1113060530597 1197196363956224 Bool.false 3644332571 17179869184 1110490998719 1197196363956224 (@Enclosure.Real.IsNear.mulLit_ft qz24 (Real.cos qz25) 151349 262144 1 262144 7619 8192 14652303 9133883392 1153128031 2147483648 1113060530597 1197196363956224 qz282 (@Enclosure.Real.IsNear.recentre' (Real.cos qz25) Bool.true 243808 262144 14652303 9133883392 7619 8192 14652303 9133883392 (ep70 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)) 151349 262144 1 262144 24079 65536 14652303 9133883392 3644332571 17179869184 1110490998719 1197196363956224 qz282 (@Enclosure.Real.IsNear.neg (Real.sin qz25) Bool.true 24079 65536 14652303 9133883392 (@Enclosure.Real.IsNear.recentre' (Real.sin qz25) Bool.true 96316 262144 14652303 9133883392 24079 65536 14652303 9133883392 (ep74 rfl rfl) rfl)) rfl)

noncomputable def ep76 := @ep49 1153128031 2147483648 1113060530597 1197196363956224 Bool.false 3644332571 17179869184 1110490998719 1197196363956224 Bool.false 42657555451614330880 19863972185 17179869184 154800302719 74824772747264 Bool.false 21427620427046322176 77953229 1073741824 154192710485 74824772747264 (ep50 (BSN.head_sum_c_succ qz6 2 3 rfl rfl) (ep64 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep65 ep75) rfl rfl

noncomputable abbrev qz283 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz30 := (@Inv.inv Real Real.instInv (Real.sqrt qz283))

noncomputable abbrev qz31 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep77 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)))) Bool.false 31683661759 68719476736 1924362280667 2394392727912448 Bool.true 6646741481 34359738368 959736781933 1197196363956224 (BSN.cpow_neg_s_mk qz17 54675 1000 4 qz18 rfl)

noncomputable def ep78 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz283) 524289 262144 1 262144 65535 65536 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz283) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz283 qz19)) Bool.false 524289 262144 1 262144 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz283 qz19)) Bool.false 524289 262144 1 262144 524289 262144 1 262144 (BSN.sqrt_enclosure 4 1 262144 262145 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep79 := nat_lit 753960950911045074462890625

noncomputable def ep80 := nat_lit 117048680082474133384580175

noncomputable def ep81 := BSN.log_dyadic_bound 3 5 12 11 ep79 131072 34843 ep80 431467934736729065175 181704 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 3) (BSN.artanhQ 5) 0 11 ep80 ep79 431467934736729065175 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep82 := nat_lit 2069145035626231119217371800643856

noncomputable def ep83 := BSN.cos_dyadic_bound_f 213278822 536870912 2 1 262144 69755 ep82 ep57 ep82 ep82 ep58 ep82 241729 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 213278822) qz269 0 1 ep82 ep57 ep82 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 213278822) qz270 0 1 ep82 ep58 ep82 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz32 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz284 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4967333) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz285 := (BSN.isNear_log_sfrac 4 1 181704 131072 1 34843 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 181704 131072 34843 rfl rfl rfl (ep81 rfl)))

noncomputable abbrev qz286 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep84 := @Enclosure.Real.IsNear.cos_image qz31 qz284 Bool.false 4967333 65536 103 65536 Bool.false 241729 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 49673331 655360 2187 1393720 4967333 65536 103 65536 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz32 54675 1000 0 1 181704 131072 1 34843 49673331 655360 2187 1393720 qz22 qz285 rfl) rfl) (Enclosure.sfrac_false_div 4967333 65536) (BSN.cos_reduce0 qz284 (@HDiv.hDiv Real Real Real qz2 qz274 qz286) 226375608064910080 72057594037927936 Bool.false 241729 262144 12 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 4967333 65536 226375608064910080 72057594037927936 12 3752040723591920091136 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 241729 262144 3752040723591920091136 9444732965739290427392 213278822 536870912 69755 69686 (ep83 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep85 := BSN.sin_dyadic_bound_f 213278822 536870912 2 1 262144 69755 ep82 ep71 ep82 ep82 ep72 ep82 101422 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 213278822) qz276 0 1 ep82 ep71 ep82 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 213278822) qz277 0 1 ep82 ep72 ep82 rfl rfl rfl rfl) rfl rfl

noncomputable def ep86 := @Enclosure.Real.IsNear.sin_image qz31 qz284 Bool.false 4967333 65536 103 65536 Bool.false 101422 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 49673331 655360 2187 1393720 4967333 65536 103 65536 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz32 54675 1000 0 1 181704 131072 1 34843 49673331 655360 2187 1393720 qz22 qz285 rfl) rfl) (Enclosure.sfrac_false_div 4967333 65536) (BSN.sin_reduce0 qz284 (@HDiv.hDiv Real Real Real qz2 qz274 qz286) 226375608064910080 72057594037927936 Bool.false 101422 262144 12 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 4967333 65536 226375608064910080 72057594037927936 12 3752040723591920091136 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 101422 262144 3752040723591920091136 9444732965739290427392 213278822 536870912 69755 69686 (ep85 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz287 := (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 131071 262144 1 262144 131071 262144 1 262144 (ep78 rfl rfl) rfl)

noncomputable def ep87 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31))) Bool.false 31683661759 68719476736 1924362280667 2394392727912448 Bool.true 6646741481 34359738368 959736781933 1197196363956224 (@Enclosure.Real.IsNear.mulLit_ff qz30 (Real.cos qz31) 131071 262144 1 262144 241729 262144 3654365 2283470848 31683661759 68719476736 1924362280667 2394392727912448 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz31) Bool.false 241729 262144 3654365 2283470848 241729 262144 3654365 2283470848 (ep84 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)) 131071 262144 1 262144 50711 131072 3654365 2283470848 6646741481 34359738368 959736781933 1197196363956224 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz31) Bool.false 50711 131072 3654365 2283470848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz31) Bool.false 101422 262144 3654365 2283470848 50711 131072 3654365 2283470848 (ep86 rfl rfl) rfl)) rfl)

noncomputable def ep88 := @ep47 31683661759 68719476736 1924362280667 2394392727912448 Bool.true 6646741481 34359738368 959736781933 1197196363956224 Bool.false 1909362938741381922816 111139550499 68719476736 6877971967675 2394392727912448 Bool.true 4458431768084611072 4152238153 34359738368 3426820149693 1197196363956224 (ep48 (BSN.head_sum_c_succ qz6 3 4 rfl rfl) (ep76 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep77 ep87) rfl rfl

noncomputable abbrev qz288 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt qz288))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep89 := @Enclosure.Complex.IsNear.of_eq qz10 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.false 30717328525 68719476736 1722821929205 2394392727912448 Bool.true 962382115 68719476736 1713978566747 2394392727912448 (BSN.cpow_neg_s_mk qz17 54675 1000 5 qz18 rfl)

noncomputable def ep90 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz288) 586171 262144 1 262144 58617 58618 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz288) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz288 qz19)) Bool.false 586171 262144 1 262144 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz288 qz19)) Bool.false 586171 262144 1 262144 586171 262144 1 262144 (BSN.sqrt_enclosure 5 1 293085 293086 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep91 := nat_lit 141613827518379161815574079375

noncomputable def ep92 := nat_lit 29325128709309236875766211300

noncomputable def ep93 := BSN.log_dyadic_bound 2 3 15 14 ep91 131072 34843 ep92 57299708096576225280000 210952 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP 2) (BSN.artanhQ 3) 0 14 ep92 ep91 57299708096576225280000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep94 := BSN.cos_dyadic_bound_f 16814882 536870912 1 0 262144 69755 0 1 1 0 1 1 262015 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 16814882) qz269 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 16814882) qz270 0 0 rfl) rfl rfl

noncomputable abbrev qz35 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz289 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 23067601) qz27)

noncomputable abbrev qz290 := (BSN.isNear_log_sfrac 5 1 210952 131072 1 34843 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 210952 131072 34843 rfl rfl rfl (ep93 rfl)))

noncomputable def ep95 := @Enclosure.Real.IsNear.cos_image qz34 qz289 Bool.false 23067601 262144 103 65536 Bool.false 262015 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 57669003 655360 2187 1393720 23067601 262144 103 65536 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz35 54675 1000 0 1 210952 131072 1 34843 57669003 655360 2187 1393720 qz22 qz290 rfl) rfl) (Enclosure.sfrac_false_div 23067601 262144) (BSN.cos_reduce0 qz289 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1183242142004860157952) qz29) 226375608064910080 72057594037927936 Bool.false 262015 262144 14 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 23067601 262144 226375608064910080 72057594037927936 14 1183242142004860157952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 262015 262144 1183242142004860157952 37778931862957161709568 16814882 536870912 69755 69686 (ep94 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep96 := BSN.sin_dyadic_bound_f 16814882 536870912 1 0 262144 69755 0 1 1 0 1 1 8209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 16814882) qz276 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 16814882) qz277 0 0 rfl) rfl rfl

noncomputable def ep97 := @Enclosure.Real.IsNear.sin_image qz34 qz289 Bool.false 23067601 262144 103 65536 Bool.false 8209 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 57669003 655360 2187 1393720 23067601 262144 103 65536 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz35 54675 1000 0 1 210952 131072 1 34843 57669003 655360 2187 1393720 qz22 qz290 rfl) rfl) (Enclosure.sfrac_false_div 23067601 262144) (BSN.sin_reduce0 qz289 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1183242142004860157952) qz29) 226375608064910080 72057594037927936 Bool.false 8209 262144 14 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 23067601 262144 226375608064910080 72057594037927936 14 1183242142004860157952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8209 262144 1183242142004860157952 37778931862957161709568 16814882 536870912 69755 69686 (ep96 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz291 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 117235 262144 1 262144 117235 262144 1 262144 (ep90 rfl rfl) rfl)

noncomputable def ep98 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.false 30717328525 68719476736 1722821929205 2394392727912448 Bool.true 962382115 68719476736 1713978566747 2394392727912448 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz34) 117235 262144 1 262144 262015 262144 3654365 2283470848 30717328525 68719476736 1722821929205 2394392727912448 qz291 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.false 262015 262144 3654365 2283470848 262015 262144 3654365 2283470848 (ep95 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 117235 262144 1 262144 8209 262144 3654365 2283470848 962382115 68719476736 1713978566747 2394392727912448 qz291 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.false 8209 262144 3654365 2283470848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.false 8209 262144 3654365 2283470848 8209 262144 3654365 2283470848 (ep97 rfl rfl) rfl)) rfl)

noncomputable def ep99 := @ep45 30717328525 68719476736 1722821929205 2394392727912448 Bool.true 962382115 68719476736 1713978566747 2394392727912448 Bool.false 9748330497931334385664 8866054939 4294967296 537549618555 149649545494528 Bool.true 318406830838857596928 9266858421 68719476736 8567618866133 2394392727912448 (ep46 (BSN.head_sum_c_succ qz6 4 5 rfl rfl) (ep88 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep89 ep98) rfl rfl

noncomputable abbrev qz292 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz292))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep100 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.true 5885698675 17179869184 789859839415 1197196363956224 Bool.false 476800855 2147483648 196790599721 299299090989056 (BSN.cpow_neg_s_mk qz17 54675 1000 6 qz18 rfl)

noncomputable abbrev qz293 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz19)

noncomputable def ep101 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz292) 642119 262144 1 262144 53509 53511 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz292) (Real.sqrt qz293) Bool.false 642119 262144 1 262144 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz293) Bool.false 642119 262144 1 262144 642119 262144 1 262144 (BSN.sqrt_enclosure 6 1 321059 321060 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep102 := BSN.log_dyadic_bound 2 10 4 3 105000000 131072 34843 1434560 960 53145 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz38 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep103 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz38 54675 1000 0 1 4034681531866359 2251799813685248 500000000034843 17421500000000000000 8823848510191727133 90071992547409920 1093500000076201641 696860000000000000000 qz22 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000034843 17421500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz293) Bool.false 8461340443916598509568 4722366482869645213696 1000000000069686 34843000000000000000 4034681531866359 2251799813685248 500000000034843 17421500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 53145 131072 24973259072661432 36028797018963968 34843 1000000000000000 rfl rfl rfl rfl (ep102 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep104 := nat_lit 9082949698864887280332404860121616

noncomputable def ep105 := BSN.cos_dyadic_bound_f 308714286 536870912 2 1 262144 69755 ep104 ep57 ep104 ep104 ep58 ep104 219985 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 308714286) qz269 0 1 ep104 ep57 ep104 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 308714286) qz270 0 1 ep104 ep58 ep104 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz294 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 25680779) qz27)

noncomputable def ep106 := @Enclosure.Real.IsNear.cos_image qz37 qz294 Bool.false 25680779 262144 103 65536 Bool.true 219985 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 8823848510191727133 90071992547409920 1093500000076201641 696860000000000000000 25680779 262144 103 65536 (ep103 rfl) rfl) (Enclosure.sfrac_false_div 25680779 262144) (BSN.cos_reduce2 qz294 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21723836684287027970048) qz29) 226375608064910080 72057594037927936 Bool.false 219985 262144 15 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q2 25680779 262144 226375608064910080 72057594037927936 15 21723836684287027970048 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 219985 262144 21723836684287027970048 37778931862957161709568 308714286 536870912 69755 69686 (ep105 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep107 := BSN.sin_dyadic_bound_f 308714286 536870912 2 1 262144 69755 ep104 ep71 ep104 ep104 ep72 ep104 142568 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 308714286) qz276 0 1 ep104 ep71 ep104 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 308714286) qz277 0 1 ep104 ep72 ep104 rfl rfl rfl rfl) rfl rfl

noncomputable def ep108 := @Enclosure.Real.IsNear.sin_image qz37 qz294 Bool.false 25680779 262144 103 65536 Bool.true 142568 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 8823848510191727133 90071992547409920 1093500000076201641 696860000000000000000 25680779 262144 103 65536 (ep103 rfl) rfl) (Enclosure.sfrac_false_div 25680779 262144) (BSN.sin_reduce2 qz294 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21723836684287027970048) qz29) 226375608064910080 72057594037927936 Bool.false 142568 262144 15 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q2 25680779 262144 226375608064910080 72057594037927936 15 21723836684287027970048 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 142568 262144 21723836684287027970048 37778931862957161709568 308714286 536870912 69755 69686 (ep107 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz295 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 107020 262144 2 262144 26755 65536 1 131072 (ep101 rfl rfl) rfl)

noncomputable def ep109 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.true 5885698675 17179869184 789859839415 1197196363956224 Bool.false 476800855 2147483648 196790599721 299299090989056 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz37) 26755 65536 1 131072 219985 262144 3654365 2283470848 5885698675 17179869184 789859839415 1197196363956224 qz295 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.true 219985 262144 3654365 2283470848 219985 262144 3654365 2283470848 (ep106 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 26755 65536 1 131072 17821 32768 3654365 2283470848 476800855 2147483648 196790599721 299299090989056 qz295 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.true 17821 32768 3654365 2283470848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.true 142568 262144 3654365 2283470848 17821 32768 3654365 2283470848 (ep108 rfl rfl) rfl)) rfl)

noncomputable def ep110 := @ep43 5885698675 17179869184 789859839415 1197196363956224 Bool.false 476800855 2147483648 196790599721 299299090989056 Bool.false 127038780706941566976 29578521081 17179869184 5090256787855 1197196363956224 Bool.false 12865078335448809472 5990768939 68719476736 10141943663901 2394392727912448 (ep44 (BSN.head_sum_c_succ qz6 5 6 rfl rfl) (ep99 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep100 ep109) rfl rfl

noncomputable abbrev qz296 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz39 := (@Inv.inv Real Real.instInv (Real.sqrt qz296))

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep111 := @Enclosure.Complex.IsNear.of_eq qz8 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)))) Bool.false 23695716555 68719476736 1456660049385 2394392727912448 Bool.false 5318172675 34359738368 726033783885 1197196363956224 (BSN.cpow_neg_s_mk qz17 54675 1000 7 qz18 rfl)

noncomputable abbrev qz297 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) qz19)

noncomputable def ep112 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz296) 693567 262144 1 262144 49540 49541 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz296) (Real.sqrt qz297) Bool.false 693567 262144 1 262144 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz297) Bool.false 693567 262144 1 262144 693567 262144 1 262144 (BSN.sqrt_enclosure 7 1 346783 346784 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep113 := BSN.log_dyadic_bound 3 11 5 4 202569142545 131072 34843 5259111624 688905 73349 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz41 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep114 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz41 54675 1000 0 1 4381783608859895 2251799813685248 500000000034843 17421500000000000000 1916592150515318073 18014398509481984 1093500000076201641 696860000000000000000 qz22 (BSN.isNear_log_sfrac 7 1 4381783608859895 2251799813685248 500000000034843 17421500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz297) Bool.false 9189266258887746519040 4722366482869645213696 1000000000069686 34843000000000000000 4381783608859895 2251799813685248 500000000034843 17421500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 73349 131072 24973259072661432 36028797018963968 34843 1000000000000000 rfl rfl rfl rfl (ep113 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep115 := nat_lit 36382368216788893696681882788925605779157313071028303815485291635056640000

noncomputable def ep116 := nat_lit 2504505714323359787184324207303086996185458423821189873137376790332288532480

noncomputable def ep117 := nat_lit 20948797015752781604417084142123108522472262990396670290276377600000000

noncomputable def ep118 := nat_lit 95253237753564455178235874882384577722089912474518248717229602051891200000

noncomputable def ep119 := nat_lit 45915938095928262765045943800556594930066737770055147674185241156091956428800

noncomputable def ep120 := BSN.sin_dyadic_bound_f 616800740 536870912 3 2 262144 69755 ep115 ep116 ep117 ep118 ep119 ep117 239155 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 616800740) qz276 0 2 ep115 ep116 ep117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 616800740) qz277 0 2 ep118 ep119 ep117 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz298 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13945043) qz20)

noncomputable def ep121 := @Enclosure.Real.IsNear.cos_image qz40 qz298 Bool.false 13945043 131072 103 65536 Bool.false 239155 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 1916592150515318073 18014398509481984 1093500000076201641 696860000000000000000 13945043 131072 103 65536 (ep114 rfl) rfl) (Enclosure.sfrac_false_div 13945043 131072) (BSN.cos_reduce3 qz298 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21701746751876498456576) qz275) 226375608064910080 72057594037927936 Bool.false 239155 262144 16 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q3 13945043 131072 226375608064910080 72057594037927936 16 21701746751876498456576 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 239155 262144 21701746751876498456576 18889465931478580854784 616800740 536870912 69755 69686 (ep120 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep122 := nat_lit 20221737363556386623314120253466280147764050489678122862065284853964800000

noncomputable def ep123 := nat_lit 278278412702595531909369356367009666242828713757909985904152976703587614720

noncomputable def ep124 := nat_lit 60623314496637654306733526592114594226247206943053575245615301806694400000

noncomputable def ep125 := nat_lit 12522528571616798935921621036515434980927292119105949365686883951661442662400

noncomputable def ep126 := BSN.cos_dyadic_bound_f 616800740 536870912 3 2 262144 69755 ep122 ep123 ep117 ep124 ep125 ep117 107350 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 616800740) qz269 0 2 ep122 ep123 ep117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 616800740) qz270 0 2 ep124 ep125 ep117 rfl rfl rfl rfl) rfl rfl

noncomputable def ep127 := @Enclosure.Real.IsNear.sin_image qz40 qz298 Bool.false 13945043 131072 103 65536 Bool.true 107350 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 1916592150515318073 18014398509481984 1093500000076201641 696860000000000000000 13945043 131072 103 65536 (ep114 rfl) rfl) (Enclosure.sfrac_false_div 13945043 131072) (BSN.sin_reduce3 qz298 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21701746751876498456576) qz275) 226375608064910080 72057594037927936 Bool.false 107350 262144 16 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q3 13945043 131072 226375608064910080 72057594037927936 16 21701746751876498456576 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 107350 262144 21701746751876498456576 18889465931478580854784 616800740 536870912 69755 69686 (ep126 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz299 := (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 99081 262144 1 262144 99081 262144 1 262144 (ep112 rfl rfl) rfl)

noncomputable def ep128 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40))) Bool.false 23695716555 68719476736 1456660049385 2394392727912448 Bool.false 5318172675 34359738368 726033783885 1197196363956224 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz40) 99081 262144 1 262144 239155 262144 3654365 2283470848 23695716555 68719476736 1456660049385 2394392727912448 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz40) Bool.false 239155 262144 3654365 2283470848 239155 262144 3654365 2283470848 (ep121 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)) 99081 262144 1 262144 53675 131072 3654365 2283470848 5318172675 34359738368 726033783885 1197196363956224 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz40) Bool.true 53675 131072 3654365 2283470848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz40) Bool.true 107350 262144 3654365 2283470848 53675 131072 3654365 2283470848 (ep127 rfl rfl) rfl)) rfl)

noncomputable def ep129 := @ep41 23695716555 68719476736 1456660049385 2394392727912448 Bool.false 5318172675 34359738368 726033783885 1197196363956224 Bool.false 2439709801947108212736 142009800879 68719476736 11637173625095 2394392727912448 Bool.false 571303296784874340352 16627114289 68719476736 11594011231671 2394392727912448 (ep42 (BSN.head_sum_c_succ qz6 6 7 rfl rfl) (ep110 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep111 ep128) rfl rfl

noncomputable abbrev qz300 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt qz300))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep130 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.false 10052614107 34359738368 684960718781 1197196363956224 Bool.true 6820422039 34359738368 682530489217 1197196363956224 (BSN.cpow_neg_s_mk qz17 54675 1000 8 qz18 rfl)

noncomputable abbrev qz301 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz19)

noncomputable def ep131 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz300) 741455 262144 1 262144 46340 46342 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz300) (Real.sqrt qz301) Bool.false 741455 262144 1 262144 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz301) Bool.false 741455 262144 1 262144 741455 262144 1 262144 (BSN.sqrt_enclosure 8 1 370727 370728 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep132 := BSN.log_dyadic_bound 0 16 1 0 1 131072 34843 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz44 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep133 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz44 54675 1000 0 1 9364972152248037 4503599627370496 1000000000104529 34843000000000000000 20481194096966456919 180143985094819840 2187000000228604923 1393720000000000000000 qz22 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000104529 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz301) Bool.false 9819885039515637645312 4722366482869645213696 1000000000104529 34843000000000000000 9364972152248037 4503599627370496 1000000000104529 34843000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 131072 24973259072661432 36028797018963968 34843 1000000000000000 rfl rfl rfl rfl (ep132 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep134 := nat_lit 10491686889909978527500210457249761

noncomputable def ep135 := BSN.cos_dyadic_bound_f 320045209 536870912 2 1 262144 69755 ep134 ep57 ep134 ep134 ep58 ep134 216927 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 320045209) qz269 0 1 ep134 ep57 ep134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 320045209) qz270 0 1 ep134 ep58 ep134 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz302 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7451015) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep136 := @Enclosure.Real.IsNear.cos_image qz43 qz302 Bool.false 7451015 65536 103 65536 Bool.false 216927 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 20481194096966456919 180143985094819840 2187000000228604923 1393720000000000000000 7451015 65536 103 65536 (ep133 rfl) rfl) (Enclosure.sfrac_false_div 7451015 65536) (BSN.cos_reduce0 qz302 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5630294870803055902720) qz286) 226375608064910080 72057594037927936 Bool.false 216927 262144 18 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 7451015 65536 226375608064910080 72057594037927936 18 5630294870803055902720 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 216927 262144 5630294870803055902720 9444732965739290427392 320045209 536870912 69755 69686 (ep135 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep137 := BSN.sin_dyadic_bound_f 320045209 536870912 2 1 262144 69755 ep134 ep71 ep134 ep134 ep72 ep134 147179 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 320045209) qz276 0 1 ep134 ep71 ep134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 320045209) qz277 0 1 ep134 ep72 ep134 rfl rfl rfl rfl) rfl rfl

noncomputable def ep138 := @Enclosure.Real.IsNear.sin_image qz43 qz302 Bool.false 7451015 65536 103 65536 Bool.false 147179 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 20481194096966456919 180143985094819840 2187000000228604923 1393720000000000000000 7451015 65536 103 65536 (ep133 rfl) rfl) (Enclosure.sfrac_false_div 7451015 65536) (BSN.sin_reduce0 qz302 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5630294870803055902720) qz286) 226375608064910080 72057594037927936 Bool.false 147179 262144 18 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 7451015 65536 226375608064910080 72057594037927936 18 5630294870803055902720 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 147179 262144 5630294870803055902720 9444732965739290427392 320045209 536870912 69755 69686 (ep137 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz303 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 92682 262144 2 262144 46341 131072 1 131072 (ep131 rfl rfl) rfl)

noncomputable def ep139 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.false 10052614107 34359738368 684960718781 1197196363956224 Bool.true 6820422039 34359738368 682530489217 1197196363956224 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz43) 46341 131072 1 131072 216927 262144 3654365 2283470848 10052614107 34359738368 684960718781 1197196363956224 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.false 216927 262144 3654365 2283470848 216927 262144 3654365 2283470848 (ep136 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 46341 131072 1 131072 147179 262144 3654365 2283470848 6820422039 34359738368 682530489217 1197196363956224 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.false 147179 262144 3654365 2283470848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.false 147179 262144 3654365 2283470848 147179 262144 3654365 2283470848 (ep138 rfl rfl) rfl)) rfl)

noncomputable def ep140 := @ep39 10052614107 34359738368 684960718781 1197196363956224 Bool.true 6820422039 34359738368 682530489217 1197196363956224 Bool.false 5570229985156188340224 162115029093 68719476736 13007095062657 2394392727912448 Bool.false 102607463146112155648 2986270211 68719476736 12959072210105 2394392727912448 (ep40 (BSN.head_sum_c_succ qz6 7 8 rfl rfl) (ep129 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep130 ep139) rfl rfl

theorem EMRow12.d6 : Enclosure.Complex.IsNear qz4 Bool.false 162115029093 68719476736 13007095062657 2394392727912448 Bool.false 2986270211 68719476736 12959072210105 2394392727912448 := ep38 (BSN.head_sum_c_succ qz6 8 9 rfl rfl) (ep140 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow12.d7 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow12.d8 : @Eq Nat (Nat.pow 11 1) 11 := @Eq.refl Nat 11

noncomputable def ep141 := nat_lit 449378323991225456003641059

noncomputable def ep142 := nat_lit 151658347075668097850408960

noncomputable def ep143 := nat_lit 4960936796659282028302930377630097

noncomputable def ep144 := nat_lit 552355464479786686842956688780165120

noncomputable abbrev qz455 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz435 := qz455

noncomputable abbrev qz304 := qz435

noncomputable abbrev qz45 := qz304

noncomputable abbrev qz46 := (@instHSub Real Real.instSub)

noncomputable abbrev qz436 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz305 := qz436

noncomputable abbrev qz47 := qz305

noncomputable abbrev qz456 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz457 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz437 := (@HAdd.hAdd Complex Complex Complex qz453 (@HAdd.hAdd Complex Complex Complex qz453 qz456 (@HMul.hMul Complex Complex Complex qz455 Complex.I (@HDiv.hDiv Complex Complex Complex qz457 (↑qz454) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz306 := qz437

noncomputable abbrev qz48 := (Complex.Stirling.logGammaStirling 1 qz306)

noncomputable abbrev qz438 := (@HAdd.hAdd Complex Complex Complex qz453 qz456 (@HMul.hMul Complex Complex Complex qz455 Complex.I (@HDiv.hDiv Complex Complex Complex qz457 (↑qz454) (2 : Complex))))

noncomputable abbrev qz307 := qz438

noncomputable abbrev qz49 := qz307

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz254 (@HDiv.hDiv Real Real Real qz257 qz267 (2 : Real)) (Real.log Real.pi))

noncomputable def ep145 := Complex.re (@HMul.hMul Complex Complex Complex qz45 (Complex.exp (@HMul.hMul Complex Complex Complex qz45 Complex.I ↑(@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50))) (zetaApproximant qz6 1 11))

noncomputable def ep146 := @Enclosure.Real.IsNear.of_eq ep145 (@HSub.hSub Real Real Real qz46 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.re (zetaApproximant qz6 1 11))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.im (zetaApproximant qz6 1 11))))

noncomputable def ep147 := nat_lit 449382112877789087583382299

noncomputable def ep148 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.re (zetaApproximant qz6 1 11))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.im (zetaApproximant qz6 1 11))) ep147

noncomputable def ep149 := nat_lit 1639470884001683065713944795644707

noncomputable def ep150 := nat_lit 184118488159928895614318896260055040

noncomputable def ep151 := nat_lit 3791458676891702446260224

noncomputable def ep152 := nat_lit 5315518081779103895136998836997

noncomputable def ep153 := nat_lit 69044433059973335855369586097520640

noncomputable def ep154 := nat_lit 1703799345703582453836356427373582654279421804937216

noncomputable def ep155 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.re (zetaApproximant qz6 1 11)) 262143 262144 399657

noncomputable def ep156 := nat_lit 60473233648195307160207360

noncomputable def ep157 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) Bool.false 262143 262144 399657

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8235431) qz27)

noncomputable def ep158 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) qz308 Bool.false 8235431 262144 11

noncomputable def ep159 := nat_lit 45669416960000000000000000

noncomputable def ep160 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) Bool.false 22637381395115341637 720575940379279360 30466737418881314978823 ep159

noncomputable def ep161 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50 45187117897176250181 720575940379279360 11416327168881314978823 ep159 164070927 5242880

noncomputable def ep162 := nat_lit 118685074168822322361794560

noncomputable def ep163 := nat_lit 11417354240000000000000000

noncomputable def ep164 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 7719148130166682991 180143985094819840 4916853200208347954193 ep163 Bool.false 45187117897176250181 720575940379279360

noncomputable def ep165 := @Enclosure.Complex.IsNear.subLitP qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 6527026788554766871 180143985094819840 4753013200105591766033 ep163 Bool.false 47411360278702150981 720575940379279360 10105607168835645561863

noncomputable def ep166 := nat_lit 34763952642636334471729079738433536

noncomputable def ep167 := nat_lit 12719042957729351943802655904628736

noncomputable abbrev qz458 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz439 := qz458

noncomputable abbrev qz309 := (@HSub.hSub Complex Complex Complex qz436 qz437 qz439)

noncomputable abbrev qz310 := (Complex.log qz437)

noncomputable abbrev qz51 := (@HSub.hSub Complex Complex Complex qz305 (@HMul.hMul Complex Complex Complex qz304 qz309 qz310) qz306)

noncomputable abbrev qz311 := qz439

noncomputable abbrev qz52 := (@HMul.hMul Complex Complex Complex qz304 qz311 ↑(Real.log qz258))

noncomputable abbrev qz440 := qz457

noncomputable abbrev qz312 := qz440

noncomputable abbrev qz53 := qz312

noncomputable abbrev qz54 := (@instHMul Nat instMulNat)

noncomputable abbrev qz441 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz313 := qz441

noncomputable abbrev qz55 := qz313

noncomputable abbrev qz56 := qz306

noncomputable abbrev qz314 := (@instHSub Int Int.instSub)

noncomputable abbrev qz57 := qz314

noncomputable abbrev qz315 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz58 := qz315

noncomputable abbrev qz316 := (@instHMul Int Int.instMul)

noncomputable abbrev qz59 := qz316

noncomputable abbrev qz317 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz60 := qz317

noncomputable def ep168 := @Enclosure.Complex.IsNear.of_eq qz48 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz51 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k)))))) Bool.true 6527026788554766871

noncomputable def ep169 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz51 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) Bool.true 6527071680609909271 180143985094819840

noncomputable def ep170 := nat_lit 14016683298479315407924625408

noncomputable def ep171 := nat_lit 407260483711798367576498634752

noncomputable def ep172 := @ep169 2320799438596666321 5574880000000000000000 Bool.false 47413542032582071621 720575940379279360 1233500000690692789 5574880000000000000000 Bool.false 535155 2147483648 3 2147483648 Bool.true 26008533 8589934592 729 42949672960 Bool.true ep170 6527026788554766871 180143985094819840 4753013200105591766033 ep163 Bool.false ep171

noncomputable def ep173 := @Enclosure.Complex.IsNear.addLitP qz51 qz52 Bool.true 6692612089703561751 180143985094819840 2257000000120103821 5574880000000000000000

noncomputable def ep174 := nat_lit 1711032678641804055937024

noncomputable def ep175 := @ep173 Bool.false 47413542032582071621 720575940379279360 1233500000690692789 5574880000000000000000 Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 Bool.true ep174 6527071680609909271 180143985094819840 2320799438596666321 5574880000000000000000 Bool.false 47413542032582071621 47413542032582071621 720575940379279360

noncomputable abbrev qz61 := (@HMul.hMul Complex Complex Complex qz304 qz309 qz310)

noncomputable def ep176 := @Enclosure.Complex.IsNear.subLitP qz61 qz56 Bool.true 6287288123240217111 180143985094819840 2257000000120103821 5574880000000000000000 Bool.false 13422457360540124225

noncomputable def ep177 := @ep176 144115188075855872 1233500000690692789 5574880000000000000000 Bool.false 9000 4000 0 1 Bool.false 109350 4000 0 1 Bool.true 26770448358814247004000 6692612089703561751 180143985094819840 2257000000120103821 5574880000000000000000 Bool.false 37930833626065657296800 47413542032582071621 720575940379279360 1233500000690692789 5574880000000000000000

noncomputable abbrev qz62 := qz309

noncomputable abbrev qz63 := qz310

noncomputable def ep178 := @Enclosure.Complex.IsNear.mul qz62 qz63 Bool.true 6287288123240217111 180143985094819840 2257000000120103821 5574880000000000000000 Bool.false 13422457360540124225 144115188075855872 1233500000690692789

noncomputable abbrev qz64 := (Complex.re qz309)

noncomputable abbrev qz65 := (Complex.re qz310)

noncomputable abbrev qz66 := (Complex.im qz309)

noncomputable abbrev qz67 := (Complex.im qz310)

noncomputable def ep179 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz64 qz65) (@HMul.hMul Real Real Real qz0 qz66 qz67) 208799879651795145 36028797018963968 3500000002195109 278744000000000000000 1832821880374798209 45035996273704960

noncomputable def ep180 := nat_lit 56630856897991173826013250151514112

noncomputable def ep181 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz65 7000 4000 0 1 29828554235970735 9007199254740992 500000000313587 69686000000000000000

noncomputable def ep182 := @Enclosure.Complex.IsNear.re_isNear qz62 Bool.false 7000 4000 0 1 Bool.false 109350 4000 0 1

noncomputable abbrev qz318 := (Enclosure.sfrac Bool.false 109350 4000)

noncomputable abbrev qz68 := qz318

noncomputable def ep183 := @Enclosure.Complex.IsNear.of_eq qz62 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz68) Bool.false 7000 4000 0 1 Bool.false 109350 4000 0

noncomputable abbrev qz319 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz69 := (Complex.mk qz319 qz318)

noncomputable def ep184 := @Enclosure.Complex.IsNear.of_eq qz63 (Complex.log qz69) Bool.false 29828554235970735 9007199254740992 500000000313587 69686000000000000000 Bool.false 838052985996707 562949953421312 1000000000034843 69686000000000000000

noncomputable def ep185 := nat_lit 7198118899495198482301104490827273502417115478515625000000000000

noncomputable def ep186 := nat_lit 88666360381038812025651597937558221558239990234375000000000000

noncomputable def ep187 := nat_lit 48577278221887598815059467817387202445068359375000000000000

noncomputable def ep188 := BSN.log_dyadic_bound 3846422500 20230422500 4 3 ep185 262144 69686 ep186 ep187 100911 24076845000 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3846422500) (BSN.artanhQ 20230422500) 0 3 ep186 ep185 ep187 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz70 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz320 := (Real.log (Enclosure.sfrac Bool.false 12038422500 16000000))

noncomputable abbrev qz321 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep189 := @Enclosure.Real.IsNear.mulLit_ff qz70 qz320 1 2 0 1 29828554235970735 4503599627370496 500000000313587 34843000000000000000 29828554235970735 9007199254740992 500000000313587 69686000000000000000 qz321 (BSN.isNear_log_sfrac 12038422500 16000000 29828554235970735 4503599627370496 500000000313587 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12038422500) qz322)) Bool.false 62555012173074498846720 9444732965739290427392 1000000000627174 69686000000000000000 29828554235970735 4503599627370496 500000000313587 34843000000000000000 (BSN.log_rat_reduce_isNear 12038422500 16000000 9 24076845000 16384000000 100911 262144 24973259072661432 36028797018963968 69686 1000000000000000 rfl rfl rfl rfl (ep188 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep190 := BSN.arctan_dyadic_bound_f 9000 109350 1 0 262144 69686 0 1 1 0 1 1 21526 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 109350) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 109350) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz254 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz72 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz321 BSN.pi_near_15 rfl)

noncomputable abbrev qz323 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 109350)))

noncomputable def ep191 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz323 884279719003555 562949953421312 1 2000000000000000 21526 262144 1 69686 219690561961120759808 838052985996707 562949953421312 1000000000034843 69686000000000000000 qz72 (ep190 rfl) rfl rfl

noncomputable abbrev qz324 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 109350) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep192 := @Enclosure.Complex.IsNear.re_isNear qz63 Bool.false 29828554235970735 9007199254740992 500000000313587 69686000000000000000 Bool.false 838052985996707 562949953421312 1000000000034843 69686000000000000000 (ep184 (@congrArg Complex Complex qz56 qz69 Complex.log (BSN.w_shift_mk qz17 Bool.false 54675 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz69) Bool.false 29828554235970735 9007199254740992 500000000313587 69686000000000000000 Bool.false 838052985996707 562949953421312 1000000000034843 69686000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz69)) (@HMul.hMul Real Real Real qz0 qz70 qz320) Bool.false 29828554235970735 9007199254740992 500000000313587 69686000000000000000 (Enclosure.clog_re_eq 9000 109350 4000 12038422500 16000000 rfl rfl rfl) (ep189 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz69)) qz324 Bool.false 838052985996707 562949953421312 1000000000034843 69686000000000000000 (Enclosure.clog_im_eq 9000 109350 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz324 (@HSub.hSub Real Real Real qz46 qz71 qz323) Bool.false 838052985996707 562949953421312 1000000000034843 69686000000000000000 (BSN.arctan_recip 109350 9000 rfl rfl) ep191))))

noncomputable def ep193 := @Enclosure.Real.IsNear.mulLit_ff qz66 qz67 109350 4000 0 1 838052985996707 562949953421312 1000000000034843 69686000000000000000

noncomputable def ep194 := @Enclosure.Complex.IsNear.im_isNear qz62 Bool.false 7000 4000 0 1 Bool.false 109350 4000 0 1

noncomputable def ep195 := @Enclosure.Complex.IsNear.im_isNear qz63 Bool.false 29828554235970735 9007199254740992 500000000313587 69686000000000000000 Bool.false 838052985996707 562949953421312 1000000000034843 69686000000000000000 (ep184 (@congrArg Complex Complex qz56 qz69 Complex.log (BSN.w_shift_mk qz17 Bool.false 54675 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz69) Bool.false 29828554235970735 9007199254740992 500000000313587 69686000000000000000 Bool.false 838052985996707 562949953421312 1000000000034843 69686000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz69)) (@HMul.hMul Real Real Real qz0 qz70 qz320) Bool.false 29828554235970735 9007199254740992 500000000313587 69686000000000000000 (Enclosure.clog_re_eq 9000 109350 4000 12038422500 16000000 rfl rfl rfl) (ep189 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz69)) qz324 Bool.false 838052985996707 562949953421312 1000000000034843 69686000000000000000 (Enclosure.clog_im_eq 9000 109350 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz324 (@HSub.hSub Real Real Real qz46 qz71 qz323) Bool.false 838052985996707 562949953421312 1000000000034843 69686000000000000000 (BSN.arctan_recip 109350 9000 rfl rfl) ep191))))

noncomputable abbrev qz325 := (Enclosure.Real.IsNear.const Bool.false 109350 4000)

noncomputable abbrev qz73 := (@ep183 1 (BSN.w_sub_half_mk qz267 Bool.false 54675 1000 2 qz268 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz318 Bool.false 7000 4000 0 1 Bool.false 109350 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz325))

noncomputable def ep196 := @ep179 2187000000076201641 5574880000000000000000 ep180 6287288123240217111 180143985094819840 2257000000120103821 5574880000000000000000 (@ep181 208799879651795145 36028797018963968 3500000002195109 278744000000000000000 (ep182 qz73) ep192 rfl) (@ep193 1832821880374798209 45035996273704960 2187000000076201641 5574880000000000000000 (ep194 qz73) ep195 rfl) rfl

noncomputable def ep197 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz64 qz67) (@HMul.hMul Real Real Real qz0 qz66 qz65) 5866370901976949 2251799813685248 7000000000243901 278744000000000000000 13047009622813599489 144115188075855872

noncomputable def ep198 := nat_lit 30224686983662437370247168969932800

noncomputable def ep199 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz67 7000 4000 0 1 838052985996707 562949953421312 1000000000034843 69686000000000000000

noncomputable def ep200 := @Enclosure.Real.IsNear.mulLit_ff qz66 qz65 109350 4000 0 1 29828554235970735 9007199254740992 500000000313587 69686000000000000000

noncomputable def ep201 := @ep197 1093500000685814769 5574880000000000000000 ep198 13422457360540124225 144115188075855872 1233500000690692789 5574880000000000000000 (@ep199 5866370901976949 2251799813685248 7000000000243901 278744000000000000000 (ep182 qz73) ep195 rfl) (@ep200 13047009622813599489 144115188075855872 1093500000685814769 5574880000000000000000 (ep194 qz73) ep192 rfl) rfl

noncomputable def ep202 := @Enclosure.Complex.IsNear.of_eq qz56 qz69 Bool.false 9000 4000 0 1 Bool.false 109350 4000 0 1 (BSN.w_shift_mk qz17 Bool.false 54675 1000 2 qz18 rfl)

noncomputable abbrev qz326 := (ep202 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 109350 4000) Bool.false 9000 4000 0 1 Bool.false 109350 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 109350 4000)))

noncomputable abbrev qz74 := qz326

noncomputable def ep203 := ep177 (@ep178 5574880000000000000000 (ep196 rfl) (ep201 rfl)) qz74 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz75 := qz311

noncomputable def ep204 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz75) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz75) (Complex.im ↑qz3)) 240893 262144 3 262144 0 1 0 1 240893 240893

noncomputable def ep205 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz75) (Complex.re ↑qz3) 1 2 0 1 240893 131072 3 131072 240893 262144 3 262144

noncomputable abbrev qz76 := (@Enclosure.Complex.IsNear.of_eq qz311 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz265) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz265 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz321 qz279))

noncomputable def ep206 := ep205 (@Enclosure.Complex.IsNear.re_isNear qz75 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz76) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 240893 131072 3 131072 (Complex.ofReal_re qz3) EMRow12.d4)

noncomputable def ep207 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz75) (Complex.im ↑qz3) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep208 := ep207 (@Enclosure.Complex.IsNear.im_isNear qz75 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz76) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz23)

noncomputable def ep209 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz75) (Complex.im ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz75) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep210 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz75) (Complex.im ↑qz3) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep211 := ep210 (@Enclosure.Complex.IsNear.re_isNear qz75 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz76) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz23)

noncomputable def ep212 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz75) (Complex.re ↑qz3) 0 1 0 1 240893 131072 3 131072 0 1 0 1

noncomputable def ep213 := ep212 (@Enclosure.Complex.IsNear.im_isNear qz75 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz76) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 240893 131072 3 131072 (Complex.ofReal_re qz3) EMRow12.d4)

noncomputable def ep214 := @ep175 1233500000690692789 5574880000000000000000 (ep203 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz75 (↑qz3) Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 (@ep204 262144 3 262144 (ep206 rfl) (ep208 rfl) rfl rfl) (@ep209 1 0 1 (ep211 rfl) (ep213 rfl) rfl rfl))

noncomputable abbrev qz77 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz327 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz78 := (@HMul.hMul Complex Complex Complex qz304 (@HMul.hMul Complex Complex Complex qz304 (2 : Complex) qz327) (@HSub.hSub Complex Complex Complex qz305 (@HMul.hMul Complex Complex Complex qz304 (2 : Complex) qz327) (1 : Complex)))

noncomputable abbrev qz328 := (@HPow.hPow Complex Int Complex qz441 qz437 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz79 := qz328

noncomputable def ep215 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz79)) Bool.false 535155 2147483648 3 2147483648

noncomputable def ep216 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz79) Bool.false 0 1 0 1 Bool.false

noncomputable def ep217 := @ep216 0 1 0 1 Bool.false 535155 2147483648 3 2147483648 Bool.true 26008533 8589934592 729 42949672960 Bool.false 535155 535155 2147483648 3 2147483648 Bool.true 26008533 26008533 8589934592 729

noncomputable def ep218 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep219 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz79 Bool.false 535155 2147483648 3 2147483648 Bool.true 26008533 8589934592 729 42949672960

noncomputable abbrev qz80 := (Complex.re qz328)

noncomputable abbrev qz81 := (Complex.im qz328)

noncomputable def ep220 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz80) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz81) 535155 2147483648 3 2147483648 0 1 0

noncomputable def ep221 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz80 1 12 0 1 1605465 536870912 9 536870912 535155

noncomputable def ep222 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz82 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz265 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz279)

noncomputable def ep223 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep222 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz82)

noncomputable def ep224 := @Enclosure.Complex.IsNear.re_isNear qz79 Bool.false 1605465 536870912 9 536870912 Bool.true 78025599 2147483648 2187 10737418240

noncomputable abbrev qz442 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz329 := (@HPow.hPow Complex Nat Complex qz442 qz437 1)

noncomputable abbrev qz83 := (@Inv.inv Complex Complex.instInv qz329)

noncomputable def ep225 := @Enclosure.Complex.IsNear.of_eq qz79 qz83 Bool.false 1605465 536870912 9 536870912 Bool.true 78025599 2147483648 2187

noncomputable def ep226 := @Enclosure.Complex.IsNear.of_parts qz83 Bool.false 1605465 536870912 9 536870912 Bool.true 78025599 2147483648 2187

noncomputable abbrev qz84 := (Complex.re qz329)

noncomputable abbrev qz85 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz86 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz87 := qz329

noncomputable def ep227 := @Enclosure.Real.IsNear.mulLit_ff qz84 (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz87)) 9000 4000 0 1 178385 134217728 1 134217728

noncomputable def ep228 := @Enclosure.Complex.IsNear.re_isNear qz87 Bool.false 9000 4000 0 1 Bool.false 109350 4000 0 1

noncomputable def ep229 := @Enclosure.Complex.IsNear.of_eq qz87 qz56 Bool.false 9000 4000 0 1 Bool.false 109350 4000 0

noncomputable def ep230 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz87)) Bool.false 178385 134217728 1 134217728 178385 134217728 1

noncomputable abbrev qz88 := (@instHAdd Real Real.instAdd)

noncomputable abbrev qz89 := (Complex.im qz329)

noncomputable def ep231 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz87) (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 qz84 qz84) (@HMul.hMul Real Real Real qz0 qz89 qz89)) Bool.false 4815369 6400 0 1

noncomputable def ep232 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz84 qz84) (@HMul.hMul Real Real Real qz0 qz89 qz89) 81 16 0 1 4782969 6400

noncomputable def ep233 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz84 9000 4000 0 1 9000 4000 0 1

noncomputable def ep234 := @Enclosure.Real.IsNear.mulLit_ff qz89 qz89 109350 4000 0 1 109350 4000 0 1

noncomputable def ep235 := @Enclosure.Complex.IsNear.im_isNear qz87 Bool.false 9000 4000 0 1 Bool.false 109350 4000 0 1

noncomputable abbrev qz90 := (ep228 (@ep229 1 (BSN.pow_one_c qz306) qz326))

noncomputable abbrev qz91 := (ep235 (@ep229 1 (BSN.pow_one_c qz306) qz326))

noncomputable def ep236 := @ep232 0 1 77045904 4815369 6400 0 1 (@ep233 81 16 0 1 qz90 qz90 rfl) (@ep234 4782969 6400 0 1 qz91 qz91 rfl)

noncomputable def ep237 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz87) 4815369 6400 0 1 89192 89193 67108864 (ep231 (Enclosure.Complex.normSq_eq_mul_add_mul qz87) (ep236 rfl rfl)) rfl

noncomputable def ep238 := @Enclosure.Real.IsNear.of_eq (Complex.re qz83) (@HMul.hMul Real Real Real qz0 qz84 (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz87))) Bool.false 1605465 536870912 9 536870912 (Enclosure.Complex.inv_re_eq_mul qz87) (@ep227 1605465 536870912 9 536870912 qz90 (@ep230 134217728 (ep237 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep239 := @Enclosure.Real.IsNear.of_eq (Complex.im qz83) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz89) (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz87))) Bool.true 78025599 2147483648 2187 10737418240 (Enclosure.Complex.inv_im_eq_mul qz87)

noncomputable def ep240 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz89) (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz87)) 109350 4000 0 1 178385 134217728 1

noncomputable def ep241 := @ep240 134217728 78025599 2147483648 2187 10737418240 (@Enclosure.Real.IsNear.neg qz89 Bool.false 109350 4000 0 1 qz91) (@ep230 134217728 (ep237 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep242 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz81 0 1 0 1 78025599 2147483648 2187 10737418240 0

noncomputable def ep243 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep222 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz82)

noncomputable def ep244 := @Enclosure.Complex.IsNear.im_isNear qz79 Bool.false 1605465 536870912 9 536870912 Bool.true 78025599 2147483648 2187 10737418240

noncomputable abbrev qz92 := (@ep225 10737418240 (BSN.zpow_one_sub_two_mul qz306 1 1 rfl rfl) (@ep226 10737418240 ep238 (ep239 ep241)))

noncomputable def ep245 := @ep220 1 535155 535155 2147483648 3 2147483648 (@ep221 2147483648 3 2147483648 ep223 (ep224 qz92) rfl) (@ep242 1 0 1 ep243 (ep244 qz92) rfl) rfl

noncomputable def ep246 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz81) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz80) 26008533 8589934592 729 42949672960 0 1 0

noncomputable def ep247 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz81 1 12 0 1 78025599 2147483648 2187 10737418240 26008533

noncomputable def ep248 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz80 0 1 0 1 1605465 536870912 9 536870912 0

noncomputable def ep249 := @ep246 1 26008533 26008533 8589934592 729 42949672960 (@ep247 8589934592 729 42949672960 ep223 (ep244 qz92) rfl) (@ep248 1 0 1 ep243 (ep224 qz92) rfl) rfl

noncomputable abbrev qz93 := (@Enclosure.Complex.IsNear.mk qz265 qz265 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz279 qz279)

noncomputable def ep250 := @ep217 42949672960 (@ep218 0 1 0 1 (BSN.stirling_sum_base qz56) qz93) (ep219 (ep245 rfl) (ep249 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep251 := @ep172 47411360278702150981 720575940379279360 10105607168835645561863 ep159 (ep214 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep215 Bool.true 26008533 8589934592 729 42949672960 (BSN.stirling_sum_succ qz56 0 1 rfl) (ep250 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep252 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz17 2) Bool.false 29803033540297903 4503599627370496 500000000313587 34843000000000000000 Bool.false 868844680283555 281474976710656

noncomputable abbrev qz94 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz260 qz307 qz327))

noncomputable def ep253 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 1) qz94) Bool.false 29803033540297903 4503599627370496 500000000313587 34843000000000000000 Bool.false 868844680283555 281474976710656 1000000000034843 34843000000000000000

noncomputable def ep254 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 1) qz94 Bool.false 29798523824637103 9007199254740992 500000000313587 69686000000000000000 Bool.false 879132200699299 562949953421312 1000000000034843 69686000000000000000 Bool.false

noncomputable def ep255 := nat_lit 536883722986384120536913571479552

noncomputable def ep256 := nat_lit 978232144591964007725080248320

noncomputable abbrev qz95 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz260 qz307 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep257 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 0) qz95) Bool.false 29798523824637103 9007199254740992 500000000313587 69686000000000000000 Bool.false 879132200699299 562949953421312 1000000000034843 69686000000000000000

noncomputable def ep258 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 0) qz95 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz330 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz68))

noncomputable def ep259 := @Enclosure.Complex.IsNear.of_eq qz95 qz330 Bool.false 29798523824637103 9007199254740992 500000000313587 69686000000000000000 Bool.false 879132200699299 562949953421312 1000000000034843 69686000000000000000

noncomputable def ep260 := nat_lit 7029011249967002376767502993856513620620240478515625000000000000

noncomputable def ep261 := nat_lit 83617072260347751317293567745249349105114990234375000000000000

noncomputable def ep262 := nat_lit 42821854600050969641451703263118374320068359375000000000000

noncomputable def ep263 := BSN.log_dyadic_bound 3766422500 20150422500 4 3 ep260 262144 69686 ep261 ep262 99163 23916845000 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3766422500) (BSN.artanhQ 20150422500) 0 3 ep261 ep260 ep262 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep264 := @Enclosure.Real.IsNear.mulLit_ff qz70 (Real.log (Enclosure.sfrac Bool.false 11958422500 16000000)) 1 2 0 1 29798523824637103 4503599627370496 500000000313587 34843000000000000000 29798523824637103 9007199254740992 500000000313587 69686000000000000000 qz321 (BSN.isNear_log_sfrac 11958422500 16000000 29798523824637103 4503599627370496 500000000313587 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11958422500) qz322)) Bool.false 62492033835885349830656 9444732965739290427392 1000000000627174 69686000000000000000 29798523824637103 4503599627370496 500000000313587 34843000000000000000 (BSN.log_rat_reduce_isNear 11958422500 16000000 9 23916845000 16384000000 99163 262144 24973259072661432 36028797018963968 69686 1000000000000000 rfl rfl rfl rfl (ep263 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep265 := BSN.arctan_dyadic_bound_f 1000 109350 1 0 262144 69686 0 1 1 0 1 1 2397 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 109350) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 109350) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz331 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz332 := (@Nat.cast Real Real.instNatCast 109350)

noncomputable def ep266 := @Enclosure.Real.IsNear.subLit_ff_p qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz331 qz332)) 884279719003555 562949953421312 1 2000000000000000 2397 262144 1 69686 230459231620117037056 879132200699299 562949953421312 1000000000034843 69686000000000000000 qz72 (ep265 rfl) rfl rfl

noncomputable abbrev qz96 := (@HAdd.hAdd Complex Complex Complex qz260 qz307 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz333 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz68)

noncomputable def ep267 := @ep258 29798523824637103 9007199254740992 500000000313587 69686000000000000000 Bool.false 879132200699299 562949953421312 1000000000034843 69686000000000000000 Bool.false 29798523824637103 29798523824637103 9007199254740992 500000000313587 69686000000000000000 Bool.false 879132200699299 879132200699299 562949953421312 1000000000034843 69686000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz17) qz93) (ep259 (@congrArg Complex Complex qz96 qz333 Complex.log (BSN.w_shift_mk qz17 Bool.false 54675 1000 0 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz330 Bool.false 29798523824637103 9007199254740992 500000000313587 69686000000000000000 Bool.false 879132200699299 562949953421312 1000000000034843 69686000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz330) (@HMul.hMul Real Real Real qz0 qz70 (Real.log (Enclosure.sfrac Bool.false 11958422500 16000000))) Bool.false 29798523824637103 9007199254740992 500000000313587 69686000000000000000 (Enclosure.clog_re_eq 1000 109350 4000 11958422500 16000000 rfl rfl rfl) (ep264 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz330) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz332 qz331)) Bool.false 879132200699299 562949953421312 1000000000034843 69686000000000000000 (Enclosure.clog_im_eq 1000 109350 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz332 qz331)) (@HSub.hSub Real Real Real qz46 qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz331 qz332))) Bool.false 879132200699299 562949953421312 1000000000034843 69686000000000000000 (BSN.arctan_recip 109350 1000 rfl rfl) ep266)))) rfl rfl

noncomputable abbrev qz334 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz68))

noncomputable def ep268 := @Enclosure.Complex.IsNear.of_eq qz94 qz334 Bool.false 29807543255958703 9007199254740992 500000000313587 69686000000000000000 Bool.false 858557159867811 562949953421312 1000000000034843 69686000000000000000

noncomputable def ep269 := nat_lit 7079392142757839581788676259131148897659302978515625000000000000

noncomputable def ep270 := nat_lit 85109307732683054052515221975524098341052490234375000000000000

noncomputable def ep271 := nat_lit 44485347480174966571162120087586522757568359375000000000000

noncomputable def ep272 := BSN.log_dyadic_bound 3790422500 20174422500 4 3 ep269 262144 69686 ep270 ep271 99688 23964845000 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3790422500) (BSN.artanhQ 20174422500) 0 3 ep270 ep269 ep271 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep273 := @Enclosure.Real.IsNear.mulLit_ff qz70 (Real.log (Enclosure.sfrac Bool.false 11982422500 16000000)) 1 2 0 1 29807543255958703 4503599627370496 500000000313587 34843000000000000000 29807543255958703 9007199254740992 500000000313587 69686000000000000000 qz321 (BSN.isNear_log_sfrac 11982422500 16000000 29807543255958703 4503599627370496 500000000313587 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11982422500) qz322)) Bool.false 62510948954320305913856 9444732965739290427392 1000000000627174 69686000000000000000 29807543255958703 4503599627370496 500000000313587 34843000000000000000 (BSN.log_rat_reduce_isNear 11982422500 16000000 9 23964845000 16384000000 99688 262144 24973259072661432 36028797018963968 69686 1000000000000000 rfl rfl rfl rfl (ep272 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep274 := BSN.arctan_dyadic_bound_f 5000 109350 1 0 262144 69686 0 1 1 0 1 1 11978 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 109350) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 109350) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz335 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep275 := @Enclosure.Real.IsNear.subLit_ff_p qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz335 qz332)) 884279719003555 562949953421312 1 2000000000000000 11978 262144 1 69686 225065608116387446784 858557159867811 562949953421312 1000000000034843 69686000000000000000 qz72 (ep274 rfl) rfl rfl

noncomputable abbrev qz97 := (@HAdd.hAdd Complex Complex Complex qz260 qz307 qz327)

noncomputable abbrev qz336 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz68)

noncomputable def ep276 := @ep254 29807543255958703 9007199254740992 500000000313587 69686000000000000000 Bool.false 858557159867811 562949953421312 1000000000034843 69686000000000000000 Bool.false ep255 29803033540297903 4503599627370496 500000000313587 34843000000000000000 Bool.false ep256 868844680283555 281474976710656 1000000000034843 34843000000000000000 (ep257 (BSN.log_sum_c_succ qz17 0 1 rfl) (ep267 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep268 (@congrArg Complex Complex qz97 qz336 Complex.log (BSN.w_shift_mk qz17 Bool.false 54675 1000 1 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz334 Bool.false 29807543255958703 9007199254740992 500000000313587 69686000000000000000 Bool.false 858557159867811 562949953421312 1000000000034843 69686000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz334) (@HMul.hMul Real Real Real qz0 qz70 (Real.log (Enclosure.sfrac Bool.false 11982422500 16000000))) Bool.false 29807543255958703 9007199254740992 500000000313587 69686000000000000000 (Enclosure.clog_re_eq 5000 109350 4000 11982422500 16000000 rfl rfl rfl) (ep273 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz334) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz332 qz335)) Bool.false 858557159867811 562949953421312 1000000000034843 69686000000000000000 (Enclosure.clog_im_eq 5000 109350 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz332 qz335)) (@HSub.hSub Real Real Real qz46 qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz335 qz332))) Bool.false 858557159867811 562949953421312 1000000000034843 69686000000000000000 (BSN.arctan_recip 109350 5000 rfl rfl) ep275)))) rfl rfl

noncomputable def ep277 := @ep165 ep159 Bool.false 29803033540297903 4503599627370496 500000000313587 34843000000000000000 Bool.false 868844680283555 281474976710656 1000000000034843 34843000000000000000 Bool.true ep166 7719148130166682991 180143985094819840 4916853200208347954193 ep163 Bool.false ep167 45187117897176250181 720575940379279360 11416327168881314978823 ep159 (@ep168 180143985094819840 4753013200105591766033 ep163 Bool.false 47411360278702150981 720575940379279360 10105607168835645561863 ep159 (BSN.logGammaStirling_unfold 1 qz56) (ep251 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep252 1000000000034843 34843000000000000000 (BSN.log_sum_c_eq qz17 2) (ep253 (BSN.log_sum_c_succ qz17 1 2 rfl) (ep276 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz98 := (@HDiv.hDiv Real Real Real qz257 qz267 (2 : Real))

noncomputable def ep278 := @Enclosure.Real.IsNear.mulLit_ff qz98 (Real.log Real.pi) 54675 2000 0 1 75021 65536 1 65536 164070927 5242880 2187 5242880 (@Enclosure.Real.IsNear.of_eq qz98 (Enclosure.sfrac Bool.false 54675 2000) Bool.false 54675 2000 0 1 (BSN.t_half_eq qz17 Bool.false 54675 1000 qz18) (Enclosure.Real.IsNear.const Bool.false 54675 2000)) EMRow12.d5 rfl

noncomputable def ep279 := @ep161 2187 5242880 ep162 22637381395115341637 720575940379279360 30466737418881314978823 ep159 (@ep164 11416327168881314978823 ep159 (ep277 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep278 rfl rfl

noncomputable def ep280 := nat_lit 127237822880449064559847920709735984120364733814490181503875821491898078625

noncomputable def ep281 := nat_lit 255484216388668625335583195619938899691717399221973961232485187027785121

noncomputable def ep282 := nat_lit 332828275955594467501439324304019104953835331820162517525298365985497601441

noncomputable def ep283 := BSN.sin_dyadic_bound_f 843180413 536870912 3 2 262144 69755 ep280 ep116 ep281 ep282 ep119 ep281 262143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 843180413) qz276 0 2 ep280 ep116 ep281 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 843180413) qz277 0 2 ep282 ep119 ep281 rfl rfl rfl rfl) rfl rfl

noncomputable def ep284 := @ep158 16384 Bool.false 262143 262144 1 34843 (@ep160 8235431 262144 11 16384 ep279 rfl) (Enclosure.sfrac_false_div 8235431 262144) (BSN.cos_reduce3 qz308 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59333546839945827581952) qz29) 226375608064910080 72057594037927936 Bool.false 262143 262144 4 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q3 8235431 262144 226375608064910080 72057594037927936 4 59333546839945827581952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 262143 262144 59333546839945827581952 37778931862957161709568 843180413 536870912 69755 69686 (ep283 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep285 := nat_lit 7559154206024413395025920

noncomputable abbrev qz99 := qz261

noncomputable abbrev qz100 := qz262

noncomputable abbrev qz443 := (@Nat.cast Complex Complex.instNatCast 11)

noncomputable abbrev qz337 := (@HPow.hPow Complex Complex Complex qz430 qz443 qz431)

noncomputable abbrev qz101 := qz337

noncomputable abbrev qz338 := qz443

noncomputable abbrev qz102 := (@HAdd.hAdd Complex Complex Complex qz260 (@HDiv.hDiv Complex Complex Complex qz312 qz338 (@HSub.hSub Complex Complex Complex qz305 qz259 (1 : Complex))) qz311)

noncomputable abbrev qz103 := (@instHSub Nat instSubNat)

noncomputable abbrev qz339 := qz442

noncomputable abbrev qz104 := qz339

noncomputable abbrev qz105 := qz338

noncomputable def ep286 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz6 1 11) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 11, @HPow.hPow Complex Complex Complex qz99 (@Nat.cast Complex Complex.instNatCast n) qz100) (@HMul.hMul Complex Complex Complex qz45 qz101 (@HAdd.hAdd Complex Complex Complex qz5 qz102 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) Bool.false 5142789769833134063279 1735592045696274923520 412743795705959150742037

noncomputable def ep287 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 11, @HPow.hPow Complex Complex Complex qz99 (@Nat.cast Complex Complex.instNatCast n) qz100) (@HMul.hMul Complex Complex Complex qz45 qz101 (@HAdd.hAdd Complex Complex Complex qz5 qz102 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) Bool.false 199992727613 68719476736 15511716199025 2394392727912448

noncomputable def ep288 := nat_lit 353409821946186850863470392377344

noncomputable def ep289 := nat_lit 250356059677714738176029884416

noncomputable def ep290 := @ep287 Bool.true 8811064433 34359738368 1932057200649 299299090989056 Bool.false 91735778608741983119 1735592045696274923520 20976970216989150354037 ep156 Bool.false 11258171570282386993 72316335237344788480 2622789213575269037023 ep285 Bool.false ep288 5142789769833134063279 1735592045696274923520 412743795705959150742037 ep156 Bool.true ep289 7286320314676114887 72316335237344788480

noncomputable def ep291 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 11, @HPow.hPow Complex Complex Complex qz99 (@Nat.cast Complex Complex.instNatCast n) qz100) (BSN.headSumC qz6 11) Bool.false 199992727613 68719476736 15511716199025 2394392727912448 Bool.true 8811064433 34359738368 1932057200649

noncomputable abbrev qz106 := (BSN.headSumC qz259 10)

noncomputable abbrev qz107 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 10) qz262)

noncomputable def ep292 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 11) (@HAdd.hAdd Complex Complex Complex qz5 qz106 qz107) Bool.false 199992727613 68719476736 15511716199025 2394392727912448 Bool.true 8811064433 34359738368 1932057200649 299299090989056

noncomputable def ep293 := @Enclosure.Complex.IsNear.addLitP qz106 qz107 Bool.false 178832936775 68719476736 14291064184823 2394392727912448 Bool.true 12672929275 68719476736 14242619174483 2394392727912448 Bool.false

noncomputable abbrev qz108 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 9) qz262)

noncomputable def ep294 := @Enclosure.Complex.IsNear.of_eq qz106 (@HAdd.hAdd Complex Complex Complex qz5 qz4 qz108) Bool.false 178832936775 68719476736 14291064184823 2394392727912448 Bool.true 12672929275 68719476736 14242619174483 2394392727912448

noncomputable def ep295 := @Enclosure.Complex.IsNear.addLitP qz4 qz108 Bool.false 162115029093 68719476736 13007095062657 2394392727912448 Bool.false 2986270211 68719476736 12959072210105 2394392727912448 Bool.false

noncomputable abbrev qz340 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz109 := (@Inv.inv Real Real.instInv (Real.sqrt qz340))

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep296 := @Enclosure.Complex.IsNear.of_eq qz108 (Complex.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz110)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110)))) Bool.false 8358953841 34359738368 641984561083 1197196363956224 Bool.true 7829599743 34359738368 641773482189 1197196363956224 (BSN.cpow_neg_s_mk qz17 54675 1000 9 qz18 rfl)

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9) qz19)

noncomputable def ep297 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz340) 786433 262144 1 262144 43690 43691 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz340) (Real.sqrt qz341) Bool.false 786433 262144 1 262144 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz341) Bool.false 786433 262144 1 262144 786433 262144 1 262144 (BSN.sqrt_enclosure 9 1 393216 393217 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep298 := BSN.log_dyadic_bound 1 17 2 1 867 131072 34843 1 1 15438 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz111 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep299 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz111 54675 1000 0 1 9895417793173221 4503599627370496 1000000000104529 34843000000000000000 21641278713669834327 180143985094819840 2187000000228604923 1393720000000000000000 qz22 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000104529 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 10376097607894403383296 4722366482869645213696 1000000000104529 34843000000000000000 9895417793173221 4503599627370496 1000000000104529 34843000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 15438 131072 24973259072661432 36028797018963968 34843 1000000000000000 rfl rfl rfl rfl (ep298 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep300 := nat_lit 26667628035559440939589826954666401

noncomputable def ep301 := BSN.cos_dyadic_bound_f 404106743 536870912 2 1 262144 69755 ep300 ep57 ep300 ep300 ep58 ep300 191322 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 404106743) qz269 0 1 ep300 ep57 ep300 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 404106743) qz270 0 1 ep300 ep58 ep300 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 31492205) qz27)

noncomputable def ep302 := @Enclosure.Real.IsNear.cos_image qz110 qz342 Bool.false 31492205 262144 103 65536 Bool.false 191322 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz110 Bool.false 21641278713669834327 180143985094819840 2187000000228604923 1393720000000000000000 31492205 262144 103 65536 (ep299 rfl) rfl) (Enclosure.sfrac_false_div 31492205 262144) (BSN.cos_reduce0 qz342 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28436484055256782602240) qz29) 226375608064910080 72057594037927936 Bool.false 191322 262144 19 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 31492205 262144 226375608064910080 72057594037927936 19 28436484055256782602240 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 191322 262144 28436484055256782602240 37778931862957161709568 404106743 536870912 69755 69686 (ep301 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep303 := BSN.sin_dyadic_bound_f 404106743 536870912 2 1 262144 69755 ep300 ep71 ep300 ep300 ep72 ep300 179206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 404106743) qz276 0 1 ep300 ep71 ep300 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 404106743) qz277 0 1 ep300 ep72 ep300 rfl rfl rfl rfl) rfl rfl

noncomputable def ep304 := @Enclosure.Real.IsNear.sin_image qz110 qz342 Bool.false 31492205 262144 103 65536 Bool.false 179206 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz110 Bool.false 21641278713669834327 180143985094819840 2187000000228604923 1393720000000000000000 31492205 262144 103 65536 (ep299 rfl) rfl) (Enclosure.sfrac_false_div 31492205 262144) (BSN.sin_reduce0 qz342 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28436484055256782602240) qz29) 226375608064910080 72057594037927936 Bool.false 179206 262144 19 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 31492205 262144 226375608064910080 72057594037927936 19 28436484055256782602240 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 179206 262144 28436484055256782602240 37778931862957161709568 404106743 536870912 69755 69686 (ep303 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz343 := (@Enclosure.Real.IsNear.recentre' qz109 Bool.false 87381 262144 1 262144 87381 262144 1 262144 (ep297 rfl rfl) rfl)

noncomputable def ep305 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz110)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110))) Bool.false 8358953841 34359738368 641984561083 1197196363956224 Bool.true 7829599743 34359738368 641773482189 1197196363956224 (@Enclosure.Real.IsNear.mulLit_ff qz109 (Real.cos qz110) 87381 262144 1 262144 95661 131072 3654365 2283470848 8358953841 34359738368 641984561083 1197196363956224 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz110) Bool.false 191322 262144 3654365 2283470848 95661 131072 3654365 2283470848 (ep302 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110)) 87381 262144 1 262144 89603 131072 3654365 2283470848 7829599743 34359738368 641773482189 1197196363956224 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz110) Bool.false 89603 131072 3654365 2283470848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz110) Bool.false 179206 262144 3654365 2283470848 89603 131072 3654365 2283470848 (ep304 rfl rfl) rfl)) rfl)

noncomputable def ep306 := @ep295 8358953841 34359738368 641984561083 1197196363956224 Bool.true 7829599743 34359738368 641773482189 1197196363956224 Bool.false 6144652919170085683200 178832936775 68719476736 14291064184823 2394392727912448 Bool.true 435438534245167923200 12672929275 68719476736 14242619174483 2394392727912448 EMRow12.d6 (ep296 ep305) rfl rfl

noncomputable abbrev qz344 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz112 := (@Inv.inv Real Real.instInv (Real.sqrt qz344))

noncomputable abbrev qz113 := (@HMul.hMul Real Real Real qz254 qz267 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep307 := @Enclosure.Complex.IsNear.of_eq qz107 (Complex.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz113)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz113)))) Bool.false 10579895419 34359738368 610326007101 1197196363956224 Bool.true 4949199591 68719476736 1213838430709 2394392727912448 (BSN.cpow_neg_s_mk qz17 54675 1000 10 qz18 rfl)

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10) qz19)

noncomputable def ep308 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz344) 828973 262144 1 262144 41448 41449 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz344) (Real.sqrt qz345) Bool.false 828973 262144 1 262144 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz345) Bool.false 828973 262144 1 262144 828973 262144 1 262144 (BSN.sqrt_enclosure 10 1 414486 414487 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep309 := BSN.log_dyadic_bound 2 18 3 2 1574640 131072 34843 6528 48 29247 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz114 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep310 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz114 54675 1000 0 1 10369891420296933 4503599627370496 1000000000104529 34843000000000000000 22678952536189392471 180143985094819840 2187000000228604923 1393720000000000000000 qz22 (BSN.isNear_log_sfrac 10 1 10369891420296933 4503599627370496 1000000000104529 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false 10873619265929276817408 4722366482869645213696 1000000000104529 34843000000000000000 10369891420296933 4503599627370496 1000000000104529 34843000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 29247 131072 24973259072661432 36028797018963968 34843 1000000000000000 rfl rfl rfl rfl (ep309 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep311 := nat_lit 231547959564651294132825588670641

noncomputable def ep312 := BSN.cos_dyadic_bound_f 123355989 536870912 2 1 262144 69755 ep311 ep57 ep311 ep311 ep58 ep311 255254 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 123355989) qz269 0 1 ep311 ep57 ep311 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 123355989) qz270 0 1 ep311 ep58 ep311 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz346 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 33002219) qz27)

noncomputable def ep313 := @Enclosure.Real.IsNear.cos_image qz113 qz346 Bool.false 33002219 262144 103 65536 Bool.false 255254 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 22678952536189392471 180143985094819840 2187000000228604923 1393720000000000000000 33002219 262144 103 65536 (ep310 rfl) rfl) (Enclosure.sfrac_false_div 33002219 262144) (BSN.cos_reduce0 qz346 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8680406060161059258368) qz29) 226375608064910080 72057594037927936 Bool.false 255254 262144 20 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 33002219 262144 226375608064910080 72057594037927936 20 8680406060161059258368 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 255254 262144 8680406060161059258368 37778931862957161709568 123355989 536870912 69755 69686 (ep312 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep314 := BSN.sin_dyadic_bound_f 123355989 536870912 2 1 262144 69755 ep311 ep71 ep311 ep311 ep72 ep311 59703 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 123355989) qz276 0 1 ep311 ep71 ep311 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 123355989) qz277 0 1 ep311 ep72 ep311 rfl rfl rfl rfl) rfl rfl

noncomputable def ep315 := @Enclosure.Real.IsNear.sin_image qz113 qz346 Bool.false 33002219 262144 103 65536 Bool.false 59703 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 22678952536189392471 180143985094819840 2187000000228604923 1393720000000000000000 33002219 262144 103 65536 (ep310 rfl) rfl) (Enclosure.sfrac_false_div 33002219 262144) (BSN.sin_reduce0 qz346 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8680406060161059258368) qz29) 226375608064910080 72057594037927936 Bool.false 59703 262144 20 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 33002219 262144 226375608064910080 72057594037927936 20 8680406060161059258368 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 59703 262144 8680406060161059258368 37778931862957161709568 123355989 536870912 69755 69686 (ep314 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz347 := (@Enclosure.Real.IsNear.recentre' qz112 Bool.false 82897 262144 1 262144 82897 262144 1 262144 (ep308 rfl rfl) rfl)

noncomputable def ep316 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz113)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz113))) Bool.false 10579895419 34359738368 610326007101 1197196363956224 Bool.true 4949199591 68719476736 1213838430709 2394392727912448 (@Enclosure.Real.IsNear.mulLit_ff qz112 (Real.cos qz113) 82897 262144 1 262144 127627 131072 3654365 2283470848 10579895419 34359738368 610326007101 1197196363956224 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz113) Bool.false 255254 262144 3654365 2283470848 127627 131072 3654365 2283470848 (ep313 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz112 (@Neg.neg Real Real.instNeg (Real.sin qz113)) 82897 262144 1 262144 59703 262144 3654365 2283470848 4949199591 68719476736 1213838430709 2394392727912448 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz113) Bool.false 59703 262144 3654365 2283470848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz113) Bool.false 59703 262144 3654365 2283470848 59703 262144 3654365 2283470848 (ep315 rfl rfl) rfl)) rfl)

noncomputable def ep317 := @ep293 10579895419 34359738368 610326007101 1197196363956224 Bool.true 4949199591 68719476736 1213838430709 2394392727912448 Bool.false 6871697796285369155584 199992727613 68719476736 15511716199025 2394392727912448 Bool.true 1210983474645881061376 8811064433 34359738368 1932057200649 299299090989056 (ep294 (BSN.head_sum_c_succ qz6 9 10 rfl rfl) (ep306 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep307 ep316) rfl rfl

noncomputable def ep318 := @Enclosure.Complex.IsNear.mul qz101 (@HAdd.hAdd Complex Complex Complex qz5 qz102 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 91735778608741983119 1735592045696274923520 20976970216989150354037 ep156 Bool.false

noncomputable abbrev qz115 := (Complex.re qz337)

noncomputable abbrev qz116 := (Complex.im qz337)

noncomputable def ep319 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz115 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz102 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz116 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz102 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 2186315907970165717 21694900571203436544 184049971237508241929

noncomputable def ep320 := nat_lit 20157744549398435720069120

noncomputable def ep321 := nat_lit 663399531912862814973792352727478566912

noncomputable def ep322 := @Enclosure.Real.IsNear.mulLit_ff qz115 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz102 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 3449182921 17179869184 290361523277 598598181978112 633864877

noncomputable abbrev qz348 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz117 := (@Inv.inv Real Real.instInv (Real.sqrt qz348))

noncomputable abbrev qz349 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz434 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable abbrev qz118 := (Real.cos qz349)

noncomputable abbrev qz119 := (@Neg.neg Real Real.instNeg (Real.sin qz349))

noncomputable def ep323 := @Enclosure.Complex.IsNear.of_eq qz101 (Complex.mk (@HMul.hMul Real Real Real qz0 qz117 qz118) (@HMul.hMul Real Real Real qz0 qz117 qz119)) Bool.false 3449182921 17179869184 290361523277 598598181978112 Bool.false 15457894347 68719476736 1162178388439 2394392727912448 (BSN.cpow_neg_s_mk qz17 54675 1000 11 qz18 rfl)

noncomputable abbrev qz350 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11) qz19)

noncomputable def ep324 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz348) 869433 262144 1 262144 39519 39520 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz348) (Real.sqrt qz350) Bool.false 869433 262144 1 262144 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz350) Bool.false 869433 262144 1 262144 869433 262144 1 262144 (BSN.sqrt_enclosure 11 1 434716 434717 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep325 := BSN.log_dyadic_bound 3 19 3 2 1954815 131072 34843 16488 243 41740 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 19) 0 2 16488 1954815 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz351 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz120 := qz351

noncomputable abbrev qz352 := (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11) qz19))

noncomputable def ep326 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz120 54675 1000 0 1 10799147631728357 4503599627370496 1000000000104529 34843000000000000000 23617735870589916759 180143985094819840 2187000000228604923 1393720000000000000000 qz22 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 1000000000104529 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz352 Bool.false 11323727027087193669632 4722366482869645213696 1000000000104529 34843000000000000000 10799147631728357 4503599627370496 1000000000104529 34843000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 41740 131072 24973259072661432 36028797018963968 34843 1000000000000000 rfl rfl rfl rfl (ep325 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep327 := nat_lit 23421583345590454551249359055721201

noncomputable def ep328 := BSN.sin_dyadic_bound_f 391204699 536870912 2 1 262144 69755 ep327 ep71 ep327 ep327 ep72 ep327 174556 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 391204699) qz276 0 1 ep327 ep71 ep327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 391204699) qz277 0 1 ep327 ep72 ep327 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz121 := qz349

noncomputable abbrev qz353 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 34368329) qz27)

noncomputable def ep329 := @Enclosure.Real.IsNear.cos_image qz121 qz353 Bool.false 34368329 262144 103 65536 Bool.false 174556 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 23617735870589916759 180143985094819840 2187000000228604923 1393720000000000000000 34368329 262144 103 65536 (ep326 rfl) rfl) (Enclosure.sfrac_false_div 34368329 262144) (BSN.cos_reduce3 qz353 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 27528583440765160521728) qz29) 226375608064910080 72057594037927936 Bool.false 174556 262144 20 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q3 34368329 262144 226375608064910080 72057594037927936 20 27528583440765160521728 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 174556 262144 27528583440765160521728 37778931862957161709568 391204699 536870912 69755 69686 (ep328 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep330 := BSN.cos_dyadic_bound_f 391204699 536870912 2 1 262144 69755 ep327 ep57 ep327 ep327 ep58 ep327 195573 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 391204699) qz269 0 1 ep327 ep57 ep327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 391204699) qz270 0 1 ep327 ep58 ep327 rfl rfl rfl rfl) rfl rfl

noncomputable def ep331 := @Enclosure.Real.IsNear.sin_image qz121 qz353 Bool.false 34368329 262144 103 65536 Bool.true 195573 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 23617735870589916759 180143985094819840 2187000000228604923 1393720000000000000000 34368329 262144 103 65536 (ep326 rfl) rfl) (Enclosure.sfrac_false_div 34368329 262144) (BSN.sin_reduce3 qz353 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 27528583440765160521728) qz29) 226375608064910080 72057594037927936 Bool.false 195573 262144 20 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q3 34368329 262144 226375608064910080 72057594037927936 20 27528583440765160521728 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 195573 262144 27528583440765160521728 37778931862957161709568 391204699 536870912 69755 69686 (ep330 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz122 := (Real.sin qz349)

noncomputable abbrev qz354 := (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 79039 262144 1 262144 79039 262144 1 262144 (ep324 rfl rfl) rfl)

noncomputable def ep332 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz117 qz118) (@HMul.hMul Real Real Real qz0 qz117 qz119) Bool.false 3449182921 17179869184 290361523277 598598181978112 Bool.false 15457894347 68719476736 1162178388439 2394392727912448 (@Enclosure.Real.IsNear.mulLit_ff qz117 qz118 79039 262144 1 262144 43639 65536 3654365 2283470848 3449182921 17179869184 290361523277 598598181978112 qz354 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 174556 262144 3654365 2283470848 43639 65536 3654365 2283470848 (ep329 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz117 qz119 79039 262144 1 262144 195573 262144 3654365 2283470848 15457894347 68719476736 1162178388439 2394392727912448 qz354 (@Enclosure.Real.IsNear.neg qz122 Bool.true 195573 262144 3654365 2283470848 (@Enclosure.Real.IsNear.recentre' qz122 Bool.true 195573 262144 3654365 2283470848 195573 262144 3654365 2283470848 (ep331 rfl rfl) rfl)) rfl)

noncomputable def ep333 := @ep322 1262809416 0 1 2186315907970165717 21694900571203436544 184049971237508241929 755915420602441339502592 (@Enclosure.Complex.IsNear.re_isNear qz101 Bool.false 3449182921 17179869184 290361523277 598598181978112 Bool.false 15457894347 68719476736 1162178388439 2394392727912448 (ep323 ep332))

noncomputable def ep334 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz102 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 633864877 1262809416 0 1 Bool.false

noncomputable def ep335 := @Enclosure.Complex.IsNear.addLitP qz102 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) Bool.false 4765769 9566738 0 1 Bool.true 962280

noncomputable def ep336 := @ep335 4783369 0 1 Bool.false 1 264 0 1 Bool.false 729 1760 0 1 Bool.false 1267729754 633864877 1262809416 0 1 Bool.false 1793463201 1793463201 8418729440 0 1

noncomputable abbrev qz123 := (@HDiv.hDiv Complex Complex Complex qz312 qz338 (@HSub.hSub Complex Complex Complex qz305 qz259 (1 : Complex)))

noncomputable def ep337 := @Enclosure.Complex.IsNear.addLitP qz123 qz75 Bool.true 22000000 11958422500 0 1 Bool.true 2405700000 11958422500 0 1

noncomputable def ep338 := @Enclosure.Complex.IsNear.of_eq qz123 (Complex.mk (Enclosure.sfrac Bool.true 22000000 11958422500) (Enclosure.sfrac Bool.true 2405700000 11958422500)) Bool.true 22000000 11958422500 0 1 Bool.true 2405700000 11958422500 0 1

noncomputable def ep339 := @ep337 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 11914422500 4765769 9566738 0 1 Bool.true 2405700000 962280 4783369 0 1 (ep338 (BSN.N_div_s_sub_one_mk qz17 54675 1000 11 qz18 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 22000000 11958422500) (Enclosure.sfrac Bool.true 2405700000 11958422500) Bool.true 22000000 11958422500 0 1 Bool.true 2405700000 11958422500 0 1 (Enclosure.Real.IsNear.const Bool.true 22000000 11958422500) (Enclosure.Real.IsNear.const Bool.true 2405700000 11958422500))) qz76 rfl

noncomputable abbrev qz124 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz355 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz442 qz443 1))

noncomputable abbrev qz125 := qz355

noncomputable def ep340 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz125)) Bool.false 1 264 0 1

noncomputable def ep341 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz125) Bool.false 0 1 0 1 Bool.false

noncomputable def ep342 := @ep341 0 1 0 1 Bool.false 1 264 0 1 Bool.false 729 1760 0 1 Bool.false 1 1 264 0 1 Bool.false 729 729 1760 0

noncomputable def ep343 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep344 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz125 Bool.false 1 264 0 1 Bool.false 729 1760 0 1

noncomputable abbrev qz126 := (Complex.re qz355)

noncomputable abbrev qz127 := (Complex.im qz355)

noncomputable def ep345 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127) 1 264 0 1 0 1 0

noncomputable def ep346 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126 1 24 0 1 1 11 0 1 1

noncomputable def ep347 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep348 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep349 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow12.d7 rfl) qz82

noncomputable def ep350 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz6 Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 (BSN.ascPochhammer_one_eval qz6)

noncomputable def ep351 := ep350 (@Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk qz70 qz17) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 (BSN.s_crit_mk qz17 Bool.false 54675 1000 qz18) (@Enclosure.Complex.IsNear.mk qz70 qz17 Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 qz321 qz22))

noncomputable def ep352 := @ep348 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep351)

noncomputable def ep353 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 54675 1000 0 1 0 1 0

noncomputable def ep354 := @ep353 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep351)

noncomputable def ep355 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 729 160 0 1 0 1 0 1 729

noncomputable def ep356 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 54675 1000 0 1 729 160 0

noncomputable def ep357 := @ep356 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep351)

noncomputable def ep358 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep359 := @ep358 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep351)

noncomputable def ep360 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 729 160 0 1 (@ep347 1 24 0 1 (ep352 rfl) (ep354 rfl) rfl rfl) (@ep355 729 160 0 1 (ep357 rfl) (ep359 rfl) rfl rfl)

noncomputable def ep361 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 729 160 0 1 ep360

noncomputable abbrev qz128 := (@Enclosure.Complex.IsNear.of_eq qz355 (Complex.mk (Enclosure.sfrac Bool.false 1 11) qz265) Bool.false 1 11 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 11 1 11 EMRow12.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 11) qz265 Bool.false 1 11 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 11) qz279))

noncomputable def ep362 := @ep346 264 0 1 ep361 (@Enclosure.Complex.IsNear.re_isNear qz125 Bool.false 1 11 0 1 Bool.false 0 1 0 1 qz128)

noncomputable def ep363 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127 729 160 0 1 0 1 0 1 0

noncomputable def ep364 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 729 160 0 1 ep360

noncomputable def ep365 := @ep363 1 0 1 ep364 (@Enclosure.Complex.IsNear.im_isNear qz125 Bool.false 1 11 0 1 Bool.false 0 1 0 1 qz128)

noncomputable def ep366 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126) 0 1 0 1 729 1760 0

noncomputable def ep367 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz127 1 24 0 1 0 1 0 1 0

noncomputable def ep368 := @ep367 1 0 1 ep361 (@Enclosure.Complex.IsNear.im_isNear qz125 Bool.false 1 11 0 1 Bool.false 0 1 0 1 qz128)

noncomputable def ep369 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz126 729 160 0 1 1 11 0 1 729

noncomputable def ep370 := @ep369 1760 0 1 ep364 (@Enclosure.Complex.IsNear.re_isNear qz125 Bool.false 1 11 0 1 Bool.false 0 1 0 1 qz128)

noncomputable def ep371 := @ep342 1 (@ep343 0 1 0 1 (BSN.bern_sum_base qz6 11) qz93) (ep344 (@ep345 1 1 1 264 0 1 (ep362 rfl) (ep365 rfl) rfl rfl) (@ep366 1 729 729 1760 0 1 (ep368 rfl) (ep370 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep372 := ep336 (ep339 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep340 Bool.false 729 1760 0 1 (BSN.bern_sum_succ qz6 11 0 1 1 rfl rfl) (ep371 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep373 := @Enclosure.Real.IsNear.mulLit_ff qz116 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz102 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 15457894347 68719476736 1162178388439 2394392727912448 1793463201

noncomputable def ep374 := @ep373 8418729440 0 1 27723164676290424747 578530681898758307840 2084324172662830333239 ep320 (@Enclosure.Complex.IsNear.im_isNear qz101 Bool.false 3449182921 17179869184 290361523277 598598181978112 Bool.false 15457894347 68719476736 1162178388439 2394392727912448 (ep323 ep332))

noncomputable def ep375 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz102 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 633864877 1262809416 0 1 Bool.false

noncomputable def ep376 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz115 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz102 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz116 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz102 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 6185982642331190121 144632670474689576960 520752706983604429677

noncomputable def ep377 := nat_lit 5039436137349608930017280

noncomputable def ep378 := nat_lit 3023661682409765358010368

noncomputable def ep379 := nat_lit 651319767548868393924522599778470592512

noncomputable def ep380 := @Enclosure.Real.IsNear.mulLit_ff qz115 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz102 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 3449182921 17179869184 290361523277 598598181978112 1793463201

noncomputable def ep381 := @ep380 8418729440 0 1 6185982642331190121 144632670474689576960 520752706983604429677 ep377 (@Enclosure.Complex.IsNear.re_isNear qz101 Bool.false 3449182921 17179869184 290361523277 598598181978112 Bool.false 15457894347 68719476736 1162178388439 2394392727912448 (ep323 ep332))

noncomputable def ep382 := @Enclosure.Real.IsNear.mulLit_ff qz116 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz102 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz105 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 15457894347 68719476736 1162178388439 2394392727912448 633864877

noncomputable def ep383 := @ep382 1262809416 0 1 3266072099646716773 28926534094937915392 736664061239944957003 ep378 (@Enclosure.Complex.IsNear.im_isNear qz101 Bool.false 3449182921 17179869184 290361523277 598598181978112 Bool.false 15457894347 68719476736 1162178388439 2394392727912448 (ep323 ep332))

noncomputable abbrev qz356 := (ep372 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep384 := @ep318 11258171570282386993 72316335237344788480 2622789213575269037023 ep285 (@ep319 755915420602441339502592 27723164676290424747 578530681898758307840 2084324172662830333239 ep320 ep321 91735778608741983119 1735592045696274923520 20976970216989150354037 ep156 (ep333 (@ep334 1793463201 8418729440 0 1 qz356) rfl) (ep374 (@ep375 1793463201 8418729440 0 1 qz356) rfl) rfl rfl) (@ep376 ep377 3266072099646716773 28926534094937915392 736664061239944957003 ep378 ep379 11258171570282386993 72316335237344788480 2622789213575269037023 ep285 (ep381 (@ep375 1793463201 8418729440 0 1 qz356) rfl) (ep383 (@ep334 1793463201 8418729440 0 1 qz356) rfl) rfl rfl)

noncomputable def ep385 := @ep290 51419189718178439256703 ep285 (@ep291 299299090989056 (BSN.head_sum_c_eq qz6 11) (ep292 (BSN.head_sum_c_succ qz6 10 11 rfl rfl) (ep317 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep384 rfl rfl rfl

noncomputable def ep386 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz6 1 11) Bool.false 5142789769833134063279 1735592045696274923520 412743795705959150742037 ep156 Bool.true 7286320314676114887 72316335237344788480 51419189718178439256703 ep285 (@ep286 ep156 Bool.true 7286320314676114887 72316335237344788480 51419189718178439256703 ep285 (BSN.zetaApproximant_eq_folded' qz6 1 11 rfl) (ep385 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep387 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.im (zetaApproximant qz6 1 11)) 65 262144 399657

noncomputable def ep388 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) Bool.true 65 262144 399657

noncomputable def ep389 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) qz308 Bool.false 8235431 262144 11

noncomputable def ep390 := nat_lit 70801227918644444144509104036795519577843393185482089262701005356400170401

noncomputable def ep391 := nat_lit 211892715323155995182856145719146680934146744758002319865638045695144940961

noncomputable def ep392 := BSN.cos_dyadic_bound_f 843180413 536870912 3 2 262144 69755 ep390 ep123 ep281 ep391 ep125 ep281 65 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 843180413) qz269 0 2 ep390 ep123 ep281 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 843180413) qz270 0 2 ep391 ep125 ep281 rfl rfl rfl rfl) rfl rfl

noncomputable def ep393 := @ep389 16384 Bool.true 65 262144 1 34843 (@ep160 8235431 262144 11 16384 ep279 rfl) (Enclosure.sfrac_false_div 8235431 262144) (BSN.sin_reduce3 qz308 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59333546839945827581952) qz29) 226375608064910080 72057594037927936 Bool.false 65 262144 4 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q3 8235431 262144 226375608064910080 72057594037927936 4 59333546839945827581952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 65 262144 59333546839945827581952 37778931862957161709568 843180413 536870912 69755 69686 (ep392 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep394 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz6 1 11) Bool.false 5142789769833134063279 1735592045696274923520 412743795705959150742037 ep156 Bool.true 7286320314676114887 72316335237344788480 51419189718178439256703 ep285 (@ep286 ep156 Bool.true 7286320314676114887 72316335237344788480 51419189718178439256703 ep285 (BSN.zetaApproximant_eq_folded' qz6 1 11 rfl) (ep385 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow12.d9 : Enclosure.Real.IsNear (hardyZApproximantEM 1 11 qz17) Bool.false ep141 ep142 ep143 ep144 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 11 qz17) ep145 Bool.false ep141 ep142 ep143 ep144 (@Eq.refl Real ep145) (@ep146 Bool.false ep141 ep142 ep143 ep144 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) (zetaApproximant qz6 1 11)) (@ep148 ep142 ep149 ep150 94722164090789493531 ep151 ep152 ep153 ep154 ep141 ep142 ep143 ep144 (@ep155 570867712 5142789769833134063279 1735592045696274923520 412743795705959150742037 ep156 ep147 ep142 ep149 ep150 (@ep157 570867712 262143 262144 399657 570867712 (ep284 rfl rfl) rfl) ep386 rfl) (@ep387 570867712 7286320314676114887 72316335237344788480 51419189718178439256703 ep285 94722164090789493531 ep151 ep152 ep153 (@ep388 570867712 65 262144 399657 570867712 (ep393 rfl rfl) rfl) ep394 rfl) rfl rfl))

noncomputable abbrev qz459 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 57545 1000)))

noncomputable abbrev qz444 := qz459

noncomputable abbrev qz357 := qz444

noncomputable abbrev qz129 := (BSN.headSumC qz357 9)

noncomputable abbrev qz130 := qz357

noncomputable abbrev qz445 := (@Neg.neg Complex Complex.instNeg qz459)

noncomputable abbrev qz358 := qz445

noncomputable abbrev qz131 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 8) qz358)

noncomputable def ep395 := @Enclosure.Complex.IsNear.of_eq qz129 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz130 8) qz131) Bool.false 75050675517 68719476736 13656127261219 2394392727912448 Bool.false 10086898337 68719476736 13655738692083 2394392727912448

noncomputable def ep396 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz130 8) qz131 Bool.false 51707230905 68719476736 12212724515039 2394392727912448 Bool.false 16823118779 68719476736 12224822631813 2394392727912448 Bool.false

noncomputable abbrev qz132 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 7) qz358)

noncomputable def ep397 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz130 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz130 7) qz132) Bool.false 51707230905 68719476736 12212724515039 2394392727912448 Bool.false 16823118779 68719476736 12224822631813 2394392727912448

noncomputable def ep398 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz130 7) qz132 Bool.false 40399512699 68719476736 10684469940329 2394392727912448 Bool.true 3279849989 34359738368 5346160852925 1197196363956224 Bool.false

noncomputable abbrev qz133 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 6) qz358)

noncomputable def ep399 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz130 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz130 6) qz133) Bool.false 40399512699 68719476736 10684469940329 2394392727912448 Bool.true 3279849989 34359738368 5346160852925 1197196363956224

noncomputable def ep400 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz130 6) qz133 Bool.false 64081754459 68719476736 9022622174629 2394392727912448 Bool.false 4240231371 34359738368 4518050612011 1197196363956224 Bool.true

noncomputable abbrev qz134 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 5) qz358)

noncomputable def ep401 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz130 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz130 5) qz134) Bool.false 64081754459 68719476736 9022622174629 2394392727912448 Bool.false 4240231371 34359738368 4518050612011 1197196363956224

noncomputable def ep402 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz130 5) qz134 Bool.false 8248191703 8589934592 902312128967 299299090989056 Bool.true 11096451329 34359738368 3611712787043 1197196363956224 Bool.true

noncomputable abbrev qz135 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 4) qz358)

noncomputable def ep403 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz130 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz130 4) qz135) Bool.false 8248191703 8589934592 902312128967 299299090989056 Bool.true 11096451329 34359738368 3611712787043 1197196363956224

noncomputable def ep404 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz130 4) qz135 Bool.false 19332366633 17179869184 1299767251335 598598181978112 Bool.true 27312817591 34359738368 2599195724181 1197196363956224 Bool.true

noncomputable abbrev qz136 := (@HPow.hPow Complex Complex Complex qz261 qz263 qz358)

noncomputable def ep405 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz130 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz130 3) qz136) Bool.false 19332366633 17179869184 1299767251335 598598181978112 Bool.true 27312817591 34359738368 2599195724181 1197196363956224

noncomputable def ep406 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz130 3) qz136 Bool.false 2537392189 4294967296 715560894971 598598181978112 Bool.true 1238370543 2147483648 716642352005 598598181978112 Bool.false

noncomputable abbrev qz137 := (@HPow.hPow Complex Complex Complex qz261 qz264 qz358)

noncomputable def ep407 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz130 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz130 2) qz137) Bool.false 2537392189 4294967296 715560894971 598598181978112 Bool.true 1238370543 2147483648 716642352005 598598181978112

noncomputable def ep408 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz130 2) qz137 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep409 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz130 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz130)

noncomputable abbrev qz460 := (Enclosure.sfrac Bool.false 57545 1000)

noncomputable abbrev qz446 := qz460

noncomputable abbrev qz359 := qz446

noncomputable abbrev qz138 := (@HMul.hMul Real Real Real qz254 qz359 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz139 := qz359

noncomputable abbrev qz360 := (@Eq.refl Real qz446)

noncomputable abbrev qz140 := qz360

noncomputable def ep410 := @Enclosure.Complex.IsNear.of_eq qz137 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz138)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz138)))) Bool.true 1757575107 4294967296 715560894971 598598181978112 Bool.true 1238370543 2147483648 716642352005 598598181978112 (BSN.cpow_neg_s_mk qz139 57545 1000 2 qz140 rfl)

noncomputable def ep411 := nat_lit 12052437497006881671176740203042576

noncomputable def ep412 := BSN.sin_dyadic_bound_f 331336074 536870912 2 1 262144 69755 ep411 ep71 ep411 ep411 ep72 ep411 151708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 331336074) qz276 0 1 ep411 ep71 ep411 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 331336074) qz277 0 1 ep411 ep72 ep411 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz361 := (Enclosure.Real.IsNear.const Bool.false 57545 1000)

noncomputable abbrev qz141 := qz361

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2614039) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep413 := @Enclosure.Real.IsNear.cos_image qz138 qz362 Bool.false 2614039 65536 217 131072 Bool.true 151708 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz138 Bool.false 261403917 6553600 11509 6968600 2614039 65536 217 131072 (@Enclosure.Real.IsNear.mulLit_ff qz139 qz21 57545 1000 0 1 90852 131072 1 34843 261403917 6553600 11509 6968600 qz141 qz273 rfl) rfl) (Enclosure.sfrac_false_div 2614039 65536) (BSN.cos_reduce1 qz362 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5828925869073532715008) qz286) 226375608064910080 72057594037927936 Bool.false 151708 262144 6 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q1 2614039 65536 226375608064910080 72057594037927936 6 5828925869073532715008 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 151708 262144 5828925869073532715008 9444732965739290427392 331336074 536870912 69755 69686 (ep412 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep414 := BSN.cos_dyadic_bound_f 331336074 536870912 2 1 262144 69755 ep411 ep57 ep411 ep411 ep58 ep411 213784 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 331336074) qz269 0 1 ep411 ep57 ep411 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 331336074) qz270 0 1 ep411 ep58 ep411 rfl rfl rfl rfl) rfl rfl

noncomputable def ep415 := @Enclosure.Real.IsNear.sin_image qz138 qz362 Bool.false 2614039 65536 217 131072 Bool.false 213784 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz138 Bool.false 261403917 6553600 11509 6968600 2614039 65536 217 131072 (@Enclosure.Real.IsNear.mulLit_ff qz139 qz21 57545 1000 0 1 90852 131072 1 34843 261403917 6553600 11509 6968600 qz141 qz273 rfl) rfl) (Enclosure.sfrac_false_div 2614039 65536) (BSN.sin_reduce1 qz362 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5828925869073532715008) qz286) 226375608064910080 72057594037927936 Bool.false 213784 262144 6 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q1 2614039 65536 226375608064910080 72057594037927936 6 5828925869073532715008 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 213784 262144 5828925869073532715008 9444732965739290427392 331336074 536870912 69755 69686 (ep414 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep416 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz138)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz138))) Bool.true 1757575107 4294967296 715560894971 598598181978112 Bool.true 1238370543 2147483648 716642352005 598598181978112 (@Enclosure.Real.IsNear.mulLit_ft qz15 (Real.cos qz138) 46341 65536 1 131072 37927 65536 7692003 4566941696 1757575107 4294967296 715560894971 598598181978112 qz278 (@Enclosure.Real.IsNear.recentre' (Real.cos qz138) Bool.true 151708 262144 7692003 4566941696 37927 65536 7692003 4566941696 (ep413 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz15 (@Neg.neg Real Real.instNeg (Real.sin qz138)) 46341 65536 1 131072 26723 32768 7692003 4566941696 1238370543 2147483648 716642352005 598598181978112 qz278 (@Enclosure.Real.IsNear.neg (Real.sin qz138) Bool.false 26723 32768 7692003 4566941696 (@Enclosure.Real.IsNear.recentre' (Real.sin qz138) Bool.false 213784 262144 7692003 4566941696 26723 32768 7692003 4566941696 (ep415 rfl rfl) rfl)) rfl)

noncomputable def ep417 := @ep408 1757575107 4294967296 715560894971 598598181978112 Bool.true 1238370543 2147483648 716642352005 598598181978112 Bool.false 2537392189 2537392189 4294967296 715560894971 598598181978112 Bool.true 1238370543 1238370543 2147483648 716642352005 598598181978112 (ep409 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz23)) (ep410 ep416) rfl rfl

noncomputable abbrev qz142 := (@HMul.hMul Real Real Real qz254 qz359 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep418 := @Enclosure.Complex.IsNear.of_eq qz136 (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz142)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz142)))) Bool.false 9182797877 17179869184 146051589091 149649545494528 Bool.true 7498888903 34359738368 1165911020171 1197196363956224 (BSN.cpow_neg_s_mk qz139 57545 1000 3 qz140 rfl)

noncomputable def ep419 := nat_lit 1876068427562249951829522780810000

noncomputable def ep420 := BSN.cos_dyadic_bound_f 208119210 536870912 2 1 262144 69755 ep419 ep57 ep419 ep419 ep58 ep419 242692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 208119210) qz269 0 1 ep419 ep57 ep419 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 208119210) qz270 0 1 ep419 ep58 ep419 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8286307) qz20)

noncomputable def ep421 := @Enclosure.Real.IsNear.cos_image qz142 qz363 Bool.false 8286307 131072 217 131072 Bool.false 242692 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 1657261473 26214400 11509 6968600 8286307 131072 217 131072 (@Enclosure.Real.IsNear.mulLit_ff qz139 qz28 57545 1000 0 1 143997 131072 1 34843 1657261473 26214400 11509 6968600 qz141 qz281 rfl) rfl) (Enclosure.sfrac_false_div 8286307 131072) (BSN.cos_reduce0 qz363 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7322543747925282914304) qz275) 226375608064910080 72057594037927936 Bool.false 242692 262144 10 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 8286307 131072 226375608064910080 72057594037927936 10 7322543747925282914304 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 242692 262144 7322543747925282914304 18889465931478580854784 208119210 536870912 69755 69686 (ep420 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep422 := BSN.sin_dyadic_bound_f 208119210 536870912 2 1 262144 69755 ep419 ep71 ep419 ep419 ep72 ep419 99094 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 208119210) qz276 0 1 ep419 ep71 ep419 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 208119210) qz277 0 1 ep419 ep72 ep419 rfl rfl rfl rfl) rfl rfl

noncomputable def ep423 := @Enclosure.Real.IsNear.sin_image qz142 qz363 Bool.false 8286307 131072 217 131072 Bool.false 99094 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 1657261473 26214400 11509 6968600 8286307 131072 217 131072 (@Enclosure.Real.IsNear.mulLit_ff qz139 qz28 57545 1000 0 1 143997 131072 1 34843 1657261473 26214400 11509 6968600 qz141 qz281 rfl) rfl) (Enclosure.sfrac_false_div 8286307 131072) (BSN.sin_reduce0 qz363 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7322543747925282914304) qz275) 226375608064910080 72057594037927936 Bool.false 99094 262144 10 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 8286307 131072 226375608064910080 72057594037927936 10 7322543747925282914304 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 99094 262144 7322543747925282914304 18889465931478580854784 208119210 536870912 69755 69686 (ep422 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep424 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz142)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz142))) Bool.false 9182797877 17179869184 146051589091 149649545494528 Bool.true 7498888903 34359738368 1165911020171 1197196363956224 (@Enclosure.Real.IsNear.mulLit_ff qz24 (Real.cos qz142) 151349 262144 1 262144 60673 65536 7692003 4566941696 9182797877 17179869184 146051589091 149649545494528 qz282 (@Enclosure.Real.IsNear.recentre' (Real.cos qz142) Bool.false 242692 262144 7692003 4566941696 60673 65536 7692003 4566941696 (ep421 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz24 (@Neg.neg Real Real.instNeg (Real.sin qz142)) 151349 262144 1 262144 49547 131072 7692003 4566941696 7498888903 34359738368 1165911020171 1197196363956224 qz282 (@Enclosure.Real.IsNear.neg (Real.sin qz142) Bool.false 49547 131072 7692003 4566941696 (@Enclosure.Real.IsNear.recentre' (Real.sin qz142) Bool.false 99094 262144 7692003 4566941696 49547 131072 7692003 4566941696 (ep423 rfl rfl) rfl)) rfl)

noncomputable def ep425 := @ep406 9182797877 17179869184 146051589091 149649545494528 Bool.true 7498888903 34359738368 1165911020171 1197196363956224 Bool.false 83031882443016634368 19332366633 17179869184 1299767251335 598598181978112 Bool.true 58653829157479251968 27312817591 34359738368 2599195724181 1197196363956224 (ep407 (BSN.head_sum_c_succ qz130 2 3 rfl rfl) (ep417 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep418 ep424) rfl rfl

noncomputable abbrev qz143 := (@HMul.hMul Real Real Real qz254 qz359 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep426 := @Enclosure.Complex.IsNear.of_eq qz135 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz143)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz143)))) Bool.true 2835983227 17179869184 504857006599 598598181978112 Bool.false 8108183131 17179869184 506258531431 598598181978112 (BSN.cpow_neg_s_mk qz139 57545 1000 4 qz140 rfl)

noncomputable def ep427 := nat_lit 26951855409318088276316338823541383747755363904544239445993877944512774241

noncomputable def ep428 := nat_lit 37187799775100449360200067829469371462140143737792115138434872351883361

noncomputable def ep429 := nat_lit 80781190628404063930228616334965212500341811426157134107704764088834556001

noncomputable def ep430 := BSN.cos_dyadic_bound_f 662674197 536870912 3 2 262144 69755 ep427 ep123 ep428 ep429 ep125 ep428 86548 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 662674197) qz269 0 2 ep427 ep123 ep428 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 662674197) qz270 0 2 ep429 ep125 ep428 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20912313) qz27)

noncomputable def ep431 := @Enclosure.Real.IsNear.cos_image qz143 qz364 Bool.false 20912313 262144 217 131072 Bool.true 86548 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 261403917 3276800 11509 6968600 20912313 262144 217 131072 (@Enclosure.Real.IsNear.mulLit_ff qz139 qz32 57545 1000 0 1 181704 131072 1 34843 261403917 3276800 11509 6968600 qz141 qz285 rfl) rfl) (Enclosure.sfrac_false_div 20912313 262144) (BSN.cos_reduce2 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46631551067776337575936) qz29) 226375608064910080 72057594037927936 Bool.false 86548 262144 12 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q2 20912313 262144 226375608064910080 72057594037927936 12 46631551067776337575936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 86548 262144 46631551067776337575936 37778931862957161709568 662674197 536870912 69755 69686 (ep430 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep432 := nat_lit 48483589496952478537881249828110915248789942913189397310678232402241486945

noncomputable def ep433 := nat_lit 126920620816192043062153425630471351431130195016111043817742666498253226081

noncomputable def ep434 := BSN.sin_dyadic_bound_f 662674197 536870912 3 2 262144 69755 ep432 ep116 ep428 ep433 ep119 ep428 247444 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 662674197) qz276 0 2 ep432 ep116 ep428 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 662674197) qz277 0 2 ep433 ep119 ep428 rfl rfl rfl rfl) rfl rfl

noncomputable def ep435 := @Enclosure.Real.IsNear.sin_image qz143 qz364 Bool.false 20912313 262144 217 131072 Bool.true 247444 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 261403917 3276800 11509 6968600 20912313 262144 217 131072 (@Enclosure.Real.IsNear.mulLit_ff qz139 qz32 57545 1000 0 1 181704 131072 1 34843 261403917 3276800 11509 6968600 qz141 qz285 rfl) rfl) (Enclosure.sfrac_false_div 20912313 262144) (BSN.sin_reduce2 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46631551067776337575936) qz29) 226375608064910080 72057594037927936 Bool.false 247444 262144 12 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q2 20912313 262144 226375608064910080 72057594037927936 12 46631551067776337575936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 247444 262144 46631551067776337575936 37778931862957161709568 662674197 536870912 69755 69686 (ep434 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep436 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz143)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz143))) Bool.true 2835983227 17179869184 504857006599 598598181978112 Bool.false 8108183131 17179869184 506258531431 598598181978112 (@Enclosure.Real.IsNear.mulLit_ft qz30 (Real.cos qz143) 131071 262144 1 262144 21637 65536 7692003 4566941696 2835983227 17179869184 504857006599 598598181978112 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz143) Bool.true 86548 262144 7692003 4566941696 21637 65536 7692003 4566941696 (ep431 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz30 (@Neg.neg Real Real.instNeg (Real.sin qz143)) 131071 262144 1 262144 61861 65536 7692003 4566941696 8108183131 17179869184 506258531431 598598181978112 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz143) Bool.true 61861 65536 7692003 4566941696 (@Enclosure.Real.IsNear.recentre' (Real.sin qz143) Bool.true 247444 262144 7692003 4566941696 61861 65536 7692003 4566941696 (ep435 rfl rfl) rfl)) rfl)

noncomputable def ep437 := @ep404 2835983227 17179869184 504857006599 598598181978112 Bool.false 8108183131 17179869184 506258531431 598598181978112 Bool.false 283405708924188360704 8248191703 8589934592 902312128967 299299090989056 Bool.true 190635582238842945536 11096451329 34359738368 3611712787043 1197196363956224 (ep405 (BSN.head_sum_c_succ qz130 3 4 rfl rfl) (ep425 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep426 ep436) rfl rfl

noncomputable abbrev qz144 := (@HMul.hMul Real Real Real qz254 qz359 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep438 := @Enclosure.Complex.IsNear.of_eq qz134 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz144)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz144)))) Bool.true 1903779165 68719476736 1804125142893 2394392727912448 Bool.false 3834170675 8589934592 113292228121 149649545494528 (BSN.cpow_neg_s_mk qz139 57545 1000 5 qz140 rfl)

noncomputable def ep439 := nat_lit 60275495759661125375847710745026022215811333525934681629841231597973187201

noncomputable def ep440 := nat_lit 185365426373013983528533378765993182349271735844975564512244849587169921

noncomputable def ep441 := nat_lit 180455756426237348160486065477546080282735457106114093760499205094745221761

noncomputable def ep442 := BSN.cos_dyadic_bound_f 810034641 536870912 3 2 262144 69755 ep439 ep123 ep440 ep441 ep125 ep440 16239 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 810034641) qz269 0 2 ep439 ep123 ep440 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 810034641) qz270 0 2 ep441 ep125 ep440 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz365 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24278465) qz27)

noncomputable def ep443 := @Enclosure.Real.IsNear.cos_image qz144 qz365 Bool.false 24278465 262144 217 131072 Bool.true 16239 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 303480821 3276800 11509 6968600 24278465 262144 217 131072 (@Enclosure.Real.IsNear.mulLit_ff qz139 qz35 57545 1000 0 1 210952 131072 1 34843 303480821 3276800 11509 6968600 qz141 qz290 rfl) rfl) (Enclosure.sfrac_false_div 24278465 262144) (BSN.cos_reduce2 qz365 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 57001120435152428728320) qz29) 226375608064910080 72057594037927936 Bool.false 16239 262144 14 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q2 24278465 262144 226375608064910080 72057594037927936 14 57001120435152428728320 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16239 262144 57001120435152428728320 37778931862957161709568 810034641 536870912 69755 69686 (ep442 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep444 := nat_lit 108347600026291614489703052638034045442580982958006446482104420996682001025

noncomputable def ep445 := nat_lit 283467408426159824833033226676848987197241848746267875586777468091978394241

noncomputable def ep446 := BSN.sin_dyadic_bound_f 810034641 536870912 3 2 262144 69755 ep444 ep116 ep440 ep445 ep119 ep440 261640 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 810034641) qz276 0 2 ep444 ep116 ep440 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 810034641) qz277 0 2 ep445 ep119 ep440 rfl rfl rfl rfl) rfl rfl

noncomputable def ep447 := @Enclosure.Real.IsNear.sin_image qz144 qz365 Bool.false 24278465 262144 217 131072 Bool.true 261640 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 303480821 3276800 11509 6968600 24278465 262144 217 131072 (@Enclosure.Real.IsNear.mulLit_ff qz139 qz35 57545 1000 0 1 210952 131072 1 34843 303480821 3276800 11509 6968600 qz141 qz290 rfl) rfl) (Enclosure.sfrac_false_div 24278465 262144) (BSN.sin_reduce2 qz365 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 57001120435152428728320) qz29) 226375608064910080 72057594037927936 Bool.false 261640 262144 14 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q2 24278465 262144 226375608064910080 72057594037927936 14 57001120435152428728320 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 261640 262144 57001120435152428728320 37778931862957161709568 810034641 536870912 69755 69686 (ep446 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep448 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz144)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz144))) Bool.true 1903779165 68719476736 1804125142893 2394392727912448 Bool.false 3834170675 8589934592 113292228121 149649545494528 (@Enclosure.Real.IsNear.mulLit_ft qz33 (Real.cos qz144) 117235 262144 1 262144 16239 262144 7692003 4566941696 1903779165 68719476736 1804125142893 2394392727912448 qz291 (@Enclosure.Real.IsNear.recentre' (Real.cos qz144) Bool.true 16239 262144 7692003 4566941696 16239 262144 7692003 4566941696 (ep443 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz144)) 117235 262144 1 262144 32705 32768 7692003 4566941696 3834170675 8589934592 113292228121 149649545494528 qz291 (@Enclosure.Real.IsNear.neg (Real.sin qz144) Bool.true 32705 32768 7692003 4566941696 (@Enclosure.Real.IsNear.recentre' (Real.sin qz144) Bool.true 261640 262144 7692003 4566941696 32705 32768 7692003 4566941696 (ep447 rfl rfl) rfl)) rfl)

noncomputable def ep449 := @ep402 1903779165 68719476736 1804125142893 2394392727912448 Bool.false 3834170675 8589934592 113292228121 149649545494528 Bool.false 550458079343414345728 64081754459 68719476736 9022622174629 2394392727912448 Bool.false 36423310131836485632 4240231371 34359738368 4518050612011 1197196363956224 (ep403 (BSN.head_sum_c_succ qz130 4 5 rfl rfl) (ep437 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep438 ep448) rfl rfl

noncomputable abbrev qz145 := (@HMul.hMul Real Real Real qz254 qz359 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep450 := @Enclosure.Complex.IsNear.of_eq qz133 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz145)))) Bool.true 740070055 2147483648 415461941425 598598181978112 Bool.true 470005085 2147483648 414055120457 598598181978112 (BSN.cpow_neg_s_mk qz139 57545 1000 6 qz140 rfl)

noncomputable def ep451 := @Enclosure.Real.IsNear.mulLit_ff qz139 qz38 57545 1000 0 1 4034681531866359 2251799813685248 500000000034843 17421500000000000000 46435149750249925731 450359962737049600 5754500000401008087 3484300000000000000000 qz141 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000034843 17421500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz293) Bool.false 8461340443916598509568 4722366482869645213696 1000000000069686 34843000000000000000 4034681531866359 2251799813685248 500000000034843 17421500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 53145 131072 24973259072661432 36028797018963968 34843 1000000000000000 rfl rfl rfl rfl (ep102 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep452 := nat_lit 84744586949080420343618935063736881

noncomputable def ep453 := BSN.sin_dyadic_bound_f 539545397 536870912 2 1 262144 69755 ep452 ep71 ep452 ep452 ep72 ep452 221288 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 539545397) qz276 0 1 ep452 ep71 ep452 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 539545397) qz277 0 1 ep452 ep72 ep452 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz366 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13514407) qz20)

noncomputable def ep454 := @Enclosure.Real.IsNear.cos_image qz145 qz366 Bool.false 13514407 131072 217 131072 Bool.true 221288 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 46435149750249925731 450359962737049600 5754500000401008087 3484300000000000000000 13514407 131072 217 131072 (ep451 rfl) rfl) (Enclosure.sfrac_false_div 13514407 131072) (BSN.cos_reduce1 qz366 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18983566020210017173504) qz275) 226375608064910080 72057594037927936 Bool.false 221288 262144 16 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q1 13514407 131072 226375608064910080 72057594037927936 16 18983566020210017173504 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 221288 262144 18983566020210017173504 18889465931478580854784 539545397 536870912 69755 69686 (ep453 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep455 := nat_lit 11834893778731574346448368965853898654363033098222335630393390292347891041

noncomputable def ep456 := nat_lit 7181645017170251506205573067094937725114756112276663342945859999608161

noncomputable def ep457 := nat_lit 35490318046160382536332695751427506087638869782442453564494279157044456801

noncomputable def ep458 := BSN.cos_dyadic_bound_f 539545397 536870912 3 2 262144 69755 ep455 ep123 ep456 ep457 ep125 ep456 140536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 539545397) qz269 0 2 ep455 ep123 ep456 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 539545397) qz270 0 2 ep457 ep125 ep456 rfl rfl rfl rfl) rfl rfl

noncomputable def ep459 := @Enclosure.Real.IsNear.sin_image qz145 qz366 Bool.false 13514407 131072 217 131072 Bool.false 140536 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 46435149750249925731 450359962737049600 5754500000401008087 3484300000000000000000 13514407 131072 217 131072 (ep451 rfl) rfl) (Enclosure.sfrac_false_div 13514407 131072) (BSN.sin_reduce1 qz366 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18983566020210017173504) qz275) 226375608064910080 72057594037927936 Bool.false 140536 262144 16 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q1 13514407 131072 226375608064910080 72057594037927936 16 18983566020210017173504 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 140536 262144 18983566020210017173504 18889465931478580854784 539545397 536870912 69755 69686 (ep458 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep460 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz145))) Bool.true 740070055 2147483648 415461941425 598598181978112 Bool.true 470005085 2147483648 414055120457 598598181978112 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz145) 26755 65536 1 131072 27661 32768 7692003 4566941696 740070055 2147483648 415461941425 598598181978112 qz295 (@Enclosure.Real.IsNear.recentre' (Real.cos qz145) Bool.true 221288 262144 7692003 4566941696 27661 32768 7692003 4566941696 (ep454 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz145)) 26755 65536 1 131072 17567 32768 7692003 4566941696 470005085 2147483648 414055120457 598598181978112 qz295 (@Enclosure.Real.IsNear.neg (Real.sin qz145) Bool.false 17567 32768 7692003 4566941696 (@Enclosure.Real.IsNear.recentre' (Real.sin qz145) Bool.false 140536 262144 7692003 4566941696 17567 32768 7692003 4566941696 (ep459 rfl rfl) rfl)) rfl)

noncomputable def ep461 := @ep400 740070055 2147483648 415461941425 598598181978112 Bool.true 470005085 2147483648 414055120457 598598181978112 Bool.false 86757292908270845952 40399512699 68719476736 10684469940329 2394392727912448 Bool.true 7043424219270479872 3279849989 34359738368 5346160852925 1197196363956224 (ep401 (BSN.head_sum_c_succ qz130 5 6 rfl rfl) (ep449 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep450 ep460) rfl rfl

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz254 qz359 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep462 := @Enclosure.Complex.IsNear.of_eq qz132 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz146)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz146)))) Bool.false 5653859103 34359738368 764127287355 1197196363956224 Bool.false 23382818757 68719476736 1532500925963 2394392727912448 (BSN.cpow_neg_s_mk qz139 57545 1000 7 qz140 rfl)

noncomputable def ep463 := @Enclosure.Real.IsNear.mulLit_ff qz139 qz41 57545 1000 0 1 4381783608859895 2251799813685248 500000000034843 17421500000000000000 10085989510873706311 90071992547409920 5754500000401008087 3484300000000000000000 qz141 (BSN.isNear_log_sfrac 7 1 4381783608859895 2251799813685248 500000000034843 17421500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz297) Bool.false 9189266258887746519040 4722366482869645213696 1000000000069686 34843000000000000000 4381783608859895 2251799813685248 500000000034843 17421500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 73349 131072 24973259072661432 36028797018963968 34843 1000000000000000 rfl rfl rfl rfl (ep113 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep464 := nat_lit 3419866163843243126298206635059216

noncomputable def ep465 := BSN.sin_dyadic_bound_f 241825602 536870912 2 1 262144 69755 ep464 ep71 ep464 ep464 ep72 ep464 114126 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 241825602) qz276 0 1 ep464 ep71 ep464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 241825602) qz277 0 1 ep464 ep72 ep464 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7338523) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep466 := @Enclosure.Real.IsNear.cos_image qz146 qz367 Bool.false 7338523 65536 217 131072 Bool.false 114126 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 10085989510873706311 90071992547409920 5754500000401008087 3484300000000000000000 7338523 65536 217 131072 (ep463 rfl) rfl) (Enclosure.sfrac_false_div 7338523 65536) (BSN.cos_reduce3 qz367 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4254240983915824152576) qz286) 226375608064910080 72057594037927936 Bool.false 114126 262144 17 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q3 7338523 65536 226375608064910080 72057594037927936 17 4254240983915824152576 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 114126 262144 4254240983915824152576 9444732965739290427392 241825602 536870912 69755 69686 (ep465 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep467 := BSN.cos_dyadic_bound_f 241825602 536870912 2 1 262144 69755 ep464 ep57 ep464 ep464 ep58 ep464 235997 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 241825602) qz269 0 1 ep464 ep57 ep464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 241825602) qz270 0 1 ep464 ep58 ep464 rfl rfl rfl rfl) rfl rfl

noncomputable def ep468 := @Enclosure.Real.IsNear.sin_image qz146 qz367 Bool.false 7338523 65536 217 131072 Bool.true 235997 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 10085989510873706311 90071992547409920 5754500000401008087 3484300000000000000000 7338523 65536 217 131072 (ep463 rfl) rfl) (Enclosure.sfrac_false_div 7338523 65536) (BSN.sin_reduce3 qz367 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4254240983915824152576) qz286) 226375608064910080 72057594037927936 Bool.false 235997 262144 17 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q3 7338523 65536 226375608064910080 72057594037927936 17 4254240983915824152576 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 235997 262144 4254240983915824152576 9444732965739290427392 241825602 536870912 69755 69686 (ep467 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep469 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz146)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz146))) Bool.false 5653859103 34359738368 764127287355 1197196363956224 Bool.false 23382818757 68719476736 1532500925963 2394392727912448 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz146) 99081 262144 1 262144 57063 131072 7692003 4566941696 5653859103 34359738368 764127287355 1197196363956224 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz146) Bool.false 114126 262144 7692003 4566941696 57063 131072 7692003 4566941696 (ep466 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz39 (@Neg.neg Real Real.instNeg (Real.sin qz146)) 99081 262144 1 262144 235997 262144 7692003 4566941696 23382818757 68719476736 1532500925963 2394392727912448 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz146) Bool.true 235997 262144 7692003 4566941696 (@Enclosure.Real.IsNear.recentre' (Real.sin qz146) Bool.true 235997 262144 7692003 4566941696 235997 262144 7692003 4566941696 (ep468 rfl rfl) rfl)) rfl)

noncomputable def ep470 := @ep398 5653859103 34359738368 764127287355 1197196363956224 Bool.false 23382818757 68719476736 1532500925963 2394392727912448 Bool.false 1776646925629563863040 51707230905 68719476736 12212724515039 2394392727912448 Bool.false 578037959780227612672 16823118779 68719476736 12224822631813 2394392727912448 (ep399 (BSN.head_sum_c_succ qz130 6 7 rfl rfl) (ep461 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep462 ep469) rfl rfl

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz254 qz359 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep471 := @Enclosure.Complex.IsNear.of_eq qz131 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz147)))) Bool.false 5835861153 17179869184 360850686545 598598181978112 Bool.true 3368110221 34359738368 715458030135 1197196363956224 (BSN.cpow_neg_s_mk qz139 57545 1000 8 qz140 rfl)

noncomputable def ep472 := @Enclosure.Real.IsNear.mulLit_ff qz139 qz44 57545 1000 0 1 9364972152248037 4503599627370496 1000000000104529 34843000000000000000 107781464500222657833 900719925474099200 11509000001203024261 6968600000000000000000 qz141 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000104529 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz301) Bool.false 9819885039515637645312 4722366482869645213696 1000000000104529 34843000000000000000 9364972152248037 4503599627370496 1000000000104529 34843000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 131072 24973259072661432 36028797018963968 34843 1000000000000000 rfl rfl rfl rfl (ep132 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep473 := nat_lit 517528237713257047570437126750625

noncomputable def ep474 := BSN.cos_dyadic_bound_f 150828535 536870912 2 1 262144 69755 ep473 ep57 ep473 ep473 ep58 ep473 251866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 150828535) qz269 0 1 ep473 ep57 ep473 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 150828535) qz270 0 1 ep473 ep58 ep473 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz368 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15684267) qz20)

noncomputable def ep475 := @Enclosure.Real.IsNear.cos_image qz147 qz368 Bool.false 15684267 131072 217 131072 Bool.false 251866 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 107781464500222657833 900719925474099200 11509000001203024261 6968600000000000000000 15684267 131072 217 131072 (ep472 rfl) rfl) (Enclosure.sfrac_false_div 15684267 131072) (BSN.cos_reduce0 qz368 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5306807315363805528064) qz275) 226375608064910080 72057594037927936 Bool.false 251866 262144 19 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 15684267 131072 226375608064910080 72057594037927936 19 5306807315363805528064 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 251866 262144 5306807315363805528064 18889465931478580854784 150828535 536870912 69755 69686 (ep474 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep476 := BSN.sin_dyadic_bound_f 150828535 536870912 2 1 262144 69755 ep473 ep71 ep473 ep473 ep72 ep473 72681 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 150828535) qz276 0 1 ep473 ep71 ep473 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 150828535) qz277 0 1 ep473 ep72 ep473 rfl rfl rfl rfl) rfl rfl

noncomputable def ep477 := @Enclosure.Real.IsNear.sin_image qz147 qz368 Bool.false 15684267 131072 217 131072 Bool.false 72681 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 107781464500222657833 900719925474099200 11509000001203024261 6968600000000000000000 15684267 131072 217 131072 (ep472 rfl) rfl) (Enclosure.sfrac_false_div 15684267 131072) (BSN.sin_reduce0 qz368 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5306807315363805528064) qz275) 226375608064910080 72057594037927936 Bool.false 72681 262144 19 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 15684267 131072 226375608064910080 72057594037927936 19 5306807315363805528064 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 72681 262144 5306807315363805528064 18889465931478580854784 150828535 536870912 69755 69686 (ep476 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep478 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz147))) Bool.false 5835861153 17179869184 360850686545 598598181978112 Bool.true 3368110221 34359738368 715458030135 1197196363956224 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz147) 46341 131072 1 131072 125933 131072 7692003 4566941696 5835861153 17179869184 360850686545 598598181978112 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz147) Bool.false 251866 262144 7692003 4566941696 125933 131072 7692003 4566941696 (ep475 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz147)) 46341 131072 1 131072 72681 262144 7692003 4566941696 3368110221 34359738368 715458030135 1197196363956224 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz147) Bool.false 72681 262144 7692003 4566941696 (@Enclosure.Real.IsNear.recentre' (Real.sin qz147) Bool.false 72681 262144 7692003 4566941696 72681 262144 7692003 4566941696 (ep477 rfl rfl) rfl)) rfl)

noncomputable def ep479 := @ep396 5835861153 17179869184 360850686545 598598181978112 Bool.true 3368110221 34359738368 715458030135 1197196363956224 Bool.false 1289360787552891568128 75050675517 68719476736 13656127261219 2394392727912448 Bool.false 346583187803934294016 10086898337 68719476736 13655738692083 2394392727912448 (ep397 (BSN.head_sum_c_succ qz130 7 8 rfl rfl) (ep470 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep471 ep478) rfl rfl

theorem EMRow12.d10 : Enclosure.Complex.IsNear qz129 Bool.false 75050675517 68719476736 13656127261219 2394392727912448 Bool.false 10086898337 68719476736 13655738692083 2394392727912448 := ep395 (BSN.head_sum_c_succ qz130 8 9 rfl rfl) (ep479 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow12.d11 : @Eq Nat (Nat.pow 12 1) 12 := @Eq.refl Nat 12

noncomputable def ep480 := nat_lit 1689616280858162677432414513

noncomputable def ep481 := nat_lit 916344878024382429146382336

noncomputable def ep482 := nat_lit 753972995064137655313452493939986047

noncomputable def ep483 := nat_lit 83435582426645920185787173667917004800

noncomputable abbrev qz447 := (@HAdd.hAdd Complex Complex Complex qz453 (@HAdd.hAdd Complex Complex Complex qz453 qz456 (@HMul.hMul Complex Complex Complex qz455 Complex.I (@HDiv.hDiv Complex Complex Complex qz457 (↑qz460) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz369 := qz447

noncomputable abbrev qz148 := (Complex.Stirling.logGammaStirling 1 qz369)

noncomputable abbrev qz448 := (@HAdd.hAdd Complex Complex Complex qz453 qz456 (@HMul.hMul Complex Complex Complex qz455 Complex.I (@HDiv.hDiv Complex Complex Complex qz457 (↑qz460) (2 : Complex))))

noncomputable abbrev qz370 := qz448

noncomputable abbrev qz149 := qz370

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz254 (@HDiv.hDiv Real Real Real qz257 qz359 (2 : Real)) (Real.log Real.pi))

noncomputable def ep484 := Complex.re (@HMul.hMul Complex Complex Complex qz45 (Complex.exp (@HMul.hMul Complex Complex Complex qz45 Complex.I ↑(@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))))) qz150))) (zetaApproximant qz130 1 12))

noncomputable def ep485 := @Enclosure.Real.IsNear.of_eq ep484 (@HSub.hSub Real Real Real qz46 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))))) qz150)) (Complex.re (zetaApproximant qz130 1 12))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))))) qz150)) (Complex.im (zetaApproximant qz130 1 12))))

noncomputable def ep486 := nat_lit 563207432467174279299065691

noncomputable def ep487 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))))) qz150)) (Complex.re (zetaApproximant qz130 1 12))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))))) qz150)) (Complex.im (zetaApproximant qz130 1 12))) ep486

noncomputable def ep488 := nat_lit 305448292674794143048794112

noncomputable def ep489 := nat_lit 150272476602298826331868341456941683

noncomputable def ep490 := nat_lit 16687116485329184037157434733583400960

noncomputable def ep491 := nat_lit 28635777438261950910824448

noncomputable def ep492 := nat_lit 13596937774185019031827013829571

noncomputable def ep493 := nat_lit 434560325138780834300974862853734400

noncomputable def ep494 := nat_lit 16127825258239414200089139779677188547420452036804608

noncomputable def ep495 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))))) qz150)) (Complex.re (zetaApproximant qz130 1 12)) 262143 262144 834157

noncomputable def ep496 := nat_lit 69904376180085278153572483

noncomputable def ep497 := nat_lit 9134732604504649251579494400

noncomputable def ep498 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))))) qz150)) Bool.true 262143 262144 834157

noncomputable abbrev qz371 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4529497) qz20)

noncomputable def ep499 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))))) qz150) qz371 Bool.false 4529497 131072 23

noncomputable def ep500 := nat_lit 685041254400000000000000000

noncomputable def ep501 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))))) qz150) Bool.false 373517622279590641201 10808639105689190400 479054895135604804363883 ep500

noncomputable def ep502 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))))) qz150 29180755228753940953 432345564227567616 178298829885604804363883 ep500 863416689 26214400

noncomputable def ep503 := nat_lit 391661614299444036187979776

noncomputable def ep504 := nat_lit 57086771200000000000000000

noncomputable def ep505 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 40637558024882755859 900719925474099200 25759818001082699529301 ep504 Bool.false 29180755228753940953 432345564227567616

noncomputable def ep506 := @Enclosure.Complex.IsNear.subLitP qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 34584882679879200859 900719925474099200 24940618000568918588501 ep504 Bool.false 30516483182425154521 432345564227567616 158638029884919763109483

noncomputable def ep507 := nat_lit 183015291178108888703311426107736064

noncomputable def ep508 := nat_lit 8213652398412868827496452789895168

noncomputable abbrev qz372 := (@HSub.hSub Complex Complex Complex qz436 qz447 qz439)

noncomputable abbrev qz373 := (Complex.log qz447)

noncomputable abbrev qz151 := (@HSub.hSub Complex Complex Complex qz305 (@HMul.hMul Complex Complex Complex qz304 qz372 qz373) qz369)

noncomputable abbrev qz152 := qz369

noncomputable def ep509 := @Enclosure.Complex.IsNear.of_eq qz148 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz151 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz152 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k)))))) Bool.true 34584882679879200859

noncomputable def ep510 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz151 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz152 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) Bool.true 34585085442181460059 900719925474099200

noncomputable def ep511 := nat_lit 74270470023039002460010053632

noncomputable def ep512 := nat_lit 163834121571812550794301931520000

noncomputable def ep513 := @ep510 12177997193003331487 27874400000000000000000 Bool.false 254314398037261626043 3602879701896396800 6454500003633462883 27874400000000000000000 Bool.false 483423 2147483648 3 2147483648 Bool.true 1854571769 644245094400 11509 644245094400 Bool.true ep511 34584882679879200859 900719925474099200 24940618000568918588501 ep504 Bool.false ep512

noncomputable def ep514 := @Enclosure.Complex.IsNear.addLitP qz151 qz52 Bool.true 35412787487649722459 900719925474099200 11859000000620518987 27874400000000000000000

noncomputable def ep515 := nat_lit 9066272638155216665706496

noncomputable def ep516 := @ep514 Bool.false 254314398037261626043 3602879701896396800 6454500003633462883 27874400000000000000000 Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 Bool.true ep515 34585085442181460059 900719925474099200 12177997193003331487 27874400000000000000000 Bool.false 254314398037261626043 254314398037261626043 3602879701896396800

noncomputable abbrev qz153 := (@HMul.hMul Complex Complex Complex qz304 qz372 qz373)

noncomputable def ep517 := @Enclosure.Complex.IsNear.subLitP qz153 qz152 Bool.true 33386167655332999259 900719925474099200 11859000000620518987 27874400000000000000000 Bool.false 357978254260075702971

noncomputable def ep518 := @ep517 3602879701896396800 6454500003633462883 27874400000000000000000 Bool.false 9000 4000 0 1 Bool.false 115090 4000 0 1 Bool.true 141651149950598889836000 35412787487649722459 900719925474099200 11859000000620518987 27874400000000000000000 Bool.false 1017257592149046504172000 254314398037261626043 3602879701896396800 6454500003633462883 27874400000000000000000

noncomputable abbrev qz154 := qz372

noncomputable abbrev qz155 := qz373

noncomputable def ep519 := @Enclosure.Complex.IsNear.mul qz154 qz155 Bool.true 33386167655332999259 900719925474099200 11859000000620518987 27874400000000000000000 Bool.false 357978254260075702971 3602879701896396800 6454500003633462883

noncomputable abbrev qz156 := (Complex.re qz372)

noncomputable abbrev qz157 := (Complex.re qz373)

noncomputable abbrev qz158 := (Complex.im qz372)

noncomputable abbrev qz159 := (Complex.im qz373)

noncomputable def ep520 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz156 qz157) (@HMul.hMul Real Real Real qz0 qz158 qz159) 212004904507154633 36028797018963968 3500000002195109 278744000000000000000 9671572567002966271 225179981368524800

noncomputable def ep521 := nat_lit 300715864423773203190507862572924928

noncomputable def ep522 := @Enclosure.Real.IsNear.mulLit_ff qz156 qz157 7000 4000 0 1 30286414929593519 9007199254740992 500000000313587 69686000000000000000

noncomputable def ep523 := @Enclosure.Complex.IsNear.re_isNear qz154 Bool.false 7000 4000 0 1 Bool.false 115090 4000 0 1

noncomputable abbrev qz374 := (Enclosure.sfrac Bool.false 115090 4000)

noncomputable abbrev qz160 := qz374

noncomputable def ep524 := @Enclosure.Complex.IsNear.of_eq qz154 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz160) Bool.false 7000 4000 0 1 Bool.false 115090 4000 0

noncomputable abbrev qz161 := (Complex.mk qz319 qz374)

noncomputable def ep525 := @Enclosure.Complex.IsNear.of_eq qz155 (Complex.log qz161) Bool.false 30286414929593519 9007199254740992 500000000313587 69686000000000000000 Bool.false 840348646016419 562949953421312 1000000000034843 69686000000000000000

noncomputable def ep526 := nat_lit 43447157053633374337220821503477884676713266079454298422806702699097450000000000000000

noncomputable def ep527 := nat_lit 853958821669552308494234019387637543735546774558449708923750971937040000000000000000

noncomputable def ep528 := nat_lit 50735900916461061740904300231654401198656130636737805643617233050000000000000000

noncomputable def ep529 := BSN.log_dyadic_bound 5134708100 21518708100 5 4 ep526 262144 69686 ep527 ep528 127562 26653416200 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5134708100) (BSN.artanhQ 21518708100) 0 4 ep527 ep526 ep528 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz375 := (Real.log (Enclosure.sfrac Bool.false 13326708100 16000000))

noncomputable def ep530 := @Enclosure.Real.IsNear.mulLit_ff qz70 qz375 1 2 0 1 30286414929593519 4503599627370496 500000000313587 34843000000000000000 30286414929593519 9007199254740992 500000000313587 69686000000000000000 qz321 (BSN.isNear_log_sfrac 13326708100 16000000 30286414929593519 4503599627370496 500000000313587 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13326708100) qz322)) Bool.false 63515215642426907557888 9444732965739290427392 1000000000627174 69686000000000000000 30286414929593519 4503599627370496 500000000313587 34843000000000000000 (BSN.log_rat_reduce_isNear 13326708100 16000000 9 26653416200 16384000000 127562 262144 24973259072661432 36028797018963968 69686 1000000000000000 rfl rfl rfl rfl (ep529 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep531 := BSN.arctan_dyadic_bound_f 9000 115090 1 0 262144 69686 0 1 1 0 1 1 20457 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 115090) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 115090) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz376 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 115090)))

noncomputable def ep532 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz376 884279719003555 562949953421312 1 2000000000000000 20457 262144 1 69686 220292355461328142336 840348646016419 562949953421312 1000000000034843 69686000000000000000 qz72 (ep531 rfl) rfl rfl

noncomputable abbrev qz377 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 115090) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep533 := @Enclosure.Complex.IsNear.re_isNear qz155 Bool.false 30286414929593519 9007199254740992 500000000313587 69686000000000000000 Bool.false 840348646016419 562949953421312 1000000000034843 69686000000000000000 (ep525 (@congrArg Complex Complex qz152 qz161 Complex.log (BSN.w_shift_mk qz139 Bool.false 57545 1000 2 qz140 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz161) Bool.false 30286414929593519 9007199254740992 500000000313587 69686000000000000000 Bool.false 840348646016419 562949953421312 1000000000034843 69686000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz161)) (@HMul.hMul Real Real Real qz0 qz70 qz375) Bool.false 30286414929593519 9007199254740992 500000000313587 69686000000000000000 (Enclosure.clog_re_eq 9000 115090 4000 13326708100 16000000 rfl rfl rfl) (ep530 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz161)) qz377 Bool.false 840348646016419 562949953421312 1000000000034843 69686000000000000000 (Enclosure.clog_im_eq 9000 115090 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz377 (@HSub.hSub Real Real Real qz46 qz71 qz376) Bool.false 840348646016419 562949953421312 1000000000034843 69686000000000000000 (BSN.arctan_recip 115090 9000 rfl rfl) ep532))))

noncomputable def ep534 := @Enclosure.Real.IsNear.mulLit_ff qz158 qz159 115090 4000 0 1 840348646016419 562949953421312 1000000000034843 69686000000000000000

noncomputable def ep535 := @Enclosure.Complex.IsNear.im_isNear qz154 Bool.false 7000 4000 0 1 Bool.false 115090 4000 0 1

noncomputable def ep536 := @Enclosure.Complex.IsNear.im_isNear qz155 Bool.false 30286414929593519 9007199254740992 500000000313587 69686000000000000000 Bool.false 840348646016419 562949953421312 1000000000034843 69686000000000000000 (ep525 (@congrArg Complex Complex qz152 qz161 Complex.log (BSN.w_shift_mk qz139 Bool.false 57545 1000 2 qz140 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz161) Bool.false 30286414929593519 9007199254740992 500000000313587 69686000000000000000 Bool.false 840348646016419 562949953421312 1000000000034843 69686000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz161)) (@HMul.hMul Real Real Real qz0 qz70 qz375) Bool.false 30286414929593519 9007199254740992 500000000313587 69686000000000000000 (Enclosure.clog_re_eq 9000 115090 4000 13326708100 16000000 rfl rfl rfl) (ep530 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz161)) qz377 Bool.false 840348646016419 562949953421312 1000000000034843 69686000000000000000 (Enclosure.clog_im_eq 9000 115090 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz377 (@HSub.hSub Real Real Real qz46 qz71 qz376) Bool.false 840348646016419 562949953421312 1000000000034843 69686000000000000000 (BSN.arctan_recip 115090 9000 rfl rfl) ep532))))

noncomputable abbrev qz378 := (Enclosure.Real.IsNear.const Bool.false 115090 4000)

noncomputable abbrev qz162 := (@ep524 1 (BSN.w_sub_half_mk qz359 Bool.false 57545 1000 2 qz360 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz374 Bool.false 7000 4000 0 1 Bool.false 115090 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz378))

noncomputable def ep537 := @ep520 11509000000401008087 27874400000000000000000 ep521 33386167655332999259 900719925474099200 11859000000620518987 27874400000000000000000 (@ep522 212004904507154633 36028797018963968 3500000002195109 278744000000000000000 (ep523 qz162) ep533 rfl) (@ep534 9671572567002966271 225179981368524800 11509000000401008087 27874400000000000000000 (ep535 qz162) ep536 rfl) rfl

noncomputable def ep538 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz156 qz159) (@HMul.hMul Real Real Real qz0 qz158 qz157) 5882440522114933 2251799813685248 7000000000243901 278744000000000000000 348566349424691810171 3602879701896396800

noncomputable def ep539 := nat_lit 806095366246208804091149699732471808

noncomputable def ep540 := @Enclosure.Real.IsNear.mulLit_ff qz156 qz159 7000 4000 0 1 840348646016419 562949953421312 1000000000034843 69686000000000000000

noncomputable def ep541 := @Enclosure.Real.IsNear.mulLit_ff qz158 qz157 115090 4000 0 1 30286414929593519 9007199254740992 500000000313587 69686000000000000000

noncomputable def ep542 := @ep538 5754500003609072783 27874400000000000000000 ep539 357978254260075702971 3602879701896396800 6454500003633462883 27874400000000000000000 (@ep540 5882440522114933 2251799813685248 7000000000243901 278744000000000000000 (ep523 qz162) ep536 rfl) (@ep541 348566349424691810171 3602879701896396800 5754500003609072783 27874400000000000000000 (ep535 qz162) ep533 rfl) rfl

noncomputable def ep543 := @Enclosure.Complex.IsNear.of_eq qz152 qz161 Bool.false 9000 4000 0 1 Bool.false 115090 4000 0 1 (BSN.w_shift_mk qz139 Bool.false 57545 1000 2 qz140 rfl)

noncomputable abbrev qz379 := (ep543 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 115090 4000) Bool.false 9000 4000 0 1 Bool.false 115090 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 115090 4000)))

noncomputable abbrev qz163 := qz379

noncomputable def ep544 := ep518 (@ep519 27874400000000000000000 (ep537 rfl) (ep542 rfl)) qz163 rfl rfl rfl rfl rfl rfl

noncomputable def ep545 := @ep516 6454500003633462883 27874400000000000000000 (ep544 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz75 (↑qz3) Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 (@ep204 262144 3 262144 (ep206 rfl) (ep208 rfl) rfl rfl) (@ep209 1 0 1 (ep211 rfl) (ep213 rfl) rfl rfl))

noncomputable abbrev qz380 := (@HPow.hPow Complex Int Complex qz441 qz447 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz164 := qz380

noncomputable def ep546 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz152 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz152 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz164)) Bool.false 483423 2147483648 3 2147483648

noncomputable def ep547 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz152 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz164) Bool.false 0 1 0 1 Bool.false

noncomputable def ep548 := @ep547 0 1 0 1 Bool.false 483423 2147483648 3 2147483648 Bool.true 1854571769 644245094400 11509 644245094400 Bool.false 483423 483423 2147483648 3 2147483648 Bool.true 1854571769 1854571769 644245094400 11509

noncomputable def ep549 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz45 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz152 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep550 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz164 Bool.false 483423 2147483648 3 2147483648 Bool.true 1854571769 644245094400 11509 644245094400

noncomputable abbrev qz165 := (Complex.re qz380)

noncomputable abbrev qz166 := (Complex.im qz380)

noncomputable def ep551 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz165) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz166) 483423 2147483648 3 2147483648 0 1 0

noncomputable def ep552 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz165 1 12 0 1 1450269 536870912 9 536870912 483423

noncomputable def ep553 := @Enclosure.Complex.IsNear.re_isNear qz164 Bool.false 1450269 536870912 9 536870912 Bool.true 1854571769 53687091200 11509 53687091200

noncomputable abbrev qz381 := (@HPow.hPow Complex Nat Complex qz442 qz447 1)

noncomputable abbrev qz167 := (@Inv.inv Complex Complex.instInv qz381)

noncomputable def ep554 := @Enclosure.Complex.IsNear.of_eq qz164 qz167 Bool.false 1450269 536870912 9 536870912 Bool.true 1854571769 53687091200 11509

noncomputable def ep555 := @Enclosure.Complex.IsNear.of_parts qz167 Bool.false 1450269 536870912 9 536870912 Bool.true 1854571769 53687091200 11509

noncomputable abbrev qz168 := (Complex.re qz381)

noncomputable abbrev qz169 := qz381

noncomputable def ep556 := @Enclosure.Real.IsNear.mulLit_ff qz168 (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz169)) 9000 4000 0 1 161141 134217728 1 134217728

noncomputable def ep557 := @Enclosure.Complex.IsNear.re_isNear qz169 Bool.false 9000 4000 0 1 Bool.false 115090 4000 0 1

noncomputable def ep558 := @Enclosure.Complex.IsNear.of_eq qz169 qz152 Bool.false 9000 4000 0 1 Bool.false 115090 4000 0

noncomputable def ep559 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz169)) Bool.false 161141 134217728 1 134217728 161141 134217728 1

noncomputable abbrev qz170 := (Complex.im qz381)

noncomputable def ep560 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz169) (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 qz168 qz168) (@HMul.hMul Real Real Real qz0 qz170 qz170)) Bool.false 133267081 160000 0 1

noncomputable def ep561 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz168 qz168) (@HMul.hMul Real Real Real qz0 qz170 qz170) 81 16 0 1 132457081 160000

noncomputable def ep562 := @Enclosure.Real.IsNear.mulLit_ff qz168 qz168 9000 4000 0 1 9000 4000 0 1

noncomputable def ep563 := @Enclosure.Real.IsNear.mulLit_ff qz170 qz170 115090 4000 0 1 115090 4000 0 1

noncomputable def ep564 := @Enclosure.Complex.IsNear.im_isNear qz169 Bool.false 9000 4000 0 1 Bool.false 115090 4000 0 1

noncomputable abbrev qz171 := (ep557 (@ep558 1 (BSN.pow_one_c qz369) qz379))

noncomputable abbrev qz172 := (ep564 (@ep558 1 (BSN.pow_one_c qz369) qz379))

noncomputable def ep565 := @ep561 0 1 2132273296 133267081 160000 0 1 (@ep562 81 16 0 1 qz171 qz171 rfl) (@ep563 132457081 160000 0 1 qz172 qz172 rfl)

noncomputable def ep566 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz169) 133267081 160000 0 1 80570 80571 67108864 (ep560 (Enclosure.Complex.normSq_eq_mul_add_mul qz169) (ep565 rfl rfl)) rfl

noncomputable def ep567 := @Enclosure.Real.IsNear.of_eq (Complex.re qz167) (@HMul.hMul Real Real Real qz0 qz168 (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz169))) Bool.false 1450269 536870912 9 536870912 (Enclosure.Complex.inv_re_eq_mul qz169) (@ep556 1450269 536870912 9 536870912 qz171 (@ep559 134217728 (ep566 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep568 := @Enclosure.Real.IsNear.of_eq (Complex.im qz167) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz170) (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz169))) Bool.true 1854571769 53687091200 11509 53687091200 (Enclosure.Complex.inv_im_eq_mul qz169)

noncomputable def ep569 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz170) (@Inv.inv Real Real.instInv (@DFunLike.coe qz85 Complex (fun (x : Complex) => Real) qz86 Complex.normSq qz169)) 115090 4000 0 1 161141 134217728 1

noncomputable def ep570 := @ep569 134217728 1854571769 53687091200 11509 53687091200 (@Enclosure.Real.IsNear.neg qz170 Bool.false 115090 4000 0 1 qz172) (@ep559 134217728 (ep566 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep571 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz166 0 1 0 1 1854571769 53687091200 11509 53687091200 0

noncomputable def ep572 := @Enclosure.Complex.IsNear.im_isNear qz164 Bool.false 1450269 536870912 9 536870912 Bool.true 1854571769 53687091200 11509 53687091200

noncomputable abbrev qz173 := (@ep554 53687091200 (BSN.zpow_one_sub_two_mul qz369 1 1 rfl rfl) (@ep555 53687091200 ep567 (ep568 ep570)))

noncomputable def ep573 := @ep551 1 483423 483423 2147483648 3 2147483648 (@ep552 2147483648 3 2147483648 ep223 (ep553 qz173) rfl) (@ep571 1 0 1 ep243 (ep572 qz173) rfl) rfl

noncomputable def ep574 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz166) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz165) 1854571769 644245094400 11509 644245094400 0 1 0

noncomputable def ep575 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz166 1 12 0 1 1854571769 53687091200 11509 53687091200 1854571769

noncomputable def ep576 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz165 0 1 0 1 1450269 536870912 9 536870912 0

noncomputable def ep577 := @ep574 1 1854571769 1854571769 644245094400 11509 644245094400 (@ep575 644245094400 11509 644245094400 ep223 (ep572 qz173) rfl) (@ep576 1 0 1 ep243 (ep553 qz173) rfl) rfl

noncomputable def ep578 := @ep548 644245094400 (@ep549 0 1 0 1 (BSN.stirling_sum_base qz152) qz93) (ep550 (ep573 rfl) (ep577 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep579 := @ep513 30516483182425154521 432345564227567616 158638029884919763109483 ep500 (ep545 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep546 Bool.true 1854571769 644245094400 11509 644245094400 (BSN.stirling_sum_succ qz152 0 1 rfl) (ep578 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep580 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz139 2) Bool.false 30263376725017775 4503599627370496 500000000313587 34843000000000000000 Bool.false 869614553171363 281474976710656

noncomputable abbrev qz174 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz260 qz370 qz327))

noncomputable def ep581 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz139 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz139 1) qz174) Bool.false 30263376725017775 4503599627370496 500000000313587 34843000000000000000 Bool.false 869614553171363 281474976710656 1000000000034843 34843000000000000000

noncomputable def ep582 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz139 1) qz174 Bool.false 30259305096021167 9007199254740992 500000000313587 69686000000000000000 Bool.false 879389898737059 562949953421312 1000000000034843 69686000000000000000 Bool.false

noncomputable def ep583 := nat_lit 545176528567051972325928442265600

noncomputable def ep584 := nat_lit 979098944404627696843344576512

noncomputable abbrev qz175 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz260 qz370 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep585 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz139 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz139 0) qz175) Bool.false 30259305096021167 9007199254740992 500000000313587 69686000000000000000 Bool.false 879389898737059 562949953421312 1000000000034843 69686000000000000000

noncomputable def ep586 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz139 0) qz175 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz382 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz160))

noncomputable def ep587 := @Enclosure.Complex.IsNear.of_eq qz175 qz382 Bool.false 30259305096021167 9007199254740992 500000000313587 69686000000000000000 Bool.false 879389898737059 562949953421312 1000000000034843 69686000000000000000

noncomputable def ep588 := nat_lit 42171660124929041200885682068730736286360057344953487552192741419097450000000000000000

noncomputable def ep589 := nat_lit 808581379654474309534998627062331541479088935839685148187303995937040000000000000000

noncomputable def ep590 := nat_lit 44746384142770308535470490247394323903757780040467699025697233050000000000000000

noncomputable def ep591 := BSN.log_dyadic_bound 5054708100 21438708100 5 4 ep588 262144 69686 ep589 ep590 125984 26493416200 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5054708100) (BSN.artanhQ 21438708100) 0 4 ep589 ep588 ep590 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep592 := @Enclosure.Real.IsNear.mulLit_ff qz70 (Real.log (Enclosure.sfrac Bool.false 13246708100 16000000)) 1 2 0 1 30259305096021167 4503599627370496 500000000313587 34843000000000000000 30259305096021167 9007199254740992 500000000313587 69686000000000000000 qz321 (BSN.isNear_log_sfrac 13246708100 16000000 30259305096021167 4503599627370496 500000000313587 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13246708100) qz322)) Bool.false 63458362200730982416384 9444732965739290427392 1000000000627174 69686000000000000000 30259305096021167 4503599627370496 500000000313587 34843000000000000000 (BSN.log_rat_reduce_isNear 13246708100 16000000 9 26493416200 16384000000 125984 262144 24973259072661432 36028797018963968 69686 1000000000000000 rfl rfl rfl rfl (ep591 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep593 := BSN.arctan_dyadic_bound_f 1000 115090 1 0 262144 69686 0 1 1 0 1 1 2277 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 115090) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 115090) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz383 := (@Nat.cast Real Real.instNatCast 115090)

noncomputable def ep594 := @Enclosure.Real.IsNear.subLit_ff_p qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz331 qz383)) 884279719003555 562949953421312 1 2000000000000000 2277 262144 1 69686 230526785614527594496 879389898737059 562949953421312 1000000000034843 69686000000000000000 qz72 (ep593 rfl) rfl rfl

noncomputable abbrev qz176 := (@HAdd.hAdd Complex Complex Complex qz260 qz370 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz384 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz160)

noncomputable def ep595 := @ep586 30259305096021167 9007199254740992 500000000313587 69686000000000000000 Bool.false 879389898737059 562949953421312 1000000000034843 69686000000000000000 Bool.false 30259305096021167 30259305096021167 9007199254740992 500000000313587 69686000000000000000 Bool.false 879389898737059 879389898737059 562949953421312 1000000000034843 69686000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz139 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz139) qz93) (ep587 (@congrArg Complex Complex qz176 qz384 Complex.log (BSN.w_shift_mk qz139 Bool.false 57545 1000 0 qz140 rfl)) (@Enclosure.Complex.IsNear.of_parts qz382 Bool.false 30259305096021167 9007199254740992 500000000313587 69686000000000000000 Bool.false 879389898737059 562949953421312 1000000000034843 69686000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz382) (@HMul.hMul Real Real Real qz0 qz70 (Real.log (Enclosure.sfrac Bool.false 13246708100 16000000))) Bool.false 30259305096021167 9007199254740992 500000000313587 69686000000000000000 (Enclosure.clog_re_eq 1000 115090 4000 13246708100 16000000 rfl rfl rfl) (ep592 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz382) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz383 qz331)) Bool.false 879389898737059 562949953421312 1000000000034843 69686000000000000000 (Enclosure.clog_im_eq 1000 115090 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz383 qz331)) (@HSub.hSub Real Real Real qz46 qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz331 qz383))) Bool.false 879389898737059 562949953421312 1000000000034843 69686000000000000000 (BSN.arctan_recip 115090 1000 rfl rfl) ep594)))) rfl rfl

noncomputable abbrev qz385 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz160))

noncomputable def ep596 := @Enclosure.Complex.IsNear.of_eq qz174 qz385 Bool.false 30267448354014383 9007199254740992 500000000313587 69686000000000000000 Bool.false 859839207605667 562949953421312 1000000000034843 69686000000000000000

noncomputable def ep597 := nat_lit 42550822661543373552496001066440356485667592073193599334819489803097450000000000000000

noncomputable def ep598 := nat_lit 821984837926485448186605537502880719766641356428834073526190088737040000000000000000

noncomputable def ep599 := nat_lit 46474563340594859346688478176677222487391512201478846851073233050000000000000000

noncomputable def ep600 := BSN.log_dyadic_bound 5078708100 21462708100 5 4 ep597 262144 69686 ep598 ep599 126458 26541416200 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5078708100) (BSN.artanhQ 21462708100) 0 4 ep598 ep597 ep599 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep601 := @Enclosure.Real.IsNear.mulLit_ff qz70 (Real.log (Enclosure.sfrac Bool.false 13270708100 16000000)) 1 2 0 1 30267448354014383 4503599627370496 500000000313587 34843000000000000000 30267448354014383 9007199254740992 500000000313587 69686000000000000000 qz321 (BSN.isNear_log_sfrac 13270708100 16000000 30267448354014383 4503599627370496 500000000313587 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13270708100) qz322)) Bool.false 63475439850517971337216 9444732965739290427392 1000000000627174 69686000000000000000 30267448354014383 4503599627370496 500000000313587 34843000000000000000 (BSN.log_rat_reduce_isNear 13270708100 16000000 9 26541416200 16384000000 126458 262144 24973259072661432 36028797018963968 69686 1000000000000000 rfl rfl rfl rfl (ep600 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep602 := BSN.arctan_dyadic_bound_f 5000 115090 1 0 262144 69686 0 1 1 0 1 1 11381 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 115090) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 115090) 0 0 rfl) rfl rfl rfl

noncomputable def ep603 := @Enclosure.Real.IsNear.subLit_ff_p qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz335 qz383)) 884279719003555 562949953421312 1 2000000000000000 11381 262144 1 69686 225401689238579970048 859839207605667 562949953421312 1000000000034843 69686000000000000000 qz72 (ep602 rfl) rfl rfl

noncomputable abbrev qz177 := (@HAdd.hAdd Complex Complex Complex qz260 qz370 qz327)

noncomputable abbrev qz386 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz160)

noncomputable def ep604 := @ep582 30267448354014383 9007199254740992 500000000313587 69686000000000000000 Bool.false 859839207605667 562949953421312 1000000000034843 69686000000000000000 Bool.false ep583 30263376725017775 4503599627370496 500000000313587 34843000000000000000 Bool.false ep584 869614553171363 281474976710656 1000000000034843 34843000000000000000 (ep585 (BSN.log_sum_c_succ qz139 0 1 rfl) (ep595 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep596 (@congrArg Complex Complex qz177 qz386 Complex.log (BSN.w_shift_mk qz139 Bool.false 57545 1000 1 qz140 rfl)) (@Enclosure.Complex.IsNear.of_parts qz385 Bool.false 30267448354014383 9007199254740992 500000000313587 69686000000000000000 Bool.false 859839207605667 562949953421312 1000000000034843 69686000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz385) (@HMul.hMul Real Real Real qz0 qz70 (Real.log (Enclosure.sfrac Bool.false 13270708100 16000000))) Bool.false 30267448354014383 9007199254740992 500000000313587 69686000000000000000 (Enclosure.clog_re_eq 5000 115090 4000 13270708100 16000000 rfl rfl rfl) (ep601 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz385) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz383 qz335)) Bool.false 859839207605667 562949953421312 1000000000034843 69686000000000000000 (Enclosure.clog_im_eq 5000 115090 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz383 qz335)) (@HSub.hSub Real Real Real qz46 qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz335 qz383))) Bool.false 859839207605667 562949953421312 1000000000034843 69686000000000000000 (BSN.arctan_recip 115090 5000 rfl rfl) ep603)))) rfl rfl

noncomputable def ep605 := @ep506 ep500 Bool.false 30263376725017775 4503599627370496 500000000313587 34843000000000000000 Bool.false 869614553171363 281474976710656 1000000000034843 34843000000000000000 Bool.true ep507 40637558024882755859 900719925474099200 25759818001082699529301 ep504 Bool.false ep508 29180755228753940953 432345564227567616 178298829885604804363883 ep500 (@ep509 900719925474099200 24940618000568918588501 ep504 Bool.false 30516483182425154521 432345564227567616 158638029884919763109483 ep500 (BSN.logGammaStirling_unfold 1 qz152) (ep579 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep580 1000000000034843 34843000000000000000 (BSN.log_sum_c_eq qz139 2) (ep581 (BSN.log_sum_c_succ qz139 1 2 rfl) (ep604 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz178 := (@HDiv.hDiv Real Real Real qz257 qz359 (2 : Real))

noncomputable def ep606 := @Enclosure.Real.IsNear.mulLit_ff qz178 (Real.log Real.pi) 57545 2000 0 1 75021 65536 1 65536 863416689 26214400 11509 26214400 (@Enclosure.Real.IsNear.of_eq qz178 (Enclosure.sfrac Bool.false 57545 2000) Bool.false 57545 2000 0 1 (BSN.t_half_eq qz139 Bool.false 57545 1000 qz140) (Enclosure.Real.IsNear.const Bool.false 57545 2000)) EMRow12.d5 rfl

noncomputable def ep607 := @ep502 11509 26214400 ep503 373517622279590641201 10808639105689190400 479054895135604804363883 ep500 (@ep505 178298829885604804363883 ep500 (ep605 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep606 rfl rfl

noncomputable def ep608 := nat_lit 127254341953890948240996398458388897521509147394011069735960924013203619840

noncomputable def ep609 := nat_lit 255550425901093362390410389747241401050481368941796840648927831958552576

noncomputable def ep610 := nat_lit 332871432999207856139691807712380150287966035244123225852180346401886109696

noncomputable def ep611 := BSN.sin_dyadic_bound_f 843207724 536870912 3 2 262144 69755 ep608 ep116 ep609 ep610 ep119 ep609 262143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 843207724) qz276 0 2 ep608 ep116 ep609 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 843207724) qz277 0 2 ep610 ep119 ep609 rfl rfl rfl rfl) rfl rfl

noncomputable def ep612 := @ep499 32768 Bool.true 262143 262144 1 34843 (@ep501 4529497 131072 23 32768 ep607 rfl) (Enclosure.sfrac_false_div 4529497 131072) (BSN.cos_reduce1 qz371 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29667734338063170535424) qz275) 226375608064910080 72057594037927936 Bool.false 262143 262144 5 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q1 4529497 131072 226375608064910080 72057594037927936 5 29667734338063170535424 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 262143 262144 29667734338063170535424 18889465931478580854784 843207724 536870912 69755 69686 (ep611 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep613 := nat_lit 2183624451181978628339453

noncomputable def ep614 := nat_lit 285460393890770289111859200

noncomputable abbrev qz179 := qz358

noncomputable abbrev qz449 := (@Nat.cast Complex Complex.instNatCast 12)

noncomputable abbrev qz387 := (@HPow.hPow Complex Complex Complex qz430 qz449 qz445)

noncomputable abbrev qz180 := qz387

noncomputable abbrev qz388 := qz449

noncomputable abbrev qz181 := (@HAdd.hAdd Complex Complex Complex qz260 (@HDiv.hDiv Complex Complex Complex qz312 qz388 (@HSub.hSub Complex Complex Complex qz305 qz357 (1 : Complex))) qz311)

noncomputable abbrev qz182 := qz388

noncomputable def ep615 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz130 1 12) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 12, @HPow.hPow Complex Complex Complex qz99 (@Nat.cast Complex Complex.instNatCast n) qz179) (@HMul.hMul Complex Complex Complex qz45 qz180 (@HAdd.hAdd Complex Complex Complex qz5 qz181 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) Bool.false 6445422145170852694511 3495578300569085804544 ep496

noncomputable def ep616 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 12, @HPow.hPow Complex Complex Complex qz99 (@Nat.cast Complex Complex.instNatCast n) qz179) (@HMul.hMul Complex Complex Complex qz45 qz180 (@HAdd.hAdd Complex Complex Complex qz5 qz181 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) Bool.false 64992392741 34359738368 4378704288031 598598181978112

noncomputable def ep617 := nat_lit 3084439151236020328305283

noncomputable def ep618 := nat_lit 221463018579383813242865789698048

noncomputable def ep619 := nat_lit 993879114109813290509805813760

noncomputable def ep620 := @ep616 Bool.true 12408121729 68719476736 17504687560321 2394392727912448 Bool.true 166560615998447033617 3495578300569085804544 ep617 ep497 Bool.false 64433203358628198317 436947287571135725568 96709072742517764638553 ep614 Bool.false ep618 6445422145170852694511 3495578300569085804544 ep496 ep497 Bool.true ep619 14462844615770348035 436947287571135725568

noncomputable def ep621 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 12, @HPow.hPow Complex Complex Complex qz99 (@Nat.cast Complex Complex.instNatCast n) qz179) (BSN.headSumC qz130 12) Bool.false 64992392741 34359738368 4378704288031 598598181978112 Bool.true 12408121729 68719476736 17504687560321

noncomputable abbrev qz183 := (@HPow.hPow Complex Complex Complex qz261 qz338 qz358)

noncomputable def ep622 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz130 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz130 11) qz183) Bool.false 64992392741 34359738368 4378704288031 598598181978112 Bool.true 12408121729 68719476736 17504687560321 2394392727912448

noncomputable def ep623 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz130 11) qz183 Bool.false 109875762141 68719476736 16290000596667 2394392727912448 Bool.true 17400699203 68719476736 16286534833143 2394392727912448 Bool.false

noncomputable abbrev qz184 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 10) qz358)

noncomputable def ep624 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz130 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz130 10) qz184) Bool.false 109875762141 68719476736 16290000596667 2394392727912448 Bool.true 17400699203 68719476736 16286534833143 2394392727912448

noncomputable def ep625 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz130 10) qz184 Bool.false 91406476335 68719476736 15006934316565 2394392727912448 Bool.true 5950136593 68719476736 15006418640165 2394392727912448 Bool.false

noncomputable abbrev qz185 := (@HPow.hPow Complex Complex Complex qz261 (@Nat.cast Complex Complex.instNatCast 9) qz358)

noncomputable def ep626 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz130 10) (@HAdd.hAdd Complex Complex Complex qz5 qz129 qz185) Bool.false 91406476335 68719476736 15006934316565 2394392727912448 Bool.true 5950136593 68719476736 15006418640165 2394392727912448

noncomputable def ep627 := @Enclosure.Complex.IsNear.addLitP qz129 qz185 Bool.false 75050675517 68719476736 13656127261219 2394392727912448 Bool.false 10086898337 68719476736 13655738692083 2394392727912448 Bool.false

noncomputable abbrev qz186 := (@HMul.hMul Real Real Real qz254 qz359 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep628 := @Enclosure.Complex.IsNear.of_eq qz185 (Complex.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz186)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz186)))) Bool.false 8177900409 34359738368 675403527673 1197196363956224 Bool.true 8018517465 34359738368 675339974041 1197196363956224 (BSN.cpow_neg_s_mk qz139 57545 1000 9 qz140 rfl)

noncomputable def ep629 := @Enclosure.Real.IsNear.mulLit_ff qz139 qz111 57545 1000 0 1 9895417793173221 4503599627370496 1000000000104529 34843000000000000000 113886363381630600489 900719925474099200 11509000001203024261 6968600000000000000000 qz141 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000104529 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 10376097607894403383296 4722366482869645213696 1000000000104529 34843000000000000000 9895417793173221 4503599627370496 1000000000104529 34843000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 15438 131072 24973259072661432 36028797018963968 34843 1000000000000000 rfl rfl rfl rfl (ep298 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep630 := nat_lit 30056104767156228710518893635928241

noncomputable def ep631 := BSN.cos_dyadic_bound_f 416373589 536870912 2 1 262144 69755 ep630 ep57 ep630 ep630 ep58 ep630 187178 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 416373589) qz269 0 1 ep630 ep57 ep630 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 416373589) qz270 0 1 ep630 ep58 ep630 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz389 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16572647) qz20)

noncomputable def ep632 := @Enclosure.Real.IsNear.cos_image qz186 qz389 Bool.false 16572647 131072 217 131072 Bool.false 187178 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz186 Bool.false 113886363381630600489 900719925474099200 11509000001203024261 6968600000000000000000 16572647 131072 217 131072 (ep629 rfl) rfl) (Enclosure.sfrac_false_div 16572647 131072) (BSN.cos_reduce0 qz389 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14649843297057069072384) qz275) 226375608064910080 72057594037927936 Bool.false 187178 262144 20 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 16572647 131072 226375608064910080 72057594037927936 20 14649843297057069072384 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 187178 262144 14649843297057069072384 18889465931478580854784 416373589 536870912 69755 69686 (ep631 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep633 := BSN.sin_dyadic_bound_f 416373589 536870912 2 1 262144 69755 ep630 ep71 ep630 ep630 ep72 ep630 183530 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 416373589) qz276 0 1 ep630 ep71 ep630 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 416373589) qz277 0 1 ep630 ep72 ep630 rfl rfl rfl rfl) rfl rfl

noncomputable def ep634 := @Enclosure.Real.IsNear.sin_image qz186 qz389 Bool.false 16572647 131072 217 131072 Bool.false 183530 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz186 Bool.false 113886363381630600489 900719925474099200 11509000001203024261 6968600000000000000000 16572647 131072 217 131072 (ep629 rfl) rfl) (Enclosure.sfrac_false_div 16572647 131072) (BSN.sin_reduce0 qz389 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14649843297057069072384) qz275) 226375608064910080 72057594037927936 Bool.false 183530 262144 20 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 16572647 131072 226375608064910080 72057594037927936 20 14649843297057069072384 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 183530 262144 14649843297057069072384 18889465931478580854784 416373589 536870912 69755 69686 (ep633 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep635 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz186)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz186))) Bool.false 8177900409 34359738368 675403527673 1197196363956224 Bool.true 8018517465 34359738368 675339974041 1197196363956224 (@Enclosure.Real.IsNear.mulLit_ff qz109 (Real.cos qz186) 87381 262144 1 262144 93589 131072 7692003 4566941696 8177900409 34359738368 675403527673 1197196363956224 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz186) Bool.false 187178 262144 7692003 4566941696 93589 131072 7692003 4566941696 (ep632 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz109 (@Neg.neg Real Real.instNeg (Real.sin qz186)) 87381 262144 1 262144 91765 131072 7692003 4566941696 8018517465 34359738368 675339974041 1197196363956224 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz186) Bool.false 91765 131072 7692003 4566941696 (@Enclosure.Real.IsNear.recentre' (Real.sin qz186) Bool.false 183530 262144 7692003 4566941696 91765 131072 7692003 4566941696 (ep634 rfl rfl) rfl)) rfl)

noncomputable def ep636 := @ep627 8177900409 34359738368 675403527673 1197196363956224 Bool.true 8018517465 34359738368 675339974041 1197196363956224 Bool.false 3140702612011383521280 91406476335 68719476736 15006934316565 2394392727912448 Bool.true 204445136589342900224 5950136593 68719476736 15006418640165 2394392727912448 EMRow12.d10 (ep628 ep635) rfl rfl

noncomputable abbrev qz187 := (@HMul.hMul Real Real Real qz254 qz359 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep637 := @Enclosure.Complex.IsNear.of_eq qz184 (Complex.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz187)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz187)))) Bool.false 9234642903 34359738368 641533140051 1197196363956224 Bool.true 5725281305 34359738368 640058096489 1197196363956224 (BSN.cpow_neg_s_mk qz139 57545 1000 10 qz140 rfl)

noncomputable def ep638 := @Enclosure.Real.IsNear.mulLit_ff qz139 qz114 57545 1000 0 1 10369891420296933 4503599627370496 1000000000104529 34843000000000000000 119347080356197401897 900719925474099200 11509000001203024261 6968600000000000000000 qz141 (BSN.isNear_log_sfrac 10 1 10369891420296933 4503599627370496 1000000000104529 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false 10873619265929276817408 4722366482869645213696 1000000000104529 34843000000000000000 10369891420296933 4503599627370496 1000000000104529 34843000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 29247 131072 24973259072661432 36028797018963968 34843 1000000000000000 rfl rfl rfl rfl (ep309 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep639 := nat_lit 7881225001869997787928644443631761

noncomputable def ep640 := BSN.cos_dyadic_bound_f 297953459 536870912 2 1 262144 69755 ep639 ep57 ep639 ep639 ep58 ep639 222798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 297953459) qz269 0 1 ep639 ep57 ep639 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 297953459) qz270 0 1 ep639 ep58 ep639 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz390 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 34734571) qz27)

noncomputable def ep641 := @Enclosure.Real.IsNear.cos_image qz187 qz390 Bool.false 34734571 262144 217 131072 Bool.false 222798 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz187 Bool.false 119347080356197401897 900719925474099200 11509000001203024261 6968600000000000000000 34734571 262144 217 131072 (ep638 rfl) rfl) (Enclosure.sfrac_false_div 34734571 262144) (BSN.cos_reduce0 qz390 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20966610751474978783232) qz29) 226375608064910080 72057594037927936 Bool.false 222798 262144 21 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 34734571 262144 226375608064910080 72057594037927936 21 20966610751474978783232 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 222798 262144 20966610751474978783232 37778931862957161709568 297953459 536870912 69755 69686 (ep640 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep642 := BSN.sin_dyadic_bound_f 297953459 536870912 2 1 262144 69755 ep639 ep71 ep639 ep639 ep72 ep639 138130 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 297953459) qz276 0 1 ep639 ep71 ep639 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 297953459) qz277 0 1 ep639 ep72 ep639 rfl rfl rfl rfl) rfl rfl

noncomputable def ep643 := @Enclosure.Real.IsNear.sin_image qz187 qz390 Bool.false 34734571 262144 217 131072 Bool.false 138130 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz187 Bool.false 119347080356197401897 900719925474099200 11509000001203024261 6968600000000000000000 34734571 262144 217 131072 (ep638 rfl) rfl) (Enclosure.sfrac_false_div 34734571 262144) (BSN.sin_reduce0 qz390 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20966610751474978783232) qz29) 226375608064910080 72057594037927936 Bool.false 138130 262144 21 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q0 34734571 262144 226375608064910080 72057594037927936 21 20966610751474978783232 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 138130 262144 20966610751474978783232 37778931862957161709568 297953459 536870912 69755 69686 (ep642 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep644 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz187)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz187))) Bool.false 9234642903 34359738368 641533140051 1197196363956224 Bool.true 5725281305 34359738368 640058096489 1197196363956224 (@Enclosure.Real.IsNear.mulLit_ff qz112 (Real.cos qz187) 82897 262144 1 262144 111399 131072 7692003 4566941696 9234642903 34359738368 641533140051 1197196363956224 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz187) Bool.false 222798 262144 7692003 4566941696 111399 131072 7692003 4566941696 (ep641 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz112 (@Neg.neg Real Real.instNeg (Real.sin qz187)) 82897 262144 1 262144 69065 131072 7692003 4566941696 5725281305 34359738368 640058096489 1197196363956224 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz187) Bool.false 69065 131072 7692003 4566941696 (@Enclosure.Real.IsNear.recentre' (Real.sin qz187) Bool.false 138130 262144 7692003 4566941696 69065 131072 7692003 4566941696 (ep643 rfl rfl) rfl)) rfl)

noncomputable def ep645 := @ep625 9234642903 34359738368 641533140051 1197196363956224 Bool.true 5725281305 34359738368 640058096489 1197196363956224 Bool.false 3775302440149359525888 109875762141 68719476736 16290000596667 2394392727912448 Bool.true 597883472035346120704 17400699203 68719476736 16286534833143 2394392727912448 (ep626 (BSN.head_sum_c_succ qz130 9 10 rfl rfl) (ep636 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep637 ep644) rfl rfl

noncomputable abbrev qz188 := (@HMul.hMul Real Real Real qz254 qz359 qz351)

noncomputable def ep646 := @Enclosure.Complex.IsNear.of_eq qz183 (Complex.mk (@HMul.hMul Real Real Real qz0 qz117 (Real.cos qz188)) (@HMul.hMul Real Real Real qz0 qz117 (@Neg.neg Real Real.instNeg (Real.sin qz188)))) Bool.false 20109023341 68719476736 1224816555457 2394392727912448 Bool.false 2496288737 34359738368 609076363589 1197196363956224 (BSN.cpow_neg_s_mk qz139 57545 1000 11 qz140 rfl)

noncomputable def ep647 := @Enclosure.Real.IsNear.mulLit_ff qz139 qz120 57545 1000 0 1 10799147631728357 4503599627370496 1000000000104529 34843000000000000000 124287390093561660713 900719925474099200 11509000001203024261 6968600000000000000000 qz141 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 1000000000104529 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz352 Bool.false 11323727027087193669632 4722366482869645213696 1000000000104529 34843000000000000000 10799147631728357 4503599627370496 1000000000104529 34843000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 41740 131072 24973259072661432 36028797018963968 34843 1000000000000000 rfl rfl rfl rfl (ep325 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep648 := nat_lit 64870444318161960128684768534958664218029271773582238547051106531072412865

noncomputable def ep649 := nat_lit 66539538243354448119275713232811898330467241908471151770368191746936001

noncomputable def ep650 := nat_lit 169791052057077797897219375960610044164208288634387385758458016223313661121

noncomputable def ep651 := BSN.sin_dyadic_bound_f 712664249 536870912 3 2 262144 69755 ep648 ep116 ep649 ep650 ep119 ep649 254419 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 712664249) qz276 0 2 ep648 ep116 ep649 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 712664249) qz277 0 2 ep650 ep119 ep649 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz391 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 36172391) qz27)

noncomputable def ep652 := @Enclosure.Real.IsNear.cos_image qz188 qz391 Bool.false 36172391 262144 217 131072 Bool.false 254419 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz188 Bool.false 124287390093561660713 900719925474099200 11509000001203024261 6968600000000000000000 36172391 262144 217 131072 (ep647 rfl) rfl) (Enclosure.sfrac_false_div 36172391 262144) (BSN.cos_reduce3 qz391 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 50149288268998704627712) qz29) 226375608064910080 72057594037927936 Bool.false 254419 262144 21 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q3 36172391 262144 226375608064910080 72057594037927936 21 50149288268998704627712 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 254419 262144 50149288268998704627712 37778931862957161709568 712664249 536870912 69755 69686 (ep651 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep653 := nat_lit 36068708860420357603988993947524952075940914203949453038037445046927756481

noncomputable def ep654 := nat_lit 108073047504774363915728430416109232431161808128031416810571598757289397441

noncomputable def ep655 := BSN.cos_dyadic_bound_f 712664249 536870912 3 2 262144 69755 ep653 ep123 ep649 ep654 ep125 ep649 63166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 712664249) qz269 0 2 ep653 ep123 ep649 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 712664249) qz270 0 2 ep654 ep125 ep649 rfl rfl rfl rfl) rfl rfl

noncomputable def ep656 := @Enclosure.Real.IsNear.sin_image qz188 qz391 Bool.false 36172391 262144 217 131072 Bool.true 63166 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz188 Bool.false 124287390093561660713 900719925474099200 11509000001203024261 6968600000000000000000 36172391 262144 217 131072 (ep647 rfl) rfl) (Enclosure.sfrac_false_div 36172391 262144) (BSN.sin_reduce3 qz391 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 50149288268998704627712) qz29) 226375608064910080 72057594037927936 Bool.false 63166 262144 21 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q3 36172391 262144 226375608064910080 72057594037927936 21 50149288268998704627712 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 63166 262144 50149288268998704627712 37778931862957161709568 712664249 536870912 69755 69686 (ep655 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep657 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz117 (Real.cos qz188)) (@HMul.hMul Real Real Real qz0 qz117 (@Neg.neg Real Real.instNeg (Real.sin qz188))) Bool.false 20109023341 68719476736 1224816555457 2394392727912448 Bool.false 2496288737 34359738368 609076363589 1197196363956224 (@Enclosure.Real.IsNear.mulLit_ff qz117 (Real.cos qz188) 79039 262144 1 262144 254419 262144 7692003 4566941696 20109023341 68719476736 1224816555457 2394392727912448 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz188) Bool.false 254419 262144 7692003 4566941696 254419 262144 7692003 4566941696 (ep652 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz117 (@Neg.neg Real Real.instNeg (Real.sin qz188)) 79039 262144 1 262144 31583 131072 7692003 4566941696 2496288737 34359738368 609076363589 1197196363956224 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz188) Bool.true 31583 131072 7692003 4566941696 (@Enclosure.Real.IsNear.recentre' (Real.sin qz188) Bool.true 63166 262144 7692003 4566941696 31583 131072 7692003 4566941696 (ep656 rfl rfl) rfl)) rfl)

noncomputable def ep658 := @ep623 20109023341 68719476736 1224816555457 2394392727912448 Bool.false 2496288737 34359738368 609076363589 1197196363956224 Bool.false 8932486441964249546752 64992392741 34359738368 4378704288031 598598181978112 Bool.true 426339816246735798272 12408121729 68719476736 17504687560321 2394392727912448 (ep624 (BSN.head_sum_c_succ qz130 10 11 rfl rfl) (ep645 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep646 ep657) rfl rfl

noncomputable def ep659 := @Enclosure.Complex.IsNear.mul qz180 (@HAdd.hAdd Complex Complex Complex qz5 qz181 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.true 166560615998447033617 3495578300569085804544 ep617 ep497 Bool.false

noncomputable abbrev qz189 := (Complex.re qz387)

noncomputable abbrev qz190 := (Complex.im qz387)

noncomputable def ep660 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz189 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz181 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz190 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz181 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 542152231825167875 72824547928522620928 1857512760330203264615

noncomputable def ep661 := nat_lit 7612277170420541042982912

noncomputable def ep662 := nat_lit 12129701562783157636912003730843763736576

noncomputable def ep663 := @Enclosure.Real.IsNear.mulLit_ff qz189 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz181 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 254949075 17179869184 291167395581 598598181978112 19138606745

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz446 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable abbrev qz191 := (Real.cos qz392)

noncomputable abbrev qz192 := (@Neg.neg Real Real.instNeg (Real.sin qz392))

noncomputable abbrev qz393 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq qz180 (Complex.mk (@HMul.hMul Real Real Real qz0 qz393 qz191) (@HMul.hMul Real Real Real qz0 qz393 qz192)) Bool.false 254949075 17179869184 291167395581 598598181978112 Bool.false 19811487975 68719476736 1173321830927 2394392727912448 (BSN.cpow_neg_s_mk qz139 57545 1000 12 qz140 rfl)

noncomputable abbrev qz394 := (Real.sqrt (@Nat.cast Real Real.instNatCast 12))

noncomputable abbrev qz395 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12) qz19)

noncomputable def ep665 := @Enclosure.Real.IsNear.inv_image qz394 908093 262144 1 262144 37837 37838 131072 (@Enclosure.Real.IsNear.of_eq qz394 (Real.sqrt qz395) Bool.false 908093 262144 1 262144 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz395) Bool.false 908093 262144 1 262144 908093 262144 1 262144 (BSN.sqrt_enclosure 12 1 454046 454047 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep666 := BSN.log_dyadic_bound 4 20 4 3 6720000000 131072 34843 91811840 61440 53145 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz396 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz193 := qz396

noncomputable def ep667 := @Enclosure.Real.IsNear.mulLit_ff qz139 qz193 57545 1000 0 1 11191020447815397 4503599627370496 1000000000104529 34843000000000000000 128797454333907404073 900719925474099200 11509000001203024261 6968600000000000000000 qz141 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000104529 34843000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz395) Bool.false 11734635457088477724672 4722366482869645213696 1000000000104529 34843000000000000000 11191020447815397 4503599627370496 1000000000104529 34843000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 53145 131072 24973259072661432 36028797018963968 34843 1000000000000000 rfl rfl rfl rfl (ep666 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep668 := BSN.sin_dyadic_bound_f 27611671 536870912 1 0 262144 69755 0 1 1 0 1 1 13476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 27611671) qz276 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 27611671) qz277 0 0 rfl) rfl rfl

noncomputable abbrev qz194 := qz392

noncomputable abbrev qz397 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 585703) (@Nat.cast Real Real.instNatCast 4096))

noncomputable def ep669 := @Enclosure.Real.IsNear.cos_image qz194 qz397 Bool.false 585703 4096 217 131072 Bool.false 13476 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 128797454333907404073 900719925474099200 11509000001203024261 6968600000000000000000 585703 4096 217 131072 (ep667 rfl) rfl) (Enclosure.sfrac_false_div 585703 4096) (BSN.cos_reduce3 qz397 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 30359353910688219136) (@Nat.cast Real Real.instNatCast 590295810358705651712)) 226375608064910080 72057594037927936 Bool.false 13476 262144 22 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q3 585703 4096 226375608064910080 72057594037927936 22 30359353910688219136 590295810358705651712 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13476 262144 30359353910688219136 590295810358705651712 27611671 536870912 69755 69686 (ep668 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep670 := BSN.cos_dyadic_bound_f 27611671 536870912 1 0 262144 69755 0 1 1 0 1 1 261797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 27611671) qz269 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 27611671) qz270 0 0 rfl) rfl rfl

noncomputable def ep671 := @Enclosure.Real.IsNear.sin_image qz194 qz397 Bool.false 585703 4096 217 131072 Bool.true 261797 262144 1 34843 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 128797454333907404073 900719925474099200 11509000001203024261 6968600000000000000000 585703 4096 217 131072 (ep667 rfl) rfl) (Enclosure.sfrac_false_div 585703 4096) (BSN.sin_reduce3 qz397 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 30359353910688219136) (@Nat.cast Real Real.instNatCast 590295810358705651712)) 226375608064910080 72057594037927936 Bool.false 261797 262144 22 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q3 585703 4096 226375608064910080 72057594037927936 22 30359353910688219136 590295810358705651712 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 261797 262144 30359353910688219136 590295810358705651712 27611671 536870912 69755 69686 (ep670 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz195 := (Real.sin qz392)

noncomputable def ep672 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz393 qz191) (@HMul.hMul Real Real Real qz0 qz393 qz192) Bool.false 254949075 17179869184 291167395581 598598181978112 Bool.false 19811487975 68719476736 1173321830927 2394392727912448 (@Enclosure.Real.IsNear.mulLit_ff qz393 qz191 75675 262144 1 262144 3369 65536 7692003 4566941696 254949075 17179869184 291167395581 598598181978112 (@Enclosure.Real.IsNear.recentre' qz393 Bool.false 75675 262144 1 262144 75675 262144 1 262144 (ep665 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz191 Bool.false 13476 262144 7692003 4566941696 3369 65536 7692003 4566941696 (ep669 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz393 qz192 75675 262144 1 262144 261797 262144 7692003 4566941696 19811487975 68719476736 1173321830927 2394392727912448 (@Enclosure.Real.IsNear.recentre' qz393 Bool.false 75675 262144 1 262144 75675 262144 1 262144 (ep665 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz195 Bool.true 261797 262144 7692003 4566941696 (@Enclosure.Real.IsNear.recentre' qz195 Bool.true 261797 262144 7692003 4566941696 261797 262144 7692003 4566941696 (ep671 rfl rfl) rfl)) rfl)

noncomputable def ep673 := @ep663 38150519328 0 1 542152231825167875 72824547928522620928 1857512760330203264615 ep661 (@Enclosure.Complex.IsNear.re_isNear qz180 Bool.false 254949075 17179869184 291167395581 598598181978112 Bool.false 19811487975 68719476736 1173321830927 2394392727912448 (ep664 ep672))

noncomputable def ep674 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz181 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 19138606745 38150519328 0 1 Bool.false

noncomputable def ep675 := @Enclosure.Complex.IsNear.addLitP qz181 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) Bool.false 131987081 264934162 0 1 Bool.true 27621600

noncomputable def ep676 := @ep675 132467081 0 1 Bool.false 1 288 0 1 Bool.false 11509 28800 0 1 Bool.false 38277213490 19138606745 38150519328 0 1 Bool.false 729061555229 729061555229 3815051932800 0 1

noncomputable abbrev qz196 := (@HDiv.hDiv Complex Complex Complex qz312 qz388 (@HSub.hSub Complex Complex Complex qz305 qz357 (1 : Complex)))

noncomputable def ep677 := @Enclosure.Complex.IsNear.addLitP qz196 qz75 Bool.true 24000000 13246708100 0 1 Bool.true 2762160000 13246708100 0 1

noncomputable def ep678 := @Enclosure.Complex.IsNear.of_eq qz196 (Complex.mk (Enclosure.sfrac Bool.true 24000000 13246708100) (Enclosure.sfrac Bool.true 2762160000 13246708100)) Bool.true 24000000 13246708100 0 1 Bool.true 2762160000 13246708100 0 1

noncomputable def ep679 := @ep677 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 13198708100 131987081 264934162 0 1 Bool.true 2762160000 27621600 132467081 0 1 (ep678 (BSN.N_div_s_sub_one_mk qz139 57545 1000 12 qz140 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 24000000 13246708100) (Enclosure.sfrac Bool.true 2762160000 13246708100) Bool.true 24000000 13246708100 0 1 Bool.true 2762160000 13246708100 0 1 (Enclosure.Real.IsNear.const Bool.true 24000000 13246708100) (Enclosure.Real.IsNear.const Bool.true 2762160000 13246708100))) qz76 rfl

noncomputable abbrev qz398 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz442 qz449 1))

noncomputable abbrev qz197 := qz398

noncomputable def ep680 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) qz197)) Bool.false 1 288 0 1

noncomputable def ep681 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) qz197) Bool.false 0 1 0 1 Bool.false

noncomputable def ep682 := @ep681 0 1 0 1 Bool.false 1 288 0 1 Bool.false 11509 28800 0 1 Bool.false 1 1 288 0 1 Bool.false 11509 11509 28800 0

noncomputable def ep683 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep684 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) qz197 Bool.false 1 288 0 1 Bool.false 11509 28800 0 1

noncomputable abbrev qz198 := (Complex.re qz398)

noncomputable abbrev qz199 := (Complex.im qz398)

noncomputable def ep685 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199) 1 288 0 1 0 1 0

noncomputable def ep686 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198 1 24 0 1 1 12 0 1 1

noncomputable def ep687 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep688 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep689 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)) qz130 Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 (BSN.ascPochhammer_one_eval qz130)

noncomputable def ep690 := ep689 (@Enclosure.Complex.IsNear.of_eq qz130 (Complex.mk qz70 qz139) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 (BSN.s_crit_mk qz139 Bool.false 57545 1000 qz140) (@Enclosure.Complex.IsNear.mk qz70 qz139 Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 qz321 qz141))

noncomputable def ep691 := @ep688 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep690)

noncomputable def ep692 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 57545 1000 0 1 0 1 0

noncomputable def ep693 := @ep692 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep690)

noncomputable def ep694 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)))) 11509 2400 0 1 0 1 0 1 11509

noncomputable def ep695 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 57545 1000 0 1 11509 2400 0

noncomputable def ep696 := @ep695 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep690)

noncomputable def ep697 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep698 := @ep697 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep349) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep690)

noncomputable def ep699 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 11509 2400 0 1 (@ep687 1 24 0 1 (ep691 rfl) (ep693 rfl) rfl rfl) (@ep694 11509 2400 0 1 (ep696 rfl) (ep698 rfl) rfl rfl)

noncomputable def ep700 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 11509 2400 0 1 ep699

noncomputable abbrev qz200 := (@Enclosure.Complex.IsNear.of_eq qz398 (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz265) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 12 1 12 EMRow12.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz265 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz279))

noncomputable def ep701 := @ep686 288 0 1 ep700 (@Enclosure.Complex.IsNear.re_isNear qz197 Bool.false 1 12 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep702 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199 11509 2400 0 1 0 1 0 1 0

noncomputable def ep703 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 11509 2400 0 1 ep699

noncomputable def ep704 := @ep702 1 0 1 ep703 (@Enclosure.Complex.IsNear.im_isNear qz197 Bool.false 1 12 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep705 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198) 0 1 0 1 11509 28800 0

noncomputable def ep706 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)))) qz199 1 24 0 1 0 1 0 1 0

noncomputable def ep707 := @ep706 1 0 1 ep700 (@Enclosure.Complex.IsNear.im_isNear qz197 Bool.false 1 12 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep708 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz124) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)))) qz198 11509 2400 0 1 1 12 0 1 11509

noncomputable def ep709 := @ep708 28800 0 1 ep703 (@Enclosure.Complex.IsNear.re_isNear qz197 Bool.false 1 12 0 1 Bool.false 0 1 0 1 qz200)

noncomputable def ep710 := @ep682 1 (@ep683 0 1 0 1 (BSN.bern_sum_base qz130 12) qz93) (ep684 (@ep685 1 1 1 288 0 1 (ep701 rfl) (ep704 rfl) rfl rfl) (@ep705 1 11509 11509 28800 0 1 (ep707 rfl) (ep709 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep711 := ep676 (ep679 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep680 Bool.false 11509 28800 0 1 (BSN.bern_sum_succ qz130 12 0 1 1 rfl rfl) (ep710 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep712 := @Enclosure.Real.IsNear.mulLit_ff qz190 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz181 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 19811487975 68719476736 1173321830927 2394392727912448 729061555229

noncomputable def ep713 := @ep712 3815051932800 0 1 192583923126055091617 3495578300569085804544 855423838839776410767283 ep497 (@Enclosure.Complex.IsNear.im_isNear qz180 Bool.false 254949075 17179869184 291167395581 598598181978112 Bool.false 19811487975 68719476736 1173321830927 2394392727912448 (ep664 ep672))

noncomputable def ep714 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz181 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 19138606745 38150519328 0 1 Bool.false

noncomputable def ep715 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz189 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz181 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz190 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz181 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 826104751660866503 291298191714090483712 70759651418087107347683

noncomputable def ep716 := nat_lit 761227717042054104298291200

noncomputable def ep717 := nat_lit 91347326045046492515794944

noncomputable def ep718 := nat_lit 37538551249429311529615635383899188625408

noncomputable def ep719 := @Enclosure.Real.IsNear.mulLit_ff qz189 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz181 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 254949075 17179869184 291167395581 598598181978112 729061555229

noncomputable def ep720 := @ep719 3815051932800 0 1 826104751660866503 291298191714090483712 70759651418087107347683 ep716 (@Enclosure.Complex.IsNear.re_isNear qz180 Bool.false 254949075 17179869184 291167395581 598598181978112 Bool.false 19811487975 68719476736 1173321830927 2394392727912448 (ep664 ep672))

noncomputable def ep721 := @Enclosure.Real.IsNear.mulLit_ff qz190 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz181 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz104 qz182 (@HSub.hSub Nat Nat Nat qz103 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 19811487975 68719476736 1173321830927 2394392727912448 19138606745

noncomputable def ep722 := @ep721 38150519328 0 1 126388092462273797125 873894575142271451136 22455745107435231802615 ep717 (@Enclosure.Complex.IsNear.im_isNear qz180 Bool.false 254949075 17179869184 291167395581 598598181978112 Bool.false 19811487975 68719476736 1173321830927 2394392727912448 (ep664 ep672))

noncomputable abbrev qz399 := (ep711 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep723 := @ep659 64433203358628198317 436947287571135725568 96709072742517764638553 ep614 (@ep660 ep661 192583923126055091617 3495578300569085804544 855423838839776410767283 ep497 ep662 166560615998447033617 3495578300569085804544 ep617 ep497 (ep673 (@ep674 729061555229 3815051932800 0 1 qz399) rfl) (ep713 (@ep714 729061555229 3815051932800 0 1 qz399) rfl) rfl rfl) (@ep715 ep716 126388092462273797125 873894575142271451136 22455745107435231802615 ep717 ep718 64433203358628198317 436947287571135725568 96709072742517764638553 ep614 (ep720 (@ep714 729061555229 3815051932800 0 1 qz399) rfl) (ep722 (@ep674 729061555229 3815051932800 0 1 qz399) rfl) rfl rfl)

noncomputable def ep724 := @ep620 ep613 ep614 (@ep621 2394392727912448 (BSN.head_sum_c_eq qz130 12) (ep622 (BSN.head_sum_c_succ qz130 11 12 rfl rfl) (ep658 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep723 rfl rfl rfl

noncomputable def ep725 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz130 1 12) Bool.false 6445422145170852694511 3495578300569085804544 ep496 ep497 Bool.true 14462844615770348035 436947287571135725568 ep613 ep614 (@ep615 ep497 Bool.true 14462844615770348035 436947287571135725568 ep613 ep614 (BSN.zetaApproximant_eq_folded' qz130 1 12 rfl) (ep724 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep726 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))))) qz150)) (Complex.im (zetaApproximant qz130 1 12)) 13 65536 834157

noncomputable def ep727 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))))) qz150)) Bool.false 52 262144 834157

noncomputable def ep728 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))))) qz150) qz371 Bool.false 4529497 131072 23

noncomputable def ep729 := nat_lit 70810434608117679406060403761214828134638629160646948449155592377094701056

noncomputable def ep730 := nat_lit 211920202972550851493400390504150001601814924744057251666168921467366998016

noncomputable def ep731 := BSN.cos_dyadic_bound_f 843207724 536870912 3 2 262144 69755 ep729 ep123 ep609 ep730 ep125 ep609 52 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 843207724) qz269 0 2 ep729 ep123 ep609 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 843207724) qz270 0 2 ep730 ep125 ep609 rfl rfl rfl rfl) rfl rfl

noncomputable def ep732 := @ep728 32768 Bool.false 52 262144 1 34843 (@ep501 4529497 131072 23 32768 ep607 rfl) (Enclosure.sfrac_false_div 4529497 131072) (BSN.sin_reduce1 qz371 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29667734338063170535424) qz275) 226375608064910080 72057594037927936 Bool.false 52 262144 5 1000000000000000 69686 34843 (BSN.sin_reduce_arg_pos_rat_q1 4529497 131072 226375608064910080 72057594037927936 5 29667734338063170535424 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 52 262144 29667734338063170535424 18889465931478580854784 843207724 536870912 69755 69686 (ep731 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep733 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz130 1 12) Bool.false 6445422145170852694511 3495578300569085804544 ep496 ep497 Bool.true 14462844615770348035 436947287571135725568 ep613 ep614 (@ep615 ep497 Bool.true 14462844615770348035 436947287571135725568 ep613 ep614 (BSN.zetaApproximant_eq_folded' qz130 1 12 rfl) (ep724 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow12.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 12 qz139) Bool.true ep480 ep481 ep482 ep483 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 12 qz139) ep484 Bool.true ep480 ep481 ep482 ep483 (@Eq.refl Real ep484) (@ep485 Bool.true ep480 ep481 ep482 ep483 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz46 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz148 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz149 (@Nat.cast Complex Complex.instNatCast j))))) qz150) (zetaApproximant qz130 1 12)) (@ep487 ep488 ep489 ep490 188016980005014524455 ep491 ep492 ep493 ep494 ep480 ep481 ep482 ep483 (@ep495 1141735424 6445422145170852694511 3495578300569085804544 ep496 ep497 ep486 ep488 ep489 ep490 (@ep498 1141735424 262143 262144 834157 1141735424 (ep612 rfl rfl) rfl) ep725 rfl) (@ep726 1141735424 14462844615770348035 436947287571135725568 ep613 ep614 188016980005014524455 ep491 ep492 ep493 (@ep727 1141735424 13 65536 834157 1141735424 (ep732 rfl rfl) rfl) ep733 rfl) rfl rfl))

theorem EMRow12.d13 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow12.d14 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow12.d15 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow12.d16 : @Eq Nat (Nat.pow 11 (Nat.succ (Nat.mul 2 3))) 19487171 := @Eq.refl Nat 19487171

noncomputable abbrev qz450 := (@HAdd.hAdd Complex Complex Complex qz453 qz452 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz400 := qz450

noncomputable abbrev qz201 := (@HDiv.hDiv Real Real Real qz257 (@Norm.norm Complex Complex.instNorm qz400) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz259) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz202 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz203 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz401 := (@HPow.hPow Complex Complex Complex qz430 qz443 (@HSub.hSub Complex Complex Complex qz436 qz431 qz432))

noncomputable abbrev qz204 := qz401

noncomputable def ep734 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 11))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) 2580739087 57982058496 6545741 57982058496 113452179645873 140737488355328 1951088235

noncomputable def ep735 := nat_lit 6941397653930511165292544

noncomputable def ep736 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 11)) 6641 442368 1 442368 388607 131072 927 131072 2580739087 57982058496

noncomputable abbrev qz402 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz205 := (@HPow.hPow Real Nat Real qz402 qz258 2)

noncomputable def ep737 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz205) 96 162 0 1 6641 262144 1 262144 6641 442368 1 442368

noncomputable def ep738 := nat_lit 781950621441006189802102638025

noncomputable def ep739 := nat_lit 19807040628566084398385987584

noncomputable def ep740 := nat_lit 26986075409044041160201671

noncomputable def ep741 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz206 := qz258

noncomputable abbrev qz403 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz206 1)

noncomputable def ep742 := @Enclosure.Real.IsNear.mulLit_ff qz403 qz206 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep738 ep739 ep740 ep741

noncomputable def ep743 := ep742 (@Enclosure.Real.IsNear.of_eq qz403 qz206 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz206) (@Enclosure.Real.IsNear.of_eq qz206 qz255 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz256)) (@Enclosure.Real.IsNear.of_eq qz206 qz255 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz256) rfl

noncomputable def ep744 := @Enclosure.Real.IsNear.inv_image qz205 ep738 ep739 ep740 ep741 3320 3321 131072 (@Enclosure.Real.IsNear.of_eq qz205 (@HMul.hMul Real Real Real qz0 qz403 qz206) Bool.false ep738 ep739 ep740 ep741 (BSN.pow_succ_r qz206 1 2 rfl) ep743) rfl rfl rfl

noncomputable def ep745 := ep737 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz205) Bool.false 6641 262144 1 262144 6641 262144 1 262144 (ep744 rfl rfl rfl) rfl)

noncomputable def ep746 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 11)) (Real.sqrt (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 11)) (Complex.re (zetaApproximant qz6 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 11)) (Complex.im (zetaApproximant qz6 1 11))))) Bool.false 388607 131072 927 131072

noncomputable def ep747 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 11)) (Complex.re (zetaApproximant qz6 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 11)) (Complex.im (zetaApproximant qz6 1 11))))) Bool.false 777214 262144 1854 262144

noncomputable def ep748 := nat_lit 1107122060782168536610047460426933253

noncomputable def ep749 := nat_lit 125948039931026875086299617107640320

noncomputable def ep750 := nat_lit 10218111606428881779711807876992393562168506212517

noncomputable def ep751 := nat_lit 243800799191281406597915482913688454892362546544640

noncomputable def ep752 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 11)) (Complex.re (zetaApproximant qz6 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 11)) (Complex.im (zetaApproximant qz6 1 11)))) ep748 ep749 ep750 ep751 387680 389534

noncomputable def ep753 := nat_lit 26448286616700340035367391952497776776231841

noncomputable def ep754 := nat_lit 3012279749084180462273389565922781849190400

noncomputable def ep755 := nat_lit 13462696710380523031514257870749228105498288790177

noncomputable def ep756 := nat_lit 332455635260838281724430203973211529398676199833600

noncomputable def ep757 := nat_lit 53090463728061837867948960376423022769

noncomputable def ep758 := nat_lit 5229652342160035524780190218615940710400

noncomputable def ep759 := nat_lit 80968910660116771078441899635068660500725257747

noncomputable def ep760 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 11)) (Complex.re (zetaApproximant qz6 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 11)) (Complex.im (zetaApproximant qz6 1 11))) ep753 ep754 ep755 ep756 ep757 ep758 ep759

noncomputable def ep761 := nat_lit 57140812310456579671386441307895731615397471846400

noncomputable def ep762 := nat_lit 138475267379904383903404245597067696899128562661549944650852707790801817844056064000

noncomputable def ep763 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz6 1 11)) (Complex.re (zetaApproximant qz6 1 11)) 5142789769833134063279 1735592045696274923520 412743795705959150742037 ep156 5142789769833134063279 1735592045696274923520 412743795705959150742037 ep156 ep753

noncomputable def ep764 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz6 1 11)) (Complex.im (zetaApproximant qz6 1 11)) 7286320314676114887 72316335237344788480 51419189718178439256703 ep285 7286320314676114887 72316335237344788480 51419189718178439256703 ep285 ep757

noncomputable def ep765 := @ep734 985162418487296 ep735 3232340167244203 3799912185593856 3055551157577 26599385299156992 (@ep736 6545741 57982058496 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz205)) Bool.false 6641 442368 1 442368 (BSN.theta_err_eq 1 2 96 162 EMRow12.d13 EMRow12.d14 rfl) (ep745 rfl)) (ep746 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz6 1 11)) (@ep747 388607 131072 927 131072 (@ep752 131072 (@ep760 ep761 ep762 ep748 ep749 ep750 ep751 (@ep763 ep754 ep755 ep756 ep386 ep386 rfl) (@ep764 ep758 ep759 ep761 ep394 ep394 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz207 := (@Norm.norm Complex Complex.instNorm qz400)

noncomputable abbrev qz404 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep766 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz207 qz404) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) Bool.false 113452179645873 140737488355328 1951088235 985162418487296 (BSN.zrb_shape_eq qz207 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) qz17 3)

noncomputable def ep767 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz207 qz404) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) 2051723 131072 1 917504 55296051 1073741824 33 268435456

noncomputable def ep768 := @Enclosure.Real.IsNear.mulLit_ff qz207 qz404 14362061 262144 1 262144 2 7 0 1 2051723 131072

noncomputable abbrev qz405 := (Complex.re qz450)

noncomputable abbrev qz406 := (Complex.im qz450)

noncomputable abbrev qz208 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz254 qz405 qz405) (@HMul.hMul Real Real Real qz254 qz406 qz406))

noncomputable abbrev qz209 := qz400

noncomputable def ep769 := @Enclosure.Real.IsNear.of_eq qz207 (Real.sqrt qz208) Bool.false 14362061 262144 1 262144 (BSN.norm_eq_sqrt_mul_add qz209)

noncomputable def ep770 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz208) Bool.false 14362061 262144 1 262144 14362061

noncomputable def ep771 := @Enclosure.Real.IsNear.sqrt_image qz208 4802569 1600 0 1 7181030 7181031 131072

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz254 qz405 qz405)

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz254 qz406 qz406)

noncomputable def ep772 := @Enclosure.Real.IsNear.addLit_ff qz210 qz211 49 4 0 1 4782969 1600 0 1

noncomputable abbrev qz212 := qz405

noncomputable def ep773 := @Enclosure.Real.IsNear.mulLit_ff qz212 qz212 7 2 0 1 7 2 0 1 49 4

noncomputable def ep774 := @Enclosure.Complex.IsNear.of_eq qz209 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz17) Bool.false 7 2 0 1 Bool.false 54675 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 54675 1000 3 qz18)

noncomputable abbrev qz213 := (ep774 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz267 Bool.false 7 2 0 1 Bool.false 54675 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz271))

noncomputable def ep775 := @ep773 0 1 (@Enclosure.Complex.IsNear.re_isNear qz209 Bool.false 7 2 0 1 Bool.false 54675 1000 0 1 qz213)

noncomputable def ep776 := ep775 (@Enclosure.Complex.IsNear.re_isNear qz209 Bool.false 7 2 0 1 Bool.false 54675 1000 0 1 qz213)

noncomputable abbrev qz214 := qz406

noncomputable def ep777 := @Enclosure.Real.IsNear.mulLit_ff qz214 qz214 54675 1000 0 1 54675 1000 0 1 4782969 1600

noncomputable def ep778 := @ep777 0 1 (@Enclosure.Complex.IsNear.im_isNear qz209 Bool.false 7 2 0 1 Bool.false 54675 1000 0 1 qz213)

noncomputable def ep779 := ep778 (@Enclosure.Complex.IsNear.im_isNear qz209 Bool.false 7 2 0 1 Bool.false 54675 1000 0 1 qz213)

noncomputable def ep780 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Real.sqrt (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))))) Bool.false 55296051 1073741824

noncomputable def ep781 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))))) Bool.false 110592102 2147483648

noncomputable def ep782 := nat_lit 13307313559783366531841787206855511544771963450613

noncomputable def ep783 := nat_lit 5017667669669390206845536611345881338845593600000000

noncomputable def ep784 := nat_lit 16467888686071281339386015799359257536120221797990577965296503

noncomputable def ep785 := nat_lit 1305793362884643128687118515234487249644096695672174436312678400000000

noncomputable def ep786 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))) ep782 ep783 ep784 ep785

noncomputable def ep787 := nat_lit 6311858401018651135268184722509635822764403550129

noncomputable def ep788 := nat_lit 2796669553881243537011744244709112216891406098737603432864733

noncomputable def ep789 := nat_lit 435264454294881042895706171744829083214698898557391478770892800000000

noncomputable def ep790 := nat_lit 1748863789691178849143400621086468930501889975121

noncomputable def ep791 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204))) ep787 ep783 ep788 ep789 ep790

noncomputable def ep792 := nat_lit 1254416917417347551711384152836470334711398400000000

noncomputable def ep793 := nat_lit 252433750763360960260961970788497527670187609430555239584447

noncomputable def ep794 := nat_lit 40806042590145097771472453601077726551378021739755451134771200000000

noncomputable def ep795 := nat_lit 16692919254769520566785249135649029998116005949393116363940811555146063050678351778366567219200000000

noncomputable def ep796 := nat_lit 2512341219066122621352377

noncomputable def ep797 := nat_lit 70835497243044678205440000

noncomputable def ep798 := nat_lit 1091052626099241913757829023

noncomputable def ep799 := nat_lit 12045254311621113062076176138240000

noncomputable def ep800 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) ep796 ep797 ep798 ep799 ep796 ep797 ep798

noncomputable def ep801 := nat_lit 1322446138673019396987511

noncomputable def ep802 := nat_lit 35417748621522339102720000

noncomputable def ep803 := nat_lit 374181803653748041589002433

noncomputable def ep804 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204) Bool.true ep796 ep797 ep798 ep799 Bool.false ep801 ep802 ep803

noncomputable def ep805 := nat_lit 4516970366857917398278566051840000

noncomputable def ep806 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204 Bool.true ep796 ep797 ep798 ep799 Bool.false ep801 ep802 ep803 ep805

noncomputable def ep807 := nat_lit 1770887431076116955136000

noncomputable def ep808 := nat_lit 150565678895263913275952201728000

noncomputable def ep809 := nat_lit 23611832414348226068480000

noncomputable def ep810 := nat_lit 92335071340091311433929773

noncomputable abbrev qz215 := (Complex.re qz401)

noncomputable abbrev qz216 := (Complex.im qz401)

noncomputable def ep811 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216) 4990973657254574291347 ep807 942085516977968599807519 ep808 903993388452101864335419 ep809 ep810

noncomputable def ep812 := nat_lit 1095023119238283005643288739840000

noncomputable def ep813 := nat_lit 1483024495806215290638558751553480198585319424000

noncomputable def ep814 := nat_lit 588147183184624661234188288

noncomputable def ep815 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215 14346907 768000 0 1 347878023970921 2305843009213693952 196994136153102951 ep814 4990973657254574291347

noncomputable def ep816 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 14346907 768000 0 1 0 1 0 1 14346907

noncomputable def ep817 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 43040721 3200 0 1 14346907 768000 0

noncomputable def ep818 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz14) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow12.d15 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz14 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz23)

noncomputable abbrev qz407 := (@HAdd.hAdd Complex Complex Complex qz429 qz428 qz433)

noncomputable abbrev qz217 := qz407

noncomputable def ep819 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz217) Bool.true 43040721 3200 0 1 Bool.true 10440232803 64000 0 1

noncomputable abbrev qz218 := (Complex.re qz407)

noncomputable abbrev qz219 := (Complex.im qz407)

noncomputable def ep820 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz218) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz219) 4781769 640 0 1 4782969 800 0 1

noncomputable def ep821 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz218 4781769 1600 0 1 5 2 0 1 4781769 640

noncomputable abbrev qz408 := (@HAdd.hAdd Complex Complex Complex qz429 qz428 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz220 := qz408

noncomputable def ep822 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz220) Bool.true 4781769 1600 0 1 Bool.false 2187 20 0 1

noncomputable abbrev qz221 := (Complex.re qz408)

noncomputable abbrev qz222 := (Complex.im qz408)

noncomputable def ep823 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz221) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz222) 3 4 0 1 4782969 1600 0 1

noncomputable def ep824 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz221 1 2 0 1 3 2 0 1 3 4

noncomputable def ep825 := @ep824 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep351)

noncomputable def ep826 := @Enclosure.Complex.IsNear.of_eq qz220 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz17) Bool.false 3 2 0 1 Bool.false 54675 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 54675 1000 1 qz18)

noncomputable abbrev qz223 := (ep826 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz267 Bool.false 3 2 0 1 Bool.false 54675 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz271))

noncomputable def ep827 := ep825 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 3 2 0 1 Bool.false 54675 1000 0 1 qz223)

noncomputable def ep828 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz222 54675 1000 0 1 54675 1000 0 1 4782969 1600

noncomputable def ep829 := @ep828 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep351)

noncomputable def ep830 := ep829 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 3 2 0 1 Bool.false 54675 1000 0 1 qz223)

noncomputable def ep831 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz220 Bool.true 4781769 1600 0 1 Bool.false 2187 20 0 1 (@ep823 19127076 4781769 1600 0 1 (ep827 rfl) (ep830 rfl) rfl rfl)

noncomputable def ep832 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz222) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz221) 2187 80 0 1 6561 80 0 1

noncomputable def ep833 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz222 1 2 0 1 54675 1000 0 1 2187 80

noncomputable def ep834 := @ep833 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep351)

noncomputable def ep835 := ep834 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 3 2 0 1 Bool.false 54675 1000 0 1 qz223)

noncomputable def ep836 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz221 54675 1000 0 1 3 2 0 1 6561 80

noncomputable def ep837 := @ep836 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep351)

noncomputable def ep838 := ep837 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 3 2 0 1 Bool.false 54675 1000 0 1 qz223)

noncomputable abbrev qz224 := (ep822 (BSN.ascPochhammer_succ_eval_c 1 2 qz259 rfl) (ep831 (@ep832 699840 2187 20 0 1 (ep835 rfl) (ep838 rfl) rfl rfl)))

noncomputable def ep839 := @ep821 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4781769 1600 0 1 Bool.false 2187 20 0 1 qz224)

noncomputable def ep840 := @Enclosure.Complex.IsNear.of_eq qz217 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz17) Bool.false 5 2 0 1 Bool.false 54675 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 54675 1000 2 qz18)

noncomputable abbrev qz225 := (ep840 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz267 Bool.false 5 2 0 1 Bool.false 54675 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz271))

noncomputable def ep841 := ep839 (@Enclosure.Complex.IsNear.re_isNear qz217 Bool.false 5 2 0 1 Bool.false 54675 1000 0 1 qz225)

noncomputable def ep842 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz219 2187 20 0 1 54675 1000 0 1 4782969 800

noncomputable def ep843 := @ep842 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4781769 1600 0 1 Bool.false 2187 20 0 1 qz224)

noncomputable def ep844 := ep843 (@Enclosure.Complex.IsNear.im_isNear qz217 Bool.false 5 2 0 1 Bool.false 54675 1000 0 1 qz225)

noncomputable def ep845 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz217 Bool.true 43040721 3200 0 1 Bool.true 10440232803 64000 0 1 (@ep820 6886515360 43040721 3200 0 1 (ep841 rfl) (ep844 rfl) rfl rfl)

noncomputable def ep846 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz219) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz218) 10457728803 64000 0 1 2187 8 0 1

noncomputable def ep847 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz219 4781769 1600 0 1 54675 1000 0 1 10457728803 64000

noncomputable def ep848 := @ep847 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4781769 1600 0 1 Bool.false 2187 20 0 1 qz224)

noncomputable def ep849 := ep848 (@Enclosure.Complex.IsNear.im_isNear qz217 Bool.false 5 2 0 1 Bool.false 54675 1000 0 1 qz225)

noncomputable def ep850 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz218 2187 20 0 1 5 2 0 1 2187 8

noncomputable def ep851 := @ep850 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4781769 1600 0 1 Bool.false 2187 20 0 1 qz224)

noncomputable def ep852 := ep851 (@Enclosure.Complex.IsNear.re_isNear qz217 Bool.false 5 2 0 1 Bool.false 54675 1000 0 1 qz225)

noncomputable abbrev qz226 := (ep819 (BSN.ascPochhammer_succ_eval_c 2 3 qz259 rfl) (ep845 (@ep846 83521862424 10440232803 64000 0 1 (ep849 rfl) (ep852 rfl) rfl rfl)))

noncomputable def ep853 := @ep817 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep818) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43040721 3200 0 1 Bool.true 10440232803 64000 0 1 qz226)

noncomputable def ep854 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 10440232803 64000 0 1 0 1 0

noncomputable def ep855 := @ep854 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep818) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43040721 3200 0 1 Bool.true 10440232803 64000 0 1 qz226)

noncomputable def ep856 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 1160025867 5120000 0 1 0 1 0 1 1160025867

noncomputable def ep857 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 10440232803 64000 0 1 1160025867 5120000 0

noncomputable def ep858 := @ep857 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep818) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43040721 3200 0 1 Bool.true 10440232803 64000 0 1 qz226)

noncomputable def ep859 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 43040721 3200 0 1 0 1 0

noncomputable def ep860 := @ep859 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep818) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43040721 3200 0 1 Bool.true 10440232803 64000 0 1 qz226)

noncomputable def ep861 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 14346907 768000 0 1 Bool.false 1160025867 5120000 0 1 (@ep816 14346907 768000 0 1 (ep853 rfl) (ep855 rfl) rfl rfl) (@ep856 1160025867 5120000 0 1 (ep858 rfl) (ep860 rfl) rfl rfl)

noncomputable def ep862 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 14346907 768000 0 1 Bool.false 1160025867 5120000 0 1 ep861

noncomputable def ep863 := nat_lit 2352588732738498644936753152

noncomputable def ep864 := @Enclosure.Complex.IsNear.re_isNear qz204 Bool.false 347878023970921 2305843009213693952 196994136153102951 ep814 Bool.false 779287267783057 4611686018427387904 875571669248824109 ep863

noncomputable abbrev qz409 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 19487171)))

noncomputable def ep865 := @Enclosure.Complex.IsNear.of_eq qz204 (Complex.mk (@HMul.hMul Real Real Real qz0 qz409 qz118) (@HMul.hMul Real Real Real qz0 qz409 qz119)) Bool.false 347878023970921 2305843009213693952 196994136153102951 ep814 Bool.false 779287267783057 4611686018427387904 875571669248824109

noncomputable abbrev qz410 := (Real.sqrt (@Nat.cast Real Real.instNatCast 19487171))

noncomputable abbrev qz411 := (@Nat.cast Real Real.instNatCast 19487171)

noncomputable def ep866 := @Enclosure.Real.IsNear.inv_image qz410 9479911077611 2147483648 1 2147483648 243234 243235 1073741824 (@Enclosure.Real.IsNear.of_eq qz410 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz411 qz19)) Bool.false 9479911077611 2147483648 1 2147483648 (BSN.sqrt_natCast_div_one 19487171) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz411 qz19)) Bool.false 9479911077611 2147483648 1 2147483648 9479911077611 2147483648 1 2147483648 (BSN.sqrt_enclosure 19487171 1 4739955538805 4739955538806 1073741824 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep867 := nat_lit 20405454520000000000000000

noncomputable def ep868 := nat_lit 92764080252577317623169024

noncomputable def ep869 := nat_lit 38685626227668133590597632

noncomputable def ep870 := BSN.log_dyadic_bound 3 19 6 5 63732433749841395 1073741824 510136363 537698765144529 55801305 341937090 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 3) (BSN.artanhQ 19) 0 5 537698765144529 63732433749841395 55801305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep871 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz120 54675 1000 0 1 10799160256583397 4503599627370496 1000001530409089 510136363000000000000000 23617763481147889239 180143985094819840 2187003347004677643 ep867 qz22 (BSN.isNear_log_sfrac 11 1 10799160256583397 4503599627370496 1000001530409089 510136363000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz352 Bool.false ep868 ep869 1000001530409089 510136363000000000000000 10799160256583397 4503599627370496 1000001530409089 510136363000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 341937090 1073741824 24973259072661432 36028797018963968 510136363 1000000000000000 rfl rfl rfl rfl (ep870 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep872 := nat_lit 28195202809751795436355584

noncomputable def ep873 := nat_lit 119454693128641500364992410398076517827312196872302143702305954494574391468708119601688011546600407040000

noncomputable def ep874 := nat_lit 50797410752592599495442790923292316227798919877281851451531752809858799638366050241238301547400049385799680

noncomputable def ep875 := nat_lit 11145082158311966081208395679003739835682129878270310916143598241105106675591365093041904025600000000

noncomputable def ep876 := nat_lit 312839485203899995867991499354339159683226554074321748240746600707685426531046498651413200491721523200000

noncomputable def ep877 := nat_lit 931285863797530990749784500260359130842980197750167276611415468180744660036710921089368861702334238739660800

noncomputable def ep878 := BSN.sin_dyadic_bound_f 3205423446360 4398046511104 3 2 2147483648 1021269087 ep873 ep874 ep875 ep876 ep877 ep875 1430216618 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3205423446360) (BSN.sinEvenQ 4398046511104) 0 2 ep873 ep874 ep875 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3205423446360) (BSN.sinOddQ 4398046511104) 0 2 ep876 ep877 ep875 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz412 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 35193210067) (@Nat.cast Real Real.instNatCast 268435456))

noncomputable def ep879 := @Enclosure.Real.IsNear.cos_image qz121 qz412 Bool.false 35193210067 268435456 231 2147483648 Bool.false 1430216618 2147483648 1 510136363 (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 23617763481147889239 180143985094819840 2187003347004677643 ep867 35193210067 268435456 231 2147483648 (ep871 rfl) rfl) (Enclosure.sfrac_false_div 35193210067 268435456) (BSN.cos_reduce3 qz412 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep872) (@Nat.cast Real Real.instNatCast ep869)) 226375608064910080 72057594037927936 Bool.false 1430216618 2147483648 20 1000000000000000 1020272726 510136363 (BSN.sin_reduce_arg_pos_rat_q3 35193210067 268435456 226375608064910080 72057594037927936 20 ep872 ep869 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1430216618 2147483648 ep872 ep869 3205423446360 4398046511104 1021269087 1020272726 (ep878 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep880 := nat_lit 66368671774648972187698542841455400455100412542335977750577149651759597530026995940979136149900492800000

noncomputable def ep881 := nat_lit 5644156750288066610604754547032479580866546653031316827947972534428755515374005582359811283044449931755520

noncomputable def ep882 := nat_lit 199083725159630292630933211733008193885629873367251392629899161758796582376729805092751324641650278400000

noncomputable def ep883 := nat_lit 253987053762962997477213954616461581138994599386409257257658764049293998191830251206191507737000246928998400

noncomputable def ep884 := BSN.cos_dyadic_bound_f 3205423446360 4398046511104 3 2 2147483648 1021269087 ep880 ep881 ep875 ep882 ep883 ep875 1601925853 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3205423446360) (BSN.cosEvenQ 4398046511104) 0 2 ep880 ep881 ep875 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3205423446360) (BSN.cosOddQ 4398046511104) 0 2 ep882 ep883 ep875 rfl rfl rfl rfl) rfl rfl

noncomputable def ep885 := @Enclosure.Real.IsNear.sin_image qz121 qz412 Bool.false 35193210067 268435456 231 2147483648 Bool.true 1601925853 2147483648 1 510136363 (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 23617763481147889239 180143985094819840 2187003347004677643 ep867 35193210067 268435456 231 2147483648 (ep871 rfl) rfl) (Enclosure.sfrac_false_div 35193210067 268435456) (BSN.sin_reduce3 qz412 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep872) (@Nat.cast Real Real.instNatCast ep869)) 226375608064910080 72057594037927936 Bool.false 1601925853 2147483648 20 1000000000000000 1020272726 510136363 (BSN.sin_reduce_arg_pos_rat_q3 35193210067 268435456 226375608064910080 72057594037927936 20 ep872 ep869 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1601925853 2147483648 ep872 ep869 3205423446360 4398046511104 1021269087 1020272726 (ep884 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep886 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz409 qz118) (@HMul.hMul Real Real Real qz0 qz409 qz119) Bool.false 347878023970921 2305843009213693952 196994136153102951 ep814 Bool.false 779287267783057 4611686018427387904 875571669248824109 ep863 (@Enclosure.Real.IsNear.mulLit_ff qz409 qz118 486469 2147483648 1 2147483648 715108309 1073741824 119988983501 1095509497792692224 347878023970921 2305843009213693952 196994136153102951 ep814 (@Enclosure.Real.IsNear.recentre' qz409 Bool.false 486469 2147483648 1 2147483648 486469 2147483648 1 2147483648 (ep866 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 1430216618 2147483648 119988983501 1095509497792692224 715108309 1073741824 119988983501 1095509497792692224 (ep879 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz409 qz119 486469 2147483648 1 2147483648 1601925853 2147483648 119988983501 1095509497792692224 779287267783057 4611686018427387904 875571669248824109 ep863 (@Enclosure.Real.IsNear.recentre' qz409 Bool.false 486469 2147483648 1 2147483648 486469 2147483648 1 2147483648 (ep866 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz122 Bool.true 1601925853 2147483648 119988983501 1095509497792692224 (@Enclosure.Real.IsNear.recentre' qz122 Bool.true 1601925853 2147483648 119988983501 1095509497792692224 1601925853 2147483648 119988983501 1095509497792692224 (ep885 rfl rfl) rfl)) rfl)

noncomputable def ep887 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216 1160025867 5120000 0 1 779287267783057 4611686018427387904 875571669248824109 ep863 903993388452101864335419

noncomputable def ep888 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 14346907 768000 0 1 Bool.false 1160025867 5120000 0 1 ep861

noncomputable def ep889 := @Enclosure.Complex.IsNear.im_isNear qz204 Bool.false 347878023970921 2305843009213693952 196994136153102951 ep814 Bool.false 779287267783057 4611686018427387904 875571669248824109 ep863

noncomputable def ep890 := nat_lit 3541774862152233910272000

noncomputable def ep891 := nat_lit 12561745310547639351180863

noncomputable def ep892 := nat_lit 1806788146743166959311426420736000

noncomputable def ep893 := nat_lit 11805916207174113034240000

noncomputable def ep894 := nat_lit 20774390325901754134003047

noncomputable def ep895 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215) 11180361957167614954699 ep890 ep891 ep892 403547506367114415813507 ep893 ep894

noncomputable def ep896 := nat_lit 273755779809570751410822184960000

noncomputable def ep897 := nat_lit 1561268830167462428234355430592264765559537664000

noncomputable def ep898 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz216 14346907 768000 0 1 779287267783057 4611686018427387904 875571669248824109 ep863 11180361957167614954699

noncomputable def ep899 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz215 1160025867 5120000 0 1 347878023970921 2305843009213693952 196994136153102951 ep814 403547506367114415813507

noncomputable abbrev qz413 := (@ep865 ep863 (BSN.cpow_neg_s_sub_mk qz17 54675 1000 11 3 19487171 qz18 rfl EMRow12.d16) ep886)

noncomputable def ep900 := ep806 (@ep811 ep812 ep813 ep796 ep797 ep798 ep799 (@ep815 ep807 942085516977968599807519 ep808 ep862 (ep864 qz413) rfl) (@ep887 ep809 ep810 ep812 ep888 (ep889 qz413) rfl) rfl rfl) (@ep895 ep896 ep897 ep801 ep802 ep803 ep805 (@ep898 ep890 ep891 ep892 ep862 (ep889 qz413) rfl) (@ep899 ep893 ep894 ep896 ep888 (ep864 qz413) rfl) rfl rfl)

noncomputable def ep901 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) ep801 ep802 ep803 ep805 ep801 ep802 ep803

noncomputable def ep902 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204) Bool.true ep796 ep797 ep798 ep799 Bool.false ep801 ep802 ep803

noncomputable def ep903 := @ep767 113452179645873 140737488355328 1951088235 985162418487296 (@ep768 1 917504 (ep769 (@ep770 262144 1 262144 (ep771 (@ep772 19210276 4802569 1600 0 1 (ep776 rfl) (ep779 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep780 33 268435456 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)) (@ep781 264 2147483648 55296051 1073741824 33 268435456 (@ep786 55295919 55296183 1073741824 (@ep791 ep792 ep793 ep794 ep795 ep782 ep783 ep784 ep785 (@ep800 ep799 ep787 ep783 ep788 ep789 (@ep804 ep805 ep900) (@ep804 ep805 ep900) rfl) (@ep901 ep805 ep790 ep792 ep793 ep794 (@ep902 ep805 ep900) (@ep902 ep805 ep900) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow12.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 11))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))) Bool.false 3232340167244203 3799912185593856 3055551157577 26599385299156992 := ep765 (ep766 ep903) rfl rfl

theorem EMRow12.d18 : @Eq Nat (Nat.pow 12 (Nat.succ (Nat.mul 2 3))) 35831808 := @Eq.refl Nat 35831808

noncomputable abbrev qz451 := (@HAdd.hAdd Complex Complex Complex qz453 qz459 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz414 := qz451

noncomputable abbrev qz227 := (@HDiv.hDiv Real Real Real qz257 (@Norm.norm Complex Complex.instNorm qz414) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz357) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz415 := (@HPow.hPow Complex Complex Complex qz430 qz449 (@HSub.hSub Complex Complex Complex qz436 qz445 qz432))

noncomputable abbrev qz228 := qz415

noncomputable def ep904 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz130 1 12))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) 118907105 4294967296 522451 4294967296 51315654087675 70368744177664 1128112861

noncomputable def ep905 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz130 1 12)) 6641 442368 1 442368 483435 262144 2051 262144 118907105 4294967296

noncomputable def ep906 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz130 1 12)) (Real.sqrt (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz130 1 12)) (Complex.re (zetaApproximant qz130 1 12))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz130 1 12)) (Complex.im (zetaApproximant qz130 1 12))))) Bool.false 483435 262144 2051 262144

noncomputable def ep907 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz130 1 12)) (Complex.re (zetaApproximant qz130 1 12))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz130 1 12)) (Complex.im (zetaApproximant qz130 1 12))))) Bool.false 483435 262144 2051 262144

noncomputable def ep908 := nat_lit 313714573037350700108254561673001241

noncomputable def ep909 := nat_lit 92242295694652303682361312417939456

noncomputable def ep910 := nat_lit 481374083583346958151071774279141289031728769356483031

noncomputable def ep911 := nat_lit 16688667951160058552045896570830115806234640511926272000

noncomputable def ep912 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz130 1 12)) (Complex.re (zetaApproximant qz130 1 12))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz130 1 12)) (Complex.im (zetaApproximant qz130 1 12)))) ep908 ep909 ep910 ep911 240692 242743

noncomputable def ep913 := nat_lit 41543466629458836506497429335411669089529121

noncomputable def ep914 := nat_lit 12219067655409457978727954243333491771047936

noncomputable def ep915 := nat_lit 2359732733059185857591649537535375301633302953656889139

noncomputable def ep916 := nat_lit 83443339755800292760229482854150579031173202559631360000

noncomputable def ep917 := nat_lit 209173874379917346084944599145028361225

noncomputable def ep918 := nat_lit 190922932115772780917624285052085808922624

noncomputable def ep919 := nat_lit 92065790737400260085369792695959264697931431885793

noncomputable def ep920 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz130 1 12)) (Complex.re (zetaApproximant qz130 1 12))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz130 1 12)) (Complex.im (zetaApproximant qz130 1 12))) ep913 ep914 ep915 ep916 ep917 ep918 ep919

noncomputable def ep921 := nat_lit 162975272960547446797323208699512849670260161249280000

noncomputable def ep922 := nat_lit 7934156368872833628917025804948316989579238311101134851370311448541099157931482415104

noncomputable def ep923 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz130 1 12)) (Complex.re (zetaApproximant qz130 1 12)) 6445422145170852694511 3495578300569085804544 ep496 ep497 6445422145170852694511 3495578300569085804544 ep496 ep497 ep913

noncomputable def ep924 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz130 1 12)) (Complex.im (zetaApproximant qz130 1 12)) 14462844615770348035 436947287571135725568 ep613 ep614 14462844615770348035 436947287571135725568 ep613 ep614 ep917

noncomputable def ep925 := @ep904 985162418487296 228766399732064473579520 53263828095995 70368744177664 120965833437 985162418487296 (@ep905 522451 4294967296 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz205)) Bool.false 6641 442368 1 442368 (BSN.theta_err_eq 1 2 96 162 EMRow12.d13 EMRow12.d14 rfl) (ep745 rfl)) (ep906 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz130 1 12)) (@ep907 483435 262144 2051 262144 (@ep912 131072 (@ep920 ep921 ep922 ep908 ep909 ep910 ep911 (@ep923 ep914 ep915 ep916 ep725 ep725 rfl) (@ep924 ep918 ep919 ep921 ep733 ep733 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz229 := (@Norm.norm Complex Complex.instNorm qz414)

noncomputable def ep926 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz229 qz404) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) Bool.false 51315654087675 70368744177664 1128112861 985162418487296 (BSN.zrb_shape_eq qz229 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) qz139 3)

noncomputable def ep927 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz229 qz404) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) 15112953 917504 1 917504 23768325 536870912 143 2147483648

noncomputable def ep928 := @Enclosure.Real.IsNear.mulLit_ff qz229 qz404 15112953 262144 1 262144 2 7 0 1 15112953 917504

noncomputable abbrev qz416 := (Complex.re qz451)

noncomputable abbrev qz417 := (Complex.im qz451)

noncomputable abbrev qz230 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz254 qz416 qz416) (@HMul.hMul Real Real Real qz254 qz417 qz417))

noncomputable abbrev qz231 := qz414

noncomputable def ep929 := @Enclosure.Real.IsNear.of_eq qz229 (Real.sqrt qz230) Bool.false 15112953 262144 1 262144 (BSN.norm_eq_sqrt_mul_add qz231)

noncomputable def ep930 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz230) Bool.false 15112953 262144 1 262144 15112953

noncomputable def ep931 := @Enclosure.Real.IsNear.sqrt_image qz230 132947081 40000 0 1 7556476 7556477 131072

noncomputable abbrev qz232 := (@HMul.hMul Real Real Real qz254 qz416 qz416)

noncomputable abbrev qz233 := (@HMul.hMul Real Real Real qz254 qz417 qz417)

noncomputable def ep932 := @Enclosure.Real.IsNear.addLit_ff qz232 qz233 49 4 0 1 132457081 40000 0 1

noncomputable abbrev qz234 := qz416

noncomputable def ep933 := @Enclosure.Real.IsNear.mulLit_ff qz234 qz234 7 2 0 1 7 2 0 1 49 4

noncomputable def ep934 := @Enclosure.Complex.IsNear.of_eq qz231 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz139) Bool.false 7 2 0 1 Bool.false 57545 1000 0 1 (BSN.s_add_nat_mk qz139 Bool.false 57545 1000 3 qz140)

noncomputable abbrev qz235 := (ep934 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz359 Bool.false 7 2 0 1 Bool.false 57545 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz361))

noncomputable def ep935 := @ep933 0 1 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 7 2 0 1 Bool.false 57545 1000 0 1 qz235)

noncomputable def ep936 := ep935 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 7 2 0 1 Bool.false 57545 1000 0 1 qz235)

noncomputable abbrev qz236 := qz417

noncomputable def ep937 := @Enclosure.Real.IsNear.mulLit_ff qz236 qz236 57545 1000 0 1 57545 1000 0 1 132457081 40000

noncomputable def ep938 := @ep937 0 1 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 7 2 0 1 Bool.false 57545 1000 0 1 qz235)

noncomputable def ep939 := ep938 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 7 2 0 1 Bool.false 57545 1000 0 1 qz235)

noncomputable def ep940 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Real.sqrt (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))))) Bool.false 23768325 536870912

noncomputable def ep941 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))))) Bool.false 190146600 4294967296

noncomputable def ep942 := nat_lit 4917329419952678765346475750285294388707301324840801

noncomputable def ep943 := nat_lit 2508833834834695103422768305672940669422796800000000000

noncomputable def ep944 := nat_lit 26486423566720981710983860353454629689286529263484283813417689

noncomputable def ep945 := nat_lit 4496302644732462245513731549457078337952922614315792465920000000000000

noncomputable def ep946 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))) ep942 ep943 ep944 ep945

noncomputable def ep947 := nat_lit 2686183834779755469046181547982657290129801563126809

noncomputable def ep948 := nat_lit 1393796574908163946345982392040522594123776000000000000

noncomputable def ep949 := nat_lit 8086486276728310406042913365792662418213496892748171074878061

noncomputable def ep950 := nat_lit 1405094576478894451723041109205336980610288316973685145600000000000000

noncomputable def ep951 := nat_lit 102748146686398651329186204895639083092073139015681

noncomputable def ep952 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228))) ep947 ep948 ep949 ep950 ep951

noncomputable def ep953 := nat_lit 3136042293543368879278460382091175836778496000000000000

noncomputable def ep954 := nat_lit 3048337405951942058232687914590549755016696033450681869039469

noncomputable def ep955 := nat_lit 22481513223662311227568657747285391689764613071578962329600000000000000

noncomputable def ep956 := nat_lit 8567196129031490245962366374619561983042362636408962809303169136681640129818516027926611230720000000000000

noncomputable def ep957 := nat_lit 51828407604129180586952197

noncomputable def ep958 := nat_lit 1180591620717411303424000000

noncomputable def ep959 := nat_lit 1228509701530253435102551963

noncomputable def ep960 := nat_lit 18742295593649237206845358080000000

noncomputable def ep961 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) ep957 ep958 ep959 ep960 ep957 ep958 ep959

noncomputable def ep962 := nat_lit 10136476048726137612072959

noncomputable def ep963 := nat_lit 1770887431076116955136000000

noncomputable def ep964 := nat_lit 1775921550148831129224289427

noncomputable def ep965 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228) Bool.true ep957 ep958 ep959 ep960 Bool.false ep962 ep963 ep964

noncomputable def ep966 := nat_lit 149938364749193897654762864640000000

noncomputable def ep967 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228 Bool.true ep957 ep958 ep959 ep960 Bool.false ep962 ep963 ep964 ep966

noncomputable def ep968 := nat_lit 5902958103587056517120000

noncomputable def ep969 := nat_lit 499794549163979658849209548800000

noncomputable def ep970 := nat_lit 52038453631404829869412797

noncomputable def ep971 := nat_lit 2437196312858700205240990751

noncomputable abbrev qz237 := (Complex.re qz415)

noncomputable abbrev qz238 := (Complex.im qz415)

noncomputable def ep972 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238) 1050230136378246412303 ep968 264307869357422199521509 ep969 ep970 ep958 ep971

noncomputable def ep973 := nat_lit 37484591187298474413690716160000000

noncomputable def ep974 := nat_lit 305940918662807367260455567840737965086752112640000

noncomputable def ep975 := nat_lit 26030966102290607231729664

noncomputable def ep976 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237 397321243 19200000 0 1 39649156251315 4611686018427387904 665224611102463 ep975 1050230136378246412303

noncomputable def ep977 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)))) 397321243 19200000 0 1 0 1 0 1 397321243

noncomputable def ep978 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1191963729 80000 0 1 397321243 19200000 0

noncomputable abbrev qz418 := (@HAdd.hAdd Complex Complex Complex qz429 qz444 qz433)

noncomputable abbrev qz239 := qz418

noncomputable def ep979 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2)) qz239) Bool.true 1191963729 80000 0 1 Bool.true 1521801475229 8000000 0 1

noncomputable abbrev qz240 := (Complex.re qz418)

noncomputable abbrev qz241 := (Complex.im qz418)

noncomputable def ep980 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2))) qz240) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2))) qz241) 132427081 16000 0 1 132457081 20000 0 1

noncomputable def ep981 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2))) qz240 132427081 40000 0 1 5 2 0 1 132427081 16000

noncomputable abbrev qz419 := (@HAdd.hAdd Complex Complex Complex qz429 qz444 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz242 := qz419

noncomputable def ep982 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz45 (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)) qz242) Bool.true 132427081 40000 0 1 Bool.false 11509 100 0 1

noncomputable abbrev qz243 := (Complex.re qz419)

noncomputable abbrev qz244 := (Complex.im qz419)

noncomputable def ep983 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) qz243) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) qz244) 3 4 0 1 132457081 40000 0 1

noncomputable def ep984 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) qz243 1 2 0 1 3 2 0 1 3 4

noncomputable def ep985 := @ep984 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep690)

noncomputable def ep986 := @Enclosure.Complex.IsNear.of_eq qz242 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz139) Bool.false 3 2 0 1 Bool.false 57545 1000 0 1 (BSN.s_add_nat_mk qz139 Bool.false 57545 1000 1 qz140)

noncomputable abbrev qz245 := (ep986 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz359 Bool.false 3 2 0 1 Bool.false 57545 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz361))

noncomputable def ep987 := ep985 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 3 2 0 1 Bool.false 57545 1000 0 1 qz245)

noncomputable def ep988 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) qz244 57545 1000 0 1 57545 1000 0 1 132457081 40000

noncomputable def ep989 := @ep988 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep690)

noncomputable def ep990 := ep989 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 3 2 0 1 Bool.false 57545 1000 0 1 qz245)

noncomputable def ep991 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)) qz242 Bool.true 132427081 40000 0 1 Bool.false 11509 100 0 1 (@ep983 529708324 132427081 40000 0 1 (ep987 rfl) (ep990 rfl) rfl rfl)

noncomputable def ep992 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) qz244) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) qz243) 11509 400 0 1 34527 400 0 1

noncomputable def ep993 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) qz244 1 2 0 1 57545 1000 0 1 11509 400

noncomputable def ep994 := @ep993 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep690)

noncomputable def ep995 := ep994 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 3 2 0 1 Bool.false 57545 1000 0 1 qz245)

noncomputable def ep996 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1))) qz243 57545 1000 0 1 3 2 0 1 34527 400

noncomputable def ep997 := @ep996 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 57545 1000 0 1 ep690)

noncomputable def ep998 := ep997 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 3 2 0 1 Bool.false 57545 1000 0 1 qz245)

noncomputable abbrev qz246 := (ep982 (BSN.ascPochhammer_succ_eval_c 1 2 qz357 rfl) (ep991 (@ep992 18414400 11509 100 0 1 (ep995 rfl) (ep998 rfl) rfl rfl)))

noncomputable def ep999 := @ep981 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 132427081 40000 0 1 Bool.false 11509 100 0 1 qz246)

noncomputable def ep1000 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz139) Bool.false 5 2 0 1 Bool.false 57545 1000 0 1 (BSN.s_add_nat_mk qz139 Bool.false 57545 1000 2 qz140)

noncomputable abbrev qz247 := (ep1000 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz359 Bool.false 5 2 0 1 Bool.false 57545 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz361))

noncomputable def ep1001 := ep999 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 5 2 0 1 Bool.false 57545 1000 0 1 qz247)

noncomputable def ep1002 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2))) qz241 11509 100 0 1 57545 1000 0 1 132457081 20000

noncomputable def ep1003 := @ep1002 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 132427081 40000 0 1 Bool.false 11509 100 0 1 qz246)

noncomputable def ep1004 := ep1003 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 5 2 0 1 Bool.false 57545 1000 0 1 qz247)

noncomputable def ep1005 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2)) qz239 Bool.true 1191963729 80000 0 1 Bool.true 1521801475229 8000000 0 1 (@ep980 4767854916000 1191963729 80000 0 1 (ep1001 rfl) (ep1004 rfl) rfl rfl)

noncomputable def ep1006 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2))) qz240) 1524103275229 8000000 0 1 11509 40 0 1

noncomputable def ep1007 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2))) qz241 132427081 40000 0 1 57545 1000 0 1 1524103275229 8000000

noncomputable def ep1008 := @ep1007 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 132427081 40000 0 1 Bool.false 11509 100 0 1 qz246)

noncomputable def ep1009 := ep1008 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 5 2 0 1 Bool.false 57545 1000 0 1 qz247)

noncomputable def ep1010 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2))) qz240 11509 100 0 1 5 2 0 1 11509 40

noncomputable def ep1011 := @ep1010 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 132427081 40000 0 1 Bool.false 11509 100 0 1 qz246)

noncomputable def ep1012 := ep1011 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 5 2 0 1 Bool.false 57545 1000 0 1 qz247)

noncomputable abbrev qz248 := (ep979 (BSN.ascPochhammer_succ_eval_c 2 3 qz357 rfl) (ep1005 (@ep1006 60872059009160 1521801475229 8000000 0 1 (ep1009 rfl) (ep1012 rfl) rfl rfl)))

noncomputable def ep1013 := @ep978 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep818) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1191963729 80000 0 1 Bool.true 1521801475229 8000000 0 1 qz248)

noncomputable def ep1014 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1521801475229 8000000 0 1 0 1 0

noncomputable def ep1015 := @ep1014 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep818) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1191963729 80000 0 1 Bool.true 1521801475229 8000000 0 1 qz248)

noncomputable def ep1016 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)))) 1521801475229 5760000000 0 1 0 1 0 1 1521801475229

noncomputable def ep1017 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1521801475229 8000000 0 1 1521801475229 5760000000 0

noncomputable def ep1018 := @ep1017 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep818) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1191963729 80000 0 1 Bool.true 1521801475229 8000000 0 1 qz248)

noncomputable def ep1019 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1191963729 80000 0 1 0 1 0

noncomputable def ep1020 := @ep1019 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep818) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1191963729 80000 0 1 Bool.true 1521801475229 8000000 0 1 qz248)

noncomputable def ep1021 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 397321243 19200000 0 1 Bool.false 1521801475229 5760000000 0 1 (@ep977 397321243 19200000 0 1 (ep1013 rfl) (ep1015 rfl) rfl rfl) (@ep1016 1521801475229 5760000000 0 1 (ep1018 rfl) (ep1020 rfl) rfl rfl)

noncomputable def ep1022 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 397321243 19200000 0 1 Bool.false 1521801475229 5760000000 0 1 ep1021

noncomputable def ep1023 := nat_lit 6507741525572651807932416

noncomputable def ep1024 := @Enclosure.Complex.IsNear.re_isNear qz228 Bool.false 39649156251315 4611686018427387904 665224611102463 ep975 Bool.false 1538788371236685 9223372036854775808 1601520535056619 ep1023

noncomputable abbrev qz420 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 35831808)))

noncomputable def ep1025 := @Enclosure.Complex.IsNear.of_eq qz228 (Complex.mk (@HMul.hMul Real Real Real qz0 qz420 qz191) (@HMul.hMul Real Real Real qz0 qz420 qz192)) Bool.false 39649156251315 4611686018427387904 665224611102463 ep975 Bool.false 1538788371236685 9223372036854775808 1601520535056619

noncomputable abbrev qz421 := (Real.sqrt (@Nat.cast Real Real.instNatCast 35831808))

noncomputable abbrev qz422 := (@Nat.cast Real Real.instNatCast 35831808)

noncomputable def ep1026 := @Enclosure.Real.IsNear.inv_image qz421 25709535038081 4294967296 1 4294967296 358752 358753 2147483648 (@Enclosure.Real.IsNear.of_eq qz421 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz422 qz19)) Bool.false 25709535038081 4294967296 1 4294967296 (BSN.sqrt_natCast_div_one 35831808) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz422 qz19)) Bool.false 25709535038081 4294967296 1 4294967296 25709535038081 4294967296 1 4294967296 (BSN.sqrt_enclosure 35831808 1 12854767519040 12854767519041 2147483648 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1027 := nat_lit 192260339710790830139637760

noncomputable def ep1028 := nat_lit 77371252455336267181195264

noncomputable def ep1029 := BSN.log_dyadic_bound 4 20 7 6 553512960000000000000 2147483648 722504448 7562520407908024320 174399160320 870729689 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 4) (BSN.artanhQ 20) 0 6 7562520407908024320 553512960000000000000 174399160320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1030 := @Enclosure.Real.IsNear.mulLit_ff qz139 qz193 57545 1000 0 1 11191024660993765 4503599627370496 3906258466849 2822283000000000000000 25759500564675448277 180143985094819840 44957128694965141 564456600000000000000000 qz141 (BSN.isNear_log_sfrac 12 1 11191024660993765 4503599627370496 3906258466849 2822283000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz395) Bool.false ep1027 ep1028 1000002167513344 722504448000000000000000 11191024660993765 4503599627370496 3906258466849 2822283000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 870729689 2147483648 24973259072661432 36028797018963968 722504448 1000000000000000 rfl rfl rfl rfl (ep1029 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1031 := nat_lit 31869163343691019188174848

noncomputable def ep1032 := nat_lit 618970019642690137449562112

noncomputable def ep1033 := nat_lit 42069121830069297760453999510099764129860813056

noncomputable def ep1034 := nat_lit 718357284780885402355475168976707429821283963523563520

noncomputable def ep1035 := nat_lit 5028500993466197816488326182836952008748987744664944640

noncomputable def ep1036 := BSN.sin_dyadic_bound_f 452888050172 8796093022208 2 1 4294967296 1446420038 ep1033 ep1034 ep1033 ep1033 ep1035 ep1033 221039052 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 452888050172) (BSN.sinEvenQ 8796093022208) 0 1 ep1033 ep1034 ep1033 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 452888050172) (BSN.sinOddQ 8796093022208) 0 1 ep1033 ep1035 ep1033 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz423 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 614154352299) (@Nat.cast Real Real.instNatCast 4294967296))

noncomputable def ep1037 := @Enclosure.Real.IsNear.cos_image qz194 qz423 Bool.false 614154352299 4294967296 343 4294967296 Bool.false 221039052 4294967296 1 722504448 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 25759500564675448277 180143985094819840 44957128694965141 564456600000000000000000 614154352299 4294967296 343 4294967296 (ep1030 rfl) rfl) (Enclosure.sfrac_false_div 614154352299 4294967296) (BSN.cos_reduce3 qz423 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1031) (@Nat.cast Real Real.instNatCast ep1032)) 226375608064910080 72057594037927936 Bool.false 221039052 4294967296 22 1000000000000000 1445008896 722504448 (BSN.sin_reduce_arg_pos_rat_q3 614154352299 4294967296 226375608064910080 72057594037927936 22 ep1031 ep1032 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 221039052 4294967296 ep1031 ep1032 452888050172 8796093022208 1446420038 1445008896 (ep1036 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1038 := nat_lit 143671456956177080471095033795341485964256792704712704

noncomputable def ep1039 := nat_lit 2155071854342656207066425506930122289463851890570690560

noncomputable def ep1040 := BSN.cos_dyadic_bound_f 452888050172 8796093022208 2 1 4294967296 1446420038 ep1033 ep1038 ep1033 ep1033 ep1039 ep1033 4289275674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 452888050172) (BSN.cosEvenQ 8796093022208) 0 1 ep1033 ep1038 ep1033 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 452888050172) (BSN.cosOddQ 8796093022208) 0 1 ep1033 ep1039 ep1033 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1041 := @Enclosure.Real.IsNear.sin_image qz194 qz423 Bool.false 614154352299 4294967296 343 4294967296 Bool.true 4289275674 4294967296 1 722504448 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 25759500564675448277 180143985094819840 44957128694965141 564456600000000000000000 614154352299 4294967296 343 4294967296 (ep1030 rfl) rfl) (Enclosure.sfrac_false_div 614154352299 4294967296) (BSN.sin_reduce3 qz423 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1031) (@Nat.cast Real Real.instNatCast ep1032)) 226375608064910080 72057594037927936 Bool.false 4289275674 4294967296 22 1000000000000000 1445008896 722504448 (BSN.sin_reduce_arg_pos_rat_q3 614154352299 4294967296 226375608064910080 72057594037927936 22 ep1031 ep1032 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 4289275674 4294967296 ep1031 ep1032 452888050172 8796093022208 1446420038 1445008896 (ep1040 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1042 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz420 qz191) (@HMul.hMul Real Real Real qz0 qz420 qz192) Bool.false 39649156251315 4611686018427387904 665224611102463 ep975 Bool.false 1538788371236685 9223372036854775808 1601520535056619 ep1023 (@Enclosure.Real.IsNear.mulLit_ff qz420 qz191 717505 4294967296 1 4294967296 55259763 1073741824 984820285 12121613185056768 39649156251315 4611686018427387904 665224611102463 ep975 (@Enclosure.Real.IsNear.recentre' qz420 Bool.false 717505 4294967296 1 4294967296 717505 4294967296 1 4294967296 (ep1026 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz191 Bool.false 221039052 4294967296 252113992960 3103132975374532608 55259763 1073741824 984820285 12121613185056768 (ep1037 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz420 qz192 717505 4294967296 1 4294967296 2144637837 2147483648 984820285 12121613185056768 1538788371236685 9223372036854775808 1601520535056619 ep1023 (@Enclosure.Real.IsNear.recentre' qz420 Bool.false 717505 4294967296 1 4294967296 717505 4294967296 1 4294967296 (ep1026 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz195 Bool.true 2144637837 2147483648 984820285 12121613185056768 (@Enclosure.Real.IsNear.recentre' qz195 Bool.true 4289275674 4294967296 252113992960 3103132975374532608 2144637837 2147483648 984820285 12121613185056768 (ep1041 rfl rfl) rfl)) rfl)

noncomputable def ep1043 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238 1521801475229 5760000000 0 1 1538788371236685 9223372036854775808 1601520535056619 ep1023 ep970

noncomputable def ep1044 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 397321243 19200000 0 1 Bool.false 1521801475229 5760000000 0 1 ep1021

noncomputable def ep1045 := @Enclosure.Complex.IsNear.im_isNear qz228 Bool.false 39649156251315 4611686018427387904 665224611102463 ep975 Bool.false 1538788371236685 9223372036854775808 1601520535056619 ep1023

noncomputable def ep1046 := nat_lit 124948637290994914712302387200000

noncomputable def ep1047 := nat_lit 4022542964989086298078409

noncomputable def ep1048 := nat_lit 1012339794534366005475389027

noncomputable def ep1049 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237) 40759553891580342093297 ep893 636318129678720936457417 ep1046 ep1047 ep963 ep1048

noncomputable def ep1050 := nat_lit 119670386867288122340229219430980323947745116160000

noncomputable def ep1051 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)))) qz238 397321243 19200000 0 1 1538788371236685 9223372036854775808 1601520535056619 ep1023 40759553891580342093297

noncomputable def ep1052 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237 1521801475229 5760000000 0 1 39649156251315 4611686018427387904 665224611102463 ep975 ep1047

noncomputable abbrev qz424 := (@ep1025 ep1023 (BSN.cpow_neg_s_sub_mk qz139 57545 1000 12 3 35831808 qz140 rfl EMRow12.d18) ep1042)

noncomputable def ep1053 := ep967 (@ep972 ep973 ep974 ep957 ep958 ep959 ep960 (@ep976 ep968 264307869357422199521509 ep969 ep1022 (ep1024 qz424) rfl) (@ep1043 ep958 ep971 ep973 ep1044 (ep1045 qz424) rfl) rfl rfl) (@ep1049 ep966 ep1050 ep962 ep963 ep964 ep966 (@ep1051 ep893 636318129678720936457417 ep1046 ep1022 (ep1045 qz424) rfl) (@ep1052 ep963 ep1048 ep966 ep1044 (ep1024 qz424) rfl) rfl rfl)

noncomputable def ep1054 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (Complex.im (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) ep962 ep963 ep964 ep966 ep962 ep963 ep964

noncomputable def ep1055 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228) Bool.true ep957 ep958 ep959 ep960 Bool.false ep962 ep963 ep964

noncomputable def ep1056 := @ep927 51315654087675 70368744177664 1128112861 985162418487296 (@ep928 1 917504 (ep929 (@ep930 262144 1 262144 (ep931 (@ep932 531788324 132947081 40000 0 1 (ep936 rfl) (ep939 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep940 143 2147483648 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)) (@ep941 286 4294967296 23768325 536870912 143 2147483648 (@ep946 95073157 95073443 2147483648 (@ep952 ep953 ep954 ep955 ep956 ep942 ep943 ep944 ep945 (@ep961 ep960 ep947 ep948 ep949 ep950 (@ep965 ep966 ep1053) (@ep965 ep966 ep1053) rfl) (@ep1054 ep966 ep951 ep953 ep954 ep955 (@ep1055 ep966 ep1053) (@ep1055 ep966 ep1053) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow12.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz130 1 12))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))) Bool.false 53263828095995 70368744177664 120965833437 985162418487296 := ep925 (ep926 ep1056) rfl rfl

noncomputable def EMRow12.d20 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz425 := (EMRow12.d3 qz434 qz446 (@Enclosure.dec_le_dec qz434 qz446 54675 1000 57545 1000 (@Eq.refl Real qz434) (@Eq.refl Real qz446) rfl rfl rfl) 11 12 1 1)

noncomputable abbrev qz249 := qz425

noncomputable def ep1057 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz249 (@Enclosure.dec_nonneg qz17 54675 1000 qz18) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 11 rfl)

noncomputable abbrev qz250 := (Zeta.Certificates.ZIntervalEM.fstVal qz425)

noncomputable def ep1058 := @Enclosure.Real.IsNear.pos_val qz250 ep141 ep142

noncomputable def ep1059 := @Enclosure.Real.IsNear.of_eq qz250 (hardyZApproximantEM 1 11 qz17) Bool.false

noncomputable abbrev qz251 := (Zeta.Certificates.ZIntervalEM.sndVal qz425)

noncomputable def ep1060 := BSN.mul_neg_of_pos_neg_r qz250 qz251 (@ep1058 ep143 ep144 (@ep1059 ep141 ep142 ep143 ep144 (@Eq.refl Real (hardyZApproximantEM 1 11 qz17)) EMRow12.d9) rfl rfl rfl)

noncomputable def ep1061 := @Enclosure.Real.IsNear.neg_val qz251 ep480 ep481

noncomputable def ep1062 := @Enclosure.Real.IsNear.of_eq qz251 (hardyZApproximantEM 1 12 qz139) Bool.true

noncomputable def ep1063 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz250) (BSN.hardyZErrorBoundStrong 1 11 qz17)

noncomputable def ep1064 := @Enclosure.norm_gt_of_isNear qz250 (BSN.hardyZErrorBoundStrong 1 11 qz17) Bool.false

noncomputable def ep1065 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 11 qz17) (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 11))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))) Bool.false 3232340167244203 3799912185593856 3055551157577 26599385299156992 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 11))) (@HMul.hMul Real Real Real qz0 qz201 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz204)))))

noncomputable def ep1066 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz251) (BSN.hardyZErrorBoundStrong 1 12 qz139)

noncomputable def ep1067 := @Enclosure.norm_gt_of_isNear qz251 (BSN.hardyZErrorBoundStrong 1 12 qz139) Bool.true

noncomputable def ep1068 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 12 qz139) (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz130 1 12))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))) Bool.false 53263828095995 70368744177664 120965833437 985162418487296 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz88 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz130 1 12))) (@HMul.hMul Real Real Real qz0 qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz45 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz202)) ↑qz203) (@Polynomial.eval Complex Complex.instSemiring qz130 (@ascPochhammer Complex Complex.instSemiring 3))) qz228)))))

noncomputable def ep1069 := @List.cons EMRow12.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz249 (ep1057 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 12 rfl) (ep1060 (@ep1061 ep482 ep483 (@ep1062 ep480 ep481 ep482 ep483 (@Eq.refl Real (hardyZApproximantEM 1 12 qz139)) EMRow12.d12) rfl rfl rfl)) (ep1063 (hardyZErrorBoundEM 1 11 qz17) (BSN.hardyZErrorBoundEM_le_strong 1 11 qz17 rfl) (@ep1064 Bool.false ep141 ep142 ep143 ep144 3232340167244203 3799912185593856 3055551157577 26599385299156992 (@ep1059 ep141 ep142 ep143 ep144 (@Eq.refl Real (hardyZApproximantEM 1 11 qz17)) EMRow12.d9) (ep1065 EMRow12.d17) rfl rfl rfl rfl rfl)) (ep1066 (hardyZErrorBoundEM 1 12 qz139) (BSN.hardyZErrorBoundEM_le_strong 1 12 qz139 rfl) (@ep1067 Bool.false ep480 ep481 ep482 ep483 53263828095995 70368744177664 120965833437 985162418487296 (@ep1062 ep480 ep481 ep482 ep483 (@Eq.refl Real (hardyZApproximantEM 1 12 qz139)) EMRow12.d12) (ep1068 EMRow12.d19) rfl rfl rfl rfl rfl)))) (@List.nil EMRow12.d0)

noncomputable abbrev qz426 := (@Enclosure.dec_le_dec qz434 qz446 54675 1000 57545 1000 (@Eq.refl Real qz434) (@Eq.refl Real qz446) rfl rfl rfl)

noncomputable abbrev qz252 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1069 (@List.IsChain.singleton EMRow12.d1 EMRow12.d20 (EMRow12.d2 qz267 qz359 qz426))))

noncomputable abbrev qz427 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1070 := And (@Eq (Option Real) (@Option.map qz427 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz427 qz252)) (@Option.some Real qz17))

noncomputable def ep1071 := ep1070 (@Eq (Option Real) (@Option.map qz427 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz427 qz252)) (@Option.some Real qz139))

noncomputable def ep1072 := @And.intro (@Eq Nat (@List.length qz427 qz252) 1) ep1071

noncomputable def ep1073 := @And.intro (@Eq (Option Real) (@Option.map qz427 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz427 qz252)) (@Option.some Real qz17))

noncomputable def ep1074 := @ep1073 (@Eq (Option Real) (@Option.map qz427 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz427 qz252)) (@Option.some Real qz139))

noncomputable abbrev qz253 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1069 (@List.IsChain.singleton EMRow12.d1 EMRow12.d20 (EMRow12.d2 qz267 qz359 qz426)))

theorem EMRow12.d21 : Zeta.Certificates.BatchSpec 1 54675 1000 57545 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz427 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz427 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz427 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz17)) (@Eq (Option Real) (@Option.map qz427 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz427 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz139)))) qz253 (ep1072 (@Eq.refl Nat 1) (ep1074 (@Eq.refl (Option Real) (@Option.some Real qz17)) (@Eq.refl (Option Real) (@Option.some Real qz139))))

theorem solution : Zeta.Certificates.BatchSpec 1 54675 1000 57545 1000 := EMRow12.d21
#print axioms solution
#check solution
