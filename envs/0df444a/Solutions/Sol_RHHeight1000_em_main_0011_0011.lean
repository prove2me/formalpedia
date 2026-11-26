-- Prove2me | solution 1 for RHHeight1000.em_main_0011_0011
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:56:55.496947+00:00
-- url     : https://prove2.me/submissions/c2f30949-a93f-47b4-b463-144b5791de3b

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow11.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow11.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow11.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow11.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow11.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz253 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz253

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz254 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz254 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138525251149047 2251799813685248 125000000017001 8500500000000000000 4138525251149047 2251799813685248 125000000017001 8500500000000000000 240893 131072

noncomputable abbrev qz255 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 131072 qz255 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 779317518150410741488063439345657628452599855445271348474342368876423347582876053728679783827237610085654588674605917415063316248867402488514697634436426745

noncomputable def ep10 := nat_lit 13198325246229587668616048586507268161410801335203869857947191811663857046415771104290097871102374067703089877156867761119753226876438075596795543285583799

noncomputable def ep11 := nat_lit 13338205139369261376383149914767634013226508915861991492218067381232119098362059104733250767410551174650894954010182016771344050520336484956804919489535

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 4 3 ep9 262144 68004 ep10 ep11 118379 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 3 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz256 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz256

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138525251149047 2251799813685248 125000000017001 8500500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 17358233014995452428288 9444732965739290427392 1000000000136008 68004000000000000000 4138525251149047 2251799813685248 125000000017001 8500500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 118379 262144 24973259072661432 36028797018963968 68004 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 779317518150412560342812906055656980396982394702499187106382620393032652998517540933158707129341055012778793601285942846917973645097155238594697634436426745

noncomputable def ep18 := nat_lit 13198325246229655554962711811363413523213721429909419700721697472804734044169853548961061453892255410264786862895235075217650796661500958924795543285583799

noncomputable def ep19 := nat_lit 13338205139369401582665284895604560799810298653799657073142644093199656832454717421805370366589019475922075211274104314270069372987910244956804919489535

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 4 3 ep17 262144 68004 ep18 ep19 118379 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 3 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138525251149047 2251799813685248 125000000017001 8500500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 17358233014995452428288 9444732965739290427392 1000000000136008 68004000000000000000 4138525251149047 2251799813685248 125000000017001 8500500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 118379 262144 24973259072661432 36028797018963968 68004 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz257 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz3 := (Real.log qz257)

theorem EMRow11.d4 : Enclosure.Real.IsNear qz3 Bool.false 240893 131072 3 131072 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz254) Bool.false 240893 131072 3 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz254) Bool.false 240893 131072 3 131072 240893 131072 3 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 300084 262144 1 68004 300084 262144 1 68004 150042 131072 2 131072 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 5456220599384213465248909714772227496572670538165976141063262914812807742611017753801422503639530882087556452122005170047444298375835020188444492540969863625638808382453421118235702266947370928498132967594635949979551089348001357731941995137847266570621617494261809398531128871567535833923098076891483476912075228072418610430965163137427706923427310178652894498746239459018086669257415154730407592571637957767157504839263249849478535520334507104454135585522664276476675

noncomputable def ep28 := nat_lit 583201912334273870627228188254822588827079241605343036411752047433839590517388190714780374919746279700129906501257101384229175562492847525225536391462542197025353003914524118772974087630067522636400444148635637549655768907025719966434833632093412247469427754039812435067522613541620617101084764807513402584784781490076808276521160080078978009740617112077674385114356333461540984478969922738031393369686631450339262287925718320742111081121726382582016608811398564907105

noncomputable def ep29 := nat_lit 2006268627360805445673839316848610509641534779303135707206598861506426804997221642604762844037348942607248852390277353874343091902420975230792155995982437872051629609224882022549487822374001366578458875613104959699164386313425243185530298109514065278868815165519648262204211929774735225023360668387821809970420335957473972782118680523137645713941929429588852958886338507735711181009301082096313539911189247153419366938656533848809858580689548163599238034961919825

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 10 9 ep27 262144 68004 ep28 ep29 300084 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 9 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 5456220599384260892400251500854699790811159195150212163211869656216336849990273498858157048596616978904240776489460003685239051624059887013466241201881443704542959173524008982544253046253151867013374679201187657749749224297051088632484873343955402287279851789208893474071824987110190207053471018354491495133306616646837230249901879422821128116650397962087630806812522581253210958036113071268120219429850657911869289056672761916619783759890108169949892385522664276476675

noncomputable def ep34 := nat_lit 583201912334279575053067226115417021307550325332234501953544426829928714668898700518418107620762577859683234776628347658361181262145210140271013263714562720079188253110303208819702903278206870150494721073991877864419341163488949363940583288588224434829960190109694548513088121652843287215458036179968684293644459891198769761601084092249455692877745995219003758983943549453190712470220270279351626860119698313725888367584660500821040083453648022042061408811398564907105

noncomputable def ep35 := nat_lit 2006268627360839170887858856494478835319319717359667041823756329478526322484078784125879825811686186445537802910004300367040714583746383402724632880452479311196631191501299191497899488881639138562974769996989848045902383299749709271247360054208480548633525642122514778503225872819822968825602771791453574137145372948950799520945900351638147820910599315255916738483881817718250085827996954508077874524152655659774549924038927632065100609588052048399238034961919825

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 10 9 ep33 262144 68004 ep34 ep35 300084 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 9 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 150042 131072 2 131072 75021 65536 1 65536 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 300084 262144 1 68004 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 300084 262144 68004 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 300084 262144 1 68004 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 300084 262144 68004 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow11.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 65536 := ep37

noncomputable abbrev qz437 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 51734 1000)))

noncomputable abbrev qz414 := qz437

noncomputable abbrev qz258 := qz414

noncomputable abbrev qz4 := (BSN.headSumC qz258 9)

noncomputable abbrev qz438 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz415 := qz438

noncomputable abbrev qz259 := qz415

noncomputable abbrev qz5 := qz259

noncomputable abbrev qz6 := (BSN.headSumC qz258 8)

noncomputable abbrev qz416 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz260 := qz416

noncomputable abbrev qz417 := (@Neg.neg Complex Complex.instNeg qz437)

noncomputable abbrev qz261 := qz417

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 8) qz261)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz4 (@HAdd.hAdd Complex Complex Complex qz5 qz6 qz7) Bool.false 53904728743 34359738368 1024304536759 194716637331456 Bool.true 632483307 8589934592 1026097348879 194716637331456

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP qz6 qz7 Bool.false 22565146049 17179869184 687119070127 146037477998592 Bool.false 2935706013 17179869184 2753991591919 584149911994368 Bool.false

noncomputable abbrev qz8 := (BSN.headSumC qz258 7)

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 7) qz261)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq qz6 (@HAdd.hAdd Complex Complex Complex qz5 qz8 qz9) Bool.false 22565146049 17179869184 687119070127 146037477998592 Bool.false 2935706013 17179869184 2753991591919 584149911994368

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP qz8 qz9 Bool.false 32267695759 34359738368 266986352593 64905545777152 Bool.false 957824793 4294967296 267810243721 64905545777152 Bool.false

noncomputable abbrev qz10 := (BSN.headSumC qz258 6)

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 6) qz261)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq qz8 (@HAdd.hAdd Complex Complex Complex qz5 qz10 qz11) Bool.false 32267695759 34359738368 266986352593 64905545777152 Bool.false 957824793 4294967296 267810243721 64905545777152

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP qz10 qz11 Bool.false 32017322469 34359738368 677599122659 194716637331456 Bool.true 1590619919 8589934592 339305989951 97358318665728 Bool.false

noncomputable abbrev qz12 := qz258

noncomputable abbrev qz13 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 5) qz261)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq qz10 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz12 5) qz13) Bool.false 32017322469 34359738368 677599122659 194716637331456 Bool.true 1590619919 8589934592 339305989951 97358318665728

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 5) qz13 Bool.false 8044102591 8589934592 406616317981 146037477998592 Bool.false 18005733963 68719476736 3254597372891 1168299823988736 Bool.true

noncomputable abbrev qz14 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 4) qz261)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz12 4) qz14) Bool.false 8044102591 8589934592 406616317981 146037477998592 Bool.false 18005733963 68719476736 3254597372891 1168299823988736

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 4) qz14 Bool.false 93854412479 68719476736 2340582043783 1168299823988736 Bool.false 1113091371 2147483648 292973862191 146037477998592 Bool.true

noncomputable abbrev qz418 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz262 := qz418

noncomputable abbrev qz15 := (@HPow.hPow Complex Complex Complex qz260 qz262 qz261)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz12 3) qz15) Bool.false 93854412479 68719476736 2340582043783 1168299823988736 Bool.false 1113091371 2147483648 292973862191 146037477998592

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 3) qz15 Bool.false 6974997083 8589934592 321807277537 292074955997184 Bool.false 2927685357 4294967296 161681477021 146037477998592 Bool.false

noncomputable abbrev qz419 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz263 := qz419

noncomputable abbrev qz16 := (@HPow.hPow Complex Complex Complex qz260 qz263 qz261)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz12 2) qz16) Bool.false 6974997083 8589934592 321807277537 292074955997184 Bool.false 2927685357 4294967296 161681477021 146037477998592

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 2) qz16 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz264 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz17 := qz264

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz17) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz12)

noncomputable abbrev qz265 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz18 := (@Inv.inv Real Real.instInv (Real.sqrt qz265))

noncomputable abbrev qz439 := (Enclosure.sfrac Bool.false 51734 1000)

noncomputable abbrev qz420 := qz439

noncomputable abbrev qz266 := qz420

noncomputable abbrev qz19 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz20 := qz266

noncomputable abbrev qz267 := (@Eq.refl Real qz420)

noncomputable abbrev qz21 := qz267

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz16 (Complex.mk (@HMul.hMul Real Real Real qz0 qz18 (Real.cos qz19)) (@HMul.hMul Real Real Real qz0 qz18 (@Neg.neg Real Real.instNeg (Real.sin qz19)))) Bool.true 1614937509 8589934592 321807277537 292074955997184 Bool.false 2927685357 4294967296 161681477021 146037477998592 (BSN.cpow_neg_s_mk qz20 51734 1000 2 qz21 rfl)

noncomputable abbrev qz22 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz265) 370727 262144 1 262144 92681 92683 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz265) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz265 qz22)) Bool.false 370727 262144 1 262144 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz265 qz22)) Bool.false 370727 262144 1 262144 370727 262144 1 262144 (BSN.sqrt_enclosure 2 1 185363 185364 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 131072 34002 24381081 945 90852 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 33344727106225854184049430854220366908217921472152042082544039615854084096

noncomputable def ep57 := nat_lit 278278412702595531909369356367009666242828713757909985904152976703587614720

noncomputable def ep58 := nat_lit 56884473378795079798521525313522711896915882172859997698460047879766016

noncomputable def ep59 := nat_lit 99920412371919972392551249512034055300859932652110406252235198751802720256

noncomputable def ep60 := nat_lit 12522528571616798935921621036515434980927292119105949365686883951661442662400

noncomputable abbrev qz268 := (BSN.cosEvenQ 536870912)

noncomputable abbrev qz269 := (BSN.cosOddQ 536870912)

noncomputable def ep61 := BSN.cos_dyadic_bound_f 698834308 536870912 3 2 262144 68071 ep56 ep57 ep58 ep59 ep60 ep58 69698 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 698834308) qz268 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 698834308) qz269 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz23 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz24 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz270 := (Enclosure.Real.IsNear.const Bool.false 51734 1000)

noncomputable abbrev qz25 := qz270

noncomputable abbrev qz271 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4700137) qz23)

noncomputable abbrev qz272 := (BSN.isNear_log_sfrac 2 1 90852 131072 1 34002 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 90852 131072 34002 rfl rfl rfl (ep55 rfl)))

noncomputable abbrev qz273 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz19 qz271 Bool.false 4700137 131072 25 16384 Bool.true 69698 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 587517171 16384000 25867 17001000 4700137 131072 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz20 qz24 51734 1000 0 1 90852 131072 1 34002 587517171 16384000 25867 17001000 qz25 qz272 rfl) rfl) (Enclosure.sfrac_false_div 4700137 131072) (BSN.cos_reduce2 qz271 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24588046331043322527744) qz273) 226375608064910080 72057594037927936 Bool.false 69698 262144 5 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q2 4700137 131072 226375608064910080 72057594037927936 5 24588046331043322527744 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 69698 262144 24588046331043322527744 18889465931478580854784 698834308 536870912 68071 68004 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 59975001212503501467450158317345842265274725944135387750420503270233538560

noncomputable def ep64 := nat_lit 2504505714323359787184324207303086996185458423821189873137376790332288532480

noncomputable def ep65 := nat_lit 156985285456800645142695665504445788208838799377789004111970478011187265536

noncomputable def ep66 := nat_lit 45915938095928262765045943800556594930066737770055147674185241156091956428800

noncomputable abbrev qz274 := (BSN.sinEvenQ 536870912)

noncomputable abbrev qz275 := (BSN.sinOddQ 536870912)

noncomputable def ep67 := BSN.sin_dyadic_bound_f 698834308 536870912 3 2 262144 68071 ep63 ep64 ep58 ep65 ep66 ep58 252708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 698834308) qz274 0 2 ep63 ep64 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 698834308) qz275 0 2 ep65 ep66 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz19 qz271 Bool.false 4700137 131072 25 16384 Bool.true 252708 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 587517171 16384000 25867 17001000 4700137 131072 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz20 qz24 51734 1000 0 1 90852 131072 1 34002 587517171 16384000 25867 17001000 qz25 qz272 rfl) rfl) (Enclosure.sfrac_false_div 4700137 131072) (BSN.sin_reduce2 qz271 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24588046331043322527744) qz273) 226375608064910080 72057594037927936 Bool.false 252708 262144 5 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q2 4700137 131072 226375608064910080 72057594037927936 5 24588046331043322527744 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 252708 262144 24588046331043322527744 18889465931478580854784 698834308 536870912 68071 68004 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz276 := (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 185364 262144 2 262144 46341 65536 1 131072 (ep54 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz18 (Real.cos qz19)) (@HMul.hMul Real Real Real qz0 qz18 (@Neg.neg Real Real.instNeg (Real.sin qz19))) Bool.true 1614937509 8589934592 321807277537 292074955997184 Bool.false 2927685357 4294967296 161681477021 146037477998592 (@Enclosure.Real.IsNear.mulLit_ft qz18 (Real.cos qz19) 46341 65536 1 131072 34849 131072 433217 278544384 1614937509 8589934592 321807277537 292074955997184 qz276 (@Enclosure.Real.IsNear.recentre' (Real.cos qz19) Bool.true 69698 262144 866434 557088768 34849 131072 433217 278544384 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@Neg.neg Real Real.instNeg (Real.sin qz19)) 46341 65536 1 131072 63177 65536 433217 278544384 2927685357 4294967296 161681477021 146037477998592 qz276 (@Enclosure.Real.IsNear.neg (Real.sin qz19) Bool.true 63177 65536 433217 278544384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz19) Bool.true 252708 262144 866434 557088768 63177 65536 433217 278544384 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz277 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz26 := qz277

noncomputable def ep70 := @ep51 1614937509 8589934592 321807277537 292074955997184 Bool.false 2927685357 4294967296 161681477021 146037477998592 Bool.false 6974997083 6974997083 8589934592 321807277537 292074955997184 Bool.false 2927685357 2927685357 4294967296 161681477021 146037477998592 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz17 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz26)) (ep53 ep69) rfl rfl

noncomputable abbrev qz27 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq qz15 (Complex.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.false 38054435815 68719476736 351117644545 389433274662912 Bool.true 701502615 4294967296 21882064195 24339579666432 (BSN.cpow_neg_s_mk qz20 51734 1000 3 qz21 rfl)

noncomputable abbrev qz29 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz29) 454047 262144 1 262144 75674 75675 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz29) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz29 qz22)) Bool.false 454047 262144 1 262144 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz29 qz22)) Bool.false 454047 262144 1 262144 454047 262144 1 262144 (BSN.sqrt_enclosure 3 1 227023 227024 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 9 8 2258332876800 131072 34002 222698787165 2027025 143997 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1) (BSN.artanhQ 2) 0 8 222698787165 2258332876800 2027025 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := nat_lit 562201102588262801769525709967616

noncomputable def ep75 := nat_lit 1993841993677373809355710590420516864

noncomputable def ep76 := nat_lit 29907629905160607140335658856307752960

noncomputable def ep77 := BSN.cos_dyadic_bound_f 153983052 536870912 2 1 262144 68071 ep74 ep75 ep74 ep74 ep76 ep74 251435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 153983052) qz268 0 1 ep74 ep75 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 153983052) qz269 0 1 ep74 ep76 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz30 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz31 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz32 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz278 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14899081) qz30)

noncomputable abbrev qz279 := (BSN.isNear_log_sfrac 3 1 143997 131072 1 34002 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 143997 131072 34002 rfl rfl rfl (ep73 rfl)))

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz28 qz278 Bool.false 14899081 262144 25 16384 Bool.false 251435 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 3724770399 65536000 25867 17001000 14899081 262144 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz20 qz31 51734 1000 0 1 143997 131072 1 34002 3724770399 65536000 25867 17001000 qz25 qz279 rfl) rfl) (Enclosure.sfrac_false_div 14899081 262144) (BSN.cos_reduce0 qz278 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10835594051970412838912) qz32) 226375608064910080 72057594037927936 Bool.false 251435 262144 9 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 14899081 262144 226375608064910080 72057594037927936 9 10835594051970412838912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 251435 262144 10835594051970412838912 37778931862957161709568 153983052 536870912 68071 68004 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 9969209968386869046778552952102584320

noncomputable def ep80 := nat_lit 69784469778708083327449870664718090240

noncomputable def ep81 := BSN.sin_dyadic_bound_f 153983052 536870912 2 1 262144 68071 ep74 ep79 ep74 ep74 ep80 ep74 74160 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 153983052) qz274 0 1 ep74 ep79 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 153983052) qz275 0 1 ep74 ep80 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable def ep82 := @Enclosure.Real.IsNear.sin_image qz28 qz278 Bool.false 14899081 262144 25 16384 Bool.false 74160 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 3724770399 65536000 25867 17001000 14899081 262144 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz20 qz31 51734 1000 0 1 143997 131072 1 34002 3724770399 65536000 25867 17001000 qz25 qz279 rfl) rfl) (Enclosure.sfrac_false_div 14899081 262144) (BSN.sin_reduce0 qz278 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10835594051970412838912) qz32) 226375608064910080 72057594037927936 Bool.false 74160 262144 9 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 14899081 262144 226375608064910080 72057594037927936 9 10835594051970412838912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 74160 262144 10835594051970412838912 37778931862957161709568 153983052 536870912 68071 68004 (ep81 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz280 := (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 151349 262144 1 262144 151349 262144 1 262144 (ep72 rfl rfl) rfl)

noncomputable def ep83 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.false 38054435815 68719476736 351117644545 389433274662912 Bool.true 701502615 4294967296 21882064195 24339579666432 (@Enclosure.Real.IsNear.mulLit_ff qz27 (Real.cos qz28) 151349 262144 1 262144 251435 262144 433217 278544384 38054435815 68719476736 351117644545 389433274662912 qz280 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.false 251435 262144 866434 557088768 251435 262144 433217 278544384 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 151349 262144 1 262144 4635 16384 433217 278544384 701502615 4294967296 21882064195 24339579666432 qz280 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.false 4635 16384 433217 278544384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.false 74160 262144 866434 557088768 4635 16384 433217 278544384 (ep82 rfl rfl) rfl)) rfl)

noncomputable def ep84 := @ep49 38054435815 68719476736 351117644545 389433274662912 Bool.true 701502615 4294967296 21882064195 24339579666432 Bool.false 806203264365198573568 93854412479 68719476736 2340582043783 1168299823988736 Bool.false 9561382071809605632 1113091371 2147483648 292973862191 146037477998592 (ep50 (BSN.head_sum_c_succ qz12 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep83) rfl rfl

noncomputable abbrev qz281 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt qz281))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep85 := @Enclosure.Complex.IsNear.of_eq qz14 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.true 29501591751 68719476736 912348500065 1168299823988736 Bool.true 17613189909 68719476736 910806475363 1168299823988736 (BSN.cpow_neg_s_mk qz20 51734 1000 4 qz21 rfl)

noncomputable def ep86 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz281) 524289 262144 1 262144 65535 65536 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz281) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz281 qz22)) Bool.false 524289 262144 1 262144 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz281 qz22)) Bool.false 524289 262144 1 262144 524289 262144 1 262144 (BSN.sqrt_enclosure 4 1 262144 262145 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep87 := nat_lit 753960950911045074462890625

noncomputable def ep88 := nat_lit 117048680082474133384580175

noncomputable def ep89 := BSN.log_dyadic_bound 3 5 12 11 ep87 131072 34002 ep88 431467934736729065175 181704 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 3) (BSN.artanhQ 5) 0 11 ep88 ep87 431467934736729065175 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep90 := nat_lit 23734436231469999983243004814712852626025667930944878071351547504686530560

noncomputable def ep91 := nat_lit 8918849099215807183494778366056060276884438949974089291257529306710016

noncomputable def ep92 := nat_lit 62147178660070317220672687730702904208666555489412817851830112226730049536

noncomputable def ep93 := BSN.sin_dyadic_bound_f 554355808 536870912 3 2 262144 68071 ep90 ep64 ep91 ep92 ep66 ep91 225081 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 554355808) qz274 0 2 ep90 ep64 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 554355808) qz275 0 2 ep92 ep66 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz35 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz282 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18800549) qz30)

noncomputable abbrev qz283 := (BSN.isNear_log_sfrac 4 1 181704 131072 1 34002 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 181704 131072 34002 rfl rfl rfl (ep89 rfl)))

noncomputable def ep94 := @Enclosure.Real.IsNear.cos_image qz34 qz282 Bool.false 18800549 262144 25 16384 Bool.true 225081 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 587517171 8192000 25867 17001000 18800549 262144 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz20 qz35 51734 1000 0 1 181704 131072 1 34002 587517171 8192000 25867 17001000 qz25 qz283 rfl) rfl) (Enclosure.sfrac_false_div 18800549 262144) (BSN.cos_reduce1 qz282 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39009322038793577955328) qz32) 226375608064910080 72057594037927936 Bool.false 225081 262144 11 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q1 18800549 262144 226375608064910080 72057594037927936 11 39009322038793577955328 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 225081 262144 39009322038793577955328 37778931862957161709568 554355808 536870912 68071 68004 (ep93 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep95 := nat_lit 13189761839305207016105444798558720819026208601169365190435863071184388096

noncomputable def ep96 := nat_lit 39551447819717189433949344838944050336524856925608147392725074154939744256

noncomputable def ep97 := BSN.cos_dyadic_bound_f 554355808 536870912 3 2 262144 68071 ep95 ep57 ep91 ep96 ep60 ep91 134379 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 554355808) qz268 0 2 ep95 ep57 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 554355808) qz269 0 2 ep96 ep60 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable def ep98 := @Enclosure.Real.IsNear.sin_image qz34 qz282 Bool.false 18800549 262144 25 16384 Bool.false 134379 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 587517171 8192000 25867 17001000 18800549 262144 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz20 qz35 51734 1000 0 1 181704 131072 1 34002 587517171 8192000 25867 17001000 qz25 qz283 rfl) rfl) (Enclosure.sfrac_false_div 18800549 262144) (BSN.sin_reduce1 qz282 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39009322038793577955328) qz32) 226375608064910080 72057594037927936 Bool.false 134379 262144 11 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q1 18800549 262144 226375608064910080 72057594037927936 11 39009322038793577955328 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 134379 262144 39009322038793577955328 37778931862957161709568 554355808 536870912 68071 68004 (ep97 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz284 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 131071 262144 1 262144 131071 262144 1 262144 (ep86 rfl rfl) rfl)

noncomputable def ep99 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.true 29501591751 68719476736 912348500065 1168299823988736 Bool.true 17613189909 68719476736 910806475363 1168299823988736 (@Enclosure.Real.IsNear.mulLit_ft qz33 (Real.cos qz34) 131071 262144 1 262144 225081 262144 433217 278544384 29501591751 68719476736 912348500065 1168299823988736 qz284 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.true 225081 262144 866434 557088768 225081 262144 433217 278544384 (ep94 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 131071 262144 1 262144 134379 262144 433217 278544384 17613189909 68719476736 910806475363 1168299823988736 qz284 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.false 134379 262144 433217 278544384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.false 134379 262144 866434 557088768 134379 262144 433217 278544384 (ep98 rfl rfl) rfl)) rfl)

noncomputable def ep100 := @ep47 29501591751 68719476736 912348500065 1168299823988736 Bool.true 17613189909 68719476736 910806475363 1168299823988736 Bool.false 4422292166913774583808 8044102591 8589934592 406616317981 146037477998592 Bool.false 38667019255780737024 18005733963 68719476736 3254597372891 1168299823988736 (ep48 (BSN.head_sum_c_succ qz12 3 4 rfl rfl) (ep84 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep85 ep99) rfl rfl

noncomputable abbrev qz285 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz285))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep101 := @Enclosure.Complex.IsNear.of_eq qz13 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.true 159087895 34359738368 406332096053 584149911994368 Bool.true 30730693315 68719476736 817074506521 1168299823988736 (BSN.cpow_neg_s_mk qz20 51734 1000 5 qz21 rfl)

noncomputable def ep102 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz285) 586171 262144 1 262144 58617 58618 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz285) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz285 qz22)) Bool.false 586171 262144 1 262144 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz285 qz22)) Bool.false 586171 262144 1 262144 586171 262144 1 262144 (BSN.sqrt_enclosure 5 1 293085 293086 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep103 := nat_lit 141613827518379161815574079375

noncomputable def ep104 := nat_lit 29325128709309236875766211300

noncomputable def ep105 := BSN.log_dyadic_bound 2 3 15 14 ep103 131072 34002 ep104 57299708096576225280000 210952 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP 2) (BSN.artanhQ 3) 0 14 ep104 ep103 57299708096576225280000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep106 := BSN.sin_dyadic_bound_f 5560091 536870912 1 0 262144 68071 0 1 1 0 1 1 2714 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 5560091) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 5560091) qz275 0 0 rfl) rfl rfl

noncomputable abbrev qz38 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz286 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21826781) qz30)

noncomputable abbrev qz287 := (BSN.isNear_log_sfrac 5 1 210952 131072 1 34002 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 210952 131072 34002 rfl rfl rfl (ep105 rfl)))

noncomputable def ep107 := @Enclosure.Real.IsNear.cos_image qz37 qz286 Bool.false 21826781 262144 25 16384 Bool.true 2714 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 682086923 8192000 25867 17001000 21826781 262144 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz20 qz38 51734 1000 0 1 210952 131072 1 34002 682086923 8192000 25867 17001000 qz25 qz287 rfl) rfl) (Enclosure.sfrac_false_div 21826781 262144) (BSN.cos_reduce1 qz286 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 391256675424741097472) qz32) 226375608064910080 72057594037927936 Bool.false 2714 262144 13 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q1 21826781 262144 226375608064910080 72057594037927936 13 391256675424741097472 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2714 262144 391256675424741097472 37778931862957161709568 5560091 536870912 68071 68004 (ep106 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep108 := BSN.cos_dyadic_bound_f 5560091 536870912 1 0 262144 68071 0 1 1 0 1 1 262129 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 5560091) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 5560091) qz269 0 0 rfl) rfl rfl

noncomputable def ep109 := @Enclosure.Real.IsNear.sin_image qz37 qz286 Bool.false 21826781 262144 25 16384 Bool.false 262129 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 682086923 8192000 25867 17001000 21826781 262144 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz20 qz38 51734 1000 0 1 210952 131072 1 34002 682086923 8192000 25867 17001000 qz25 qz287 rfl) rfl) (Enclosure.sfrac_false_div 21826781 262144) (BSN.sin_reduce1 qz286 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 391256675424741097472) qz32) 226375608064910080 72057594037927936 Bool.false 262129 262144 13 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q1 21826781 262144 226375608064910080 72057594037927936 13 391256675424741097472 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 262129 262144 391256675424741097472 37778931862957161709568 5560091 536870912 68071 68004 (ep108 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz288 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 117235 262144 1 262144 117235 262144 1 262144 (ep102 rfl rfl) rfl)

noncomputable def ep110 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.true 159087895 34359738368 406332096053 584149911994368 Bool.true 30730693315 68719476736 817074506521 1168299823988736 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz37) 117235 262144 1 262144 1357 131072 433217 278544384 159087895 34359738368 406332096053 584149911994368 qz288 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.true 2714 262144 866434 557088768 1357 131072 433217 278544384 (ep107 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 117235 262144 1 262144 262129 262144 433217 278544384 30730693315 68719476736 817074506521 1168299823988736 qz288 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.false 262129 262144 433217 278544384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.false 262129 262144 866434 557088768 262129 262144 433217 278544384 (ep109 rfl rfl) rfl)) rfl)

noncomputable def ep111 := @ep45 159087895 34359738368 406332096053 584149911994368 Bool.true 30730693315 68719476736 817074506521 1168299823988736 Bool.false 275026705819681947648 32017322469 34359738368 677599122659 194716637331456 Bool.true 874452548156309635072 1590619919 8589934592 339305989951 97358318665728 (ep46 (BSN.head_sum_c_succ qz12 4 5 rfl rfl) (ep100 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep101 ep110) rfl rfl

noncomputable abbrev qz289 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz39 := (@Inv.inv Real Real.instInv (Real.sqrt qz289))

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep112 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)))) Bool.false 125186645 17179869184 7709995945 12169789833216 Bool.false 3506269505 8589934592 124818751261 194716637331456 (BSN.cpow_neg_s_mk qz20 51734 1000 6 qz21 rfl)

noncomputable abbrev qz290 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz22)

noncomputable def ep113 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz289) 642119 262144 1 262144 53509 53511 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz289) (Real.sqrt qz290) Bool.false 642119 262144 1 262144 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz290) Bool.false 642119 262144 1 262144 642119 262144 1 262144 (BSN.sqrt_enclosure 6 1 321059 321060 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep114 := BSN.log_dyadic_bound 2 10 4 3 105000000 131072 34002 1434560 960 53145 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz41 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep115 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz41 51734 1000 0 1 4034681531866359 2251799813685248 250000000017001 8500500000000000000 104365107184787108253 1125899906842624000 6466750000439764867 4250250000000000000000 qz25 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000017001 8500500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz290) Bool.false 8461340443916598509568 4722366482869645213696 1000000000068004 34002000000000000000 4034681531866359 2251799813685248 250000000017001 8500500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 53145 131072 24973259072661432 36028797018963968 34002 1000000000000000 rfl rfl rfl rfl (ep114 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep116 := BSN.sin_dyadic_bound_f 9584424 536870912 1 0 262144 68071 0 1 1 0 1 1 4679 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 9584424) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 9584424) qz275 0 0 rfl) rfl rfl

noncomputable abbrev qz291 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24299395) qz30)

noncomputable def ep117 := @Enclosure.Real.IsNear.cos_image qz40 qz291 Bool.false 24299395 262144 399 262144 Bool.false 4679 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 104365107184787108253 1125899906842624000 6466750000439764867 4250250000000000000000 24299395 262144 399 262144 (ep115 rfl) rfl) (Enclosure.sfrac_false_div 24299395 262144) (BSN.cos_reduce3 qz291 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 674443921012304117760) qz32) 226375608064910080 72057594037927936 Bool.false 4679 262144 14 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q3 24299395 262144 226375608064910080 72057594037927936 14 674443921012304117760 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4679 262144 674443921012304117760 37778931862957161709568 9584424 536870912 68071 68004 (ep116 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep118 := BSN.cos_dyadic_bound_f 9584424 536870912 1 0 262144 68071 0 1 1 0 1 1 262102 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 9584424) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 9584424) qz269 0 0 rfl) rfl rfl

noncomputable def ep119 := @Enclosure.Real.IsNear.sin_image qz40 qz291 Bool.false 24299395 262144 399 262144 Bool.true 262102 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 104365107184787108253 1125899906842624000 6466750000439764867 4250250000000000000000 24299395 262144 399 262144 (ep115 rfl) rfl) (Enclosure.sfrac_false_div 24299395 262144) (BSN.sin_reduce3 qz291 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 674443921012304117760) qz32) 226375608064910080 72057594037927936 Bool.false 262102 262144 14 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q3 24299395 262144 226375608064910080 72057594037927936 14 674443921012304117760 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 262102 262144 674443921012304117760 37778931862957161709568 9584424 536870912 68071 68004 (ep118 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz292 := (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 107020 262144 2 262144 26755 65536 1 131072 (ep113 rfl rfl) rfl)

noncomputable def ep120 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40))) Bool.false 125186645 17179869184 7709995945 12169789833216 Bool.false 3506269505 8589934592 124818751261 194716637331456 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz40) 26755 65536 1 131072 4679 262144 6914471 4456710144 125186645 17179869184 7709995945 12169789833216 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz40) Bool.false 4679 262144 13828942 8913420288 4679 262144 6914471 4456710144 (ep117 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)) 26755 65536 1 131072 131051 131072 6914471 4456710144 3506269505 8589934592 124818751261 194716637331456 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz40) Bool.true 131051 131072 6914471 4456710144 (@Enclosure.Real.IsNear.recentre' (Real.sin qz40) Bool.true 262102 262144 13828942 8913420288 131051 131072 6914471 4456710144 (ep119 rfl rfl) rfl)) rfl)

noncomputable def ep121 := @ep43 125186645 17179869184 7709995945 12169789833216 Bool.false 3506269505 8589934592 124818751261 194716637331456 Bool.false 554354792008731590656 32267695759 34359738368 266986352593 64905545777152 Bool.false 16455304644931878912 957824793 4294967296 267810243721 64905545777152 (ep44 (BSN.head_sum_c_succ qz12 5 6 rfl rfl) (ep111 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep112 ep120) rfl rfl

noncomputable abbrev qz293 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt qz293))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep122 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.false 12862596339 34359738368 345599107171 584149911994368 Bool.true 895593159 17179869184 171849699215 292074955997184 (BSN.cpow_neg_s_mk qz20 51734 1000 7 qz21 rfl)

noncomputable abbrev qz294 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) qz22)

noncomputable def ep123 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz293) 693567 262144 1 262144 49540 49541 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz293) (Real.sqrt qz294) Bool.false 693567 262144 1 262144 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz294) Bool.false 693567 262144 1 262144 693567 262144 1 262144 (BSN.sqrt_enclosure 7 1 346783 346784 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep124 := BSN.log_dyadic_bound 3 11 5 4 202569142545 131072 34002 5259111624 688905 73349 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz44 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep125 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz44 51734 1000 0 1 4381783608859895 2251799813685248 250000000017001 8500500000000000000 22668719322075780793 225179981368524800 6466750000439764867 4250250000000000000000 qz25 (BSN.isNear_log_sfrac 7 1 4381783608859895 2251799813685248 250000000017001 8500500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz294) Bool.false 9189266258887746519040 4722366482869645213696 1000000000068004 34002000000000000000 4381783608859895 2251799813685248 250000000017001 8500500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 73349 131072 24973259072661432 36028797018963968 34002 1000000000000000 rfl rfl rfl rfl (ep124 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep126 := nat_lit 30453760034496055091525751234001

noncomputable def ep127 := BSN.cos_dyadic_bound_f 74286557 536870912 2 1 262144 68071 ep126 ep75 ep126 ep126 ep76 ep126 259638 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 74286557) qz268 0 1 ep126 ep75 ep126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 74286557) qz269 0 1 ep126 ep76 ep126 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz295 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13194931) qz23)

noncomputable def ep128 := @Enclosure.Real.IsNear.cos_image qz43 qz295 Bool.false 13194931 131072 25 16384 Bool.false 259638 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 22668719322075780793 225179981368524800 6466750000439764867 4250250000000000000000 13194931 131072 25 16384 (ep125 rfl) rfl) (Enclosure.sfrac_false_div 13194931 131072) (BSN.cos_reduce0 qz295 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2613725894771780616192) qz273) 226375608064910080 72057594037927936 Bool.false 259638 262144 16 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 13194931 131072 226375608064910080 72057594037927936 16 2613725894771780616192 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 259638 262144 2613725894771780616192 18889465931478580854784 74286557 536870912 68071 68004 (ep127 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep129 := BSN.sin_dyadic_bound_f 74286557 536870912 1 0 262144 68071 0 1 1 0 1 1 36156 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 74286557) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 74286557) qz275 0 0 rfl) rfl rfl

noncomputable def ep130 := @Enclosure.Real.IsNear.sin_image qz43 qz295 Bool.false 13194931 131072 25 16384 Bool.false 36156 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 22668719322075780793 225179981368524800 6466750000439764867 4250250000000000000000 13194931 131072 25 16384 (ep125 rfl) rfl) (Enclosure.sfrac_false_div 13194931 131072) (BSN.sin_reduce0 qz295 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2613725894771780616192) qz273) 226375608064910080 72057594037927936 Bool.false 36156 262144 16 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 13194931 131072 226375608064910080 72057594037927936 16 2613725894771780616192 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 36156 262144 2613725894771780616192 18889465931478580854784 74286557 536870912 68071 68004 (ep129 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz296 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 99081 262144 1 262144 99081 262144 1 262144 (ep123 rfl rfl) rfl)

noncomputable def ep131 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.false 12862596339 34359738368 345599107171 584149911994368 Bool.true 895593159 17179869184 171849699215 292074955997184 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz43) 99081 262144 1 262144 129819 131072 433217 278544384 12862596339 34359738368 345599107171 584149911994368 qz296 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.false 259638 262144 866434 557088768 129819 131072 433217 278544384 (ep128 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 99081 262144 1 262144 9039 65536 433217 278544384 895593159 17179869184 171849699215 292074955997184 qz296 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.false 9039 65536 433217 278544384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.false 36156 262144 866434 557088768 9039 65536 433217 278544384 (ep130 rfl rfl) rfl)) rfl)

noncomputable def ep132 := @ep41 12862596339 34359738368 345599107171 584149911994368 Bool.true 895593159 17179869184 171849699215 292074955997184 Bool.false 1550665028958697816064 22565146049 17179869184 687119070127 146037477998592 Bool.false 12608761316505550848 2935706013 17179869184 2753991591919 584149911994368 (ep42 (BSN.head_sum_c_succ qz12 6 7 rfl rfl) (ep121 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep122 ep131) rfl rfl

noncomputable abbrev qz297 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv (Real.sqrt qz297))

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep133 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)))) Bool.false 8774436645 34359738368 324437329769 584149911994368 Bool.true 4200672627 17179869184 162150227359 292074955997184 (BSN.cpow_neg_s_mk qz20 51734 1000 8 qz21 rfl)

noncomputable abbrev qz298 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz22)

noncomputable def ep134 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz297) 741455 262144 1 262144 46340 46342 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz297) (Real.sqrt qz298) Bool.false 741455 262144 1 262144 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz298) Bool.false 741455 262144 1 262144 741455 262144 1 262144 (BSN.sqrt_enclosure 8 1 370727 370728 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep135 := BSN.log_dyadic_bound 0 16 1 0 1 131072 34002 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz47 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep136 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz47 51734 1000 0 1 9364972152248037 4503599627370496 500000000051003 17001000000000000000 242243734662199973079 2251799813685248000 12933500001319294601 8500500000000000000000 qz25 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000051003 17001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz298) Bool.false 9819885039515637645312 4722366482869645213696 1000000000102006 34002000000000000000 9364972152248037 4503599627370496 500000000051003 17001000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 131072 24973259072661432 36028797018963968 34002 1000000000000000 rfl rfl rfl rfl (ep135 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep137 := nat_lit 28256532366655593458619263427438961

noncomputable def ep138 := BSN.cos_dyadic_bound_f 409996091 536870912 2 1 262144 68071 ep137 ep75 ep137 ep137 ep76 ep137 189345 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 409996091) qz268 0 1 ep137 ep75 ep137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 409996091) qz269 0 1 ep137 ep76 ep137 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz299 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14100441) qz23)

noncomputable def ep139 := @Enclosure.Real.IsNear.cos_image qz46 qz299 Bool.false 14100441 131072 25 16384 Bool.false 189345 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 242243734662199973079 2251799813685248000 12933500001319294601 8500500000000000000000 14100441 131072 25 16384 (ep136 rfl) rfl) (Enclosure.sfrac_false_div 14100441 131072) (BSN.cos_reduce0 qz299 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14425455048204455247872) qz273) 226375608064910080 72057594037927936 Bool.false 189345 262144 17 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 14100441 131072 226375608064910080 72057594037927936 17 14425455048204455247872 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 189345 262144 14425455048204455247872 18889465931478580854784 409996091 536870912 68071 68004 (ep138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep140 := BSN.sin_dyadic_bound_f 409996091 536870912 2 1 262144 68071 ep137 ep79 ep137 ep137 ep80 ep137 181294 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 409996091) qz274 0 1 ep137 ep79 ep137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 409996091) qz275 0 1 ep137 ep80 ep137 rfl rfl rfl rfl) rfl rfl

noncomputable def ep141 := @Enclosure.Real.IsNear.sin_image qz46 qz299 Bool.false 14100441 131072 25 16384 Bool.false 181294 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 242243734662199973079 2251799813685248000 12933500001319294601 8500500000000000000000 14100441 131072 25 16384 (ep136 rfl) rfl) (Enclosure.sfrac_false_div 14100441 131072) (BSN.sin_reduce0 qz299 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14425455048204455247872) qz273) 226375608064910080 72057594037927936 Bool.false 181294 262144 17 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 14100441 131072 226375608064910080 72057594037927936 17 14425455048204455247872 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 181294 262144 14425455048204455247872 18889465931478580854784 409996091 536870912 68071 68004 (ep140 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz300 := (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 92682 262144 2 262144 46341 131072 1 131072 (ep134 rfl rfl) rfl)

noncomputable def ep142 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46))) Bool.false 8774436645 34359738368 324437329769 584149911994368 Bool.true 4200672627 17179869184 162150227359 292074955997184 (@Enclosure.Real.IsNear.mulLit_ff qz45 (Real.cos qz46) 46341 131072 1 131072 189345 262144 433217 278544384 8774436645 34359738368 324437329769 584149911994368 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz46) Bool.false 189345 262144 866434 557088768 189345 262144 433217 278544384 (ep139 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)) 46341 131072 1 131072 90647 131072 433217 278544384 4200672627 17179869184 162150227359 292074955997184 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz46) Bool.false 90647 131072 433217 278544384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz46) Bool.false 181294 262144 866434 557088768 90647 131072 433217 278544384 (ep141 rfl rfl) rfl)) rfl)

noncomputable def ep143 := @ep39 8774436645 34359738368 324437329769 584149911994368 Bool.true 4200672627 17179869184 162150227359 292074955997184 Bool.false 926076188203744755712 53904728743 34359738368 1024304536759 194716637331456 Bool.true 21731960950647422976 632483307 8589934592 1026097348879 194716637331456 (ep40 (BSN.head_sum_c_succ qz12 7 8 rfl rfl) (ep132 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep133 ep142) rfl rfl

theorem EMRow11.d6 : Enclosure.Complex.IsNear qz4 Bool.false 53904728743 34359738368 1024304536759 194716637331456 Bool.true 632483307 8589934592 1026097348879 194716637331456 := ep38 (BSN.head_sum_c_succ qz12 8 9 rfl rfl) (ep143 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow11.d7 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow11.d8 : @Eq Nat (Nat.pow 11 1) 11 := @Eq.refl Nat 11

noncomputable def ep144 := nat_lit 277708980600929568835237722803

noncomputable def ep145 := nat_lit 132600494058123526968180736000

noncomputable def ep146 := nat_lit 923961364925285430576524972549242751

noncomputable def ep147 := nat_lit 114978153996588508655534033451614208000

noncomputable abbrev qz440 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz421 := qz440

noncomputable abbrev qz301 := qz421

noncomputable abbrev qz48 := qz301

noncomputable abbrev qz49 := (@instHSub Real Real.instSub)

noncomputable abbrev qz422 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz302 := qz422

noncomputable abbrev qz50 := qz302

noncomputable abbrev qz441 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz442 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz423 := (@HAdd.hAdd Complex Complex Complex qz438 (@HAdd.hAdd Complex Complex Complex qz438 qz441 (@HMul.hMul Complex Complex Complex qz440 Complex.I (@HDiv.hDiv Complex Complex Complex qz442 (↑qz439) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz303 := qz423

noncomputable abbrev qz51 := (Complex.Stirling.logGammaStirling 1 qz303)

noncomputable abbrev qz424 := (@HAdd.hAdd Complex Complex Complex qz438 qz441 (@HMul.hMul Complex Complex Complex qz440 Complex.I (@HDiv.hDiv Complex Complex Complex qz442 (↑qz439) (2 : Complex))))

noncomputable abbrev qz304 := qz424

noncomputable abbrev qz52 := qz304

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz253 (@HDiv.hDiv Real Real Real qz256 qz266 (2 : Real)) (Real.log Real.pi))

noncomputable def ep148 := Complex.re (@HMul.hMul Complex Complex Complex qz48 (Complex.exp (@HMul.hMul Complex Complex Complex qz48 Complex.I ↑(@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))))) qz53))) (zetaApproximant qz12 1 11))

noncomputable def ep149 := @Enclosure.Real.IsNear.of_eq ep148 (@HSub.hSub Real Real Real qz49 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))))) qz53)) (Complex.re (zetaApproximant qz12 1 11))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))))) qz53)) (Complex.im (zetaApproximant qz12 1 11))))

noncomputable def ep150 := nat_lit 55541703868186970802420871119

noncomputable def ep151 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))))) qz53)) (Complex.re (zetaApproximant qz12 1 11))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))))) qz53)) (Complex.im (zetaApproximant qz12 1 11))) ep150

noncomputable def ep152 := nat_lit 26520098811624705393636147200

noncomputable def ep153 := nat_lit 184286426208112181666651419710834611

noncomputable def ep154 := nat_lit 22995630799317701731106806690322841600

noncomputable def ep155 := nat_lit 1506823796115040079183872000

noncomputable def ep156 := nat_lit 898165442018651364796830253931

noncomputable def ep157 := nat_lit 40830310368106714721425438015488000

noncomputable def ep158 := nat_lit 83691700072866143431871902957941605496782010400846643200

noncomputable def ep159 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))))) qz53)) (Complex.re (zetaApproximant qz12 1 11)) 262143 262144 3004241

noncomputable def ep160 := nat_lit 34043055139342307877677803

noncomputable def ep161 := nat_lit 5159777067906550785795686400

noncomputable def ep162 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))))) qz53)) Bool.true 262143 262144 6008482

noncomputable abbrev qz305 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 463249) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep163 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))))) qz53) qz305 Bool.false 463249 16384 169

noncomputable def ep164 := nat_lit 278544384000000000000000000

noncomputable def ep165 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))))) qz53) Bool.false 152804312459693804899 5404319552844595200 178281306302507022412301 ep164

noncomputable def ep166 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))))) qz53 1564150552831815418607 27021597764222976000 68340089552507022412301 ep164 1940568207 65536000

noncomputable def ep167 := nat_lit 50070917106792465989304320000

noncomputable def ep168 := nat_lit 139272192000000000000000000

noncomputable def ep169 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 182513682660249350523 4503599627370496000 58409654315156133807107 ep168 Bool.false 1564150552831815418607 27021597764222976000

noncomputable def ep170 := nat_lit 46424064000000000000000000

noncomputable def ep171 := @Enclosure.Complex.IsNear.subLitP qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 153208092232174167523 4503599627370496000 18787218104634228026369 ep170 Bool.false 1647475529499511834607 27021597764222976000 20049363184076159342767

noncomputable def ep172 := nat_lit 92848128000000000000000000

noncomputable def ep173 := nat_lit 821968553218715932113266798292369408

noncomputable def ep174 := nat_lit 440269240430294952262081896557576192

noncomputable abbrev qz443 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz425 := qz443

noncomputable abbrev qz306 := (@HSub.hSub Complex Complex Complex qz422 qz423 qz425)

noncomputable abbrev qz307 := (Complex.log qz423)

noncomputable abbrev qz54 := (@HSub.hSub Complex Complex Complex qz302 (@HMul.hMul Complex Complex Complex qz301 qz306 qz307) qz303)

noncomputable abbrev qz308 := qz425

noncomputable abbrev qz55 := (@HMul.hMul Complex Complex Complex qz301 qz308 ↑(Real.log qz257))

noncomputable abbrev qz426 := qz442

noncomputable abbrev qz309 := qz426

noncomputable abbrev qz56 := qz309

noncomputable abbrev qz57 := (@instHMul Nat instMulNat)

noncomputable abbrev qz427 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz310 := qz427

noncomputable abbrev qz58 := qz310

noncomputable abbrev qz59 := qz303

noncomputable abbrev qz311 := (@instHSub Int Int.instSub)

noncomputable abbrev qz60 := qz311

noncomputable abbrev qz312 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz61 := qz312

noncomputable abbrev qz313 := (@instHMul Int Int.instMul)

noncomputable abbrev qz62 := qz313

noncomputable abbrev qz314 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz63 := qz314

noncomputable def ep175 := @Enclosure.Complex.IsNear.of_eq qz51 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz54 qz55) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz50 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz58 qz59 (@HSub.hSub Int Int Int qz60 qz61 (@HMul.hMul Int Int Int qz62 qz63 (@Nat.cast Int instNatCastInt k)))))) Bool.true 153208092232174167523

noncomputable def ep176 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz54 qz55) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz50 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz58 qz59 (@HSub.hSub Int Int Int qz60 qz61 (@HMul.hMul Int Int Int qz62 qz63 (@Nat.cast Int instNatCastInt k))))) Bool.true 153209344779274839523 4503599627370496000

noncomputable def ep177 := nat_lit 329011872809869844243655163904

noncomputable def ep178 := nat_lit 884481690020085822200253251584000

noncomputable def ep179 := @ep176 4586707336661624789 11334000000000000000000 Bool.false 549187309509484462757 9007199254740992000 815750000443070617 3778000000000000000000 Bool.false 597261 2147483648 3 2147483648 Bool.true 5149783429 1610612736000 25867 1610612736000 Bool.true ep177 153208092232174167523 4503599627370496000 18787218104634228026369 ep170 Bool.false ep178

noncomputable def ep180 := @Enclosure.Complex.IsNear.addLitP qz54 qz55 Bool.true 157347855006616151523 4503599627370496000 4457000000235843539 11334000000000000000000

noncomputable def ep181 := nat_lit 40162910477818223531917312

noncomputable def ep182 := @ep180 Bool.false 549187309509484462757 9007199254740992000 815750000443070617 3778000000000000000000 Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 Bool.true ep181 153209344779274839523 4503599627370496000 4586707336661624789 11334000000000000000000 Bool.false 549187309509484462757 549187309509484462757 9007199254740992000

noncomputable abbrev qz64 := (@HMul.hMul Complex Complex Complex qz301 qz306 qz307)

noncomputable def ep183 := @Enclosure.Complex.IsNear.subLitP qz64 qz59 Bool.true 147214755845032535523 4503599627370496000 4457000000235843539 11334000000000000000000 Bool.false 782176532631869702821

noncomputable def ep184 := nat_lit 2196749238037937851028000

noncomputable def ep185 := @ep183 9007199254740992000 815750000443070617 3778000000000000000000 Bool.false 9000 4000 0 1 Bool.false 103468 4000 0 1 Bool.true 629391420026464606092000 157347855006616151523 4503599627370496000 4457000000235843539 11334000000000000000000 Bool.false ep184 549187309509484462757 9007199254740992000 815750000443070617 3778000000000000000000

noncomputable abbrev qz65 := qz306

noncomputable abbrev qz66 := qz307

noncomputable def ep186 := @Enclosure.Complex.IsNear.mul qz65 qz66 Bool.true 147214755845032535523 4503599627370496000 4457000000235843539 11334000000000000000000 Bool.false 782176532631869702821 9007199254740992000 815750000443070617

noncomputable abbrev qz67 := (Complex.re qz306)

noncomputable abbrev qz68 := (Complex.re qz307)

noncomputable abbrev qz69 := (Complex.im qz306)

noncomputable abbrev qz70 := (Complex.im qz307)

noncomputable def ep187 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz67 qz68) (@HMul.hMul Real Real Real qz0 qz69 qz70) 205338462428733641 36028797018963968 1750000001071063 136008000000000000000 21610257956078030081 562949953421312000

noncomputable def ep188 := nat_lit 662996319567127074965808224202129408

noncomputable def ep189 := @Enclosure.Real.IsNear.mulLit_ff qz67 qz68 7000 4000 0 1 29334066061247663 9007199254740992 250000000153009 34002000000000000000

noncomputable def ep190 := @Enclosure.Complex.IsNear.re_isNear qz65 Bool.false 7000 4000 0 1 Bool.false 103468 4000 0 1

noncomputable abbrev qz315 := (Enclosure.sfrac Bool.false 103468 4000)

noncomputable abbrev qz71 := qz315

noncomputable def ep191 := @Enclosure.Complex.IsNear.of_eq qz65 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz71) Bool.false 7000 4000 0 1 Bool.false 103468 4000 0

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz72 := (Complex.mk qz316 qz315)

noncomputable def ep192 := @Enclosure.Complex.IsNear.of_eq qz66 (Complex.log qz72) Bool.false 29334066061247663 9007199254740992 250000000153009 34002000000000000000 Bool.false 835437350913443 562949953421312 500000000017001 34002000000000000000

noncomputable def ep193 := nat_lit 1946033995895279686892833244126039743856640

noncomputable def ep194 := nat_lit 12260061705462003636548848234766711390208

noncomputable def ep195 := nat_lit 135963082813136618194160422050956771328

noncomputable def ep196 := BSN.log_dyadic_bound 2594627024 18978627024 3 2 ep193 262144 68004 ep194 ep195 72128 21573254048 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2594627024) (BSN.artanhQ 18978627024) 0 2 ep194 ep193 ep195 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz73 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz317 := (Real.log (Enclosure.sfrac Bool.false 10786627024 16000000))

noncomputable abbrev qz318 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep197 := @Enclosure.Real.IsNear.mulLit_ff qz73 qz317 1 2 0 1 29334066061247663 4503599627370496 250000000153009 17001000000000000000 29334066061247663 9007199254740992 250000000153009 34002000000000000000 qz318 (BSN.isNear_log_sfrac 10786627024 16000000 29334066061247663 4503599627370496 250000000153009 17001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10786627024) qz319)) Bool.false 61517995308477658955776 9444732965739290427392 1000000000612036 68004000000000000000 29334066061247663 4503599627370496 250000000153009 17001000000000000000 (BSN.log_rat_reduce_isNear 10786627024 16000000 9 21573254048 16384000000 72128 262144 24973259072661432 36028797018963968 68004 1000000000000000 rfl rfl rfl rfl (ep196 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep198 := BSN.arctan_dyadic_bound_f 9000 103468 1 0 262144 68004 0 1 1 0 1 1 22744 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 103468) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 103468) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz74 := (@HMul.hMul Real Real Real qz253 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz75 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz318 BSN.pi_near_15 rfl)

noncomputable abbrev qz320 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 103468)))

noncomputable def ep199 := @Enclosure.Real.IsNear.subLit_ff_p qz74 qz320 884279719003555 562949953421312 1 2000000000000000 22744 262144 1 68004 219004888917853601792 835437350913443 562949953421312 500000000017001 34002000000000000000 qz75 (ep198 rfl) rfl rfl

noncomputable abbrev qz321 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 103468) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep200 := @Enclosure.Complex.IsNear.re_isNear qz66 Bool.false 29334066061247663 9007199254740992 250000000153009 34002000000000000000 Bool.false 835437350913443 562949953421312 500000000017001 34002000000000000000 (ep192 (@congrArg Complex Complex qz59 qz72 Complex.log (BSN.w_shift_mk qz20 Bool.false 51734 1000 2 qz21 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz72) Bool.false 29334066061247663 9007199254740992 250000000153009 34002000000000000000 Bool.false 835437350913443 562949953421312 500000000017001 34002000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz72)) (@HMul.hMul Real Real Real qz0 qz73 qz317) Bool.false 29334066061247663 9007199254740992 250000000153009 34002000000000000000 (Enclosure.clog_re_eq 9000 103468 4000 10786627024 16000000 rfl rfl rfl) (ep197 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz72)) qz321 Bool.false 835437350913443 562949953421312 500000000017001 34002000000000000000 (Enclosure.clog_im_eq 9000 103468 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz321 (@HSub.hSub Real Real Real qz49 qz74 qz320) Bool.false 835437350913443 562949953421312 500000000017001 34002000000000000000 (BSN.arctan_recip 103468 9000 rfl rfl) ep199))))

noncomputable def ep201 := @Enclosure.Real.IsNear.mulLit_ff qz69 qz70 103468 4000 0 1 835437350913443 562949953421312 500000000017001 34002000000000000000

noncomputable def ep202 := @Enclosure.Complex.IsNear.im_isNear qz65 Bool.false 7000 4000 0 1 Bool.false 103468 4000 0 1

noncomputable def ep203 := @Enclosure.Complex.IsNear.im_isNear qz66 Bool.false 29334066061247663 9007199254740992 250000000153009 34002000000000000000 Bool.false 835437350913443 562949953421312 500000000017001 34002000000000000000 (ep192 (@congrArg Complex Complex qz59 qz72 Complex.log (BSN.w_shift_mk qz20 Bool.false 51734 1000 2 qz21 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz72) Bool.false 29334066061247663 9007199254740992 250000000153009 34002000000000000000 Bool.false 835437350913443 562949953421312 500000000017001 34002000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz72)) (@HMul.hMul Real Real Real qz0 qz73 qz317) Bool.false 29334066061247663 9007199254740992 250000000153009 34002000000000000000 (Enclosure.clog_re_eq 9000 103468 4000 10786627024 16000000 rfl rfl rfl) (ep197 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz72)) qz321 Bool.false 835437350913443 562949953421312 500000000017001 34002000000000000000 (Enclosure.clog_im_eq 9000 103468 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz321 (@HSub.hSub Real Real Real qz49 qz74 qz320) Bool.false 835437350913443 562949953421312 500000000017001 34002000000000000000 (BSN.arctan_recip 103468 9000 rfl rfl) ep199))))

noncomputable abbrev qz322 := (Enclosure.Real.IsNear.const Bool.false 103468 4000)

noncomputable abbrev qz76 := (@ep191 1 (BSN.w_sub_half_mk qz266 Bool.false 51734 1000 2 qz267 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz315 Bool.false 7000 4000 0 1 Bool.false 103468 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz322))

noncomputable def ep204 := @ep187 12933500000439764867 34002000000000000000000 ep188 147214755845032535523 4503599627370496000 4457000000235843539 11334000000000000000000 (@ep189 205338462428733641 36028797018963968 1750000001071063 136008000000000000000 (ep190 qz76) ep200 rfl) (@ep201 21610257956078030081 562949953421312000 12933500000439764867 34002000000000000000000 (ep202 qz76) ep203 rfl) rfl

noncomputable def ep205 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz67 qz70) (@HMul.hMul Real Real Real qz0 qz69 qz68) 5848061456394101 2251799813685248 3500000000119007 136008000000000000000 758784286806293298821 9007199254740992000

noncomputable def ep206 := nat_lit 1761304970449417499285616822591684608

noncomputable def ep207 := @Enclosure.Real.IsNear.mulLit_ff qz67 qz70 7000 4000 0 1 835437350913443 562949953421312 500000000017001 34002000000000000000

noncomputable def ep208 := @Enclosure.Real.IsNear.mulLit_ff qz69 qz68 103468 4000 0 1 29334066061247663 9007199254740992 250000000153009 34002000000000000000

noncomputable def ep209 := @ep205 6466750003957883803 34002000000000000000000 ep206 782176532631869702821 9007199254740992000 815750000443070617 3778000000000000000000 (@ep207 5848061456394101 2251799813685248 3500000000119007 136008000000000000000 (ep190 qz76) ep203 rfl) (@ep208 758784286806293298821 9007199254740992000 6466750003957883803 34002000000000000000000 (ep202 qz76) ep200 rfl) rfl

noncomputable def ep210 := @Enclosure.Complex.IsNear.of_eq qz59 qz72 Bool.false 9000 4000 0 1 Bool.false 103468 4000 0 1 (BSN.w_shift_mk qz20 Bool.false 51734 1000 2 qz21 rfl)

noncomputable abbrev qz323 := (ep210 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 103468 4000) Bool.false 9000 4000 0 1 Bool.false 103468 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 103468 4000)))

noncomputable abbrev qz77 := qz323

noncomputable def ep211 := ep185 (@ep186 3778000000000000000000 (ep204 rfl) (ep209 rfl)) qz77 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz78 := qz308

noncomputable def ep212 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz78) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz78) (Complex.im ↑qz3)) 240893 262144 3 262144 0 1 0 1 240893 240893

noncomputable def ep213 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz78) (Complex.re ↑qz3) 1 2 0 1 240893 131072 3 131072 240893 262144 3 262144

noncomputable abbrev qz79 := (@Enclosure.Complex.IsNear.of_eq qz308 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz264) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz264 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz318 qz277))

noncomputable def ep214 := ep213 (@Enclosure.Complex.IsNear.re_isNear qz78 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz79) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 240893 131072 3 131072 (Complex.ofReal_re qz3) EMRow11.d4)

noncomputable def ep215 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz78) (Complex.im ↑qz3) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep216 := ep215 (@Enclosure.Complex.IsNear.im_isNear qz78 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz79) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz17 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz17 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz26)

noncomputable def ep217 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz78) (Complex.im ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz78) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep218 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz78) (Complex.im ↑qz3) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep219 := ep218 (@Enclosure.Complex.IsNear.re_isNear qz78 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz79) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz17 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz17 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz26)

noncomputable def ep220 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz78) (Complex.re ↑qz3) 0 1 0 1 240893 131072 3 131072 0 1 0 1

noncomputable def ep221 := ep220 (@Enclosure.Complex.IsNear.im_isNear qz78 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz79) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 240893 131072 3 131072 (Complex.ofReal_re qz3) EMRow11.d4)

noncomputable def ep222 := @ep182 815750000443070617 3778000000000000000000 (ep211 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz78 (↑qz3) Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 (@ep212 262144 3 262144 (ep214 rfl) (ep216 rfl) rfl rfl) (@ep217 1 0 1 (ep219 rfl) (ep221 rfl) rfl rfl))

noncomputable abbrev qz80 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz324 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz81 := (@HMul.hMul Complex Complex Complex qz301 (@HMul.hMul Complex Complex Complex qz301 (2 : Complex) qz324) (@HSub.hSub Complex Complex Complex qz302 (@HMul.hMul Complex Complex Complex qz301 (2 : Complex) qz324) (1 : Complex)))

noncomputable abbrev qz325 := (@HPow.hPow Complex Int Complex qz427 qz423 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz82 := qz325

noncomputable def ep223 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz50 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz58 qz59 (@HSub.hSub Int Int Int qz60 qz61 (@HMul.hMul Int Int Int qz62 qz63 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz50 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz58 qz59 (@HSub.hSub Int Int Int qz60 qz61 (@HMul.hMul Int Int Int qz62 qz63 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81) qz82)) Bool.false 597261 2147483648 3 2147483648

noncomputable def ep224 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz50 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz58 qz59 (@HSub.hSub Int Int Int qz60 qz61 (@HMul.hMul Int Int Int qz62 qz63 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81) qz82) Bool.false 0 1 0 1 Bool.false

noncomputable def ep225 := @ep224 0 1 0 1 Bool.false 597261 2147483648 3 2147483648 Bool.true 5149783429 1610612736000 25867 1610612736000 Bool.false 597261 597261 2147483648 3 2147483648 Bool.true 5149783429 5149783429 1610612736000 25867

noncomputable def ep226 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz50 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz58 qz59 (@HSub.hSub Int Int Int qz60 qz61 (@HMul.hMul Int Int Int qz62 qz63 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz17 qz17) Bool.false 0 1 0 1 Bool.false

noncomputable def ep227 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81) qz82 Bool.false 597261 2147483648 3 2147483648 Bool.true 5149783429 1610612736000 25867 1610612736000

noncomputable abbrev qz83 := (Complex.re qz325)

noncomputable abbrev qz84 := (Complex.im qz325)

noncomputable def ep228 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz83) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz84) 597261 2147483648 3 2147483648 0 1 0

noncomputable def ep229 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz83 1 12 0 1 1791783 536870912 9 536870912 597261

noncomputable def ep230 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz17) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz326 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz17 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz26)

noncomputable def ep231 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep230 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz326)

noncomputable def ep232 := @Enclosure.Complex.IsNear.re_isNear qz82 Bool.false 1791783 536870912 9 536870912 Bool.true 5149783429 134217728000 25867 134217728000

noncomputable abbrev qz428 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz327 := (@HPow.hPow Complex Nat Complex qz428 qz423 1)

noncomputable abbrev qz85 := (@Inv.inv Complex Complex.instInv qz327)

noncomputable def ep233 := @Enclosure.Complex.IsNear.of_eq qz82 qz85 Bool.false 1791783 536870912 9 536870912 Bool.true 5149783429 134217728000 25867

noncomputable def ep234 := @Enclosure.Complex.IsNear.of_parts qz85 Bool.false 1791783 536870912 9 536870912 Bool.true 5149783429 134217728000 25867

noncomputable abbrev qz86 := (Complex.re qz327)

noncomputable abbrev qz87 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz88 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz89 := qz327

noncomputable def ep235 := @Enclosure.Real.IsNear.mulLit_ff qz86 (@Inv.inv Real Real.instInv (@DFunLike.coe qz87 Complex (fun (x : Complex) => Real) qz88 Complex.normSq qz89)) 9000 4000 0 1 199087 134217728 1 134217728

noncomputable def ep236 := @Enclosure.Complex.IsNear.re_isNear qz89 Bool.false 9000 4000 0 1 Bool.false 103468 4000 0 1

noncomputable def ep237 := @Enclosure.Complex.IsNear.of_eq qz89 qz59 Bool.false 9000 4000 0 1 Bool.false 103468 4000 0

noncomputable def ep238 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz87 Complex (fun (x : Complex) => Real) qz88 Complex.normSq qz89)) Bool.false 199087 134217728 1 134217728 199087 134217728 1

noncomputable abbrev qz90 := (@instHAdd Real Real.instAdd)

noncomputable abbrev qz91 := (Complex.im qz327)

noncomputable def ep239 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz87 Complex (fun (x : Complex) => Real) qz88 Complex.normSq qz89) (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 qz86 qz86) (@HMul.hMul Real Real Real qz0 qz91 qz91)) Bool.false 674164189 1000000 0 1

noncomputable def ep240 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz86 qz86) (@HMul.hMul Real Real Real qz0 qz91 qz91) 81 16 0 1 669101689 1000000

noncomputable def ep241 := @Enclosure.Real.IsNear.mulLit_ff qz86 qz86 9000 4000 0 1 9000 4000 0 1

noncomputable def ep242 := @Enclosure.Real.IsNear.mulLit_ff qz91 qz91 103468 4000 0 1 103468 4000 0 1

noncomputable def ep243 := @Enclosure.Complex.IsNear.im_isNear qz89 Bool.false 9000 4000 0 1 Bool.false 103468 4000 0 1

noncomputable abbrev qz92 := (ep236 (@ep237 1 (BSN.pow_one_c qz303) qz323))

noncomputable abbrev qz93 := (ep243 (@ep237 1 (BSN.pow_one_c qz303) qz323))

noncomputable def ep244 := @ep240 0 1 10786627024 674164189 1000000 0 1 (@ep241 81 16 0 1 qz92 qz92 rfl) (@ep242 669101689 1000000 0 1 qz93 qz93 rfl)

noncomputable def ep245 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz87 Complex (fun (x : Complex) => Real) qz88 Complex.normSq qz89) 674164189 1000000 0 1 99543 99544 67108864 (ep239 (Enclosure.Complex.normSq_eq_mul_add_mul qz89) (ep244 rfl rfl)) rfl

noncomputable def ep246 := @Enclosure.Real.IsNear.of_eq (Complex.re qz85) (@HMul.hMul Real Real Real qz0 qz86 (@Inv.inv Real Real.instInv (@DFunLike.coe qz87 Complex (fun (x : Complex) => Real) qz88 Complex.normSq qz89))) Bool.false 1791783 536870912 9 536870912 (Enclosure.Complex.inv_re_eq_mul qz89) (@ep235 1791783 536870912 9 536870912 qz92 (@ep238 134217728 (ep245 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep247 := @Enclosure.Real.IsNear.of_eq (Complex.im qz85) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz91) (@Inv.inv Real Real.instInv (@DFunLike.coe qz87 Complex (fun (x : Complex) => Real) qz88 Complex.normSq qz89))) Bool.true 5149783429 134217728000 25867 134217728000 (Enclosure.Complex.inv_im_eq_mul qz89)

noncomputable def ep248 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz91) (@Inv.inv Real Real.instInv (@DFunLike.coe qz87 Complex (fun (x : Complex) => Real) qz88 Complex.normSq qz89)) 103468 4000 0 1 199087 134217728 1

noncomputable def ep249 := @ep248 134217728 5149783429 134217728000 25867 134217728000 (@Enclosure.Real.IsNear.neg qz91 Bool.false 103468 4000 0 1 qz93) (@ep238 134217728 (ep245 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep250 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz84 0 1 0 1 5149783429 134217728000 25867 134217728000 0

noncomputable def ep251 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep230 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz326)

noncomputable def ep252 := @Enclosure.Complex.IsNear.im_isNear qz82 Bool.false 1791783 536870912 9 536870912 Bool.true 5149783429 134217728000 25867 134217728000

noncomputable abbrev qz94 := (@ep233 134217728000 (BSN.zpow_one_sub_two_mul qz303 1 1 rfl rfl) (@ep234 134217728000 ep246 (ep247 ep249)))

noncomputable def ep253 := @ep228 1 597261 597261 2147483648 3 2147483648 (@ep229 2147483648 3 2147483648 ep231 (ep232 qz94) rfl) (@ep250 1 0 1 ep251 (ep252 qz94) rfl) rfl

noncomputable def ep254 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz84) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz83) 5149783429 1610612736000 25867 1610612736000 0 1 0

noncomputable def ep255 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz84 1 12 0 1 5149783429 134217728000 25867 134217728000 5149783429

noncomputable def ep256 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz83 0 1 0 1 1791783 536870912 9 536870912 0

noncomputable def ep257 := @ep254 1 5149783429 5149783429 1610612736000 25867 1610612736000 (@ep255 1610612736000 25867 1610612736000 ep231 (ep252 qz94) rfl) (@ep256 1 0 1 ep251 (ep232 qz94) rfl) rfl

noncomputable abbrev qz95 := (@Enclosure.Complex.IsNear.mk qz264 qz264 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz277 qz277)

noncomputable def ep258 := @ep225 1610612736000 (@ep226 0 1 0 1 (BSN.stirling_sum_base qz59) qz95) (ep227 (ep253 rfl) (ep257 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep259 := @ep179 1647475529499511834607 27021597764222976000 20049363184076159342767 ep172 (ep222 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep223 Bool.true 5149783429 1610612736000 25867 1610612736000 (BSN.stirling_sum_succ qz59 0 1 rfl) (ep258 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep260 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz20 2) Bool.false 29305590428075183 4503599627370496 250000000153009 17001000000000000000 Bool.false 867968506955171 281474976710656

noncomputable abbrev qz96 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz259 qz304 qz324))

noncomputable def ep261 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz20 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz20 1) qz96) Bool.false 29305590428075183 4503599627370496 250000000153009 17001000000000000000 Bool.false 867968506955171 281474976710656 500000000017001 17001000000000000000

noncomputable def ep262 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz20 1) qz96 Bool.false 29300548136469679 9007199254740992 250000000153009 34002000000000000000 Bool.false 878840142923171 562949953421312 500000000017001 34002000000000000000 Bool.false

noncomputable def ep263 := nat_lit 527922584527007074071987536003072

noncomputable def ep264 := nat_lit 977245661123158470318520008704

noncomputable abbrev qz97 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz259 qz304 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep265 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz20 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz20 0) qz97) Bool.false 29300548136469679 9007199254740992 250000000153009 34002000000000000000 Bool.false 878840142923171 562949953421312 500000000017001 34002000000000000000

noncomputable def ep266 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz20 0) qz97 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz328 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz71))

noncomputable def ep267 := @Enclosure.Complex.IsNear.of_eq qz97 qz328 Bool.false 29300548136469679 9007199254740992 250000000153009 34002000000000000000 Bool.false 878840142923171 562949953421312 500000000017001 34002000000000000000

noncomputable def ep268 := nat_lit 1913428662281377440807753713870884543856640

noncomputable def ep269 := nat_lit 11412131034717328734630016952017271390208

noncomputable def ep270 := nat_lit 119954230376801382845664291019916771328

noncomputable def ep271 := BSN.log_dyadic_bound 2514627024 18898627024 3 2 ep268 262144 68004 ep269 ep270 70177 21413254048 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2514627024) (BSN.artanhQ 18898627024) 0 2 ep269 ep268 ep270 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep272 := @Enclosure.Real.IsNear.mulLit_ff qz73 (Real.log (Enclosure.sfrac Bool.false 10706627024 16000000)) 1 2 0 1 29300548136469679 4503599627370496 250000000153009 17001000000000000000 29300548136469679 9007199254740992 250000000153009 34002000000000000000 qz318 (BSN.isNear_log_sfrac 10706627024 16000000 29300548136469679 4503599627370496 250000000153009 17001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10706627024) qz319)) Bool.false 61447703125493660254208 9444732965739290427392 1000000000612036 68004000000000000000 29300548136469679 4503599627370496 250000000153009 17001000000000000000 (BSN.log_rat_reduce_isNear 10706627024 16000000 9 21413254048 16384000000 70177 262144 24973259072661432 36028797018963968 68004 1000000000000000 rfl rfl rfl rfl (ep271 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep273 := BSN.arctan_dyadic_bound_f 1000 103468 1 0 262144 68004 0 1 1 0 1 1 2533 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 103468) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 103468) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz329 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz330 := (@Nat.cast Real Real.instNatCast 103468)

noncomputable def ep274 := @Enclosure.Real.IsNear.subLit_ff_p qz74 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz329 qz330)) 884279719003555 562949953421312 1 2000000000000000 2533 262144 1 68004 230382670426451738624 878840142923171 562949953421312 500000000017001 34002000000000000000 qz75 (ep273 rfl) rfl rfl

noncomputable abbrev qz98 := (@HAdd.hAdd Complex Complex Complex qz259 qz304 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz331 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz71)

noncomputable def ep275 := @ep266 29300548136469679 9007199254740992 250000000153009 34002000000000000000 Bool.false 878840142923171 562949953421312 500000000017001 34002000000000000000 Bool.false 29300548136469679 29300548136469679 9007199254740992 250000000153009 34002000000000000000 Bool.false 878840142923171 878840142923171 562949953421312 500000000017001 34002000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz20 0) (Complex.mk qz17 qz17) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz20) qz95) (ep267 (@congrArg Complex Complex qz98 qz331 Complex.log (BSN.w_shift_mk qz20 Bool.false 51734 1000 0 qz21 rfl)) (@Enclosure.Complex.IsNear.of_parts qz328 Bool.false 29300548136469679 9007199254740992 250000000153009 34002000000000000000 Bool.false 878840142923171 562949953421312 500000000017001 34002000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz328) (@HMul.hMul Real Real Real qz0 qz73 (Real.log (Enclosure.sfrac Bool.false 10706627024 16000000))) Bool.false 29300548136469679 9007199254740992 250000000153009 34002000000000000000 (Enclosure.clog_re_eq 1000 103468 4000 10706627024 16000000 rfl rfl rfl) (ep272 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz328) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz329)) Bool.false 878840142923171 562949953421312 500000000017001 34002000000000000000 (Enclosure.clog_im_eq 1000 103468 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz329)) (@HSub.hSub Real Real Real qz49 qz74 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz329 qz330))) Bool.false 878840142923171 562949953421312 500000000017001 34002000000000000000 (BSN.arctan_recip 103468 1000 rfl rfl) ep274)))) rfl rfl

noncomputable abbrev qz332 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz71))

noncomputable def ep276 := @Enclosure.Complex.IsNear.of_eq qz96 qz332 Bool.false 29310632719680687 9007199254740992 250000000153009 34002000000000000000 Bool.false 857096870987171 562949953421312 500000000017001 34002000000000000000

noncomputable def ep277 := nat_lit 1923166901847548972091675739987431103856640

noncomputable def ep278 := nat_lit 11662603003873185020415355424842103390208

noncomputable def ep279 := nat_lit 124599657964249720073846538329228771328

noncomputable def ep280 := BSN.log_dyadic_bound 2538627024 18922627024 3 2 ep277 262144 68004 ep278 ep279 70764 21461254048 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2538627024) (BSN.artanhQ 18922627024) 0 2 ep278 ep277 ep279 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep281 := @Enclosure.Real.IsNear.mulLit_ff qz73 (Real.log (Enclosure.sfrac Bool.false 10730627024 16000000)) 1 2 0 1 29310632719680687 4503599627370496 250000000153009 17001000000000000000 29310632719680687 9007199254740992 250000000153009 34002000000000000000 qz318 (BSN.isNear_log_sfrac 10730627024 16000000 29310632719680687 4503599627370496 250000000153009 17001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10730627024) qz319)) Bool.false 61468852029343792103424 9444732965739290427392 1000000000612036 68004000000000000000 29310632719680687 4503599627370496 250000000153009 17001000000000000000 (BSN.log_rat_reduce_isNear 10730627024 16000000 9 21461254048 16384000000 70764 262144 24973259072661432 36028797018963968 68004 1000000000000000 rfl rfl rfl rfl (ep280 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep282 := BSN.arctan_dyadic_bound_f 5000 103468 1 0 262144 68004 0 1 1 0 1 1 12658 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 103468) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 103468) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz333 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep283 := @Enclosure.Real.IsNear.subLit_ff_p qz74 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz333 qz330)) 884279719003555 562949953421312 1 2000000000000000 12658 262144 1 68004 224682802148060954624 857096870987171 562949953421312 500000000017001 34002000000000000000 qz75 (ep282 rfl) rfl rfl

noncomputable abbrev qz99 := (@HAdd.hAdd Complex Complex Complex qz259 qz304 qz324)

noncomputable abbrev qz334 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz71)

noncomputable def ep284 := @ep262 29310632719680687 9007199254740992 250000000153009 34002000000000000000 Bool.false 857096870987171 562949953421312 500000000017001 34002000000000000000 Bool.false ep263 29305590428075183 4503599627370496 250000000153009 17001000000000000000 Bool.false ep264 867968506955171 281474976710656 500000000017001 17001000000000000000 (ep265 (BSN.log_sum_c_succ qz20 0 1 rfl) (ep275 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep276 (@congrArg Complex Complex qz99 qz334 Complex.log (BSN.w_shift_mk qz20 Bool.false 51734 1000 1 qz21 rfl)) (@Enclosure.Complex.IsNear.of_parts qz332 Bool.false 29310632719680687 9007199254740992 250000000153009 34002000000000000000 Bool.false 857096870987171 562949953421312 500000000017001 34002000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz332) (@HMul.hMul Real Real Real qz0 qz73 (Real.log (Enclosure.sfrac Bool.false 10730627024 16000000))) Bool.false 29310632719680687 9007199254740992 250000000153009 34002000000000000000 (Enclosure.clog_re_eq 5000 103468 4000 10730627024 16000000 rfl rfl rfl) (ep281 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz332) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz333)) Bool.false 857096870987171 562949953421312 500000000017001 34002000000000000000 (Enclosure.clog_im_eq 5000 103468 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz333)) (@HSub.hSub Real Real Real qz49 qz74 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz333 qz330))) Bool.false 857096870987171 562949953421312 500000000017001 34002000000000000000 (BSN.arctan_recip 103468 5000 rfl rfl) ep283)))) rfl rfl

noncomputable def ep285 := @ep171 ep172 Bool.false 29305590428075183 4503599627370496 250000000153009 17001000000000000000 Bool.false 867968506955171 281474976710656 500000000017001 17001000000000000000 Bool.true ep173 182513682660249350523 4503599627370496000 58409654315156133807107 ep168 Bool.false ep174 1564150552831815418607 27021597764222976000 68340089552507022412301 ep164 (@ep175 4503599627370496000 18787218104634228026369 ep170 Bool.false 1647475529499511834607 27021597764222976000 20049363184076159342767 ep172 (BSN.logGammaStirling_unfold 1 qz59) (ep259 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep260 500000000017001 17001000000000000000 (BSN.log_sum_c_eq qz20 2) (ep261 (BSN.log_sum_c_succ qz20 1 2 rfl) (ep284 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz100 := (@HDiv.hDiv Real Real Real qz256 qz266 (2 : Real))

noncomputable def ep286 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log Real.pi) 51734 2000 0 1 75021 65536 1 65536 1940568207 65536000 25867 65536000 (@Enclosure.Real.IsNear.of_eq qz100 (Enclosure.sfrac Bool.false 51734 2000) Bool.false 51734 2000 0 1 (BSN.t_half_eq qz20 Bool.false 51734 1000 qz21) (Enclosure.Real.IsNear.const Bool.false 51734 2000)) EMRow11.d5 rfl

noncomputable def ep287 := @ep166 25867 65536000 ep167 152804312459693804899 5404319552844595200 178281306302507022412301 ep164 (@ep169 68340089552507022412301 ep164 (ep285 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep286 rfl rfl

noncomputable def ep288 := BSN.cos_dyadic_bound_f 75814 536870912 1 0 262144 68071 0 1 1 0 1 1 262143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 75814) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 75814) qz269 0 0 rfl) rfl rfl

noncomputable def ep289 := @ep163 262144 Bool.true 262143 262144 1 34002 (@ep165 463249 16384 169 262144 ep287 rfl) (Enclosure.sfrac_false_div 463249 16384) (BSN.cos_reduce2 qz305 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 333435313395335168) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 262143 262144 4 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q2 463249 16384 226375608064910080 72057594037927936 4 333435313395335168 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 262143 262144 333435313395335168 2361183241434822606848 75814 536870912 68071 68004 (ep288 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep290 := nat_lit 42596019927532296351933947

noncomputable def ep291 := nat_lit 6449721334883188482244608000

noncomputable abbrev qz101 := qz260

noncomputable abbrev qz102 := qz261

noncomputable abbrev qz429 := (@Nat.cast Complex Complex.instNatCast 11)

noncomputable abbrev qz335 := (@HPow.hPow Complex Complex Complex qz416 qz429 qz417)

noncomputable abbrev qz103 := qz335

noncomputable abbrev qz336 := qz429

noncomputable abbrev qz104 := (@HAdd.hAdd Complex Complex Complex qz259 (@HDiv.hDiv Complex Complex Complex qz309 qz336 (@HSub.hSub Complex Complex Complex qz302 qz258 (1 : Complex))) qz308)

noncomputable abbrev qz105 := (@instHSub Nat instSubNat)

noncomputable abbrev qz337 := qz428

noncomputable abbrev qz106 := qz337

noncomputable abbrev qz107 := qz336

noncomputable def ep292 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz12 1 11) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 11, @HPow.hPow Complex Complex Complex qz101 (@Nat.cast Complex Complex.instNatCast n) qz102) (@HMul.hMul Complex Complex Complex qz48 qz103 (@HAdd.hAdd Complex Complex Complex qz5 qz104 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))))) Bool.false 211875594115375847542833 101166148420809575628800 ep160

noncomputable def ep293 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 11, @HPow.hPow Complex Complex Complex qz101 (@Nat.cast Complex Complex.instNatCast n) qz102) (@HMul.hMul Complex Complex Complex qz48 qz103 (@HAdd.hAdd Complex Complex Complex qz5 qz104 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))))) Bool.false 148053073683 68719476736 2444723071757 389433274662912

noncomputable def ep294 := nat_lit 1651816732833446018232403

noncomputable def ep295 := nat_lit 2072377141491196697123447

noncomputable def ep296 := nat_lit 14559979960737749055115995107033088

noncomputable def ep297 := nat_lit 4867559194725548413357259751424

noncomputable def ep298 := @ep293 Bool.true 5965507205 34359738368 1223405949811 194716637331456 Bool.true 6082398840716416248567 101166148420809575628800 ep294 ep161 Bool.false 856311330160462840007 5748076614818725888000 ep295 ep291 Bool.false ep296 211875594115375847542833 101166148420809575628800 ep160 ep161 Bool.true ep297 141664617541407596243 5748076614818725888000

noncomputable def ep299 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 11, @HPow.hPow Complex Complex Complex qz101 (@Nat.cast Complex Complex.instNatCast n) qz102) (BSN.headSumC qz12 11) Bool.false 148053073683 68719476736 2444723071757 389433274662912 Bool.true 5965507205 34359738368 1223405949811

noncomputable abbrev qz108 := (BSN.headSumC qz258 10)

noncomputable abbrev qz109 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 10) qz261)

noncomputable def ep300 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 11) (@HAdd.hAdd Complex Complex Complex qz5 qz108 qz109) Bool.false 148053073683 68719476736 2444723071757 389433274662912 Bool.true 5965507205 34359738368 1223405949811 194716637331456

noncomputable def ep301 := @Enclosure.Complex.IsNear.addLitP qz108 qz109 Bool.false 63523279699 34359738368 3377627955505 584149911994368 Bool.true 17495143947 68719476736 6764689408889 1168299823988736 Bool.false

noncomputable abbrev qz110 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 9) qz261)

noncomputable def ep302 := @Enclosure.Complex.IsNear.of_eq qz108 (@HAdd.hAdd Complex Complex Complex qz5 qz4 qz110) Bool.false 63523279699 34359738368 3377627955505 584149911994368 Bool.true 17495143947 68719476736 6764689408889 1168299823988736

noncomputable def ep303 := @Enclosure.Complex.IsNear.addLitP qz4 qz110 Bool.false 53904728743 34359738368 1024304536759 194716637331456 Bool.true 632483307 8589934592 1026097348879 194716637331456 Bool.false

noncomputable abbrev qz338 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz111 := (@Inv.inv Real Real.instInv (Real.sqrt qz338))

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep304 := @Enclosure.Complex.IsNear.of_eq qz110 (Complex.mk (@HMul.hMul Real Real Real qz0 qz111 (Real.cos qz112)) (@HMul.hMul Real Real Real qz0 qz111 (@Neg.neg Real Real.instNeg (Real.sin qz112)))) Bool.false 2404637739 8589934592 76178586307 146037477998592 Bool.true 12435277491 68719476736 608105315615 1168299823988736 (BSN.cpow_neg_s_mk qz20 51734 1000 9 qz21 rfl)

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9) qz22)

noncomputable def ep305 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz338) 786433 262144 1 262144 43690 43691 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz338) (Real.sqrt qz339) Bool.false 786433 262144 1 262144 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 786433 262144 1 262144 786433 262144 1 262144 (BSN.sqrt_enclosure 9 1 393216 393217 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep306 := BSN.log_dyadic_bound 1 17 2 1 867 131072 34002 1 1 15438 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz113 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep307 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz113 51734 1000 0 1 9895417793173221 4503599627370496 500000000051003 17001000000000000000 255964772056011707607 2251799813685248000 12933500001319294601 8500500000000000000000 qz25 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000051003 17001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false 10376097607894403383296 4722366482869645213696 1000000000102006 34002000000000000000 9895417793173221 4503599627370496 500000000051003 17001000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 15438 131072 24973259072661432 36028797018963968 34002 1000000000000000 rfl rfl rfl rfl (ep306 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep308 := nat_lit 9009343338737907752714235261396961

noncomputable def ep309 := BSN.cos_dyadic_bound_f 308086937 536870912 2 1 262144 68071 ep308 ep75 ep308 ep308 ep76 ep308 220152 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 308086937) qz268 0 1 ep308 ep75 ep308 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 308086937) qz269 0 1 ep308 ep76 ep308 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29798221) qz30)

noncomputable def ep310 := @Enclosure.Real.IsNear.cos_image qz112 qz340 Bool.false 29798221 262144 25 16384 Bool.false 220152 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz112 Bool.false 255964772056011707607 2251799813685248000 12933500001319294601 8500500000000000000000 29798221 262144 25 16384 (ep307 rfl) rfl) (Enclosure.sfrac_false_div 29798221 262144) (BSN.cos_reduce0 qz340 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21679690900037301174272) qz32) 226375608064910080 72057594037927936 Bool.false 220152 262144 18 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 29798221 262144 226375608064910080 72057594037927936 18 21679690900037301174272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 220152 262144 21679690900037301174272 37778931862957161709568 308086937 536870912 68071 68004 (ep309 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep311 := BSN.sin_dyadic_bound_f 308086937 536870912 2 1 262144 68071 ep308 ep79 ep308 ep308 ep80 ep308 142311 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 308086937) qz274 0 1 ep308 ep79 ep308 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 308086937) qz275 0 1 ep308 ep80 ep308 rfl rfl rfl rfl) rfl rfl

noncomputable def ep312 := @Enclosure.Real.IsNear.sin_image qz112 qz340 Bool.false 29798221 262144 25 16384 Bool.false 142311 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz112 Bool.false 255964772056011707607 2251799813685248000 12933500001319294601 8500500000000000000000 29798221 262144 25 16384 (ep307 rfl) rfl) (Enclosure.sfrac_false_div 29798221 262144) (BSN.sin_reduce0 qz340 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21679690900037301174272) qz32) 226375608064910080 72057594037927936 Bool.false 142311 262144 18 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 29798221 262144 226375608064910080 72057594037927936 18 21679690900037301174272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 142311 262144 21679690900037301174272 37778931862957161709568 308086937 536870912 68071 68004 (ep311 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz341 := (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 87381 262144 1 262144 87381 262144 1 262144 (ep305 rfl rfl) rfl)

noncomputable def ep313 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz111 (Real.cos qz112)) (@HMul.hMul Real Real Real qz0 qz111 (@Neg.neg Real Real.instNeg (Real.sin qz112))) Bool.false 2404637739 8589934592 76178586307 146037477998592 Bool.true 12435277491 68719476736 608105315615 1168299823988736 (@Enclosure.Real.IsNear.mulLit_ff qz111 (Real.cos qz112) 87381 262144 1 262144 27519 32768 433217 278544384 2404637739 8589934592 76178586307 146037477998592 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz112) Bool.false 220152 262144 866434 557088768 27519 32768 433217 278544384 (ep310 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz111 (@Neg.neg Real Real.instNeg (Real.sin qz112)) 87381 262144 1 262144 142311 262144 433217 278544384 12435277491 68719476736 608105315615 1168299823988736 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz112) Bool.false 142311 262144 433217 278544384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz112) Bool.false 142311 262144 866434 557088768 142311 262144 433217 278544384 (ep312 rfl rfl) rfl)) rfl)

noncomputable def ep314 := @ep303 2404637739 8589934592 76178586307 146037477998592 Bool.true 12435277491 68719476736 608105315615 1168299823988736 Bool.false 545660817683731447808 63523279699 34359738368 3377627955505 584149911994368 Bool.true 150282142182354714624 17495143947 68719476736 6764689408889 1168299823988736 EMRow11.d6 (ep304 ep313) rfl rfl

noncomputable abbrev qz342 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz114 := (@Inv.inv Real Real.instInv (Real.sqrt qz342))

noncomputable abbrev qz115 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep315 := @Enclosure.Complex.IsNear.of_eq qz109 (Complex.mk (@HMul.hMul Real Real Real qz0 qz114 (Real.cos qz115)) (@HMul.hMul Real Real Real qz0 qz114 (@Neg.neg Real Real.instNeg (Real.sin qz115)))) Bool.false 21006514285 68719476736 578913304261 1168299823988736 Bool.false 5564129537 68719476736 575746289977 1168299823988736 (BSN.cpow_neg_s_mk qz20 51734 1000 10 qz21 rfl)

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10) qz22)

noncomputable def ep316 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz342) 828973 262144 1 262144 41448 41449 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz342) (Real.sqrt qz343) Bool.false 828973 262144 1 262144 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz343) Bool.false 828973 262144 1 262144 828973 262144 1 262144 (BSN.sqrt_enclosure 10 1 414486 414487 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep317 := BSN.log_dyadic_bound 2 18 3 2 1574640 131072 34002 6528 48 29247 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz116 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep318 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz116 51734 1000 0 1 10369891420296933 4503599627370496 500000000051003 17001000000000000000 268237981368820765911 2251799813685248000 12933500001319294601 8500500000000000000000 qz25 (BSN.isNear_log_sfrac 10 1 10369891420296933 4503599627370496 500000000051003 17001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false 10873619265929276817408 4722366482869645213696 1000000000102006 34002000000000000000 10369891420296933 4503599627370496 500000000051003 17001000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 29247 131072 24973259072661432 36028797018963968 34002 1000000000000000 rfl rfl rfl rfl (ep317 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep319 := nat_lit 61876069255385930657447954568942620694613894270751587859929271778672640000

noncomputable def ep320 := nat_lit 60544201694743786646679112343518018825922383854293172446927257600000000

noncomputable def ep321 := nat_lit 161958347913743090353030971974864977407794420182871017353948305765171200000

noncomputable def ep322 := BSN.sin_dyadic_bound_f 704302240 536870912 3 2 262144 68071 ep319 ep64 ep320 ep321 ep66 ep320 253405 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 704302240) qz274 0 2 ep319 ep64 ep320 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 704302240) qz275 0 2 ep321 ep66 ep320 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15613505) qz23)

noncomputable def ep323 := @Enclosure.Real.IsNear.cos_image qz115 qz344 Bool.false 15613505 131072 25 16384 Bool.false 253405 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz115 Bool.false 268237981368820765911 2251799813685248000 12933500001319294601 8500500000000000000000 15613505 131072 25 16384 (ep318 rfl) rfl) (Enclosure.sfrac_false_div 15613505 131072) (BSN.cos_reduce3 qz344 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24780432077023986319360) qz273) 226375608064910080 72057594037927936 Bool.false 253405 262144 18 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q3 15613505 131072 226375608064910080 72057594037927936 18 24780432077023986319360 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 253405 262144 24780432077023986319360 18889465931478580854784 704302240 536870912 68071 68004 (ep322 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep324 := nat_lit 34402502564856514270425165477120797283152573432130567998826007547084800000

noncomputable def ep325 := nat_lit 103086419291180055237982138206675355811805875528683117651584168126054400000

noncomputable def ep326 := BSN.cos_dyadic_bound_f 704302240 536870912 3 2 262144 68071 ep324 ep57 ep320 ep325 ep60 ep320 67121 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 704302240) qz268 0 2 ep324 ep57 ep320 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 704302240) qz269 0 2 ep325 ep60 ep320 rfl rfl rfl rfl) rfl rfl

noncomputable def ep327 := @Enclosure.Real.IsNear.sin_image qz115 qz344 Bool.false 15613505 131072 25 16384 Bool.true 67121 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz115 Bool.false 268237981368820765911 2251799813685248000 12933500001319294601 8500500000000000000000 15613505 131072 25 16384 (ep318 rfl) rfl) (Enclosure.sfrac_false_div 15613505 131072) (BSN.sin_reduce3 qz344 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24780432077023986319360) qz273) 226375608064910080 72057594037927936 Bool.false 67121 262144 18 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q3 15613505 131072 226375608064910080 72057594037927936 18 24780432077023986319360 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67121 262144 24780432077023986319360 18889465931478580854784 704302240 536870912 68071 68004 (ep326 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz345 := (@Enclosure.Real.IsNear.recentre' qz114 Bool.false 82897 262144 1 262144 82897 262144 1 262144 (ep316 rfl rfl) rfl)

noncomputable def ep328 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz114 (Real.cos qz115)) (@HMul.hMul Real Real Real qz0 qz114 (@Neg.neg Real Real.instNeg (Real.sin qz115))) Bool.false 21006514285 68719476736 578913304261 1168299823988736 Bool.false 5564129537 68719476736 575746289977 1168299823988736 (@Enclosure.Real.IsNear.mulLit_ff qz114 (Real.cos qz115) 82897 262144 1 262144 253405 262144 433217 278544384 21006514285 68719476736 578913304261 1168299823988736 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz115) Bool.false 253405 262144 866434 557088768 253405 262144 433217 278544384 (ep323 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz114 (@Neg.neg Real Real.instNeg (Real.sin qz115)) 82897 262144 1 262144 67121 262144 433217 278544384 5564129537 68719476736 575746289977 1168299823988736 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz115) Bool.true 67121 262144 433217 278544384 (@Enclosure.Real.IsNear.recentre' (Real.sin qz115) Bool.true 67121 262144 866434 557088768 67121 262144 433217 278544384 (ep327 rfl rfl) rfl)) rfl)

noncomputable def ep329 := @ep301 21006514285 68719476736 578913304261 1168299823988736 Bool.false 5564129537 68719476736 575746289977 1168299823988736 Bool.false 5087064876326106169344 148053073683 68719476736 2444723071757 389433274662912 Bool.true 819893067184875765760 5965507205 34359738368 1223405949811 194716637331456 (ep302 (BSN.head_sum_c_succ qz12 9 10 rfl rfl) (ep314 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep315 ep328) rfl rfl

noncomputable def ep330 := @Enclosure.Complex.IsNear.mul qz103 (@HAdd.hAdd Complex Complex Complex qz5 qz104 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))) Bool.true 6082398840716416248567 101166148420809575628800 ep294 ep161 Bool.false

noncomputable abbrev qz117 := (Complex.re qz335)

noncomputable abbrev qz118 := (Complex.im qz335)

noncomputable def ep331 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz117 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz104 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz118 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz104 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))))) 6172011067626253183 1011661484208095756288 12144068759701631220731

noncomputable def ep332 := nat_lit 51597770679065507857956864

noncomputable def ep333 := nat_lit 469070642536959162345062400

noncomputable def ep334 := nat_lit 6153328638744770671991141180410561661239296

noncomputable def ep335 := @Enclosure.Real.IsNear.mulLit_tf qz117 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz104 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))))) 208900077 17179869184 137010820363 292074955997184 88635837137

noncomputable abbrev qz119 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

noncomputable abbrev qz346 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz420 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable abbrev qz120 := (Real.cos qz346)

noncomputable abbrev qz121 := (@Neg.neg Real Real.instNeg (Real.sin qz346))

noncomputable def ep336 := @Enclosure.Complex.IsNear.of_eq qz103 (Complex.mk (@HMul.hMul Real Real Real qz0 qz119 qz120) (@HMul.hMul Real Real Real qz0 qz119 qz121)) Bool.true 208900077 17179869184 137010820363 292074955997184 Bool.false 10351342635 34359738368 276158309405 584149911994368 (BSN.cpow_neg_s_mk qz20 51734 1000 11 qz21 rfl)

noncomputable abbrev qz122 := (@HDiv.hDiv Real Real Real qz256 (@Nat.cast Real Real.instNatCast 11) (@Nat.cast Real Real.instNatCast 1))

noncomputable def ep337 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) 869433 262144 1 262144 39519 39520 131072 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) (Real.sqrt qz122) Bool.false 869433 262144 1 262144 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz122) Bool.false 869433 262144 1 262144 869433 262144 1 262144 (BSN.sqrt_enclosure 11 1 434716 434717 131072 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep338 := BSN.log_dyadic_bound 3 19 3 2 1954815 131072 34002 16488 243 41740 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 19) 0 2 16488 1954815 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz347 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz123 := qz347

noncomputable def ep339 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz123 51734 1000 0 1 10799147631728357 4503599627370496 500000000051003 17001000000000000000 279341551789917410519 2251799813685248000 12933500001319294601 8500500000000000000000 qz25 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 500000000051003 17001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz122) Bool.false 11323727027087193669632 4722366482869645213696 1000000000102006 34002000000000000000 10799147631728357 4503599627370496 500000000051003 17001000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 41740 131072 24973259072661432 36028797018963968 34002 1000000000000000 rfl rfl rfl rfl (ep338 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep340 := nat_lit 63821095259460165875020912777042244907225308373735265798523531694437376256

noncomputable def ep341 := nat_lit 207739487192423230292277722859917619651021578283524626462054462277099776

noncomputable def ep342 := nat_lit 191047806803995651164478182885406899482373881964638748142646486158757929216

noncomputable def ep343 := BSN.cos_dyadic_bound_f 821655718 536870912 3 2 262144 68071 ep340 ep57 ep341 ep342 ep60 ep341 10572 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 821655718) qz268 0 2 ep340 ep57 ep341 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 821655718) qz269 0 2 ep342 ep60 ep341 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz124 := qz346

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8129909) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz349 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep344 := @Enclosure.Real.IsNear.cos_image qz124 qz348 Bool.false 8129909 65536 25 16384 Bool.true 10572 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 279341551789917410519 2251799813685248000 12933500001319294601 8500500000000000000000 8129909 65536 25 16384 (ep339 rfl) rfl) (Enclosure.sfrac_false_div 8129909 65536) (BSN.cos_reduce2 qz348 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14454720263521470251008) qz349) 226375608064910080 72057594037927936 Bool.false 10572 262144 19 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q2 8129909 65536 226375608064910080 72057594037927936 19 14454720263521470251008 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 10572 262144 14454720263521470251008 9444732965739290427392 821655718 536870912 68071 68004 (ep343 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep345 := nat_lit 114711779877274359990803820820388106737284737810096658736172713480165597440

noncomputable def ep346 := nat_lit 300099273842168924269727271549719460546786945042556018723323304271032688896

noncomputable def ep347 := BSN.sin_dyadic_bound_f 821655718 536870912 3 2 262144 68071 ep345 ep64 ep341 ep346 ep66 ep341 261930 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 821655718) qz274 0 2 ep345 ep64 ep341 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 821655718) qz275 0 2 ep346 ep66 ep341 rfl rfl rfl rfl) rfl rfl

noncomputable def ep348 := @Enclosure.Real.IsNear.sin_image qz124 qz348 Bool.false 8129909 65536 25 16384 Bool.true 261930 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 279341551789917410519 2251799813685248000 12933500001319294601 8500500000000000000000 8129909 65536 25 16384 (ep339 rfl) rfl) (Enclosure.sfrac_false_div 8129909 65536) (BSN.sin_reduce2 qz348 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14454720263521470251008) qz349) 226375608064910080 72057594037927936 Bool.false 261930 262144 19 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q2 8129909 65536 226375608064910080 72057594037927936 19 14454720263521470251008 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 261930 262144 14454720263521470251008 9444732965739290427392 821655718 536870912 68071 68004 (ep347 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz125 := (Real.sin qz346)

noncomputable abbrev qz350 := (@Enclosure.Real.IsNear.recentre' qz119 Bool.false 79039 262144 1 262144 79039 262144 1 262144 (ep337 rfl rfl) rfl)

noncomputable def ep349 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz119 qz120) (@HMul.hMul Real Real Real qz0 qz119 qz121) Bool.true 208900077 17179869184 137010820363 292074955997184 Bool.false 10351342635 34359738368 276158309405 584149911994368 (@Enclosure.Real.IsNear.mulLit_ft qz119 qz120 79039 262144 1 262144 2643 65536 433217 278544384 208900077 17179869184 137010820363 292074955997184 qz350 (@Enclosure.Real.IsNear.recentre' qz120 Bool.true 10572 262144 866434 557088768 2643 65536 433217 278544384 (ep344 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz119 qz121 79039 262144 1 262144 130965 131072 433217 278544384 10351342635 34359738368 276158309405 584149911994368 qz350 (@Enclosure.Real.IsNear.neg qz125 Bool.true 130965 131072 433217 278544384 (@Enclosure.Real.IsNear.recentre' qz125 Bool.true 261930 262144 866434 557088768 130965 131072 433217 278544384 (ep348 rfl rfl) rfl)) rfl)

noncomputable def ep350 := @ep335 176659345896 0 1 6172011067626253183 1011661484208095756288 12144068759701631220731 ep332 (@Enclosure.Complex.IsNear.re_isNear qz103 Bool.true 208900077 17179869184 137010820363 292074955997184 Bool.false 10351342635 34359738368 276158309405 584149911994368 (ep336 ep349))

noncomputable def ep351 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz104 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))) Bool.false 88635837137 176659345896 0 1 Bool.false

noncomputable def ep352 := @Enclosure.Complex.IsNear.addLitP qz104 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) Bool.false 666414189 1338328378 0 1 Bool.true 142268500

noncomputable def ep353 := @ep352 669164189 0 1 Bool.false 1 264 0 1 Bool.false 25867 66000 0 1 Bool.false 177271674274 88635837137 176659345896 0 1 Bool.false 7919549076863 7919549076863 44164836474000 0 1

noncomputable abbrev qz126 := (@HDiv.hDiv Complex Complex Complex qz309 qz336 (@HSub.hSub Complex Complex Complex qz302 qz258 (1 : Complex)))

noncomputable def ep354 := @Enclosure.Complex.IsNear.addLitP qz126 qz78 Bool.true 22000000 10706627024 0 1 Bool.true 2276296000 10706627024 0 1

noncomputable def ep355 := @Enclosure.Complex.IsNear.of_eq qz126 (Complex.mk (Enclosure.sfrac Bool.true 22000000 10706627024) (Enclosure.sfrac Bool.true 2276296000 10706627024)) Bool.true 22000000 10706627024 0 1 Bool.true 2276296000 10706627024 0 1

noncomputable def ep356 := @ep354 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 10662627024 666414189 1338328378 0 1 Bool.true 2276296000 142268500 669164189 0 1 (ep355 (BSN.N_div_s_sub_one_mk qz20 51734 1000 11 qz21 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 22000000 10706627024) (Enclosure.sfrac Bool.true 2276296000 10706627024) Bool.true 22000000 10706627024 0 1 Bool.true 2276296000 10706627024 0 1 (Enclosure.Real.IsNear.const Bool.true 22000000 10706627024) (Enclosure.Real.IsNear.const Bool.true 2276296000 10706627024))) qz79 rfl

noncomputable abbrev qz127 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz351 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz428 qz429 1))

noncomputable abbrev qz128 := qz351

noncomputable def ep357 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz128)) Bool.false 1 264 0 1

noncomputable def ep358 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz128) Bool.false 0 1 0 1 Bool.false

noncomputable def ep359 := @ep358 0 1 0 1 Bool.false 1 264 0 1 Bool.false 25867 66000 0 1 Bool.false 1 1 264 0 1 Bool.false 25867 25867 66000 0

noncomputable def ep360 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (Complex.mk qz17 qz17) Bool.false 0 1 0 1 Bool.false

noncomputable def ep361 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz128 Bool.false 1 264 0 1 Bool.false 25867 66000 0 1

noncomputable abbrev qz129 := (Complex.re qz351)

noncomputable abbrev qz130 := (Complex.im qz351)

noncomputable def ep362 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz130) 1 264 0 1 0 1 0

noncomputable def ep363 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129 1 24 0 1 1 11 0 1 1

noncomputable def ep364 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep365 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep366 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz17) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow11.d7 rfl) qz326

noncomputable def ep367 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz12 Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 (BSN.ascPochhammer_one_eval qz12)

noncomputable def ep368 := ep367 (@Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk qz73 qz20) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 (BSN.s_crit_mk qz20 Bool.false 51734 1000 qz21) (@Enclosure.Complex.IsNear.mk qz73 qz20 Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 qz318 qz25))

noncomputable def ep369 := @ep365 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep366) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep368)

noncomputable def ep370 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 51734 1000 0 1 0 1 0

noncomputable def ep371 := @ep370 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep366) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep368)

noncomputable def ep372 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) 25867 6000 0 1 0 1 0 1 25867

noncomputable def ep373 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 51734 1000 0 1 25867 6000 0

noncomputable def ep374 := @ep373 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep366) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep368)

noncomputable def ep375 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep376 := @ep375 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep366) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep368)

noncomputable def ep377 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 25867 6000 0 1 (@ep364 1 24 0 1 (ep369 rfl) (ep371 rfl) rfl rfl) (@ep372 25867 6000 0 1 (ep374 rfl) (ep376 rfl) rfl rfl)

noncomputable def ep378 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 25867 6000 0 1 ep377

noncomputable abbrev qz131 := (@Enclosure.Complex.IsNear.re_isNear qz351 Bool.false 1 11 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz351 (Complex.mk (Enclosure.sfrac Bool.false 1 11) qz264) Bool.false 1 11 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 11 1 11 EMRow11.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 11) qz264 Bool.false 1 11 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 11) qz277)))

noncomputable def ep379 := @ep363 264 0 1 ep378 qz131

noncomputable def ep380 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz130 25867 6000 0 1 0 1 0 1 0

noncomputable def ep381 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 25867 6000 0 1 ep377

noncomputable abbrev qz132 := (@Enclosure.Complex.IsNear.im_isNear qz351 Bool.false 1 11 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz351 (Complex.mk (Enclosure.sfrac Bool.false 1 11) qz264) Bool.false 1 11 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 11 1 11 EMRow11.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 11) qz264 Bool.false 1 11 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 11) qz277)))

noncomputable def ep382 := @ep380 1 0 1 ep381 qz132

noncomputable def ep383 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz130) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129) 0 1 0 1 25867 66000 0

noncomputable def ep384 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz130 1 24 0 1 0 1 0 1 0

noncomputable def ep385 := @ep384 1 0 1 ep378 qz132

noncomputable def ep386 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129 25867 6000 0 1 1 11 0 1 25867

noncomputable def ep387 := @ep386 66000 0 1 ep381 qz131

noncomputable def ep388 := @ep359 1 (@ep360 0 1 0 1 (BSN.bern_sum_base qz12 11) qz95) (ep361 (@ep362 1 1 1 264 0 1 (ep379 rfl) (ep382 rfl) rfl rfl) (@ep383 1 25867 25867 66000 0 1 (ep385 rfl) (ep387 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep389 := ep353 (ep356 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep357 Bool.false 25867 66000 0 1 (BSN.bern_sum_succ qz12 11 0 1 1 rfl rfl) (ep388 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep390 := @Enclosure.Real.IsNear.mulLit_ff qz118 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz104 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))))) 10351342635 34359738368 276158309405 584149911994368 7919549076863

noncomputable def ep391 := @ep390 44164836474000 0 1 5465197733953790930267 101166148420809575628800 39764532442116626923573 ep333 (@Enclosure.Complex.IsNear.im_isNear qz103 Bool.true 208900077 17179869184 137010820363 292074955997184 Bool.false 10351342635 34359738368 276158309405 584149911994368 (ep336 ep349))

noncomputable def ep392 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz104 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))) Bool.false 88635837137 176659345896 0 1 Bool.false

noncomputable def ep393 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz117 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz104 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz118 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz104 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))))) 551464803987319872817 252915371052023939072000 1085063915926038972561269

noncomputable def ep394 := nat_lit 12899442669766376964489216000

noncomputable def ep395 := nat_lit 9381412850739183246901248

noncomputable def ep396 := nat_lit 76234152826862144287013365313833176722833408

noncomputable def ep397 := @Enclosure.Real.IsNear.mulLit_tf qz117 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz104 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))))) 208900077 17179869184 137010820363 292074955997184 7919549076863

noncomputable def ep398 := @ep397 44164836474000 0 1 551464803987319872817 252915371052023939072000 1085063915926038972561269 ep394 (@Enclosure.Complex.IsNear.re_isNear qz103 Bool.true 208900077 17179869184 137010820363 292074955997184 Bool.false 10351342635 34359738368 276158309405 584149911994368 (ep336 ep349))

noncomputable def ep399 := @Enclosure.Real.IsNear.mulLit_ff qz118 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz104 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))))) 10351342635 34359738368 276158309405 584149911994368 88635837137

noncomputable def ep400 := @ep399 176659345896 0 1 305833306648381478665 2023322968416191512576 2225229357859166852135 ep395 (@Enclosure.Complex.IsNear.im_isNear qz103 Bool.true 208900077 17179869184 137010820363 292074955997184 Bool.false 10351342635 34359738368 276158309405 584149911994368 (ep336 ep349))

noncomputable abbrev qz352 := (ep389 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep401 := @ep330 856311330160462840007 5748076614818725888000 ep295 ep291 (@ep331 ep332 5465197733953790930267 101166148420809575628800 39764532442116626923573 ep333 ep334 6082398840716416248567 101166148420809575628800 ep294 ep161 (ep350 (@ep351 7919549076863 44164836474000 0 1 qz352) rfl) (ep391 (@ep392 7919549076863 44164836474000 0 1 qz352) rfl) rfl rfl) (@ep393 ep394 305833306648381478665 2023322968416191512576 2225229357859166852135 ep395 ep396 856311330160462840007 5748076614818725888000 ep295 ep291 (ep398 (@ep392 7919549076863 44164836474000 0 1 qz352) rfl) (ep400 (@ep351 7919549076863 44164836474000 0 1 qz352) rfl) rfl rfl)

noncomputable def ep402 := @ep298 ep290 ep291 (@ep299 194716637331456 (BSN.head_sum_c_eq qz12 11) (ep300 (BSN.head_sum_c_succ qz12 10 11 rfl rfl) (ep329 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep401 rfl rfl rfl

noncomputable def ep403 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz12 1 11) Bool.false 211875594115375847542833 101166148420809575628800 ep160 ep161 Bool.true 141664617541407596243 5748076614818725888000 ep290 ep291 (@ep292 ep161 Bool.true 141664617541407596243 5748076614818725888000 ep290 ep291 (BSN.zetaApproximant_eq_folded' qz12 1 11 rfl) (ep402 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep404 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))))) qz53)) (Complex.im (zetaApproximant qz12 1 11)) 37 262144 3004241

noncomputable def ep405 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))))) qz53)) Bool.true 37 262144 6008482

noncomputable def ep406 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))))) qz53) qz305 Bool.false 463249 16384 169

noncomputable def ep407 := BSN.sin_dyadic_bound_f 75814 536870912 1 0 262144 68071 0 1 1 0 1 1 37 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 75814) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 75814) qz275 0 0 rfl) rfl rfl

noncomputable def ep408 := @ep406 262144 Bool.true 37 262144 1 34002 (@ep165 463249 16384 169 262144 ep287 rfl) (Enclosure.sfrac_false_div 463249 16384) (BSN.sin_reduce2 qz305 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 333435313395335168) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 37 262144 4 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q2 463249 16384 226375608064910080 72057594037927936 4 333435313395335168 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 37 262144 333435313395335168 2361183241434822606848 75814 536870912 68071 68004 (ep407 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep409 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz12 1 11) Bool.false 211875594115375847542833 101166148420809575628800 ep160 ep161 Bool.true 141664617541407596243 5748076614818725888000 ep290 ep291 (@ep292 ep161 Bool.true 141664617541407596243 5748076614818725888000 ep290 ep291 (BSN.zetaApproximant_eq_folded' qz12 1 11 rfl) (ep402 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow11.d9 : Enclosure.Real.IsNear (hardyZApproximantEM 1 11 qz20) Bool.true ep144 ep145 ep146 ep147 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 11 qz20) ep148 Bool.true ep144 ep145 ep146 ep147 (@Eq.refl Real ep148) (@ep149 Bool.true ep144 ep145 ep146 ep147 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz51 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz52 (@Nat.cast Complex Complex.instNatCast j))))) qz53) (zetaApproximant qz12 1 11)) (@ep151 ep152 ep153 ep154 5241590849032081060991 ep155 ep156 ep157 ep158 ep144 ep145 ep146 ep147 (@ep159 4456710144 211875594115375847542833 101166148420809575628800 ep160 ep161 ep150 ep152 ep153 ep154 (@ep162 8913420288 262143 262144 3004241 4456710144 (ep289 rfl rfl) rfl) ep403 rfl) (@ep404 4456710144 141664617541407596243 5748076614818725888000 ep290 ep291 5241590849032081060991 ep155 ep156 ep157 (@ep405 8913420288 37 262144 3004241 4456710144 (ep408 rfl rfl) rfl) ep409 rfl) rfl rfl))

noncomputable abbrev qz444 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 54675 1000)))

noncomputable abbrev qz430 := qz444

noncomputable abbrev qz353 := qz430

noncomputable abbrev qz133 := (BSN.headSumC qz353 9)

noncomputable abbrev qz134 := qz353

noncomputable abbrev qz431 := (@Neg.neg Complex Complex.instNeg qz444)

noncomputable abbrev qz354 := qz431

noncomputable abbrev qz135 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 8) qz354)

noncomputable def ep410 := @Enclosure.Complex.IsNear.of_eq qz133 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz134 8) qz135) Bool.false 162115029093 68719476736 2167103295023 389433274662912 Bool.false 2986270211 68719476736 2159292672935 389433274662912

noncomputable def ep411 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz134 8) qz135 Bool.false 142009800879 68719476736 5816831527319 1168299823988736 Bool.false 16627114289 68719476736 5795771232551 1168299823988736 Bool.false

noncomputable abbrev qz136 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 7) qz354)

noncomputable def ep412 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz134 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz134 7) qz136) Bool.false 142009800879 68719476736 5816831527319 1168299823988736 Bool.false 16627114289 68719476736 5795771232551 1168299823988736

noncomputable def ep413 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz134 7) qz136 Bool.false 29578521081 17179869184 282624344643 64905545777152 Bool.false 5990768939 68719476736 563157636179 129811091554304 Bool.false

noncomputable abbrev qz137 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 6) qz354)

noncomputable def ep414 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz134 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz134 6) qz137) Bool.false 29578521081 17179869184 282624344643 64905545777152 Bool.false 5990768939 68719476736 563157636179 129811091554304

noncomputable def ep415 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz134 6) qz137 Bool.false 8866054939 4294967296 89539785307 24339579666432 Bool.true 9266858421 68719476736 1427240849869 389433274662912 Bool.true

noncomputable abbrev qz138 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 5) qz354)

noncomputable def ep416 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz134 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz134 5) qz138) Bool.false 8866054939 4294967296 89539785307 24339579666432 Bool.true 9266858421 68719476736 1427240849869 389433274662912

noncomputable def ep417 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz134 5) qz138 Bool.false 111139550499 68719476736 3436988283137 1168299823988736 Bool.true 4152238153 34359738368 1712558046907 584149911994368 Bool.false

noncomputable abbrev qz139 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 4) qz354)

noncomputable def ep418 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz134 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz134 4) qz139) Bool.false 111139550499 68719476736 3436988283137 1168299823988736 Bool.true 4152238153 34359738368 1712558046907 584149911994368

noncomputable def ep419 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz134 4) qz139 Bool.false 19863972185 17179869184 309416617355 146037477998592 Bool.false 77953229 1073741824 308230763603 146037477998592 Bool.false

noncomputable abbrev qz140 := (@HPow.hPow Complex Complex Complex qz260 qz262 qz354)

noncomputable def ep420 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz134 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz134 3) qz140) Bool.false 19863972185 17179869184 309416617355 146037477998592 Bool.false 77953229 1073741824 308230763603 146037477998592

noncomputable def ep421 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz134 3) qz140 Bool.false 29088996433 17179869184 681464170391 584149911994368 Bool.true 2397080907 17179869184 677974511129 584149911994368 Bool.true

noncomputable abbrev qz141 := (@HPow.hPow Complex Complex Complex qz260 qz263 qz354)

noncomputable def ep422 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz134 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz134 2) qz141) Bool.false 29088996433 17179869184 681464170391 584149911994368 Bool.true 2397080907 17179869184 677974511129 584149911994368

noncomputable def ep423 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz134 2) qz141 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep424 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz134 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz17) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz134)

noncomputable abbrev qz445 := (Enclosure.sfrac Bool.false 54675 1000)

noncomputable abbrev qz432 := qz445

noncomputable abbrev qz355 := qz432

noncomputable abbrev qz142 := (@HMul.hMul Real Real Real qz253 qz355 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz143 := qz355

noncomputable abbrev qz356 := (@Eq.refl Real qz432)

noncomputable abbrev qz144 := qz356

noncomputable def ep425 := @Enclosure.Complex.IsNear.of_eq qz141 (Complex.mk (@HMul.hMul Real Real Real qz0 qz18 (Real.cos qz142)) (@HMul.hMul Real Real Real qz0 qz18 (@Neg.neg Real Real.instNeg (Real.sin qz142)))) Bool.false 11909127249 17179869184 681464170391 584149911994368 Bool.true 2397080907 17179869184 677974511129 584149911994368 (BSN.cpow_neg_s_mk qz143 54675 1000 2 qz144 rfl)

noncomputable def ep426 := nat_lit 129321564726639444951085737540241

noncomputable def ep427 := BSN.cos_dyadic_bound_f 106639411 536870912 2 1 262144 68071 ep426 ep75 ep426 ep426 ep76 ep426 256989 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 106639411) qz268 0 1 ep426 ep75 ep426 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 106639411) qz269 0 1 ep426 ep76 ep426 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz357 := (Enclosure.Real.IsNear.const Bool.false 54675 1000)

noncomputable abbrev qz145 := qz357

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4967333) qz23)

noncomputable abbrev qz359 := (@Nat.cast Real Real.instNatCast 3752040723591920091136)

noncomputable def ep428 := @Enclosure.Real.IsNear.cos_image qz142 qz358 Bool.false 4967333 131072 211 131072 Bool.false 256989 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 49673331 1310720 243 151120 4967333 131072 211 131072 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz24 54675 1000 0 1 90852 131072 1 34002 49673331 1310720 243 151120 qz145 qz272 rfl) rfl) (Enclosure.sfrac_false_div 4967333 131072) (BSN.cos_reduce0 qz358 (@HDiv.hDiv Real Real Real qz2 qz359 qz273) 226375608064910080 72057594037927936 Bool.false 256989 262144 6 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 4967333 131072 226375608064910080 72057594037927936 6 3752040723591920091136 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 256989 262144 3752040723591920091136 18889465931478580854784 106639411 536870912 68071 68004 (ep427 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep429 := BSN.sin_dyadic_bound_f 106639411 536870912 1 0 262144 68071 0 1 1 0 1 1 51727 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 106639411) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 106639411) qz275 0 0 rfl) rfl rfl

noncomputable def ep430 := @Enclosure.Real.IsNear.sin_image qz142 qz358 Bool.false 4967333 131072 211 131072 Bool.false 51727 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 49673331 1310720 243 151120 4967333 131072 211 131072 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz24 54675 1000 0 1 90852 131072 1 34002 49673331 1310720 243 151120 qz145 qz272 rfl) rfl) (Enclosure.sfrac_false_div 4967333 131072) (BSN.sin_reduce0 qz358 (@HDiv.hDiv Real Real Real qz2 qz359 qz273) 226375608064910080 72057594037927936 Bool.false 51727 262144 6 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 4967333 131072 226375608064910080 72057594037927936 6 3752040723591920091136 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 51727 262144 3752040723591920091136 18889465931478580854784 106639411 536870912 68071 68004 (ep429 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep431 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz18 (Real.cos qz142)) (@HMul.hMul Real Real Real qz0 qz18 (@Neg.neg Real Real.instNeg (Real.sin qz142))) Bool.false 11909127249 17179869184 681464170391 584149911994368 Bool.true 2397080907 17179869184 677974511129 584149911994368 (@Enclosure.Real.IsNear.mulLit_ff qz18 (Real.cos qz142) 46341 65536 1 131072 256989 262144 3652747 2228355072 11909127249 17179869184 681464170391 584149911994368 qz276 (@Enclosure.Real.IsNear.recentre' (Real.cos qz142) Bool.false 256989 262144 7305494 4456710144 256989 262144 3652747 2228355072 (ep428 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz18 (@Neg.neg Real Real.instNeg (Real.sin qz142)) 46341 65536 1 131072 51727 262144 3652747 2228355072 2397080907 17179869184 677974511129 584149911994368 qz276 (@Enclosure.Real.IsNear.neg (Real.sin qz142) Bool.false 51727 262144 3652747 2228355072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz142) Bool.false 51727 262144 7305494 4456710144 51727 262144 3652747 2228355072 (ep430 rfl rfl) rfl)) rfl)

noncomputable def ep432 := @ep423 11909127249 17179869184 681464170391 584149911994368 Bool.true 2397080907 17179869184 677974511129 584149911994368 Bool.false 29088996433 29088996433 17179869184 681464170391 584149911994368 Bool.true 2397080907 2397080907 17179869184 677974511129 584149911994368 (ep424 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz17 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz26)) (ep425 ep431) rfl rfl

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz253 qz355 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep433 := @Enclosure.Complex.IsNear.of_eq qz140 (Complex.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz146)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz146)))) Bool.true 1153128031 2147483648 185400766343 194716637331456 Bool.false 3644332571 17179869184 184982847761 194716637331456 (BSN.cpow_neg_s_mk qz143 54675 1000 3 qz144 rfl)

noncomputable def ep434 := nat_lit 1664599131716786073114254774978161

noncomputable def ep435 := BSN.cos_dyadic_bound_f 201988859 536870912 2 1 262144 68071 ep434 ep75 ep434 ep434 ep76 ep434 243808 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 201988859) qz268 0 1 ep434 ep75 ep434 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 201988859) qz269 0 1 ep434 ep76 ep434 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz360 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15746071) qz30)

noncomputable def ep436 := @Enclosure.Real.IsNear.cos_image qz146 qz360 Bool.false 15746071 262144 423 262144 Bool.true 243808 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 314921439 5242880 243 151120 15746071 262144 423 262144 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz31 54675 1000 0 1 143997 131072 1 34002 314921439 5242880 243 151120 qz145 qz279 rfl) rfl) (Enclosure.sfrac_false_div 15746071 262144) (BSN.cos_reduce2 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14213702399204001841152) qz32) 226375608064910080 72057594037927936 Bool.false 243808 262144 9 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q2 15746071 262144 226375608064910080 72057594037927936 9 14213702399204001841152 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 243808 262144 14213702399204001841152 37778931862957161709568 201988859 536870912 68071 68004 (ep435 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep437 := BSN.sin_dyadic_bound_f 201988859 536870912 2 1 262144 68071 ep434 ep79 ep434 ep434 ep80 ep434 96316 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 201988859) qz274 0 1 ep434 ep79 ep434 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 201988859) qz275 0 1 ep434 ep80 ep434 rfl rfl rfl rfl) rfl rfl

noncomputable def ep438 := @Enclosure.Real.IsNear.sin_image qz146 qz360 Bool.false 15746071 262144 423 262144 Bool.true 96316 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 314921439 5242880 243 151120 15746071 262144 423 262144 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz31 54675 1000 0 1 143997 131072 1 34002 314921439 5242880 243 151120 qz145 qz279 rfl) rfl) (Enclosure.sfrac_false_div 15746071 262144) (BSN.sin_reduce2 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14213702399204001841152) qz32) 226375608064910080 72057594037927936 Bool.false 96316 262144 9 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q2 15746071 262144 226375608064910080 72057594037927936 9 14213702399204001841152 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 96316 262144 14213702399204001841152 37778931862957161709568 201988859 536870912 68071 68004 (ep437 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep439 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz146)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz146))) Bool.true 1153128031 2147483648 185400766343 194716637331456 Bool.false 3644332571 17179869184 184982847761 194716637331456 (@Enclosure.Real.IsNear.mulLit_ft qz27 (Real.cos qz146) 151349 262144 1 262144 7619 8192 7322495 4456710144 1153128031 2147483648 185400766343 194716637331456 qz280 (@Enclosure.Real.IsNear.recentre' (Real.cos qz146) Bool.true 243808 262144 14644990 8913420288 7619 8192 7322495 4456710144 (ep436 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz27 (@Neg.neg Real Real.instNeg (Real.sin qz146)) 151349 262144 1 262144 24079 65536 7322495 4456710144 3644332571 17179869184 184982847761 194716637331456 qz280 (@Enclosure.Real.IsNear.neg (Real.sin qz146) Bool.true 24079 65536 7322495 4456710144 (@Enclosure.Real.IsNear.recentre' (Real.sin qz146) Bool.true 96316 262144 14644990 8913420288 24079 65536 7322495 4456710144 (ep438 rfl rfl) rfl)) rfl)

noncomputable def ep440 := @ep421 1153128031 2147483648 185400766343 194716637331456 Bool.false 3644332571 17179869184 184982847761 194716637331456 Bool.false 42657555451614330880 19863972185 17179869184 309416617355 146037477998592 Bool.false 21427620427046322176 77953229 1073741824 308230763603 146037477998592 (ep422 (BSN.head_sum_c_succ qz134 2 3 rfl rfl) (ep432 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep433 ep439) rfl rfl

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz253 qz355 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep441 := @Enclosure.Complex.IsNear.of_eq qz139 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz147)))) Bool.false 31683661759 68719476736 961655344297 1168299823988736 Bool.true 6646741481 34359738368 479634992495 584149911994368 (BSN.cpow_neg_s_mk qz143 54675 1000 4 qz144 rfl)

noncomputable def ep442 := nat_lit 2069145035626231119217371800643856

noncomputable def ep443 := BSN.cos_dyadic_bound_f 213278822 536870912 2 1 262144 68071 ep442 ep75 ep442 ep442 ep76 ep442 241729 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 213278822) qz268 0 1 ep442 ep75 ep442 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 213278822) qz269 0 1 ep442 ep76 ep442 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz361 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4967333) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep444 := @Enclosure.Real.IsNear.cos_image qz147 qz361 Bool.false 4967333 65536 211 131072 Bool.false 241729 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 49673331 655360 243 151120 4967333 65536 211 131072 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz35 54675 1000 0 1 181704 131072 1 34002 49673331 655360 243 151120 qz145 qz283 rfl) rfl) (Enclosure.sfrac_false_div 4967333 65536) (BSN.cos_reduce0 qz361 (@HDiv.hDiv Real Real Real qz2 qz359 qz349) 226375608064910080 72057594037927936 Bool.false 241729 262144 12 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 4967333 65536 226375608064910080 72057594037927936 12 3752040723591920091136 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 241729 262144 3752040723591920091136 9444732965739290427392 213278822 536870912 68071 68004 (ep443 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep445 := BSN.sin_dyadic_bound_f 213278822 536870912 2 1 262144 68071 ep442 ep79 ep442 ep442 ep80 ep442 101422 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 213278822) qz274 0 1 ep442 ep79 ep442 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 213278822) qz275 0 1 ep442 ep80 ep442 rfl rfl rfl rfl) rfl rfl

noncomputable def ep446 := @Enclosure.Real.IsNear.sin_image qz147 qz361 Bool.false 4967333 65536 211 131072 Bool.false 101422 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 49673331 655360 243 151120 4967333 65536 211 131072 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz35 54675 1000 0 1 181704 131072 1 34002 49673331 655360 243 151120 qz145 qz283 rfl) rfl) (Enclosure.sfrac_false_div 4967333 65536) (BSN.sin_reduce0 qz361 (@HDiv.hDiv Real Real Real qz2 qz359 qz349) 226375608064910080 72057594037927936 Bool.false 101422 262144 12 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 4967333 65536 226375608064910080 72057594037927936 12 3752040723591920091136 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 101422 262144 3752040723591920091136 9444732965739290427392 213278822 536870912 68071 68004 (ep445 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep447 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz147))) Bool.false 31683661759 68719476736 961655344297 1168299823988736 Bool.true 6646741481 34359738368 479634992495 584149911994368 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz147) 131071 262144 1 262144 241729 262144 3652747 2228355072 31683661759 68719476736 961655344297 1168299823988736 qz284 (@Enclosure.Real.IsNear.recentre' (Real.cos qz147) Bool.false 241729 262144 7305494 4456710144 241729 262144 3652747 2228355072 (ep444 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz33 (@Neg.neg Real Real.instNeg (Real.sin qz147)) 131071 262144 1 262144 50711 131072 3652747 2228355072 6646741481 34359738368 479634992495 584149911994368 qz284 (@Enclosure.Real.IsNear.neg (Real.sin qz147) Bool.false 50711 131072 3652747 2228355072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz147) Bool.false 101422 262144 7305494 4456710144 50711 131072 3652747 2228355072 (ep446 rfl rfl) rfl)) rfl)

noncomputable def ep448 := @ep419 31683661759 68719476736 961655344297 1168299823988736 Bool.true 6646741481 34359738368 479634992495 584149911994368 Bool.false 1909362938741381922816 111139550499 68719476736 3436988283137 1168299823988736 Bool.true 4458431768084611072 4152238153 34359738368 1712558046907 584149911994368 (ep420 (BSN.head_sum_c_succ qz134 3 4 rfl rfl) (ep440 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep441 ep447) rfl rfl

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz253 qz355 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep449 := @Enclosure.Complex.IsNear.of_eq qz138 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz148)))) Bool.false 30717328525 68719476736 860921411599 1168299823988736 Bool.true 962382115 68719476736 856606455793 1168299823988736 (BSN.cpow_neg_s_mk qz143 54675 1000 5 qz144 rfl)

noncomputable def ep450 := BSN.cos_dyadic_bound_f 16814882 536870912 1 0 262144 68071 0 1 1 0 1 1 262015 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 16814882) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 16814882) qz269 0 0 rfl) rfl rfl

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 23067601) qz30)

noncomputable def ep451 := @Enclosure.Real.IsNear.cos_image qz148 qz362 Bool.false 23067601 262144 211 131072 Bool.false 262015 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 57669003 655360 243 151120 23067601 262144 211 131072 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz38 54675 1000 0 1 210952 131072 1 34002 57669003 655360 243 151120 qz145 qz287 rfl) rfl) (Enclosure.sfrac_false_div 23067601 262144) (BSN.cos_reduce0 qz362 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1183242142004860157952) qz32) 226375608064910080 72057594037927936 Bool.false 262015 262144 14 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 23067601 262144 226375608064910080 72057594037927936 14 1183242142004860157952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 262015 262144 1183242142004860157952 37778931862957161709568 16814882 536870912 68071 68004 (ep450 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep452 := BSN.sin_dyadic_bound_f 16814882 536870912 1 0 262144 68071 0 1 1 0 1 1 8209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 16814882) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 16814882) qz275 0 0 rfl) rfl rfl

noncomputable def ep453 := @Enclosure.Real.IsNear.sin_image qz148 qz362 Bool.false 23067601 262144 211 131072 Bool.false 8209 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 57669003 655360 243 151120 23067601 262144 211 131072 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz38 54675 1000 0 1 210952 131072 1 34002 57669003 655360 243 151120 qz145 qz287 rfl) rfl) (Enclosure.sfrac_false_div 23067601 262144) (BSN.sin_reduce0 qz362 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1183242142004860157952) qz32) 226375608064910080 72057594037927936 Bool.false 8209 262144 14 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 23067601 262144 226375608064910080 72057594037927936 14 1183242142004860157952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8209 262144 1183242142004860157952 37778931862957161709568 16814882 536870912 68071 68004 (ep452 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep454 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz148))) Bool.false 30717328525 68719476736 860921411599 1168299823988736 Bool.true 962382115 68719476736 856606455793 1168299823988736 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz148) 117235 262144 1 262144 262015 262144 3652747 2228355072 30717328525 68719476736 860921411599 1168299823988736 qz288 (@Enclosure.Real.IsNear.recentre' (Real.cos qz148) Bool.false 262015 262144 7305494 4456710144 262015 262144 3652747 2228355072 (ep451 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz148)) 117235 262144 1 262144 8209 262144 3652747 2228355072 962382115 68719476736 856606455793 1168299823988736 qz288 (@Enclosure.Real.IsNear.neg (Real.sin qz148) Bool.false 8209 262144 3652747 2228355072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz148) Bool.false 8209 262144 7305494 4456710144 8209 262144 3652747 2228355072 (ep453 rfl rfl) rfl)) rfl)

noncomputable def ep455 := @ep417 30717328525 68719476736 860921411599 1168299823988736 Bool.true 962382115 68719476736 856606455793 1168299823988736 Bool.false 9748330497931334385664 8866054939 4294967296 89539785307 24339579666432 Bool.true 318406830838857596928 9266858421 68719476736 1427240849869 389433274662912 (ep418 (BSN.head_sum_c_succ qz134 4 5 rfl rfl) (ep448 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep449 ep454) rfl rfl

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz253 qz355 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep456 := @Enclosure.Complex.IsNear.of_eq qz137 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.true 5885698675 17179869184 131554751473 194716637331456 Bool.false 476800855 2147483648 65558014667 97358318665728 (BSN.cpow_neg_s_mk qz143 54675 1000 6 qz144 rfl)

noncomputable def ep457 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz41 54675 1000 0 1 4034681531866359 2251799813685248 250000000017001 8500500000000000000 8823848510191727133 90071992547409920 60750000004131243 37780000000000000000 qz145 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000017001 8500500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz290) Bool.false 8461340443916598509568 4722366482869645213696 1000000000068004 34002000000000000000 4034681531866359 2251799813685248 250000000017001 8500500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 53145 131072 24973259072661432 36028797018963968 34002 1000000000000000 rfl rfl rfl rfl (ep114 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep458 := nat_lit 9082949698864887280332404860121616

noncomputable def ep459 := BSN.cos_dyadic_bound_f 308714286 536870912 2 1 262144 68071 ep458 ep75 ep458 ep458 ep76 ep458 219985 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 308714286) qz268 0 1 ep458 ep75 ep458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 308714286) qz269 0 1 ep458 ep76 ep458 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 25680779) qz30)

noncomputable def ep460 := @Enclosure.Real.IsNear.cos_image qz149 qz363 Bool.false 25680779 262144 211 131072 Bool.true 219985 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 8823848510191727133 90071992547409920 60750000004131243 37780000000000000000 25680779 262144 211 131072 (ep457 rfl) rfl) (Enclosure.sfrac_false_div 25680779 262144) (BSN.cos_reduce2 qz363 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21723836684287027970048) qz32) 226375608064910080 72057594037927936 Bool.false 219985 262144 15 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q2 25680779 262144 226375608064910080 72057594037927936 15 21723836684287027970048 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 219985 262144 21723836684287027970048 37778931862957161709568 308714286 536870912 68071 68004 (ep459 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep461 := BSN.sin_dyadic_bound_f 308714286 536870912 2 1 262144 68071 ep458 ep79 ep458 ep458 ep80 ep458 142568 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 308714286) qz274 0 1 ep458 ep79 ep458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 308714286) qz275 0 1 ep458 ep80 ep458 rfl rfl rfl rfl) rfl rfl

noncomputable def ep462 := @Enclosure.Real.IsNear.sin_image qz149 qz363 Bool.false 25680779 262144 211 131072 Bool.true 142568 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 8823848510191727133 90071992547409920 60750000004131243 37780000000000000000 25680779 262144 211 131072 (ep457 rfl) rfl) (Enclosure.sfrac_false_div 25680779 262144) (BSN.sin_reduce2 qz363 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21723836684287027970048) qz32) 226375608064910080 72057594037927936 Bool.false 142568 262144 15 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q2 25680779 262144 226375608064910080 72057594037927936 15 21723836684287027970048 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 142568 262144 21723836684287027970048 37778931862957161709568 308714286 536870912 68071 68004 (ep461 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep463 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.true 5885698675 17179869184 131554751473 194716637331456 Bool.false 476800855 2147483648 65558014667 97358318665728 (@Enclosure.Real.IsNear.mulLit_ft qz39 (Real.cos qz149) 26755 65536 1 131072 219985 262144 3652747 2228355072 5885698675 17179869184 131554751473 194716637331456 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.true 219985 262144 7305494 4456710144 219985 262144 3652747 2228355072 (ep460 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz39 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 26755 65536 1 131072 17821 32768 3652747 2228355072 476800855 2147483648 65558014667 97358318665728 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.true 17821 32768 3652747 2228355072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.true 142568 262144 7305494 4456710144 17821 32768 3652747 2228355072 (ep462 rfl rfl) rfl)) rfl)

noncomputable def ep464 := @ep415 5885698675 17179869184 131554751473 194716637331456 Bool.false 476800855 2147483648 65558014667 97358318665728 Bool.false 127038780706941566976 29578521081 17179869184 282624344643 64905545777152 Bool.false 12865078335448809472 5990768939 68719476736 563157636179 129811091554304 (ep416 (BSN.head_sum_c_succ qz134 5 6 rfl rfl) (ep455 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep456 ep463) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz253 qz355 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep465 := @Enclosure.Complex.IsNear.of_eq qz136 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.false 23695716555 68719476736 729593323745 1168299823988736 Bool.false 5318172675 34359738368 181838126735 292074955997184 (BSN.cpow_neg_s_mk qz143 54675 1000 7 qz144 rfl)

noncomputable def ep466 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz44 54675 1000 0 1 4381783608859895 2251799813685248 250000000017001 8500500000000000000 1916592150515318073 18014398509481984 60750000004131243 37780000000000000000 qz145 (BSN.isNear_log_sfrac 7 1 4381783608859895 2251799813685248 250000000017001 8500500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz294) Bool.false 9189266258887746519040 4722366482869645213696 1000000000068004 34002000000000000000 4381783608859895 2251799813685248 250000000017001 8500500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 73349 131072 24973259072661432 36028797018963968 34002 1000000000000000 rfl rfl rfl rfl (ep124 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep467 := nat_lit 36382368216788893696681882788925605779157313071028303815485291635056640000

noncomputable def ep468 := nat_lit 20948797015752781604417084142123108522472262990396670290276377600000000

noncomputable def ep469 := nat_lit 95253237753564455178235874882384577722089912474518248717229602051891200000

noncomputable def ep470 := BSN.sin_dyadic_bound_f 616800740 536870912 3 2 262144 68071 ep467 ep64 ep468 ep469 ep66 ep468 239155 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 616800740) qz274 0 2 ep467 ep64 ep468 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 616800740) qz275 0 2 ep469 ep66 ep468 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13945043) qz23)

noncomputable def ep471 := @Enclosure.Real.IsNear.cos_image qz150 qz364 Bool.false 13945043 131072 423 262144 Bool.false 239155 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 1916592150515318073 18014398509481984 60750000004131243 37780000000000000000 13945043 131072 423 262144 (ep466 rfl) rfl) (Enclosure.sfrac_false_div 13945043 131072) (BSN.cos_reduce3 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21701746751876498456576) qz273) 226375608064910080 72057594037927936 Bool.false 239155 262144 16 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q3 13945043 131072 226375608064910080 72057594037927936 16 21701746751876498456576 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 239155 262144 21701746751876498456576 18889465931478580854784 616800740 536870912 68071 68004 (ep470 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep472 := nat_lit 20221737363556386623314120253466280147764050489678122862065284853964800000

noncomputable def ep473 := nat_lit 60623314496637654306733526592114594226247206943053575245615301806694400000

noncomputable def ep474 := BSN.cos_dyadic_bound_f 616800740 536870912 3 2 262144 68071 ep472 ep57 ep468 ep473 ep60 ep468 107350 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 616800740) qz268 0 2 ep472 ep57 ep468 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 616800740) qz269 0 2 ep473 ep60 ep468 rfl rfl rfl rfl) rfl rfl

noncomputable def ep475 := @Enclosure.Real.IsNear.sin_image qz150 qz364 Bool.false 13945043 131072 423 262144 Bool.true 107350 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 1916592150515318073 18014398509481984 60750000004131243 37780000000000000000 13945043 131072 423 262144 (ep466 rfl) rfl) (Enclosure.sfrac_false_div 13945043 131072) (BSN.sin_reduce3 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21701746751876498456576) qz273) 226375608064910080 72057594037927936 Bool.false 107350 262144 16 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q3 13945043 131072 226375608064910080 72057594037927936 16 21701746751876498456576 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 107350 262144 21701746751876498456576 18889465931478580854784 616800740 536870912 68071 68004 (ep474 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep476 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.false 23695716555 68719476736 729593323745 1168299823988736 Bool.false 5318172675 34359738368 181838126735 292074955997184 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz150) 99081 262144 1 262144 239155 262144 7322495 4456710144 23695716555 68719476736 729593323745 1168299823988736 qz296 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.false 239155 262144 14644990 8913420288 239155 262144 7322495 4456710144 (ep471 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz42 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 99081 262144 1 262144 53675 131072 7322495 4456710144 5318172675 34359738368 181838126735 292074955997184 qz296 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.true 53675 131072 7322495 4456710144 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.true 107350 262144 14644990 8913420288 53675 131072 7322495 4456710144 (ep475 rfl rfl) rfl)) rfl)

noncomputable def ep477 := @ep413 23695716555 68719476736 729593323745 1168299823988736 Bool.false 5318172675 34359738368 181838126735 292074955997184 Bool.false 2439709801947108212736 142009800879 68719476736 5816831527319 1168299823988736 Bool.false 571303296784874340352 16627114289 68719476736 5795771232551 1168299823988736 (ep414 (BSN.head_sum_c_succ qz134 6 7 rfl rfl) (ep464 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep465 ep476) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz253 qz355 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep478 := @Enclosure.Complex.IsNear.of_eq qz135 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.false 10052614107 34359738368 342239178875 584149911994368 Bool.true 6820422039 34359738368 341053393127 584149911994368 (BSN.cpow_neg_s_mk qz143 54675 1000 8 qz144 rfl)

noncomputable def ep479 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz47 54675 1000 0 1 9364972152248037 4503599627370496 500000000051003 17001000000000000000 20481194096966456919 180143985094819840 121500000012393729 75560000000000000000 qz145 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000051003 17001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz298) Bool.false 9819885039515637645312 4722366482869645213696 1000000000102006 34002000000000000000 9364972152248037 4503599627370496 500000000051003 17001000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 131072 24973259072661432 36028797018963968 34002 1000000000000000 rfl rfl rfl rfl (ep135 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep480 := nat_lit 10491686889909978527500210457249761

noncomputable def ep481 := BSN.cos_dyadic_bound_f 320045209 536870912 2 1 262144 68071 ep480 ep75 ep480 ep480 ep76 ep480 216927 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 320045209) qz268 0 1 ep480 ep75 ep480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 320045209) qz269 0 1 ep480 ep76 ep480 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz365 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7451015) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep482 := @Enclosure.Real.IsNear.cos_image qz151 qz365 Bool.false 7451015 65536 211 131072 Bool.false 216927 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 20481194096966456919 180143985094819840 121500000012393729 75560000000000000000 7451015 65536 211 131072 (ep479 rfl) rfl) (Enclosure.sfrac_false_div 7451015 65536) (BSN.cos_reduce0 qz365 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5630294870803055902720) qz349) 226375608064910080 72057594037927936 Bool.false 216927 262144 18 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 7451015 65536 226375608064910080 72057594037927936 18 5630294870803055902720 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 216927 262144 5630294870803055902720 9444732965739290427392 320045209 536870912 68071 68004 (ep481 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep483 := BSN.sin_dyadic_bound_f 320045209 536870912 2 1 262144 68071 ep480 ep79 ep480 ep480 ep80 ep480 147179 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 320045209) qz274 0 1 ep480 ep79 ep480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 320045209) qz275 0 1 ep480 ep80 ep480 rfl rfl rfl rfl) rfl rfl

noncomputable def ep484 := @Enclosure.Real.IsNear.sin_image qz151 qz365 Bool.false 7451015 65536 211 131072 Bool.false 147179 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 20481194096966456919 180143985094819840 121500000012393729 75560000000000000000 7451015 65536 211 131072 (ep479 rfl) rfl) (Enclosure.sfrac_false_div 7451015 65536) (BSN.sin_reduce0 qz365 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5630294870803055902720) qz349) 226375608064910080 72057594037927936 Bool.false 147179 262144 18 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 7451015 65536 226375608064910080 72057594037927936 18 5630294870803055902720 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 147179 262144 5630294870803055902720 9444732965739290427392 320045209 536870912 68071 68004 (ep483 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep485 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.false 10052614107 34359738368 342239178875 584149911994368 Bool.true 6820422039 34359738368 341053393127 584149911994368 (@Enclosure.Real.IsNear.mulLit_ff qz45 (Real.cos qz151) 46341 131072 1 131072 216927 262144 3652747 2228355072 10052614107 34359738368 342239178875 584149911994368 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.false 216927 262144 7305494 4456710144 216927 262144 3652747 2228355072 (ep482 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 46341 131072 1 131072 147179 262144 3652747 2228355072 6820422039 34359738368 341053393127 584149911994368 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.false 147179 262144 3652747 2228355072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.false 147179 262144 7305494 4456710144 147179 262144 3652747 2228355072 (ep484 rfl rfl) rfl)) rfl)

noncomputable def ep486 := @ep411 10052614107 34359738368 342239178875 584149911994368 Bool.true 6820422039 34359738368 341053393127 584149911994368 Bool.false 5570229985156188340224 162115029093 68719476736 2167103295023 389433274662912 Bool.false 102607463146112155648 2986270211 68719476736 2159292672935 389433274662912 (ep412 (BSN.head_sum_c_succ qz134 7 8 rfl rfl) (ep477 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep478 ep485) rfl rfl

theorem EMRow11.d10 : Enclosure.Complex.IsNear qz133 Bool.false 162115029093 68719476736 2167103295023 389433274662912 Bool.false 2986270211 68719476736 2159292672935 389433274662912 := ep410 (BSN.head_sum_c_succ qz134 8 9 rfl rfl) (ep486 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep487 := nat_lit 449378323991225456003641059

noncomputable def ep488 := nat_lit 151658347075668097850408960

noncomputable def ep489 := nat_lit 1204950059971076918213538745646903

noncomputable def ep490 := nat_lit 131503256520981000209289603585146880

noncomputable abbrev qz433 := (@HAdd.hAdd Complex Complex Complex qz438 (@HAdd.hAdd Complex Complex Complex qz438 qz441 (@HMul.hMul Complex Complex Complex qz440 Complex.I (@HDiv.hDiv Complex Complex Complex qz442 (↑qz445) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz366 := qz433

noncomputable abbrev qz152 := (Complex.Stirling.logGammaStirling 1 qz366)

noncomputable abbrev qz434 := (@HAdd.hAdd Complex Complex Complex qz438 qz441 (@HMul.hMul Complex Complex Complex qz440 Complex.I (@HDiv.hDiv Complex Complex Complex qz442 (↑qz445) (2 : Complex))))

noncomputable abbrev qz367 := qz434

noncomputable abbrev qz153 := qz367

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz253 (@HDiv.hDiv Real Real Real qz256 qz355 (2 : Real)) (Real.log Real.pi))

noncomputable def ep491 := Complex.re (@HMul.hMul Complex Complex Complex qz48 (Complex.exp (@HMul.hMul Complex Complex Complex qz48 Complex.I ↑(@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154))) (zetaApproximant qz134 1 11))

noncomputable def ep492 := @Enclosure.Real.IsNear.of_eq ep491 (@HSub.hSub Real Real Real qz49 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) (Complex.re (zetaApproximant qz134 1 11))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) (Complex.im (zetaApproximant qz134 1 11))))

noncomputable def ep493 := nat_lit 449382112877789087583382299

noncomputable def ep494 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) (Complex.re (zetaApproximant qz134 1 11))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) (Complex.im (zetaApproximant qz134 1 11))) ep493

noncomputable def ep495 := nat_lit 1194741079725933342308243308777279

noncomputable def ep496 := nat_lit 3791458676891702446260224

noncomputable def ep497 := nat_lit 1276122530642946988161929608703

noncomputable def ep498 := nat_lit 16437907065122625026161200448143360

noncomputable def ep499 := nat_lit 1703799345703582453836356427373582654279421804937216

noncomputable def ep500 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) (Complex.re (zetaApproximant qz134 1 11)) 262143 262144 3140249

noncomputable def ep501 := nat_lit 29506800368882369974763520

noncomputable def ep502 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) Bool.false 262143 262144 6280498

noncomputable abbrev qz368 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8235431) qz30)

noncomputable def ep503 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154) qz368 Bool.false 8235431 262144 177

noncomputable def ep504 := nat_lit 7427850240000000000000000

noncomputable def ep505 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154) Bool.false 22637381395115341637 720575940379279360 5001150326458697930287 ep504

noncomputable def ep506 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154 45187117897176250181 720575940379279360 1902718076458697930287 ep504 164070927 5242880

noncomputable def ep507 := nat_lit 118685074168822322361794560

noncomputable def ep508 := nat_lit 1856962560000000000000000

noncomputable def ep509 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 7719148130166682991 180143985094819840 818949844203447115817 ep508 Bool.false 45187117897176250181 720575940379279360

noncomputable def ep510 := nat_lit 5570887680000000000000000

noncomputable def ep511 := @Enclosure.Complex.IsNear.subLitP qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 6527026788554766871 180143985094819840 2374929532560203358331 ep510 Bool.false 47411360278702150981 720575940379279360 5052794229353810240141

noncomputable def ep512 := nat_lit 22283550720000000000000000

noncomputable def ep513 := nat_lit 34763952642636334471729079738433536

noncomputable def ep514 := nat_lit 12719042957729351943802655904628736

noncomputable abbrev qz369 := (@HSub.hSub Complex Complex Complex qz422 qz433 qz425)

noncomputable abbrev qz370 := (Complex.log qz433)

noncomputable abbrev qz155 := (@HSub.hSub Complex Complex Complex qz302 (@HMul.hMul Complex Complex Complex qz301 qz369 qz370) qz366)

noncomputable abbrev qz156 := qz366

noncomputable def ep515 := @Enclosure.Complex.IsNear.of_eq qz152 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz155 qz55) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz50 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz58 qz156 (@HSub.hSub Int Int Int qz60 qz61 (@HMul.hMul Int Int Int qz62 qz63 (@Nat.cast Int instNatCastInt k)))))) Bool.true 6527026788554766871

noncomputable def ep516 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz155 qz55) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz50 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz58 qz156 (@HSub.hSub Int Int Int qz60 qz61 (@HMul.hMul Int Int Int qz62 qz63 (@Nat.cast Int instNatCastInt k))))) Bool.true 6527071680609909271 180143985094819840

noncomputable def ep517 := nat_lit 14016683298479315407924625408

noncomputable def ep518 := nat_lit 407260483711798367576498634752

noncomputable def ep519 := @ep516 1159629760800789947 2720160000000000000000 Bool.false 47413542032582071621 720575940379279360 616750000337010823 2720160000000000000000 Bool.false 535155 2147483648 3 2147483648 Bool.true 26008533 8589934592 729 42949672960 Bool.true ep517 6527026788554766871 180143985094819840 2374929532560203358331 ep510 Bool.false ep518

noncomputable def ep520 := @Enclosure.Complex.IsNear.addLitP qz155 qz55 Bool.true 6692612089703561751 180143985094819840 1128500000058602447 2720160000000000000000

noncomputable def ep521 := nat_lit 1711032678641804055937024

noncomputable def ep522 := @ep520 Bool.false 47413542032582071621 720575940379279360 616750000337010823 2720160000000000000000 Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 Bool.true ep521 6527071680609909271 180143985094819840 1159629760800789947 2720160000000000000000 Bool.false 47413542032582071621 47413542032582071621 720575940379279360

noncomputable abbrev qz157 := (@HMul.hMul Complex Complex Complex qz301 qz369 qz370)

noncomputable def ep523 := @Enclosure.Complex.IsNear.subLitP qz157 qz156 Bool.true 6287288123240217111 180143985094819840 1128500000058602447 2720160000000000000000 Bool.false 13422457360540124225

noncomputable def ep524 := @ep523 144115188075855872 616750000337010823 2720160000000000000000 Bool.false 9000 4000 0 1 Bool.false 109350 4000 0 1 Bool.true 26770448358814247004000 6692612089703561751 180143985094819840 1128500000058602447 2720160000000000000000 Bool.false 37930833626065657296800 47413542032582071621 720575940379279360 616750000337010823 2720160000000000000000

noncomputable abbrev qz158 := qz369

noncomputable abbrev qz159 := qz370

noncomputable def ep525 := @Enclosure.Complex.IsNear.mul qz158 qz159 Bool.true 6287288123240217111 180143985094819840 1128500000058602447 2720160000000000000000 Bool.false 13422457360540124225 144115188075855872 616750000337010823

noncomputable abbrev qz160 := (Complex.re qz369)

noncomputable abbrev qz161 := (Complex.re qz370)

noncomputable abbrev qz162 := (Complex.im qz369)

noncomputable abbrev qz163 := (Complex.im qz370)

noncomputable def ep526 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz160 qz161) (@HMul.hMul Real Real Real qz0 qz162 qz163) 208799879651795145 36028797018963968 1750000001071063 136008000000000000000 1832821880374798209 45035996273704960

noncomputable def ep527 := nat_lit 56630856897991173826013250151514112

noncomputable def ep528 := @Enclosure.Real.IsNear.mulLit_ff qz160 qz161 7000 4000 0 1 29828554235970735 9007199254740992 250000000153009 34002000000000000000

noncomputable def ep529 := @Enclosure.Complex.IsNear.re_isNear qz158 Bool.false 7000 4000 0 1 Bool.false 109350 4000 0 1

noncomputable abbrev qz371 := (Enclosure.sfrac Bool.false 109350 4000)

noncomputable abbrev qz164 := qz371

noncomputable def ep530 := @Enclosure.Complex.IsNear.of_eq qz158 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz164) Bool.false 7000 4000 0 1 Bool.false 109350 4000 0

noncomputable abbrev qz165 := (Complex.mk qz316 qz371)

noncomputable def ep531 := @Enclosure.Complex.IsNear.of_eq qz159 (Complex.log qz165) Bool.false 29828554235970735 9007199254740992 250000000153009 34002000000000000000 Bool.false 838052985996707 562949953421312 500000000017001 34002000000000000000

noncomputable def ep532 := nat_lit 7198118899495198482301104490827273502417115478515625000000000000

noncomputable def ep533 := nat_lit 88666360381038812025651597937558221558239990234375000000000000

noncomputable def ep534 := nat_lit 48577278221887598815059467817387202445068359375000000000000

noncomputable def ep535 := BSN.log_dyadic_bound 3846422500 20230422500 4 3 ep532 262144 68004 ep533 ep534 100911 24076845000 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3846422500) (BSN.artanhQ 20230422500) 0 3 ep533 ep532 ep534 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz372 := (Real.log (Enclosure.sfrac Bool.false 12038422500 16000000))

noncomputable def ep536 := @Enclosure.Real.IsNear.mulLit_ff qz73 qz372 1 2 0 1 29828554235970735 4503599627370496 250000000153009 17001000000000000000 29828554235970735 9007199254740992 250000000153009 34002000000000000000 qz318 (BSN.isNear_log_sfrac 12038422500 16000000 29828554235970735 4503599627370496 250000000153009 17001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12038422500) qz319)) Bool.false 62555012173074498846720 9444732965739290427392 1000000000612036 68004000000000000000 29828554235970735 4503599627370496 250000000153009 17001000000000000000 (BSN.log_rat_reduce_isNear 12038422500 16000000 9 24076845000 16384000000 100911 262144 24973259072661432 36028797018963968 68004 1000000000000000 rfl rfl rfl rfl (ep535 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep537 := BSN.arctan_dyadic_bound_f 9000 109350 1 0 262144 68004 0 1 1 0 1 1 21526 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 109350) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 109350) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz373 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 109350)))

noncomputable def ep538 := @Enclosure.Real.IsNear.subLit_ff_p qz74 qz373 884279719003555 562949953421312 1 2000000000000000 21526 262144 1 68004 219690561961120759808 838052985996707 562949953421312 500000000017001 34002000000000000000 qz75 (ep537 rfl) rfl rfl

noncomputable abbrev qz374 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 109350) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep539 := @Enclosure.Complex.IsNear.re_isNear qz159 Bool.false 29828554235970735 9007199254740992 250000000153009 34002000000000000000 Bool.false 838052985996707 562949953421312 500000000017001 34002000000000000000 (ep531 (@congrArg Complex Complex qz156 qz165 Complex.log (BSN.w_shift_mk qz143 Bool.false 54675 1000 2 qz144 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz165) Bool.false 29828554235970735 9007199254740992 250000000153009 34002000000000000000 Bool.false 838052985996707 562949953421312 500000000017001 34002000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz165)) (@HMul.hMul Real Real Real qz0 qz73 qz372) Bool.false 29828554235970735 9007199254740992 250000000153009 34002000000000000000 (Enclosure.clog_re_eq 9000 109350 4000 12038422500 16000000 rfl rfl rfl) (ep536 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz165)) qz374 Bool.false 838052985996707 562949953421312 500000000017001 34002000000000000000 (Enclosure.clog_im_eq 9000 109350 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz374 (@HSub.hSub Real Real Real qz49 qz74 qz373) Bool.false 838052985996707 562949953421312 500000000017001 34002000000000000000 (BSN.arctan_recip 109350 9000 rfl rfl) ep538))))

noncomputable def ep540 := @Enclosure.Real.IsNear.mulLit_ff qz162 qz163 109350 4000 0 1 838052985996707 562949953421312 500000000017001 34002000000000000000

noncomputable def ep541 := @Enclosure.Complex.IsNear.im_isNear qz158 Bool.false 7000 4000 0 1 Bool.false 109350 4000 0 1

noncomputable def ep542 := @Enclosure.Complex.IsNear.im_isNear qz159 Bool.false 29828554235970735 9007199254740992 250000000153009 34002000000000000000 Bool.false 838052985996707 562949953421312 500000000017001 34002000000000000000 (ep531 (@congrArg Complex Complex qz156 qz165 Complex.log (BSN.w_shift_mk qz143 Bool.false 54675 1000 2 qz144 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz165) Bool.false 29828554235970735 9007199254740992 250000000153009 34002000000000000000 Bool.false 838052985996707 562949953421312 500000000017001 34002000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz165)) (@HMul.hMul Real Real Real qz0 qz73 qz372) Bool.false 29828554235970735 9007199254740992 250000000153009 34002000000000000000 (Enclosure.clog_re_eq 9000 109350 4000 12038422500 16000000 rfl rfl rfl) (ep536 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz165)) qz374 Bool.false 838052985996707 562949953421312 500000000017001 34002000000000000000 (Enclosure.clog_im_eq 9000 109350 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz374 (@HSub.hSub Real Real Real qz49 qz74 qz373) Bool.false 838052985996707 562949953421312 500000000017001 34002000000000000000 (BSN.arctan_recip 109350 9000 rfl rfl) ep538))))

noncomputable abbrev qz375 := (Enclosure.Real.IsNear.const Bool.false 109350 4000)

noncomputable abbrev qz166 := (@ep530 1 (BSN.w_sub_half_mk qz355 Bool.false 54675 1000 2 qz356 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz371 Bool.false 7000 4000 0 1 Bool.false 109350 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz375))

noncomputable def ep543 := @ep526 121500000004131243 302240000000000000000 ep527 6287288123240217111 180143985094819840 1128500000058602447 2720160000000000000000 (@ep528 208799879651795145 36028797018963968 1750000001071063 136008000000000000000 (ep529 qz166) ep539 rfl) (@ep540 1832821880374798209 45035996273704960 121500000004131243 302240000000000000000 (ep541 qz166) ep542 rfl) rfl

noncomputable def ep544 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz160 qz163) (@HMul.hMul Real Real Real qz0 qz162 qz161) 5866370901976949 2251799813685248 3500000000119007 136008000000000000000 13047009622813599489 144115188075855872

noncomputable def ep545 := nat_lit 30224686983662437370247168969932800

noncomputable def ep546 := @Enclosure.Real.IsNear.mulLit_ff qz160 qz163 7000 4000 0 1 838052985996707 562949953421312 500000000017001 34002000000000000000

noncomputable def ep547 := @Enclosure.Real.IsNear.mulLit_ff qz162 qz161 109350 4000 0 1 29828554235970735 9007199254740992 250000000153009 34002000000000000000

noncomputable def ep548 := @ep544 60750000037181187 302240000000000000000 ep545 13422457360540124225 144115188075855872 616750000337010823 2720160000000000000000 (@ep546 5866370901976949 2251799813685248 3500000000119007 136008000000000000000 (ep529 qz166) ep542 rfl) (@ep547 13047009622813599489 144115188075855872 60750000037181187 302240000000000000000 (ep541 qz166) ep539 rfl) rfl

noncomputable def ep549 := @Enclosure.Complex.IsNear.of_eq qz156 qz165 Bool.false 9000 4000 0 1 Bool.false 109350 4000 0 1 (BSN.w_shift_mk qz143 Bool.false 54675 1000 2 qz144 rfl)

noncomputable abbrev qz376 := (ep549 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 109350 4000) Bool.false 9000 4000 0 1 Bool.false 109350 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 109350 4000)))

noncomputable abbrev qz167 := qz376

noncomputable def ep550 := ep524 (@ep525 2720160000000000000000 (ep543 rfl) (ep548 rfl)) qz167 rfl rfl rfl rfl rfl rfl

noncomputable def ep551 := @ep522 616750000337010823 2720160000000000000000 (ep550 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz78 (↑qz3) Bool.false 240893 262144 3 262144 Bool.false 0 1 0 1 (@ep212 262144 3 262144 (ep214 rfl) (ep216 rfl) rfl rfl) (@ep217 1 0 1 (ep219 rfl) (ep221 rfl) rfl rfl))

noncomputable abbrev qz377 := (@HPow.hPow Complex Int Complex qz427 qz433 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz168 := qz377

noncomputable def ep552 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz50 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz58 qz156 (@HSub.hSub Int Int Int qz60 qz61 (@HMul.hMul Int Int Int qz62 qz63 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz50 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz58 qz156 (@HSub.hSub Int Int Int qz60 qz61 (@HMul.hMul Int Int Int qz62 qz63 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81) qz168)) Bool.false 535155 2147483648 3 2147483648

noncomputable def ep553 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz50 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz58 qz156 (@HSub.hSub Int Int Int qz60 qz61 (@HMul.hMul Int Int Int qz62 qz63 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81) qz168) Bool.false 0 1 0 1 Bool.false

noncomputable def ep554 := @ep553 0 1 0 1 Bool.false 535155 2147483648 3 2147483648 Bool.true 26008533 8589934592 729 42949672960 Bool.false 535155 535155 2147483648 3 2147483648 Bool.true 26008533 26008533 8589934592 729

noncomputable def ep555 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz50 (@HMul.hMul Complex Complex Complex qz48 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz58 qz156 (@HSub.hSub Int Int Int qz60 qz61 (@HMul.hMul Int Int Int qz62 qz63 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz17 qz17) Bool.false 0 1 0 1 Bool.false

noncomputable def ep556 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81) qz168 Bool.false 535155 2147483648 3 2147483648 Bool.true 26008533 8589934592 729 42949672960

noncomputable abbrev qz169 := (Complex.re qz377)

noncomputable abbrev qz170 := (Complex.im qz377)

noncomputable def ep557 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz169) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz170) 535155 2147483648 3 2147483648 0 1 0

noncomputable def ep558 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz169 1 12 0 1 1605465 536870912 9 536870912 535155

noncomputable def ep559 := @Enclosure.Complex.IsNear.re_isNear qz168 Bool.false 1605465 536870912 9 536870912 Bool.true 78025599 2147483648 2187 10737418240

noncomputable abbrev qz378 := (@HPow.hPow Complex Nat Complex qz428 qz433 1)

noncomputable abbrev qz171 := (@Inv.inv Complex Complex.instInv qz378)

noncomputable def ep560 := @Enclosure.Complex.IsNear.of_eq qz168 qz171 Bool.false 1605465 536870912 9 536870912 Bool.true 78025599 2147483648 2187

noncomputable def ep561 := @Enclosure.Complex.IsNear.of_parts qz171 Bool.false 1605465 536870912 9 536870912 Bool.true 78025599 2147483648 2187

noncomputable abbrev qz172 := (Complex.re qz378)

noncomputable abbrev qz173 := qz378

noncomputable def ep562 := @Enclosure.Real.IsNear.mulLit_ff qz172 (@Inv.inv Real Real.instInv (@DFunLike.coe qz87 Complex (fun (x : Complex) => Real) qz88 Complex.normSq qz173)) 9000 4000 0 1 178385 134217728 1 134217728

noncomputable def ep563 := @Enclosure.Complex.IsNear.re_isNear qz173 Bool.false 9000 4000 0 1 Bool.false 109350 4000 0 1

noncomputable def ep564 := @Enclosure.Complex.IsNear.of_eq qz173 qz156 Bool.false 9000 4000 0 1 Bool.false 109350 4000 0

noncomputable def ep565 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz87 Complex (fun (x : Complex) => Real) qz88 Complex.normSq qz173)) Bool.false 178385 134217728 1 134217728 178385 134217728 1

noncomputable abbrev qz174 := (Complex.im qz378)

noncomputable def ep566 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz87 Complex (fun (x : Complex) => Real) qz88 Complex.normSq qz173) (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 qz172 qz172) (@HMul.hMul Real Real Real qz0 qz174 qz174)) Bool.false 4815369 6400 0 1

noncomputable def ep567 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz172 qz172) (@HMul.hMul Real Real Real qz0 qz174 qz174) 81 16 0 1 4782969 6400

noncomputable def ep568 := @Enclosure.Real.IsNear.mulLit_ff qz172 qz172 9000 4000 0 1 9000 4000 0 1

noncomputable def ep569 := @Enclosure.Real.IsNear.mulLit_ff qz174 qz174 109350 4000 0 1 109350 4000 0 1

noncomputable def ep570 := @Enclosure.Complex.IsNear.im_isNear qz173 Bool.false 9000 4000 0 1 Bool.false 109350 4000 0 1

noncomputable abbrev qz175 := (ep563 (@ep564 1 (BSN.pow_one_c qz366) qz376))

noncomputable abbrev qz176 := (ep570 (@ep564 1 (BSN.pow_one_c qz366) qz376))

noncomputable def ep571 := @ep567 0 1 77045904 4815369 6400 0 1 (@ep568 81 16 0 1 qz175 qz175 rfl) (@ep569 4782969 6400 0 1 qz176 qz176 rfl)

noncomputable def ep572 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz87 Complex (fun (x : Complex) => Real) qz88 Complex.normSq qz173) 4815369 6400 0 1 89192 89193 67108864 (ep566 (Enclosure.Complex.normSq_eq_mul_add_mul qz173) (ep571 rfl rfl)) rfl

noncomputable def ep573 := @Enclosure.Real.IsNear.of_eq (Complex.re qz171) (@HMul.hMul Real Real Real qz0 qz172 (@Inv.inv Real Real.instInv (@DFunLike.coe qz87 Complex (fun (x : Complex) => Real) qz88 Complex.normSq qz173))) Bool.false 1605465 536870912 9 536870912 (Enclosure.Complex.inv_re_eq_mul qz173) (@ep562 1605465 536870912 9 536870912 qz175 (@ep565 134217728 (ep572 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep574 := @Enclosure.Real.IsNear.of_eq (Complex.im qz171) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz174) (@Inv.inv Real Real.instInv (@DFunLike.coe qz87 Complex (fun (x : Complex) => Real) qz88 Complex.normSq qz173))) Bool.true 78025599 2147483648 2187 10737418240 (Enclosure.Complex.inv_im_eq_mul qz173)

noncomputable def ep575 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz174) (@Inv.inv Real Real.instInv (@DFunLike.coe qz87 Complex (fun (x : Complex) => Real) qz88 Complex.normSq qz173)) 109350 4000 0 1 178385 134217728 1

noncomputable def ep576 := @ep575 134217728 78025599 2147483648 2187 10737418240 (@Enclosure.Real.IsNear.neg qz174 Bool.false 109350 4000 0 1 qz176) (@ep565 134217728 (ep572 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep577 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz170 0 1 0 1 78025599 2147483648 2187 10737418240 0

noncomputable def ep578 := @Enclosure.Complex.IsNear.im_isNear qz168 Bool.false 1605465 536870912 9 536870912 Bool.true 78025599 2147483648 2187 10737418240

noncomputable abbrev qz177 := (@ep560 10737418240 (BSN.zpow_one_sub_two_mul qz366 1 1 rfl rfl) (@ep561 10737418240 ep573 (ep574 ep576)))

noncomputable def ep579 := @ep557 1 535155 535155 2147483648 3 2147483648 (@ep558 2147483648 3 2147483648 ep231 (ep559 qz177) rfl) (@ep577 1 0 1 ep251 (ep578 qz177) rfl) rfl

noncomputable def ep580 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz170) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz169) 26008533 8589934592 729 42949672960 0 1 0

noncomputable def ep581 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz170 1 12 0 1 78025599 2147483648 2187 10737418240 26008533

noncomputable def ep582 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 (@Rat.cast Complex Complex.instRatCast (bernoulli qz80)) qz81)) qz169 0 1 0 1 1605465 536870912 9 536870912 0

noncomputable def ep583 := @ep580 1 26008533 26008533 8589934592 729 42949672960 (@ep581 8589934592 729 42949672960 ep231 (ep578 qz177) rfl) (@ep582 1 0 1 ep251 (ep559 qz177) rfl) rfl

noncomputable def ep584 := @ep554 42949672960 (@ep555 0 1 0 1 (BSN.stirling_sum_base qz156) qz95) (ep556 (ep579 rfl) (ep583 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep585 := @ep519 47411360278702150981 720575940379279360 5052794229353810240141 ep512 (ep551 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep552 Bool.true 26008533 8589934592 729 42949672960 (BSN.stirling_sum_succ qz156 0 1 rfl) (ep584 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep586 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz143 2) Bool.false 29803033540297903 4503599627370496 250000000153009 17001000000000000000 Bool.false 868844680283555 281474976710656

noncomputable abbrev qz178 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz259 qz367 qz324))

noncomputable def ep587 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz143 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz143 1) qz178) Bool.false 29803033540297903 4503599627370496 250000000153009 17001000000000000000 Bool.false 868844680283555 281474976710656 500000000017001 17001000000000000000

noncomputable def ep588 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz143 1) qz178 Bool.false 29798523824637103 9007199254740992 250000000153009 34002000000000000000 Bool.false 879132200699299 562949953421312 500000000017001 34002000000000000000 Bool.false

noncomputable def ep589 := nat_lit 536883722986384120536913571479552

noncomputable def ep590 := nat_lit 978232144591964007725080248320

noncomputable abbrev qz179 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz259 qz367 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep591 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz143 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz143 0) qz179) Bool.false 29798523824637103 9007199254740992 250000000153009 34002000000000000000 Bool.false 879132200699299 562949953421312 500000000017001 34002000000000000000

noncomputable def ep592 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz143 0) qz179 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz379 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz164))

noncomputable def ep593 := @Enclosure.Complex.IsNear.of_eq qz179 qz379 Bool.false 29798523824637103 9007199254740992 250000000153009 34002000000000000000 Bool.false 879132200699299 562949953421312 500000000017001 34002000000000000000

noncomputable def ep594 := nat_lit 7029011249967002376767502993856513620620240478515625000000000000

noncomputable def ep595 := nat_lit 83617072260347751317293567745249349105114990234375000000000000

noncomputable def ep596 := nat_lit 42821854600050969641451703263118374320068359375000000000000

noncomputable def ep597 := BSN.log_dyadic_bound 3766422500 20150422500 4 3 ep594 262144 68004 ep595 ep596 99163 23916845000 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3766422500) (BSN.artanhQ 20150422500) 0 3 ep595 ep594 ep596 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep598 := @Enclosure.Real.IsNear.mulLit_ff qz73 (Real.log (Enclosure.sfrac Bool.false 11958422500 16000000)) 1 2 0 1 29798523824637103 4503599627370496 250000000153009 17001000000000000000 29798523824637103 9007199254740992 250000000153009 34002000000000000000 qz318 (BSN.isNear_log_sfrac 11958422500 16000000 29798523824637103 4503599627370496 250000000153009 17001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11958422500) qz319)) Bool.false 62492033835885349830656 9444732965739290427392 1000000000612036 68004000000000000000 29798523824637103 4503599627370496 250000000153009 17001000000000000000 (BSN.log_rat_reduce_isNear 11958422500 16000000 9 23916845000 16384000000 99163 262144 24973259072661432 36028797018963968 68004 1000000000000000 rfl rfl rfl rfl (ep597 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep599 := BSN.arctan_dyadic_bound_f 1000 109350 1 0 262144 68004 0 1 1 0 1 1 2397 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 109350) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 109350) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz380 := (@Nat.cast Real Real.instNatCast 109350)

noncomputable def ep600 := @Enclosure.Real.IsNear.subLit_ff_p qz74 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz329 qz380)) 884279719003555 562949953421312 1 2000000000000000 2397 262144 1 68004 230459231620117037056 879132200699299 562949953421312 500000000017001 34002000000000000000 qz75 (ep599 rfl) rfl rfl

noncomputable abbrev qz180 := (@HAdd.hAdd Complex Complex Complex qz259 qz367 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz381 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz164)

noncomputable def ep601 := @ep592 29798523824637103 9007199254740992 250000000153009 34002000000000000000 Bool.false 879132200699299 562949953421312 500000000017001 34002000000000000000 Bool.false 29798523824637103 29798523824637103 9007199254740992 250000000153009 34002000000000000000 Bool.false 879132200699299 879132200699299 562949953421312 500000000017001 34002000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz143 0) (Complex.mk qz17 qz17) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz143) qz95) (ep593 (@congrArg Complex Complex qz180 qz381 Complex.log (BSN.w_shift_mk qz143 Bool.false 54675 1000 0 qz144 rfl)) (@Enclosure.Complex.IsNear.of_parts qz379 Bool.false 29798523824637103 9007199254740992 250000000153009 34002000000000000000 Bool.false 879132200699299 562949953421312 500000000017001 34002000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz379) (@HMul.hMul Real Real Real qz0 qz73 (Real.log (Enclosure.sfrac Bool.false 11958422500 16000000))) Bool.false 29798523824637103 9007199254740992 250000000153009 34002000000000000000 (Enclosure.clog_re_eq 1000 109350 4000 11958422500 16000000 rfl rfl rfl) (ep598 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz379) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz380 qz329)) Bool.false 879132200699299 562949953421312 500000000017001 34002000000000000000 (Enclosure.clog_im_eq 1000 109350 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz380 qz329)) (@HSub.hSub Real Real Real qz49 qz74 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz329 qz380))) Bool.false 879132200699299 562949953421312 500000000017001 34002000000000000000 (BSN.arctan_recip 109350 1000 rfl rfl) ep600)))) rfl rfl

noncomputable abbrev qz382 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz164))

noncomputable def ep602 := @Enclosure.Complex.IsNear.of_eq qz178 qz382 Bool.false 29807543255958703 9007199254740992 250000000153009 34002000000000000000 Bool.false 858557159867811 562949953421312 500000000017001 34002000000000000000

noncomputable def ep603 := nat_lit 7079392142757839581788676259131148897659302978515625000000000000

noncomputable def ep604 := nat_lit 85109307732683054052515221975524098341052490234375000000000000

noncomputable def ep605 := nat_lit 44485347480174966571162120087586522757568359375000000000000

noncomputable def ep606 := BSN.log_dyadic_bound 3790422500 20174422500 4 3 ep603 262144 68004 ep604 ep605 99688 23964845000 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3790422500) (BSN.artanhQ 20174422500) 0 3 ep604 ep603 ep605 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep607 := @Enclosure.Real.IsNear.mulLit_ff qz73 (Real.log (Enclosure.sfrac Bool.false 11982422500 16000000)) 1 2 0 1 29807543255958703 4503599627370496 250000000153009 17001000000000000000 29807543255958703 9007199254740992 250000000153009 34002000000000000000 qz318 (BSN.isNear_log_sfrac 11982422500 16000000 29807543255958703 4503599627370496 250000000153009 17001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11982422500) qz319)) Bool.false 62510948954320305913856 9444732965739290427392 1000000000612036 68004000000000000000 29807543255958703 4503599627370496 250000000153009 17001000000000000000 (BSN.log_rat_reduce_isNear 11982422500 16000000 9 23964845000 16384000000 99688 262144 24973259072661432 36028797018963968 68004 1000000000000000 rfl rfl rfl rfl (ep606 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep608 := BSN.arctan_dyadic_bound_f 5000 109350 1 0 262144 68004 0 1 1 0 1 1 11978 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 109350) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 109350) 0 0 rfl) rfl rfl rfl

noncomputable def ep609 := @Enclosure.Real.IsNear.subLit_ff_p qz74 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz333 qz380)) 884279719003555 562949953421312 1 2000000000000000 11978 262144 1 68004 225065608116387446784 858557159867811 562949953421312 500000000017001 34002000000000000000 qz75 (ep608 rfl) rfl rfl

noncomputable abbrev qz181 := (@HAdd.hAdd Complex Complex Complex qz259 qz367 qz324)

noncomputable abbrev qz383 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz164)

noncomputable def ep610 := @ep588 29807543255958703 9007199254740992 250000000153009 34002000000000000000 Bool.false 858557159867811 562949953421312 500000000017001 34002000000000000000 Bool.false ep589 29803033540297903 4503599627370496 250000000153009 17001000000000000000 Bool.false ep590 868844680283555 281474976710656 500000000017001 17001000000000000000 (ep591 (BSN.log_sum_c_succ qz143 0 1 rfl) (ep601 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep602 (@congrArg Complex Complex qz181 qz383 Complex.log (BSN.w_shift_mk qz143 Bool.false 54675 1000 1 qz144 rfl)) (@Enclosure.Complex.IsNear.of_parts qz382 Bool.false 29807543255958703 9007199254740992 250000000153009 34002000000000000000 Bool.false 858557159867811 562949953421312 500000000017001 34002000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz382) (@HMul.hMul Real Real Real qz0 qz73 (Real.log (Enclosure.sfrac Bool.false 11982422500 16000000))) Bool.false 29807543255958703 9007199254740992 250000000153009 34002000000000000000 (Enclosure.clog_re_eq 5000 109350 4000 11982422500 16000000 rfl rfl rfl) (ep607 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz382) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz380 qz333)) Bool.false 858557159867811 562949953421312 500000000017001 34002000000000000000 (Enclosure.clog_im_eq 5000 109350 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz380 qz333)) (@HSub.hSub Real Real Real qz49 qz74 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz333 qz380))) Bool.false 858557159867811 562949953421312 500000000017001 34002000000000000000 (BSN.arctan_recip 109350 5000 rfl rfl) ep609)))) rfl rfl

noncomputable def ep611 := @ep511 ep512 Bool.false 29803033540297903 4503599627370496 250000000153009 17001000000000000000 Bool.false 868844680283555 281474976710656 500000000017001 17001000000000000000 Bool.true ep513 7719148130166682991 180143985094819840 818949844203447115817 ep508 Bool.false ep514 45187117897176250181 720575940379279360 1902718076458697930287 ep504 (@ep515 180143985094819840 2374929532560203358331 ep510 Bool.false 47411360278702150981 720575940379279360 5052794229353810240141 ep512 (BSN.logGammaStirling_unfold 1 qz156) (ep585 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep586 500000000017001 17001000000000000000 (BSN.log_sum_c_eq qz143 2) (ep587 (BSN.log_sum_c_succ qz143 1 2 rfl) (ep610 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz182 := (@HDiv.hDiv Real Real Real qz256 qz355 (2 : Real))

noncomputable def ep612 := @Enclosure.Real.IsNear.mulLit_ff qz182 (Real.log Real.pi) 54675 2000 0 1 75021 65536 1 65536 164070927 5242880 2187 5242880 (@Enclosure.Real.IsNear.of_eq qz182 (Enclosure.sfrac Bool.false 54675 2000) Bool.false 54675 2000 0 1 (BSN.t_half_eq qz143 Bool.false 54675 1000 qz144) (Enclosure.Real.IsNear.const Bool.false 54675 2000)) EMRow11.d5 rfl

noncomputable def ep613 := @ep506 2187 5242880 ep507 22637381395115341637 720575940379279360 5001150326458697930287 ep504 (@ep509 1902718076458697930287 ep504 (ep611 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep612 rfl rfl

noncomputable def ep614 := nat_lit 127237822880449064559847920709735984120364733814490181503875821491898078625

noncomputable def ep615 := nat_lit 255484216388668625335583195619938899691717399221973961232485187027785121

noncomputable def ep616 := nat_lit 332828275955594467501439324304019104953835331820162517525298365985497601441

noncomputable def ep617 := BSN.sin_dyadic_bound_f 843180413 536870912 3 2 262144 68071 ep614 ep64 ep615 ep616 ep66 ep615 262143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 843180413) qz274 0 2 ep614 ep64 ep615 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 843180413) qz275 0 2 ep616 ep66 ep615 rfl rfl rfl rfl) rfl rfl

noncomputable def ep618 := @ep503 262144 Bool.false 262143 262144 1 34002 (@ep505 8235431 262144 177 262144 ep613 rfl) (Enclosure.sfrac_false_div 8235431 262144) (BSN.cos_reduce3 qz368 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59333546839945827581952) qz32) 226375608064910080 72057594037927936 Bool.false 262143 262144 4 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q3 8235431 262144 226375608064910080 72057594037927936 4 59333546839945827581952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 262143 262144 59333546839945827581952 37778931862957161709568 843180413 536870912 68071 68004 (ep617 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep619 := nat_lit 3688350046110296246845440

noncomputable abbrev qz183 := qz354

noncomputable abbrev qz384 := (@HPow.hPow Complex Complex Complex qz416 qz429 qz431)

noncomputable abbrev qz184 := qz384

noncomputable abbrev qz185 := (@HAdd.hAdd Complex Complex Complex qz259 (@HDiv.hDiv Complex Complex Complex qz309 qz336 (@HSub.hSub Complex Complex Complex qz302 qz353 (1 : Complex))) qz308)

noncomputable def ep620 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz134 1 11) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 11, @HPow.hPow Complex Complex Complex qz101 (@Nat.cast Complex Complex.instNatCast n) qz183) (@HMul.hMul Complex Complex Complex qz48 qz184 (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))))) Bool.false 5142789769833134063279 1735592045696274923520 206326326986412458706599

noncomputable def ep621 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 11, @HPow.hPow Complex Complex Complex qz101 (@Nat.cast Complex Complex.instNatCast n) qz183) (@HMul.hMul Complex Complex Complex qz48 qz184 (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))))) Bool.false 199992727613 68719476736 2584763663621 389433274662912

noncomputable def ep622 := nat_lit 353409821946186850863470392377344

noncomputable def ep623 := nat_lit 250356059677714738176029884416

noncomputable def ep624 := @ep621 Bool.true 8811064433 34359738368 643944048161 97358318665728 Bool.false 91735778608741983119 1735592045696274923520 10482493433097131386439 ep501 Bool.false 11258171570282386993 72316335237344788480 1310637586424518536421 ep619 Bool.false ep622 5142789769833134063279 1735592045696274923520 206326326986412458706599 ep501 Bool.true ep623 7286320314676114887 72316335237344788480

noncomputable def ep625 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 11, @HPow.hPow Complex Complex Complex qz101 (@Nat.cast Complex Complex.instNatCast n) qz183) (BSN.headSumC qz134 11) Bool.false 199992727613 68719476736 2584763663621 389433274662912 Bool.true 8811064433 34359738368 643944048161

noncomputable abbrev qz186 := (BSN.headSumC qz353 10)

noncomputable abbrev qz187 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 10) qz354)

noncomputable def ep626 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz134 11) (@HAdd.hAdd Complex Complex Complex qz5 qz186 qz187) Bool.false 199992727613 68719476736 2584763663621 389433274662912 Bool.true 8811064433 34359738368 643944048161 97358318665728

noncomputable def ep627 := @Enclosure.Complex.IsNear.addLitP qz186 qz187 Bool.false 178832936775 68719476736 7142931227099 1168299823988736 Bool.true 12672929275 68719476736 7119293376719 1168299823988736 Bool.false

noncomputable abbrev qz188 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 9) qz354)

noncomputable def ep628 := @Enclosure.Complex.IsNear.of_eq qz186 (@HAdd.hAdd Complex Complex Complex qz5 qz133 qz188) Bool.false 178832936775 68719476736 7142931227099 1168299823988736 Bool.true 12672929275 68719476736 7119293376719 1168299823988736

noncomputable def ep629 := @Enclosure.Complex.IsNear.addLitP qz133 qz188 Bool.false 162115029093 68719476736 2167103295023 389433274662912 Bool.false 2986270211 68719476736 2159292672935 389433274662912 Bool.false

noncomputable abbrev qz189 := (@HMul.hMul Real Real Real qz253 qz355 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep630 := @Enclosure.Complex.IsNear.of_eq qz188 (Complex.mk (@HMul.hMul Real Real Real qz0 qz111 (Real.cos qz189)) (@HMul.hMul Real Real Real qz0 qz111 (@Neg.neg Real Real.instNeg (Real.sin qz189)))) Bool.false 8358953841 34359738368 320810671015 584149911994368 Bool.true 7829599743 34359738368 320707678957 584149911994368 (BSN.cpow_neg_s_mk qz143 54675 1000 9 qz144 rfl)

noncomputable def ep631 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz113 54675 1000 0 1 9895417793173221 4503599627370496 500000000051003 17001000000000000000 21641278713669834327 180143985094819840 121500000012393729 75560000000000000000 qz145 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000051003 17001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false 10376097607894403383296 4722366482869645213696 1000000000102006 34002000000000000000 9895417793173221 4503599627370496 500000000051003 17001000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 15438 131072 24973259072661432 36028797018963968 34002 1000000000000000 rfl rfl rfl rfl (ep306 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep632 := nat_lit 26667628035559440939589826954666401

noncomputable def ep633 := BSN.cos_dyadic_bound_f 404106743 536870912 2 1 262144 68071 ep632 ep75 ep632 ep632 ep76 ep632 191322 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 404106743) qz268 0 1 ep632 ep75 ep632 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 404106743) qz269 0 1 ep632 ep76 ep632 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz385 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 31492205) qz30)

noncomputable def ep634 := @Enclosure.Real.IsNear.cos_image qz189 qz385 Bool.false 31492205 262144 211 131072 Bool.false 191322 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz189 Bool.false 21641278713669834327 180143985094819840 121500000012393729 75560000000000000000 31492205 262144 211 131072 (ep631 rfl) rfl) (Enclosure.sfrac_false_div 31492205 262144) (BSN.cos_reduce0 qz385 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28436484055256782602240) qz32) 226375608064910080 72057594037927936 Bool.false 191322 262144 19 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 31492205 262144 226375608064910080 72057594037927936 19 28436484055256782602240 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 191322 262144 28436484055256782602240 37778931862957161709568 404106743 536870912 68071 68004 (ep633 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep635 := BSN.sin_dyadic_bound_f 404106743 536870912 2 1 262144 68071 ep632 ep79 ep632 ep632 ep80 ep632 179206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 404106743) qz274 0 1 ep632 ep79 ep632 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 404106743) qz275 0 1 ep632 ep80 ep632 rfl rfl rfl rfl) rfl rfl

noncomputable def ep636 := @Enclosure.Real.IsNear.sin_image qz189 qz385 Bool.false 31492205 262144 211 131072 Bool.false 179206 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz189 Bool.false 21641278713669834327 180143985094819840 121500000012393729 75560000000000000000 31492205 262144 211 131072 (ep631 rfl) rfl) (Enclosure.sfrac_false_div 31492205 262144) (BSN.sin_reduce0 qz385 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28436484055256782602240) qz32) 226375608064910080 72057594037927936 Bool.false 179206 262144 19 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 31492205 262144 226375608064910080 72057594037927936 19 28436484055256782602240 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 179206 262144 28436484055256782602240 37778931862957161709568 404106743 536870912 68071 68004 (ep635 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep637 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz111 (Real.cos qz189)) (@HMul.hMul Real Real Real qz0 qz111 (@Neg.neg Real Real.instNeg (Real.sin qz189))) Bool.false 8358953841 34359738368 320810671015 584149911994368 Bool.true 7829599743 34359738368 320707678957 584149911994368 (@Enclosure.Real.IsNear.mulLit_ff qz111 (Real.cos qz189) 87381 262144 1 262144 95661 131072 3652747 2228355072 8358953841 34359738368 320810671015 584149911994368 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz189) Bool.false 191322 262144 7305494 4456710144 95661 131072 3652747 2228355072 (ep634 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz111 (@Neg.neg Real Real.instNeg (Real.sin qz189)) 87381 262144 1 262144 89603 131072 3652747 2228355072 7829599743 34359738368 320707678957 584149911994368 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz189) Bool.false 89603 131072 3652747 2228355072 (@Enclosure.Real.IsNear.recentre' (Real.sin qz189) Bool.false 179206 262144 7305494 4456710144 89603 131072 3652747 2228355072 (ep636 rfl rfl) rfl)) rfl)

noncomputable def ep638 := @ep629 8358953841 34359738368 320810671015 584149911994368 Bool.true 7829599743 34359738368 320707678957 584149911994368 Bool.false 6144652919170085683200 178832936775 68719476736 7142931227099 1168299823988736 Bool.true 435438534245167923200 12672929275 68719476736 7119293376719 1168299823988736 EMRow11.d10 (ep630 ep637) rfl rfl

noncomputable abbrev qz190 := (@HMul.hMul Real Real Real qz253 qz355 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep639 := @Enclosure.Complex.IsNear.of_eq qz187 (Complex.mk (@HMul.hMul Real Real Real qz0 qz114 (Real.cos qz190)) (@HMul.hMul Real Real Real qz0 qz114 (@Neg.neg Real Real.instNeg (Real.sin qz190)))) Bool.false 10579895419 34359738368 152839940941 292074955997184 Bool.true 4949199591 68719476736 608035201213 1168299823988736 (BSN.cpow_neg_s_mk qz143 54675 1000 10 qz144 rfl)

noncomputable def ep640 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz116 54675 1000 0 1 10369891420296933 4503599627370496 500000000051003 17001000000000000000 22678952536189392471 180143985094819840 121500000012393729 75560000000000000000 qz145 (BSN.isNear_log_sfrac 10 1 10369891420296933 4503599627370496 500000000051003 17001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false 10873619265929276817408 4722366482869645213696 1000000000102006 34002000000000000000 10369891420296933 4503599627370496 500000000051003 17001000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 29247 131072 24973259072661432 36028797018963968 34002 1000000000000000 rfl rfl rfl rfl (ep317 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep641 := nat_lit 231547959564651294132825588670641

noncomputable def ep642 := BSN.cos_dyadic_bound_f 123355989 536870912 2 1 262144 68071 ep641 ep75 ep641 ep641 ep76 ep641 255254 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 123355989) qz268 0 1 ep641 ep75 ep641 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 123355989) qz269 0 1 ep641 ep76 ep641 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz386 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 33002219) qz30)

noncomputable def ep643 := @Enclosure.Real.IsNear.cos_image qz190 qz386 Bool.false 33002219 262144 423 262144 Bool.false 255254 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz190 Bool.false 22678952536189392471 180143985094819840 121500000012393729 75560000000000000000 33002219 262144 423 262144 (ep640 rfl) rfl) (Enclosure.sfrac_false_div 33002219 262144) (BSN.cos_reduce0 qz386 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8680406060161059258368) qz32) 226375608064910080 72057594037927936 Bool.false 255254 262144 20 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 33002219 262144 226375608064910080 72057594037927936 20 8680406060161059258368 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 255254 262144 8680406060161059258368 37778931862957161709568 123355989 536870912 68071 68004 (ep642 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep644 := BSN.sin_dyadic_bound_f 123355989 536870912 2 1 262144 68071 ep641 ep79 ep641 ep641 ep80 ep641 59703 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 123355989) qz274 0 1 ep641 ep79 ep641 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 123355989) qz275 0 1 ep641 ep80 ep641 rfl rfl rfl rfl) rfl rfl

noncomputable def ep645 := @Enclosure.Real.IsNear.sin_image qz190 qz386 Bool.false 33002219 262144 423 262144 Bool.false 59703 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz190 Bool.false 22678952536189392471 180143985094819840 121500000012393729 75560000000000000000 33002219 262144 423 262144 (ep640 rfl) rfl) (Enclosure.sfrac_false_div 33002219 262144) (BSN.sin_reduce0 qz386 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8680406060161059258368) qz32) 226375608064910080 72057594037927936 Bool.false 59703 262144 20 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q0 33002219 262144 226375608064910080 72057594037927936 20 8680406060161059258368 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 59703 262144 8680406060161059258368 37778931862957161709568 123355989 536870912 68071 68004 (ep644 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep646 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz114 (Real.cos qz190)) (@HMul.hMul Real Real Real qz0 qz114 (@Neg.neg Real Real.instNeg (Real.sin qz190))) Bool.false 10579895419 34359738368 152839940941 292074955997184 Bool.true 4949199591 68719476736 608035201213 1168299823988736 (@Enclosure.Real.IsNear.mulLit_ff qz114 (Real.cos qz190) 82897 262144 1 262144 127627 131072 7322495 4456710144 10579895419 34359738368 152839940941 292074955997184 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz190) Bool.false 255254 262144 14644990 8913420288 127627 131072 7322495 4456710144 (ep643 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz114 (@Neg.neg Real Real.instNeg (Real.sin qz190)) 82897 262144 1 262144 59703 262144 7322495 4456710144 4949199591 68719476736 608035201213 1168299823988736 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz190) Bool.false 59703 262144 7322495 4456710144 (@Enclosure.Real.IsNear.recentre' (Real.sin qz190) Bool.false 59703 262144 14644990 8913420288 59703 262144 7322495 4456710144 (ep645 rfl rfl) rfl)) rfl)

noncomputable def ep647 := @ep627 10579895419 34359738368 152839940941 292074955997184 Bool.true 4949199591 68719476736 608035201213 1168299823988736 Bool.false 6871697796285369155584 199992727613 68719476736 2584763663621 389433274662912 Bool.true 1210983474645881061376 8811064433 34359738368 643944048161 97358318665728 (ep628 (BSN.head_sum_c_succ qz134 9 10 rfl rfl) (ep638 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep639 ep646) rfl rfl

noncomputable def ep648 := @Enclosure.Complex.IsNear.mul qz184 (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))) Bool.false 91735778608741983119 1735592045696274923520 10482493433097131386439 ep501 Bool.false

noncomputable abbrev qz191 := (Complex.re qz384)

noncomputable abbrev qz192 := (Complex.im qz384)

noncomputable def ep649 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz191 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz192 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))))) 2186315907970165717 21694900571203436544 91972822621783761283

noncomputable def ep650 := nat_lit 663399531912862814973792352727478566912

noncomputable def ep651 := @Enclosure.Real.IsNear.mulLit_ff qz191 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))))) 3449182921 17179869184 145098468079 292074955997184 633864877

noncomputable abbrev qz387 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz432 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable abbrev qz193 := (Real.cos qz387)

noncomputable abbrev qz194 := (@Neg.neg Real Real.instNeg (Real.sin qz387))

noncomputable def ep652 := @Enclosure.Complex.IsNear.of_eq qz184 (Complex.mk (@HMul.hMul Real Real Real qz0 qz119 qz193) (@HMul.hMul Real Real Real qz0 qz119 qz194)) Bool.false 3449182921 17179869184 145098468079 292074955997184 Bool.false 15457894347 68719476736 580751182333 1168299823988736 (BSN.cpow_neg_s_mk qz143 54675 1000 11 qz144 rfl)

noncomputable def ep653 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz123 54675 1000 0 1 10799147631728357 4503599627370496 500000000051003 17001000000000000000 23617735870589916759 180143985094819840 121500000012393729 75560000000000000000 qz145 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 500000000051003 17001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz122) Bool.false 11323727027087193669632 4722366482869645213696 1000000000102006 34002000000000000000 10799147631728357 4503599627370496 500000000051003 17001000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 41740 131072 24973259072661432 36028797018963968 34002 1000000000000000 rfl rfl rfl rfl (ep338 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep654 := nat_lit 23421583345590454551249359055721201

noncomputable def ep655 := BSN.sin_dyadic_bound_f 391204699 536870912 2 1 262144 68071 ep654 ep79 ep654 ep654 ep80 ep654 174556 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 391204699) qz274 0 1 ep654 ep79 ep654 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 391204699) qz275 0 1 ep654 ep80 ep654 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz195 := qz387

noncomputable abbrev qz388 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 34368329) qz30)

noncomputable def ep656 := @Enclosure.Real.IsNear.cos_image qz195 qz388 Bool.false 34368329 262144 211 131072 Bool.false 174556 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz195 Bool.false 23617735870589916759 180143985094819840 121500000012393729 75560000000000000000 34368329 262144 211 131072 (ep653 rfl) rfl) (Enclosure.sfrac_false_div 34368329 262144) (BSN.cos_reduce3 qz388 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 27528583440765160521728) qz32) 226375608064910080 72057594037927936 Bool.false 174556 262144 20 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q3 34368329 262144 226375608064910080 72057594037927936 20 27528583440765160521728 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 174556 262144 27528583440765160521728 37778931862957161709568 391204699 536870912 68071 68004 (ep655 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep657 := BSN.cos_dyadic_bound_f 391204699 536870912 2 1 262144 68071 ep654 ep75 ep654 ep654 ep76 ep654 195573 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 391204699) qz268 0 1 ep654 ep75 ep654 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 391204699) qz269 0 1 ep654 ep76 ep654 rfl rfl rfl rfl) rfl rfl

noncomputable def ep658 := @Enclosure.Real.IsNear.sin_image qz195 qz388 Bool.false 34368329 262144 211 131072 Bool.true 195573 262144 1 34002 (@Enclosure.Real.IsNear.recentre' qz195 Bool.false 23617735870589916759 180143985094819840 121500000012393729 75560000000000000000 34368329 262144 211 131072 (ep653 rfl) rfl) (Enclosure.sfrac_false_div 34368329 262144) (BSN.sin_reduce3 qz388 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 27528583440765160521728) qz32) 226375608064910080 72057594037927936 Bool.false 195573 262144 20 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q3 34368329 262144 226375608064910080 72057594037927936 20 27528583440765160521728 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 195573 262144 27528583440765160521728 37778931862957161709568 391204699 536870912 68071 68004 (ep657 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz196 := (Real.sin qz387)

noncomputable def ep659 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz119 qz193) (@HMul.hMul Real Real Real qz0 qz119 qz194) Bool.false 3449182921 17179869184 145098468079 292074955997184 Bool.false 15457894347 68719476736 580751182333 1168299823988736 (@Enclosure.Real.IsNear.mulLit_ff qz119 qz193 79039 262144 1 262144 43639 65536 3652747 2228355072 3449182921 17179869184 145098468079 292074955997184 qz350 (@Enclosure.Real.IsNear.recentre' qz193 Bool.false 174556 262144 7305494 4456710144 43639 65536 3652747 2228355072 (ep656 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz119 qz194 79039 262144 1 262144 195573 262144 3652747 2228355072 15457894347 68719476736 580751182333 1168299823988736 qz350 (@Enclosure.Real.IsNear.neg qz196 Bool.true 195573 262144 3652747 2228355072 (@Enclosure.Real.IsNear.recentre' qz196 Bool.true 195573 262144 7305494 4456710144 195573 262144 3652747 2228355072 (ep658 rfl rfl) rfl)) rfl)

noncomputable def ep660 := @ep651 1262809416 0 1 2186315907970165717 21694900571203436544 91972822621783761283 368835004611029624684544 (@Enclosure.Complex.IsNear.re_isNear qz184 Bool.false 3449182921 17179869184 145098468079 292074955997184 Bool.false 15457894347 68719476736 580751182333 1168299823988736 (ep652 ep659))

noncomputable def ep661 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))) Bool.false 633864877 1262809416 0 1 Bool.false

noncomputable def ep662 := @Enclosure.Complex.IsNear.addLitP qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) Bool.false 4765769 9566738 0 1 Bool.true 962280

noncomputable def ep663 := @ep662 4783369 0 1 Bool.false 1 264 0 1 Bool.false 729 1760 0 1 Bool.false 1267729754 633864877 1262809416 0 1 Bool.false 1793463201 1793463201 8418729440 0 1

noncomputable abbrev qz197 := (@HDiv.hDiv Complex Complex Complex qz309 qz336 (@HSub.hSub Complex Complex Complex qz302 qz353 (1 : Complex)))

noncomputable def ep664 := @Enclosure.Complex.IsNear.addLitP qz197 qz78 Bool.true 22000000 11958422500 0 1 Bool.true 2405700000 11958422500 0 1

noncomputable def ep665 := @Enclosure.Complex.IsNear.of_eq qz197 (Complex.mk (Enclosure.sfrac Bool.true 22000000 11958422500) (Enclosure.sfrac Bool.true 2405700000 11958422500)) Bool.true 22000000 11958422500 0 1 Bool.true 2405700000 11958422500 0 1

noncomputable def ep666 := @ep664 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 11914422500 4765769 9566738 0 1 Bool.true 2405700000 962280 4783369 0 1 (ep665 (BSN.N_div_s_sub_one_mk qz143 54675 1000 11 qz144 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 22000000 11958422500) (Enclosure.sfrac Bool.true 2405700000 11958422500) Bool.true 22000000 11958422500 0 1 Bool.true 2405700000 11958422500 0 1 (Enclosure.Real.IsNear.const Bool.true 22000000 11958422500) (Enclosure.Real.IsNear.const Bool.true 2405700000 11958422500))) qz79 rfl

noncomputable def ep667 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) qz128)) Bool.false 1 264 0 1

noncomputable def ep668 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) qz128) Bool.false 0 1 0 1 Bool.false

noncomputable def ep669 := @ep668 0 1 0 1 Bool.false 1 264 0 1 Bool.false 729 1760 0 1 Bool.false 1 1 264 0 1 Bool.false 729 729 1760 0

noncomputable def ep670 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (Complex.mk qz17 qz17) Bool.false 0 1 0 1 Bool.false

noncomputable def ep671 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) qz128 Bool.false 1 264 0 1 Bool.false 729 1760 0 1

noncomputable def ep672 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)))) qz130) 1 264 0 1 0 1 0

noncomputable def ep673 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129 1 24 0 1 1 11 0 1 1

noncomputable def ep674 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep675 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep676 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)) qz134 Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 (BSN.ascPochhammer_one_eval qz134)

noncomputable def ep677 := ep676 (@Enclosure.Complex.IsNear.of_eq qz134 (Complex.mk qz73 qz143) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 (BSN.s_crit_mk qz143 Bool.false 54675 1000 qz144) (@Enclosure.Complex.IsNear.mk qz73 qz143 Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 qz318 qz145))

noncomputable def ep678 := @ep675 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep366) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep677)

noncomputable def ep679 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 54675 1000 0 1 0 1 0

noncomputable def ep680 := @ep679 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep366) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep677)

noncomputable def ep681 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)))) 729 160 0 1 0 1 0 1 729

noncomputable def ep682 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 54675 1000 0 1 729 160 0

noncomputable def ep683 := @ep682 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep366) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep677)

noncomputable def ep684 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep685 := @ep684 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep366) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep677)

noncomputable def ep686 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 729 160 0 1 (@ep674 1 24 0 1 (ep678 rfl) (ep680 rfl) rfl rfl) (@ep681 729 160 0 1 (ep683 rfl) (ep685 rfl) rfl rfl)

noncomputable def ep687 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 729 160 0 1 ep686

noncomputable def ep688 := @ep673 264 0 1 ep687 qz131

noncomputable def ep689 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)))) qz130 729 160 0 1 0 1 0 1 0

noncomputable def ep690 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 729 160 0 1 ep686

noncomputable def ep691 := @ep689 1 0 1 ep690 qz132

noncomputable def ep692 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)))) qz130) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129) 0 1 0 1 729 1760 0

noncomputable def ep693 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)))) qz130 1 24 0 1 0 1 0 1 0

noncomputable def ep694 := @ep693 1 0 1 ep687 qz132

noncomputable def ep695 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz80)) ↑qz127) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129 729 160 0 1 1 11 0 1 729

noncomputable def ep696 := @ep695 1760 0 1 ep690 qz131

noncomputable def ep697 := @ep669 1 (@ep670 0 1 0 1 (BSN.bern_sum_base qz134 11) qz95) (ep671 (@ep672 1 1 1 264 0 1 (ep688 rfl) (ep691 rfl) rfl rfl) (@ep692 1 729 729 1760 0 1 (ep694 rfl) (ep696 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep698 := ep663 (ep666 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep667 Bool.false 729 1760 0 1 (BSN.bern_sum_succ qz134 11 0 1 1 rfl rfl) (ep697 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep699 := @Enclosure.Real.IsNear.mulLit_ff qz192 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))))) 15457894347 68719476736 580751182333 1168299823988736 1793463201

noncomputable def ep700 := @ep699 8418729440 0 1 27723164676290424747 578530681898758307840 115728430494608536437 1092844458106754443509760 (@Enclosure.Complex.IsNear.im_isNear qz184 Bool.false 3449182921 17179869184 145098468079 292074955997184 Bool.false 15457894347 68719476736 580751182333 1168299823988736 (ep652 ep659))

noncomputable def ep701 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))) Bool.false 633864877 1262809416 0 1 Bool.false

noncomputable def ep702 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz191 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz192 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1))))))) 6185982642331190121 144632670474689576960 28914307002351073431

noncomputable def ep703 := nat_lit 1475340018444118498738176

noncomputable def ep704 := nat_lit 651319767548868393924522599778470592512

noncomputable def ep705 := @Enclosure.Real.IsNear.mulLit_ff qz191 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))))) 3449182921 17179869184 145098468079 292074955997184 1793463201

noncomputable def ep706 := @ep705 8418729440 0 1 6185982642331190121 144632670474689576960 28914307002351073431 273211114526688610877440 (@Enclosure.Complex.IsNear.re_isNear qz184 Bool.false 3449182921 17179869184 145098468079 292074955997184 Bool.false 15457894347 68719476736 580751182333 1168299823988736 (ep652 ep659))

noncomputable def ep707 := @Enclosure.Real.IsNear.mulLit_ff qz192 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz185 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz57 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz57 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz106 qz107 (@HSub.hSub Nat Nat Nat qz105 (@HMul.hMul Nat Nat Nat qz57 2 k) 1)))))) 15457894347 68719476736 580751182333 1168299823988736 633864877

noncomputable def ep708 := @ep707 1262809416 0 1 3266072099646716773 28926534094937915392 368117776757111618041 ep703 (@Enclosure.Complex.IsNear.im_isNear qz184 Bool.false 3449182921 17179869184 145098468079 292074955997184 Bool.false 15457894347 68719476736 580751182333 1168299823988736 (ep652 ep659))

noncomputable abbrev qz389 := (ep698 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep709 := @ep648 11258171570282386993 72316335237344788480 1310637586424518536421 ep619 (@ep649 368835004611029624684544 27723164676290424747 578530681898758307840 115728430494608536437 1092844458106754443509760 ep650 91735778608741983119 1735592045696274923520 10482493433097131386439 ep501 (ep660 (@ep661 1793463201 8418729440 0 1 qz389) rfl) (ep700 (@ep701 1793463201 8418729440 0 1 qz389) rfl) rfl rfl) (@ep702 273211114526688610877440 3266072099646716773 28926534094937915392 368117776757111618041 ep703 ep704 11258171570282386993 72316335237344788480 1310637586424518536421 ep619 (ep706 (@ep701 1793463201 8418729440 0 1 qz389) rfl) (ep708 (@ep661 1793463201 8418729440 0 1 qz389) rfl) rfl rfl)

noncomputable def ep710 := @ep624 25705995808270567055701 ep619 (@ep625 97358318665728 (BSN.head_sum_c_eq qz134 11) (ep626 (BSN.head_sum_c_succ qz134 10 11 rfl rfl) (ep647 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep709 rfl rfl rfl

noncomputable def ep711 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz134 1 11) Bool.false 5142789769833134063279 1735592045696274923520 206326326986412458706599 ep501 Bool.true 7286320314676114887 72316335237344788480 25705995808270567055701 ep619 (@ep620 ep501 Bool.true 7286320314676114887 72316335237344788480 25705995808270567055701 ep619 (BSN.zetaApproximant_eq_folded' qz134 1 11 rfl) (ep710 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep712 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) (Complex.im (zetaApproximant qz134 1 11)) 65 262144 3140249

noncomputable def ep713 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154)) Bool.true 65 262144 6280498

noncomputable def ep714 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154) qz368 Bool.false 8235431 262144 177

noncomputable def ep715 := nat_lit 70801227918644444144509104036795519577843393185482089262701005356400170401

noncomputable def ep716 := nat_lit 211892715323155995182856145719146680934146744758002319865638045695144940961

noncomputable def ep717 := BSN.cos_dyadic_bound_f 843180413 536870912 3 2 262144 68071 ep715 ep57 ep615 ep716 ep60 ep615 65 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 843180413) qz268 0 2 ep715 ep57 ep615 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 843180413) qz269 0 2 ep716 ep60 ep615 rfl rfl rfl rfl) rfl rfl

noncomputable def ep718 := @ep714 262144 Bool.true 65 262144 1 34002 (@ep505 8235431 262144 177 262144 ep613 rfl) (Enclosure.sfrac_false_div 8235431 262144) (BSN.sin_reduce3 qz368 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59333546839945827581952) qz32) 226375608064910080 72057594037927936 Bool.false 65 262144 4 1000000000000000 68004 34002 (BSN.sin_reduce_arg_pos_rat_q3 8235431 262144 226375608064910080 72057594037927936 4 59333546839945827581952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 65 262144 59333546839945827581952 37778931862957161709568 843180413 536870912 68071 68004 (ep717 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep719 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz134 1 11) Bool.false 5142789769833134063279 1735592045696274923520 206326326986412458706599 ep501 Bool.true 7286320314676114887 72316335237344788480 25705995808270567055701 ep619 (@ep620 ep501 Bool.true 7286320314676114887 72316335237344788480 25705995808270567055701 ep619 (BSN.zetaApproximant_eq_folded' qz134 1 11 rfl) (ep710 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow11.d11 : Enclosure.Real.IsNear (hardyZApproximantEM 1 11 qz143) Bool.false ep487 ep488 ep489 ep490 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 11 qz143) ep491 Bool.false ep487 ep488 ep489 ep490 (@Eq.refl Real ep491) (@ep492 Bool.false ep487 ep488 ep489 ep490 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz49 (Complex.im (@HSub.hSub Complex Complex Complex qz50 qz152 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz153 (@Nat.cast Complex Complex.instNatCast j))))) qz154) (zetaApproximant qz134 1 11)) (@ep494 ep488 ep495 ep490 94722164090789493531 ep496 ep497 ep498 ep499 ep487 ep488 ep489 ep490 (@ep500 4456710144 5142789769833134063279 1735592045696274923520 206326326986412458706599 ep501 ep493 ep488 ep495 ep490 (@ep502 8913420288 262143 262144 3140249 4456710144 (ep618 rfl rfl) rfl) ep711 rfl) (@ep712 4456710144 7286320314676114887 72316335237344788480 25705995808270567055701 ep619 94722164090789493531 ep496 ep497 ep498 (@ep713 8913420288 65 262144 3140249 4456710144 (ep718 rfl rfl) rfl) ep719 rfl) rfl rfl))

theorem EMRow11.d12 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow11.d13 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow11.d14 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow11.d15 : @Eq Nat (Nat.pow 11 (Nat.succ (Nat.mul 2 3))) 19487171 := @Eq.refl Nat 19487171

noncomputable abbrev qz435 := (@HAdd.hAdd Complex Complex Complex qz438 qz437 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz390 := qz435

noncomputable abbrev qz198 := (@HDiv.hDiv Real Real Real qz256 (@Norm.norm Complex Complex.instNorm qz390) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz258) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz199 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz200 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz391 := (@HPow.hPow Complex Complex Complex qz416 qz429 (@HSub.hSub Complex Complex Complex qz422 qz417 qz418))

noncomputable abbrev qz201 := qz391

noncomputable def ep720 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 1 11))) (@HMul.hMul Real Real Real qz0 qz198 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) 911563583 28991029248 3053101 28991029248 636850839925667 985162418487296 1446906493

noncomputable def ep721 := nat_lit 19360999510931603124649984

noncomputable def ep722 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 1 11)) 6641 442368 1 442368 137263 65536 439 65536 911563583 28991029248

noncomputable abbrev qz392 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz202 := (@HPow.hPow Real Nat Real qz392 qz257 2)

noncomputable def ep723 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz202) 96 162 0 1 6641 262144 1 262144 6641 442368 1 442368

noncomputable def ep724 := nat_lit 781950621441006189802102638025

noncomputable def ep725 := nat_lit 19807040628566084398385987584

noncomputable def ep726 := nat_lit 26986075409044041160201671

noncomputable def ep727 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz203 := qz257

noncomputable abbrev qz393 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz203 1)

noncomputable def ep728 := @Enclosure.Real.IsNear.mulLit_ff qz393 qz203 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep724 ep725 ep726 ep727

noncomputable def ep729 := ep728 (@Enclosure.Real.IsNear.of_eq qz393 qz203 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz203) (@Enclosure.Real.IsNear.of_eq qz203 qz254 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz255)) (@Enclosure.Real.IsNear.of_eq qz203 qz254 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz255) rfl

noncomputable def ep730 := @Enclosure.Real.IsNear.inv_image qz202 ep724 ep725 ep726 ep727 3320 3321 131072 (@Enclosure.Real.IsNear.of_eq qz202 (@HMul.hMul Real Real Real qz0 qz393 qz203) Bool.false ep724 ep725 ep726 ep727 (BSN.pow_succ_r qz203 1 2 rfl) ep729) rfl rfl rfl

noncomputable def ep731 := ep723 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz202) Bool.false 6641 262144 1 262144 6641 262144 1 262144 (ep730 rfl rfl rfl) rfl)

noncomputable def ep732 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 1 11)) (Real.sqrt (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 1 11)) (Complex.re (zetaApproximant qz12 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 1 11)) (Complex.im (zetaApproximant qz12 1 11))))) Bool.false 137263 65536 439 65536

noncomputable def ep733 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 1 11)) (Complex.re (zetaApproximant qz12 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 1 11)) (Complex.im (zetaApproximant qz12 1 11))))) Bool.false 549052 262144 1756 262144

noncomputable def ep734 := nat_lit 1677371736677533816698249393709900666829

noncomputable def ep735 := nat_lit 382364663058100072389014479437824000000

noncomputable def ep736 := nat_lit 18668631874551950751612024202446149187590758579229557571

noncomputable def ep737 := nat_lit 665582484762358059976516459892858852167519121178624000000

noncomputable def ep738 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 1 11)) (Complex.re (zetaApproximant qz12 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 1 11)) (Complex.im (zetaApproximant qz12 1 11)))) ep734 ep735 ep736 ep737 273648 275404

noncomputable def ep739 := nat_lit 44891267381743488476093950831831043603769665889

noncomputable def ep740 := nat_lit 10234589586301271792841446665690746915389440000

noncomputable def ep741 := nat_lit 736917245339785564862186791874346238610836508835620203

noncomputable def ep742 := nat_lit 26623299390494322399060658395714354086700764847144960000

noncomputable def ep743 := nat_lit 20068863863153288818432653131623307715049

noncomputable def ep744 := nat_lit 33040384769825903256848678543681388544000000

noncomputable def ep745 := nat_lit 15356296316081976878584650349218326394990366146190781

noncomputable def ep746 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 1 11)) (Complex.re (zetaApproximant qz12 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 1 11)) (Complex.im (zetaApproximant qz12 1 11))) ep739 ep740 ep741 ep742 ep743 ep744 ep745

noncomputable def ep747 := nat_lit 41598905297647378748532278743303678260469945073664000000

noncomputable def ep748 := nat_lit 1483430143683042635806567515381077786357993387692579232888077176645989875455252559298560000

noncomputable def ep749 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz12 1 11)) (Complex.re (zetaApproximant qz12 1 11)) 211875594115375847542833 101166148420809575628800 ep160 ep161 211875594115375847542833 101166148420809575628800 ep160 ep161 ep739

noncomputable def ep750 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz12 1 11)) (Complex.im (zetaApproximant qz12 1 11)) 141664617541407596243 5748076614818725888000 ep290 ep291 141664617541407596243 5748076614818725888000 ep290 ep291 ep743

noncomputable def ep751 := @ep720 985162418487296 ep721 18031335911649841 26599385299156992 2840298855215 26599385299156992 (@ep722 3053101 28991029248 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz202)) Bool.false 6641 442368 1 442368 (BSN.theta_err_eq 1 2 96 162 EMRow11.d12 EMRow11.d13 rfl) (ep731 rfl)) (ep732 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz12 1 11)) (@ep733 137263 65536 439 65536 (@ep738 131072 (@ep746 ep747 ep748 ep734 ep735 ep736 ep737 (@ep749 ep740 ep741 ep742 ep403 ep403 rfl) (@ep750 ep744 ep745 ep747 ep409 ep409 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz204 := (@Norm.norm Complex Complex.instNorm qz390)

noncomputable abbrev qz394 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep752 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz198 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz204 qz394) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) Bool.false 636850839925667 985162418487296 1446906493 985162418487296 (BSN.zrb_shape_eq qz204 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) qz20 3)

noncomputable def ep753 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz204 qz394) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) 13592759 917504 1 917504 46852213 1073741824 103 1073741824

noncomputable def ep754 := @Enclosure.Real.IsNear.mulLit_ff qz204 qz394 13592759 262144 1 262144 2 7 0 1 13592759 917504

noncomputable abbrev qz395 := (Complex.re qz435)

noncomputable abbrev qz396 := (Complex.im qz435)

noncomputable abbrev qz205 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz253 qz395 qz395) (@HMul.hMul Real Real Real qz253 qz396 qz396))

noncomputable abbrev qz206 := qz390

noncomputable def ep755 := @Enclosure.Real.IsNear.of_eq qz204 (Real.sqrt qz205) Bool.false 13592759 262144 1 262144 (BSN.norm_eq_sqrt_mul_add qz206)

noncomputable def ep756 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz205) Bool.false 13592759 262144 1 262144 13592759

noncomputable def ep757 := @Enclosure.Real.IsNear.sqrt_image qz205 672164189 250000 0 1 6796379 6796380 131072

noncomputable abbrev qz207 := (@HMul.hMul Real Real Real qz253 qz395 qz395)

noncomputable abbrev qz208 := (@HMul.hMul Real Real Real qz253 qz396 qz396)

noncomputable def ep758 := @Enclosure.Real.IsNear.addLit_ff qz207 qz208 49 4 0 1 669101689 250000 0 1

noncomputable abbrev qz209 := qz395

noncomputable def ep759 := @Enclosure.Real.IsNear.mulLit_ff qz209 qz209 7 2 0 1 7 2 0 1 49 4

noncomputable def ep760 := @Enclosure.Complex.IsNear.of_eq qz206 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz20) Bool.false 7 2 0 1 Bool.false 51734 1000 0 1 (BSN.s_add_nat_mk qz20 Bool.false 51734 1000 3 qz21)

noncomputable abbrev qz210 := (ep760 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz266 Bool.false 7 2 0 1 Bool.false 51734 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz270))

noncomputable def ep761 := @ep759 0 1 (@Enclosure.Complex.IsNear.re_isNear qz206 Bool.false 7 2 0 1 Bool.false 51734 1000 0 1 qz210)

noncomputable def ep762 := ep761 (@Enclosure.Complex.IsNear.re_isNear qz206 Bool.false 7 2 0 1 Bool.false 51734 1000 0 1 qz210)

noncomputable abbrev qz211 := qz396

noncomputable def ep763 := @Enclosure.Real.IsNear.mulLit_ff qz211 qz211 51734 1000 0 1 51734 1000 0 1 669101689 250000

noncomputable def ep764 := @ep763 0 1 (@Enclosure.Complex.IsNear.im_isNear qz206 Bool.false 7 2 0 1 Bool.false 51734 1000 0 1 qz210)

noncomputable def ep765 := ep764 (@Enclosure.Complex.IsNear.im_isNear qz206 Bool.false 7 2 0 1 Bool.false 51734 1000 0 1 qz210)

noncomputable def ep766 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Real.sqrt (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))))) Bool.false 46852213 1073741824

noncomputable def ep767 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))))) Bool.false 93704426 2147483648

noncomputable def ep768 := nat_lit 20499580444203159300560963631791409757534915234741553833

noncomputable def ep769 := nat_lit 10766746765857818570520837188270791065600000000000000000000

noncomputable def ep770 := nat_lit 5547061946809801737048856223615846188449149305584207483064399919003

noncomputable def ep771 := nat_lit 667075383478524074104146186673063403172407658019395993600000000000000000000

noncomputable def ep772 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)))) ep768 ep769 ep770 ep771

noncomputable def ep773 := nat_lit 20454825938508997852139947547860526525553384967448248729

noncomputable def ep774 := nat_lit 5502460470445794156890811545709922915517805858941602643291188397851

noncomputable def ep775 := nat_lit 310795178431676725145945027297800222093960189536841

noncomputable def ep776 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) ep773 ep769 ep774 ep771 ep775

noncomputable def ep777 := nat_lit 74769074762901517850839147140769382400000000000000000000

noncomputable def ep778 := nat_lit 348449034093809219984724046140025569776120676895350310728215009

noncomputable def ep779 := nat_lit 5211526433425969328938642083383307837284434828276531200000000000000000000

noncomputable def ep780 := nat_lit 1532734662840739924965400559776749206984949379202315606489925022371196853755220007687762739200000000000000000000

noncomputable def ep781 := nat_lit 4522701177229045922116587973

noncomputable def ep782 := nat_lit 103762935414616227840000000000

noncomputable def ep783 := nat_lit 2443899610194352780228486880617

noncomputable def ep784 := nat_lit 25827802529029140656884285440000000000

noncomputable def ep785 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) ep781 ep782 ep783 ep784 ep781 ep782 ep783

noncomputable def ep786 := nat_lit 17629383949295469500664221

noncomputable def ep787 := nat_lit 8646911284551352320000000000

noncomputable def ep788 := nat_lit 26468779712558534833792395937

noncomputable def ep789 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201) Bool.true ep781 ep782 ep783 ep784 Bool.false ep786 ep787 ep788

noncomputable def ep790 := nat_lit 1614237658064321291055267840000000000

noncomputable def ep791 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201 Bool.true ep781 ep782 ep783 ep784 Bool.false ep786 ep787 ep788 ep790

noncomputable def ep792 := nat_lit 23058430092136939520000000

noncomputable def ep793 := nat_lit 12324509317910676307912189

noncomputable def ep794 := nat_lit 17218535019352760437922856960000000

noncomputable def ep795 := nat_lit 4506903415123787408884826473

noncomputable def ep796 := nat_lit 2425412846217486765766618597117

noncomputable abbrev qz212 := (Complex.re qz391)

noncomputable abbrev qz213 := (Complex.im qz391)

noncomputable def ep797 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz212) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz213) 3510613801168558495947 ep792 ep793 ep794 ep795 ep782 ep796

noncomputable def ep798 := nat_lit 104286388922761394195296200927621086457060392960000000

noncomputable def ep799 := nat_lit 143487791827939670316023808

noncomputable def ep800 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz212 2006992567 120000000 0 1 5247573696423 576460752303423488 6140784734610667 ep799 3510613801168558495947

noncomputable def ep801 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) 2006992567 120000000 0 1 0 1 0 1 2006992567

noncomputable def ep802 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 6020977701 500000 0 1 2006992567 120000000 0

noncomputable def ep803 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz17) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow11.d14 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz17 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz26)

noncomputable abbrev qz397 := (@HAdd.hAdd Complex Complex Complex qz415 qz414 qz419)

noncomputable abbrev qz214 := qz397

noncomputable def ep804 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz48 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) qz214) Bool.true 6020977701 500000 0 1 Bool.true 17270469576863 125000000 0 1

noncomputable abbrev qz215 := (Complex.re qz397)

noncomputable abbrev qz216 := (Complex.im qz397)

noncomputable def ep805 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz215) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz216) 668914189 100000 0 1 669101689 125000 0 1

noncomputable def ep806 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz215 668914189 250000 0 1 5 2 0 1 668914189 100000

noncomputable abbrev qz398 := (@HAdd.hAdd Complex Complex Complex qz415 qz414 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz217 := qz398

noncomputable def ep807 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz48 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz217) Bool.true 668914189 250000 0 1 Bool.false 25867 250 0 1

noncomputable abbrev qz218 := (Complex.re qz398)

noncomputable abbrev qz219 := (Complex.im qz398)

noncomputable def ep808 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz218) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz219) 3 4 0 1 669101689 250000 0 1

noncomputable def ep809 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz218 1 2 0 1 3 2 0 1 3 4

noncomputable def ep810 := @ep809 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep368)

noncomputable def ep811 := @Enclosure.Complex.IsNear.of_eq qz217 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz20) Bool.false 3 2 0 1 Bool.false 51734 1000 0 1 (BSN.s_add_nat_mk qz20 Bool.false 51734 1000 1 qz21)

noncomputable abbrev qz220 := (ep811 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz266 Bool.false 3 2 0 1 Bool.false 51734 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz270))

noncomputable def ep812 := ep810 (@Enclosure.Complex.IsNear.re_isNear qz217 Bool.false 3 2 0 1 Bool.false 51734 1000 0 1 qz220)

noncomputable def ep813 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz219 51734 1000 0 1 51734 1000 0 1 669101689 250000

noncomputable def ep814 := @ep813 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep368)

noncomputable def ep815 := ep814 (@Enclosure.Complex.IsNear.im_isNear qz217 Bool.false 3 2 0 1 Bool.false 51734 1000 0 1 qz220)

noncomputable def ep816 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz217 Bool.true 668914189 250000 0 1 Bool.false 25867 250 0 1 (@ep808 2675656756 668914189 250000 0 1 (ep812 rfl) (ep815 rfl) rfl rfl)

noncomputable def ep817 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz219) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz218) 25867 1000 0 1 77601 1000 0 1

noncomputable def ep818 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz219 1 2 0 1 51734 1000 0 1 25867 1000

noncomputable def ep819 := @ep818 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep368)

noncomputable def ep820 := ep819 (@Enclosure.Complex.IsNear.im_isNear qz217 Bool.false 3 2 0 1 Bool.false 51734 1000 0 1 qz220)

noncomputable def ep821 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz218 51734 1000 0 1 3 2 0 1 77601 1000

noncomputable def ep822 := @ep821 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 51734 1000 0 1 ep368)

noncomputable def ep823 := ep822 (@Enclosure.Complex.IsNear.re_isNear qz217 Bool.false 3 2 0 1 Bool.false 51734 1000 0 1 qz220)

noncomputable abbrev qz221 := (ep807 (BSN.ascPochhammer_succ_eval_c 1 2 qz258 rfl) (ep816 (@ep817 103468000 25867 250 0 1 (ep820 rfl) (ep823 rfl) rfl rfl)))

noncomputable def ep824 := @ep806 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 668914189 250000 0 1 Bool.false 25867 250 0 1 qz221)

noncomputable def ep825 := @Enclosure.Complex.IsNear.of_eq qz214 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz20) Bool.false 5 2 0 1 Bool.false 51734 1000 0 1 (BSN.s_add_nat_mk qz20 Bool.false 51734 1000 2 qz21)

noncomputable abbrev qz222 := (ep825 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz266 Bool.false 5 2 0 1 Bool.false 51734 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz270))

noncomputable def ep826 := ep824 (@Enclosure.Complex.IsNear.re_isNear qz214 Bool.false 5 2 0 1 Bool.false 51734 1000 0 1 qz222)

noncomputable def ep827 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz216 25867 250 0 1 51734 1000 0 1 669101689 125000

noncomputable def ep828 := @ep827 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 668914189 250000 0 1 Bool.false 25867 250 0 1 qz221)

noncomputable def ep829 := ep828 (@Enclosure.Complex.IsNear.im_isNear qz214 Bool.false 5 2 0 1 Bool.false 51734 1000 0 1 qz222)

noncomputable def ep830 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) qz214 Bool.true 6020977701 500000 0 1 Bool.true 17270469576863 125000000 0 1 (@ep805 150524442525000 6020977701 500000 0 1 (ep826 rfl) (ep829 rfl) rfl rfl)

noncomputable def ep831 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz216) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz215) 17302803326863 125000000 0 1 25867 100 0 1

noncomputable def ep832 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz216 668914189 250000 0 1 51734 1000 0 1 17302803326863 125000000

noncomputable def ep833 := @ep832 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 668914189 250000 0 1 Bool.false 25867 250 0 1 qz221)

noncomputable def ep834 := ep833 (@Enclosure.Complex.IsNear.im_isNear qz214 Bool.false 5 2 0 1 Bool.false 51734 1000 0 1 qz222)

noncomputable def ep835 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) qz215 25867 250 0 1 5 2 0 1 25867 100

noncomputable def ep836 := @ep835 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 668914189 250000 0 1 Bool.false 25867 250 0 1 qz221)

noncomputable def ep837 := ep836 (@Enclosure.Complex.IsNear.re_isNear qz214 Bool.false 5 2 0 1 Bool.false 51734 1000 0 1 qz222)

noncomputable abbrev qz223 := (ep804 (BSN.ascPochhammer_succ_eval_c 2 3 qz258 rfl) (ep830 (@ep831 1727046957686300 17270469576863 125000000 0 1 (ep834 rfl) (ep837 rfl) rfl rfl)))

noncomputable def ep838 := @ep802 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep803) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6020977701 500000 0 1 Bool.true 17270469576863 125000000 0 1 qz223)

noncomputable def ep839 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 17270469576863 125000000 0 1 0 1 0

noncomputable def ep840 := @ep839 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep803) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6020977701 500000 0 1 Bool.true 17270469576863 125000000 0 1 qz223)

noncomputable def ep841 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) 17270469576863 90000000000 0 1 0 1 0 1 17270469576863

noncomputable def ep842 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 17270469576863 125000000 0 1 17270469576863 90000000000 0

noncomputable def ep843 := @ep842 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep803) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6020977701 500000 0 1 Bool.true 17270469576863 125000000 0 1 qz223)

noncomputable def ep844 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 6020977701 500000 0 1 0 1 0

noncomputable def ep845 := @ep844 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep803) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6020977701 500000 0 1 Bool.true 17270469576863 125000000 0 1 qz223)

noncomputable def ep846 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 2006992567 120000000 0 1 Bool.false 17270469576863 90000000000 0 1 (@ep801 2006992567 120000000 0 1 (ep838 rfl) (ep840 rfl) rfl rfl) (@ep841 17270469576863 90000000000 0 1 (ep843 rfl) (ep845 rfl) rfl rfl)

noncomputable def ep847 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2006992567 120000000 0 1 Bool.false 17270469576863 90000000000 0 1 ep846

noncomputable def ep848 := nat_lit 286975583655879340632047616

noncomputable def ep849 := @Enclosure.Complex.IsNear.re_isNear qz201 Bool.true 5247573696423 576460752303423488 6140784734610667 ep799 Bool.false 260960096948471 1152921504606846976 140436994803359459 ep848

noncomputable abbrev qz399 := (@Nat.cast Real Real.instNatCast 19487171)

noncomputable abbrev qz224 := (@Inv.inv Real Real.instInv (Real.sqrt qz399))

noncomputable def ep850 := @Enclosure.Complex.IsNear.of_eq qz201 (Complex.mk (@HMul.hMul Real Real Real qz0 qz224 qz120) (@HMul.hMul Real Real Real qz0 qz224 qz121)) Bool.true 5247573696423 576460752303423488 6140784734610667 ep799 Bool.false 260960096948471 1152921504606846976 140436994803359459

noncomputable abbrev qz225 := (Real.sqrt qz399)

noncomputable def ep851 := @Enclosure.Real.IsNear.inv_image qz225 9479911077611 2147483648 1 2147483648 243234 243235 1073741824 (@Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz399 qz22)) Bool.false 9479911077611 2147483648 1 2147483648 (BSN.sqrt_natCast_div_one 19487171) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz399 qz22)) Bool.false 9479911077611 2147483648 1 2147483648 9479911077611 2147483648 1 2147483648 (BSN.sqrt_enclosure 19487171 1 4739955538805 4739955538806 1073741824 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep852 := nat_lit 124455820500000000000000000

noncomputable def ep853 := nat_lit 92764080252577317623169024

noncomputable def ep854 := nat_lit 38685626227668133590597632

noncomputable def ep855 := BSN.log_dyadic_bound 3 19 6 5 63732433749841395 1073741824 497823282 537698765144529 55801305 341937090 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 3) (BSN.artanhQ 19) 0 5 537698765144529 63732433749841395 55801305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep856 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz123 51734 1000 0 1 10799160256583397 4503599627370496 500000746734923 248911641000000000000000 279341878357042730199 2251799813685248000 12933519315792253241 ep852 qz25 (BSN.isNear_log_sfrac 11 1 10799160256583397 4503599627370496 500000746734923 248911641000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz122) Bool.false ep853 ep854 1000001493469846 497823282000000000000000 10799160256583397 4503599627370496 500000746734923 248911641000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 341937090 1073741824 24973259072661432 36028797018963968 497823282 1000000000000000 rfl rfl rfl rfl (ep855 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep857 := nat_lit 473697925395543890277171200

noncomputable def ep858 := nat_lit 309485009821345068724781056

noncomputable def ep859 := nat_lit 5755832395196602538607613296454508186038450188279521161437803998500484461026008536538623333869753351943074337851669309263112519971151814302523048060490231054336

noncomputable def ep860 := nat_lit 25087349417715593433012958174142958689126641386910427249058555817347792676670613748293986999300093003550818609852734049752458890129433227026772000655283952025600

noncomputable def ep861 := nat_lit 8658849393474002540778769845719567678768647755596692187448272243484523966329475582582175836559363199161353084643244858827729694653698029629041486443053056

noncomputable def ep862 := nat_lit 34842869371373434882131557070381171793203112575834849108379681960961208809004001990007330185985454217560988191639450244820810481443369743143943276589243579760640

noncomputable def ep863 := nat_lit 2282948797012119002404179193847009240710524366208848879664328579378649133577025851094752816936308463323124493496598798527473759001778423659436252059630839634329600

noncomputable def ep864 := BSN.cos_dyadic_bound_f 6731652396688 4398046511104 4 3 2147483648 996618876 ep859 ep860 ep861 ep862 ep863 ep861 86296536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6731652396688) (BSN.cosEvenQ 4398046511104) 0 3 ep859 ep860 ep861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6731652396688) (BSN.cosOddQ 4398046511104) 0 3 ep862 ep863 ep861 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz400 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 266401174885) (@Nat.cast Real Real.instNatCast 2147483648))

noncomputable def ep865 := @Enclosure.Real.IsNear.cos_image qz124 qz400 Bool.false 266401174885 2147483648 7 67108864 Bool.true 86296536 2147483648 1 497823282 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 279341878357042730199 2251799813685248000 12933519315792253241 ep852 266401174885 2147483648 7 67108864 (ep856 rfl) rfl) (Enclosure.sfrac_false_div 266401174885 2147483648) (BSN.cos_reduce2 qz400 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep857) (@Nat.cast Real Real.instNatCast ep858)) 226375608064910080 72057594037927936 Bool.false 86296536 2147483648 19 1000000000000000 995646564 497823282 (BSN.sin_reduce_arg_pos_rat_q2 266401174885 2147483648 226375608064910080 72057594037927936 19 ep857 ep858 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 86296536 2147483648 ep857 ep858 6731652396688 4398046511104 996618876 995646564 (ep864 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep866 := nat_lit 14943492291071462684697132091699789211547709372477312470430053557333566233058127383367860072827598062893697370590819620910950595400007551777899253395410812665856

noncomputable def ep867 := nat_lit 326135542430302714629168456263858462958646338029835554237761225625521304796717978727821830990901209046160641928085542646781965571682631951348036008518691376332800

noncomputable def ep868 := nat_lit 74633747865693497692535462579362053712570655314472455622605943524023001673488060772569314607300285742467505379315407800283669223654648409697190135669459848790016

noncomputable def ep869 := nat_lit 11414743985060595012020895969235046203552621831044244398321642896893245667885129255473764084681542316615622467482993992637368795008892118297181260298154198171648000

noncomputable def ep870 := BSN.sin_dyadic_bound_f 6731652396688 4398046511104 4 3 2147483648 996618876 ep866 ep867 ep861 ep868 ep869 ep861 2145749036 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 6731652396688) (BSN.sinEvenQ 4398046511104) 0 3 ep866 ep867 ep861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 6731652396688) (BSN.sinOddQ 4398046511104) 0 3 ep868 ep869 ep861 rfl rfl rfl rfl) rfl rfl

noncomputable def ep871 := @Enclosure.Real.IsNear.sin_image qz124 qz400 Bool.false 266401174885 2147483648 7 67108864 Bool.true 2145749036 2147483648 1 497823282 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 279341878357042730199 2251799813685248000 12933519315792253241 ep852 266401174885 2147483648 7 67108864 (ep856 rfl) rfl) (Enclosure.sfrac_false_div 266401174885 2147483648) (BSN.sin_reduce2 qz400 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep857) (@Nat.cast Real Real.instNatCast ep858)) 226375608064910080 72057594037927936 Bool.false 2145749036 2147483648 19 1000000000000000 995646564 497823282 (BSN.sin_reduce_arg_pos_rat_q2 266401174885 2147483648 226375608064910080 72057594037927936 19 ep857 ep858 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2145749036 2147483648 ep857 ep858 6731652396688 4398046511104 996618876 995646564 (ep870 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz401 := (@Enclosure.Real.IsNear.recentre' qz224 Bool.false 486469 2147483648 1 2147483648 486469 2147483648 1 2147483648 (ep851 rfl rfl) rfl)

noncomputable def ep872 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz224 qz120) (@HMul.hMul Real Real Real qz0 qz224 qz121) Bool.true 5247573696423 576460752303423488 6140784734610667 ep799 Bool.false 260960096948471 1152921504606846976 140436994803359459 ep848 (@Enclosure.Real.IsNear.mulLit_ft qz224 qz120 486469 2147483648 1 2147483648 10787067 268435456 1775935919 16704177463885824 5247573696423 576460752303423488 6140784734610667 ep799 qz401 (@Enclosure.Real.IsNear.recentre' qz120 Bool.true 86296536 2147483648 3551871838 33408354927771648 10787067 268435456 1775935919 16704177463885824 (ep865 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz224 qz121 486469 2147483648 1 2147483648 536437259 536870912 1775935919 16704177463885824 260960096948471 1152921504606846976 140436994803359459 ep848 qz401 (@Enclosure.Real.IsNear.neg qz125 Bool.true 536437259 536870912 1775935919 16704177463885824 (@Enclosure.Real.IsNear.recentre' qz125 Bool.true 2145749036 2147483648 3551871838 33408354927771648 536437259 536870912 1775935919 16704177463885824 (ep871 rfl rfl) rfl)) rfl)

noncomputable def ep873 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz213 17270469576863 90000000000 0 1 260960096948471 1152921504606846976 140436994803359459 ep848 ep795

noncomputable def ep874 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2006992567 120000000 0 1 Bool.false 17270469576863 90000000000 0 1 ep846

noncomputable def ep875 := @Enclosure.Complex.IsNear.im_isNear qz201 Bool.true 5247573696423 576460752303423488 6140784734610667 ep799 Bool.false 260960096948471 1152921504606846976 140436994803359459 ep848

noncomputable def ep876 := nat_lit 138350580552821637120000000

noncomputable def ep877 := nat_lit 281856004702160060842141253

noncomputable def ep878 := nat_lit 34437070038705520875845713920000000

noncomputable def ep879 := nat_lit 10069784652935548625184561

noncomputable def ep880 := nat_lit 5764607523034234880000000000

noncomputable def ep881 := nat_lit 106054235937158255854536197621

noncomputable def ep882 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz213) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz212) 523744974859180679015057 ep876 ep877 ep878 ep879 ep880 ep881

noncomputable def ep883 := nat_lit 12913901264514570328442142720000000000

noncomputable def ep884 := nat_lit 1626023669449082462037185253702935720419655680000000

noncomputable def ep885 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz213 2006992567 120000000 0 1 260960096948471 1152921504606846976 140436994803359459 ep848 523744974859180679015057

noncomputable def ep886 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) qz212 17270469576863 90000000000 0 1 5247573696423 576460752303423488 6140784734610667 ep799 ep879

noncomputable abbrev qz402 := (@ep850 ep848 (BSN.cpow_neg_s_sub_mk qz20 51734 1000 11 3 19487171 qz21 rfl EMRow11.d15) ep872)

noncomputable def ep887 := ep791 (@ep797 ep784 ep798 ep781 ep782 ep783 ep784 (@ep800 ep792 ep793 ep794 ep847 (ep849 qz402) rfl) (@ep873 ep782 ep796 ep784 ep874 (ep875 qz402) rfl) rfl rfl) (@ep882 ep883 ep884 ep786 ep787 ep788 ep790 (@ep885 ep876 ep877 ep878 ep847 (ep875 qz402) rfl) (@ep886 ep880 ep881 ep883 ep874 (ep849 qz402) rfl) rfl rfl)

noncomputable def ep888 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) ep786 ep787 ep788 ep790 ep786 ep787 ep788

noncomputable def ep889 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201) Bool.true ep781 ep782 ep783 ep784 Bool.false ep786 ep787 ep788

noncomputable def ep890 := @ep753 636850839925667 985162418487296 1446906493 985162418487296 (@ep754 1 917504 (ep755 (@ep756 262144 1 262144 (ep757 (@ep758 2688656756 672164189 250000 0 1 (ep762 rfl) (ep765 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep766 103 1073741824 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (@ep767 206 2147483648 46852213 1073741824 103 1073741824 (@ep772 46852110 46852316 1073741824 (@ep776 ep777 ep778 ep779 ep780 ep768 ep769 ep770 ep771 (@ep785 ep784 ep773 ep769 ep774 ep771 (@ep789 ep790 ep887) (@ep789 ep790 ep887) rfl) (@ep888 ep790 ep775 ep777 ep778 ep779 (@ep889 ep790 ep887) (@ep889 ep790 ep887) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow11.d16 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 1 11))) (@HMul.hMul Real Real Real qz0 qz198 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)))) Bool.false 18031335911649841 26599385299156992 2840298855215 26599385299156992 := ep751 (ep752 ep890) rfl rfl

noncomputable abbrev qz436 := (@HAdd.hAdd Complex Complex Complex qz438 qz444 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz403 := qz436

noncomputable abbrev qz226 := (@HDiv.hDiv Real Real Real qz256 (@Norm.norm Complex Complex.instNorm qz403) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz353) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz404 := (@HPow.hPow Complex Complex Complex qz416 qz429 (@HSub.hSub Complex Complex Complex qz422 qz431 qz418))

noncomputable abbrev qz227 := qz404

noncomputable def ep891 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz134 1 11))) (@HMul.hMul Real Real Real qz0 qz226 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) 2580739087 57982058496 6698507 57982058496 113452179645873 140737488355328 1951088235

noncomputable def ep892 := nat_lit 6941397653930511165292544

noncomputable def ep893 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz134 1 11)) 6641 442368 1 442368 388607 131072 475 65536 2580739087 57982058496

noncomputable def ep894 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz134 1 11)) (Real.sqrt (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz134 1 11)) (Complex.re (zetaApproximant qz134 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz134 1 11)) (Complex.im (zetaApproximant qz134 1 11))))) Bool.false 388607 131072 475 65536

noncomputable def ep895 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz134 1 11)) (Complex.re (zetaApproximant qz134 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz134 1 11)) (Complex.im (zetaApproximant qz134 1 11))))) Bool.false 777214 262144 1900 262144

noncomputable def ep896 := nat_lit 1107122060782168536610047460426933253

noncomputable def ep897 := nat_lit 125948039931026875086299617107640320

noncomputable def ep898 := nat_lit 7477384677988130892978581601711779225832048644983

noncomputable def ep899 := nat_lit 174130253601815352963381468414062978984335984558080

noncomputable def ep900 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz134 1 11)) (Complex.re (zetaApproximant qz134 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz134 1 11)) (Complex.im (zetaApproximant qz134 1 11)))) ep896 ep897 ep898 ep899 387657 389557

noncomputable def ep901 := nat_lit 26448286616700340035367391952497776776231841

noncomputable def ep902 := nat_lit 3012279749084180462273389565922781849190400

noncomputable def ep903 := nat_lit 36121852143935964847873582446217820930441344017043

noncomputable def ep904 := nat_lit 870651268009076764816907342070314894921679922790400

noncomputable def ep905 := nat_lit 53090463728061837867948960376423022769

noncomputable def ep906 := nat_lit 5229652342160035524780190218615940710400

noncomputable def ep907 := nat_lit 19766738218823275265926961911579299979982800123

noncomputable def ep908 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz134 1 11)) (Complex.re (zetaApproximant qz134 1 11))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz134 1 11)) (Complex.im (zetaApproximant qz134 1 11))) ep901 ep902 ep903 ep904 ep905 ep906 ep907

noncomputable def ep909 := nat_lit 13603926062641824450264177219848670233151248793600

noncomputable def ep910 := nat_lit 138475267379904383903404245597067696899128562661549944650852707790801817844056064000

noncomputable def ep911 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz134 1 11)) (Complex.re (zetaApproximant qz134 1 11)) 5142789769833134063279 1735592045696274923520 206326326986412458706599 ep501 5142789769833134063279 1735592045696274923520 206326326986412458706599 ep501 ep901

noncomputable def ep912 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz134 1 11)) (Complex.im (zetaApproximant qz134 1 11)) 7286320314676114887 72316335237344788480 25705995808270567055701 ep619 7286320314676114887 72316335237344788480 25705995808270567055701 ep619 ep905

noncomputable def ep913 := @ep891 985162418487296 ep892 3232340167244203 3799912185593856 3125632865609 26599385299156992 (@ep893 6698507 57982058496 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz202)) Bool.false 6641 442368 1 442368 (BSN.theta_err_eq 1 2 96 162 EMRow11.d12 EMRow11.d13 rfl) (ep731 rfl)) (ep894 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz134 1 11)) (@ep895 388607 131072 475 65536 (@ep900 131072 (@ep908 ep909 ep910 ep896 ep897 ep898 ep899 (@ep911 ep902 ep903 ep904 ep711 ep711 rfl) (@ep912 ep906 ep907 ep909 ep719 ep719 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz228 := (@Norm.norm Complex Complex.instNorm qz403)

noncomputable def ep914 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz226 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz228 qz394) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) Bool.false 113452179645873 140737488355328 1951088235 985162418487296 (BSN.zrb_shape_eq qz228 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) qz143 3)

noncomputable def ep915 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz228 qz394) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) 2051723 131072 1 917504 55296051 1073741824 33 268435456

noncomputable def ep916 := @Enclosure.Real.IsNear.mulLit_ff qz228 qz394 14362061 262144 1 262144 2 7 0 1 2051723 131072

noncomputable abbrev qz405 := (Complex.re qz436)

noncomputable abbrev qz406 := (Complex.im qz436)

noncomputable abbrev qz229 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz253 qz405 qz405) (@HMul.hMul Real Real Real qz253 qz406 qz406))

noncomputable abbrev qz230 := qz403

noncomputable def ep917 := @Enclosure.Real.IsNear.of_eq qz228 (Real.sqrt qz229) Bool.false 14362061 262144 1 262144 (BSN.norm_eq_sqrt_mul_add qz230)

noncomputable def ep918 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz229) Bool.false 14362061 262144 1 262144 14362061

noncomputable def ep919 := @Enclosure.Real.IsNear.sqrt_image qz229 4802569 1600 0 1 7181030 7181031 131072

noncomputable abbrev qz231 := (@HMul.hMul Real Real Real qz253 qz405 qz405)

noncomputable abbrev qz232 := (@HMul.hMul Real Real Real qz253 qz406 qz406)

noncomputable def ep920 := @Enclosure.Real.IsNear.addLit_ff qz231 qz232 49 4 0 1 4782969 1600 0 1

noncomputable abbrev qz233 := qz405

noncomputable def ep921 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 7 2 0 1 7 2 0 1 49 4

noncomputable def ep922 := @Enclosure.Complex.IsNear.of_eq qz230 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz143) Bool.false 7 2 0 1 Bool.false 54675 1000 0 1 (BSN.s_add_nat_mk qz143 Bool.false 54675 1000 3 qz144)

noncomputable abbrev qz234 := (ep922 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz355 Bool.false 7 2 0 1 Bool.false 54675 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz357))

noncomputable def ep923 := @ep921 0 1 (@Enclosure.Complex.IsNear.re_isNear qz230 Bool.false 7 2 0 1 Bool.false 54675 1000 0 1 qz234)

noncomputable def ep924 := ep923 (@Enclosure.Complex.IsNear.re_isNear qz230 Bool.false 7 2 0 1 Bool.false 54675 1000 0 1 qz234)

noncomputable abbrev qz235 := qz406

noncomputable def ep925 := @Enclosure.Real.IsNear.mulLit_ff qz235 qz235 54675 1000 0 1 54675 1000 0 1 4782969 1600

noncomputable def ep926 := @ep925 0 1 (@Enclosure.Complex.IsNear.im_isNear qz230 Bool.false 7 2 0 1 Bool.false 54675 1000 0 1 qz234)

noncomputable def ep927 := ep926 (@Enclosure.Complex.IsNear.im_isNear qz230 Bool.false 7 2 0 1 Bool.false 54675 1000 0 1 qz234)

noncomputable def ep928 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Real.sqrt (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))))) Bool.false 55296051 1073741824

noncomputable def ep929 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))))) Bool.false 110592102 2147483648

noncomputable def ep930 := nat_lit 13307313559783366531841787206855511544771963450613

noncomputable def ep931 := nat_lit 5017667669669390206845536611345881338845593600000000

noncomputable def ep932 := nat_lit 3927777747960898705376290463262555462501558628545378564487247

noncomputable def ep933 := nat_lit 310879661025056382012368529705286280464404681073487188171161600000000

noncomputable def ep934 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)))) ep930 ep931 ep932 ep933

noncomputable def ep935 := nat_lit 6311858401018651135268184722509635822764403550129

noncomputable def ep936 := nat_lit 2000952369323793725973728603638956588651812067427402393152751

noncomputable def ep937 := nat_lit 1748863789691178849143400621086468930501889975121

noncomputable def ep938 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) ep935 ep931 ep936 ep933 ep937

noncomputable def ep939 := nat_lit 1254416917417347551711384152836470334711398400000000

noncomputable def ep940 := nat_lit 60213293082409530606330058113237464807804580034936755354203

noncomputable def ep941 := nat_lit 9714989407033011937886516553290196264512646283546474630348800000000

noncomputable def ep942 := nat_lit 16692919254769520566785249135649029998116005949393116363940811555146063050678351778366567219200000000

noncomputable def ep943 := nat_lit 2512341219066122621352377

noncomputable def ep944 := nat_lit 70835497243044678205440000

noncomputable def ep945 := nat_lit 1599861428120714887158886963

noncomputable def ep946 := nat_lit 17631779859817226688433005527040000

noncomputable def ep947 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) ep943 ep944 ep945 ep946 ep943 ep944 ep945

noncomputable def ep948 := nat_lit 1322446138673019396987511

noncomputable def ep949 := nat_lit 35417748621522339102720000

noncomputable def ep950 := nat_lit 365846320655579292299196307

noncomputable def ep951 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227) Bool.true ep943 ep944 ep945 ep946 Bool.false ep948 ep949 ep950

noncomputable def ep952 := nat_lit 4407944964954306672108251381760000

noncomputable def ep953 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227 Bool.true ep943 ep944 ep945 ep946 Bool.false ep948 ep949 ep950 ep952

noncomputable def ep954 := nat_lit 1770887431076116955136000

noncomputable def ep955 := nat_lit 110198624123857666802706284544000

noncomputable def ep956 := nat_lit 23611832414348226068480000

noncomputable def ep957 := nat_lit 5014571569480692370406619

noncomputable abbrev qz236 := (Complex.re qz404)

noncomputable abbrev qz237 := (Complex.im qz404)

noncomputable def ep958 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237) 4990973657254574291347 ep954 690835449905932832175757 ep955 903993388452101864335419 ep956 ep957

noncomputable def ep959 := nat_lit 59366262154266756526710456320000

noncomputable def ep960 := nat_lit 1483024495806215290638558751553480198585319424000

noncomputable def ep961 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236 14346907 768000 0 1 347878023970921 2305843009213693952 48152221932290551 ep799 4990973657254574291347

noncomputable def ep962 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)))) 14346907 768000 0 1 0 1 0 1 14346907

noncomputable def ep963 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 43040721 3200 0 1 14346907 768000 0

noncomputable abbrev qz407 := (@HAdd.hAdd Complex Complex Complex qz415 qz430 qz419)

noncomputable abbrev qz238 := qz407

noncomputable def ep964 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz48 (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2)) qz238) Bool.true 43040721 3200 0 1 Bool.true 10440232803 64000 0 1

noncomputable abbrev qz239 := (Complex.re qz407)

noncomputable abbrev qz240 := (Complex.im qz407)

noncomputable def ep965 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2))) qz240) 4781769 640 0 1 4782969 800 0 1

noncomputable def ep966 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2))) qz239 4781769 1600 0 1 5 2 0 1 4781769 640

noncomputable abbrev qz408 := (@HAdd.hAdd Complex Complex Complex qz415 qz430 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz241 := qz408

noncomputable def ep967 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz48 (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)) qz241) Bool.true 4781769 1600 0 1 Bool.false 2187 20 0 1

noncomputable abbrev qz242 := (Complex.re qz408)

noncomputable abbrev qz243 := (Complex.im qz408)

noncomputable def ep968 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) qz242) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) qz243) 3 4 0 1 4782969 1600 0 1

noncomputable def ep969 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) qz242 1 2 0 1 3 2 0 1 3 4

noncomputable def ep970 := @ep969 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep677)

noncomputable def ep971 := @Enclosure.Complex.IsNear.of_eq qz241 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz143) Bool.false 3 2 0 1 Bool.false 54675 1000 0 1 (BSN.s_add_nat_mk qz143 Bool.false 54675 1000 1 qz144)

noncomputable abbrev qz244 := (ep971 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz355 Bool.false 3 2 0 1 Bool.false 54675 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz357))

noncomputable def ep972 := ep970 (@Enclosure.Complex.IsNear.re_isNear qz241 Bool.false 3 2 0 1 Bool.false 54675 1000 0 1 qz244)

noncomputable def ep973 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) qz243 54675 1000 0 1 54675 1000 0 1 4782969 1600

noncomputable def ep974 := @ep973 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep677)

noncomputable def ep975 := ep974 (@Enclosure.Complex.IsNear.im_isNear qz241 Bool.false 3 2 0 1 Bool.false 54675 1000 0 1 qz244)

noncomputable def ep976 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)) qz241 Bool.true 4781769 1600 0 1 Bool.false 2187 20 0 1 (@ep968 19127076 4781769 1600 0 1 (ep972 rfl) (ep975 rfl) rfl rfl)

noncomputable def ep977 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) qz243) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) qz242) 2187 80 0 1 6561 80 0 1

noncomputable def ep978 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) qz243 1 2 0 1 54675 1000 0 1 2187 80

noncomputable def ep979 := @ep978 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep677)

noncomputable def ep980 := ep979 (@Enclosure.Complex.IsNear.im_isNear qz241 Bool.false 3 2 0 1 Bool.false 54675 1000 0 1 qz244)

noncomputable def ep981 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1))) qz242 54675 1000 0 1 3 2 0 1 6561 80

noncomputable def ep982 := @ep981 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 54675 1000 0 1 ep677)

noncomputable def ep983 := ep982 (@Enclosure.Complex.IsNear.re_isNear qz241 Bool.false 3 2 0 1 Bool.false 54675 1000 0 1 qz244)

noncomputable abbrev qz245 := (ep967 (BSN.ascPochhammer_succ_eval_c 1 2 qz353 rfl) (ep976 (@ep977 699840 2187 20 0 1 (ep980 rfl) (ep983 rfl) rfl rfl)))

noncomputable def ep984 := @ep966 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4781769 1600 0 1 Bool.false 2187 20 0 1 qz245)

noncomputable def ep985 := @Enclosure.Complex.IsNear.of_eq qz238 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz143) Bool.false 5 2 0 1 Bool.false 54675 1000 0 1 (BSN.s_add_nat_mk qz143 Bool.false 54675 1000 2 qz144)

noncomputable abbrev qz246 := (ep985 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz355 Bool.false 5 2 0 1 Bool.false 54675 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz357))

noncomputable def ep986 := ep984 (@Enclosure.Complex.IsNear.re_isNear qz238 Bool.false 5 2 0 1 Bool.false 54675 1000 0 1 qz246)

noncomputable def ep987 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2))) qz240 2187 20 0 1 54675 1000 0 1 4782969 800

noncomputable def ep988 := @ep987 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4781769 1600 0 1 Bool.false 2187 20 0 1 qz245)

noncomputable def ep989 := ep988 (@Enclosure.Complex.IsNear.im_isNear qz238 Bool.false 5 2 0 1 Bool.false 54675 1000 0 1 qz246)

noncomputable def ep990 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2)) qz238 Bool.true 43040721 3200 0 1 Bool.true 10440232803 64000 0 1 (@ep965 6886515360 43040721 3200 0 1 (ep986 rfl) (ep989 rfl) rfl rfl)

noncomputable def ep991 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2))) qz240) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2))) qz239) 10457728803 64000 0 1 2187 8 0 1

noncomputable def ep992 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2))) qz240 4781769 1600 0 1 54675 1000 0 1 10457728803 64000

noncomputable def ep993 := @ep992 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4781769 1600 0 1 Bool.false 2187 20 0 1 qz245)

noncomputable def ep994 := ep993 (@Enclosure.Complex.IsNear.im_isNear qz238 Bool.false 5 2 0 1 Bool.false 54675 1000 0 1 qz246)

noncomputable def ep995 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2))) qz239 2187 20 0 1 5 2 0 1 2187 8

noncomputable def ep996 := @ep995 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4781769 1600 0 1 Bool.false 2187 20 0 1 qz245)

noncomputable def ep997 := ep996 (@Enclosure.Complex.IsNear.re_isNear qz238 Bool.false 5 2 0 1 Bool.false 54675 1000 0 1 qz246)

noncomputable abbrev qz247 := (ep964 (BSN.ascPochhammer_succ_eval_c 2 3 qz353 rfl) (ep990 (@ep991 83521862424 10440232803 64000 0 1 (ep994 rfl) (ep997 rfl) rfl rfl)))

noncomputable def ep998 := @ep963 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep803) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43040721 3200 0 1 Bool.true 10440232803 64000 0 1 qz247)

noncomputable def ep999 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 10440232803 64000 0 1 0 1 0

noncomputable def ep1000 := @ep999 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep803) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43040721 3200 0 1 Bool.true 10440232803 64000 0 1 qz247)

noncomputable def ep1001 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)))) 1160025867 5120000 0 1 0 1 0 1 1160025867

noncomputable def ep1002 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 10440232803 64000 0 1 1160025867 5120000 0

noncomputable def ep1003 := @ep1002 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep803) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43040721 3200 0 1 Bool.true 10440232803 64000 0 1 qz247)

noncomputable def ep1004 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 43040721 3200 0 1 0 1 0

noncomputable def ep1005 := @ep1004 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep803) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43040721 3200 0 1 Bool.true 10440232803 64000 0 1 qz247)

noncomputable def ep1006 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 14346907 768000 0 1 Bool.false 1160025867 5120000 0 1 (@ep962 14346907 768000 0 1 (ep998 rfl) (ep1000 rfl) rfl rfl) (@ep1001 1160025867 5120000 0 1 (ep1003 rfl) (ep1005 rfl) rfl rfl)

noncomputable def ep1007 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 14346907 768000 0 1 Bool.false 1160025867 5120000 0 1 ep1006

noncomputable def ep1008 := nat_lit 1147902334623517362528190464

noncomputable def ep1009 := @Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 347878023970921 2305843009213693952 48152221932290551 ep799 Bool.false 779287267783057 4611686018427387904 427958202917029043 ep1008

noncomputable def ep1010 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk (@HMul.hMul Real Real Real qz0 qz224 qz193) (@HMul.hMul Real Real Real qz0 qz224 qz194)) Bool.false 347878023970921 2305843009213693952 48152221932290551 ep799 Bool.false 779287267783057 4611686018427387904 427958202917029043

noncomputable def ep1011 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz123 54675 1000 0 1 10799160256583397 4503599627370496 500000746734923 248911641000000000000000 23617763481147889239 180143985094819840 121500181456586289 1106273960000000000000000 qz145 (BSN.isNear_log_sfrac 11 1 10799160256583397 4503599627370496 500000746734923 248911641000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz122) Bool.false ep853 ep854 1000001493469846 497823282000000000000000 10799160256583397 4503599627370496 500000746734923 248911641000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 341937090 1073741824 24973259072661432 36028797018963968 497823282 1000000000000000 rfl rfl rfl rfl (ep855 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1012 := nat_lit 28195202809751795436355584

noncomputable def ep1013 := nat_lit 119454693128641500364992410398076517827312196872302143702305954494574391468708119601688011546600407040000

noncomputable def ep1014 := nat_lit 50797410752592599495442790923292316227798919877281851451531752809858799638366050241238301547400049385799680

noncomputable def ep1015 := nat_lit 11145082158311966081208395679003739835682129878270310916143598241105106675591365093041904025600000000

noncomputable def ep1016 := nat_lit 312839485203899995867991499354339159683226554074321748240746600707685426531046498651413200491721523200000

noncomputable def ep1017 := nat_lit 931285863797530990749784500260359130842980197750167276611415468180744660036710921089368861702334238739660800

noncomputable def ep1018 := BSN.sin_dyadic_bound_f 3205423446360 4398046511104 3 2 2147483648 996618876 ep1013 ep1014 ep1015 ep1016 ep1017 ep1015 1430216618 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3205423446360) (BSN.sinEvenQ 4398046511104) 0 2 ep1013 ep1014 ep1015 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3205423446360) (BSN.sinOddQ 4398046511104) 0 2 ep1016 ep1017 ep1015 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz409 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 35193210067) (@Nat.cast Real Real.instNatCast 268435456))

noncomputable def ep1019 := @Enclosure.Real.IsNear.cos_image qz195 qz409 Bool.false 35193210067 268435456 237 2147483648 Bool.false 1430216618 2147483648 1 497823282 (@Enclosure.Real.IsNear.recentre' qz195 Bool.false 23617763481147889239 180143985094819840 121500181456586289 1106273960000000000000000 35193210067 268435456 237 2147483648 (ep1011 rfl) rfl) (Enclosure.sfrac_false_div 35193210067 268435456) (BSN.cos_reduce3 qz409 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1012) (@Nat.cast Real Real.instNatCast ep854)) 226375608064910080 72057594037927936 Bool.false 1430216618 2147483648 20 1000000000000000 995646564 497823282 (BSN.sin_reduce_arg_pos_rat_q3 35193210067 268435456 226375608064910080 72057594037927936 20 ep1012 ep854 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1430216618 2147483648 ep1012 ep854 3205423446360 4398046511104 996618876 995646564 (ep1018 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1020 := nat_lit 66368671774648972187698542841455400455100412542335977750577149651759597530026995940979136149900492800000

noncomputable def ep1021 := nat_lit 5644156750288066610604754547032479580866546653031316827947972534428755515374005582359811283044449931755520

noncomputable def ep1022 := nat_lit 199083725159630292630933211733008193885629873367251392629899161758796582376729805092751324641650278400000

noncomputable def ep1023 := nat_lit 253987053762962997477213954616461581138994599386409257257658764049293998191830251206191507737000246928998400

noncomputable def ep1024 := BSN.cos_dyadic_bound_f 3205423446360 4398046511104 3 2 2147483648 996618876 ep1020 ep1021 ep1015 ep1022 ep1023 ep1015 1601925853 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3205423446360) (BSN.cosEvenQ 4398046511104) 0 2 ep1020 ep1021 ep1015 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3205423446360) (BSN.cosOddQ 4398046511104) 0 2 ep1022 ep1023 ep1015 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1025 := @Enclosure.Real.IsNear.sin_image qz195 qz409 Bool.false 35193210067 268435456 237 2147483648 Bool.true 1601925853 2147483648 1 497823282 (@Enclosure.Real.IsNear.recentre' qz195 Bool.false 23617763481147889239 180143985094819840 121500181456586289 1106273960000000000000000 35193210067 268435456 237 2147483648 (ep1011 rfl) rfl) (Enclosure.sfrac_false_div 35193210067 268435456) (BSN.sin_reduce3 qz409 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1012) (@Nat.cast Real Real.instNatCast ep854)) 226375608064910080 72057594037927936 Bool.false 1601925853 2147483648 20 1000000000000000 995646564 497823282 (BSN.sin_reduce_arg_pos_rat_q3 35193210067 268435456 226375608064910080 72057594037927936 20 ep1012 ep854 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1601925853 2147483648 ep1012 ep854 3205423446360 4398046511104 996618876 995646564 (ep1024 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1026 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz224 qz193) (@HMul.hMul Real Real Real qz0 qz224 qz194) Bool.false 347878023970921 2305843009213693952 48152221932290551 ep799 Bool.false 779287267783057 4611686018427387904 427958202917029043 ep1008 (@Enclosure.Real.IsNear.mulLit_ff qz224 qz193 486469 2147483648 1 2147483648 715108309 1073741824 60065800741 534533678844346368 347878023970921 2305843009213693952 48152221932290551 ep799 qz401 (@Enclosure.Real.IsNear.recentre' qz193 Bool.false 1430216618 2147483648 120131601482 1069067357688692736 715108309 1073741824 60065800741 534533678844346368 (ep1019 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz224 qz194 486469 2147483648 1 2147483648 1601925853 2147483648 60065800741 534533678844346368 779287267783057 4611686018427387904 427958202917029043 ep1008 qz401 (@Enclosure.Real.IsNear.neg qz196 Bool.true 1601925853 2147483648 60065800741 534533678844346368 (@Enclosure.Real.IsNear.recentre' qz196 Bool.true 1601925853 2147483648 120131601482 1069067357688692736 1601925853 2147483648 60065800741 534533678844346368 (ep1025 rfl rfl) rfl)) rfl)

noncomputable def ep1027 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237 1160025867 5120000 0 1 779287267783057 4611686018427387904 427958202917029043 ep1008 903993388452101864335419

noncomputable def ep1028 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 14346907 768000 0 1 Bool.false 1160025867 5120000 0 1 ep1006

noncomputable def ep1029 := @Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 347878023970921 2305843009213693952 48152221932290551 ep799 Bool.false 779287267783057 4611686018427387904 427958202917029043 ep1008

noncomputable def ep1030 := nat_lit 3541774862152233910272000

noncomputable def ep1031 := nat_lit 6139876537137744396220001

noncomputable def ep1032 := nat_lit 881588992990861334421650276352000

noncomputable def ep1033 := nat_lit 11805916207174113034240000

noncomputable def ep1034 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236) 11180361957167614954699 ep1030 ep1031 ep1032 403547506367114415813507 ep1033 564220434292745067875583

noncomputable def ep1035 := nat_lit 7420782769283344565838807040000

noncomputable def ep1036 := nat_lit 1561268830167462428234355430592264765559537664000

noncomputable def ep1037 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237 14346907 768000 0 1 779287267783057 4611686018427387904 427958202917029043 ep1008 11180361957167614954699

noncomputable def ep1038 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236 1160025867 5120000 0 1 347878023970921 2305843009213693952 48152221932290551 ep799 403547506367114415813507

noncomputable abbrev qz410 := (@ep1010 ep1008 (BSN.cpow_neg_s_sub_mk qz143 54675 1000 11 3 19487171 qz144 rfl EMRow11.d15) ep1026)

noncomputable def ep1039 := ep953 (@ep958 ep959 ep960 ep943 ep944 ep945 ep946 (@ep961 ep954 690835449905932832175757 ep955 ep1007 (ep1009 qz410) rfl) (@ep1027 ep956 ep957 ep959 ep1028 (ep1029 qz410) rfl) rfl rfl) (@ep1034 ep1035 ep1036 ep948 ep949 ep950 ep952 (@ep1037 ep1030 ep1031 ep1032 ep1007 (ep1029 qz410) rfl) (@ep1038 ep1033 564220434292745067875583 ep1035 ep1028 (ep1009 qz410) rfl) rfl rfl)

noncomputable def ep1040 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.im (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) ep948 ep949 ep950 ep952 ep948 ep949 ep950

noncomputable def ep1041 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227) Bool.true ep943 ep944 ep945 ep946 Bool.false ep948 ep949 ep950

noncomputable def ep1042 := @ep915 113452179645873 140737488355328 1951088235 985162418487296 (@ep916 1 917504 (ep917 (@ep918 262144 1 262144 (ep919 (@ep920 19210276 4802569 1600 0 1 (ep924 rfl) (ep927 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep928 33 268435456 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (@ep929 264 2147483648 55296051 1073741824 33 268435456 (@ep934 55295919 55296183 1073741824 (@ep938 ep939 ep940 ep941 ep942 ep930 ep931 ep932 ep933 (@ep947 ep946 ep935 ep931 ep936 ep933 (@ep951 ep952 ep1039) (@ep951 ep952 ep1039) rfl) (@ep1040 ep952 ep937 ep939 ep940 ep941 (@ep1041 ep952 ep1039) (@ep1041 ep952 ep1039) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow11.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz134 1 11))) (@HMul.hMul Real Real Real qz0 qz226 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)))) Bool.false 3232340167244203 3799912185593856 3125632865609 26599385299156992 := ep913 (ep914 ep1042) rfl rfl

noncomputable def EMRow11.d18 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz411 := (EMRow11.d3 qz420 qz432 (@Enclosure.dec_le_dec qz420 qz432 51734 1000 54675 1000 (@Eq.refl Real qz420) (@Eq.refl Real qz432) rfl rfl rfl) 11 11 1 1)

noncomputable abbrev qz248 := qz411

noncomputable def ep1043 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz248 (@Enclosure.dec_nonneg qz20 51734 1000 qz21) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 11 rfl)

noncomputable abbrev qz249 := (Zeta.Certificates.ZIntervalEM.fstVal qz411)

noncomputable def ep1044 := @Enclosure.Real.IsNear.neg_val qz249 ep144 ep145

noncomputable def ep1045 := @Enclosure.Real.IsNear.of_eq qz249 (hardyZApproximantEM 1 11 qz20) Bool.true

noncomputable abbrev qz250 := (Zeta.Certificates.ZIntervalEM.sndVal qz411)

noncomputable def ep1046 := BSN.mul_neg_of_neg_pos_r qz249 qz250 (@ep1044 ep146 ep147 (@ep1045 ep144 ep145 ep146 ep147 (@Eq.refl Real (hardyZApproximantEM 1 11 qz20)) EMRow11.d9) rfl rfl rfl)

noncomputable def ep1047 := @Enclosure.Real.IsNear.pos_val qz250 ep487 ep488

noncomputable def ep1048 := @Enclosure.Real.IsNear.of_eq qz250 (hardyZApproximantEM 1 11 qz143) Bool.false

noncomputable def ep1049 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz249) (BSN.hardyZErrorBoundStrong 1 11 qz20)

noncomputable def ep1050 := @Enclosure.norm_gt_of_isNear qz249 (BSN.hardyZErrorBoundStrong 1 11 qz20) Bool.true

noncomputable def ep1051 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 11 qz20) (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 1 11))) (@HMul.hMul Real Real Real qz0 qz198 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)))) Bool.false 18031335911649841 26599385299156992 2840298855215 26599385299156992 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 1 11))) (@HMul.hMul Real Real Real qz0 qz198 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)))))

noncomputable def ep1052 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz250) (BSN.hardyZErrorBoundStrong 1 11 qz143)

noncomputable def ep1053 := @Enclosure.norm_gt_of_isNear qz250 (BSN.hardyZErrorBoundStrong 1 11 qz143) Bool.false

noncomputable def ep1054 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 11 qz143) (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz134 1 11))) (@HMul.hMul Real Real Real qz0 qz226 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)))) Bool.false 3232340167244203 3799912185593856 3125632865609 26599385299156992 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz90 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz134 1 11))) (@HMul.hMul Real Real Real qz0 qz226 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz48 (@HMul.hMul Complex Complex Complex qz48 (@HDiv.hDiv Complex Complex Complex qz56 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz134 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)))))

noncomputable def ep1055 := @List.cons EMRow11.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz248 (ep1043 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 11 rfl) (ep1046 (@ep1047 ep489 ep490 (@ep1048 ep487 ep488 ep489 ep490 (@Eq.refl Real (hardyZApproximantEM 1 11 qz143)) EMRow11.d11) rfl rfl rfl)) (ep1049 (hardyZErrorBoundEM 1 11 qz20) (BSN.hardyZErrorBoundEM_le_strong 1 11 qz20 rfl) (@ep1050 Bool.false ep144 ep145 ep146 ep147 18031335911649841 26599385299156992 2840298855215 26599385299156992 (@ep1045 ep144 ep145 ep146 ep147 (@Eq.refl Real (hardyZApproximantEM 1 11 qz20)) EMRow11.d9) (ep1051 EMRow11.d16) rfl rfl rfl rfl rfl)) (ep1052 (hardyZErrorBoundEM 1 11 qz143) (BSN.hardyZErrorBoundEM_le_strong 1 11 qz143 rfl) (@ep1053 Bool.false ep487 ep488 ep489 ep490 3232340167244203 3799912185593856 3125632865609 26599385299156992 (@ep1048 ep487 ep488 ep489 ep490 (@Eq.refl Real (hardyZApproximantEM 1 11 qz143)) EMRow11.d11) (ep1054 EMRow11.d17) rfl rfl rfl rfl rfl)))) (@List.nil EMRow11.d0)

noncomputable abbrev qz412 := (@Enclosure.dec_le_dec qz420 qz432 51734 1000 54675 1000 (@Eq.refl Real qz420) (@Eq.refl Real qz432) rfl rfl rfl)

noncomputable abbrev qz251 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1055 (@List.IsChain.singleton EMRow11.d1 EMRow11.d18 (EMRow11.d2 qz266 qz355 qz412))))

noncomputable abbrev qz413 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1056 := And (@Eq (Option Real) (@Option.map qz413 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz413 qz251)) (@Option.some Real qz20))

noncomputable def ep1057 := ep1056 (@Eq (Option Real) (@Option.map qz413 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz413 qz251)) (@Option.some Real qz143))

noncomputable def ep1058 := @And.intro (@Eq Nat (@List.length qz413 qz251) 1) ep1057

noncomputable def ep1059 := @And.intro (@Eq (Option Real) (@Option.map qz413 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz413 qz251)) (@Option.some Real qz20))

noncomputable def ep1060 := @ep1059 (@Eq (Option Real) (@Option.map qz413 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz413 qz251)) (@Option.some Real qz143))

noncomputable abbrev qz252 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1055 (@List.IsChain.singleton EMRow11.d1 EMRow11.d18 (EMRow11.d2 qz266 qz355 qz412)))

theorem EMRow11.d19 : Zeta.Certificates.BatchSpec 1 51734 1000 54675 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz413 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz413 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz413 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz20)) (@Eq (Option Real) (@Option.map qz413 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz413 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz143)))) qz252 (ep1058 (@Eq.refl Nat 1) (ep1060 (@Eq.refl (Option Real) (@Option.some Real qz20)) (@Eq.refl (Option Real) (@Option.some Real qz143))))

theorem solution : Zeta.Certificates.BatchSpec 1 51734 1000 54675 1000 := EMRow11.d19
#print axioms solution
#check solution
