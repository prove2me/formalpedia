-- Prove2me | solution 1 for RHHeight1000.em_main_0009_0009
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:52:09.583493+00:00
-- url     : https://prove2.me/submissions/0726f44c-a060-4c44-9a54-e86211bb3f14

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow09.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow09.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow09.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow09.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow09.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz253 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz253

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz254 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz254 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138516661214455 2251799813685248 250000000032071 16035500000000000000 4138516661214455 2251799813685248 250000000032071 16035500000000000000 120446 65536

noncomputable abbrev qz255 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 65536 qz255 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 779317518150410741488063439345657628452599855445271348474342368876423347582876053728679783827237610085654588674605917415063316248867402488514697634436426745

noncomputable def ep10 := nat_lit 13198325246229587668616048586507268161410801335203869857947191811663857046415771104290097871102374067703089877156867761119753226876438075596795543285583799

noncomputable def ep11 := nat_lit 13338205139369261376383149914767634013226508915861991492218067381232119098362059104733250767410551174650894954010182016771344050520336484956804919489535

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 4 3 ep9 131072 64142 ep10 ep11 59189 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 3 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz256 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz256

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138516661214455 2251799813685248 250000000032071 16035500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000128284 64142000000000000000 4138516661214455 2251799813685248 250000000032071 16035500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 59189 131072 24973259072661432 36028797018963968 64142 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 779317518150412560342812906055656980396982394702499187106382620393032652998517540933158707129341055012778793601285942846917973645097155238594697634436426745

noncomputable def ep18 := nat_lit 13198325246229655554962711811363413523213721429909419700721697472804734044169853548961061453892255410264786862895235075217650796661500958924795543285583799

noncomputable def ep19 := nat_lit 13338205139369401582665284895604560799810298653799657073142644093199656832454717421805370366589019475922075211274104314270069372987910244956804919489535

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 4 3 ep17 131072 64142 ep18 ep19 59189 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 3 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138516661214455 2251799813685248 250000000032071 16035500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 8679098493099216732160 4722366482869645213696 1000000000128284 64142000000000000000 4138516661214455 2251799813685248 250000000032071 16035500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 59189 131072 24973259072661432 36028797018963968 64142 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz257 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz3 := (Real.log qz257)

theorem EMRow09.d4 : Enclosure.Real.IsNear qz3 Bool.false 60223 32768 1 32768 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz254) Bool.false 60223 32768 1 32768 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz254) Bool.false 120446 65536 2 65536 60223 32768 1 32768 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 150042 131072 1 64142 150042 131072 1 64142 75021 65536 2 65536 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 5456220599384213465248909714772227496572670538165976141063262914812807742611017753801422503639530882087556452122005170047444298375835020188444492540969863625638808382453421118235702266947370928498132967594635949979551089348001357731941995137847266570621617494261809398531128871567535833923098076891483476912075228072418610430965163137427706923427310178652894498746239459018086669257415154730407592571637957767157504839263249849478535520334507104454135585522664276476675

noncomputable def ep28 := nat_lit 583201912334273870627228188254822588827079241605343036411752047433839590517388190714780374919746279700129906501257101384229175562492847525225536391462542197025353003914524118772974087630067522636400444148635637549655768907025719966434833632093412247469427754039812435067522613541620617101084764807513402584784781490076808276521160080078978009740617112077674385114356333461540984478969922738031393369686631450339262287925718320742111081121726382582016608811398564907105

noncomputable def ep29 := nat_lit 2006268627360805445673839316848610509641534779303135707206598861506426804997221642604762844037348942607248852390277353874343091902420975230792155995982437872051629609224882022549487822374001366578458875613104959699164386313425243185530298109514065278868815165519648262204211929774735225023360668387821809970420335957473972782118680523137645713941929429588852958886338507735711181009301082096313539911189247153419366938656533848809858580689548163599238034961919825

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 10 9 ep27 131072 64142 ep28 ep29 150042 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 9 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 5456220599384260892400251500854699790811159195150212163211869656216336849990273498858157048596616978904240776489460003685239051624059887013466241201881443704542959173524008982544253046253151867013374679201187657749749224297051088632484873343955402287279851789208893474071824987110190207053471018354491495133306616646837230249901879422821128116650397962087630806812522581253210958036113071268120219429850657911869289056672761916619783759890108169949892385522664276476675

noncomputable def ep34 := nat_lit 583201912334279575053067226115417021307550325332234501953544426829928714668898700518418107620762577859683234776628347658361181262145210140271013263714562720079188253110303208819702903278206870150494721073991877864419341163488949363940583288588224434829960190109694548513088121652843287215458036179968684293644459891198769761601084092249455692877745995219003758983943549453190712470220270279351626860119698313725888367584660500821040083453648022042061408811398564907105

noncomputable def ep35 := nat_lit 2006268627360839170887858856494478835319319717359667041823756329478526322484078784125879825811686186445537802910004300367040714583746383402724632880452479311196631191501299191497899488881639138562974769996989848045902383299749709271247360054208480548633525642122514778503225872819822968825602771791453574137145372948950799520945900351638147820910599315255916738483881817718250085827996954508077874524152655659774549924038927632065100609588052048399238034961919825

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 10 9 ep33 131072 64142 ep34 ep35 150042 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 9 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 75021 65536 2 65536 75021 65536 1 32768 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 150042 131072 1 64142 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 150042 131072 64142 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 150042 131072 1 64142 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 150042 131072 64142 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow09.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 32768 := ep37

noncomputable abbrev qz432 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 45593 1000)))

noncomputable abbrev qz409 := qz432

noncomputable abbrev qz258 := qz409

noncomputable abbrev qz4 := (BSN.headSumC qz258 9)

noncomputable abbrev qz433 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz410 := qz433

noncomputable abbrev qz259 := qz410

noncomputable abbrev qz5 := qz259

noncomputable abbrev qz6 := (BSN.headSumC qz258 8)

noncomputable abbrev qz411 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz260 := qz411

noncomputable abbrev qz412 := (@Neg.neg Complex Complex.instNeg qz432)

noncomputable abbrev qz261 := qz412

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 8) qz261)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz4 (@HAdd.hAdd Complex Complex Complex qz5 qz6 qz7) Bool.false 60437698919 17179869184 2744649687435 550975584600064 Bool.true 557857645 2147483648 1362150463287 275487792300032

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP qz6 qz7 Bool.false 27646066651 8589934592 1228544335225 275487792300032 Bool.true 1235442215 17179869184 2438067392421 550975584600064 Bool.false

noncomputable abbrev qz8 := (BSN.headSumC qz258 7)

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 7) qz261)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq qz6 (@HAdd.hAdd Complex Complex Complex qz5 qz8 qz9) Bool.false 27646066651 8589934592 1228544335225 275487792300032 Bool.true 1235442215 17179869184 2438067392421 550975584600064

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP qz8 qz9 Bool.false 50561413671 17179869184 2148826650949 550975584600064 Bool.false 803124347 4294967296 532497108547 137743896150016 Bool.false

noncomputable abbrev qz10 := (BSN.headSumC qz258 6)

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 6) qz261)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq qz8 (@HAdd.hAdd Complex Complex Complex qz5 qz10 qz11) Bool.false 50561413671 17179869184 2148826650949 550975584600064 Bool.false 803124347 4294967296 532497108547 137743896150016

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP qz10 qz11 Bool.false 43548125521 17179869184 1810763484679 550975584600064 Bool.false 1640896419 8589934592 900124487629 275487792300032 Bool.false

noncomputable abbrev qz12 := (BSN.headSumC qz258 5)

noncomputable abbrev qz13 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 5) qz261)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq qz10 (@HAdd.hAdd Complex Complex Complex qz5 qz12 qz13) Bool.false 43548125521 17179869184 1810763484679 550975584600064 Bool.false 1640896419 8589934592 900124487629 275487792300032

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP qz12 qz13 Bool.false 46878977929 17179869184 111516116961 42382737276928 Bool.true 3641636883 17179869184 110556108581 42382737276928 Bool.true

noncomputable abbrev qz14 := (BSN.headSumC qz258 4)

noncomputable abbrev qz15 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 4) qz261)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq qz12 (@HAdd.hAdd Complex Complex Complex qz5 qz14 qz15) Bool.false 46878977929 17179869184 111516116961 42382737276928 Bool.true 3641636883 17179869184 110556108581 42382737276928

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP qz14 qz15 Bool.false 9720222481 4294967296 65260499961 34435974037504 Bool.true 508801743 17179869184 1034068809405 550975584600064 Bool.false

noncomputable abbrev qz16 := (BSN.headSumC qz258 3)

noncomputable abbrev qz413 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz262 := qz413

noncomputable abbrev qz17 := (@HPow.hPow Complex Complex Complex qz260 qz262 qz261)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq qz14 (@HAdd.hAdd Complex Complex Complex qz5 qz16 qz17) Bool.false 9720222481 4294967296 65260499961 34435974037504 Bool.true 508801743 17179869184 1034068809405 550975584600064

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP qz16 qz17 Bool.false 14558423687 8589934592 288130533803 275487792300032 Bool.true 281799621 2147483648 142390022181 137743896150016 Bool.false

noncomputable abbrev qz18 := (BSN.headSumC qz258 2)

noncomputable abbrev qz414 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz263 := qz414

noncomputable abbrev qz19 := (@HPow.hPow Complex Complex Complex qz260 qz263 qz261)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq qz16 (@HAdd.hAdd Complex Complex Complex qz5 qz18 qz19) Bool.false 14558423687 8589934592 288130533803 275487792300032 Bool.true 281799621 2147483648 142390022181 137743896150016

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP qz18 qz19 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz264 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz20 := qz264

noncomputable abbrev qz21 := qz258

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq qz18 (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz20) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz21)

noncomputable abbrev qz265 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz22 := (@Inv.inv Real Real.instInv (Real.sqrt qz265))

noncomputable abbrev qz434 := (Enclosure.sfrac Bool.false 45593 1000)

noncomputable abbrev qz415 := qz434

noncomputable abbrev qz266 := qz415

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz24 := qz266

noncomputable abbrev qz267 := (@Eq.refl Real qz415)

noncomputable abbrev qz25 := qz267

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz19 (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.false 5968489095 8589934592 288130533803 275487792300032 Bool.true 281799621 2147483648 142390022181 137743896150016 (BSN.cpow_neg_s_mk qz24 45593 1000 2 qz25 rfl)

noncomputable abbrev qz26 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz265) 185363 131072 1 131072 46340 46342 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz265) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz265 qz26)) Bool.false 185363 131072 1 131072 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz265 qz26)) Bool.false 185363 131072 1 131072 185363 131072 1 131072 (BSN.sqrt_enclosure 2 1 92681 92682 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 65536 32071 24381081 945 45426 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 6304051414227265627529049834256

noncomputable def ep57 := nat_lit 124615124604835863084731911901282304

noncomputable def ep58 := nat_lit 1869226869072537946270978678519234560

noncomputable abbrev qz268 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz269 := (BSN.cosOddQ 268435456)

noncomputable def ep59 := BSN.cos_dyadic_bound_f 50107754 268435456 2 1 131072 64205 ep56 ep57 ep56 ep56 ep58 ep56 128795 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 50107754) qz268 0 1 ep56 ep57 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 50107754) qz269 0 1 ep56 ep58 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz27 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz28 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz270 := (Enclosure.Real.IsNear.const Bool.false 45593 1000)

noncomputable abbrev qz29 := qz270

noncomputable abbrev qz30 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable abbrev qz271 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4142215) qz27)

noncomputable abbrev qz272 := (BSN.isNear_log_sfrac 2 1 45426 65536 1 32071 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 45426 65536 32071 rfl rfl rfl (ep55 rfl)))

noncomputable abbrev qz273 := (@Nat.cast Real Real.instNatCast 3526019769953450721280)

noncomputable def ep60 := @Enclosure.Real.IsNear.cos_image qz23 qz271 Bool.false 4142215 131072 187 131072 Bool.false 128795 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 1035553809 32768000 45593 32071000 4142215 131072 187 131072 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz28 45593 1000 0 1 45426 65536 1 32071 1035553809 32768000 45593 32071000 qz29 qz272 rfl) rfl) (Enclosure.sfrac_false_div 4142215 131072) (BSN.cos_reduce0 qz271 (@HDiv.hDiv Real Real Real qz2 qz273 qz30) 226375608064910080 72057594037927936 Bool.false 128795 131072 5 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 4142215 131072 226375608064910080 72057594037927936 5 3526019769953450721280 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 128795 131072 3526019769953450721280 18889465931478580854784 50107754 268435456 64205 64142 (ep59 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz274 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz275 := (BSN.sinOddQ 268435456)

noncomputable def ep61 := BSN.sin_dyadic_bound_f 50107754 268435456 1 0 131072 64205 0 1 1 0 1 1 24324 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 50107754) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 50107754) qz275 0 0 rfl) rfl rfl

noncomputable def ep62 := @Enclosure.Real.IsNear.sin_image qz23 qz271 Bool.false 4142215 131072 187 131072 Bool.false 24324 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 1035553809 32768000 45593 32071000 4142215 131072 187 131072 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz28 45593 1000 0 1 45426 65536 1 32071 1035553809 32768000 45593 32071000 qz29 qz272 rfl) rfl) (Enclosure.sfrac_false_div 4142215 131072) (BSN.sin_reduce0 qz271 (@HDiv.hDiv Real Real Real qz2 qz273 qz30) 226375608064910080 72057594037927936 Bool.false 24324 131072 5 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 4142215 131072 226375608064910080 72057594037927936 5 3526019769953450721280 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 24324 131072 3526019769953450721280 18889465931478580854784 50107754 268435456 64205 64142 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz276 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 92682 131072 2 131072 46341 65536 1 65536 (ep54 rfl rfl) rfl)

noncomputable def ep63 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.false 5968489095 8589934592 288130533803 275487792300032 Bool.true 281799621 2147483648 142390022181 137743896150016 (@Enclosure.Real.IsNear.mulLit_ff qz22 (Real.cos qz23) 46341 65536 1 65536 128795 131072 6128349 4203610112 5968489095 8589934592 288130533803 275487792300032 qz276 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.false 128795 131072 6128349 4203610112 128795 131072 6128349 4203610112 (ep60 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 46341 65536 1 65536 6081 32768 6128349 4203610112 281799621 2147483648 142390022181 137743896150016 qz276 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.false 6081 32768 6128349 4203610112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.false 24324 131072 6128349 4203610112 6081 32768 6128349 4203610112 (ep62 rfl rfl) rfl)) rfl)

noncomputable abbrev qz277 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz31 := qz277

noncomputable def ep64 := @ep51 5968489095 8589934592 288130533803 275487792300032 Bool.true 281799621 2147483648 142390022181 137743896150016 Bool.false 14558423687 14558423687 8589934592 288130533803 275487792300032 Bool.true 281799621 281799621 2147483648 142390022181 137743896150016 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz20 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz31)) (ep53 ep63) rfl rfl

noncomputable abbrev qz32 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz33 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep65 := @Enclosure.Complex.IsNear.of_eq qz17 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)))) Bool.false 4882021275 8589934592 233953465885 275487792300032 Bool.false 1745595225 17179869184 464508720681 550975584600064 (BSN.cpow_neg_s_mk qz24 45593 1000 3 qz25 rfl)

noncomputable abbrev qz34 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep66 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz34) 227023 131072 1 131072 37837 37838 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz34) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz34 qz26)) Bool.false 227023 131072 1 131072 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz34 qz26)) Bool.false 227023 131072 1 131072 227023 131072 1 131072 (BSN.sqrt_enclosure 3 1 113511 113512 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep67 := BSN.log_dyadic_bound 1 2 9 8 2258332876800 65536 32071 222698787165 2027025 71998 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1) (BSN.artanhQ 2) 0 8 222698787165 2258332876800 2027025 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep68 := nat_lit 308140322001872111587472245023610708164829343752914341352174417579830625

noncomputable def ep69 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080

noncomputable def ep70 := nat_lit 384176561753723192970134606055932232872282766425839952058608750390625

noncomputable def ep71 := nat_lit 806412176523968549940475661890127964435616966302467153142838108065590625

noncomputable def ep72 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800

noncomputable def ep73 := BSN.sin_dyadic_bound_f 374167755 268435456 3 2 131072 64205 ep68 ep69 ep70 ep71 ep72 ep70 129026 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 374167755) qz274 0 2 ep68 ep69 ep70 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 374167755) qz275 0 2 ep71 ep72 ep70 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz35 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz278 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6565209) qz27)

noncomputable abbrev qz279 := (BSN.isNear_log_sfrac 3 1 71998 65536 1 32071 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 71998 65536 32071 rfl rfl rfl (ep67 rfl)))

noncomputable def ep74 := @Enclosure.Real.IsNear.cos_image qz33 qz278 Bool.false 6565209 131072 187 131072 Bool.false 129026 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 1641302407 32768000 45593 32071000 6565209 131072 187 131072 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz35 45593 1000 0 1 71998 65536 1 32071 1641302407 32768000 45593 32071000 qz29 qz279 rfl) rfl) (Enclosure.sfrac_false_div 6565209 131072) (BSN.cos_reduce3 qz278 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 26329715083500939378688) qz30) 226375608064910080 72057594037927936 Bool.false 129026 131072 7 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q3 6565209 131072 226375608064910080 72057594037927936 7 26329715083500939378688 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 129026 131072 26329715083500939378688 18889465931478580854784 374167755 268435456 64205 64142 (ep73 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep75 := nat_lit 171359812917375050078804640393586363306181761092252785174345169211190625

noncomputable def ep76 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120

noncomputable def ep77 := nat_lit 513311085628617703850473651968647225452800717743906675618918290132790625

noncomputable def ep78 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400

noncomputable def ep79 := BSN.cos_dyadic_bound_f 374167755 268435456 3 2 131072 64205 ep75 ep76 ep70 ep77 ep78 ep70 23067 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 374167755) qz268 0 2 ep75 ep76 ep70 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 374167755) qz269 0 2 ep77 ep78 ep70 rfl rfl rfl rfl) rfl rfl

noncomputable def ep80 := @Enclosure.Real.IsNear.sin_image qz33 qz278 Bool.false 6565209 131072 187 131072 Bool.true 23067 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 1641302407 32768000 45593 32071000 6565209 131072 187 131072 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz35 45593 1000 0 1 71998 65536 1 32071 1641302407 32768000 45593 32071000 qz29 qz279 rfl) rfl) (Enclosure.sfrac_false_div 6565209 131072) (BSN.sin_reduce3 qz278 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 26329715083500939378688) qz30) 226375608064910080 72057594037927936 Bool.false 23067 131072 7 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q3 6565209 131072 226375608064910080 72057594037927936 7 26329715083500939378688 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 23067 131072 26329715083500939378688 18889465931478580854784 374167755 268435456 64205 64142 (ep79 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz280 := (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 75675 131072 1 131072 75675 131072 1 131072 (ep66 rfl rfl) rfl)

noncomputable def ep81 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33))) Bool.false 4882021275 8589934592 233953465885 275487792300032 Bool.false 1745595225 17179869184 464508720681 550975584600064 (@Enclosure.Real.IsNear.mulLit_ff qz32 (Real.cos qz33) 75675 131072 1 131072 64513 65536 6128349 4203610112 4882021275 8589934592 233953465885 275487792300032 qz280 (@Enclosure.Real.IsNear.recentre' (Real.cos qz33) Bool.false 129026 131072 6128349 4203610112 64513 65536 6128349 4203610112 (ep74 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)) 75675 131072 1 131072 23067 131072 6128349 4203610112 1745595225 17179869184 464508720681 550975584600064 qz280 (@Enclosure.Real.IsNear.neg (Real.sin qz33) Bool.true 23067 131072 6128349 4203610112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz33) Bool.true 23067 131072 6128349 4203610112 23067 131072 6128349 4203610112 (ep80 rfl rfl) rfl)) rfl)

noncomputable def ep82 := @ep49 4882021275 8589934592 233953465885 275487792300032 Bool.false 1745595225 17179869184 464508720681 550975584600064 Bool.false 166992150662955925504 9720222481 4294967296 65260499961 34435974037504 Bool.true 1092643423166398464 508801743 17179869184 1034068809405 550975584600064 (ep50 (BSN.head_sum_c_succ qz21 2 3 rfl rfl) (ep64 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep65 ep81) rfl rfl

noncomputable abbrev qz281 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz281))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep83 := @Enclosure.Complex.IsNear.of_eq qz15 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.false 7998088005 17179869184 405541521117 550975584600064 Bool.true 783208785 4294967296 100790150537 137743896150016 (BSN.cpow_neg_s_mk qz24 45593 1000 4 qz25 rfl)

noncomputable def ep84 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz281) 262145 131072 1 131072 32767 32768 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz281) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz281 qz26)) Bool.false 262145 131072 1 131072 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz281 qz26)) Bool.false 262145 131072 1 131072 262145 131072 1 131072 (BSN.sqrt_enclosure 4 1 131072 131073 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep85 := nat_lit 753960950911045074462890625

noncomputable def ep86 := nat_lit 117048680082474133384580175

noncomputable def ep87 := BSN.log_dyadic_bound 3 5 12 11 ep85 65536 32071 ep86 431467934736729065175 90852 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 3) (BSN.artanhQ 5) 0 11 ep86 ep85 431467934736729065175 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep88 := nat_lit 100864826653553042772984189904561

noncomputable def ep89 := BSN.cos_dyadic_bound_f 100215509 268435456 2 1 131072 64205 ep88 ep57 ep88 ep88 ep58 ep88 122043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 100215509) qz268 0 1 ep88 ep57 ep88 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 100215509) qz269 0 1 ep88 ep58 ep88 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz38 := (@Nat.cast Real Real.instNatCast 65536)

noncomputable abbrev qz39 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz282 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4142215) qz38)

noncomputable abbrev qz283 := (BSN.isNear_log_sfrac 4 1 90852 65536 1 32071 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 90852 65536 32071 rfl rfl rfl (ep87 rfl)))

noncomputable abbrev qz284 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep90 := @Enclosure.Real.IsNear.cos_image qz37 qz282 Bool.false 4142215 65536 187 131072 Bool.false 122043 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 1035553809 16384000 45593 32071000 4142215 65536 187 131072 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz39 45593 1000 0 1 90852 65536 1 32071 1035553809 16384000 45593 32071000 qz29 qz283 rfl) rfl) (Enclosure.sfrac_false_div 4142215 65536) (BSN.cos_reduce0 qz282 (@HDiv.hDiv Real Real Real qz2 qz273 qz284) 226375608064910080 72057594037927936 Bool.false 122043 131072 10 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 4142215 65536 226375608064910080 72057594037927936 10 3526019769953450721280 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 122043 131072 3526019769953450721280 9444732965739290427392 100215509 268435456 64205 64142 (ep89 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep91 := nat_lit 623075623024179315423659559506411520

noncomputable def ep92 := nat_lit 4361529361169255207965616916544880640

noncomputable def ep93 := BSN.sin_dyadic_bound_f 100215509 268435456 2 1 131072 64205 ep88 ep91 ep88 ep88 ep92 ep88 47804 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 100215509) qz274 0 1 ep88 ep91 ep88 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 100215509) qz275 0 1 ep88 ep92 ep88 rfl rfl rfl rfl) rfl rfl

noncomputable def ep94 := @Enclosure.Real.IsNear.sin_image qz37 qz282 Bool.false 4142215 65536 187 131072 Bool.false 47804 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 1035553809 16384000 45593 32071000 4142215 65536 187 131072 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz39 45593 1000 0 1 90852 65536 1 32071 1035553809 16384000 45593 32071000 qz29 qz283 rfl) rfl) (Enclosure.sfrac_false_div 4142215 65536) (BSN.sin_reduce0 qz282 (@HDiv.hDiv Real Real Real qz2 qz273 qz284) 226375608064910080 72057594037927936 Bool.false 47804 131072 10 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 4142215 65536 226375608064910080 72057594037927936 10 3526019769953450721280 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 47804 131072 3526019769953450721280 9444732965739290427392 100215509 268435456 64205 64142 (ep93 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz285 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 65535 131072 1 131072 65535 131072 1 131072 (ep84 rfl rfl) rfl)

noncomputable def ep95 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.false 7998088005 17179869184 405541521117 550975584600064 Bool.true 783208785 4294967296 100790150537 137743896150016 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz37) 65535 131072 1 131072 122043 131072 6128349 4203610112 7998088005 17179869184 405541521117 550975584600064 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.false 122043 131072 6128349 4203610112 122043 131072 6128349 4203610112 (ep90 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 65535 131072 1 131072 11951 32768 6128349 4203610112 783208785 4294967296 100790150537 137743896150016 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.false 11951 32768 6128349 4203610112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.false 47804 131072 6128349 4203610112 11951 32768 6128349 4203610112 (ep94 rfl rfl) rfl)) rfl)

noncomputable def ep96 := @ep47 7998088005 17179869184 405541521117 550975584600064 Bool.true 783208785 4294967296 100790150537 137743896150016 Bool.false 201343677074960809984 46878977929 17179869184 111516116961 42382737276928 Bool.true 15640711316392378368 3641636883 17179869184 110556108581 42382737276928 (ep48 (BSN.head_sum_c_succ qz21 3 4 rfl rfl) (ep82 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep83 ep95) rfl rfl

noncomputable abbrev qz286 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz40 := (@Inv.inv Real Real.instInv (Real.sqrt qz286))

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep97 := @Enclosure.Complex.IsNear.of_eq qz13 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)))) Bool.true 416356551 2147483648 180526982093 275487792300032 Bool.false 6923429721 17179869184 363019563705 550975584600064 (BSN.cpow_neg_s_mk qz24 45593 1000 5 qz25 rfl)

noncomputable def ep98 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz286) 293085 131072 1 131072 29308 29309 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz286) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz286 qz26)) Bool.false 293085 131072 1 131072 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz286 qz26)) Bool.false 293085 131072 1 131072 293085 131072 1 131072 (BSN.sqrt_enclosure 5 1 146542 146543 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep99 := nat_lit 141613827518379161815574079375

noncomputable def ep100 := nat_lit 29325128709309236875766211300

noncomputable def ep101 := BSN.log_dyadic_bound 2 3 15 14 ep99 65536 32071 ep100 57299708096576225280000 105476 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP 2) (BSN.artanhQ 3) 0 14 ep100 ep99 57299708096576225280000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep102 := nat_lit 71945091587556131876572711151977323976755748215687126489993756338961121

noncomputable def ep103 := nat_lit 67896072823075474655928167747242296866316649210041114862727911062241

noncomputable def ep104 := nat_lit 215699482617022244680406277120437487336534611348641297240255813194758881

noncomputable def ep105 := BSN.cos_dyadic_bound_f 301287131 268435456 3 2 131072 64205 ep102 ep76 ep103 ep104 ep78 ep103 56824 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 301287131) qz268 0 2 ep102 ep76 ep103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 301287131) qz269 0 2 ep104 ep78 ep103 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz42 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz287 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4808967) qz38)

noncomputable abbrev qz288 := (BSN.isNear_log_sfrac 5 1 105476 65536 1 32071 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 105476 65536 32071 rfl rfl rfl (ep101 rfl)))

noncomputable def ep106 := @Enclosure.Real.IsNear.cos_image qz41 qz287 Bool.false 4808967 65536 187 131072 Bool.true 56824 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 1202241817 16384000 45593 32071000 4808967 65536 187 131072 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz42 45593 1000 0 1 105476 65536 1 32071 1202241817 16384000 45593 32071000 qz29 qz288 rfl) rfl) (Enclosure.sfrac_false_div 4808967 65536) (BSN.cos_reduce2 qz287 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10600598549054823071744) qz284) 226375608064910080 72057594037927936 Bool.false 56824 131072 11 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q2 4808967 65536 226375608064910080 72057594037927936 11 10600598549054823071744 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 56824 131072 10600598549054823071744 9444732965739290427392 301287131 268435456 64205 64142 (ep105 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep107 := nat_lit 129446847999342576998106137539361389320667293468868794790098579081280225

noncomputable def ep108 := nat_lit 338917532070850341369406476521974770216345065462602015026194719071156961

noncomputable def ep109 := BSN.sin_dyadic_bound_f 301287131 268435456 3 2 131072 64205 ep107 ep69 ep103 ep108 ep72 ep103 118113 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 301287131) qz274 0 2 ep107 ep69 ep103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 301287131) qz275 0 2 ep108 ep72 ep103 rfl rfl rfl rfl) rfl rfl

noncomputable def ep110 := @Enclosure.Real.IsNear.sin_image qz41 qz287 Bool.false 4808967 65536 187 131072 Bool.true 118113 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 1202241817 16384000 45593 32071000 4808967 65536 187 131072 (@Enclosure.Real.IsNear.mulLit_ff qz24 qz42 45593 1000 0 1 105476 65536 1 32071 1202241817 16384000 45593 32071000 qz29 qz288 rfl) rfl) (Enclosure.sfrac_false_div 4808967 65536) (BSN.sin_reduce2 qz287 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10600598549054823071744) qz284) 226375608064910080 72057594037927936 Bool.false 118113 131072 11 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q2 4808967 65536 226375608064910080 72057594037927936 11 10600598549054823071744 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 118113 131072 10600598549054823071744 9444732965739290427392 301287131 268435456 64205 64142 (ep109 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz289 := (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 58617 131072 1 131072 58617 131072 1 131072 (ep98 rfl rfl) rfl)

noncomputable def ep111 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41))) Bool.true 416356551 2147483648 180526982093 275487792300032 Bool.false 6923429721 17179869184 363019563705 550975584600064 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz41) 58617 131072 1 131072 7103 16384 6128349 4203610112 416356551 2147483648 180526982093 275487792300032 qz289 (@Enclosure.Real.IsNear.recentre' (Real.cos qz41) Bool.true 56824 131072 6128349 4203610112 7103 16384 6128349 4203610112 (ep106 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)) 58617 131072 1 131072 118113 131072 6128349 4203610112 6923429721 17179869184 363019563705 550975584600064 qz289 (@Enclosure.Real.IsNear.neg (Real.sin qz41) Bool.true 118113 131072 6128349 4203610112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz41) Bool.true 118113 131072 6128349 4203610112 118113 131072 6128349 4203610112 (ep110 rfl rfl) rfl)) rfl)

noncomputable def ep112 := @ep45 416356551 2147483648 180526982093 275487792300032 Bool.false 6923429721 17179869184 363019563705 550975584600064 Bool.false 93518887457398980608 43548125521 17179869184 1810763484679 550975584600064 Bool.false 56380771645828104192 1640896419 8589934592 900124487629 275487792300032 (ep46 (BSN.head_sum_c_succ qz21 4 5 rfl rfl) (ep96 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep97 ep111) rfl rfl

noncomputable abbrev qz290 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz43 := (@Inv.inv Real Real.instInv (Real.sqrt qz290))

noncomputable abbrev qz44 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep113 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)))) Bool.false 3506644075 8589934592 169031583135 275487792300032 Bool.true 34647725 8589934592 164869729465 275487792300032 (BSN.cpow_neg_s_mk qz24 45593 1000 6 qz25 rfl)

noncomputable abbrev qz291 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz26)

noncomputable def ep114 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz290) 321059 131072 1 131072 26754 26756 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz290) (Real.sqrt qz291) Bool.false 321059 131072 1 131072 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz291) Bool.false 321059 131072 1 131072 321059 131072 1 131072 (BSN.sqrt_enclosure 6 1 160529 160530 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep115 := BSN.log_dyadic_bound 2 10 4 3 105000000 65536 32071 1434560 960 26572 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz45 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep116 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz45 45593 1000 0 1 4034664351997175 2251799813685248 500000000032071 16035500000000000000 7358098072024287991 90071992547409920 22796500001462213103 16035500000000000000000 qz29 (BSN.isNear_log_sfrac 6 1 4034664351997175 2251799813685248 500000000032071 16035500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz291) Bool.false 4230652207559789772800 2361183241434822606848 1000000000064142 32071000000000000000 4034664351997175 2251799813685248 500000000032071 16035500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 26572 65536 24973259072661432 36028797018963968 32071 1000000000000000 rfl rfl rfl rfl (ep115 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep117 := BSN.cos_dyadic_bound_f 2652898 268435456 1 0 131072 64205 0 1 1 0 1 1 131065 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 2652898) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 2652898) qz269 0 0 rfl) rfl rfl

noncomputable abbrev qz292 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10707441) qz27)

noncomputable def ep118 := @Enclosure.Real.IsNear.cos_image qz44 qz292 Bool.false 10707441 131072 47 32768 Bool.false 131065 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 7358098072024287991 90071992547409920 22796500001462213103 16035500000000000000000 10707441 131072 47 32768 (ep116 rfl) rfl) (Enclosure.sfrac_false_div 10707441 131072) (BSN.cos_reduce0 qz292 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 186681111367785644032) qz30) 226375608064910080 72057594037927936 Bool.false 131065 131072 13 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 10707441 131072 226375608064910080 72057594037927936 13 186681111367785644032 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 131065 131072 186681111367785644032 18889465931478580854784 2652898 268435456 64205 64142 (ep117 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep119 := BSN.sin_dyadic_bound_f 2652898 268435456 1 0 131072 64205 0 1 1 0 1 1 1295 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2652898) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2652898) qz275 0 0 rfl) rfl rfl

noncomputable def ep120 := @Enclosure.Real.IsNear.sin_image qz44 qz292 Bool.false 10707441 131072 47 32768 Bool.false 1295 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 7358098072024287991 90071992547409920 22796500001462213103 16035500000000000000000 10707441 131072 47 32768 (ep116 rfl) rfl) (Enclosure.sfrac_false_div 10707441 131072) (BSN.sin_reduce0 qz292 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 186681111367785644032) qz30) 226375608064910080 72057594037927936 Bool.false 1295 131072 13 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 10707441 131072 226375608064910080 72057594037927936 13 186681111367785644032 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1295 131072 186681111367785644032 18889465931478580854784 2652898 268435456 64205 64142 (ep119 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz293 := (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 53510 131072 2 131072 26755 65536 1 65536 (ep114 rfl rfl) rfl)

noncomputable def ep121 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44))) Bool.false 3506644075 8589934592 169031583135 275487792300032 Bool.true 34647725 8589934592 164869729465 275487792300032 (@Enclosure.Real.IsNear.mulLit_ff qz43 (Real.cos qz44) 26755 65536 1 65536 131065 131072 1540105 1050902528 3506644075 8589934592 169031583135 275487792300032 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz44) Bool.false 131065 131072 1540105 1050902528 131065 131072 1540105 1050902528 (ep118 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)) 26755 65536 1 65536 1295 131072 1540105 1050902528 34647725 8589934592 164869729465 275487792300032 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz44) Bool.false 1295 131072 1540105 1050902528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz44) Bool.false 1295 131072 1540105 1050902528 1295 131072 1540105 1050902528 (ep120 rfl rfl) rfl)) rfl)

noncomputable def ep122 := @ep43 3506644075 8589934592 169031583135 275487792300032 Bool.true 34647725 8589934592 164869729465 275487792300032 Bool.false 434319236312944607232 50561413671 17179869184 2148826650949 550975584600064 Bool.false 13797571219945422848 803124347 4294967296 532497108547 137743896150016 (ep44 (BSN.head_sum_c_succ qz21 5 6 rfl rfl) (ep112 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep113 ep121) rfl rfl

noncomputable abbrev qz294 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt qz294))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep123 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.false 4730719631 17179869184 308262019501 550975584600064 Bool.true 4447939603 17179869184 308078958233 550975584600064 (BSN.cpow_neg_s_mk qz24 45593 1000 7 qz25 rfl)

noncomputable abbrev qz295 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) qz26)

noncomputable def ep124 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz294) 346783 131072 1 131072 24770 24771 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz294) (Real.sqrt qz295) Bool.false 346783 131072 1 131072 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz295) Bool.false 346783 131072 1 131072 346783 131072 1 131072 (BSN.sqrt_enclosure 7 1 173391 173392 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep125 := BSN.log_dyadic_bound 3 11 5 4 202569142545 65536 32071 5259111624 688905 36674 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz48 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep126 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz48 45593 1000 0 1 4381766428990711 2251799813685248 500000000032071 16035500000000000000 199777876796973486623 2251799813685248000 22796500001462213103 16035500000000000000000 qz29 (BSN.isNear_log_sfrac 7 1 4381766428990711 2251799813685248 500000000032071 16035500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz295) Bool.false 4594615115045363777536 2361183241434822606848 1000000000064142 32071000000000000000 4381766428990711 2251799813685248 500000000032071 16035500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 36674 65536 24973259072661432 36028797018963968 32071 1000000000000000 rfl rfl rfl rfl (ep125 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep127 := nat_lit 1683536681243603074667419446557761

noncomputable def ep128 := BSN.cos_dyadic_bound_f 202560913 268435456 2 1 131072 64205 ep127 ep57 ep127 ep127 ep58 ep127 95491 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 202560913) qz268 0 1 ep127 ep57 ep127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 202560913) qz269 0 1 ep127 ep58 ep127 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz296 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5814301) qz38)

noncomputable def ep129 := @Enclosure.Real.IsNear.cos_image qz47 qz296 Bool.false 5814301 65536 47 32768 Bool.false 95491 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 199777876796973486623 2251799813685248000 22796500001462213103 16035500000000000000000 5814301 65536 47 32768 (ep126 rfl) rfl) (Enclosure.sfrac_false_div 5814301 65536) (BSN.cos_reduce0 qz296 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7126978536687840264192) qz284) 226375608064910080 72057594037927936 Bool.false 95491 131072 14 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 5814301 65536 226375608064910080 72057594037927936 14 7126978536687840264192 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 95491 131072 7126978536687840264192 9444732965739290427392 202560913 268435456 64205 64142 (ep128 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep130 := BSN.sin_dyadic_bound_f 202560913 268435456 2 1 131072 64205 ep127 ep91 ep127 ep127 ep92 ep127 89783 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 202560913) qz274 0 1 ep127 ep91 ep127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 202560913) qz275 0 1 ep127 ep92 ep127 rfl rfl rfl rfl) rfl rfl

noncomputable def ep131 := @Enclosure.Real.IsNear.sin_image qz47 qz296 Bool.false 5814301 65536 47 32768 Bool.false 89783 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 199777876796973486623 2251799813685248000 22796500001462213103 16035500000000000000000 5814301 65536 47 32768 (ep126 rfl) rfl) (Enclosure.sfrac_false_div 5814301 65536) (BSN.sin_reduce0 qz296 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7126978536687840264192) qz284) 226375608064910080 72057594037927936 Bool.false 89783 131072 14 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 5814301 65536 226375608064910080 72057594037927936 14 7126978536687840264192 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 89783 131072 7126978536687840264192 9444732965739290427392 202560913 268435456 64205 64142 (ep130 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz297 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 49541 131072 1 131072 49541 131072 1 131072 (ep124 rfl rfl) rfl)

noncomputable def ep132 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.false 4730719631 17179869184 308262019501 550975584600064 Bool.true 4447939603 17179869184 308078958233 550975584600064 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz47) 49541 131072 1 131072 95491 131072 1540105 1050902528 4730719631 17179869184 308262019501 550975584600064 qz297 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.false 95491 131072 1540105 1050902528 95491 131072 1540105 1050902528 (ep129 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 49541 131072 1 131072 89783 131072 1540105 1050902528 4447939603 17179869184 308078958233 550975584600064 qz297 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.false 89783 131072 1540105 1050902528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.false 89783 131072 1540105 1050902528 89783 131072 1540105 1050902528 (ep131 rfl rfl) rfl)) rfl)

noncomputable def ep133 := @ep41 4730719631 17179869184 308262019501 550975584600064 Bool.true 4447939603 17179869184 308078958233 550975584600064 Bool.false 949911617032649965568 27646066651 8589934592 1228544335225 275487792300032 Bool.true 5306183909522800640 1235442215 17179869184 2438067392421 550975584600064 (ep42 (BSN.head_sum_c_succ qz21 6 7 rfl rfl) (ep122 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep123 ep132) rfl rfl

noncomputable abbrev qz298 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt qz298))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep134 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.false 5145565617 17179869184 287561016985 550975584600064 Bool.true 3227418945 17179869184 286233534153 550975584600064 (BSN.cpow_neg_s_mk qz24 45593 1000 8 qz25 rfl)

noncomputable abbrev qz299 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz26)

noncomputable def ep135 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz298) 370727 131072 1 131072 23170 23171 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz298) (Real.sqrt qz299) Bool.false 370727 131072 1 131072 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz299) Bool.false 370727 131072 1 131072 370727 131072 1 131072 (BSN.sqrt_enclosure 8 1 185363 185364 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep136 := BSN.log_dyadic_bound 0 16 1 0 1 65536 32071 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz51 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep137 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz51 45593 1000 0 1 9364972152248037 4503599627370496 1000000000096213 32071000000000000000 426977175337444750941 4503599627370496000 45593000004386639309 32071000000000000000000 qz29 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000096213 32071000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz299) Bool.false 4909942519757818822656 2361183241434822606848 1000000000096213 32071000000000000000 9364972152248037 4503599627370496 1000000000096213 32071000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 65536 24973259072661432 36028797018963968 32071 1000000000000000 rfl rfl rfl rfl (ep136 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep138 := nat_lit 511352081818620923439037846388736

noncomputable def ep139 := BSN.cos_dyadic_bound_f 150376512 268435456 2 1 131072 64205 ep138 ep57 ep138 ep138 ep58 ep138 111037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 150376512) qz268 0 1 ep138 ep57 ep138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 150376512) qz269 0 1 ep138 ep58 ep138 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz300 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12426671) qz27)

noncomputable def ep140 := @Enclosure.Real.IsNear.cos_image qz50 qz300 Bool.false 12426671 131072 187 131072 Bool.false 111037 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 426977175337444750941 4503599627370496000 45593000004386639309 32071000000000000000000 12426671 131072 187 131072 (ep137 rfl) rfl) (Enclosure.sfrac_false_div 12426671 131072) (BSN.cos_reduce0 qz300 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10581806304750324416512) qz30) 226375608064910080 72057594037927936 Bool.false 111037 131072 15 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 12426671 131072 226375608064910080 72057594037927936 15 10581806304750324416512 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 111037 131072 10581806304750324416512 18889465931478580854784 150376512 268435456 64205 64142 (ep139 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep141 := BSN.sin_dyadic_bound_f 150376512 268435456 2 1 131072 64205 ep138 ep91 ep138 ep138 ep92 ep138 69645 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 150376512) qz274 0 1 ep138 ep91 ep138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 150376512) qz275 0 1 ep138 ep92 ep138 rfl rfl rfl rfl) rfl rfl

noncomputable def ep142 := @Enclosure.Real.IsNear.sin_image qz50 qz300 Bool.false 12426671 131072 187 131072 Bool.false 69645 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 426977175337444750941 4503599627370496000 45593000004386639309 32071000000000000000000 12426671 131072 187 131072 (ep137 rfl) rfl) (Enclosure.sfrac_false_div 12426671 131072) (BSN.sin_reduce0 qz300 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10581806304750324416512) qz30) 226375608064910080 72057594037927936 Bool.false 69645 131072 15 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 12426671 131072 226375608064910080 72057594037927936 15 10581806304750324416512 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 69645 131072 10581806304750324416512 18889465931478580854784 150376512 268435456 64205 64142 (ep141 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz301 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 46341 131072 1 131072 46341 131072 1 131072 (ep135 rfl rfl) rfl)

noncomputable def ep143 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.false 5145565617 17179869184 287561016985 550975584600064 Bool.true 3227418945 17179869184 286233534153 550975584600064 (@Enclosure.Real.IsNear.mulLit_ff qz49 (Real.cos qz50) 46341 131072 1 131072 111037 131072 6128349 4203610112 5145565617 17179869184 287561016985 550975584600064 qz301 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.false 111037 131072 6128349 4203610112 111037 131072 6128349 4203610112 (ep140 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 46341 131072 1 131072 69645 131072 6128349 4203610112 3227418945 17179869184 286233534153 550975584600064 qz301 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.false 69645 131072 6128349 4203610112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.false 69645 131072 6128349 4203610112 69645 131072 6128349 4203610112 (ep142 rfl rfl) rfl)) rfl)

noncomputable def ep144 := @ep39 5145565617 17179869184 287561016985 550975584600064 Bool.true 3227418945 17179869184 286233534153 550975584600064 Bool.false 519155880605199106048 60437698919 17179869184 2744649687435 550975584600064 Bool.true 76671370915154493440 557857645 2147483648 1362150463287 275487792300032 (ep40 (BSN.head_sum_c_succ qz21 7 8 rfl rfl) (ep133 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep134 ep143) rfl rfl

theorem EMRow09.d6 : Enclosure.Complex.IsNear qz4 Bool.false 60437698919 17179869184 2744649687435 550975584600064 Bool.true 557857645 2147483648 1362150463287 275487792300032 := ep38 (BSN.head_sum_c_succ qz21 8 9 rfl rfl) (ep144 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow09.d7 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow09.d8 : @Eq Nat (Nat.pow 10 1) 10 := @Eq.refl Nat 10

noncomputable def ep145 := nat_lit 210130674456698629577212433753

noncomputable def ep146 := nat_lit 56177135662501353618407424000

noncomputable def ep147 := nat_lit 544564156287141803625030822541831913

noncomputable def ep148 := nat_lit 57780939011792666925414835902480384000

noncomputable abbrev qz435 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz416 := qz435

noncomputable abbrev qz302 := qz416

noncomputable abbrev qz52 := qz302

noncomputable abbrev qz53 := (@instHSub Real Real.instSub)

noncomputable abbrev qz417 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz303 := qz417

noncomputable abbrev qz54 := qz303

noncomputable abbrev qz436 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz437 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz418 := (@HAdd.hAdd Complex Complex Complex qz433 (@HAdd.hAdd Complex Complex Complex qz433 qz436 (@HMul.hMul Complex Complex Complex qz435 Complex.I (@HDiv.hDiv Complex Complex Complex qz437 (↑qz434) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz304 := qz418

noncomputable abbrev qz55 := (Complex.Stirling.logGammaStirling 1 qz304)

noncomputable abbrev qz419 := (@HAdd.hAdd Complex Complex Complex qz433 qz436 (@HMul.hMul Complex Complex Complex qz435 Complex.I (@HDiv.hDiv Complex Complex Complex qz437 (↑qz434) (2 : Complex))))

noncomputable abbrev qz305 := qz419

noncomputable abbrev qz56 := qz305

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz253 (@HDiv.hDiv Real Real Real qz256 qz266 (2 : Real)) (Real.log Real.pi))

noncomputable def ep149 := Complex.re (@HMul.hMul Complex Complex Complex qz52 (Complex.exp (@HMul.hMul Complex Complex Complex qz52 Complex.I ↑(@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))))) qz57))) (zetaApproximant qz21 1 10))

noncomputable def ep150 := @Enclosure.Real.IsNear.of_eq ep149 (@HSub.hSub Real Real Real qz53 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))))) qz57)) (Complex.re (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))))) qz57)) (Complex.im (zetaApproximant qz21 1 10))))

noncomputable def ep151 := nat_lit 210130684058077105472061009323

noncomputable def ep152 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))))) qz57)) (Complex.re (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))))) qz57)) (Complex.im (zetaApproximant qz21 1 10))) ep151

noncomputable def ep153 := nat_lit 543978769698735544198422194506310683

noncomputable def ep154 := nat_lit 1872571188750045120613580800

noncomputable def ep155 := nat_lit 58538658840625942660862803552123

noncomputable def ep156 := nat_lit 5778093901179266692541483590248038400

noncomputable def ep157 := nat_lit 393484646860228894412860230563983068198650602232112742400

noncomputable def ep158 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))))) qz57)) (Complex.re (zetaApproximant qz21 1 10)) 131071 131072 4075805

noncomputable def ep159 := nat_lit 1603182123109437674787413

noncomputable def ep160 := nat_lit 39739318253810877758749079

noncomputable def ep161 := nat_lit 6872775718048404357513216000

noncomputable def ep162 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))))) qz57)) Bool.true 131071 131072 4075805

noncomputable abbrev qz306 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1441209) qz38)

noncomputable def ep163 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))))) qz57) qz306 Bool.false 1441209 65536 123

noncomputable def ep164 := nat_lit 242515968000000000000000000

noncomputable def ep165 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))))) qz57) Bool.false 237693947559074174977 10808639105689190400 225994697079379666989679 ep164

noncomputable def ep166 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))))) qz57 2598771708081328355333 54043195528445952000 57277800579379666989679 ep164 3420432453 131072000

noncomputable def ep167 := nat_lit 155775105472314851312926720000

noncomputable def ep168 := nat_lit 262725632000000000000000000

noncomputable def ep169 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 160650298050569426207 4503599627370496000 105063706030896125053069 ep168 Bool.false 2598771708081328355333 54043195528445952000

noncomputable def ep170 := @Enclosure.Complex.IsNear.subLitP qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 132481301997903907207 4503599627370496000 100967706028531594365069 ep168 Bool.false 2765000892060666659333 54043195528445952000 646307407528782963281827

noncomputable def ep171 := nat_lit 3152707584000000000000000000

noncomputable def ep172 := nat_lit 723504622437503587829992994920988672

noncomputable def ep173 := nat_lit 731489206008503611843720130695528448

noncomputable abbrev qz438 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz420 := qz438

noncomputable abbrev qz307 := (@HSub.hSub Complex Complex Complex qz417 qz418 qz420)

noncomputable abbrev qz308 := (Complex.log qz418)

noncomputable abbrev qz58 := (@HSub.hSub Complex Complex Complex qz303 (@HMul.hMul Complex Complex Complex qz302 qz307 qz308) qz304)

noncomputable abbrev qz309 := qz420

noncomputable abbrev qz59 := (@HMul.hMul Complex Complex Complex qz302 qz309 ↑(Real.log qz257))

noncomputable abbrev qz421 := qz437

noncomputable abbrev qz310 := qz421

noncomputable abbrev qz60 := qz310

noncomputable abbrev qz61 := (@instHMul Nat instMulNat)

noncomputable abbrev qz422 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz311 := qz422

noncomputable abbrev qz62 := qz311

noncomputable abbrev qz63 := qz304

noncomputable abbrev qz312 := (@instHSub Int Int.instSub)

noncomputable abbrev qz64 := qz312

noncomputable abbrev qz313 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz65 := qz313

noncomputable abbrev qz314 := (@instHMul Int Int.instMul)

noncomputable abbrev qz66 := qz314

noncomputable abbrev qz315 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz67 := qz315

noncomputable def ep174 := @Enclosure.Complex.IsNear.of_eq qz55 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz58 qz59) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz54 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz63 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k)))))) Bool.true 132481301997903907207

noncomputable def ep175 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz58 qz59) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz54 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz63 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) Bool.true 132482911220228131207 4503599627370496000

noncomputable def ep176 := nat_lit 284501429706248371002341851136

noncomputable def ep177 := nat_lit 593779420240569467489640408678400

noncomputable def ep178 := @ep175 49300458498566199603 128284000000000000000000 Bool.false 184346436230431705259 3602879701896396800 26296500013272166427 128284000000000000000000 Bool.false 767337 2147483648 3 2147483648 Bool.true 11661731947 3221225472000 45593 3221225472000 Bool.true ep176 132481301997903907207 4503599627370496000 100967706028531594365069 ep168 Bool.false ep177

noncomputable def ep179 := @Enclosure.Complex.IsNear.addLitP qz58 qz59 Bool.true 136621404267700259207 4503599627370496000 47343000002472449603 128284000000000000000000

noncomputable def ep180 := nat_lit 8682400069728870806781952

noncomputable def ep181 := @ep179 Bool.false 184346436230431705259 3602879701896396800 26296500013272166427 128284000000000000000000 Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 Bool.true ep180 132482911220228131207 4503599627370496000 49300458498566199603 128284000000000000000000 Bool.false 184346436230431705259 184346436230431705259 3602879701896396800

noncomputable abbrev qz68 := (@HMul.hMul Complex Complex Complex qz302 qz307 qz308)

noncomputable def ep182 := @Enclosure.Complex.IsNear.subLitP qz68 qz63 Bool.true 126488305106116643207 4503599627370496000 47343000002472449603 128284000000000000000000 Bool.false 1332397416773564574551

noncomputable def ep183 := nat_lit 3686928724608634105180000

noncomputable def ep184 := @ep182 18014398509481984000 26296500013272166427 128284000000000000000000 Bool.false 9000 4000 0 1 Bool.false 91186 4000 0 1 Bool.true 546485617070801036828000 136621404267700259207 4503599627370496000 47343000002472449603 128284000000000000000000 Bool.false ep183 184346436230431705259 3602879701896396800 26296500013272166427 128284000000000000000000

noncomputable abbrev qz69 := qz307

noncomputable abbrev qz70 := qz308

noncomputable def ep185 := @Enclosure.Complex.IsNear.mul qz69 qz70 Bool.true 126488305106116643207 4503599627370496000 47343000002472449603 128284000000000000000000 Bool.false 1332397416773564574551 18014398509481984000 26296500013272166427

noncomputable abbrev qz71 := (Complex.re qz307)

noncomputable abbrev qz72 := (Complex.re qz308)

noncomputable abbrev qz73 := (Complex.im qz307)

noncomputable abbrev qz74 := (Complex.im qz308)

noncomputable def ep186 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz71 qz72) (@HMul.hMul Real Real Real qz0 qz73 qz74) 197439364736360649 36028797018963968 3500000002020473 256568000000000000000 37792056424540431083 1125899906842624000

noncomputable def ep187 := nat_lit 1139305367485265041708266151261241344

noncomputable def ep188 := @Enclosure.Real.IsNear.mulLit_ff qz71 qz72 7000 4000 0 1 28205623533765807 9007199254740992 500000000288639 64142000000000000000

noncomputable def ep189 := @Enclosure.Complex.IsNear.re_isNear qz69 Bool.false 7000 4000 0 1 Bool.false 91186 4000 0 1

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 91186 4000)

noncomputable abbrev qz75 := qz316

noncomputable def ep190 := @Enclosure.Complex.IsNear.of_eq qz69 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz75) Bool.false 7000 4000 0 1 Bool.false 91186 4000 0

noncomputable abbrev qz317 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz76 := (Complex.mk qz317 qz316)

noncomputable def ep191 := @Enclosure.Complex.IsNear.of_eq qz70 (Complex.log qz76) Bool.false 28205623533765807 9007199254740992 500000000288639 64142000000000000000 Bool.false 828900410688931 562949953421312 1000000000032071 64142000000000000000

noncomputable def ep192 := BSN.log_dyadic_bound 203886596 16587886596 1 0 1 131072 64142 0 1 3222 16791773192 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 203886596) (BSN.artanhQ 16587886596) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz77 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz318 := (Real.log (Enclosure.sfrac Bool.false 8395886596 16000000))

noncomputable abbrev qz319 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz320 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep193 := @Enclosure.Real.IsNear.mulLit_ff qz77 qz318 1 2 0 1 28205623533765807 4503599627370496 500000000288639 32071000000000000000 28205623533765807 9007199254740992 500000000288639 64142000000000000000 qz319 (BSN.isNear_log_sfrac 8395886596 16000000 28205623533765807 4503599627370496 500000000288639 32071000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8395886596) qz320)) Bool.false 29575739902542014840832 4722366482869645213696 1000000000577278 64142000000000000000 28205623533765807 4503599627370496 500000000288639 32071000000000000000 (BSN.log_rat_reduce_isNear 8395886596 16000000 9 16791773192 16384000000 3222 131072 24973259072661432 36028797018963968 64142 1000000000000000 rfl rfl rfl rfl (ep192 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep194 := BSN.arctan_dyadic_bound_f 9000 91186 1 0 131072 64142 0 1 1 0 1 1 12894 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 91186) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 91186) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz78 := (@HMul.hMul Real Real Real qz253 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz79 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz319 BSN.pi_near_15 rfl)

noncomputable abbrev qz321 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 91186)))

noncomputable def ep195 := @Enclosure.Real.IsNear.subLit_ff_p qz78 qz321 884279719003555 562949953421312 1 2000000000000000 12894 131072 1 64142 108645634629819564032 828900410688931 562949953421312 1000000000032071 64142000000000000000 qz79 (ep194 rfl) rfl rfl

noncomputable abbrev qz322 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 91186) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep196 := @Enclosure.Complex.IsNear.re_isNear qz70 Bool.false 28205623533765807 9007199254740992 500000000288639 64142000000000000000 Bool.false 828900410688931 562949953421312 1000000000032071 64142000000000000000 (ep191 (@congrArg Complex Complex qz63 qz76 Complex.log (BSN.w_shift_mk qz24 Bool.false 45593 1000 2 qz25 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz76) Bool.false 28205623533765807 9007199254740992 500000000288639 64142000000000000000 Bool.false 828900410688931 562949953421312 1000000000032071 64142000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz76)) (@HMul.hMul Real Real Real qz0 qz77 qz318) Bool.false 28205623533765807 9007199254740992 500000000288639 64142000000000000000 (Enclosure.clog_re_eq 9000 91186 4000 8395886596 16000000 rfl rfl rfl) (ep193 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz76)) qz322 Bool.false 828900410688931 562949953421312 1000000000032071 64142000000000000000 (Enclosure.clog_im_eq 9000 91186 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz322 (@HSub.hSub Real Real Real qz53 qz78 qz321) Bool.false 828900410688931 562949953421312 1000000000032071 64142000000000000000 (BSN.arctan_recip 91186 9000 rfl rfl) ep195))))

noncomputable def ep197 := @Enclosure.Real.IsNear.mulLit_ff qz73 qz74 91186 4000 0 1 828900410688931 562949953421312 1000000000032071 64142000000000000000

noncomputable def ep198 := @Enclosure.Complex.IsNear.im_isNear qz69 Bool.false 7000 4000 0 1 Bool.false 91186 4000 0 1

noncomputable def ep199 := @Enclosure.Complex.IsNear.im_isNear qz70 Bool.false 28205623533765807 9007199254740992 500000000288639 64142000000000000000 Bool.false 828900410688931 562949953421312 1000000000032071 64142000000000000000 (ep191 (@congrArg Complex Complex qz63 qz76 Complex.log (BSN.w_shift_mk qz24 Bool.false 45593 1000 2 qz25 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz76) Bool.false 28205623533765807 9007199254740992 500000000288639 64142000000000000000 Bool.false 828900410688931 562949953421312 1000000000032071 64142000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz76)) (@HMul.hMul Real Real Real qz0 qz77 qz318) Bool.false 28205623533765807 9007199254740992 500000000288639 64142000000000000000 (Enclosure.clog_re_eq 9000 91186 4000 8395886596 16000000 rfl rfl rfl) (ep193 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz76)) qz322 Bool.false 828900410688931 562949953421312 1000000000032071 64142000000000000000 (Enclosure.clog_im_eq 9000 91186 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz322 (@HSub.hSub Real Real Real qz53 qz78 qz321) Bool.false 828900410688931 562949953421312 1000000000032071 64142000000000000000 (BSN.arctan_recip 91186 9000 rfl rfl) ep195))))

noncomputable abbrev qz323 := (Enclosure.Real.IsNear.const Bool.false 91186 4000)

noncomputable abbrev qz80 := (@ep190 1 (BSN.w_sub_half_mk qz266 Bool.false 45593 1000 2 qz267 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz316 Bool.false 7000 4000 0 1 Bool.false 91186 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz323))

noncomputable def ep200 := @ep186 45593000001462213103 128284000000000000000000 ep187 126488305106116643207 4503599627370496000 47343000002472449603 128284000000000000000000 (@ep188 197439364736360649 36028797018963968 3500000002020473 256568000000000000000 (ep189 qz80) ep196 rfl) (@ep197 37792056424540431083 1125899906842624000 45593000001462213103 128284000000000000000000 (ep198 qz80) ep199 rfl) rfl

noncomputable def ep201 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz71 qz74) (@HMul.hMul Real Real Real qz0 qz73 qz72) 5802302874822517 2251799813685248 7000000000224497 256568000000000000000 1285978993774984438551 18014398509481984000

noncomputable def ep202 := nat_lit 3000292254845418437366617936544923648

noncomputable def ep203 := @Enclosure.Real.IsNear.mulLit_ff qz71 qz74 7000 4000 0 1 828900410688931 562949953421312 1000000000032071 64142000000000000000

noncomputable def ep204 := @Enclosure.Real.IsNear.mulLit_ff qz73 qz72 91186 4000 0 1 28205623533765807 9007199254740992 500000000288639 64142000000000000000

noncomputable def ep205 := @ep201 22796500013159917927 128284000000000000000000 ep202 1332397416773564574551 18014398509481984000 26296500013272166427 128284000000000000000000 (@ep203 5802302874822517 2251799813685248 7000000000224497 256568000000000000000 (ep189 qz80) ep199 rfl) (@ep204 1285978993774984438551 18014398509481984000 22796500013159917927 128284000000000000000000 (ep198 qz80) ep196 rfl) rfl

noncomputable def ep206 := @Enclosure.Complex.IsNear.of_eq qz63 qz76 Bool.false 9000 4000 0 1 Bool.false 91186 4000 0 1 (BSN.w_shift_mk qz24 Bool.false 45593 1000 2 qz25 rfl)

noncomputable abbrev qz324 := (ep206 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 91186 4000) Bool.false 9000 4000 0 1 Bool.false 91186 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 91186 4000)))

noncomputable abbrev qz81 := qz324

noncomputable def ep207 := ep184 (@ep185 128284000000000000000000 (ep200 rfl) (ep205 rfl)) qz81 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz82 := qz309

noncomputable def ep208 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz82) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz82) (Complex.im ↑qz3)) 60223 65536 1 65536 0 1 0 1 60223 60223

noncomputable def ep209 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz82) (Complex.re ↑qz3) 1 2 0 1 60223 32768 1 32768 60223 65536 1 65536

noncomputable abbrev qz83 := (@Enclosure.Complex.IsNear.of_eq qz309 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz264) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz264 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz319 qz277))

noncomputable def ep210 := ep209 (@Enclosure.Complex.IsNear.re_isNear qz82 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz83) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 60223 32768 1 32768 (Complex.ofReal_re qz3) EMRow09.d4)

noncomputable def ep211 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz82) (Complex.im ↑qz3) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep212 := ep211 (@Enclosure.Complex.IsNear.im_isNear qz82 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz83) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz20 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz20 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz31)

noncomputable def ep213 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz82) (Complex.im ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz82) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep214 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz82) (Complex.im ↑qz3) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep215 := ep214 (@Enclosure.Complex.IsNear.re_isNear qz82 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz83) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz20 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz20 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz31)

noncomputable def ep216 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz82) (Complex.re ↑qz3) 0 1 0 1 60223 32768 1 32768 0 1 0 1

noncomputable def ep217 := ep216 (@Enclosure.Complex.IsNear.im_isNear qz82 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz83) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 60223 32768 1 32768 (Complex.ofReal_re qz3) EMRow09.d4)

noncomputable def ep218 := @ep181 26296500013272166427 128284000000000000000000 (ep207 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz82 (↑qz3) Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 (@ep208 65536 1 65536 (ep210 rfl) (ep212 rfl) rfl rfl) (@ep213 1 0 1 (ep215 rfl) (ep217 rfl) rfl rfl))

noncomputable abbrev qz84 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz325 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz85 := (@HMul.hMul Complex Complex Complex qz302 (@HMul.hMul Complex Complex Complex qz302 (2 : Complex) qz325) (@HSub.hSub Complex Complex Complex qz303 (@HMul.hMul Complex Complex Complex qz302 (2 : Complex) qz325) (1 : Complex)))

noncomputable abbrev qz326 := (@HPow.hPow Complex Int Complex qz422 qz418 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz86 := qz326

noncomputable def ep219 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz54 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz63 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz54 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz63 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) qz86)) Bool.false 767337 2147483648 3 2147483648

noncomputable def ep220 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz54 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz63 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) qz86) Bool.false 0 1 0 1 Bool.false

noncomputable def ep221 := @ep220 0 1 0 1 Bool.false 767337 2147483648 3 2147483648 Bool.true 11661731947 3221225472000 45593 3221225472000 Bool.false 767337 767337 2147483648 3 2147483648 Bool.true 11661731947 11661731947 3221225472000 45593

noncomputable def ep222 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz54 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz63 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false

noncomputable def ep223 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) qz86 Bool.false 767337 2147483648 3 2147483648 Bool.true 11661731947 3221225472000 45593 3221225472000

noncomputable abbrev qz87 := (Complex.re qz326)

noncomputable abbrev qz88 := (Complex.im qz326)

noncomputable def ep224 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz87) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz88) 767337 2147483648 3 2147483648 0 1 0

noncomputable def ep225 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz87 1 12 0 1 2302011 536870912 9 536870912 767337

noncomputable def ep226 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz20) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz327 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz20 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz31)

noncomputable def ep227 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep226 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz327)

noncomputable def ep228 := @Enclosure.Complex.IsNear.re_isNear qz86 Bool.false 2302011 536870912 9 536870912 Bool.true 11661731947 268435456000 45593 268435456000

noncomputable abbrev qz423 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz328 := (@HPow.hPow Complex Nat Complex qz423 qz418 1)

noncomputable abbrev qz89 := (@Inv.inv Complex Complex.instInv qz328)

noncomputable def ep229 := @Enclosure.Complex.IsNear.of_eq qz86 qz89 Bool.false 2302011 536870912 9 536870912 Bool.true 11661731947 268435456000 45593

noncomputable def ep230 := @Enclosure.Complex.IsNear.of_parts qz89 Bool.false 2302011 536870912 9 536870912 Bool.true 11661731947 268435456000 45593

noncomputable abbrev qz90 := (Complex.re qz328)

noncomputable abbrev qz91 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz92 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz93 := qz328

noncomputable def ep231 := @Enclosure.Real.IsNear.mulLit_ff qz90 (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz93)) 9000 4000 0 1 255779 134217728 1 134217728

noncomputable def ep232 := @Enclosure.Complex.IsNear.re_isNear qz93 Bool.false 9000 4000 0 1 Bool.false 91186 4000 0 1

noncomputable def ep233 := @Enclosure.Complex.IsNear.of_eq qz93 qz63 Bool.false 9000 4000 0 1 Bool.false 91186 4000 0

noncomputable def ep234 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz93)) Bool.false 255779 134217728 1 134217728 255779 134217728 1

noncomputable abbrev qz94 := (@instHAdd Real Real.instAdd)

noncomputable abbrev qz95 := (Complex.im qz328)

noncomputable def ep235 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz93) (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 qz90 qz90) (@HMul.hMul Real Real Real qz0 qz95 qz95)) Bool.false 2098971649 4000000 0 1

noncomputable def ep236 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz90 qz90) (@HMul.hMul Real Real Real qz0 qz95 qz95) 81 16 0 1 2078721649 4000000

noncomputable def ep237 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz90 9000 4000 0 1 9000 4000 0 1

noncomputable def ep238 := @Enclosure.Real.IsNear.mulLit_ff qz95 qz95 91186 4000 0 1 91186 4000 0 1

noncomputable def ep239 := @Enclosure.Complex.IsNear.im_isNear qz93 Bool.false 9000 4000 0 1 Bool.false 91186 4000 0 1

noncomputable abbrev qz96 := (ep232 (@ep233 1 (BSN.pow_one_c qz304) qz324))

noncomputable abbrev qz97 := (ep239 (@ep233 1 (BSN.pow_one_c qz304) qz324))

noncomputable def ep240 := @ep236 0 1 33583546384 2098971649 4000000 0 1 (@ep237 81 16 0 1 qz96 qz96 rfl) (@ep238 2078721649 4000000 0 1 qz97 qz97 rfl)

noncomputable def ep241 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz93) 2098971649 4000000 0 1 127889 127890 67108864 (ep235 (Enclosure.Complex.normSq_eq_mul_add_mul qz93) (ep240 rfl rfl)) rfl

noncomputable def ep242 := @Enclosure.Real.IsNear.of_eq (Complex.re qz89) (@HMul.hMul Real Real Real qz0 qz90 (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz93))) Bool.false 2302011 536870912 9 536870912 (Enclosure.Complex.inv_re_eq_mul qz93) (@ep231 2302011 536870912 9 536870912 qz96 (@ep234 134217728 (ep241 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep243 := @Enclosure.Real.IsNear.of_eq (Complex.im qz89) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz95) (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz93))) Bool.true 11661731947 268435456000 45593 268435456000 (Enclosure.Complex.inv_im_eq_mul qz93)

noncomputable def ep244 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz95) (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz93)) 91186 4000 0 1 255779 134217728 1

noncomputable def ep245 := @ep244 134217728 11661731947 268435456000 45593 268435456000 (@Enclosure.Real.IsNear.neg qz95 Bool.false 91186 4000 0 1 qz97) (@ep234 134217728 (ep241 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep246 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz88 0 1 0 1 11661731947 268435456000 45593 268435456000 0

noncomputable def ep247 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep226 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz327)

noncomputable def ep248 := @Enclosure.Complex.IsNear.im_isNear qz86 Bool.false 2302011 536870912 9 536870912 Bool.true 11661731947 268435456000 45593 268435456000

noncomputable abbrev qz98 := (@ep229 268435456000 (BSN.zpow_one_sub_two_mul qz304 1 1 rfl rfl) (@ep230 268435456000 ep242 (ep243 ep245)))

noncomputable def ep249 := @ep224 1 767337 767337 2147483648 3 2147483648 (@ep225 2147483648 3 2147483648 ep227 (ep228 qz98) rfl) (@ep246 1 0 1 ep247 (ep248 qz98) rfl) rfl

noncomputable def ep250 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz88) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz87) 11661731947 3221225472000 45593 3221225472000 0 1 0

noncomputable def ep251 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz88 1 12 0 1 11661731947 268435456000 45593 268435456000 11661731947

noncomputable def ep252 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz87 0 1 0 1 2302011 536870912 9 536870912 0

noncomputable def ep253 := @ep250 1 11661731947 11661731947 3221225472000 45593 3221225472000 (@ep251 3221225472000 45593 3221225472000 ep227 (ep248 qz98) rfl) (@ep252 1 0 1 ep247 (ep228 qz98) rfl) rfl

noncomputable abbrev qz99 := (@Enclosure.Complex.IsNear.mk qz264 qz264 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz277 qz277)

noncomputable def ep254 := @ep221 3221225472000 (@ep222 0 1 0 1 (BSN.stirling_sum_base qz63) qz99) (ep223 (ep249 rfl) (ep253 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep255 := @ep178 2765000892060666659333 54043195528445952000 646307407528782963281827 ep171 (ep218 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep219 Bool.true 11661731947 3221225472000 45593 3221225472000 (BSN.stirling_sum_succ qz63 0 1 rfl) (ep254 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep256 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz24 2) Bool.false 28168996052665519 4503599627370496 500000000288639 32071000000000000000 Bool.false 865776999892387 281474976710656

noncomputable abbrev qz100 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz259 qz305 qz325))

noncomputable def ep257 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz24 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz24 1) qz100) Bool.false 28168996052665519 4503599627370496 500000000288639 32071000000000000000 Bool.false 865776999892387 281474976710656 1000000000032071 32071000000000000000

noncomputable def ep258 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz24 1) qz100 Bool.false 28162502062113967 9007199254740992 500000000288639 64142000000000000000 Bool.false 878107850999203 562949953421312 1000000000032071 64142000000000000000 Bool.false

noncomputable def ep259 := nat_lit 507447520504741616342759108509696

noncomputable def ep260 := nat_lit 974778243525325012172944703488

noncomputable abbrev qz101 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz259 qz305 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep261 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz24 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz24 0) qz101) Bool.false 28162502062113967 9007199254740992 500000000288639 64142000000000000000 Bool.false 878107850999203 562949953421312 1000000000032071 64142000000000000000

noncomputable def ep262 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz24 0) qz101 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz329 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz75))

noncomputable def ep263 := @Enclosure.Complex.IsNear.of_eq qz101 qz329 Bool.false 28162502062113967 9007199254740992 500000000288639 64142000000000000000 Bool.false 878107850999203 562949953421312 1000000000032071 64142000000000000000

noncomputable def ep264 := BSN.log_dyadic_bound 123886596 16507886596 1 0 1 131072 64142 0 1 1967 16631773192 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 123886596) (BSN.artanhQ 16507886596) 0 0 rfl) rfl rfl rfl

noncomputable def ep265 := @Enclosure.Real.IsNear.mulLit_ff qz77 (Real.log (Enclosure.sfrac Bool.false 8315886596 16000000)) 1 2 0 1 28162502062113967 4503599627370496 500000000288639 32071000000000000000 28162502062113967 9007199254740992 500000000288639 64142000000000000000 qz319 (BSN.isNear_log_sfrac 8315886596 16000000 28162502062113967 4503599627370496 500000000288639 32071000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8315886596) qz320)) Bool.false 29530523762283215060992 4722366482869645213696 1000000000577278 64142000000000000000 28162502062113967 4503599627370496 500000000288639 32071000000000000000 (BSN.log_rat_reduce_isNear 8315886596 16000000 9 16631773192 16384000000 1967 131072 24973259072661432 36028797018963968 64142 1000000000000000 rfl rfl rfl rfl (ep264 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep266 := BSN.arctan_dyadic_bound_f 1000 91186 1 0 131072 64142 0 1 1 0 1 1 1437 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 91186) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 91186) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz330 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz331 := (@Nat.cast Real Real.instNatCast 91186)

noncomputable def ep267 := @Enclosure.Real.IsNear.subLit_ff_p qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz331)) 884279719003555 562949953421312 1 2000000000000000 1437 131072 1 64142 115095352246167535616 878107850999203 562949953421312 1000000000032071 64142000000000000000 qz79 (ep266 rfl) rfl rfl

noncomputable abbrev qz102 := (@HAdd.hAdd Complex Complex Complex qz259 qz305 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz332 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz75)

noncomputable def ep268 := @ep262 28162502062113967 9007199254740992 500000000288639 64142000000000000000 Bool.false 878107850999203 562949953421312 1000000000032071 64142000000000000000 Bool.false 28162502062113967 28162502062113967 9007199254740992 500000000288639 64142000000000000000 Bool.false 878107850999203 878107850999203 562949953421312 1000000000032071 64142000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz24 0) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz24) qz99) (ep263 (@congrArg Complex Complex qz102 qz332 Complex.log (BSN.w_shift_mk qz24 Bool.false 45593 1000 0 qz25 rfl)) (@Enclosure.Complex.IsNear.of_parts qz329 Bool.false 28162502062113967 9007199254740992 500000000288639 64142000000000000000 Bool.false 878107850999203 562949953421312 1000000000032071 64142000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz329) (@HMul.hMul Real Real Real qz0 qz77 (Real.log (Enclosure.sfrac Bool.false 8315886596 16000000))) Bool.false 28162502062113967 9007199254740992 500000000288639 64142000000000000000 (Enclosure.clog_re_eq 1000 91186 4000 8315886596 16000000 rfl rfl rfl) (ep265 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz329) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz331 qz330)) Bool.false 878107850999203 562949953421312 1000000000032071 64142000000000000000 (Enclosure.clog_im_eq 1000 91186 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz331 qz330)) (@HSub.hSub Real Real Real qz53 qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz331))) Bool.false 878107850999203 562949953421312 1000000000032071 64142000000000000000 (BSN.arctan_recip 91186 1000 rfl rfl) ep267)))) rfl rfl

noncomputable abbrev qz333 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz75))

noncomputable def ep269 := @Enclosure.Complex.IsNear.of_eq qz100 qz333 Bool.false 28175490043217071 9007199254740992 500000000288639 64142000000000000000 Bool.false 853446148785571 562949953421312 1000000000032071 64142000000000000000

noncomputable def ep270 := BSN.log_dyadic_bound 147886596 16531886596 1 0 1 131072 64142 0 1 2345 16679773192 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 147886596) (BSN.artanhQ 16531886596) 0 0 rfl) rfl rfl rfl

noncomputable def ep271 := @Enclosure.Real.IsNear.mulLit_ff qz77 (Real.log (Enclosure.sfrac Bool.false 8339886596 16000000)) 1 2 0 1 28175490043217071 4503599627370496 500000000288639 32071000000000000000 28175490043217071 9007199254740992 500000000288639 64142000000000000000 qz319 (BSN.isNear_log_sfrac 8339886596 16000000 28175490043217071 4503599627370496 500000000288639 32071000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8339886596) qz320)) Bool.false 29544142647556383440896 4722366482869645213696 1000000000577278 64142000000000000000 28175490043217071 4503599627370496 500000000288639 32071000000000000000 (BSN.log_rat_reduce_isNear 8339886596 16000000 9 16679773192 16384000000 2345 131072 24973259072661432 36028797018963968 64142 1000000000000000 rfl rfl rfl rfl (ep270 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep272 := BSN.arctan_dyadic_bound_f 5000 91186 1 0 131072 64142 0 1 1 0 1 1 7179 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 91186) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 91186) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz334 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep273 := @Enclosure.Real.IsNear.subLit_ff_p qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz334 qz331)) 884279719003555 562949953421312 1 2000000000000000 7179 131072 1 64142 111862893613622362112 853446148785571 562949953421312 1000000000032071 64142000000000000000 qz79 (ep272 rfl) rfl rfl

noncomputable abbrev qz103 := (@HAdd.hAdd Complex Complex Complex qz259 qz305 qz325)

noncomputable abbrev qz335 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz75)

noncomputable def ep274 := @ep258 28175490043217071 9007199254740992 500000000288639 64142000000000000000 Bool.false 853446148785571 562949953421312 1000000000032071 64142000000000000000 Bool.false ep259 28168996052665519 4503599627370496 500000000288639 32071000000000000000 Bool.false ep260 865776999892387 281474976710656 1000000000032071 32071000000000000000 (ep261 (BSN.log_sum_c_succ qz24 0 1 rfl) (ep268 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep269 (@congrArg Complex Complex qz103 qz335 Complex.log (BSN.w_shift_mk qz24 Bool.false 45593 1000 1 qz25 rfl)) (@Enclosure.Complex.IsNear.of_parts qz333 Bool.false 28175490043217071 9007199254740992 500000000288639 64142000000000000000 Bool.false 853446148785571 562949953421312 1000000000032071 64142000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz333) (@HMul.hMul Real Real Real qz0 qz77 (Real.log (Enclosure.sfrac Bool.false 8339886596 16000000))) Bool.false 28175490043217071 9007199254740992 500000000288639 64142000000000000000 (Enclosure.clog_re_eq 5000 91186 4000 8339886596 16000000 rfl rfl rfl) (ep271 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz333) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz331 qz334)) Bool.false 853446148785571 562949953421312 1000000000032071 64142000000000000000 (Enclosure.clog_im_eq 5000 91186 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz331 qz334)) (@HSub.hSub Real Real Real qz53 qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz334 qz331))) Bool.false 853446148785571 562949953421312 1000000000032071 64142000000000000000 (BSN.arctan_recip 91186 5000 rfl rfl) ep273)))) rfl rfl

noncomputable def ep275 := @ep170 ep171 Bool.false 28168996052665519 4503599627370496 500000000288639 32071000000000000000 Bool.false 865776999892387 281474976710656 1000000000032071 32071000000000000000 Bool.true ep172 160650298050569426207 4503599627370496000 105063706030896125053069 ep168 Bool.false ep173 2598771708081328355333 54043195528445952000 57277800579379666989679 ep164 (@ep174 4503599627370496000 100967706028531594365069 ep168 Bool.false 2765000892060666659333 54043195528445952000 646307407528782963281827 ep171 (BSN.logGammaStirling_unfold 1 qz63) (ep255 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep256 1000000000032071 32071000000000000000 (BSN.log_sum_c_eq qz24 2) (ep257 (BSN.log_sum_c_succ qz24 1 2 rfl) (ep274 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz104 := (@HDiv.hDiv Real Real Real qz256 qz266 (2 : Real))

noncomputable def ep276 := @Enclosure.Real.IsNear.mulLit_ff qz104 (Real.log Real.pi) 45593 2000 0 1 75021 65536 1 32768 3420432453 131072000 45593 65536000 (@Enclosure.Real.IsNear.of_eq qz104 (Enclosure.sfrac Bool.false 45593 2000) Bool.false 45593 2000 0 1 (BSN.t_half_eq qz24 Bool.false 45593 1000 qz25) (Enclosure.Real.IsNear.const Bool.false 45593 2000)) EMRow09.d5 rfl

noncomputable def ep277 := @ep166 45593 65536000 ep167 237693947559074174977 10808639105689190400 225994697079379666989679 ep164 (@ep169 57277800579379666989679 ep164 (ep275 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep276 rfl rfl

noncomputable def ep278 := nat_lit 497284049261305279478661945134151539676167164562272288713375726551695360

noncomputable def ep279 := nat_lit 999032748162700272532440617973666461683616587070757448135651713089536

noncomputable def ep280 := nat_lit 1300793123615917074383824000065106191547235766045931910761859657242771456

noncomputable def ep281 := BSN.sin_dyadic_bound_f 421645496 268435456 3 2 131072 64205 ep278 ep69 ep279 ep280 ep72 ep279 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 421645496) qz274 0 2 ep278 ep69 ep279 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 421645496) qz275 0 2 ep280 ep72 ep279 rfl rfl rfl rfl) rfl rfl

noncomputable def ep282 := @ep163 131072 Bool.true 131071 131072 1 32071 (@ep165 1441209 65536 123 131072 ep277 rfl) (Enclosure.sfrac_false_div 1441209 65536) (BSN.cos_reduce1 qz306 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14835332039770854391808) qz284) 226375608064910080 72057594037927936 Bool.false 131071 131072 3 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q1 1441209 65536 226375608064910080 72057594037927936 3 14835332039770854391808 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131071 131072 14835332039770854391808 9444732965739290427392 421645496 268435456 64205 64142 (ep281 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep283 := nat_lit 78934100207298343813987591

noncomputable def ep284 := nat_lit 13745551436096808715026432000

noncomputable abbrev qz105 := qz260

noncomputable abbrev qz106 := qz261

noncomputable abbrev qz424 := (@Nat.cast Complex Complex.instNatCast 10)

noncomputable abbrev qz336 := (@HPow.hPow Complex Complex Complex qz411 qz424 qz412)

noncomputable abbrev qz107 := qz336

noncomputable abbrev qz337 := qz424

noncomputable abbrev qz108 := (@HAdd.hAdd Complex Complex Complex qz259 (@HDiv.hDiv Complex Complex Complex qz310 qz337 (@HSub.hSub Complex Complex Complex qz303 qz258 (1 : Complex))) qz309)

noncomputable abbrev qz109 := (@instHSub Nat instSubNat)

noncomputable abbrev qz338 := qz423

noncomputable abbrev qz110 := qz338

noncomputable abbrev qz111 := qz337

noncomputable def ep285 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz21 1 10) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 10, @HPow.hPow Complex Complex Complex qz105 (@Nat.cast Complex Complex.instNatCast n) qz106) (@HMul.hMul Complex Complex Complex qz52 qz107 (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) Bool.false ep159 428597531604777172992000 ep160

noncomputable def ep286 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 10, @HPow.hPow Complex Complex Complex qz105 (@Nat.cast Complex Complex.instNatCast n) qz106) (@HMul.hMul Complex Complex Complex qz52 qz107 (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) Bool.false 32905693041 8589934592 116013616171 21191368638464

noncomputable def ep287 := nat_lit 2113831302684475746025079

noncomputable def ep288 := nat_lit 4252938957104405735179591

noncomputable def ep289 := nat_lit 13771229576573761284324445174890496

noncomputable def ep290 := nat_lit 85911680313513956181136113664

noncomputable def ep291 := @ep286 Bool.true 38804439 268435456 115135142141 21191368638464 Bool.true 38657947041016595828587 428597531604777172992000 ep287 ep161 Bool.false 10006140103456293655481 71432921934129528832000 ep288 ep284 Bool.false ep289 ep159 428597531604777172992000 ep160 ep161 Bool.true ep290 320045949196494952519 71432921934129528832000

noncomputable def ep292 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 10, @HPow.hPow Complex Complex Complex qz105 (@Nat.cast Complex Complex.instNatCast n) qz106) (BSN.headSumC qz21 10) Bool.false 32905693041 8589934592 116013616171 21191368638464 Bool.true 38804439 268435456 115135142141

noncomputable abbrev qz112 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 9) qz261)

noncomputable def ep293 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz21 10) (@HAdd.hAdd Complex Complex Complex qz5 qz4 qz112) Bool.false 32905693041 8589934592 116013616171 21191368638464 Bool.true 38804439 268435456 115135142141 21191368638464

noncomputable def ep294 := @Enclosure.Complex.IsNear.addLitP qz4 qz112 Bool.false 60437698919 17179869184 2744649687435 550975584600064 Bool.true 557857645 2147483648 1362150463287 275487792300032 Bool.false

noncomputable abbrev qz339 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz113 := (@Inv.inv Real Real.instInv (Real.sqrt qz339))

noncomputable abbrev qz114 := (@HMul.hMul Real Real Real qz253 qz266 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep295 := @Enclosure.Complex.IsNear.of_eq qz112 (Complex.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz114)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz114)))) Bool.false 5373687163 17179869184 271704333011 550975584600064 Bool.false 247422133 2147483648 67303192273 137743896150016 (BSN.cpow_neg_s_mk qz24 45593 1000 9 qz25 rfl)

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9) qz26)

noncomputable def ep296 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz339) 393217 131072 1 131072 21845 21846 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz339) (Real.sqrt qz340) Bool.false 393217 131072 1 131072 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz340) Bool.false 393217 131072 1 131072 393217 131072 1 131072 (BSN.sqrt_enclosure 9 1 196608 196609 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep297 := BSN.log_dyadic_bound 1 17 2 1 867 65536 32071 1 1 7719 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz115 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep298 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz115 45593 1000 0 1 9895417793173221 4503599627370496 1000000000096213 32071000000000000000 451161783444146665053 4503599627370496000 45593000004386639309 32071000000000000000000 qz29 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000096213 32071000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 5188048803947201691648 2361183241434822606848 1000000000096213 32071000000000000000 9895417793173221 4503599627370496 1000000000096213 32071000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 7719 65536 24973259072661432 36028797018963968 32071 1000000000000000 rfl rfl rfl rfl (ep297 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep299 := nat_lit 179482349139087305015644748618341571093773575789797975518370499394273185

noncomputable def ep300 := nat_lit 130475579133053774917415337471771645994939053142504459568726330310561

noncomputable def ep301 := nat_lit 469861572998060854643489002501654579723510416220573500089763846259736481

noncomputable def ep302 := BSN.sin_dyadic_bound_f 326919747 268435456 3 2 131072 64205 ep299 ep69 ep300 ep301 ep72 ep300 122993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 326919747) qz274 0 2 ep299 ep69 ep300 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 326919747) qz275 0 2 ep301 ep72 ep300 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1641317) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep303 := @Enclosure.Real.IsNear.cos_image qz114 qz341 Bool.false 1641317 16384 187 131072 Bool.false 122993 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz114 Bool.false 451161783444146665053 4503599627370496000 45593000004386639309 32071000000000000000000 1641317 16384 187 131072 (ep298 rfl) rfl) (Enclosure.sfrac_false_div 1641317 16384) (BSN.cos_reduce3 qz341 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2875616507363866968064) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 122993 131072 15 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q3 1641317 16384 226375608064910080 72057594037927936 15 2875616507363866968064 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 122993 131072 2875616507363866968064 2361183241434822606848 326919747 268435456 64205 64142 (ep302 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep304 := nat_lit 99770405334663193353099267160177215783649737240173321714458600254734241

noncomputable def ep305 := nat_lit 299050264845723472509462970805588104058959333614234956224238348103581601

noncomputable def ep306 := BSN.cos_dyadic_bound_f 326919747 268435456 3 2 131072 64205 ep304 ep76 ep300 ep305 ep78 ep300 45304 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 326919747) qz268 0 2 ep304 ep76 ep300 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 326919747) qz269 0 2 ep305 ep78 ep300 rfl rfl rfl rfl) rfl rfl

noncomputable def ep307 := @Enclosure.Real.IsNear.sin_image qz114 qz341 Bool.false 1641317 16384 187 131072 Bool.true 45304 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz114 Bool.false 451161783444146665053 4503599627370496000 45593000004386639309 32071000000000000000000 1641317 16384 187 131072 (ep298 rfl) rfl) (Enclosure.sfrac_false_div 1641317 16384) (BSN.sin_reduce3 qz341 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2875616507363866968064) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 45304 131072 15 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q3 1641317 16384 226375608064910080 72057594037927936 15 2875616507363866968064 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 45304 131072 2875616507363866968064 2361183241434822606848 326919747 268435456 64205 64142 (ep306 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz342 := (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 43691 131072 1 131072 43691 131072 1 131072 (ep296 rfl rfl) rfl)

noncomputable def ep308 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz114)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz114))) Bool.false 5373687163 17179869184 271704333011 550975584600064 Bool.false 247422133 2147483648 67303192273 137743896150016 (@Enclosure.Real.IsNear.mulLit_ff qz113 (Real.cos qz114) 43691 131072 1 131072 122993 131072 6128349 4203610112 5373687163 17179869184 271704333011 550975584600064 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz114) Bool.false 122993 131072 6128349 4203610112 122993 131072 6128349 4203610112 (ep303 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz113 (@Neg.neg Real Real.instNeg (Real.sin qz114)) 43691 131072 1 131072 5663 16384 6128349 4203610112 247422133 2147483648 67303192273 137743896150016 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz114) Bool.true 5663 16384 6128349 4203610112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz114) Bool.true 45304 131072 6128349 4203610112 5663 16384 6128349 4203610112 (ep307 rfl rfl) rfl)) rfl)

noncomputable def ep309 := @ep294 5373687163 17179869184 271704333011 550975584600064 Bool.false 247422133 2147483648 67303192273 137743896150016 Bool.false 1130631003706478297088 32905693041 8589934592 116013616171 21191368638464 Bool.true 666655185778507776 38804439 268435456 115135142141 21191368638464 EMRow09.d6 (ep295 ep308) rfl rfl

noncomputable def ep310 := @Enclosure.Complex.IsNear.mul qz107 (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))) Bool.true 38657947041016595828587 428597531604777172992000 ep287 ep161 Bool.false

noncomputable abbrev qz116 := (Complex.re qz336)

noncomputable abbrev qz117 := (Complex.im qz336)

noncomputable def ep311 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz116 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz117 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) 17630502614391378179 428597531604777172992 491293607251268731579

noncomputable def ep312 := nat_lit 2114700220937970571542528

noncomputable def ep313 := nat_lit 16568700678687912627297755713665305677922304

noncomputable def ep314 := @Enclosure.Real.IsNear.mulLit_tf qz116 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 352109255 4294967296 127554919315 275487792300032 250355569529

noncomputable abbrev qz118 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

noncomputable abbrev qz343 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz415 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz119 := (Real.cos qz343)

noncomputable abbrev qz120 := (@Neg.neg Real Real.instNeg (Real.sin qz343))

noncomputable def ep315 := @Enclosure.Complex.IsNear.of_eq qz107 (Complex.mk (@HMul.hMul Real Real Real qz0 qz118 qz119) (@HMul.hMul Real Real Real qz0 qz118 qz120)) Bool.true 352109255 4294967296 127554919315 275487792300032 Bool.false 2623514455 8589934592 64519983485 137743896150016 (BSN.cpow_neg_s_mk qz24 45593 1000 10 qz25 rfl)

noncomputable abbrev qz121 := (@HDiv.hDiv Real Real Real qz256 (@Nat.cast Real Real.instNatCast 10) (@Nat.cast Real Real.instNatCast 1))

noncomputable def ep316 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) 414487 131072 1 131072 20724 20725 65536 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) (Real.sqrt qz121) Bool.false 414487 131072 1 131072 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz121) Bool.false 414487 131072 1 131072 414487 131072 1 131072 (BSN.sqrt_enclosure 10 1 207243 207244 65536 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep317 := BSN.log_dyadic_bound 2 18 3 2 1574640 65536 32071 6528 48 14623 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz344 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz122 := qz344

noncomputable def ep318 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz122 45593 1000 0 1 10369857060558565 4503599627370496 1000000000096213 32071000000000000000 94558578592409330809 900719925474099200 45593000004386639309 32071000000000000000000 qz29 (BSN.isNear_log_sfrac 10 1 10369857060558565 4503599627370496 1000000000096213 32071000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz121) Bool.false 5436791618566128926720 2361183241434822606848 1000000000096213 32071000000000000000 10369857060558565 4503599627370496 1000000000096213 32071000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 14623 65536 24973259072661432 36028797018963968 32071 1000000000000000 rfl rfl rfl rfl (ep317 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep319 := nat_lit 133030004146520952154789144536361104571241070083802008395264868290437376

noncomputable def ep320 := nat_lit 231764568825553612794967898511977390009906423401733711057205839831296

noncomputable def ep321 := nat_lit 398626483301911749238777497812059358933703397404602557763680193191649536

noncomputable def ep322 := BSN.cos_dyadic_bound_f 351261766 268435456 3 2 131072 64205 ep319 ep76 ep320 ep321 ep78 ep320 33980 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 351261766) qz268 0 2 ep319 ep76 ep320 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 351261766) qz269 0 2 ep321 ep78 ep320 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz123 := qz343

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3440021) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep323 := @Enclosure.Real.IsNear.cos_image qz123 qz345 Bool.false 3440021 32768 187 131072 Bool.true 33980 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 94558578592409330809 900719925474099200 45593000004386639309 32071000000000000000000 3440021 32768 187 131072 (ep318 rfl) rfl) (Enclosure.sfrac_false_div 3440021 32768) (BSN.cos_reduce2 qz345 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6179462345209541558272) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 33980 131072 16 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q2 3440021 32768 226375608064910080 72057594037927936 16 6179462345209541558272 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33980 131072 6179462345209541558272 4722366482869645213696 351261766 268435456 64205 64142 (ep322 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep324 := nat_lit 239268595808677270988384485846640406316226001012122228142630998250922240

noncomputable def ep325 := nat_lit 626280608292246718167910372048372148387242535108145885793750471678402816

noncomputable def ep326 := BSN.sin_dyadic_bound_f 351261766 268435456 3 2 131072 64205 ep324 ep69 ep320 ep325 ep72 ep320 126590 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 351261766) qz274 0 2 ep324 ep69 ep320 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 351261766) qz275 0 2 ep325 ep72 ep320 rfl rfl rfl rfl) rfl rfl

noncomputable def ep327 := @Enclosure.Real.IsNear.sin_image qz123 qz345 Bool.false 3440021 32768 187 131072 Bool.true 126590 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 94558578592409330809 900719925474099200 45593000004386639309 32071000000000000000000 3440021 32768 187 131072 (ep318 rfl) rfl) (Enclosure.sfrac_false_div 3440021 32768) (BSN.sin_reduce2 qz345 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6179462345209541558272) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 126590 131072 16 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q2 3440021 32768 226375608064910080 72057594037927936 16 6179462345209541558272 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 126590 131072 6179462345209541558272 4722366482869645213696 351261766 268435456 64205 64142 (ep326 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz124 := (Real.sin qz343)

noncomputable abbrev qz346 := (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 41449 131072 1 131072 41449 131072 1 131072 (ep316 rfl rfl) rfl)

noncomputable def ep328 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz118 qz119) (@HMul.hMul Real Real Real qz0 qz118 qz120) Bool.true 352109255 4294967296 127554919315 275487792300032 Bool.false 2623514455 8589934592 64519983485 137743896150016 (@Enclosure.Real.IsNear.mulLit_ft qz118 qz119 41449 131072 1 131072 8495 32768 6128349 4203610112 352109255 4294967296 127554919315 275487792300032 qz346 (@Enclosure.Real.IsNear.recentre' qz119 Bool.true 33980 131072 6128349 4203610112 8495 32768 6128349 4203610112 (ep323 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz118 qz120 41449 131072 1 131072 63295 65536 6128349 4203610112 2623514455 8589934592 64519983485 137743896150016 qz346 (@Enclosure.Real.IsNear.neg qz124 Bool.true 63295 65536 6128349 4203610112 (@Enclosure.Real.IsNear.recentre' qz124 Bool.true 126590 131072 6128349 4203610112 63295 65536 6128349 4203610112 (ep327 rfl rfl) rfl)) rfl)

noncomputable def ep329 := @ep314 498953195760 0 1 17630502614391378179 428597531604777172992 491293607251268731579 ep312 (@Enclosure.Complex.IsNear.re_isNear qz107 Bool.true 352109255 4294967296 127554919315 275487792300032 Bool.false 2623514455 8589934592 64519983485 137743896150016 (ep315 ep328))

noncomputable def ep330 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))) Bool.false 250355569529 498953195760 0 1 Bool.false

noncomputable def ep331 := @Enclosure.Complex.IsNear.addLitP qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) Bool.false 2068971649 4157943298 0 1 Bool.true 455930000

noncomputable def ep332 := @ep331 2078971649 0 1 Bool.false 1 240 0 1 Bool.false 45593 120000 0 1 Bool.false 500711139058 250355569529 498953195760 0 1 Bool.false 40074954392857 40074954392857 249476597880000 0 1

noncomputable abbrev qz125 := (@HDiv.hDiv Complex Complex Complex qz310 qz337 (@HSub.hSub Complex Complex Complex qz303 qz258 (1 : Complex)))

noncomputable def ep333 := @Enclosure.Complex.IsNear.addLitP qz125 qz82 Bool.true 20000000 8315886596 0 1 Bool.true 1823720000 8315886596 0 1

noncomputable def ep334 := @Enclosure.Complex.IsNear.of_eq qz125 (Complex.mk (Enclosure.sfrac Bool.true 20000000 8315886596) (Enclosure.sfrac Bool.true 1823720000 8315886596)) Bool.true 20000000 8315886596 0 1 Bool.true 1823720000 8315886596 0 1

noncomputable def ep335 := @ep333 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 8275886596 2068971649 4157943298 0 1 Bool.true 1823720000 455930000 2078971649 0 1 (ep334 (BSN.N_div_s_sub_one_mk qz24 45593 1000 10 qz25 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 20000000 8315886596) (Enclosure.sfrac Bool.true 1823720000 8315886596) Bool.true 20000000 8315886596 0 1 Bool.true 1823720000 8315886596 0 1 (Enclosure.Real.IsNear.const Bool.true 20000000 8315886596) (Enclosure.Real.IsNear.const Bool.true 1823720000 8315886596))) qz83 rfl

noncomputable abbrev qz126 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz347 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz423 qz424 1))

noncomputable abbrev qz127 := qz347

noncomputable def ep336 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz127)) Bool.false 1 240 0 1

noncomputable def ep337 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz127) Bool.false 0 1 0 1 Bool.false

noncomputable def ep338 := @ep337 0 1 0 1 Bool.false 1 240 0 1 Bool.false 45593 120000 0 1 Bool.false 1 1 240 0 1 Bool.false 45593 45593 120000 0

noncomputable def ep339 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false

noncomputable def ep340 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz127 Bool.false 1 240 0 1 Bool.false 45593 120000 0 1

noncomputable abbrev qz128 := (Complex.re qz347)

noncomputable abbrev qz129 := (Complex.im qz347)

noncomputable def ep341 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz128) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129) 1 240 0 1 0 1 0

noncomputable def ep342 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz128 1 24 0 1 1 10 0 1 1

noncomputable def ep343 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep344 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep345 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz20) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow09.d7 rfl) qz327

noncomputable def ep346 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) qz21 Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 (BSN.ascPochhammer_one_eval qz21)

noncomputable def ep347 := ep346 (@Enclosure.Complex.IsNear.of_eq qz21 (Complex.mk qz77 qz24) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 (BSN.s_crit_mk qz24 Bool.false 45593 1000 qz25) (@Enclosure.Complex.IsNear.mk qz77 qz24 Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 qz319 qz29))

noncomputable def ep348 := @ep344 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep345) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep347)

noncomputable def ep349 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 45593 1000 0 1 0 1 0

noncomputable def ep350 := @ep349 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep345) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep347)

noncomputable def ep351 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) 45593 12000 0 1 0 1 0 1 45593

noncomputable def ep352 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 45593 1000 0 1 45593 12000 0

noncomputable def ep353 := @ep352 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep345) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep347)

noncomputable def ep354 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep355 := @ep354 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep345) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep347)

noncomputable def ep356 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 45593 12000 0 1 (@ep343 1 24 0 1 (ep348 rfl) (ep350 rfl) rfl rfl) (@ep351 45593 12000 0 1 (ep353 rfl) (ep355 rfl) rfl rfl)

noncomputable def ep357 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 45593 12000 0 1 ep356

noncomputable abbrev qz130 := (@Enclosure.Complex.IsNear.re_isNear qz347 Bool.false 1 10 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz347 (Complex.mk (Enclosure.sfrac Bool.false 1 10) qz264) Bool.false 1 10 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 10 1 10 EMRow09.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 10) qz264 Bool.false 1 10 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 10) qz277)))

noncomputable def ep358 := @ep342 240 0 1 ep357 qz130

noncomputable def ep359 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129 45593 12000 0 1 0 1 0 1 0

noncomputable def ep360 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 45593 12000 0 1 ep356

noncomputable abbrev qz131 := (@Enclosure.Complex.IsNear.im_isNear qz347 Bool.false 1 10 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz347 (Complex.mk (Enclosure.sfrac Bool.false 1 10) qz264) Bool.false 1 10 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 10 1 10 EMRow09.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 10) qz264 Bool.false 1 10 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 10) qz277)))

noncomputable def ep361 := @ep359 1 0 1 ep360 qz131

noncomputable def ep362 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz128) 0 1 0 1 45593 120000 0

noncomputable def ep363 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129 1 24 0 1 0 1 0 1 0

noncomputable def ep364 := @ep363 1 0 1 ep357 qz131

noncomputable def ep365 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)))) qz128 45593 12000 0 1 1 10 0 1 45593

noncomputable def ep366 := @ep365 120000 0 1 ep360 qz130

noncomputable def ep367 := @ep338 1 (@ep339 0 1 0 1 (BSN.bern_sum_base qz21 10) qz99) (ep340 (@ep341 1 1 1 240 0 1 (ep358 rfl) (ep361 rfl) rfl rfl) (@ep362 1 45593 45593 120000 0 1 (ep364 rfl) (ep366 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep368 := ep332 (ep335 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep336 Bool.false 45593 120000 0 1 (BSN.bern_sum_succ qz21 10 0 1 1 rfl rfl) (ep367 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep369 := @Enclosure.Real.IsNear.mulLit_ff qz117 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 2623514455 8589934592 64519983485 137743896150016 40074954392857

noncomputable def ep370 := @ep369 249476597880000 0 1 21027444426625217649587 428597531604777172992000 517127079117852368393329 ep161 (@Enclosure.Complex.IsNear.im_isNear qz107 Bool.true 352109255 4294967296 127554919315 275487792300032 Bool.false 2623514455 8589934592 64519983485 137743896150016 (ep315 ep328))

noncomputable def ep371 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))) Bool.false 250355569529 498953195760 0 1 Bool.false

noncomputable def ep372 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz116 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz117 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) 2822152467085571118307 214298765802388586496000 1022351514826635889466591

noncomputable def ep373 := nat_lit 25731641695397622908881781415617908715814912

noncomputable def ep374 := @Enclosure.Real.IsNear.mulLit_tf qz116 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 352109255 4294967296 127554919315 275487792300032 40074954392857

noncomputable def ep375 := @ep374 249476597880000 0 1 2822152467085571118307 214298765802388586496000 1022351514826635889466591 ep284 (@Enclosure.Complex.IsNear.re_isNear qz107 Bool.true 352109255 4294967296 127554919315 275487792300032 Bool.false 2623514455 8589934592 64519983485 137743896150016 (ep315 ep328))

noncomputable def ep376 := @Enclosure.Real.IsNear.mulLit_ff qz117 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz108 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 2623514455 8589934592 64519983485 137743896150016 250355569529

noncomputable def ep377 := @ep376 498953195760 0 1 131362291109817808339 857195063209554345984 248506726329059218901 1057350110468985285771264 (@Enclosure.Complex.IsNear.im_isNear qz107 Bool.true 352109255 4294967296 127554919315 275487792300032 Bool.false 2623514455 8589934592 64519983485 137743896150016 (ep315 ep328))

noncomputable abbrev qz348 := (ep368 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep378 := @ep310 10006140103456293655481 71432921934129528832000 ep288 ep284 (@ep311 ep312 21027444426625217649587 428597531604777172992000 517127079117852368393329 ep161 ep313 38657947041016595828587 428597531604777172992000 ep287 ep161 (ep329 (@ep330 40074954392857 249476597880000 0 1 qz348) rfl) (ep370 (@ep371 40074954392857 249476597880000 0 1 qz348) rfl) rfl rfl) (@ep372 ep284 131362291109817808339 857195063209554345984 248506726329059218901 1057350110468985285771264 ep373 10006140103456293655481 71432921934129528832000 ep288 ep284 (ep375 (@ep371 40074954392857 249476597880000 0 1 qz348) rfl) (ep377 (@ep330 40074954392857 249476597880000 0 1 qz348) rfl) rfl rfl)

noncomputable def ep379 := @ep291 ep283 ep284 (@ep292 21191368638464 (BSN.head_sum_c_eq qz21 10) (ep293 (BSN.head_sum_c_succ qz21 9 10 rfl rfl) (ep309 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep378 rfl rfl rfl

noncomputable def ep380 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz21 1 10) Bool.false ep159 428597531604777172992000 ep160 ep161 Bool.true 320045949196494952519 71432921934129528832000 ep283 ep284 (@ep285 ep161 Bool.true 320045949196494952519 71432921934129528832000 ep283 ep284 (BSN.zetaApproximant_eq_folded' qz21 1 10 rfl) (ep379 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep381 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))))) qz57)) (Complex.im (zetaApproximant qz21 1 10)) 5 131072 4075805

noncomputable def ep382 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))))) qz57)) Bool.false 5 131072 4075805

noncomputable def ep383 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))))) qz57) qz306 Bool.false 1441209 65536 123

noncomputable def ep384 := nat_lit 276712930811019688720382165349183596025285587684404941484380137734537216

noncomputable def ep385 := nat_lit 828140726936733665616081614811603455152489529879073309556869109777432576

noncomputable def ep386 := BSN.cos_dyadic_bound_f 421645496 268435456 3 2 131072 64205 ep384 ep76 ep279 ep385 ep78 ep279 5 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 421645496) qz268 0 2 ep384 ep76 ep279 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 421645496) qz269 0 2 ep385 ep78 ep279 rfl rfl rfl rfl) rfl rfl

noncomputable def ep387 := @ep383 131072 Bool.false 5 131072 1 32071 (@ep165 1441209 65536 123 131072 ep277 rfl) (Enclosure.sfrac_false_div 1441209 65536) (BSN.sin_reduce1 qz306 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14835332039770854391808) qz284) 226375608064910080 72057594037927936 Bool.false 5 131072 3 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q1 1441209 65536 226375608064910080 72057594037927936 3 14835332039770854391808 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 5 131072 14835332039770854391808 9444732965739290427392 421645496 268435456 64205 64142 (ep386 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep388 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz21 1 10) Bool.false ep159 428597531604777172992000 ep160 ep161 Bool.true 320045949196494952519 71432921934129528832000 ep283 ep284 (@ep285 ep161 Bool.true 320045949196494952519 71432921934129528832000 ep283 ep284 (BSN.zetaApproximant_eq_folded' qz21 1 10 rfl) (ep379 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow09.d9 : Enclosure.Real.IsNear (hardyZApproximantEM 1 10 qz24) Bool.true ep145 ep146 ep147 ep148 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 10 qz24) ep149 Bool.true ep145 ep146 ep147 ep148 (@Eq.refl Real ep149) (@ep150 Bool.true ep145 ep146 ep147 ep148 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz55 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz56 (@Nat.cast Complex Complex.instNatCast j))))) qz57) (zetaApproximant qz21 1 10)) (@ep152 ep146 ep153 ep148 320045949196494952519 ep154 ep155 ep156 ep157 ep145 ep146 ep147 ep148 (@ep158 4203610112 ep159 428597531604777172992000 ep160 ep161 ep151 ep146 ep153 ep148 (@ep162 4203610112 131071 131072 4075805 4203610112 (ep282 rfl rfl) rfl) ep380 rfl) (@ep381 4203610112 320045949196494952519 71432921934129528832000 ep283 ep284 320045949196494952519 ep154 ep155 ep156 (@ep382 4203610112 5 131072 4075805 4203610112 (ep387 rfl rfl) rfl) ep388 rfl) rfl rfl))

noncomputable abbrev qz439 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 48711 1000)))

noncomputable abbrev qz425 := qz439

noncomputable abbrev qz349 := qz425

noncomputable abbrev qz132 := (BSN.headSumC qz349 9)

noncomputable abbrev qz133 := (BSN.headSumC qz349 8)

noncomputable abbrev qz426 := (@Neg.neg Complex Complex.instNeg qz439)

noncomputable abbrev qz350 := qz426

noncomputable abbrev qz134 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 8) qz350)

noncomputable def ep389 := @Enclosure.Complex.IsNear.of_eq qz132 (@HAdd.hAdd Complex Complex Complex qz5 qz133 qz134) Bool.false 6449478267 17179869184 2919881782915 550975584600064 Bool.true 3178191953 17179869184 2914048196299 550975584600064

noncomputable def ep390 := @Enclosure.Complex.IsNear.addLitP qz133 qz134 Bool.false 1024908693 8589934592 326689491885 68871948075008 Bool.false 31544141 536870912 162989319085 34435974037504 Bool.false

noncomputable abbrev qz135 := (BSN.headSumC qz349 7)

noncomputable abbrev qz136 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 7) qz350)

noncomputable def ep391 := @Enclosure.Complex.IsNear.of_eq qz133 (@HAdd.hAdd Complex Complex Complex qz5 qz135 qz136) Bool.false 1024908693 8589934592 326689491885 68871948075008 Bool.false 31544141 536870912 162989319085 34435974037504

noncomputable def ep392 := @Enclosure.Complex.IsNear.addLitP qz135 qz136 Bool.true 3523891901 17179869184 2285641857659 550975584600064 Bool.false 1085186879 4294967296 570351664403 137743896150016 Bool.false

noncomputable abbrev qz137 := (BSN.headSumC qz349 6)

noncomputable abbrev qz138 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 6) qz350)

noncomputable def ep393 := @Enclosure.Complex.IsNear.of_eq qz135 (@HAdd.hAdd Complex Complex Complex qz5 qz137 qz138) Bool.true 3523891901 17179869184 2285641857659 550975584600064 Bool.false 1085186879 4294967296 570351664403 137743896150016

noncomputable def ep394 := @Enclosure.Complex.IsNear.addLitP qz137 qz138 Bool.true 8948200601 17179869184 1928889187855 550975584600064 Bool.true 52672437 8589934592 962913283855 275487792300032 Bool.false

noncomputable abbrev qz139 := (BSN.headSumC qz349 5)

noncomputable abbrev qz140 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 5) qz350)

noncomputable def ep395 := @Enclosure.Complex.IsNear.of_eq qz137 (@HAdd.hAdd Complex Complex Complex qz5 qz139 qz140) Bool.true 8948200601 17179869184 1928889187855 550975584600064 Bool.true 52672437 8589934592 962913283855 275487792300032

noncomputable def ep396 := @Enclosure.Complex.IsNear.addLitP qz139 qz140 Bool.true 335793101 4294967296 29635721349 10595684319232 Bool.false 986396751 17179869184 118581422403 42382737276928 Bool.true

noncomputable abbrev qz141 := qz349

noncomputable abbrev qz142 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 4) qz350)

noncomputable def ep397 := @Enclosure.Complex.IsNear.of_eq qz139 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz141 4) qz142) Bool.true 335793101 4294967296 29635721349 10595684319232 Bool.false 986396751 17179869184 118581422403 42382737276928

noncomputable def ep398 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 4) qz142 Bool.true 1200633779 17179869184 1112036809931 550975584600064 Bool.true 1900540401 4294967296 277101136171 137743896150016 Bool.true

noncomputable abbrev qz143 := (@HPow.hPow Complex Complex Complex qz260 qz262 qz350)

noncomputable def ep399 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz141 3) qz143) Bool.true 1200633779 17179869184 1112036809931 550975584600064 Bool.true 1900540401 4294967296 277101136171 137743896150016

noncomputable def ep400 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 3) qz143 Bool.false 4330779623 8589934592 306268608563 275487792300032 Bool.true 4330427427 8589934592 306317933761 275487792300032 Bool.true

noncomputable abbrev qz144 := (@HPow.hPow Complex Complex Complex qz260 qz263 qz350)

noncomputable def ep401 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz141 2) qz144) Bool.false 4330779623 8589934592 306268608563 275487792300032 Bool.true 4330427427 8589934592 306317933761 275487792300032

noncomputable def ep402 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 2) qz144 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep403 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz20) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz141)

noncomputable abbrev qz440 := (Enclosure.sfrac Bool.false 48711 1000)

noncomputable abbrev qz427 := qz440

noncomputable abbrev qz351 := qz427

noncomputable abbrev qz145 := (@HMul.hMul Real Real Real qz253 qz351 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz146 := qz351

noncomputable abbrev qz352 := (@Eq.refl Real qz427)

noncomputable abbrev qz147 := qz352

noncomputable def ep404 := @Enclosure.Complex.IsNear.of_eq qz144 (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz145)))) Bool.true 4259154969 8589934592 306268608563 275487792300032 Bool.true 4330427427 8589934592 306317933761 275487792300032 (BSN.cpow_neg_s_mk qz146 48711 1000 2 qz147 rfl)

noncomputable def ep405 := nat_lit 1893449247700436947923350239138576

noncomputable def ep406 := BSN.sin_dyadic_bound_f 208599574 268435456 2 1 131072 64205 ep405 ep91 ep405 ep405 ep92 ep405 91909 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 208599574) qz274 0 1 ep405 ep91 ep405 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 208599574) qz275 0 1 ep405 ep92 ep405 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz353 := (Enclosure.Real.IsNear.const Bool.false 48711 1000)

noncomputable abbrev qz148 := qz353

noncomputable abbrev qz354 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4425491) qz27)

noncomputable def ep407 := @Enclosure.Real.IsNear.cos_image qz145 qz354 Bool.false 4425491 131072 25 16384 Bool.true 91909 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 1106372943 32768000 3747 2467000 4425491 131072 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz28 48711 1000 0 1 45426 65536 1 32071 1106372943 32768000 3747 2467000 qz148 qz272 rfl) rfl) (Enclosure.sfrac_false_div 4425491 131072) (BSN.cos_reduce1 qz354 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14678890087045704712192) qz30) 226375608064910080 72057594037927936 Bool.false 91909 131072 5 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q1 4425491 131072 226375608064910080 72057594037927936 5 14678890087045704712192 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 91909 131072 14678890087045704712192 18889465931478580854784 208599574 268435456 64205 64142 (ep406 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep408 := BSN.cos_dyadic_bound_f 208599574 268435456 2 1 131072 64205 ep405 ep57 ep405 ep405 ep58 ep405 93447 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 208599574) qz268 0 1 ep405 ep57 ep405 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 208599574) qz269 0 1 ep405 ep58 ep405 rfl rfl rfl rfl) rfl rfl

noncomputable def ep409 := @Enclosure.Real.IsNear.sin_image qz145 qz354 Bool.false 4425491 131072 25 16384 Bool.false 93447 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 1106372943 32768000 3747 2467000 4425491 131072 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz28 48711 1000 0 1 45426 65536 1 32071 1106372943 32768000 3747 2467000 qz148 qz272 rfl) rfl) (Enclosure.sfrac_false_div 4425491 131072) (BSN.sin_reduce1 qz354 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14678890087045704712192) qz30) 226375608064910080 72057594037927936 Bool.false 93447 131072 5 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q1 4425491 131072 226375608064910080 72057594037927936 5 14678890087045704712192 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 93447 131072 14678890087045704712192 18889465931478580854784 208599574 268435456 64205 64142 (ep408 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep410 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz145))) Bool.true 4259154969 8589934592 306268608563 275487792300032 Bool.true 4330427427 8589934592 306317933761 275487792300032 (@Enclosure.Real.IsNear.mulLit_ft qz22 (Real.cos qz145) 46341 65536 1 65536 91909 131072 818159 525451264 4259154969 8589934592 306268608563 275487792300032 qz276 (@Enclosure.Real.IsNear.recentre' (Real.cos qz145) Bool.true 91909 131072 818159 525451264 91909 131072 818159 525451264 (ep407 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz22 (@Neg.neg Real Real.instNeg (Real.sin qz145)) 46341 65536 1 65536 93447 131072 818159 525451264 4330427427 8589934592 306317933761 275487792300032 qz276 (@Enclosure.Real.IsNear.neg (Real.sin qz145) Bool.false 93447 131072 818159 525451264 (@Enclosure.Real.IsNear.recentre' (Real.sin qz145) Bool.false 93447 131072 818159 525451264 93447 131072 818159 525451264 (ep409 rfl rfl) rfl)) rfl)

noncomputable def ep411 := @ep402 4259154969 8589934592 306268608563 275487792300032 Bool.true 4330427427 8589934592 306317933761 275487792300032 Bool.false 4330779623 4330779623 8589934592 306268608563 275487792300032 Bool.true 4330427427 4330427427 8589934592 306317933761 275487792300032 (ep403 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz20 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz31)) (ep404 ep410) rfl rfl

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz253 qz351 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep412 := @Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.true 9862193025 17179869184 499499592805 550975584600064 Bool.false 529346625 8589934592 247884338581 275487792300032 (BSN.cpow_neg_s_mk qz146 48711 1000 3 qz147 rfl)

noncomputable def ep413 := nat_lit 679081008654181893047676010000

noncomputable def ep414 := BSN.cos_dyadic_bound_f 28706510 268435456 2 1 131072 64205 ep413 ep57 ep413 ep413 ep58 ep413 130323 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 28706510) qz268 0 1 ep413 ep57 ep413 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 28706510) qz269 0 1 ep413 ep58 ep413 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7014189) qz27)

noncomputable def ep415 := @Enclosure.Real.IsNear.cos_image qz149 qz355 Bool.false 7014189 131072 25 16384 Bool.true 130323 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 1753547289 32768000 3747 2467000 7014189 131072 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz35 48711 1000 0 1 71998 65536 1 32071 1753547289 32768000 3747 2467000 qz148 qz279 rfl) rfl) (Enclosure.sfrac_false_div 7014189 131072) (BSN.cos_reduce2 qz355 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2020041124947026771968) qz30) 226375608064910080 72057594037927936 Bool.false 130323 131072 8 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q2 7014189 131072 226375608064910080 72057594037927936 8 2020041124947026771968 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 130323 131072 2020041124947026771968 18889465931478580854784 28706510 268435456 64205 64142 (ep414 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep416 := BSN.sin_dyadic_bound_f 28706510 268435456 1 0 131072 64205 0 1 1 0 1 1 13990 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 28706510) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 28706510) qz275 0 0 rfl) rfl rfl

noncomputable def ep417 := @Enclosure.Real.IsNear.sin_image qz149 qz355 Bool.false 7014189 131072 25 16384 Bool.true 13990 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 1753547289 32768000 3747 2467000 7014189 131072 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz35 48711 1000 0 1 71998 65536 1 32071 1753547289 32768000 3747 2467000 qz148 qz279 rfl) rfl) (Enclosure.sfrac_false_div 7014189 131072) (BSN.sin_reduce2 qz355 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2020041124947026771968) qz30) 226375608064910080 72057594037927936 Bool.false 13990 131072 8 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q2 7014189 131072 226375608064910080 72057594037927936 8 2020041124947026771968 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13990 131072 2020041124947026771968 18889465931478580854784 28706510 268435456 64205 64142 (ep416 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep418 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.true 9862193025 17179869184 499499592805 550975584600064 Bool.false 529346625 8589934592 247884338581 275487792300032 (@Enclosure.Real.IsNear.mulLit_ft qz32 (Real.cos qz149) 75675 131072 1 131072 130323 131072 818159 525451264 9862193025 17179869184 499499592805 550975584600064 qz280 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.true 130323 131072 818159 525451264 130323 131072 818159 525451264 (ep415 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz32 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 75675 131072 1 131072 6995 65536 818159 525451264 529346625 8589934592 247884338581 275487792300032 qz280 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.true 6995 65536 818159 525451264 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.true 13990 131072 818159 525451264 6995 65536 818159 525451264 (ep417 rfl rfl) rfl)) rfl)

noncomputable def ep419 := @ep400 9862193025 17179869184 499499592805 550975584600064 Bool.false 529346625 8589934592 247884338581 275487792300032 Bool.true 10313365630555783168 1200633779 17179869184 1112036809931 550975584600064 Bool.true 32651035468086902784 1900540401 4294967296 277101136171 137743896150016 (ep401 (BSN.head_sum_c_succ qz141 2 3 rfl rfl) (ep411 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep412 ep418) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz253 qz351 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep420 := @Enclosure.Complex.IsNear.of_eq qz142 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.true 142538625 17179869184 429020700217 550975584600064 Bool.false 8588558355 17179869184 433153946555 550975584600064 (BSN.cpow_neg_s_mk qz146 48711 1000 4 qz147 rfl)

noncomputable def ep421 := nat_lit 265189727166548100373797967925928220019095325236747777454977028487970816

noncomputable def ep422 := nat_lit 917834457585774120806131576557150838191824746453788979422567963099136

noncomputable def ep423 := nat_lit 793733512584472752879781640624670358380902326217335754406085949537714176

noncomputable def ep424 := BSN.cos_dyadic_bound_f 417201196 268435456 3 2 131072 64205 ep421 ep76 ep422 ep423 ep78 ep422 2175 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 417201196) qz268 0 2 ep421 ep76 ep422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 417201196) qz269 0 2 ep423 ep78 ep422 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz356 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8850983) qz27)

noncomputable def ep425 := @Enclosure.Real.IsNear.cos_image qz150 qz356 Bool.false 8850983 131072 25 16384 Bool.true 2175 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 1106372943 16384000 3747 2467000 8850983 131072 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz39 48711 1000 0 1 90852 65536 1 32071 1106372943 16384000 3747 2467000 qz148 qz283 rfl) rfl) (Enclosure.sfrac_false_div 8850983 131072) (BSN.cos_reduce2 qz356 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29357924289279485280256) qz30) 226375608064910080 72057594037927936 Bool.false 2175 131072 10 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q2 8850983 131072 226375608064910080 72057594037927936 10 29357924289279485280256 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 2175 131072 29357924289279485280256 18889465931478580854784 417201196 268435456 64205 64142 (ep424 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep426 := nat_lit 476607241333717961376191437005425075363818125628982968235420596907868160

noncomputable def ep427 := nat_lit 1246771042942693883599196217223592191262451184200696877507036453294637056

noncomputable def ep428 := BSN.sin_dyadic_bound_f 417201196 268435456 3 2 131072 64205 ep426 ep69 ep422 ep427 ep72 ep422 131053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 417201196) qz274 0 2 ep426 ep69 ep422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 417201196) qz275 0 2 ep427 ep72 ep422 rfl rfl rfl rfl) rfl rfl

noncomputable def ep429 := @Enclosure.Real.IsNear.sin_image qz150 qz356 Bool.false 8850983 131072 25 16384 Bool.true 131053 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 1106372943 16384000 3747 2467000 8850983 131072 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz39 48711 1000 0 1 90852 65536 1 32071 1106372943 16384000 3747 2467000 qz148 qz283 rfl) rfl) (Enclosure.sfrac_false_div 8850983 131072) (BSN.sin_reduce2 qz356 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29357924289279485280256) qz30) 226375608064910080 72057594037927936 Bool.false 131053 131072 10 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q2 8850983 131072 226375608064910080 72057594037927936 10 29357924289279485280256 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131053 131072 29357924289279485280256 18889465931478580854784 417201196 268435456 64205 64142 (ep428 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep430 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.true 142538625 17179869184 429020700217 550975584600064 Bool.false 8588558355 17179869184 433153946555 550975584600064 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz150) 65535 131072 1 131072 2175 131072 818159 525451264 142538625 17179869184 429020700217 550975584600064 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.true 2175 131072 818159 525451264 2175 131072 818159 525451264 (ep425 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 65535 131072 1 131072 131053 131072 818159 525451264 8588558355 17179869184 433153946555 550975584600064 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.true 131053 131072 818159 525451264 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.true 131053 131072 818159 525451264 131053 131072 818159 525451264 (ep429 rfl rfl) rfl)) rfl)

noncomputable def ep431 := @ep398 142538625 17179869184 429020700217 550975584600064 Bool.false 8588558355 17179869184 433153946555 550975584600064 Bool.true 23075526192278798336 335793101 4294967296 29635721349 10595684319232 Bool.false 4236541786425655296 986396751 17179869184 118581422403 42382737276928 (ep399 (BSN.head_sum_c_succ qz141 3 4 rfl rfl) (ep419 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep420 ep430) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz253 qz351 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep432 := @Enclosure.Complex.IsNear.of_eq qz140 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.true 7605028197 17179869184 387831677707 550975584600064 Bool.true 1091741625 17179869184 384268076471 550975584600064 (BSN.cpow_neg_s_mk qz146 48711 1000 5 qz147 rfl)

noncomputable def ep433 := nat_lit 339679010848923719432875122439786083092155196026526396207603062500000000

noncomputable def ep434 := nat_lit 466724442906414820149890857846178396178754696433120727539062500000000

noncomputable def ep435 := nat_lit 888879855506285069758239783096260214504688481989534556508659062500000000

noncomputable def ep436 := BSN.sin_dyadic_bound_f 383382750 268435456 3 2 131072 64205 ep433 ep69 ep434 ep435 ep72 ep434 129741 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 383382750) qz274 0 2 ep433 ep69 ep434 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 383382750) qz275 0 2 ep435 ep72 ep434 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5137841) qz38)

noncomputable def ep437 := @Enclosure.Real.IsNear.cos_image qz151 qz357 Bool.false 5137841 65536 25 16384 Bool.true 129741 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 1284460359 16384000 3747 2467000 5137841 65536 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz42 48711 1000 0 1 105476 65536 1 32071 1284460359 16384000 3747 2467000 qz148 qz288 rfl) rfl) (Enclosure.sfrac_false_div 5137841 65536) (BSN.cos_reduce1 qz357 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13489081361888006111232) qz284) 226375608064910080 72057594037927936 Bool.false 129741 131072 12 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q1 5137841 65536 226375608064910080 72057594037927936 12 13489081361888006111232 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 129741 131072 13489081361888006111232 9444732965739290427392 383382750 268435456 64205 64142 (ep436 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep438 := nat_lit 188917994668471584049441686181146125449498999879818273772019062500000000

noncomputable def ep439 := nat_lit 565820535119601922508025276827746019556139490246588579860979062500000000

noncomputable def ep440 := BSN.cos_dyadic_bound_f 383382750 268435456 3 2 131072 64205 ep438 ep76 ep434 ep439 ep78 ep434 18625 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 383382750) qz268 0 2 ep438 ep76 ep434 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 383382750) qz269 0 2 ep439 ep78 ep434 rfl rfl rfl rfl) rfl rfl

noncomputable def ep441 := @Enclosure.Real.IsNear.sin_image qz151 qz357 Bool.false 5137841 65536 25 16384 Bool.false 18625 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 1284460359 16384000 3747 2467000 5137841 65536 25 16384 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz42 48711 1000 0 1 105476 65536 1 32071 1284460359 16384000 3747 2467000 qz148 qz288 rfl) rfl) (Enclosure.sfrac_false_div 5137841 65536) (BSN.sin_reduce1 qz357 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13489081361888006111232) qz284) 226375608064910080 72057594037927936 Bool.false 18625 131072 12 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q1 5137841 65536 226375608064910080 72057594037927936 12 13489081361888006111232 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 18625 131072 13489081361888006111232 9444732965739290427392 383382750 268435456 64205 64142 (ep440 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep442 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.true 7605028197 17179869184 387831677707 550975584600064 Bool.true 1091741625 17179869184 384268076471 550975584600064 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz151) 58617 131072 1 131072 129741 131072 818159 525451264 7605028197 17179869184 387831677707 550975584600064 qz289 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.true 129741 131072 818159 525451264 129741 131072 818159 525451264 (ep437 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz40 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 58617 131072 1 131072 18625 131072 818159 525451264 1091741625 17179869184 384268076471 550975584600064 qz289 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.false 18625 131072 818159 525451264 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.false 18625 131072 818159 525451264 18625 131072 818159 525451264 (ep441 rfl rfl) rfl)) rfl)

noncomputable def ep443 := @ep396 7605028197 17179869184 387831677707 550975584600064 Bool.true 1091741625 17179869184 384268076471 550975584600064 Bool.true 38432228939342544896 8948200601 17179869184 1928889187855 550975584600064 Bool.true 1809811154524962816 52672437 8589934592 962913283855 275487792300032 (ep397 (BSN.head_sum_c_succ qz141 4 5 rfl rfl) (ep431 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep432 ep442) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz253 qz351 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep444 := @Enclosure.Complex.IsNear.of_eq qz138 (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.false 1356077175 4294967296 89188167451 137743896150016 Bool.false 2223046195 8589934592 177790044951 275487792300032 (BSN.cpow_neg_s_mk qz146 48711 1000 6 qz147 rfl)

noncomputable def ep445 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz45 48711 1000 0 1 4034664351997175 2251799813685248 500000000032071 16035500000000000000 7861301410005375657 90071992547409920 1873500000120170037 1233500000000000000000 qz148 (BSN.isNear_log_sfrac 6 1 4034664351997175 2251799813685248 500000000032071 16035500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz291) Bool.false 4230652207559789772800 2361183241434822606848 1000000000064142 32071000000000000000 4034664351997175 2251799813685248 500000000032071 16035500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 26572 65536 24973259072661432 36028797018963968 32071 1000000000000000 rfl rfl rfl rfl (ep115 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep446 := nat_lit 3173367185730565498524521716740081

noncomputable def ep447 := BSN.sin_dyadic_bound_f 237344997 268435456 2 1 131072 64205 ep446 ep91 ep446 ep446 ep92 ep446 101370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 237344997) qz274 0 1 ep446 ep91 ep446 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 237344997) qz275 0 1 ep446 ep92 ep446 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11439699) qz27)

noncomputable def ep448 := @Enclosure.Real.IsNear.cos_image qz152 qz358 Bool.false 11439699 131072 25 16384 Bool.false 101370 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 7861301410005375657 90071992547409920 1873500000120170037 1233500000000000000000 11439699 131072 25 16384 (ep445 rfl) rfl) (Enclosure.sfrac_false_div 11439699 131072) (BSN.cos_reduce3 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16701669400566172745728) qz30) 226375608064910080 72057594037927936 Bool.false 101370 131072 13 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q3 11439699 131072 226375608064910080 72057594037927936 13 16701669400566172745728 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 101370 131072 16701669400566172745728 18889465931478580854784 237344997 268435456 64205 64142 (ep447 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep449 := nat_lit 27691538567965292689225345477562417682378361920942602712811605809750241

noncomputable def ep450 := nat_lit 10070259295471529384555492215080059381963157455982637768745711886561

noncomputable def ep451 := nat_lit 83054475185304935008906925448257092928371159447915842862897326005477601

noncomputable def ep452 := BSN.cos_dyadic_bound_f 237344997 268435456 3 2 131072 64205 ep449 ep76 ep450 ep451 ep78 ep450 83089 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 237344997) qz268 0 2 ep449 ep76 ep450 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 237344997) qz269 0 2 ep451 ep78 ep450 rfl rfl rfl rfl) rfl rfl

noncomputable def ep453 := @Enclosure.Real.IsNear.sin_image qz152 qz358 Bool.false 11439699 131072 25 16384 Bool.true 83089 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 7861301410005375657 90071992547409920 1873500000120170037 1233500000000000000000 11439699 131072 25 16384 (ep445 rfl) rfl) (Enclosure.sfrac_false_div 11439699 131072) (BSN.sin_reduce3 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16701669400566172745728) qz30) 226375608064910080 72057594037927936 Bool.false 83089 131072 13 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q3 11439699 131072 226375608064910080 72057594037927936 13 16701669400566172745728 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 83089 131072 16701669400566172745728 18889465931478580854784 237344997 268435456 64205 64142 (ep452 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep454 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.false 1356077175 4294967296 89188167451 137743896150016 Bool.false 2223046195 8589934592 177790044951 275487792300032 (@Enclosure.Real.IsNear.mulLit_ff qz43 (Real.cos qz152) 26755 65536 1 65536 50685 65536 818159 525451264 1356077175 4294967296 89188167451 137743896150016 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.false 101370 131072 818159 525451264 50685 65536 818159 525451264 (ep448 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz43 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 26755 65536 1 65536 83089 131072 818159 525451264 2223046195 8589934592 177790044951 275487792300032 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.true 83089 131072 818159 525451264 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.true 83089 131072 818159 525451264 83089 131072 818159 525451264 (ep453 rfl rfl) rfl)) rfl)

noncomputable def ep455 := @ep394 1356077175 4294967296 89188167451 137743896150016 Bool.false 2223046195 8589934592 177790044951 275487792300032 Bool.true 15135000469434269696 3523891901 17179869184 2285641857659 550975584600064 Bool.false 18643368621413236736 1085186879 4294967296 570351664403 137743896150016 (ep395 (BSN.head_sum_c_succ qz141 5 6 rfl rfl) (ep443 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep444 ep454) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz253 qz351 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep456 := @Enclosure.Complex.IsNear.of_eq qz136 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.false 5573709287 17179869184 327874077421 550975584600064 Bool.true 832833751 4294967296 81605611937 137743896150016 (BSN.cpow_neg_s_mk qz146 48711 1000 7 qz147 rfl)

noncomputable def ep457 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz48 48711 1000 0 1 4381766428990711 2251799813685248 500000000032071 16035500000000000000 213440224522566523521 2251799813685248000 1873500000120170037 1233500000000000000000 qz148 (BSN.isNear_log_sfrac 7 1 4381766428990711 2251799813685248 500000000032071 16035500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz295) Bool.false 4594615115045363777536 2361183241434822606848 1000000000064142 32071000000000000000 4381766428990711 2251799813685248 500000000032071 16035500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 36674 65536 24973259072661432 36028797018963968 32071 1000000000000000 rfl rfl rfl rfl (ep125 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep458 := nat_lit 437330761419683233118251852496896

noncomputable def ep459 := BSN.cos_dyadic_bound_f 144611392 268435456 2 1 131072 64205 ep458 ep57 ep458 ep458 ep58 ep458 112507 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 144611392) qz268 0 1 ep458 ep57 ep458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 144611392) qz269 0 1 ep458 ep58 ep458 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 776491) (@Nat.cast Real Real.instNatCast 8192))

noncomputable abbrev qz360 := (@Nat.cast Real Real.instNatCast 1180591620717411303424)

noncomputable def ep460 := @Enclosure.Real.IsNear.cos_image qz153 qz359 Bool.false 776491 8192 25 16384 Bool.false 112507 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 213440224522566523521 2251799813685248000 1873500000120170037 1233500000000000000000 776491 8192 25 16384 (ep457 rfl) rfl) (Enclosure.sfrac_false_div 776491 8192) (BSN.cos_reduce0 qz359 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 636007628144799383552) qz360) 226375608064910080 72057594037927936 Bool.false 112507 131072 15 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 776491 8192 226375608064910080 72057594037927936 15 636007628144799383552 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 112507 131072 636007628144799383552 1180591620717411303424 144611392 268435456 64205 64142 (ep459 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep461 := BSN.sin_dyadic_bound_f 144611392 268435456 2 1 131072 64205 ep458 ep91 ep458 ep458 ep92 ep458 67244 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 144611392) qz274 0 1 ep458 ep91 ep458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 144611392) qz275 0 1 ep458 ep92 ep458 rfl rfl rfl rfl) rfl rfl

noncomputable def ep462 := @Enclosure.Real.IsNear.sin_image qz153 qz359 Bool.false 776491 8192 25 16384 Bool.false 67244 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 213440224522566523521 2251799813685248000 1873500000120170037 1233500000000000000000 776491 8192 25 16384 (ep457 rfl) rfl) (Enclosure.sfrac_false_div 776491 8192) (BSN.sin_reduce0 qz359 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 636007628144799383552) qz360) 226375608064910080 72057594037927936 Bool.false 67244 131072 15 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 776491 8192 226375608064910080 72057594037927936 15 636007628144799383552 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67244 131072 636007628144799383552 1180591620717411303424 144611392 268435456 64205 64142 (ep461 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep463 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.false 5573709287 17179869184 327874077421 550975584600064 Bool.true 832833751 4294967296 81605611937 137743896150016 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz153) 49541 131072 1 131072 112507 131072 818159 525451264 5573709287 17179869184 327874077421 550975584600064 qz297 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.false 112507 131072 818159 525451264 112507 131072 818159 525451264 (ep460 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 49541 131072 1 131072 16811 32768 818159 525451264 832833751 4294967296 81605611937 137743896150016 qz297 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.false 16811 32768 818159 525451264 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.false 67244 131072 818159 525451264 16811 32768 818159 525451264 (ep462 rfl rfl) rfl)) rfl)

noncomputable def ep464 := @ep392 5573709287 17179869184 327874077421 550975584600064 Bool.true 832833751 4294967296 81605611937 137743896150016 Bool.false 35215594542568833024 1024908693 8589934592 326689491885 68871948075008 Bool.false 1083848431803301888 31544141 536870912 162989319085 34435974037504 (ep393 (BSN.head_sum_c_succ qz141 6 7 rfl rfl) (ep455 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep456 ep463) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz253 qz351 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep465 := @Enclosure.Complex.IsNear.of_eq qz134 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 4399660881 17179869184 306365847835 550975584600064 Bool.true 4187604465 17179869184 306219090939 550975584600064 (BSN.cpow_neg_s_mk qz146 48711 1000 8 qz147 rfl)

noncomputable def ep466 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz51 48711 1000 0 1 9364972152248037 4503599627370496 1000000000096213 32071000000000000000 456177158508154130307 4503599627370496000 3747000000360510111 2467000000000000000000 qz148 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000096213 32071000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz299) Bool.false 4909942519757818822656 2361183241434822606848 1000000000096213 32071000000000000000 9364972152248037 4503599627370496 1000000000096213 32071000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 65536 24973259072661432 36028797018963968 32071 1000000000000000 rfl rfl rfl rfl (ep136 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep467 := nat_lit 1738716545909130191247471041395216

noncomputable def ep468 := BSN.cos_dyadic_bound_f 204200686 268435456 2 1 131072 64205 ep467 ep57 ep467 ep467 ep58 ep467 94941 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 204200686) qz268 0 1 ep467 ep57 ep467 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 204200686) qz269 0 1 ep467 ep58 ep467 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz361 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6638251) qz38)

noncomputable def ep469 := @Enclosure.Real.IsNear.cos_image qz154 qz361 Bool.false 6638251 65536 25 16384 Bool.false 94941 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 456177158508154130307 4503599627370496000 3747000000360510111 2467000000000000000000 6638251 65536 25 16384 (ep466 rfl) rfl) (Enclosure.sfrac_false_div 6638251 65536) (BSN.cos_reduce0 qz361 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7184672950653709975552) qz284) 226375608064910080 72057594037927936 Bool.false 94941 131072 16 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 6638251 65536 226375608064910080 72057594037927936 16 7184672950653709975552 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 94941 131072 7184672950653709975552 9444732965739290427392 204200686 268435456 64205 64142 (ep468 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep470 := BSN.sin_dyadic_bound_f 204200686 268435456 2 1 131072 64205 ep467 ep91 ep467 ep467 ep92 ep467 90365 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 204200686) qz274 0 1 ep467 ep91 ep467 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 204200686) qz275 0 1 ep467 ep92 ep467 rfl rfl rfl rfl) rfl rfl

noncomputable def ep471 := @Enclosure.Real.IsNear.sin_image qz154 qz361 Bool.false 6638251 65536 25 16384 Bool.false 90365 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 456177158508154130307 4503599627370496000 3747000000360510111 2467000000000000000000 6638251 65536 25 16384 (ep466 rfl) rfl) (Enclosure.sfrac_false_div 6638251 65536) (BSN.sin_reduce0 qz361 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7184672950653709975552) qz284) 226375608064910080 72057594037927936 Bool.false 90365 131072 16 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 6638251 65536 226375608064910080 72057594037927936 16 7184672950653709975552 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 90365 131072 7184672950653709975552 9444732965739290427392 204200686 268435456 64205 64142 (ep470 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep472 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 4399660881 17179869184 306365847835 550975584600064 Bool.true 4187604465 17179869184 306219090939 550975584600064 (@Enclosure.Real.IsNear.mulLit_ff qz49 (Real.cos qz154) 46341 131072 1 131072 94941 131072 818159 525451264 4399660881 17179869184 306365847835 550975584600064 qz301 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 94941 131072 818159 525451264 94941 131072 818159 525451264 (ep469 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 46341 131072 1 131072 90365 131072 818159 525451264 4187604465 17179869184 306219090939 550975584600064 qz301 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.false 90365 131072 818159 525451264 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.false 90365 131072 818159 525451264 90365 131072 818159 525451264 (ep471 rfl rfl) rfl)) rfl)

noncomputable def ep473 := @ep390 4399660881 17179869184 306365847835 550975584600064 Bool.true 4187604465 17179869184 306219090939 550975584600064 Bool.false 55400596466055512064 6449478267 17179869184 2919881782915 550975584600064 Bool.true 1706278812318171136 3178191953 17179869184 2914048196299 550975584600064 (ep391 (BSN.head_sum_c_succ qz141 7 8 rfl rfl) (ep464 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep465 ep472) rfl rfl

theorem EMRow09.d10 : Enclosure.Complex.IsNear qz132 Bool.false 6449478267 17179869184 2919881782915 550975584600064 Bool.true 3178191953 17179869184 2914048196299 550975584600064 := ep389 (BSN.head_sum_c_succ qz141 8 9 rfl rfl) (ep473 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep474 := nat_lit 19878401012235720439628273949

noncomputable def ep475 := nat_lit 26717734504303734858711040000

noncomputable def ep476 := nat_lit 193722384349679351274560439056642327

noncomputable def ep477 := nat_lit 27480500202094216861645510688112640000

noncomputable abbrev qz428 := (@HAdd.hAdd Complex Complex Complex qz433 (@HAdd.hAdd Complex Complex Complex qz433 qz436 (@HMul.hMul Complex Complex Complex qz435 Complex.I (@HDiv.hDiv Complex Complex Complex qz437 (↑qz440) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz362 := qz428

noncomputable abbrev qz155 := (Complex.Stirling.logGammaStirling 1 qz362)

noncomputable abbrev qz429 := (@HAdd.hAdd Complex Complex Complex qz433 qz436 (@HMul.hMul Complex Complex Complex qz435 Complex.I (@HDiv.hDiv Complex Complex Complex qz437 (↑qz440) (2 : Complex))))

noncomputable abbrev qz363 := qz429

noncomputable abbrev qz156 := qz363

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz253 (@HDiv.hDiv Real Real Real qz256 qz351 (2 : Real)) (Real.log Real.pi))

noncomputable def ep478 := Complex.re (@HMul.hMul Complex Complex Complex qz52 (Complex.exp (@HMul.hMul Complex Complex Complex qz52 Complex.I ↑(@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))))) qz157))) (zetaApproximant qz141 1 10))

noncomputable def ep479 := @Enclosure.Real.IsNear.of_eq ep478 (@HSub.hSub Real Real Real qz53 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))))) qz157)) (Complex.re (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))))) qz157)) (Complex.im (zetaApproximant qz141 1 10))))

noncomputable def ep480 := nat_lit 477070549003997578853778954251

noncomputable def ep481 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))))) qz157)) (Complex.re (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))))) qz157)) (Complex.im (zetaApproximant qz141 1 10))) ep480

noncomputable def ep482 := nat_lit 641225628103289636609064960000

noncomputable def ep483 := nat_lit 4582821916413982217203549163662518437

noncomputable def ep484 := nat_lit 659532004850261204679492256514703360000

noncomputable def ep485 := nat_lit 25649025124131585464362598400

noncomputable def ep486 := nat_lit 66515307978322213385901373696897411

noncomputable def ep487 := nat_lit 12236678567769521606261925770200164425888514865552057958400

noncomputable def ep488 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))))) qz157)) (Complex.re (zetaApproximant qz141 1 10)) 131071 131072 4332373

noncomputable def ep489 := nat_lit 3639787206964145988462581

noncomputable def ep490 := nat_lit 4892163300348584263680000

noncomputable def ep491 := nat_lit 322970834767743001456316367

noncomputable def ep492 := nat_lit 52298856401826481973493760000

noncomputable def ep493 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))))) qz157)) Bool.false 131071 131072 4332373

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 205889) (@Nat.cast Real Real.instNatCast 8192))

noncomputable def ep494 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))))) qz157) qz364 Bool.false 205889 8192 131

noncomputable def ep495 := nat_lit 1050902528000000000000000000

noncomputable def ep496 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))))) qz157) Bool.false 452754715946624813257 18014398509481984000 1042081388243949633692543 ep495

noncomputable def ep497 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))))) qz157 955004471205833279689 18014398509481984000 260976147743949633692543 ep495 3654347931 131072000

noncomputable def ep498 := nat_lit 59343466128556007523221504000

noncomputable def ep499 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 171753080595167605319 4503599627370496000 111449370031100919683213 ep168 Bool.false 955004471205833279689 18014398509481984000

noncomputable def ep500 := @Enclosure.Complex.IsNear.subLitP qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 142989128492790982319 4503599627370496000 107353370028736388995213 ep168 Bool.false 1010489790623355647689 18014398509481984000 228208147742898731164543

noncomputable def ep501 := nat_lit 773507109768131594665318833113268224

noncomputable def ep502 := nat_lit 268809861291234270949715217674665984

noncomputable abbrev qz365 := (@HSub.hSub Complex Complex Complex qz417 qz428 qz420)

noncomputable abbrev qz366 := (Complex.log qz428)

noncomputable abbrev qz158 := (@HSub.hSub Complex Complex Complex qz303 (@HMul.hMul Complex Complex Complex qz302 qz365 qz366) qz362)

noncomputable abbrev qz159 := qz362

noncomputable def ep503 := @Enclosure.Complex.IsNear.of_eq qz155 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz158 qz59) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz54 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz159 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k)))))) Bool.true 142989128492790982319

noncomputable def ep504 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz158 qz59) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz54 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz159 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) Bool.true 142990539974653126319 4503599627370496000

noncomputable def ep505 := nat_lit 307066815280039520411909619712

noncomputable def ep506 := nat_lit 1085005150917299990150288244736000

noncomputable def ep507 := @ep504 52418458498666196981 128284000000000000000000 Bool.false 1010550905906010666697 18014398509481984000 27855500014172142829 128284000000000000000000 Bool.false 673047 2147483648 3 2147483648 Bool.true 3642754713 1073741824000 16237 1073741824000 Bool.true ep505 142989128492790982319 4503599627370496000 107353370028736388995213 ep168 Bool.false ep506

noncomputable def ep508 := @Enclosure.Complex.IsNear.addLitP qz158 qz59 Bool.true 147129033022125254319 4503599627370496000 50461000002572446981 128284000000000000000000

noncomputable def ep509 := nat_lit 9371028027778867286441984

noncomputable def ep510 := @ep508 Bool.false 1010550905906010666697 18014398509481984000 27855500014172142829 128284000000000000000000 Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 Bool.true ep509 142990539974653126319 4503599627370496000 52418458498666196981 128284000000000000000000 Bool.false 1010550905906010666697 1010550905906010666697 18014398509481984000

noncomputable abbrev qz160 := (@HMul.hMul Complex Complex Complex qz302 qz365 qz366)

noncomputable def ep511 := @Enclosure.Complex.IsNear.subLitP qz160 qz159 Bool.true 136995933860541638319 4503599627370496000 50461000002572446981 128284000000000000000000 Bool.false 1449300588803699128009

noncomputable def ep512 := nat_lit 4042203623624042666788000

noncomputable def ep513 := @ep511 18014398509481984000 27855500014172142829 128284000000000000000000 Bool.false 9000 4000 0 1 Bool.false 97422 4000 0 1 Bool.true 588516132088501017276000 147129033022125254319 4503599627370496000 50461000002572446981 128284000000000000000000 Bool.false ep512 1010550905906010666697 18014398509481984000 27855500014172142829 128284000000000000000000

noncomputable abbrev qz161 := qz365

noncomputable abbrev qz162 := qz366

noncomputable def ep514 := @Enclosure.Complex.IsNear.mul qz161 qz162 Bool.true 136995933860541638319 4503599627370496000 50461000002572446981 128284000000000000000000 Bool.false 1449300588803699128009 18014398509481984000 27855500014172142829

noncomputable abbrev qz163 := (Complex.re qz365)

noncomputable abbrev qz164 := (Complex.re qz366)

noncomputable abbrev qz165 := (Complex.im qz365)

noncomputable abbrev qz166 := (Complex.im qz366)

noncomputable def ep515 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz163 qz164) (@HMul.hMul Real Real Real qz0 qz165 qz166) 201572428945170633 36028797018963968 3500000002020473 256568000000000000000 40548121869671991861 1125899906842624000

noncomputable def ep516 := nat_lit 1233949673371216875726025083687272448

noncomputable def ep517 := @Enclosure.Real.IsNear.mulLit_ff qz163 qz164 7000 4000 0 1 28796061277881519 9007199254740992 500000000288639 64142000000000000000

noncomputable def ep518 := @Enclosure.Complex.IsNear.re_isNear qz161 Bool.false 7000 4000 0 1 Bool.false 97422 4000 0 1

noncomputable abbrev qz367 := (Enclosure.sfrac Bool.false 97422 4000)

noncomputable abbrev qz167 := qz367

noncomputable def ep519 := @Enclosure.Complex.IsNear.of_eq qz161 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz167) Bool.false 7000 4000 0 1 Bool.false 97422 4000 0

noncomputable abbrev qz168 := (Complex.mk qz317 qz367)

noncomputable def ep520 := @Enclosure.Complex.IsNear.of_eq qz162 (Complex.log qz168) Bool.false 28796061277881519 9007199254740992 500000000288639 64142000000000000000 Bool.false 832422283871651 562949953421312 1000000000032071 64142000000000000000

noncomputable def ep521 := nat_lit 1493684325869471201042839626457972609847040

noncomputable def ep522 := nat_lit 3015857374421103582613417191136666585088

noncomputable def ep523 := nat_lit 10881671497642135475782622622489969408

noncomputable def ep524 := BSN.log_dyadic_bound 1380046084 17764046084 3 2 ep521 131072 64142 ep522 ep523 20406 19144092168 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1380046084) (BSN.artanhQ 17764046084) 0 2 ep522 ep521 ep523 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz368 := (Real.log (Enclosure.sfrac Bool.false 9572046084 16000000))

noncomputable def ep525 := @Enclosure.Real.IsNear.mulLit_ff qz77 qz368 1 2 0 1 28796061277881519 4503599627370496 500000000288639 32071000000000000000 28796061277881519 9007199254740992 500000000288639 64142000000000000000 qz319 (BSN.isNear_log_sfrac 9572046084 16000000 28796061277881519 4503599627370496 500000000288639 32071000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9572046084) qz320)) Bool.false 30194858750515891666944 4722366482869645213696 1000000000577278 64142000000000000000 28796061277881519 4503599627370496 500000000288639 32071000000000000000 (BSN.log_rat_reduce_isNear 9572046084 16000000 9 19144092168 16384000000 20406 131072 24973259072661432 36028797018963968 64142 1000000000000000 rfl rfl rfl rfl (ep524 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep526 := BSN.arctan_dyadic_bound_f 9000 97422 1 0 131072 64142 0 1 1 0 1 1 12074 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 97422) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 97422) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz369 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 97422)))

noncomputable def ep527 := @Enclosure.Real.IsNear.subLit_ff_p qz78 qz369 884279719003555 562949953421312 1 2000000000000000 12074 131072 1 64142 109107253591625039872 832422283871651 562949953421312 1000000000032071 64142000000000000000 qz79 (ep526 rfl) rfl rfl

noncomputable abbrev qz370 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 97422) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep528 := @Enclosure.Complex.IsNear.re_isNear qz162 Bool.false 28796061277881519 9007199254740992 500000000288639 64142000000000000000 Bool.false 832422283871651 562949953421312 1000000000032071 64142000000000000000 (ep520 (@congrArg Complex Complex qz159 qz168 Complex.log (BSN.w_shift_mk qz146 Bool.false 48711 1000 2 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz168) Bool.false 28796061277881519 9007199254740992 500000000288639 64142000000000000000 Bool.false 832422283871651 562949953421312 1000000000032071 64142000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz168)) (@HMul.hMul Real Real Real qz0 qz77 qz368) Bool.false 28796061277881519 9007199254740992 500000000288639 64142000000000000000 (Enclosure.clog_re_eq 9000 97422 4000 9572046084 16000000 rfl rfl rfl) (ep525 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz168)) qz370 Bool.false 832422283871651 562949953421312 1000000000032071 64142000000000000000 (Enclosure.clog_im_eq 9000 97422 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz370 (@HSub.hSub Real Real Real qz53 qz78 qz369) Bool.false 832422283871651 562949953421312 1000000000032071 64142000000000000000 (BSN.arctan_recip 97422 9000 rfl rfl) ep527))))

noncomputable def ep529 := @Enclosure.Real.IsNear.mulLit_ff qz165 qz166 97422 4000 0 1 832422283871651 562949953421312 1000000000032071 64142000000000000000

noncomputable def ep530 := @Enclosure.Complex.IsNear.im_isNear qz161 Bool.false 7000 4000 0 1 Bool.false 97422 4000 0 1

noncomputable def ep531 := @Enclosure.Complex.IsNear.im_isNear qz162 Bool.false 28796061277881519 9007199254740992 500000000288639 64142000000000000000 Bool.false 832422283871651 562949953421312 1000000000032071 64142000000000000000 (ep520 (@congrArg Complex Complex qz159 qz168 Complex.log (BSN.w_shift_mk qz146 Bool.false 48711 1000 2 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz168) Bool.false 28796061277881519 9007199254740992 500000000288639 64142000000000000000 Bool.false 832422283871651 562949953421312 1000000000032071 64142000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz168)) (@HMul.hMul Real Real Real qz0 qz77 qz368) Bool.false 28796061277881519 9007199254740992 500000000288639 64142000000000000000 (Enclosure.clog_re_eq 9000 97422 4000 9572046084 16000000 rfl rfl rfl) (ep525 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz168)) qz370 Bool.false 832422283871651 562949953421312 1000000000032071 64142000000000000000 (Enclosure.clog_im_eq 9000 97422 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz370 (@HSub.hSub Real Real Real qz53 qz78 qz369) Bool.false 832422283871651 562949953421312 1000000000032071 64142000000000000000 (BSN.arctan_recip 97422 9000 rfl rfl) ep527))))

noncomputable abbrev qz371 := (Enclosure.Real.IsNear.const Bool.false 97422 4000)

noncomputable abbrev qz169 := (@ep519 1 (BSN.w_sub_half_mk qz351 Bool.false 48711 1000 2 qz352 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz367 Bool.false 7000 4000 0 1 Bool.false 97422 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz371))

noncomputable def ep532 := @ep515 3747000000120170037 9868000000000000000000 ep516 136995933860541638319 4503599627370496000 50461000002572446981 128284000000000000000000 (@ep517 201572428945170633 36028797018963968 3500000002020473 256568000000000000000 (ep518 qz169) ep528 rfl) (@ep529 40548121869671991861 1125899906842624000 3747000000120170037 9868000000000000000000 (ep530 qz169) ep531 rfl) rfl

noncomputable def ep533 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz163 qz166) (@HMul.hMul Real Real Real qz0 qz165 qz164) 5826955987101557 2251799813685248 7000000000224497 256568000000000000000 1402684940906886672009 18014398509481984000

noncomputable def ep534 := nat_lit 3263534795842089920035486482386911232

noncomputable def ep535 := @Enclosure.Real.IsNear.mulLit_ff qz163 qz166 7000 4000 0 1 832422283871651 562949953421312 1000000000032071 64142000000000000000

noncomputable def ep536 := @Enclosure.Real.IsNear.mulLit_ff qz165 qz164 97422 4000 0 1 28796061277881519 9007199254740992 500000000288639 64142000000000000000

noncomputable def ep537 := @ep533 1873500001081530333 9868000000000000000000 ep534 1449300588803699128009 18014398509481984000 27855500014172142829 128284000000000000000000 (@ep535 5826955987101557 2251799813685248 7000000000224497 256568000000000000000 (ep518 qz169) ep531 rfl) (@ep536 1402684940906886672009 18014398509481984000 1873500001081530333 9868000000000000000000 (ep530 qz169) ep528 rfl) rfl

noncomputable def ep538 := @Enclosure.Complex.IsNear.of_eq qz159 qz168 Bool.false 9000 4000 0 1 Bool.false 97422 4000 0 1 (BSN.w_shift_mk qz146 Bool.false 48711 1000 2 qz147 rfl)

noncomputable abbrev qz372 := (ep538 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 97422 4000) Bool.false 9000 4000 0 1 Bool.false 97422 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 97422 4000)))

noncomputable abbrev qz170 := qz372

noncomputable def ep539 := ep513 (@ep514 128284000000000000000000 (ep532 rfl) (ep537 rfl)) qz170 rfl rfl rfl rfl rfl rfl

noncomputable def ep540 := @ep510 27855500014172142829 128284000000000000000000 (ep539 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz82 (↑qz3) Bool.false 60223 65536 1 65536 Bool.false 0 1 0 1 (@ep208 65536 1 65536 (ep210 rfl) (ep212 rfl) rfl rfl) (@ep213 1 0 1 (ep215 rfl) (ep217 rfl) rfl rfl))

noncomputable abbrev qz373 := (@HPow.hPow Complex Int Complex qz422 qz428 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz171 := qz373

noncomputable def ep541 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz54 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz159 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz54 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz159 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) qz171)) Bool.false 673047 2147483648 3 2147483648

noncomputable def ep542 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz54 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz159 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) qz171) Bool.false 0 1 0 1 Bool.false

noncomputable def ep543 := @ep542 0 1 0 1 Bool.false 673047 2147483648 3 2147483648 Bool.true 3642754713 1073741824000 16237 1073741824000 Bool.false 673047 673047 2147483648 3 2147483648 Bool.true 3642754713 3642754713 1073741824000 16237

noncomputable def ep544 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz54 (@HMul.hMul Complex Complex Complex qz52 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz62 qz159 (@HSub.hSub Int Int Int qz64 qz65 (@HMul.hMul Int Int Int qz66 qz67 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false

noncomputable def ep545 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85) qz171 Bool.false 673047 2147483648 3 2147483648 Bool.true 3642754713 1073741824000 16237 1073741824000

noncomputable abbrev qz172 := (Complex.re qz373)

noncomputable abbrev qz173 := (Complex.im qz373)

noncomputable def ep546 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz172) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz173) 673047 2147483648 3 2147483648 0 1 0

noncomputable def ep547 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz172 1 12 0 1 2019141 536870912 9 536870912 673047

noncomputable def ep548 := @Enclosure.Complex.IsNear.re_isNear qz171 Bool.false 2019141 536870912 9 536870912 Bool.true 10928264139 268435456000 48711 268435456000

noncomputable abbrev qz374 := (@HPow.hPow Complex Nat Complex qz423 qz428 1)

noncomputable abbrev qz174 := (@Inv.inv Complex Complex.instInv qz374)

noncomputable def ep549 := @Enclosure.Complex.IsNear.of_eq qz171 qz174 Bool.false 2019141 536870912 9 536870912 Bool.true 10928264139 268435456000 48711

noncomputable def ep550 := @Enclosure.Complex.IsNear.of_parts qz174 Bool.false 2019141 536870912 9 536870912 Bool.true 10928264139 268435456000 48711

noncomputable abbrev qz175 := (Complex.re qz374)

noncomputable abbrev qz176 := qz374

noncomputable def ep551 := @Enclosure.Real.IsNear.mulLit_ff qz175 (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz176)) 9000 4000 0 1 224349 134217728 1 134217728

noncomputable def ep552 := @Enclosure.Complex.IsNear.re_isNear qz176 Bool.false 9000 4000 0 1 Bool.false 97422 4000 0 1

noncomputable def ep553 := @Enclosure.Complex.IsNear.of_eq qz176 qz159 Bool.false 9000 4000 0 1 Bool.false 97422 4000 0

noncomputable def ep554 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz176)) Bool.false 224349 134217728 1 134217728 224349 134217728 1

noncomputable abbrev qz177 := (Complex.im qz374)

noncomputable def ep555 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz176) (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 qz175 qz175) (@HMul.hMul Real Real Real qz0 qz177 qz177)) Bool.false 2393011521 4000000 0 1

noncomputable def ep556 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz175 qz175) (@HMul.hMul Real Real Real qz0 qz177 qz177) 81 16 0 1 2372761521 4000000

noncomputable def ep557 := @Enclosure.Real.IsNear.mulLit_ff qz175 qz175 9000 4000 0 1 9000 4000 0 1

noncomputable def ep558 := @Enclosure.Real.IsNear.mulLit_ff qz177 qz177 97422 4000 0 1 97422 4000 0 1

noncomputable def ep559 := @Enclosure.Complex.IsNear.im_isNear qz176 Bool.false 9000 4000 0 1 Bool.false 97422 4000 0 1

noncomputable abbrev qz178 := (ep552 (@ep553 1 (BSN.pow_one_c qz362) qz372))

noncomputable abbrev qz179 := (ep559 (@ep553 1 (BSN.pow_one_c qz362) qz372))

noncomputable def ep560 := @ep556 0 1 38288184336 2393011521 4000000 0 1 (@ep557 81 16 0 1 qz178 qz178 rfl) (@ep558 2372761521 4000000 0 1 qz179 qz179 rfl)

noncomputable def ep561 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz176) 2393011521 4000000 0 1 112174 112175 67108864 (ep555 (Enclosure.Complex.normSq_eq_mul_add_mul qz176) (ep560 rfl rfl)) rfl

noncomputable def ep562 := @Enclosure.Real.IsNear.of_eq (Complex.re qz174) (@HMul.hMul Real Real Real qz0 qz175 (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz176))) Bool.false 2019141 536870912 9 536870912 (Enclosure.Complex.inv_re_eq_mul qz176) (@ep551 2019141 536870912 9 536870912 qz178 (@ep554 134217728 (ep561 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep563 := @Enclosure.Real.IsNear.of_eq (Complex.im qz174) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz177) (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz176))) Bool.true 10928264139 268435456000 48711 268435456000 (Enclosure.Complex.inv_im_eq_mul qz176)

noncomputable def ep564 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz177) (@Inv.inv Real Real.instInv (@DFunLike.coe qz91 Complex (fun (x : Complex) => Real) qz92 Complex.normSq qz176)) 97422 4000 0 1 224349 134217728 1

noncomputable def ep565 := @ep564 134217728 10928264139 268435456000 48711 268435456000 (@Enclosure.Real.IsNear.neg qz177 Bool.false 97422 4000 0 1 qz179) (@ep554 134217728 (ep561 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep566 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz173 0 1 0 1 10928264139 268435456000 48711 268435456000 0

noncomputable def ep567 := @Enclosure.Complex.IsNear.im_isNear qz171 Bool.false 2019141 536870912 9 536870912 Bool.true 10928264139 268435456000 48711 268435456000

noncomputable abbrev qz180 := (@ep549 268435456000 (BSN.zpow_one_sub_two_mul qz362 1 1 rfl rfl) (@ep550 268435456000 ep562 (ep563 ep565)))

noncomputable def ep568 := @ep546 1 673047 673047 2147483648 3 2147483648 (@ep547 2147483648 3 2147483648 ep227 (ep548 qz180) rfl) (@ep566 1 0 1 ep247 (ep567 qz180) rfl) rfl

noncomputable def ep569 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz173) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz172) 3642754713 1073741824000 16237 1073741824000 0 1 0

noncomputable def ep570 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz173 1 12 0 1 10928264139 268435456000 48711 268435456000 3642754713

noncomputable def ep571 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 (@Rat.cast Complex Complex.instRatCast (bernoulli qz84)) qz85)) qz172 0 1 0 1 2019141 536870912 9 536870912 0

noncomputable def ep572 := @ep569 1 3642754713 3642754713 1073741824000 16237 1073741824000 (@ep570 1073741824000 16237 1073741824000 ep227 (ep567 qz180) rfl) (@ep571 1 0 1 ep247 (ep548 qz180) rfl) rfl

noncomputable def ep573 := @ep543 1073741824000 (@ep544 0 1 0 1 (BSN.stirling_sum_base qz159) qz99) (ep545 (ep568 rfl) (ep572 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep574 := @ep507 1010489790623355647689 18014398509481984000 228208147742898731164543 ep495 (ep540 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep541 Bool.true 3642754713 1073741824000 16237 1073741824000 (BSN.stirling_sum_succ qz159 0 1 rfl) (ep573 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep575 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz146 2) Bool.false 28763952102376623 4503599627370496 500000000288639 32071000000000000000 Bool.false 866958115898787 281474976710656

noncomputable abbrev qz181 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz259 qz363 qz325))

noncomputable def ep576 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz146 1) qz181) Bool.false 28763952102376623 4503599627370496 500000000288639 32071000000000000000 Bool.false 866958115898787 281474976710656 1000000000032071 32071000000000000000

noncomputable def ep577 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz146 1) qz181 Bool.false 28758265565676719 9007199254740992 500000000288639 64142000000000000000 Bool.false 878502987990435 562949953421312 1000000000032071 64142000000000000000 Bool.false

noncomputable def ep578 := nat_lit 518165295879864617417767001260032

noncomputable def ep579 := nat_lit 976108061926901104265121497088

noncomputable abbrev qz182 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz259 qz363 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep580 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz146 0) qz182) Bool.false 28758265565676719 9007199254740992 500000000288639 64142000000000000000 Bool.false 878502987990435 562949953421312 1000000000032071 64142000000000000000

noncomputable def ep581 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz146 0) qz182 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz375 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz167))

noncomputable def ep582 := @Enclosure.Complex.IsNear.of_eq qz182 qz375 Bool.false 28758265565676719 9007199254740992 500000000288639 64142000000000000000 Bool.false 878502987990435 562949953421312 1000000000032071 64142000000000000000

noncomputable def ep583 := nat_lit 1466958442980583504609554002518593409847040

noncomputable def ep584 := nat_lit 2651287225544463318279372210134426585088

noncomputable def ep585 := nat_lit 8569515023181547192269354746649969408

noncomputable def ep586 := BSN.log_dyadic_bound 1300046084 17684046084 3 2 ep583 131072 64142 ep584 ep585 19306 18984092168 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1300046084) (BSN.artanhQ 17684046084) 0 2 ep584 ep583 ep585 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep587 := @Enclosure.Real.IsNear.mulLit_ff qz77 (Real.log (Enclosure.sfrac Bool.false 9492046084 16000000)) 1 2 0 1 28758265565676719 4503599627370496 500000000288639 32071000000000000000 28758265565676719 9007199254740992 500000000288639 64142000000000000000 qz319 (BSN.isNear_log_sfrac 9492046084 16000000 28758265565676719 4503599627370496 500000000288639 32071000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9492046084) qz320)) Bool.false 30155227073795031302144 4722366482869645213696 1000000000577278 64142000000000000000 28758265565676719 4503599627370496 500000000288639 32071000000000000000 (BSN.log_rat_reduce_isNear 9492046084 16000000 9 18984092168 16384000000 19306 131072 24973259072661432 36028797018963968 64142 1000000000000000 rfl rfl rfl rfl (ep586 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep588 := BSN.arctan_dyadic_bound_f 1000 97422 1 0 131072 64142 0 1 1 0 1 1 1345 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 97422) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 97422) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz376 := (@Nat.cast Real Real.instNatCast 97422)

noncomputable def ep589 := @Enclosure.Real.IsNear.subLit_ff_p qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz376)) 884279719003555 562949953421312 1 2000000000000000 1345 131072 1 64142 115147143641882296320 878502987990435 562949953421312 1000000000032071 64142000000000000000 qz79 (ep588 rfl) rfl rfl

noncomputable abbrev qz183 := (@HAdd.hAdd Complex Complex Complex qz259 qz363 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz377 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz167)

noncomputable def ep590 := @ep581 28758265565676719 9007199254740992 500000000288639 64142000000000000000 Bool.false 878502987990435 562949953421312 1000000000032071 64142000000000000000 Bool.false 28758265565676719 28758265565676719 9007199254740992 500000000288639 64142000000000000000 Bool.false 878502987990435 878502987990435 562949953421312 1000000000032071 64142000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 0) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz146) qz99) (ep582 (@congrArg Complex Complex qz183 qz377 Complex.log (BSN.w_shift_mk qz146 Bool.false 48711 1000 0 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz375 Bool.false 28758265565676719 9007199254740992 500000000288639 64142000000000000000 Bool.false 878502987990435 562949953421312 1000000000032071 64142000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz375) (@HMul.hMul Real Real Real qz0 qz77 (Real.log (Enclosure.sfrac Bool.false 9492046084 16000000))) Bool.false 28758265565676719 9007199254740992 500000000288639 64142000000000000000 (Enclosure.clog_re_eq 1000 97422 4000 9492046084 16000000 rfl rfl rfl) (ep587 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz375) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz376 qz330)) Bool.false 878502987990435 562949953421312 1000000000032071 64142000000000000000 (Enclosure.clog_im_eq 1000 97422 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz376 qz330)) (@HSub.hSub Real Real Real qz53 qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz330 qz376))) Bool.false 878502987990435 562949953421312 1000000000032071 64142000000000000000 (BSN.arctan_recip 97422 1000 rfl rfl) ep589)))) rfl rfl

noncomputable abbrev qz378 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz167))

noncomputable def ep591 := @Enclosure.Complex.IsNear.of_eq qz181 qz378 Bool.false 28769638639076527 9007199254740992 500000000288639 64142000000000000000 Bool.false 855413243807139 562949953421312 1000000000032071 64142000000000000000

noncomputable def ep592 := nat_lit 1474938232084818338025987315940407169847040

noncomputable def ep593 := nat_lit 2757857725308692658575653032435098585088

noncomputable def ep594 := nat_lit 9220058135252367270848583109401969408

noncomputable def ep595 := BSN.log_dyadic_bound 1324046084 17708046084 3 2 ep592 131072 64142 ep593 ep594 19637 19032092168 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1324046084) (BSN.artanhQ 17708046084) 0 2 ep593 ep592 ep594 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep596 := @Enclosure.Real.IsNear.mulLit_ff qz77 (Real.log (Enclosure.sfrac Bool.false 9516046084 16000000)) 1 2 0 1 28769638639076527 4503599627370496 500000000288639 32071000000000000000 28769638639076527 9007199254740992 500000000288639 64142000000000000000 qz319 (BSN.isNear_log_sfrac 9516046084 16000000 28769638639076527 4503599627370496 500000000288639 32071000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9516046084) qz320)) Bool.false 30167152605608308375552 4722366482869645213696 1000000000577278 64142000000000000000 28769638639076527 4503599627370496 500000000288639 32071000000000000000 (BSN.log_rat_reduce_isNear 9516046084 16000000 9 19032092168 16384000000 19637 131072 24973259072661432 36028797018963968 64142 1000000000000000 rfl rfl rfl rfl (ep595 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep597 := BSN.arctan_dyadic_bound_f 5000 97422 1 0 131072 64142 0 1 1 0 1 1 6721 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 97422) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 97422) 0 0 rfl) rfl rfl rfl

noncomputable def ep598 := @Enclosure.Real.IsNear.subLit_ff_p qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz334 qz376)) 884279719003555 562949953421312 1 2000000000000000 6721 131072 1 64142 112120724692289323008 855413243807139 562949953421312 1000000000032071 64142000000000000000 qz79 (ep597 rfl) rfl rfl

noncomputable abbrev qz184 := (@HAdd.hAdd Complex Complex Complex qz259 qz363 qz325)

noncomputable abbrev qz379 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz167)

noncomputable def ep599 := @ep577 28769638639076527 9007199254740992 500000000288639 64142000000000000000 Bool.false 855413243807139 562949953421312 1000000000032071 64142000000000000000 Bool.false ep578 28763952102376623 4503599627370496 500000000288639 32071000000000000000 Bool.false ep579 866958115898787 281474976710656 1000000000032071 32071000000000000000 (ep580 (BSN.log_sum_c_succ qz146 0 1 rfl) (ep590 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep591 (@congrArg Complex Complex qz184 qz379 Complex.log (BSN.w_shift_mk qz146 Bool.false 48711 1000 1 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz378 Bool.false 28769638639076527 9007199254740992 500000000288639 64142000000000000000 Bool.false 855413243807139 562949953421312 1000000000032071 64142000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz378) (@HMul.hMul Real Real Real qz0 qz77 (Real.log (Enclosure.sfrac Bool.false 9516046084 16000000))) Bool.false 28769638639076527 9007199254740992 500000000288639 64142000000000000000 (Enclosure.clog_re_eq 5000 97422 4000 9516046084 16000000 rfl rfl rfl) (ep596 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz378) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz376 qz334)) Bool.false 855413243807139 562949953421312 1000000000032071 64142000000000000000 (Enclosure.clog_im_eq 5000 97422 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz376 qz334)) (@HSub.hSub Real Real Real qz53 qz78 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz334 qz376))) Bool.false 855413243807139 562949953421312 1000000000032071 64142000000000000000 (BSN.arctan_recip 97422 5000 rfl rfl) ep598)))) rfl rfl

noncomputable def ep600 := @ep500 ep495 Bool.false 28763952102376623 4503599627370496 500000000288639 32071000000000000000 Bool.false 866958115898787 281474976710656 1000000000032071 32071000000000000000 Bool.true ep501 171753080595167605319 4503599627370496000 111449370031100919683213 ep168 Bool.false ep502 955004471205833279689 18014398509481984000 260976147743949633692543 ep495 (@ep503 4503599627370496000 107353370028736388995213 ep168 Bool.false 1010489790623355647689 18014398509481984000 228208147742898731164543 ep495 (BSN.logGammaStirling_unfold 1 qz159) (ep574 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep575 1000000000032071 32071000000000000000 (BSN.log_sum_c_eq qz146 2) (ep576 (BSN.log_sum_c_succ qz146 1 2 rfl) (ep599 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz185 := (@HDiv.hDiv Real Real Real qz256 qz351 (2 : Real))

noncomputable def ep601 := @Enclosure.Real.IsNear.mulLit_ff qz185 (Real.log Real.pi) 48711 2000 0 1 75021 65536 1 32768 3654347931 131072000 48711 65536000 (@Enclosure.Real.IsNear.of_eq qz185 (Enclosure.sfrac Bool.false 48711 2000) Bool.false 48711 2000 0 1 (BSN.t_half_eq qz146 Bool.false 48711 1000 qz147) (Enclosure.Real.IsNear.const Bool.false 48711 2000)) EMRow09.d5 rfl

noncomputable def ep602 := @ep497 48711 65536000 ep498 452754715946624813257 18014398509481984000 1042081388243949633692543 ep495 (@ep499 260976147743949633692543 ep495 (ep600 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep601 rfl rfl

noncomputable def ep603 := BSN.cos_dyadic_bound_f 51899 268435456 1 0 131072 64205 0 1 1 0 1 1 131071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 51899) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 51899) qz269 0 0 rfl) rfl rfl

noncomputable def ep604 := @ep494 131072 Bool.false 131071 131072 1 32071 (@ep496 205889 8192 131 131072 ep602 rfl) (Enclosure.sfrac_false_div 205889 8192) (BSN.cos_reduce0 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 228257465995624448) qz360) 226375608064910080 72057594037927936 Bool.false 131071 131072 4 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 205889 8192 226375608064910080 72057594037927936 4 228257465995624448 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 131071 131072 228257465995624448 1180591620717411303424 51899 268435456 64205 64142 (ep603 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep605 := nat_lit 322137989827302173756975047

noncomputable abbrev qz186 := qz350

noncomputable abbrev qz380 := (@HPow.hPow Complex Complex Complex qz411 qz424 qz426)

noncomputable abbrev qz187 := qz380

noncomputable abbrev qz188 := (@HAdd.hAdd Complex Complex Complex qz259 (@HDiv.hDiv Complex Complex Complex qz310 qz337 (@HSub.hSub Complex Complex Complex qz303 qz349 (1 : Complex))) qz309)

noncomputable def ep606 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz141 1 10) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 10, @HPow.hPow Complex Complex Complex qz105 (@Nat.cast Complex Complex.instNatCast n) qz186) (@HMul.hMul Complex Complex Complex qz52 qz187 (@HAdd.hAdd Complex Complex Complex qz5 qz188 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) Bool.false ep489 ep490 ep491

noncomputable def ep607 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 10, @HPow.hPow Complex Complex Complex qz105 (@Nat.cast Complex Complex.instNatCast n) qz186) (@HMul.hMul Complex Complex Complex qz52 qz187 (@HAdd.hAdd Complex Complex Complex qz5 qz188 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) Bool.false 12044460345 17179869184 246920365789 42382737276928

noncomputable def ep608 := nat_lit 18279500918590748820436367

noncomputable def ep609 := nat_lit 18305155244566214796775047

noncomputable def ep610 := nat_lit 62531068073240761860065514859003904

noncomputable def ep611 := nat_lit 7610881101150193390483466893656064

noncomputable def ep612 := @ep607 Bool.true 4399005875 17179869184 246224642185 42382737276928 Bool.false 209990027414629819062581 ep490 ep608 ep492 Bool.false 809655408290134413015179 ep490 ep609 ep492 Bool.false ep610 ep489 ep490 ep491 ep492 Bool.true ep611 443011586388467891984821 ep490

noncomputable def ep613 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 10, @HPow.hPow Complex Complex Complex qz105 (@Nat.cast Complex Complex.instNatCast n) qz186) (BSN.headSumC qz141 10) Bool.false 12044460345 17179869184 246920365789 42382737276928 Bool.true 4399005875 17179869184 246224642185

noncomputable abbrev qz189 := (@HPow.hPow Complex Complex Complex qz260 (@Nat.cast Complex Complex.instNatCast 9) qz350)

noncomputable def ep614 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 10) (@HAdd.hAdd Complex Complex Complex qz5 qz132 qz189) Bool.false 12044460345 17179869184 246920365789 42382737276928 Bool.true 4399005875 17179869184 246224642185 42382737276928

noncomputable def ep615 := @Enclosure.Complex.IsNear.addLitP qz132 qz189 Bool.false 6449478267 17179869184 2919881782915 550975584600064 Bool.true 3178191953 17179869184 2914048196299 550975584600064 Bool.false

noncomputable abbrev qz190 := (@HMul.hMul Real Real Real qz253 qz351 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep616 := @Enclosure.Complex.IsNear.of_eq qz189 (Complex.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz190)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz190)))) Bool.false 2797491039 8589934592 145041486171 275487792300032 Bool.true 610406961 8589934592 143436076053 275487792300032 (BSN.cpow_neg_s_mk qz146 48711 1000 9 qz147 rfl)

noncomputable def ep617 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz115 48711 1000 0 1 9895417793173221 4503599627370496 1000000000096213 32071000000000000000 482015696123260768131 4503599627370496000 3747000000360510111 2467000000000000000000 qz148 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000096213 32071000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 5188048803947201691648 2361183241434822606848 1000000000096213 32071000000000000000 9895417793173221 4503599627370496 1000000000096213 32071000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 7719 65536 24973259072661432 36028797018963968 32071 1000000000000000 rfl rfl rfl rfl (ep297 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep618 := nat_lit 11060386800236429903174696630481

noncomputable def ep619 := BSN.cos_dyadic_bound_f 57669021 268435456 2 1 131072 64205 ep618 ep57 ep618 ep618 ep58 ep618 128058 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 57669021) qz268 0 1 ep618 ep57 ep618 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 57669021) qz269 0 1 ep618 ep58 ep618 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz381 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14028503) qz27)

noncomputable def ep620 := @Enclosure.Real.IsNear.cos_image qz190 qz381 Bool.false 14028503 131072 25 16384 Bool.false 128058 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz190 Bool.false 482015696123260768131 4503599627370496000 3747000000360510111 2467000000000000000000 14028503 131072 25 16384 (ep617 rfl) rfl) (Enclosure.sfrac_false_div 14028503 131072) (BSN.cos_reduce0 qz381 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4058096648403535527936) qz30) 226375608064910080 72057594037927936 Bool.false 128058 131072 17 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 14028503 131072 226375608064910080 72057594037927936 17 4058096648403535527936 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 128058 131072 4058096648403535527936 18889465931478580854784 57669021 268435456 64205 64142 (ep619 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep621 := BSN.sin_dyadic_bound_f 57669021 268435456 1 0 131072 64205 0 1 1 0 1 1 27942 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 57669021) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 57669021) qz275 0 0 rfl) rfl rfl

noncomputable def ep622 := @Enclosure.Real.IsNear.sin_image qz190 qz381 Bool.false 14028503 131072 25 16384 Bool.false 27942 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz190 Bool.false 482015696123260768131 4503599627370496000 3747000000360510111 2467000000000000000000 14028503 131072 25 16384 (ep617 rfl) rfl) (Enclosure.sfrac_false_div 14028503 131072) (BSN.sin_reduce0 qz381 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4058096648403535527936) qz30) 226375608064910080 72057594037927936 Bool.false 27942 131072 17 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 14028503 131072 226375608064910080 72057594037927936 17 4058096648403535527936 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 27942 131072 4058096648403535527936 18889465931478580854784 57669021 268435456 64205 64142 (ep621 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep623 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz190)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz190))) Bool.false 2797491039 8589934592 145041486171 275487792300032 Bool.true 610406961 8589934592 143436076053 275487792300032 (@Enclosure.Real.IsNear.mulLit_ff qz113 (Real.cos qz190) 43691 131072 1 131072 64029 65536 818159 525451264 2797491039 8589934592 145041486171 275487792300032 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz190) Bool.false 128058 131072 818159 525451264 64029 65536 818159 525451264 (ep620 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz113 (@Neg.neg Real Real.instNeg (Real.sin qz190)) 43691 131072 1 131072 13971 65536 818159 525451264 610406961 8589934592 143436076053 275487792300032 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz190) Bool.false 13971 65536 818159 525451264 (@Enclosure.Real.IsNear.recentre' (Real.sin qz190) Bool.false 27942 131072 818159 525451264 13971 65536 818159 525451264 (ep622 rfl rfl) rfl)) rfl)

noncomputable def ep624 := @ep615 2797491039 8589934592 145041486171 275487792300032 Bool.true 610406961 8589934592 143436076053 275487792300032 Bool.false 103461126559487754240 12044460345 17179869184 246920365789 42382737276928 Bool.true 37787172736073728000 4399005875 17179869184 246224642185 42382737276928 EMRow09.d10 (ep616 ep623) rfl rfl

noncomputable def ep625 := @Enclosure.Complex.IsNear.mul qz187 (@HAdd.hAdd Complex Complex Complex qz5 qz188 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))) Bool.false 209990027414629819062581 ep490 ep608 ep492 Bool.false

noncomputable abbrev qz191 := (Complex.re qz380)

noncomputable abbrev qz192 := (Complex.im qz380)

noncomputable def ep626 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz191 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz188 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz192 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz188 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) 920177428094422560169 9784326600697168527360 26095473543804532813117

noncomputable def ep627 := nat_lit 104597712803652963946987520

noncomputable def ep628 := nat_lit 1630721100116194754560000

noncomputable def ep629 := nat_lit 4022988953986652459499520000

noncomputable def ep630 := nat_lit 684870337038030068660047280676667617150238720

noncomputable def ep631 := @Enclosure.Real.IsNear.mulLit_ff qz191 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz188 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 3218141809 17179869184 273791548911 550975584600064 285934394041

noncomputable abbrev qz382 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz427 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable abbrev qz193 := (Real.cos qz382)

noncomputable abbrev qz194 := (@Neg.neg Real Real.instNeg (Real.sin qz382))

noncomputable def ep632 := @Enclosure.Complex.IsNear.of_eq qz187 (Complex.mk (@HMul.hMul Real Real Real qz0 qz118 qz193) (@HMul.hMul Real Real Real qz0 qz118 qz194)) Bool.false 3218141809 17179869184 273791548911 550975584600064 Bool.false 4377055849 17179869184 274688254071 550975584600064 (BSN.cpow_neg_s_mk qz146 48711 1000 10 qz147 rfl)

noncomputable def ep633 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz122 48711 1000 0 1 10369857060558565 4503599627370496 1000000000096213 32071000000000000000 101025221455373651943 900719925474099200 3747000000360510111 2467000000000000000000 qz148 (BSN.isNear_log_sfrac 10 1 10369857060558565 4503599627370496 1000000000096213 32071000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz121) Bool.false 5436791618566128926720 2361183241434822606848 1000000000096213 32071000000000000000 10369857060558565 4503599627370496 1000000000096213 32071000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 14623 65536 24973259072661432 36028797018963968 32071 1000000000000000 rfl rfl rfl rfl (ep317 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep634 := nat_lit 838823660807216565865987857450625

noncomputable def ep635 := BSN.sin_dyadic_bound_f 170183585 268435456 2 1 131072 64205 ep634 ep91 ep634 ep634 ep92 ep634 77641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 170183585) qz274 0 1 ep634 ep91 ep634 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 170183585) qz275 0 1 ep634 ep92 ep634 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz195 := qz382

noncomputable abbrev qz383 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 918819) (@Nat.cast Real Real.instNatCast 8192))

noncomputable def ep636 := @Enclosure.Real.IsNear.cos_image qz195 qz383 Bool.false 918819 8192 25 16384 Bool.false 77641 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz195 Bool.false 101025221455373651943 900719925474099200 3747000000360510111 2467000000000000000000 918819 8192 25 16384 (ep633 rfl) rfl) (Enclosure.sfrac_false_div 918819 8192) (BSN.cos_reduce3 qz383 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 748475322660036804608) qz360) 226375608064910080 72057594037927936 Bool.false 77641 131072 17 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q3 918819 8192 226375608064910080 72057594037927936 17 748475322660036804608 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 77641 131072 748475322660036804608 1180591620717411303424 170183585 268435456 64205 64142 (ep635 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep637 := BSN.cos_dyadic_bound_f 170183585 268435456 2 1 131072 64205 ep634 ep57 ep634 ep634 ep58 ep634 105601 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 170183585) qz268 0 1 ep634 ep57 ep634 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 170183585) qz269 0 1 ep634 ep58 ep634 rfl rfl rfl rfl) rfl rfl

noncomputable def ep638 := @Enclosure.Real.IsNear.sin_image qz195 qz383 Bool.false 918819 8192 25 16384 Bool.true 105601 131072 1 32071 (@Enclosure.Real.IsNear.recentre' qz195 Bool.false 101025221455373651943 900719925474099200 3747000000360510111 2467000000000000000000 918819 8192 25 16384 (ep633 rfl) rfl) (Enclosure.sfrac_false_div 918819 8192) (BSN.sin_reduce3 qz383 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 748475322660036804608) qz360) 226375608064910080 72057594037927936 Bool.false 105601 131072 17 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q3 918819 8192 226375608064910080 72057594037927936 17 748475322660036804608 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 105601 131072 748475322660036804608 1180591620717411303424 170183585 268435456 64205 64142 (ep637 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz196 := (Real.sin qz382)

noncomputable def ep639 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz118 qz193) (@HMul.hMul Real Real Real qz0 qz118 qz194) Bool.false 3218141809 17179869184 273791548911 550975584600064 Bool.false 4377055849 17179869184 274688254071 550975584600064 (@Enclosure.Real.IsNear.mulLit_ff qz118 qz193 41449 131072 1 131072 77641 131072 818159 525451264 3218141809 17179869184 273791548911 550975584600064 qz346 (@Enclosure.Real.IsNear.recentre' qz193 Bool.false 77641 131072 818159 525451264 77641 131072 818159 525451264 (ep636 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz118 qz194 41449 131072 1 131072 105601 131072 818159 525451264 4377055849 17179869184 274688254071 550975584600064 qz346 (@Enclosure.Real.IsNear.neg qz196 Bool.true 105601 131072 818159 525451264 (@Enclosure.Real.IsNear.recentre' qz196 Bool.true 105601 131072 818159 525451264 105601 131072 818159 525451264 (ep638 rfl rfl) rfl)) rfl)

noncomputable def ep640 := @ep631 569522765040 0 1 920177428094422560169 9784326600697168527360 26095473543804532813117 ep627 (@Enclosure.Complex.IsNear.re_isNear qz187 Bool.false 3218141809 17179869184 273791548911 550975584600064 Bool.false 4377055849 17179869184 274688254071 550975584600064 (ep632 ep639))

noncomputable def ep641 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz188 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))) Bool.false 285934394041 569522765040 0 1 Bool.false

noncomputable def ep642 := @Enclosure.Complex.IsNear.addLitP qz188 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) Bool.false 2363011521 4746023042 0 1 Bool.true 487110000

noncomputable def ep643 := @ep642 2373011521 0 1 Bool.false 1 240 0 1 Bool.false 16237 40000 0 1 Bool.false 571868788082 285934394041 569522765040 0 1 Bool.false 19046188066477 19046188066477 94920460840000 0 1

noncomputable abbrev qz197 := (@HDiv.hDiv Complex Complex Complex qz310 qz337 (@HSub.hSub Complex Complex Complex qz303 qz349 (1 : Complex)))

noncomputable def ep644 := @Enclosure.Complex.IsNear.addLitP qz197 qz82 Bool.true 20000000 9492046084 0 1 Bool.true 1948440000 9492046084 0 1

noncomputable def ep645 := @Enclosure.Complex.IsNear.of_eq qz197 (Complex.mk (Enclosure.sfrac Bool.true 20000000 9492046084) (Enclosure.sfrac Bool.true 1948440000 9492046084)) Bool.true 20000000 9492046084 0 1 Bool.true 1948440000 9492046084 0 1

noncomputable def ep646 := @ep644 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 9452046084 2363011521 4746023042 0 1 Bool.true 1948440000 487110000 2373011521 0 1 (ep645 (BSN.N_div_s_sub_one_mk qz146 48711 1000 10 qz147 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 20000000 9492046084) (Enclosure.sfrac Bool.true 1948440000 9492046084) Bool.true 20000000 9492046084 0 1 Bool.true 1948440000 9492046084 0 1 (Enclosure.Real.IsNear.const Bool.true 20000000 9492046084) (Enclosure.Real.IsNear.const Bool.true 1948440000 9492046084))) qz83 rfl

noncomputable def ep647 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz127)) Bool.false 1 240 0 1

noncomputable def ep648 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz127) Bool.false 0 1 0 1 Bool.false

noncomputable def ep649 := @ep648 0 1 0 1 Bool.false 1 240 0 1 Bool.false 16237 40000 0 1 Bool.false 1 1 240 0 1 Bool.false 16237 16237 40000 0

noncomputable def ep650 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (Complex.mk qz20 qz20) Bool.false 0 1 0 1 Bool.false

noncomputable def ep651 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz127 Bool.false 1 240 0 1 Bool.false 16237 40000 0 1

noncomputable def ep652 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz128) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129) 1 240 0 1 0 1 0

noncomputable def ep653 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz128 1 24 0 1 1 10 0 1 1

noncomputable def ep654 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep655 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep656 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) qz141 Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 (BSN.ascPochhammer_one_eval qz141)

noncomputable def ep657 := ep656 (@Enclosure.Complex.IsNear.of_eq qz141 (Complex.mk qz77 qz146) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 (BSN.s_crit_mk qz146 Bool.false 48711 1000 qz147) (@Enclosure.Complex.IsNear.mk qz77 qz146 Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 qz319 qz148))

noncomputable def ep658 := @ep655 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep345) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep657)

noncomputable def ep659 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 48711 1000 0 1 0 1 0

noncomputable def ep660 := @ep659 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep345) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep657)

noncomputable def ep661 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) 16237 4000 0 1 0 1 0 1 16237

noncomputable def ep662 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 48711 1000 0 1 16237 4000 0

noncomputable def ep663 := @ep662 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep345) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep657)

noncomputable def ep664 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep665 := @ep664 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep345) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep657)

noncomputable def ep666 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 16237 4000 0 1 (@ep654 1 24 0 1 (ep658 rfl) (ep660 rfl) rfl rfl) (@ep661 16237 4000 0 1 (ep663 rfl) (ep665 rfl) rfl rfl)

noncomputable def ep667 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 16237 4000 0 1 ep666

noncomputable def ep668 := @ep653 240 0 1 ep667 qz130

noncomputable def ep669 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129 16237 4000 0 1 0 1 0 1 0

noncomputable def ep670 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 16237 4000 0 1 ep666

noncomputable def ep671 := @ep669 1 0 1 ep670 qz131

noncomputable def ep672 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz128) 0 1 0 1 16237 40000 0

noncomputable def ep673 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz129 1 24 0 1 0 1 0 1 0

noncomputable def ep674 := @ep673 1 0 1 ep667 qz131

noncomputable def ep675 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz84)) ↑qz126) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz128 16237 4000 0 1 1 10 0 1 16237

noncomputable def ep676 := @ep675 40000 0 1 ep670 qz130

noncomputable def ep677 := @ep649 1 (@ep650 0 1 0 1 (BSN.bern_sum_base qz141 10) qz99) (ep651 (@ep652 1 1 1 240 0 1 (ep668 rfl) (ep671 rfl) rfl rfl) (@ep672 1 16237 16237 40000 0 1 (ep674 rfl) (ep676 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep678 := ep643 (ep646 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep647 Bool.false 16237 40000 0 1 (BSN.bern_sum_succ qz141 10 0 1 1 rfl rfl) (ep677 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep679 := @Enclosure.Real.IsNear.mulLit_ff qz192 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz188 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 4377055849 17179869184 274688254071 550975584600064 19046188066477

noncomputable def ep680 := @ep679 94920460840000 0 1 83366228877527153673973 ep628 402443395899114031836759 ep629 (@Enclosure.Complex.IsNear.im_isNear qz187 Bool.false 3218141809 17179869184 273791548911 550975584600064 Bool.false 4377055849 17179869184 274688254071 550975584600064 (ep632 ep639))

noncomputable def ep681 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz188 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))) Bool.false 285934394041 569522765040 0 1 Bool.false

noncomputable def ep682 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz191 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz188 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz192 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz188 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1))))))) 61293334118806505036893 ep628 401129640890072466535119

noncomputable def ep683 := nat_lit 2640644316243829641168831545933216786918932480

noncomputable def ep684 := @Enclosure.Real.IsNear.mulLit_ff qz191 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz188 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 3218141809 17179869184 273791548911 550975584600064 19046188066477

noncomputable def ep685 := @ep684 94920460840000 0 1 61293334118806505036893 ep628 401129640890072466535119 ep629 (@Enclosure.Complex.IsNear.re_isNear qz187 Bool.false 3218141809 17179869184 273791548911 550975584600064 Bool.false 4377055849 17179869184 274688254071 550975584600064 (ep632 ep639))

noncomputable def ep686 := @Enclosure.Real.IsNear.mulLit_ff qz192 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz188 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz61 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz61 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz110 qz111 (@HSub.hSub Nat Nat Nat qz109 (@HMul.hMul Nat Nat Nat qz61 2 k) 1)))))) 4377055849 17179869184 274688254071 550975584600064 285934394041

noncomputable def ep687 := @ep686 569522765040 0 1 1251550811867429795809 9784326600697168527360 26180939825990545463637 ep627 (@Enclosure.Complex.IsNear.im_isNear qz187 Bool.false 3218141809 17179869184 273791548911 550975584600064 Bool.false 4377055849 17179869184 274688254071 550975584600064 (ep632 ep639))

noncomputable abbrev qz384 := (ep678 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep688 := @ep625 809655408290134413015179 ep490 ep609 ep492 (@ep626 ep627 83366228877527153673973 ep628 402443395899114031836759 ep629 ep630 209990027414629819062581 ep490 ep608 ep492 (ep640 (@ep641 19046188066477 94920460840000 0 1 qz384) rfl) (ep680 (@ep681 19046188066477 94920460840000 0 1 qz384) rfl) rfl rfl) (@ep682 ep629 1251550811867429795809 9784326600697168527360 26180939825990545463637 ep627 ep683 809655408290134413015179 ep490 ep609 ep492 (ep685 (@ep681 19046188066477 94920460840000 0 1 qz384) rfl) (ep687 (@ep641 19046188066477 94920460840000 0 1 qz384) rfl) rfl rfl)

noncomputable def ep689 := @ep612 ep605 ep492 (@ep613 42382737276928 (BSN.head_sum_c_eq qz141 10) (ep614 (BSN.head_sum_c_succ qz141 9 10 rfl rfl) (ep624 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep688 rfl rfl rfl

noncomputable def ep690 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz141 1 10) Bool.false ep489 ep490 ep491 ep492 Bool.true 443011586388467891984821 ep490 ep605 ep492 (@ep606 ep492 Bool.true 443011586388467891984821 ep490 ep605 ep492 (BSN.zetaApproximant_eq_folded' qz141 1 10 rfl) (ep689 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep691 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))))) qz157)) (Complex.im (zetaApproximant qz141 1 10)) 25 131072 4332373

noncomputable def ep692 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))))) qz157)) Bool.false 25 131072 4332373

noncomputable def ep693 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))))) qz157) qz364 Bool.false 205889 8192 131

noncomputable def ep694 := BSN.sin_dyadic_bound_f 51899 268435456 1 0 131072 64205 0 1 1 0 1 1 25 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 51899) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 51899) qz275 0 0 rfl) rfl rfl

noncomputable def ep695 := @ep693 131072 Bool.false 25 131072 1 32071 (@ep496 205889 8192 131 131072 ep602 rfl) (Enclosure.sfrac_false_div 205889 8192) (BSN.sin_reduce0 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 228257465995624448) qz360) 226375608064910080 72057594037927936 Bool.false 25 131072 4 1000000000000000 64142 32071 (BSN.sin_reduce_arg_pos_rat_q0 205889 8192 226375608064910080 72057594037927936 4 228257465995624448 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 25 131072 228257465995624448 1180591620717411303424 51899 268435456 64205 64142 (ep694 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep696 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz141 1 10) Bool.false ep489 ep490 ep491 ep492 Bool.true 443011586388467891984821 ep490 ep605 ep492 (@ep606 ep492 Bool.true 443011586388467891984821 ep490 ep605 ep492 (BSN.zetaApproximant_eq_folded' qz141 1 10 rfl) (ep689 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow09.d11 : Enclosure.Real.IsNear (hardyZApproximantEM 1 10 qz146) Bool.false ep474 ep475 ep476 ep477 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 10 qz146) ep478 Bool.false ep474 ep475 ep476 ep477 (@Eq.refl Real ep478) (@ep479 Bool.false ep474 ep475 ep476 ep477 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz53 (Complex.im (@HSub.hSub Complex Complex Complex qz54 qz155 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz156 (@Nat.cast Complex Complex.instNatCast j))))) qz157) (zetaApproximant qz141 1 10)) (@ep481 ep482 ep483 ep484 443011586388467891984821 ep485 ep486 ep484 ep487 ep474 ep475 ep476 ep477 (@ep488 4203610112 ep489 ep490 ep491 ep492 ep480 ep482 ep483 ep484 (@ep493 4203610112 131071 131072 4332373 4203610112 (ep604 rfl rfl) rfl) ep690 rfl) (@ep691 4203610112 443011586388467891984821 ep490 ep605 ep492 443011586388467891984821 ep485 ep486 ep484 (@ep692 4203610112 25 131072 4332373 4203610112 (ep695 rfl rfl) rfl) ep696 rfl) rfl rfl))

theorem EMRow09.d12 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow09.d13 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow09.d14 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow09.d15 : @Eq Nat (Nat.pow 10 (Nat.succ (Nat.mul 2 3))) 10000000 := @Eq.refl Nat 10000000

noncomputable abbrev qz430 := (@HAdd.hAdd Complex Complex Complex qz433 qz432 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz385 := qz430

noncomputable abbrev qz198 := (@HDiv.hDiv Real Real Real qz256 (@Norm.norm Complex Complex.instNorm qz385) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz258) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz199 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz200 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz386 := (@HPow.hPow Complex Complex Complex qz411 qz424 (@HSub.hSub Complex Complex Complex qz417 qz412 qz413))

noncomputable abbrev qz201 := qz386

noncomputable def ep697 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 qz198 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) 60304317 1073741824 335369 3221225472 536893638548165 985162418487296 1006591735

noncomputable def ep698 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 10)) 123 8192 1 221184 490279 131072 761 131072 60304317 1073741824

noncomputable abbrev qz387 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz202 := (@HPow.hPow Real Nat Real qz387 qz257 2)

noncomputable def ep699 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz202) 96 162 0 1 3321 131072 1 131072 123 8192 1 221184

noncomputable def ep700 := nat_lit 781950621441006189802102638025

noncomputable def ep701 := nat_lit 19807040628566084398385987584

noncomputable def ep702 := nat_lit 26986075409044041160201671

noncomputable def ep703 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz203 := qz257

noncomputable abbrev qz388 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz203 1)

noncomputable def ep704 := @Enclosure.Real.IsNear.mulLit_ff qz388 qz203 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep700 ep701 ep702 ep703

noncomputable def ep705 := ep704 (@Enclosure.Real.IsNear.of_eq qz388 qz203 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz203) (@Enclosure.Real.IsNear.of_eq qz203 qz254 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz255)) (@Enclosure.Real.IsNear.of_eq qz203 qz254 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz255) rfl

noncomputable def ep706 := @Enclosure.Real.IsNear.inv_image qz202 ep700 ep701 ep702 ep703 1660 1661 65536 (@Enclosure.Real.IsNear.of_eq qz202 (@HMul.hMul Real Real Real qz0 qz388 qz203) Bool.false ep700 ep701 ep702 ep703 (BSN.pow_succ_r qz203 1 2 rfl) ep705) rfl rfl rfl

noncomputable def ep707 := ep699 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz202) Bool.false 3321 131072 1 131072 3321 131072 1 131072 (ep706 rfl rfl rfl) rfl)

noncomputable def ep708 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 10)) (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz21 1 10)) (Complex.re (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz21 1 10)) (Complex.im (zetaApproximant qz21 1 10))))) Bool.false 490279 131072 761 131072

noncomputable def ep709 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz21 1 10)) (Complex.re (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz21 1 10)) (Complex.im (zetaApproximant qz21 1 10))))) Bool.false 490279 131072 761 131072

noncomputable def ep710 := nat_lit 247256532675922957878789859313309082937

noncomputable def ep711 := nat_lit 17671798861332905811532554908467200000

noncomputable def ep712 := nat_lit 2731720638004955847651068511624395305146541710829675807

noncomputable def ep713 := nat_lit 62980061427461013479902382079472590973636819550208000000

noncomputable def ep714 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz21 1 10)) (Complex.re (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz21 1 10)) (Complex.im (zetaApproximant qz21 1 10)))) ep710 ep711 ep712 ep713 244759 245520

noncomputable def ep715 := nat_lit 2570192919857684176615713298698473571014743232569

noncomputable def ep716 := nat_lit 183695844097707967664817594476195494232064000000

noncomputable def ep717 := nat_lit 1022401122896319152627281291529229908615180368899969379

noncomputable def ep718 := nat_lit 23617523035297880054963393279802221615113807331328000000

noncomputable def ep719 := nat_lit 102429409597085428143916857427444064445361

noncomputable def ep720 := nat_lit 5102662336047443546244933179894319284224000000

noncomputable def ep721 := nat_lit 15952930844314321934955202639346646518182181289272389

noncomputable def ep722 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz21 1 10)) (Complex.re (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz21 1 10)) (Complex.im (zetaApproximant qz21 1 10))) ep715 ep716 ep717 ep718 ep719 ep720 ep721

noncomputable def ep723 := nat_lit 188940184282383040439707146238417772920910458650624000000

noncomputable def ep724 := nat_lit 13114845424390466961328943909072958715051980619613094012238115772388657310850030826946560000000

noncomputable def ep725 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz21 1 10)) (Complex.re (zetaApproximant qz21 1 10)) ep159 428597531604777172992000 ep160 ep161 ep159 428597531604777172992000 ep160 ep161 ep715

noncomputable def ep726 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz21 1 10)) (Complex.im (zetaApproximant qz21 1 10)) 320045949196494952519 71432921934129528832000 ep283 ep284 320045949196494952519 71432921934129528832000 ep283 ep284 ep719

noncomputable def ep727 := @ep697 985162418487296 635894701529647957409792 592223090612933 985162418487296 310722174181 2955487255461888 (@ep698 335369 3221225472 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz202)) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow09.d12 EMRow09.d13 rfl) (ep707 rfl)) (ep708 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz21 1 10)) (@ep709 490279 131072 761 131072 (@ep714 65536 (@ep722 ep723 ep724 ep710 ep711 ep712 ep713 (@ep725 ep716 ep717 ep718 ep380 ep380 rfl) (@ep726 ep720 ep721 ep723 ep388 ep388 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz204 := (@Norm.norm Complex Complex.instNorm qz385)

noncomputable abbrev qz389 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep728 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz198 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz204 qz389) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) Bool.false 536893638548165 985162418487296 1006591735 985162418487296 (BSN.zrb_shape_eq qz204 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) qz24 3)

noncomputable def ep729 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz204 qz389) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) 5993549 458752 1 458752 89578585 2147483648 153 2147483648

noncomputable def ep730 := @Enclosure.Real.IsNear.mulLit_ff qz204 qz389 5993549 131072 1 131072 2 7 0 1 5993549 458752

noncomputable abbrev qz390 := (Complex.re qz430)

noncomputable abbrev qz391 := (Complex.im qz430)

noncomputable abbrev qz205 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz253 qz390 qz390) (@HMul.hMul Real Real Real qz253 qz391 qz391))

noncomputable abbrev qz206 := qz385

noncomputable def ep731 := @Enclosure.Real.IsNear.of_eq qz204 (Real.sqrt qz205) Bool.false 5993549 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz206)

noncomputable def ep732 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz205) Bool.false 5993549 131072 1 131072 5993549

noncomputable def ep733 := @Enclosure.Real.IsNear.sqrt_image qz205 2090971649 1000000 0 1 2996774 2996775 65536

noncomputable abbrev qz207 := (@HMul.hMul Real Real Real qz253 qz390 qz390)

noncomputable abbrev qz208 := (@HMul.hMul Real Real Real qz253 qz391 qz391)

noncomputable def ep734 := @Enclosure.Real.IsNear.addLit_ff qz207 qz208 49 4 0 1 2078721649 1000000 0 1

noncomputable abbrev qz209 := qz390

noncomputable def ep735 := @Enclosure.Real.IsNear.mulLit_ff qz209 qz209 7 2 0 1 7 2 0 1 49 4

noncomputable def ep736 := @Enclosure.Complex.IsNear.of_eq qz206 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz24) Bool.false 7 2 0 1 Bool.false 45593 1000 0 1 (BSN.s_add_nat_mk qz24 Bool.false 45593 1000 3 qz25)

noncomputable abbrev qz210 := (ep736 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz266 Bool.false 7 2 0 1 Bool.false 45593 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz270))

noncomputable def ep737 := @ep735 0 1 (@Enclosure.Complex.IsNear.re_isNear qz206 Bool.false 7 2 0 1 Bool.false 45593 1000 0 1 qz210)

noncomputable def ep738 := ep737 (@Enclosure.Complex.IsNear.re_isNear qz206 Bool.false 7 2 0 1 Bool.false 45593 1000 0 1 qz210)

noncomputable abbrev qz211 := qz391

noncomputable def ep739 := @Enclosure.Real.IsNear.mulLit_ff qz211 qz211 45593 1000 0 1 45593 1000 0 1 2078721649 1000000

noncomputable def ep740 := @ep739 0 1 (@Enclosure.Complex.IsNear.im_isNear qz206 Bool.false 7 2 0 1 Bool.false 45593 1000 0 1 qz210)

noncomputable def ep741 := ep740 (@Enclosure.Complex.IsNear.im_isNear qz206 Bool.false 7 2 0 1 Bool.false 45593 1000 0 1 qz210)

noncomputable def ep742 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))))) Bool.false 89578585 2147483648

noncomputable def ep743 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))))) Bool.false 89578585 2147483648

noncomputable def ep744 := nat_lit 19183733071824860758406337605227748104146822860424930899441

noncomputable def ep745 := nat_lit 11025148688238406216213337280789290051174400000000000000000000

noncomputable def ep746 := nat_lit 155152399002951445137482431395303303381005966013299825571731941883

noncomputable def ep747 := nat_lit 26210951622989138066417036592930316210258575360000000000000000000000000000

noncomputable def ep748 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)))) ep744 ep745 ep746 ep747

noncomputable def ep749 := nat_lit 2918560439339174921619525328672692055892089490101373209

noncomputable def ep750 := nat_lit 1722679482537250971283333950123326570496000000000000000000

noncomputable def ep751 := nat_lit 3023222324503347377932839888415842604264909058534026520998574323

noncomputable def ep752 := nat_lit 546061492145607043050354929019381587713720320000000000000000000000000000

noncomputable def ep753 := nat_lit 504946260054141260041375501722518946437450123776142361841

noncomputable def ep754 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201))) ep749 ep750 ep751 ep752 ep753

noncomputable def ep755 := nat_lit 10037727426790770996706116751342858376290331203666552563800374379

noncomputable def ep756 := nat_lit 33047423361303999151691678865036094402978671862648569709300333963590468456857290931035839173492736000000000000000000

noncomputable def ep757 := nat_lit 1708379477557364864758577797

noncomputable def ep758 := nat_lit 41505174165846491136000000000

noncomputable def ep759 := nat_lit 28693017766708035052014951979

noncomputable def ep760 := nat_lit 426638602779763723468800000000000000

noncomputable def ep761 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) ep757 ep758 ep759 ep760 ep757 ep758 ep759

noncomputable def ep762 := nat_lit 22471009324330343930065701721

noncomputable def ep763 := nat_lit 3320413933267719290880000000000

noncomputable def ep764 := nat_lit 144854752358681432254553273123

noncomputable def ep765 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201) Bool.true ep757 ep758 ep759 ep760 Bool.true ep762 ep763 ep764

noncomputable def ep766 := nat_lit 5119663233357164681625600000000000000

noncomputable def ep767 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201 Bool.true ep757 ep758 ep759 ep760 Bool.true ep762 ep763 ep764 ep766

noncomputable def ep768 := nat_lit 2351523146262456487073491

noncomputable def ep769 := nat_lit 2213609288845146193920000000

noncomputable def ep770 := nat_lit 7380531814108365220811633

noncomputable def ep771 := nat_lit 3413108822238109787750400000000000

noncomputable def ep772 := nat_lit 6657153674259775222503799363

noncomputable def ep773 := nat_lit 166020696663385964544000000000

noncomputable def ep774 := nat_lit 4628408548324081566568916309

noncomputable abbrev qz212 := (Complex.re qz386)

noncomputable abbrev qz213 := (Complex.im qz386)

noncomputable def ep775 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz212) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz213) ep768 ep769 ep770 ep771 ep772 ep773 ep774

noncomputable def ep776 := nat_lit 71106433796627287244800000000000000

noncomputable def ep777 := nat_lit 15126738721573603322652386652100904403227073576960000000

noncomputable def ep778 := nat_lit 7110643379662728724480000

noncomputable def ep779 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz212 6234914947 480000000 0 1 377154005507953 4611686018427387904 1183742180422139 ep778 ep768

noncomputable def ep780 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) 6234914947 480000000 0 1 0 1 0 1 6234914947

noncomputable def ep781 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 18704744841 2000000 0 1 6234914947 480000000 0

noncomputable def ep782 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz20) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow09.d14 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz20 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz31)

noncomputable abbrev qz392 := (@HAdd.hAdd Complex Complex Complex qz410 qz409 qz414)

noncomputable abbrev qz214 := qz392

noncomputable def ep783 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz52 (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) qz214) Bool.true 18704744841 2000000 0 1 Bool.true 94512996392857 1000000000 0 1

noncomputable abbrev qz215 := (Complex.re qz392)

noncomputable abbrev qz216 := (Complex.im qz392)

noncomputable def ep784 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz215) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz216) 2077971649 400000 0 1 2078721649 500000 0 1

noncomputable def ep785 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz215 2077971649 1000000 0 1 5 2 0 1 2077971649 400000

noncomputable abbrev qz393 := (@HAdd.hAdd Complex Complex Complex qz410 qz409 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz217 := qz393

noncomputable def ep786 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz52 (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) qz217) Bool.true 2077971649 1000000 0 1 Bool.false 45593 500 0 1

noncomputable abbrev qz218 := (Complex.re qz393)

noncomputable abbrev qz219 := (Complex.im qz393)

noncomputable def ep787 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz218) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz219) 3 4 0 1 2078721649 1000000 0 1

noncomputable def ep788 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz218 1 2 0 1 3 2 0 1 3 4

noncomputable def ep789 := @ep788 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep347)

noncomputable def ep790 := @Enclosure.Complex.IsNear.of_eq qz217 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz24) Bool.false 3 2 0 1 Bool.false 45593 1000 0 1 (BSN.s_add_nat_mk qz24 Bool.false 45593 1000 1 qz25)

noncomputable abbrev qz220 := (ep790 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz266 Bool.false 3 2 0 1 Bool.false 45593 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz270))

noncomputable def ep791 := ep789 (@Enclosure.Complex.IsNear.re_isNear qz217 Bool.false 3 2 0 1 Bool.false 45593 1000 0 1 qz220)

noncomputable def ep792 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz219 45593 1000 0 1 45593 1000 0 1 2078721649 1000000

noncomputable def ep793 := @ep792 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep347)

noncomputable def ep794 := ep793 (@Enclosure.Complex.IsNear.im_isNear qz217 Bool.false 3 2 0 1 Bool.false 45593 1000 0 1 qz220)

noncomputable def ep795 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) qz217 Bool.true 2077971649 1000000 0 1 Bool.false 45593 500 0 1 (@ep787 8311886596 2077971649 1000000 0 1 (ep791 rfl) (ep794 rfl) rfl rfl)

noncomputable def ep796 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz219) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz218) 45593 2000 0 1 136779 2000 0 1

noncomputable def ep797 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz219 1 2 0 1 45593 1000 0 1 45593 2000

noncomputable def ep798 := @ep797 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep347)

noncomputable def ep799 := ep798 (@Enclosure.Complex.IsNear.im_isNear qz217 Bool.false 3 2 0 1 Bool.false 45593 1000 0 1 qz220)

noncomputable def ep800 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1))) qz218 45593 1000 0 1 3 2 0 1 136779 2000

noncomputable def ep801 := @ep800 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 45593 1000 0 1 ep347)

noncomputable def ep802 := ep801 (@Enclosure.Complex.IsNear.re_isNear qz217 Bool.false 3 2 0 1 Bool.false 45593 1000 0 1 qz220)

noncomputable abbrev qz221 := (ep786 (BSN.ascPochhammer_succ_eval_c 1 2 qz258 rfl) (ep795 (@ep796 364744000 45593 500 0 1 (ep799 rfl) (ep802 rfl) rfl rfl)))

noncomputable def ep803 := @ep785 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2077971649 1000000 0 1 Bool.false 45593 500 0 1 qz221)

noncomputable def ep804 := @Enclosure.Complex.IsNear.of_eq qz214 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz24) Bool.false 5 2 0 1 Bool.false 45593 1000 0 1 (BSN.s_add_nat_mk qz24 Bool.false 45593 1000 2 qz25)

noncomputable abbrev qz222 := (ep804 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz266 Bool.false 5 2 0 1 Bool.false 45593 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz270))

noncomputable def ep805 := ep803 (@Enclosure.Complex.IsNear.re_isNear qz214 Bool.false 5 2 0 1 Bool.false 45593 1000 0 1 qz222)

noncomputable def ep806 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz216 45593 500 0 1 45593 1000 0 1 2078721649 500000

noncomputable def ep807 := @ep806 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2077971649 1000000 0 1 Bool.false 45593 500 0 1 qz221)

noncomputable def ep808 := ep807 (@Enclosure.Complex.IsNear.im_isNear qz214 Bool.false 5 2 0 1 Bool.false 45593 1000 0 1 qz222)

noncomputable def ep809 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) qz214 Bool.true 18704744841 2000000 0 1 Bool.true 94512996392857 1000000000 0 1 (@ep784 1870474484100000 18704744841 2000000 0 1 (ep805 rfl) (ep808 rfl) rfl rfl)

noncomputable def ep810 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz216) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz215) 94740961392857 1000000000 0 1 45593 200 0 1

noncomputable def ep811 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz216 2077971649 1000000 0 1 45593 1000 0 1 94740961392857 1000000000

noncomputable def ep812 := @ep811 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2077971649 1000000 0 1 Bool.false 45593 500 0 1 qz221)

noncomputable def ep813 := ep812 (@Enclosure.Complex.IsNear.im_isNear qz214 Bool.false 5 2 0 1 Bool.false 45593 1000 0 1 qz222)

noncomputable def ep814 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2))) qz215 45593 500 0 1 5 2 0 1 45593 200

noncomputable def ep815 := @ep814 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2077971649 1000000 0 1 Bool.false 45593 500 0 1 qz221)

noncomputable def ep816 := ep815 (@Enclosure.Complex.IsNear.re_isNear qz214 Bool.false 5 2 0 1 Bool.false 45593 1000 0 1 qz222)

noncomputable abbrev qz223 := (ep783 (BSN.ascPochhammer_succ_eval_c 2 3 qz258 rfl) (ep809 (@ep810 18902599278571400 94512996392857 1000000000 0 1 (ep813 rfl) (ep816 rfl) rfl rfl)))

noncomputable def ep817 := @ep781 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep782) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 18704744841 2000000 0 1 Bool.true 94512996392857 1000000000 0 1 qz223)

noncomputable def ep818 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 94512996392857 1000000000 0 1 0 1 0

noncomputable def ep819 := @ep818 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep782) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 18704744841 2000000 0 1 Bool.true 94512996392857 1000000000 0 1 qz223)

noncomputable def ep820 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) 94512996392857 720000000000 0 1 0 1 0 1 94512996392857

noncomputable def ep821 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 94512996392857 1000000000 0 1 94512996392857 720000000000 0

noncomputable def ep822 := @ep821 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep782) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 18704744841 2000000 0 1 Bool.true 94512996392857 1000000000 0 1 qz223)

noncomputable def ep823 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 18704744841 2000000 0 1 0 1 0

noncomputable def ep824 := @ep823 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep782) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 18704744841 2000000 0 1 Bool.true 94512996392857 1000000000 0 1 qz223)

noncomputable def ep825 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 6234914947 480000000 0 1 Bool.false 94512996392857 720000000000 0 1 (@ep780 6234914947 480000000 0 1 (ep817 rfl) (ep819 rfl) rfl rfl) (@ep820 94512996392857 720000000000 0 1 (ep822 rfl) (ep824 rfl) rfl rfl)

noncomputable def ep826 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 6234914947 480000000 0 1 Bool.false 94512996392857 720000000000 0 1 ep825

noncomputable def ep827 := @Enclosure.Complex.IsNear.re_isNear qz201 Bool.true 377154005507953 4611686018427387904 1183742180422139 ep778 Bool.false 352181918272295 1152921504606846976 440740200022533 888830422457841090560000

noncomputable abbrev qz394 := (@Nat.cast Real Real.instNatCast 10000000)

noncomputable abbrev qz224 := (@Inv.inv Real Real.instInv (Real.sqrt qz394))

noncomputable def ep828 := @Enclosure.Complex.IsNear.of_eq qz201 (Complex.mk (@HMul.hMul Real Real Real qz0 qz224 qz119) (@HMul.hMul Real Real Real qz0 qz224 qz120)) Bool.true 377154005507953 4611686018427387904 1183742180422139 ep778 Bool.false 352181918272295 1152921504606846976 440740200022533

noncomputable abbrev qz225 := (Real.sqrt qz394)

noncomputable def ep829 := @Enclosure.Real.IsNear.inv_image qz225 6790939565647 2147483648 1 2147483648 339546 339547 1073741824 (@Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz394 qz26)) Bool.false 6790939565647 2147483648 1 2147483648 (BSN.sqrt_natCast_div_one 10000000) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz394 qz26)) Bool.false 6790939565647 2147483648 1 2147483648 6790939565647 2147483648 1 2147483648 (BSN.sqrt_enclosure 10000000 1 3395469782823 3395469782824 1073741824 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep830 := nat_lit 89076946236074554071973888

noncomputable def ep831 := nat_lit 38685626227668133590597632

noncomputable def ep832 := BSN.log_dyadic_bound 2 18 5 4 10413862744320 1073741824 320710000 43175675904 26880 239598563 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 18) 0 4 43175675904 10413862744320 26880 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep833 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz122 45593 1000 0 1 10369921363433189 4503599627370496 100000096213 32071000000000000000 472795824723009386077 4503599627370496000 4559304386639309 32071000000000000000000 qz29 (BSN.isNear_log_sfrac 10 1 10369921363433189 4503599627370496 100000096213 32071000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz121) Bool.false ep830 ep831 1000000962130000 320710000000000000000000 10369921363433189 4503599627370496 100000096213 32071000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 239598563 1073741824 24973259072661432 36028797018963968 320710000 1000000000000000 rfl rfl rfl rfl (ep832 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep834 := nat_lit 405179180618912225948598272

noncomputable def ep835 := nat_lit 309485009821345068724781056

noncomputable def ep836 := nat_lit 3076327268869164504033066547719080536010798031469910807115772959410230666914684011807105160106275194238542828407932797391691862736964302700844298105718287062881

noncomputable def ep837 := nat_lit 25087349417715593433012958174142958689126641386910427249058555817347792676670613748293986999300093003550818609852734049752458890129433227026772000655283952025600

noncomputable def ep838 := nat_lit 1328029907734088302198831062731064843191428285445214817021316561139973897243061058903172888647087789590683063517894931952356482444584804849412168010127201

noncomputable def ep839 := nat_lit 18641325702404866548841656641088826685642747430440909267606269433606788268702708309711546022368272907838664826684972032484108850735896369422352784665401416177505

noncomputable def ep840 := nat_lit 2282948797012119002404179193847009240710524366208848879664328579378649133577025851094752816936308463323124493496598798527473759001778423659436252059630839634329600

noncomputable def ep841 := BSN.cos_dyadic_bound_f 5757942469399 4398046511104 4 3 2147483648 642046387 ep836 ep837 ep838 ep839 ep840 ep838 555379021 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 5757942469399) (BSN.cosEvenQ 4398046511104) 0 3 ep836 ep837 ep838 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 5757942469399) (BSN.cosOddQ 4398046511104) 0 3 ep839 ep840 ep838 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz395 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 225446617471) (@Nat.cast Real Real.instNatCast 2147483648))

noncomputable def ep842 := @Enclosure.Real.IsNear.cos_image qz123 qz395 Bool.false 225446617471 2147483648 153 1073741824 Bool.true 555379021 2147483648 1 320710000 (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 472795824723009386077 4503599627370496000 4559304386639309 32071000000000000000000 225446617471 2147483648 153 1073741824 (ep833 rfl) rfl) (Enclosure.sfrac_false_div 225446617471 2147483648) (BSN.cos_reduce2 qz395 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep834) (@Nat.cast Real Real.instNatCast ep835)) 226375608064910080 72057594037927936 Bool.false 555379021 2147483648 16 1000000000000000 641420000 320710000 (BSN.sin_reduce_arg_pos_rat_q2 225446617471 2147483648 226375608064910080 72057594037927936 16 ep834 ep835 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 555379021 2147483648 ep834 ep835 5757942469399 4398046511104 642046387 641420000 (ep841 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep843 := nat_lit 7992243155150108977017580189464801196659310025848919946212250952128282481054620366445866740856695348166311511759447897627126798032732604905624162637978270914401

noncomputable def ep844 := nat_lit 326135542430302714629168456263858462958646338029835554237761225625521304796717978727821830990901209046160641928085542646781965571682631951348036008518691376332800

noncomputable def ep845 := nat_lit 39937234208164612107425406156527747544604161967011218295868833120843138233466039659750209156175792273905758184896647303303752621119313836353670663855731176068961

noncomputable def ep846 := nat_lit 11414743985060595012020895969235046203552621831044244398321642896893245667885129255473764084681542316615622467482993992637368795008892118297181260298154198171648000

noncomputable def ep847 := BSN.sin_dyadic_bound_f 5757942469399 4398046511104 4 3 2147483648 642046387 ep843 ep844 ep838 ep845 ep846 ep838 2074425260 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 5757942469399) (BSN.sinEvenQ 4398046511104) 0 3 ep843 ep844 ep838 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 5757942469399) (BSN.sinOddQ 4398046511104) 0 3 ep845 ep846 ep838 rfl rfl rfl rfl) rfl rfl

noncomputable def ep848 := @Enclosure.Real.IsNear.sin_image qz123 qz395 Bool.false 225446617471 2147483648 153 1073741824 Bool.true 2074425260 2147483648 1 320710000 (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 472795824723009386077 4503599627370496000 4559304386639309 32071000000000000000000 225446617471 2147483648 153 1073741824 (ep833 rfl) rfl) (Enclosure.sfrac_false_div 225446617471 2147483648) (BSN.sin_reduce2 qz395 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep834) (@Nat.cast Real Real.instNatCast ep835)) 226375608064910080 72057594037927936 Bool.false 2074425260 2147483648 16 1000000000000000 641420000 320710000 (BSN.sin_reduce_arg_pos_rat_q2 225446617471 2147483648 226375608064910080 72057594037927936 16 ep834 ep835 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2074425260 2147483648 ep834 ep835 5757942469399 4398046511104 642046387 641420000 (ep847 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz396 := (@Enclosure.Real.IsNear.recentre' qz224 Bool.false 679093 2147483648 1 2147483648 679093 2147483648 1 2147483648 (ep829 rfl rfl) rfl)

noncomputable def ep849 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz224 qz119) (@HMul.hMul Real Real Real qz0 qz224 qz120) Bool.true 377154005507953 4611686018427387904 1183742180422139 ep778 Bool.false 352181918272295 1152921504606846976 440740200022533 888830422457841090560000 (@Enclosure.Real.IsNear.mulLit_ft qz224 qz119 679093 2147483648 1 2147483648 555379021 2147483648 3133898239 21522483773440000 377154005507953 4611686018427387904 1183742180422139 ep778 qz396 (@Enclosure.Real.IsNear.recentre' qz119 Bool.true 555379021 2147483648 50142371824 344359740375040000 555379021 2147483648 3133898239 21522483773440000 (ep842 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz224 qz120 679093 2147483648 1 2147483648 518606315 536870912 3133898239 21522483773440000 352181918272295 1152921504606846976 440740200022533 888830422457841090560000 qz396 (@Enclosure.Real.IsNear.neg qz124 Bool.true 518606315 536870912 3133898239 21522483773440000 (@Enclosure.Real.IsNear.recentre' qz124 Bool.true 2074425260 2147483648 50142371824 344359740375040000 518606315 536870912 3133898239 21522483773440000 (ep848 rfl rfl) rfl)) rfl)

noncomputable def ep850 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz213 94512996392857 720000000000 0 1 352181918272295 1152921504606846976 440740200022533 888830422457841090560000 ep772

noncomputable def ep851 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 6234914947 480000000 0 1 Bool.false 94512996392857 720000000000 0 1 ep825

noncomputable def ep852 := @Enclosure.Complex.IsNear.im_isNear qz201 Bool.true 377154005507953 4611686018427387904 1183742180422139 ep778 Bool.false 352181918272295 1152921504606846976 440740200022533 888830422457841090560000

noncomputable def ep853 := nat_lit 110680464442257309696000000

noncomputable def ep854 := nat_lit 142212867593254574489600000000000

noncomputable def ep855 := nat_lit 35645955162124730999025891721

noncomputable def ep856 := nat_lit 111879020428310303392544261123

noncomputable def ep857 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz213) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz212) 439164861259812902298673 ep853 915992553621420246166917 ep854 ep855 ep763 ep856

noncomputable def ep858 := nat_lit 2487101748503177085391324040255139355651857186816000000

noncomputable def ep859 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz213 6234914947 480000000 0 1 352181918272295 1152921504606846976 440740200022533 888830422457841090560000 439164861259812902298673

noncomputable def ep860 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3)))) qz212 94512996392857 720000000000 0 1 377154005507953 4611686018427387904 1183742180422139 ep778 ep855

noncomputable abbrev qz397 := (@ep828 888830422457841090560000 (BSN.cpow_neg_s_sub_mk qz24 45593 1000 10 3 10000000 qz25 rfl EMRow09.d15) ep849)

noncomputable def ep861 := ep767 (@ep775 ep776 ep777 ep757 ep758 ep759 ep760 (@ep779 ep769 ep770 ep771 ep826 (ep827 qz397) rfl) (@ep850 ep773 ep774 ep776 ep851 (ep852 qz397) rfl) rfl rfl) (@ep857 ep766 ep858 ep762 ep763 ep764 ep766 (@ep859 ep853 915992553621420246166917 ep854 ep826 (ep852 qz397) rfl) (@ep860 ep763 ep856 ep766 ep851 (ep827 qz397) rfl) rfl rfl)

noncomputable def ep862 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) ep762 ep763 ep764 ep766 ep762 ep763 ep764

noncomputable def ep863 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201) Bool.true ep757 ep758 ep759 ep760 Bool.true ep762 ep763 ep764

noncomputable def ep864 := @ep729 536893638548165 985162418487296 1006591735 985162418487296 (@ep730 1 458752 (ep731 (@ep732 131072 1 131072 (ep733 (@ep734 8363886596 2090971649 1000000 0 1 (ep738 rfl) (ep741 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep742 153 2147483648 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)) (@ep743 153 2147483648 89578585 2147483648 153 2147483648 (@ep748 44789216 44789369 1073741824 (@ep754 ep745 ep755 ep747 ep756 ep744 ep745 ep746 ep747 (@ep761 ep760 ep749 ep750 ep751 ep752 (@ep765 ep766 ep861) (@ep765 ep766 ep861) rfl) (@ep862 ep766 ep753 ep745 ep755 ep747 (@ep863 ep766 ep861) (@ep863 ep766 ep861) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow09.d16 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 qz198 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)))) Bool.false 592223090612933 985162418487296 310722174181 2955487255461888 := ep727 (ep728 ep864) rfl rfl

noncomputable abbrev qz431 := (@HAdd.hAdd Complex Complex Complex qz433 qz439 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz398 := qz431

noncomputable abbrev qz226 := (@HDiv.hDiv Real Real Real qz256 (@Norm.norm Complex Complex.instNorm qz398) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz349) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz399 := (@HPow.hPow Complex Complex Complex qz411 qz424 (@HSub.hSub Complex Complex Complex qz417 qz426 qz413))

noncomputable abbrev qz227 := qz399

noncomputable def ep865 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 qz226 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) 12082659 1073741824 3117931 28991029248 699089918187375 985162418487296 1395836985

noncomputable def ep866 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 10)) 123 8192 1 221184 98233 131072 909 131072 12082659 1073741824

noncomputable def ep867 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 10)) (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 10)) (Complex.re (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 10)) (Complex.im (zetaApproximant qz141 1 10))))) Bool.false 98233 131072 909 131072

noncomputable def ep868 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 10)) (Complex.re (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 10)) (Complex.im (zetaApproximant qz141 1 10))))) Bool.false 98233 131072 909 131072

noncomputable def ep869 := nat_lit 2832752824560409256858740960053097426681

noncomputable def ep870 := nat_lit 5042803531605262754977401746227200000000

noncomputable def ep871 := nat_lit 42589911925717221888605758596230367067702060475929006141

noncomputable def ep872 := nat_lit 4102755571408300195351820336207438490310831138406400000000

noncomputable def ep873 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 10)) (Complex.re (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 10)) (Complex.im (zetaApproximant qz141 1 10)))) ep869 ep870 ep871 ep872 48662 49571

noncomputable def ep874 := nat_lit 13248050911979858903974229354145859374764037181561

noncomputable def ep875 := nat_lit 23933261757277552283587148876885327767142400000000

noncomputable def ep876 := nat_lit 25238248364457576268351426810801424247667116705402780767

noncomputable def ep877 := nat_lit 2735170380938866796901213557471625660207220758937600000000

noncomputable def ep878 := nat_lit 196259265674426950027451781375342555734894402041

noncomputable def ep879 := nat_lit 9465078758061714972157236760056461392402770835649669981

noncomputable def ep880 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 10)) (Complex.re (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 10)) (Complex.im (zetaApproximant qz141 1 10))) ep874 ep875 ep876 ep877 ep878 ep875 ep879

noncomputable def ep881 := nat_lit 8205511142816600390703640672414876980621662276812800000000

noncomputable def ep882 := nat_lit 321766194627830694587786414779298383076998892333127824766031867741861741781051180334238924800000000

noncomputable def ep883 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz141 1 10)) (Complex.re (zetaApproximant qz141 1 10)) ep489 ep490 ep491 ep492 ep489 ep490 ep491 ep492 ep874

noncomputable def ep884 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz141 1 10)) (Complex.im (zetaApproximant qz141 1 10)) 443011586388467891984821 ep490 ep605 ep492 443011586388467891984821 ep490 ep605 ep492 ep878

noncomputable def ep885 := @ep865 985162418487296 762545465456720099672064 710175806150511 985162418487296 2898401762819 26599385299156992 (@ep866 3117931 28991029248 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz202)) Bool.false 123 8192 1 221184 (BSN.theta_err_eq 1 2 96 162 EMRow09.d12 EMRow09.d13 rfl) (ep707 rfl)) (ep867 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz141 1 10)) (@ep868 98233 131072 909 131072 (@ep873 65536 (@ep880 ep881 ep882 ep869 ep870 ep871 ep872 (@ep883 ep875 ep876 ep877 ep690 ep690 rfl) (@ep884 ep875 ep879 ep881 ep696 ep696 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz228 := (@Norm.norm Complex Complex.instNorm qz398)

noncomputable def ep886 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz226 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz228 qz389) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) Bool.false 699089918187375 985162418487296 1395836985 985162418487296 (BSN.zrb_shape_eq qz228 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) qz146 3)

noncomputable def ep887 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz228 qz389) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) 6401109 458752 1 458752 109213875 2147483648 201 2147483648

noncomputable def ep888 := @Enclosure.Real.IsNear.mulLit_ff qz228 qz389 6401109 131072 1 131072 2 7 0 1 6401109 458752

noncomputable abbrev qz400 := (Complex.re qz431)

noncomputable abbrev qz401 := (Complex.im qz431)

noncomputable abbrev qz229 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz253 qz400 qz400) (@HMul.hMul Real Real Real qz253 qz401 qz401))

noncomputable abbrev qz230 := qz398

noncomputable def ep889 := @Enclosure.Real.IsNear.of_eq qz228 (Real.sqrt qz229) Bool.false 6401109 131072 1 131072 (BSN.norm_eq_sqrt_mul_add qz230)

noncomputable def ep890 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz229) Bool.false 6401109 131072 1 131072 6401109

noncomputable def ep891 := @Enclosure.Real.IsNear.sqrt_image qz229 2385011521 1000000 0 1 3200554 3200555 65536

noncomputable abbrev qz231 := (@HMul.hMul Real Real Real qz253 qz400 qz400)

noncomputable abbrev qz232 := (@HMul.hMul Real Real Real qz253 qz401 qz401)

noncomputable def ep892 := @Enclosure.Real.IsNear.addLit_ff qz231 qz232 49 4 0 1 2372761521 1000000 0 1

noncomputable abbrev qz233 := qz400

noncomputable def ep893 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 7 2 0 1 7 2 0 1 49 4

noncomputable def ep894 := @Enclosure.Complex.IsNear.of_eq qz230 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz146) Bool.false 7 2 0 1 Bool.false 48711 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 48711 1000 3 qz147)

noncomputable abbrev qz234 := (ep894 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz351 Bool.false 7 2 0 1 Bool.false 48711 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz353))

noncomputable def ep895 := @ep893 0 1 (@Enclosure.Complex.IsNear.re_isNear qz230 Bool.false 7 2 0 1 Bool.false 48711 1000 0 1 qz234)

noncomputable def ep896 := ep895 (@Enclosure.Complex.IsNear.re_isNear qz230 Bool.false 7 2 0 1 Bool.false 48711 1000 0 1 qz234)

noncomputable abbrev qz235 := qz401

noncomputable def ep897 := @Enclosure.Real.IsNear.mulLit_ff qz235 qz235 48711 1000 0 1 48711 1000 0 1 2372761521 1000000

noncomputable def ep898 := @ep897 0 1 (@Enclosure.Complex.IsNear.im_isNear qz230 Bool.false 7 2 0 1 Bool.false 48711 1000 0 1 qz234)

noncomputable def ep899 := ep898 (@Enclosure.Complex.IsNear.im_isNear qz230 Bool.false 7 2 0 1 Bool.false 48711 1000 0 1 qz234)

noncomputable def ep900 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))))) Bool.false 109213875 2147483648

noncomputable def ep901 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))))) Bool.false 109213875 2147483648

noncomputable def ep902 := nat_lit 198024013854331862380785868029089629298714879993689263437

noncomputable def ep903 := nat_lit 76563532557211154279259286672147847577600000000000000000000

noncomputable def ep904 := nat_lit 1149648512685324084370257683611534347908913645583084834610659057

noncomputable def ep905 := nat_lit 121346998254579342900078873115418130603048960000000000000000000000000000

noncomputable def ep906 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)))) ep902 ep903 ep904 ep905

noncomputable def ep907 := nat_lit 27637013828146583472544254426701301935571669433507736569

noncomputable def ep908 := nat_lit 19140883139302788569814821668036961894400000000000000000000

noncomputable def ep909 := nat_lit 1341606631088426336394701095740756447415121643962459392568095307

noncomputable def ep910 := nat_lit 242693996509158685800157746230836261206097920000000000000000000000000000

noncomputable def ep911 := nat_lit 87475958541745528490608850322284421556428202259658317161

noncomputable def ep912 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227))) ep907 ep908 ep909 ep910 ep911

noncomputable def ep913 := nat_lit 319230131427407277448604757160770749467568549067903425551074269

noncomputable def ep914 := nat_lit 80897998836386228600052582076945420402032640000000000000000000000000000

noncomputable def ep915 := nat_lit 3790354507961442554698796195269025072858889283485878225088682465628905212210463168137572175052800000000000000000000

noncomputable def ep916 := nat_lit 5257091765239273761991008587

noncomputable def ep917 := nat_lit 138350580552821637120000000000

noncomputable def ep918 := nat_lit 62067081337604065030689722339

noncomputable def ep919 := nat_lit 853277205559527446937600000000000000

noncomputable def ep920 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) ep916 ep917 ep918 ep919 ep916 ep917 ep918

noncomputable def ep921 := nat_lit 9352858308653324642784806381

noncomputable def ep922 := nat_lit 276701161105643274240000000000

noncomputable def ep923 := nat_lit 49807242453061944259220013589

noncomputable def ep924 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227) Bool.true ep916 ep917 ep918 ep919 Bool.false ep921 ep922 ep923

noncomputable def ep925 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227 Bool.true ep916 ep917 ep918 ep919 Bool.false ep921 ep922 ep923 ep919

noncomputable def ep926 := nat_lit 184467440737095516160000000

noncomputable def ep927 := nat_lit 8229646946767985282094191

noncomputable def ep928 := nat_lit 1706554411119054893875200000000000

noncomputable def ep929 := nat_lit 5641715528094306705741943337

noncomputable def ep930 := nat_lit 57952257864220072389642626839

noncomputable abbrev qz236 := (Complex.re qz399)

noncomputable abbrev qz237 := (Complex.im qz399)

noncomputable def ep931 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237) 512831683806710591667913 ep926 ep927 ep928 ep929 ep917 ep930

noncomputable def ep932 := nat_lit 969762263653748586533178696560214743713757265920000000

noncomputable def ep933 := nat_lit 3555321689831364362240000

noncomputable def ep934 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236 7117034563 480000000 0 1 216170799481353 1152921504606846976 1156330895110757 ep933 512831683806710591667913

noncomputable def ep935 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) 7117034563 480000000 0 1 0 1 0 1 7117034563

noncomputable def ep936 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 21351103689 2000000 0 1 7117034563 480000000 0

noncomputable abbrev qz402 := (@HAdd.hAdd Complex Complex Complex qz410 qz425 qz414)

noncomputable abbrev qz238 := qz402

noncomputable def ep937 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz52 (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) qz238) Bool.true 21351103689 2000000 0 1 Bool.true 115299498199431 1000000000 0 1

noncomputable abbrev qz239 := (Complex.re qz402)

noncomputable abbrev qz240 := (Complex.im qz402)

noncomputable def ep938 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz240) 2372011521 400000 0 1 2372761521 500000 0 1

noncomputable def ep939 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz239 2372011521 1000000 0 1 5 2 0 1 2372011521 400000

noncomputable abbrev qz403 := (@HAdd.hAdd Complex Complex Complex qz410 qz425 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz241 := qz403

noncomputable def ep940 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz52 (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) qz241) Bool.true 2372011521 1000000 0 1 Bool.false 48711 500 0 1

noncomputable abbrev qz242 := (Complex.re qz403)

noncomputable abbrev qz243 := (Complex.im qz403)

noncomputable def ep941 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz242) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz243) 3 4 0 1 2372761521 1000000 0 1

noncomputable def ep942 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz242 1 2 0 1 3 2 0 1 3 4

noncomputable def ep943 := @ep942 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep657)

noncomputable def ep944 := @Enclosure.Complex.IsNear.of_eq qz241 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz146) Bool.false 3 2 0 1 Bool.false 48711 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 48711 1000 1 qz147)

noncomputable abbrev qz244 := (ep944 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz351 Bool.false 3 2 0 1 Bool.false 48711 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz353))

noncomputable def ep945 := ep943 (@Enclosure.Complex.IsNear.re_isNear qz241 Bool.false 3 2 0 1 Bool.false 48711 1000 0 1 qz244)

noncomputable def ep946 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz243 48711 1000 0 1 48711 1000 0 1 2372761521 1000000

noncomputable def ep947 := @ep946 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep657)

noncomputable def ep948 := ep947 (@Enclosure.Complex.IsNear.im_isNear qz241 Bool.false 3 2 0 1 Bool.false 48711 1000 0 1 qz244)

noncomputable def ep949 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) qz241 Bool.true 2372011521 1000000 0 1 Bool.false 48711 500 0 1 (@ep941 9488046084 2372011521 1000000 0 1 (ep945 rfl) (ep948 rfl) rfl rfl)

noncomputable def ep950 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz243) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz242) 48711 2000 0 1 146133 2000 0 1

noncomputable def ep951 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz243 1 2 0 1 48711 1000 0 1 48711 2000

noncomputable def ep952 := @ep951 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep657)

noncomputable def ep953 := ep952 (@Enclosure.Complex.IsNear.im_isNear qz241 Bool.false 3 2 0 1 Bool.false 48711 1000 0 1 qz244)

noncomputable def ep954 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz242 48711 1000 0 1 3 2 0 1 146133 2000

noncomputable def ep955 := @ep954 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 48711 1000 0 1 ep657)

noncomputable def ep956 := ep955 (@Enclosure.Complex.IsNear.re_isNear qz241 Bool.false 3 2 0 1 Bool.false 48711 1000 0 1 qz244)

noncomputable abbrev qz245 := (ep940 (BSN.ascPochhammer_succ_eval_c 1 2 qz349 rfl) (ep949 (@ep950 389688000 48711 500 0 1 (ep953 rfl) (ep956 rfl) rfl rfl)))

noncomputable def ep957 := @ep939 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2372011521 1000000 0 1 Bool.false 48711 500 0 1 qz245)

noncomputable def ep958 := @Enclosure.Complex.IsNear.of_eq qz238 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz146) Bool.false 5 2 0 1 Bool.false 48711 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 48711 1000 2 qz147)

noncomputable abbrev qz246 := (ep958 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz351 Bool.false 5 2 0 1 Bool.false 48711 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz353))

noncomputable def ep959 := ep957 (@Enclosure.Complex.IsNear.re_isNear qz238 Bool.false 5 2 0 1 Bool.false 48711 1000 0 1 qz246)

noncomputable def ep960 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz240 48711 500 0 1 48711 1000 0 1 2372761521 500000

noncomputable def ep961 := @ep960 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2372011521 1000000 0 1 Bool.false 48711 500 0 1 qz245)

noncomputable def ep962 := ep961 (@Enclosure.Complex.IsNear.im_isNear qz238 Bool.false 5 2 0 1 Bool.false 48711 1000 0 1 qz246)

noncomputable def ep963 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) qz238 Bool.true 21351103689 2000000 0 1 Bool.true 115299498199431 1000000000 0 1 (@ep938 2135110368900000 21351103689 2000000 0 1 (ep959 rfl) (ep962 rfl) rfl rfl)

noncomputable def ep964 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz240) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz239) 115543053199431 1000000000 0 1 48711 200 0 1

noncomputable def ep965 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz240 2372011521 1000000 0 1 48711 1000 0 1 115543053199431 1000000000

noncomputable def ep966 := @ep965 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2372011521 1000000 0 1 Bool.false 48711 500 0 1 qz245)

noncomputable def ep967 := ep966 (@Enclosure.Complex.IsNear.im_isNear qz238 Bool.false 5 2 0 1 Bool.false 48711 1000 0 1 qz246)

noncomputable def ep968 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz239 48711 500 0 1 5 2 0 1 48711 200

noncomputable def ep969 := @ep968 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2372011521 1000000 0 1 Bool.false 48711 500 0 1 qz245)

noncomputable def ep970 := ep969 (@Enclosure.Complex.IsNear.re_isNear qz238 Bool.false 5 2 0 1 Bool.false 48711 1000 0 1 qz246)

noncomputable abbrev qz247 := (ep937 (BSN.ascPochhammer_succ_eval_c 2 3 qz349 rfl) (ep963 (@ep964 23059899639886200 115299498199431 1000000000 0 1 (ep967 rfl) (ep970 rfl) rfl rfl)))

noncomputable def ep971 := @ep936 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep782) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21351103689 2000000 0 1 Bool.true 115299498199431 1000000000 0 1 qz247)

noncomputable def ep972 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 115299498199431 1000000000 0 1 0 1 0

noncomputable def ep973 := @ep972 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep782) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21351103689 2000000 0 1 Bool.true 115299498199431 1000000000 0 1 qz247)

noncomputable def ep974 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) 38433166066477 240000000000 0 1 0 1 0 1 38433166066477

noncomputable def ep975 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 115299498199431 1000000000 0 1 38433166066477 240000000000 0

noncomputable def ep976 := @ep975 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep782) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21351103689 2000000 0 1 Bool.true 115299498199431 1000000000 0 1 qz247)

noncomputable def ep977 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 21351103689 2000000 0 1 0 1 0

noncomputable def ep978 := @ep977 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep782) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21351103689 2000000 0 1 Bool.true 115299498199431 1000000000 0 1 qz247)

noncomputable def ep979 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 7117034563 480000000 0 1 Bool.false 38433166066477 240000000000 0 1 (@ep935 7117034563 480000000 0 1 (ep971 rfl) (ep973 rfl) rfl rfl) (@ep974 38433166066477 240000000000 0 1 (ep976 rfl) (ep978 rfl) rfl rfl)

noncomputable def ep980 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 7117034563 480000000 0 1 Bool.false 38433166066477 240000000000 0 1 ep979

noncomputable def ep981 := @Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 216170799481353 1152921504606846976 1156330895110757 ep933 Bool.false 146792890243181 576460752303423488 1507871034199507 ep933

noncomputable def ep982 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk (@HMul.hMul Real Real Real qz0 qz224 qz193) (@HMul.hMul Real Real Real qz0 qz224 qz194)) Bool.false 216170799481353 1152921504606846976 1156330895110757 ep933 Bool.false 146792890243181 576460752303423488 1507871034199507

noncomputable def ep983 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz122 48711 1000 0 1 10369921363433189 4503599627370496 100000096213 32071000000000000000 505129239534194069379 4503599627370496000 374700360510111 2467000000000000000000 qz148 (BSN.isNear_log_sfrac 10 1 10369921363433189 4503599627370496 100000096213 32071000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz121) Bool.false ep830 ep831 1000000962130000 320710000000000000000000 10369921363433189 4503599627370496 100000096213 32071000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 239598563 1073741824 24973259072661432 36028797018963968 320710000 1000000000000000 rfl rfl rfl rfl (ep832 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep984 := nat_lit 3069139755037848378540032

noncomputable def ep985 := nat_lit 4835703278458516698824704

noncomputable def ep986 := nat_lit 68692878349772278780038385232515052882709012744281971383148987746815642957963859343412524911123003097345

noncomputable def ep987 := nat_lit 50797410752592599495442790923292316227798919877281851451531752809858799638366050241238301547400049385799680

noncomputable def ep988 := nat_lit 3685824948625278990866995234560969331152971093825688978166289753724815497947906227585443592494137601

noncomputable def ep989 := nat_lit 179903951961391527305543890950016801694844595234205635840377936772534938998146763575045284049029541413121

noncomputable def ep990 := nat_lit 931285863797530990749784500260359130842980197750167276611415468180744660036710921089368861702334238739660800

noncomputable def ep991 := BSN.sin_dyadic_bound_f 2791366346207 4398046511104 3 2 2147483648 642046387 ep986 ep987 ep988 ep989 ep990 ep988 1273291284 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2791366346207) (BSN.sinEvenQ 4398046511104) 0 2 ep986 ep987 ep988 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2791366346207) (BSN.sinOddQ 4398046511104) 0 2 ep989 ep990 ep988 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz404 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3763506111) (@Nat.cast Real Real.instNatCast 33554432))

noncomputable def ep992 := @Enclosure.Real.IsNear.cos_image qz195 qz404 Bool.false 3763506111 33554432 327 2147483648 Bool.false 1273291284 2147483648 1 320710000 (@Enclosure.Real.IsNear.recentre' qz195 Bool.false 505129239534194069379 4503599627370496000 374700360510111 2467000000000000000000 3763506111 33554432 327 2147483648 (ep983 rfl) rfl) (Enclosure.sfrac_false_div 3763506111 33554432) (BSN.cos_reduce3 qz404 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep984) (@Nat.cast Real Real.instNatCast ep985)) 226375608064910080 72057594037927936 Bool.false 1273291284 2147483648 17 1000000000000000 641420000 320710000 (BSN.sin_reduce_arg_pos_rat_q3 3763506111 33554432 226375608064910080 72057594037927936 17 ep984 ep985 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1273291284 2147483648 ep984 ep985 2791366346207 4398046511104 642046387 641420000 (ep991 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep993 := nat_lit 38164348338739543890683932682612612032318852845087239963517511543677012672423454260219218481109443559681

noncomputable def ep994 := nat_lit 5644156750288066610604754547032479580866546653031316827947972534428755515374005582359811283044449931755520

noncomputable def ep995 := nat_lit 114485673366321381114070064057368714158294252593074068512596202051523588386274466968202484556143342403841

noncomputable def ep996 := nat_lit 253987053762962997477213954616461581138994599386409257257658764049293998191830251206191507737000246928998400

noncomputable def ep997 := BSN.cos_dyadic_bound_f 2791366346207 4398046511104 3 2 2147483648 642046387 ep993 ep994 ep988 ep995 ep996 ep988 1729281736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2791366346207) (BSN.cosEvenQ 4398046511104) 0 2 ep993 ep994 ep988 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2791366346207) (BSN.cosOddQ 4398046511104) 0 2 ep995 ep996 ep988 rfl rfl rfl rfl) rfl rfl

noncomputable def ep998 := @Enclosure.Real.IsNear.sin_image qz195 qz404 Bool.false 3763506111 33554432 327 2147483648 Bool.true 1729281736 2147483648 1 320710000 (@Enclosure.Real.IsNear.recentre' qz195 Bool.false 505129239534194069379 4503599627370496000 374700360510111 2467000000000000000000 3763506111 33554432 327 2147483648 (ep983 rfl) rfl) (Enclosure.sfrac_false_div 3763506111 33554432) (BSN.sin_reduce3 qz404 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep984) (@Nat.cast Real Real.instNatCast ep985)) 226375608064910080 72057594037927936 Bool.false 1729281736 2147483648 17 1000000000000000 641420000 320710000 (BSN.sin_reduce_arg_pos_rat_q3 3763506111 33554432 226375608064910080 72057594037927936 17 ep984 ep985 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1729281736 2147483648 ep984 ep985 2791366346207 4398046511104 642046387 641420000 (ep997 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep999 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz224 qz193) (@HMul.hMul Real Real Real qz0 qz224 qz194) Bool.false 216170799481353 1152921504606846976 1156330895110757 ep933 Bool.false 146792890243181 576460752303423488 1507871034199507 ep933 (@Enclosure.Real.IsNear.mulLit_ff qz224 qz193 679093 2147483648 1 2147483648 318322821 536870912 6688728353 43044967546880000 216170799481353 1152921504606846976 1156330895110757 ep933 qz396 (@Enclosure.Real.IsNear.recentre' qz193 Bool.false 1273291284 2147483648 107019653648 688719480750080000 318322821 536870912 6688728353 43044967546880000 (ep992 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz224 qz194 679093 2147483648 1 2147483648 216160217 268435456 6688728353 43044967546880000 146792890243181 576460752303423488 1507871034199507 ep933 qz396 (@Enclosure.Real.IsNear.neg qz196 Bool.true 216160217 268435456 6688728353 43044967546880000 (@Enclosure.Real.IsNear.recentre' qz196 Bool.true 1729281736 2147483648 107019653648 688719480750080000 216160217 268435456 6688728353 43044967546880000 (ep998 rfl rfl) rfl)) rfl)

noncomputable def ep1000 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237 38433166066477 240000000000 0 1 146792890243181 576460752303423488 1507871034199507 ep933 ep929

noncomputable def ep1001 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 7117034563 480000000 0 1 Bool.false 38433166066477 240000000000 0 1 ep979

noncomputable def ep1002 := @Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 216170799481353 1152921504606846976 1156330895110757 ep933 Bool.false 146792890243181 576460752303423488 1507871034199507 ep933

noncomputable def ep1003 := nat_lit 276701161105643274240000000

noncomputable def ep1004 := nat_lit 10731570266944446356560441

noncomputable def ep1005 := nat_lit 2769376078396646663573301127

noncomputable def ep1006 := nat_lit 92233720368547758080000000000

noncomputable def ep1007 := nat_lit 44441457319589721080939793089

noncomputable def ep1008 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236) 1044730073463384652064903 ep1003 ep1004 ep928 ep1005 ep1006 ep1007

noncomputable def ep1009 := nat_lit 862648917886979283465797313036124559604428308480000000

noncomputable def ep1010 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz237 7117034563 480000000 0 1 146792890243181 576460752303423488 1507871034199507 ep933 1044730073463384652064903

noncomputable def ep1011 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236 38433166066477 240000000000 0 1 216170799481353 1152921504606846976 1156330895110757 ep933 ep1005

noncomputable abbrev qz405 := (@ep982 ep933 (BSN.cpow_neg_s_sub_mk qz146 48711 1000 10 3 10000000 qz147 rfl EMRow09.d15) ep999)

noncomputable def ep1012 := ep925 (@ep931 ep919 ep932 ep916 ep917 ep918 ep919 (@ep934 ep926 ep927 ep928 ep980 (ep981 qz405) rfl) (@ep1000 ep917 ep930 ep919 ep1001 (ep1002 qz405) rfl) rfl rfl) (@ep1008 ep919 ep1009 ep921 ep922 ep923 ep919 (@ep1010 ep1003 ep1004 ep928 ep980 (ep1002 qz405) rfl) (@ep1011 ep1006 ep1007 ep919 ep1001 (ep981 qz405) rfl) rfl rfl)

noncomputable def ep1013 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (Complex.im (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) ep921 ep922 ep923 ep919 ep921 ep922 ep923

noncomputable def ep1014 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227) Bool.true ep916 ep917 ep918 ep919 Bool.false ep921 ep922 ep923

noncomputable def ep1015 := @ep887 699089918187375 985162418487296 1395836985 985162418487296 (@ep888 1 458752 (ep889 (@ep890 131072 1 131072 (ep891 (@ep892 9540046084 2385011521 1000000 0 1 (ep896 rfl) (ep899 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep900 201 2147483648 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)) (@ep901 201 2147483648 109213875 2147483648 201 2147483648 (@ep906 54606837 54607038 1073741824 (@ep912 ep903 ep913 ep914 ep915 ep902 ep903 ep904 ep905 (@ep920 ep919 ep907 ep908 ep909 ep910 (@ep924 ep919 ep1012) (@ep924 ep919 ep1012) rfl) (@ep1013 ep919 ep911 ep903 ep913 ep914 (@ep1014 ep919 ep1012) (@ep1014 ep919 ep1012) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow09.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 qz226 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)))) Bool.false 710175806150511 985162418487296 2898401762819 26599385299156992 := ep885 (ep886 ep1015) rfl rfl

noncomputable def EMRow09.d18 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz406 := (EMRow09.d3 qz415 qz427 (@Enclosure.dec_le_dec qz415 qz427 45593 1000 48711 1000 (@Eq.refl Real qz415) (@Eq.refl Real qz427) rfl rfl rfl) 10 10 1 1)

noncomputable abbrev qz248 := qz406

noncomputable def ep1016 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz248 (@Enclosure.dec_nonneg qz24 45593 1000 qz25) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 10 rfl)

noncomputable abbrev qz249 := (Zeta.Certificates.ZIntervalEM.fstVal qz406)

noncomputable def ep1017 := @Enclosure.Real.IsNear.neg_val qz249 ep145 ep146

noncomputable def ep1018 := @Enclosure.Real.IsNear.of_eq qz249 (hardyZApproximantEM 1 10 qz24) Bool.true

noncomputable abbrev qz250 := (Zeta.Certificates.ZIntervalEM.sndVal qz406)

noncomputable def ep1019 := BSN.mul_neg_of_neg_pos_r qz249 qz250 (@ep1017 ep147 ep148 (@ep1018 ep145 ep146 ep147 ep148 (@Eq.refl Real (hardyZApproximantEM 1 10 qz24)) EMRow09.d9) rfl rfl rfl)

noncomputable def ep1020 := @Enclosure.Real.IsNear.pos_val qz250 ep474 ep475

noncomputable def ep1021 := @Enclosure.Real.IsNear.of_eq qz250 (hardyZApproximantEM 1 10 qz146) Bool.false

noncomputable def ep1022 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz249) (BSN.hardyZErrorBoundStrong 1 10 qz24)

noncomputable def ep1023 := @Enclosure.norm_gt_of_isNear qz249 (BSN.hardyZErrorBoundStrong 1 10 qz24) Bool.true

noncomputable def ep1024 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 10 qz24) (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 qz198 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)))) Bool.false 592223090612933 985162418487296 310722174181 2955487255461888 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz21 1 10))) (@HMul.hMul Real Real Real qz0 qz198 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz21 (@ascPochhammer Complex Complex.instSemiring 3))) qz201)))))

noncomputable def ep1025 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz250) (BSN.hardyZErrorBoundStrong 1 10 qz146)

noncomputable def ep1026 := @Enclosure.norm_gt_of_isNear qz250 (BSN.hardyZErrorBoundStrong 1 10 qz146) Bool.false

noncomputable def ep1027 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 10 qz146) (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 qz226 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)))) Bool.false 710175806150511 985162418487296 2898401762819 26599385299156992 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz94 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 10))) (@HMul.hMul Real Real Real qz0 qz226 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz52 (@HMul.hMul Complex Complex Complex qz52 (@HDiv.hDiv Complex Complex Complex qz60 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz199)) ↑qz200) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz227)))))

noncomputable def ep1028 := @List.cons EMRow09.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz248 (ep1016 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 10 rfl) (ep1019 (@ep1020 ep476 ep477 (@ep1021 ep474 ep475 ep476 ep477 (@Eq.refl Real (hardyZApproximantEM 1 10 qz146)) EMRow09.d11) rfl rfl rfl)) (ep1022 (hardyZErrorBoundEM 1 10 qz24) (BSN.hardyZErrorBoundEM_le_strong 1 10 qz24 rfl) (@ep1023 Bool.false ep145 ep146 ep147 ep148 592223090612933 985162418487296 310722174181 2955487255461888 (@ep1018 ep145 ep146 ep147 ep148 (@Eq.refl Real (hardyZApproximantEM 1 10 qz24)) EMRow09.d9) (ep1024 EMRow09.d16) rfl rfl rfl rfl rfl)) (ep1025 (hardyZErrorBoundEM 1 10 qz146) (BSN.hardyZErrorBoundEM_le_strong 1 10 qz146 rfl) (@ep1026 Bool.false ep474 ep475 ep476 ep477 710175806150511 985162418487296 2898401762819 26599385299156992 (@ep1021 ep474 ep475 ep476 ep477 (@Eq.refl Real (hardyZApproximantEM 1 10 qz146)) EMRow09.d11) (ep1027 EMRow09.d17) rfl rfl rfl rfl rfl)))) (@List.nil EMRow09.d0)

noncomputable abbrev qz407 := (@Enclosure.dec_le_dec qz415 qz427 45593 1000 48711 1000 (@Eq.refl Real qz415) (@Eq.refl Real qz427) rfl rfl rfl)

noncomputable abbrev qz251 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1028 (@List.IsChain.singleton EMRow09.d1 EMRow09.d18 (EMRow09.d2 qz266 qz351 qz407))))

noncomputable abbrev qz408 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1029 := And (@Eq (Option Real) (@Option.map qz408 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz408 qz251)) (@Option.some Real qz24))

noncomputable def ep1030 := ep1029 (@Eq (Option Real) (@Option.map qz408 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz408 qz251)) (@Option.some Real qz146))

noncomputable def ep1031 := @And.intro (@Eq Nat (@List.length qz408 qz251) 1) ep1030

noncomputable def ep1032 := @And.intro (@Eq (Option Real) (@Option.map qz408 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz408 qz251)) (@Option.some Real qz24))

noncomputable def ep1033 := @ep1032 (@Eq (Option Real) (@Option.map qz408 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz408 qz251)) (@Option.some Real qz146))

noncomputable abbrev qz252 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1028 (@List.IsChain.singleton EMRow09.d1 EMRow09.d18 (EMRow09.d2 qz266 qz351 qz407)))

theorem EMRow09.d19 : Zeta.Certificates.BatchSpec 1 45593 1000 48711 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz408 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz408 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz408 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz24)) (@Eq (Option Real) (@Option.map qz408 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz408 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz146)))) qz252 (ep1031 (@Eq.refl Nat 1) (ep1033 (@Eq.refl (Option Real) (@Option.some Real qz24)) (@Eq.refl (Option Real) (@Option.some Real qz146))))

theorem solution : Zeta.Certificates.BatchSpec 1 45593 1000 48711 1000 := EMRow09.d19
#print axioms solution
#check solution
