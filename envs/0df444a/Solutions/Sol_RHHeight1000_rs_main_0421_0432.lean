-- Prove2me | solution 1 for RHHeight1000.rs_main_0421_0432
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T07:53:44.999728+00:00
-- url     : https://prove2.me/submissions/0553b895-aa34-4e3f-8aa3-9a5d68286705

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable abbrev RSCompact.c0 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) 

noncomputable abbrev RSCompact.c1 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) 

noncomputable abbrev RSCompact.c2 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi) 

noncomputable abbrev RSCompact.c3 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c4 := (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) 

noncomputable abbrev RSCompact.c5 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c6 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c7 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c8 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c9 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) RSCompact.c2 Real.pi) 

noncomputable abbrev RSCompact.c10 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) RSCompact.c2 Real.pi) 

noncomputable abbrev RSCompact.c11 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) RSCompact.c2 Real.pi) 

noncomputable def RS421to432.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS421to432.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS421to432.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS421to432.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS421to432.d2 a b h 

theorem RS421to432.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS421to432.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS421to432.d3 a b h)) 

noncomputable def Ns420p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns420p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns420p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns420p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns420p0 Ns420p1 Ns420p2 Ns420p1 307286088 268435456 1 108160000 307286088 268435456 1 108160000 153643044 134217728 2 134217728 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns420p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns420p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns420p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns420p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns420p8 := nat_lit 6573389678388862351155759458724141871788046104702795740939545775355827438482086890337971184306503456724674701876007739166027855002689342487126242201873902293161938510715598861337724155978462934346539722102807352693564004597780440630880721700532830491857281958381906437104026277614553345439647264822859384496062743250358046048880947907642984145065307980413206151384068885350206914057384338280179177725692904928360597982006748935836093248417685721122261418062303135764477585928239149568275027355236134745000697766005167655784166499502223346815249842007858448160935771607172549259242715110048115445292136446613946552506617916138661398090061483392335970316672263498462800198746102072055363920390651513279180731193678641632192805423820381724597815072905552156968003637925334143020171520625 

noncomputable def Ns420p9 := nat_lit 702614123509571190207434367497643053726389003684617183996726348470791223755418688598787599501240412886827946200799073391711533512528899996899108221816773619593298708861540359234024488137706935294538610329535191474811214152768697527793266408685885408431698677504366547635987768499962038530066773279961750661013789994039311989768445302208965109624014234440840481147386361324656837522786906307734587964680180646868573806366973424595907336814393861048013934514934272026683624090151873353554279683010347128413433843775162422864773798490322287367830744467164676975854073090397461536167654230134598982106570951920409048997311342333559851528447946435833392322432321465286801524775001800171249769824525762984779161997185015423416919065587459911326773695449510414365759468097615398764501522575 

noncomputable def Ns420p10 := nat_lit 541392566138474909591412279139378993255101875047003589935782329109463644892392322173295519240510467068363239080443023466297029982601757003829684821059136286585994161974307047499333049696728682047261006046816072264069316416942594393775486731411634963656291648112663555457379375292741727868294229136381639619442405391741167595634732196900940186574903289828257139713673376723681752760045249773972946001592268830432998579610986951410273979009689762628244990479410235165324966379611071762421902787196495466840333515349387051622842182127210560393625584510287605139387730811840242457253978115925211125629993337408355023684205061830608267784338105681114876710224147942516826039256450164994945245879666660679160980454641866547806615379410050641833332584350523565507268843323231339375 

noncomputable def Ns420p11 := BSN.log_dyadic_bound Ns420p6 Ns420p7 16 15 Ns420p8 268435456 108160000 Ns420p9 Ns420p10 307286088 Ns420p4 Ns420p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns420p6) (BSN.artanhQ Ns420p7) 0 15 Ns420p9 Ns420p8 Ns420p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns420p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns420p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns420p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns420p15 := nat_lit 6573389678388957581038003304946500209472262679236338533996718496177406624059139082449994147026037314666926693076053053862592074936423388863596813530408382584499373597031431853921413941298322255656576695489433951602693567143885654771592106690789036275646003378131729522606930818530515414843848039000889531334935427389830473690579523667466182538201372727149023132371319359578146651783732835416323469915494090659780509855937937675396353734377829186029766969614606089327824892671842834136516654569045504808111725705550748907924941183733134599012581542910476929082687043869700761244349471219210833189555347464155979117619898077496880661665775336657207488512148128426326823595335945176245554694022845325705851563290369414226074229552025260849280553835909109839168582914725334143020171520625 

noncomputable def Ns420p16 := nat_lit 702614123509582134195699383225799303120857312948289364169564431944606347230839067212220070086773571232938822231607515388838247088164426860334641427891924556959013106220289292017417932077264689683982462259236603120411894481357554273197237433243865910367073588753830073256225145709268648257922640132615276470163987114280905050307903018021985933333474523803420109333064989110261463867307642914581311357336787925252212965840242792007601256472655504246146516404729632839909377990937267835233434162343951883521915890115762575574377037535717851480622294463860980162526686236248764915916362237196611189536095144270945605478817014333998082847306947436470576941659846222535334992451365706225994338058508887942119777908276510373758951874822816373072605980596581754554466975502415398764501522575 

noncomputable def Ns420p17 := nat_lit 541392566138490077533790984620311058177654278555980714203107761719673916425133183846751239616284470803704371181920004286935467360846628369375164068764590875438310007353955324186636582299553928814156491749519256774653872128089233575343481607925575468185460509172779152955629338248076232826253005811067688706928164570779608774451502836676056177667078421728722179008027603013170304530594440809888606240685402729798990208830923560422594844623819537735750113690675240496626214395332044296593456069970973486809806367897564108502902289348063943342100923856630472249952347312756547637419241376870243223562839253667975765230153074010838184467350558565952691487980795548332122966513692688198426849374346091985539852378055886379210372820263137502377721028428076000707268843323231339375 

noncomputable def Ns420p18 := BSN.log_dyadic_bound Ns420p13 Ns420p14 16 15 Ns420p15 268435456 108160000 Ns420p16 Ns420p17 307286088 Ns420p12 Ns420p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns420p13) (BSN.artanhQ Ns420p14) 0 15 Ns420p16 Ns420p15 Ns420p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns420p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 153643044 134217728 2 134217728 38410761 33554432 1 67108864 (Ns420p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns420p0 Ns420p1 307286088 268435456 1 108160000 Bool.false (BSN.logfrac_isNear Ns420p4 Ns420p5 1 Ns420p0 Ns420p1 307286088 268435456 108160000 rfl rfl rfl (Ns420p11 rfl))) (BSN.isNear_log_sfrac Ns420p2 Ns420p1 307286088 268435456 1 108160000 Bool.false (BSN.logfrac_isNear Ns420p12 Ns420p5 1 Ns420p2 Ns420p1 307286088 268435456 108160000 rfl rfl rfl (Ns420p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS421to432.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 67108864 := Ns420p19 

noncomputable def Ns420p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 16777216 6760000 385100712855 135135 11629079 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz791 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz584 := qz791

noncomputable abbrev qz316 := qz584

noncomputable abbrev qz0 := qz316

theorem RS421to432.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 11629079 16777216 1 6760000 := BSN.isNear_log_sfrac 2 1 11629079 16777216 1 6760000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 11629079 16777216 6760000 rfl rfl rfl (Ns420p20 rfl)) 

theorem RS421to432.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 186065264 268435456 40 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 11629079 16777216 1 6760000 186065264 268435456 40 268435456 RS421to432.d6 rfl 

noncomputable abbrev qz317 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz585 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz586 := (@Nat.cast Real Real.instNatCast 2)

noncomputable def Ns420p21 := @Enclosure.Real.IsNear.inv_image qz585 47453133 33554432 1 33554432 11863282 11863284 16777216 (@Enclosure.Real.IsNear.of_eq qz585 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz586 qz317)) Bool.false 47453133 33554432 1 33554432 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz586 qz317)) Bool.false 47453133 33554432 1 33554432 47453133 33554432 1 33554432 (BSN.sqrt_enclosure 2 1 23726566 23726567 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz587 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS421to432.d8 : Enclosure.Real.IsNear qz587 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz587 Bool.false 23726566 33554432 2 33554432 11863283 16777216 1 16777216 (Ns420p21 rfl rfl) rfl 

theorem RS421to432.d9 : Enclosure.Real.IsNear qz587 Bool.false 189812528 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz587 Bool.false 11863283 16777216 1 16777216 189812528 268435456 16 268435456 RS421to432.d8 rfl 

noncomputable def Ns420p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 16777216 6760000 13079757671720842725 316234143225 18431655 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz318 := (Enclosure.sfrac Bool.false 3 1)

theorem RS421to432.d10 : Enclosure.Real.IsNear (Real.log qz318) Bool.false 18431655 16777216 1 6760000 := BSN.isNear_log_sfrac 3 1 18431655 16777216 1 6760000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 18431655 16777216 6760000 rfl rfl rfl (Ns420p22 rfl)) 

theorem RS421to432.d11 : Enclosure.Real.IsNear (Real.log qz318) Bool.false 294906480 268435456 40 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz318) Bool.false 18431655 16777216 1 6760000 294906480 268435456 40 268435456 RS421to432.d10 rfl 

noncomputable abbrev qz588 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz589 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns420p23 := @Enclosure.Real.IsNear.inv_image qz588 58117981 33554432 1 33554432 9686330 9686331 16777216 (@Enclosure.Real.IsNear.of_eq qz588 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz589 qz317)) Bool.false 58117981 33554432 1 33554432 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz589 qz317)) Bool.false 58117981 33554432 1 33554432 58117981 33554432 1 33554432 (BSN.sqrt_enclosure 3 1 29058990 29058991 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz590 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS421to432.d12 : Enclosure.Real.IsNear qz590 Bool.false 19372661 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz590 Bool.false 19372661 33554432 1 33554432 19372661 33554432 1 33554432 (Ns420p23 rfl rfl) rfl 

theorem RS421to432.d13 : Enclosure.Real.IsNear qz590 Bool.false 154981288 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz590 Bool.false 19372661 33554432 1 33554432 154981288 268435456 8 268435456 RS421to432.d12 rfl 

noncomputable def Ns420p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns420p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns420p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns420p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns420p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns420p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns420p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns420p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns420p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns420p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns420p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns420p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns420p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns420p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns420p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns420p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns420p25 Ns420p26 Ns420p27 Ns420p28 200200021673987500790625 Ns420p29 Ns420p30 Ns420p31 Ns420p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns420p32 Ns420p33 151412625 Ns420p34 Ns420p35 1322214852783825 Ns420p27 Ns420p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns420p32 Ns420p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns420p34 Ns420p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns420p36 Ns420p37 1267389585 Ns420p38 Ns420p39 1927077560082675 Ns420p29 Ns420p30 Ns420p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns420p36 Ns420p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns420p38 Ns420p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz591 := (@Nat.cast Real Real.instNatCast 5)

theorem RS421to432.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz317 qz591)) Bool.false Ns420p24 Ns420p25 1 Ns420p26 := Ns420p40 rfl rfl rfl 

noncomputable def Ns420p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns420p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns420p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns420p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns420p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns420p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns420p25 Ns420p26 Ns420p42 Ns420p43 9945 Ns420p44 Ns420p45 65835 Ns420p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns420p42 Ns420p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns420p44 Ns420p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS421to432.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz317 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns420p41 Ns420p25 1 Ns420p26 := Ns420p46 rfl 

noncomputable def Ns420p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns420p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS421to432.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns420p47 Ns420p25 1 Ns420p48 := BSN.pi_combine Ns420p24 Ns420p41 Ns420p25 Ns420p26 Ns420p48 Ns420p47 rfl rfl rfl rfl RS421to432.d14 RS421to432.d15 

theorem RS421to432.d17 : Enclosure.Real.IsNear Real.pi Bool.false 14148475504056880 4503599627370496 1 4503599627370496 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns420p47 Ns420p25 1 Ns420p48 14148475504056880 4503599627370496 1 4503599627370496 RS421to432.d16 rfl 

noncomputable def Ns420p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns420p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns420p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns420p52 := BSN.log_dyadic_bound 3 5 17 16 Ns420p49 16777216 6760000 Ns420p50 Ns420p51 23258159 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns420p50 Ns420p49 Ns420p51 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz592 := (Enclosure.sfrac Bool.false 4 1)

noncomputable abbrev qz319 := qz592

theorem RS421to432.d18 : Enclosure.Real.IsNear (Real.log qz319) Bool.false 23258159 16777216 1 6760000 := BSN.isNear_log_sfrac 4 1 23258159 16777216 1 6760000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 23258159 16777216 6760000 rfl rfl rfl (Ns420p52 rfl)) 

theorem RS421to432.d19 : Enclosure.Real.IsNear (Real.log qz319) Bool.false 372130544 268435456 40 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz319) Bool.false 23258159 16777216 1 6760000 372130544 268435456 40 268435456 RS421to432.d18 rfl 

noncomputable abbrev qz593 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz594 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns420p53 := @Enclosure.Real.IsNear.inv_image qz593 67108865 33554432 1 33554432 8388607 8388608 16777216 (@Enclosure.Real.IsNear.of_eq qz593 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz594 qz317)) Bool.false 67108865 33554432 1 33554432 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz594 qz317)) Bool.false 67108865 33554432 1 33554432 67108865 33554432 1 33554432 (BSN.sqrt_enclosure 4 1 33554432 33554433 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz595 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS421to432.d20 : Enclosure.Real.IsNear qz595 Bool.false 16777215 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz595 Bool.false 16777215 33554432 1 33554432 16777215 33554432 1 33554432 (Ns420p53 rfl rfl) rfl 

theorem RS421to432.d21 : Enclosure.Real.IsNear qz595 Bool.false 134217720 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz595 Bool.false 16777215 33554432 1 33554432 134217720 268435456 8 268435456 RS421to432.d20 rfl 

noncomputable def Ns420p54 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns420p55 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns420p56 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns420p57 := nat_lit 885951608314392539099884620 

noncomputable def Ns420p58 := nat_lit 1286943652057122751813246125 

noncomputable def Ns420p59 := BSN.log_dyadic_bound 2 3 22 21 Ns420p54 16777216 6760000 Ns420p55 Ns420p56 27001887 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns420p57 Ns420p58 84004523356416638976000 Ns420p55 Ns420p54 Ns420p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns420p57 Ns420p58 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS421to432.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 6760000 := BSN.isNear_log_sfrac 5 1 27001887 16777216 1 6760000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 27001887 16777216 6760000 rfl rfl rfl (Ns420p59 rfl rfl)) 

theorem RS421to432.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 432030192 268435456 40 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 6760000 432030192 268435456 40 268435456 RS421to432.d22 rfl 

noncomputable abbrev qz596 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns420p60 := @Enclosure.Real.IsNear.inv_image qz596 75029991 33554432 1 33554432 7502998 7503000 16777216 (@Enclosure.Real.IsNear.of_eq qz596 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz591 qz317)) Bool.false 75029991 33554432 1 33554432 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz591 qz317)) Bool.false 75029991 33554432 1 33554432 75029991 33554432 1 33554432 (BSN.sqrt_enclosure 5 1 37514995 37514996 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz597 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS421to432.d24 : Enclosure.Real.IsNear qz597 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz597 Bool.false 15005998 33554432 2 33554432 7502999 16777216 1 16777216 (Ns420p60 rfl rfl) rfl 

theorem RS421to432.d25 : Enclosure.Real.IsNear qz597 Bool.false 120047984 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz597 Bool.false 7502999 16777216 1 16777216 120047984 268435456 16 268435456 RS421to432.d24 rfl 

noncomputable def Ns420p61 := BSN.log_dyadic_bound 2 10 6 5 103950000000000 16777216 6760000 1420244935680 967680 6802575 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 2) (BSN.artanhQ 10) 0 5 1420244935680 103950000000000 967680 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz598 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz317)

theorem RS421to432.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 12500000169 84500000000000000 := BSN.isNear_log_sfrac 6 1 4034683545132279 2251799813685248 12500000169 84500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz598) Bool.false 1083052117253279893684224 604462909807314587353088 1000000013520000 6760000000000000000000 4034683545132279 2251799813685248 12500000169 84500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 6802575 16777216 24973259072661432 36028797018963968 6760000 1000000000000000 rfl rfl rfl rfl (Ns420p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS421to432.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 480971758 268435456 41 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 12500000169 84500000000000000 480971758 268435456 41 268435456 RS421to432.d26 rfl 

noncomputable abbrev qz599 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns420p62 := @Enclosure.Real.IsNear.inv_image qz599 82191237 33554432 1 33554432 6849269 6849270 16777216 (@Enclosure.Real.IsNear.of_eq qz599 (Real.sqrt qz598) Bool.false 82191237 33554432 1 33554432 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz598) Bool.false 82191237 33554432 1 33554432 82191237 33554432 1 33554432 (BSN.sqrt_enclosure 6 1 41095618 41095619 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz600 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS421to432.d28 : Enclosure.Real.IsNear qz600 Bool.false 13698539 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz600 Bool.false 13698539 33554432 1 33554432 13698539 33554432 1 33554432 (Ns420p62 rfl rfl) rfl 

theorem RS421to432.d29 : Enclosure.Real.IsNear qz600 Bool.false 109588312 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz600 Bool.false 13698539 33554432 1 33554432 109588312 268435456 8 268435456 RS421to432.d28 rfl 

noncomputable def Ns420p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 16777216 6760000 11010900719820672 5524329195 9388794 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz601 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz317)

theorem RS421to432.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 12500000169 84500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 12500000169 84500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz601) Bool.false 1176230476650867868041216 604462909807314587353088 1000000013520000 6760000000000000000000 4381799983422711 2251799813685248 12500000169 84500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 9388794 16777216 24973259072661432 36028797018963968 6760000 1000000000000000 rfl rfl rfl rfl (Ns420p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS421to432.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 522351262 268435456 41 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 12500000169 84500000000000000 522351262 268435456 41 268435456 RS421to432.d30 rfl 

noncomputable abbrev qz602 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns420p64 := @Enclosure.Real.IsNear.inv_image qz602 88776683 33554432 1 33554432 6341191 6341192 16777216 (@Enclosure.Real.IsNear.of_eq qz602 (Real.sqrt qz601) Bool.false 88776683 33554432 1 33554432 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz601) Bool.false 88776683 33554432 1 33554432 88776683 33554432 1 33554432 (BSN.sqrt_enclosure 7 1 44388341 44388342 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz603 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS421to432.d32 : Enclosure.Real.IsNear qz603 Bool.false 12682383 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz603 Bool.false 12682383 33554432 1 33554432 12682383 33554432 1 33554432 (Ns420p64 rfl rfl) rfl 

theorem RS421to432.d33 : Enclosure.Real.IsNear qz603 Bool.false 101459064 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz603 Bool.false 12682383 33554432 1 33554432 101459064 268435456 8 268435456 RS421to432.d32 rfl 

noncomputable def Ns420p65 := nat_lit 1256945285058001618599936 

noncomputable def Ns420p66 := BSN.log_dyadic_bound 0 16 1 0 1 16777216 6760000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz320 := (Enclosure.sfrac Bool.false 8 1)

noncomputable abbrev qz604 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz317)

theorem RS421to432.d34 : Enclosure.Real.IsNear (Real.log qz320) Bool.false 9364972152248037 4503599627370496 25000000507 169000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 25000000507 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz604) Bool.false Ns420p65 604462909807314587353088 1000000020280000 6760000000000000000000 9364972152248037 4503599627370496 25000000507 169000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 16777216 24973259072661432 36028797018963968 6760000 1000000000000000 rfl rfl rfl rfl (Ns420p66 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS421to432.d35 : Enclosure.Real.IsNear (Real.log qz320) Bool.false 558195838 268435456 41 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz320) Bool.false 9364972152248037 4503599627370496 25000000507 169000000000000000 558195838 268435456 41 268435456 RS421to432.d34 rfl 

noncomputable abbrev qz605 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns420p67 := @Enclosure.Real.IsNear.inv_image qz605 94906265 33554432 1 33554432 5931641 5931642 16777216 (@Enclosure.Real.IsNear.of_eq qz605 (Real.sqrt qz604) Bool.false 94906265 33554432 1 33554432 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz604) Bool.false 94906265 33554432 1 33554432 94906265 33554432 1 33554432 (BSN.sqrt_enclosure 8 1 47453132 47453133 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz606 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS421to432.d36 : Enclosure.Real.IsNear qz606 Bool.false 11863283 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz606 Bool.false 11863283 33554432 1 33554432 11863283 33554432 1 33554432 (Ns420p67 rfl rfl) rfl 

theorem RS421to432.d37 : Enclosure.Real.IsNear qz606 Bool.false 94906264 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz606 Bool.false 11863283 33554432 1 33554432 94906264 268435456 8 268435456 RS421to432.d36 rfl 

noncomputable def Ns420p68 := nat_lit 1328140746012062765809664 

noncomputable def Ns420p69 := BSN.log_dyadic_bound 1 17 3 2 1252815 16777216 6760000 1448 3 1976071 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz607 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz317)

theorem RS421to432.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 25000000507 169000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 25000000507 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz607) Bool.false Ns420p68 604462909807314587353088 1000000020280000 6760000000000000000000 9895419672221413 4503599627370496 25000000507 169000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 1976071 16777216 24973259072661432 36028797018963968 6760000 1000000000000000 rfl rfl rfl rfl (Ns420p69 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS421to432.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 589812974 268435456 41 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 25000000507 169000000000000000 589812974 268435456 41 268435456 RS421to432.d38 rfl 

noncomputable abbrev qz608 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns420p70 := @Enclosure.Real.IsNear.inv_image qz608 100663297 33554432 1 33554432 5592405 5592406 16777216 (@Enclosure.Real.IsNear.of_eq qz608 (Real.sqrt qz607) Bool.false 100663297 33554432 1 33554432 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz607) Bool.false 100663297 33554432 1 33554432 100663297 33554432 1 33554432 (BSN.sqrt_enclosure 9 1 50331648 50331649 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz609 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS421to432.d40 : Enclosure.Real.IsNear qz609 Bool.false 11184811 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz609 Bool.false 11184811 33554432 1 33554432 11184811 33554432 1 33554432 (Ns420p70 rfl rfl) rfl 

theorem RS421to432.d41 : Enclosure.Real.IsNear qz609 Bool.false 89478488 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz609 Bool.false 11184811 33554432 1 33554432 89478488 268435456 8 268435456 RS421to432.d40 rfl 

noncomputable def Ns420p71 := nat_lit 1391827265235416537628672 

noncomputable def Ns420p72 := BSN.log_dyadic_bound 2 18 4 3 3571283520 16777216 6760000 14806464 960 3743727 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz610 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz317)

theorem RS421to432.d42 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921216632549 4503599627370496 25000000507 169000000000000000 := BSN.isNear_log_sfrac 10 1 10369921216632549 4503599627370496 25000000507 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz610) Bool.false Ns420p71 604462909807314587353088 1000000020280000 6760000000000000000000 10369921216632549 4503599627370496 25000000507 169000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 3743727 16777216 24973259072661432 36028797018963968 6760000 1000000000000000 rfl rfl rfl rfl (Ns420p72 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS421to432.d43 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 618095470 268435456 41 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921216632549 4503599627370496 25000000507 169000000000000000 618095470 268435456 41 268435456 RS421to432.d42 rfl 

noncomputable abbrev qz611 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns420p73 := @Enclosure.Real.IsNear.inv_image qz611 106108431 33554432 1 33554432 5305421 5305422 16777216 (@Enclosure.Real.IsNear.of_eq qz611 (Real.sqrt qz610) Bool.false 106108431 33554432 1 33554432 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz610) Bool.false 106108431 33554432 1 33554432 106108431 33554432 1 33554432 (BSN.sqrt_enclosure 10 1 53054215 53054216 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz612 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS421to432.d44 : Enclosure.Real.IsNear qz612 Bool.false 10610843 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz612 Bool.false 10610843 33554432 1 33554432 10610843 33554432 1 33554432 (Ns420p73 rfl rfl) rfl 

theorem RS421to432.d45 : Enclosure.Real.IsNear qz612 Bool.false 84886744 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz612 Bool.false 10610843 33554432 1 33554432 84886744 268435456 8 268435456 RS421to432.d44 rfl 

noncomputable def Ns420p74 := nat_lit 1449438752820620681019392 

noncomputable def Ns420p75 := BSN.log_dyadic_bound 3 19 5 4 16049467073745 16777216 6760000 135406373544 688905 5342767 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 19) 0 4 135406373544 16049467073745 688905 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz792 := (Enclosure.sfrac Bool.false 11 1)

noncomputable abbrev qz613 := qz792

noncomputable abbrev qz321 := qz613

noncomputable abbrev qz1 := qz321

noncomputable abbrev qz614 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11) qz317)

theorem RS421to432.d46 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 10799160248194789 4503599627370496 25000000507 169000000000000000 := BSN.isNear_log_sfrac 11 1 10799160248194789 4503599627370496 25000000507 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz614) Bool.false Ns420p74 604462909807314587353088 1000000020280000 6760000000000000000000 10799160248194789 4503599627370496 25000000507 169000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 5342767 16777216 24973259072661432 36028797018963968 6760000 1000000000000000 rfl rfl rfl rfl (Ns420p75 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS421to432.d47 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 643680110 268435456 41 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 10799160248194789 4503599627370496 25000000507 169000000000000000 643680110 268435456 41 268435456 RS421to432.d46 rfl 

noncomputable abbrev qz615 := (Real.sqrt (@Nat.cast Real Real.instNatCast 11))

noncomputable def Ns420p76 := @Enclosure.Real.IsNear.inv_image qz615 111287461 33554432 1 33554432 5058520 5058521 16777216 (@Enclosure.Real.IsNear.of_eq qz615 (Real.sqrt qz614) Bool.false 111287461 33554432 1 33554432 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz614) Bool.false 111287461 33554432 1 33554432 111287461 33554432 1 33554432 (BSN.sqrt_enclosure 11 1 55643730 55643731 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz616 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

theorem RS421to432.d48 : Enclosure.Real.IsNear qz616 Bool.false 10117041 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz616 Bool.false 10117041 33554432 1 33554432 10117041 33554432 1 33554432 (Ns420p76 rfl rfl) rfl 

theorem RS421to432.d49 : Enclosure.Real.IsNear qz616 Bool.false 80936328 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz616 Bool.false 10117041 33554432 1 33554432 80936328 268435456 8 268435456 RS421to432.d48 rfl 

theorem RS421to432.d50 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz793 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz617 := qz793

noncomputable abbrev qz322 := qz617

noncomputable abbrev qz2 := qz322

noncomputable abbrev qz323 := (Enclosure.Real.IsNear.const Bool.false 2 1)

theorem RS421to432.d51 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 qz323 RS421to432.d50 rfl 

noncomputable abbrev qz324 := (@Inv.inv Real Real.instInv qz617)

noncomputable abbrev qz3 := qz324

theorem RS421to432.d52 : Enclosure.Real.IsNear qz3 Bool.false 5340353 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 5340353 33554432 1 33554432 5340353 33554432 1 33554432 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 2670176 2670177 16777216 RS421to432.d51 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns420p77 := nat_lit 249399979876553137848320000 

noncomputable def Ns420p78 := nat_lit 356476032352066574394486423552 

noncomputable abbrev qz794 := (Enclosure.sfrac Bool.false 775738 1000)

noncomputable abbrev qz618 := qz794

noncomputable abbrev qz325 := qz618

noncomputable abbrev qz4 := qz325

noncomputable abbrev qz795 := (@instHMul Real Real.instMul)

noncomputable abbrev qz619 := qz795

noncomputable abbrev qz326 := qz619

noncomputable abbrev qz5 := qz326

noncomputable abbrev qz620 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 11)

noncomputable abbrev qz6 := qz620

noncomputable abbrev qz796 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 775738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz621 := qz796

noncomputable abbrev qz327 := qz621

noncomputable abbrev qz7 := qz327

noncomputable abbrev qz328 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz8 := qz328

noncomputable abbrev qz797 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 775738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz622 := qz797

noncomputable abbrev qz329 := qz622

noncomputable abbrev qz9 := qz329

noncomputable abbrev qz623 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz330 := (@HPow.hPow Real Real Real qz623 qz7 qz8)

noncomputable def Ns420p79 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz330) (Zeta.RiemannSiegel.correction qz9)) 103278745 134217728 149359 134217728 977844383036899431581 4722366482869645213696 1262234443748410166231 Ns420p77 Ns420p78 

noncomputable def Ns420p80 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 775738 1000 195 242 268435456 134217728 4503599627370496 Bool.false 397201607245 2526 

noncomputable def Ns420p81 := Ns420p80 618095470 41 84886744 8 643680110 41 80936328 8 Bool.true 43687339 128132 Bool.true 55337949 Bool.true 84416285 14148475504056880 1 Bool.false 54946824 Bool.false Bool.false 255271072 Bool.true Bool.true 103278745 

noncomputable def Ns420p82 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 775738 1000 84 143 268435456 134217728 4503599627370496 Bool.false 397201607245 2526 

noncomputable def Ns420p83 := Ns420p82 558195838 41 94906264 8 589812974 41 89478488 8 Bool.true 67687956 104531 Bool.true 392891759 Bool.true 41717337 14148475504056880 1 Bool.false 28710646 Bool.false Bool.false 41549613 Bool.false Bool.true 43687339 

noncomputable def Ns420p84 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 775738 1000 57 18 268435456 134217728 4503599627370496 Bool.false 397201607245 2526 

noncomputable def Ns420p85 := Ns420p84 480971758 41 109588312 8 522351262 41 101459064 8 Bool.true 41737722 77519 Bool.false 59064226 Bool.true 416282327 14148475504056880 1 Bool.false 58588790 Bool.true Bool.false 5374742 Bool.true Bool.true 67687956 

noncomputable def Ns420p86 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 775738 1000 257 147 268435456 134217728 4503599627370496 Bool.false 397201607245 2526 

noncomputable def Ns420p87 := Ns420p86 372130544 40 134217720 8 432030192 40 120047984 16 Bool.false 125046 45706 Bool.false 159844239 Bool.false 75728208 14148475504056880 1 Bool.false 150564043 Bool.true Bool.false 74727715 Bool.false Bool.true 41737722 

noncomputable def Ns420p88 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 775738 1000 599 399 268435456 134217728 4503599627370496 Bool.false 397201607245 2526 

noncomputable def Ns420p89 := Ns420p88 186065264 40 189812528 16 294906480 40 154981288 8 Bool.true 268435272 2576 Bool.false 290911948 Bool.false 190130384 14148475504056880 1 Bool.false 237219205 Bool.false Bool.false 174627111 Bool.false Bool.false 125046 

noncomputable def Ns420p90 := nat_lit 408426922860974156696753275280885714841612954492488823743 

noncomputable def Ns420p91 := nat_lit 276021711092840180660157146494035567571507523616768000 

noncomputable def Ns420p92 := nat_lit 134839466387321508525221253360640000 

noncomputable def Ns420p93 := nat_lit 627600709533090095328946396180152913920 

noncomputable abbrev qz10 := (@Eq.refl Real qz325)

noncomputable def Ns420p94 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 775738 1000 2407078778576 16000000 1551476 4000 2000 Ns420p92 Ns420p93 qz10 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns420p95 := nat_lit 8364583380192750729149507077752539439956233308006171110256640 

noncomputable abbrev qz798 := (@instHSub Real Real.instSub)

noncomputable abbrev qz624 := qz798

noncomputable abbrev qz331 := qz624

noncomputable abbrev qz11 := qz331

noncomputable abbrev qz625 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz626 := (@HMul.hMul Real Real Real qz795 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz627 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz332 := (@HMul.hMul Real Real Real qz619 qz625 (@HSub.hSub Real Real Real qz624 qz626 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 (@Nat.cast Real Real.instNatCast 1551476)))))

noncomputable abbrev qz628 := (Real.log (Enclosure.sfrac Bool.false 2407078778576 16000000))

noncomputable abbrev qz629 := (Enclosure.sfrac Bool.false 775738 2000)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 775738 4000) qz628) qz332) qz629)

noncomputable abbrev qz333 := (@HSub.hSub Real Real Real qz11 qz12 (@HMul.hMul Real Real Real qz5 qz629 (Real.log Real.pi)))

noncomputable def Ns420p96 := @Enclosure.Real.IsNear.addLit_ft_p qz333 (Enclosure.sfrac Bool.true Ns420p92 Ns420p93) 13327876255814958072267 9007199254740992000 3254404945285634913 346112000000000000000000 Ns420p92 Ns420p93 0 1 Ns420p95 

noncomputable def Ns420p97 := nat_lit 447209317530157615218734137344000 

noncomputable abbrev qz334 := (@HMul.hMul Real Real Real qz5 qz629 (Real.log Real.pi))

noncomputable def Ns420p98 := @Enclosure.Real.IsNear.subLit_ff_p qz12 qz334 17327119875690751476171 9007199254740992000 1224591739389887 338000000000000000000 14898343458309 33554432000 387869 67108864000 Ns420p97 13327876255814958072267 9007199254740992000 

noncomputable def Ns420p99 := nat_lit 34654239751381502952342000 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 775738 4000) qz628) qz332)

noncomputable def Ns420p100 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz629 20820733243427885302219 9007199254740992000 1224591739389887 338000000000000000000 775738 2000 0 1 Ns420p99 17327119875690751476171 9007199254740992000 1224591739389887 338000000000000000000 

noncomputable def Ns420p101 := nat_lit 46884123238341161416114664232621965312 

noncomputable def Ns420p102 := nat_lit 57648042210054944455655424 

noncomputable def Ns420p103 := nat_lit 4835703278458516698824704 

noncomputable def Ns420p104 := nat_lit 876825360601704119119142878742145588516225982903839399546691782815477378580480 

noncomputable def Ns420p105 := nat_lit 1387729766705777826557528531728360385056786108874547830532121728711860944896 

noncomputable def Ns420p106 := nat_lit 13293699947179366220589089664815033055460165535603225107528449408368640 

noncomputable def Ns420p107 := BSN.log_dyadic_bound 309926778576 4504230778576 4 3 Ns420p104 134217728 54080000 Ns420p105 Ns420p106 18499719 4814157557152 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 309926778576) (BSN.artanhQ 4504230778576) 0 3 Ns420p105 Ns420p104 Ns420p106 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz335 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns420p108 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 775738 4000) qz628 775738 4000 0 1 53688923092610151 4503599627370496 3125002873 169000000000000000 20824268911007606658219 9007199254740992000 1212091739347637 338000000000000000000 (Enclosure.Real.IsNear.const Bool.false 775738 4000) (BSN.isNear_log_sfrac 2407078778576 16000000 53688923092610151 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2407078778576) qz335)) Bool.false Ns420p102 Ns420p103 1000000919360000 54080000000000000000000 53688923092610151 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2407078778576 16000000 17 4814157557152 4194304000000 18499719 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns420p107 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns420p109 := BSN.arctan_dyadic_bound_f 1000 1551476 1 0 16777216 6760000 0 1 1 0 1 1 10813 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1551476) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1551476) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := qz626

noncomputable abbrev qz14 := qz336

noncomputable abbrev qz337 := qz627

noncomputable abbrev qz15 := qz337

noncomputable abbrev qz630 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz338 := qz630

noncomputable abbrev qz16 := (@Enclosure.Real.IsNear.mulLit_ff qz338 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def Ns420p110 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1551476))) 884279719003555 562949953421312 1 2000000000000000 10813 16777216 1 6760000 14829664672295602356224 883916894930339 562949953421312 50000000169 338000000000000000 qz16 (Ns420p109 rfl) rfl rfl 

noncomputable abbrev qz17 := qz332

noncomputable abbrev qz339 := qz625

noncomputable abbrev qz18 := qz339

noncomputable abbrev qz340 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns420p111 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 775738 4000) qz628) qz17 20824268911007606658219 9007199254740992000 1212091739347637 338000000000000000000 883916894930339 2251799813685248 50000000169 1352000000000000000 Ns420p101 20820733243427885302219 9007199254740992000 1224591739389887 338000000000000000000 (Ns420p108 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1551476)))) 1 4 0 1 883916894930339 562949953421312 50000000169 338000000000000000 883916894930339 2251799813685248 50000000169 1352000000000000000 qz340 Ns420p110 rfl) 

noncomputable def Ns420p112 := @Ns420p96 Ns420p90 Ns420p91 3254404945285634913 346112000000000000000000 (@Ns420p98 3254404945285634913 346112000000000000000000 (Ns420p100 (Ns420p111 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 775738 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz629 (Real.log Real.pi) 775738 2000 0 1 38410761 33554432 1 67108864 14898343458309 33554432000 387869 67108864000 (Enclosure.Real.IsNear.const Bool.false 775738 2000) RS421to432.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns420p92 Ns420p93) 

noncomputable abbrev qz341 := (@instHAdd Real Real.instAdd)

noncomputable def Ns420p113 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns420p90 Ns420p91 3254404945285634913 346112000000000000000000 49650200905 33554432 317 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz341 qz333 (Enclosure.sfrac Bool.true Ns420p92 Ns420p93)) Bool.false Ns420p90 Ns420p91 3254404945285634913 346112000000000000000000 Ns420p94 (Ns420p112 rfl rfl)) 

noncomputable def Ns420p114 := BSN.cos_dyadic_bound_f 79312162 68719476736 1 0 33554432 13533204 0 1 1 0 1 1 33554409 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 79312162) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 79312162) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable abbrev qz342 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable abbrev qz343 := (@Nat.cast Real Real.instNatCast Ns420p103)

noncomputable def Ns420p115 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49650200905) qz342) Bool.false 49650200905 33554432 317 33554432 Bool.true 33554409 33554432 1 6760000 (Ns420p113 rfl) (Enclosure.sfrac_false_div 49650200905 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49650200905) qz342) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5581097242817346928640) qz343) 226375608064910080 72057594037927936 Bool.false 33554409 33554432 235 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q2 49650200905 33554432 226375608064910080 72057594037927936 235 5581097242817346928640 Ns420p103 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554409 33554432 5581097242817346928640 Ns420p103 79312162 68719476736 13533204 13520000 (Ns420p114 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns420p116 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns420p90 Ns420p91 3254404945285634913 346112000000000000000000 397201607245 268435456 2526 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz341 qz333 (Enclosure.sfrac Bool.true Ns420p92 Ns420p93)) Bool.false Ns420p90 Ns420p91 3254404945285634913 346112000000000000000000 Ns420p94 (Ns420p112 rfl rfl)) 

noncomputable def Ns420p117 := Ns420p89 45706 BSN.abs_quadSignPos (BSN.cos_quad_nat3 599 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 237219205 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 399 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 174627111 268435456) qz10 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 33554409 33554432 34007413 3544186880000 268435272 268435456 2576 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554409 33554432 34007413 3544186880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554409 33554432 2176474432 226827960320000 33554409 33554432 34007413 3544186880000 (Ns420p115 rfl rfl) rfl)) rfl) (Ns420p116 rfl) RS421to432.d7 

noncomputable def Ns420p118 := nat_lit 112508566696410213696321727385812038823403207950685193758149466268958720 

noncomputable def Ns420p119 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080 

noncomputable def Ns420p120 := nat_lit 51297059130207336992055993936474518056537458344113563581069572243456 

noncomputable def Ns420p121 := nat_lit 294582241347244509706665004877420095317774007795427895025545918063640576 

noncomputable def Ns420p122 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800 

noncomputable abbrev qz344 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz345 := (BSN.sinOddQ 268435456)

noncomputable def Ns420p123 := BSN.sin_dyadic_bound_f 290911948 268435456 3 2 268435456 134217728 Ns420p118 Ns420p119 Ns420p120 Ns420p121 Ns420p122 Ns420p120 237219205 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 290911948) qz344 0 2 Ns420p118 Ns420p119 Ns420p120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 290911948) qz345 0 2 Ns420p121 Ns420p122 Ns420p120 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p124 := nat_lit 20520292456891402904823881469276633864281382514908342781068725337456640 

noncomputable def Ns420p125 := nat_lit 1707702454509329240192995194036792926737350181005157720522642948096 

noncomputable def Ns420p126 := nat_lit 53740858249789230598626043760648457694093665162562127504584863033327616 

noncomputable def Ns420p127 := BSN.sin_dyadic_bound_f 190130384 268435456 3 2 268435456 134217728 Ns420p124 Ns420p119 Ns420p125 Ns420p126 Ns420p122 Ns420p125 174627111 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 190130384) qz344 0 2 Ns420p124 Ns420p119 Ns420p125 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 190130384) qz345 0 2 Ns420p126 Ns420p122 Ns420p125 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p128 := nat_lit 10250553355917339760304392219687782394694939493583922156250155815247745 

noncomputable def Ns420p129 := nat_lit 426163162558489387538434819415192652196952116292963785419557674881 

noncomputable def Ns420p130 := nat_lit 26845997382282223722741203109474662626573665513102940848812109756080001 

noncomputable def Ns420p131 := BSN.sin_dyadic_bound_f 159844239 268435456 3 2 268435456 134217728 Ns420p128 Ns420p119 Ns420p129 Ns420p130 Ns420p122 Ns420p129 150564043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 159844239) qz344 0 2 Ns420p128 Ns420p119 Ns420p129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 159844239) qz345 0 2 Ns420p130 Ns420p122 Ns420p129 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p132 := nat_lit 32887489311531301118910959517696 

noncomputable def Ns420p133 := nat_lit 623075623024179315423659559506411520 

noncomputable def Ns420p134 := nat_lit 4361529361169255207965616916544880640 

noncomputable def Ns420p135 := BSN.sin_dyadic_bound_f 75728208 268435456 2 1 268435456 134217728 Ns420p132 Ns420p133 Ns420p132 Ns420p132 Ns420p134 Ns420p132 74727715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 75728208) qz344 0 1 Ns420p132 Ns420p133 Ns420p132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 75728208) qz345 0 1 Ns420p132 Ns420p134 Ns420p132 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p136 := Ns420p87 77519 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 257 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 150564043 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 74727715 268435456) qz10 rfl rfl (Ns420p117 RS421to432.d9 RS421to432.d11 RS421to432.d13 RS421to432.d17 (Ns420p123 rfl rfl) (Ns420p127 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns420p116 rfl) RS421to432.d19 RS421to432.d21 RS421to432.d23 RS421to432.d25 RS421to432.d17 (Ns420p131 rfl rfl) (Ns420p135 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns420p137 := nat_lit 12170209903469690636278973813776 

noncomputable def Ns420p138 := BSN.sin_dyadic_bound_f 59064226 268435456 2 1 268435456 134217728 Ns420p137 Ns420p133 Ns420p137 Ns420p137 Ns420p134 Ns420p137 58588790 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 59064226) qz344 0 1 Ns420p137 Ns420p133 Ns420p137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 59064226) qz345 0 1 Ns420p137 Ns420p134 Ns420p137 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p139 := nat_lit 16213989724698149069961087935414691035343321027687851692282389228288014256986873544213729370107424593664111201 

noncomputable def Ns420p140 := nat_lit 67052582193422231333984484018745857420694574238012043916021913709013615522643186318434558042568065189255577600 

noncomputable def Ns420p141 := nat_lit 27080437915116374181380725232645203650333652471335259188375766074439814055780029036601232801861426573921 

noncomputable def Ns420p142 := nat_lit 98139756531699548628713734291909969857552543590172379404951629646168049268302411902677715003568651813198852705 

noncomputable def Ns420p143 := nat_lit 6101784979601423051392588045705873025283206255659095996357994147520239012560529954977544781873693932222257561600 

noncomputable abbrev qz346 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz347 := (BSN.cosOddQ 268435456)

noncomputable def Ns420p144 := BSN.cos_dyadic_bound_f 416282327 268435456 4 3 268435456 134217728 Ns420p139 Ns420p140 Ns420p141 Ns420p142 Ns420p143 Ns420p141 5374742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 416282327) qz346 0 3 Ns420p139 Ns420p140 Ns420p141 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 416282327) qz347 0 3 Ns420p142 Ns420p143 Ns420p141 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p145 := Ns420p85 104531 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58588790 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 5374742 268435456) qz10 rfl rfl (Ns420p136 rfl rfl) (Ns420p116 rfl) RS421to432.d27 RS421to432.d29 RS421to432.d31 RS421to432.d33 RS421to432.d17 (Ns420p138 rfl rfl) (Ns420p144 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p146 := nat_lit 12856465929299612860452176080705678979081924154748507690063325258114273750768006780774970182705814970458144961 

noncomputable def Ns420p147 := nat_lit 13529290863878244545661099054561793022272423647328743286934262348038431102109029208415934884976439820481 

noncomputable def Ns420p148 := nat_lit 77854174232140715006869752582262586408949909781444235671007181896589229650952458258298629718477021901501202625 

noncomputable def Ns420p149 := BSN.cos_dyadic_bound_f 392891759 268435456 4 3 268435456 134217728 Ns420p146 Ns420p140 Ns420p147 Ns420p148 Ns420p143 Ns420p147 28710646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 392891759) qz346 0 3 Ns420p146 Ns420p140 Ns420p147 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 392891759) qz347 0 3 Ns420p148 Ns420p143 Ns420p147 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p150 := nat_lit 3028770111207784403592491521761 

noncomputable def Ns420p151 := BSN.sin_dyadic_bound_f 41717337 268435456 2 1 268435456 134217728 Ns420p150 Ns420p133 Ns420p150 Ns420p150 Ns420p134 Ns420p150 41549613 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 41717337) qz344 0 1 Ns420p150 Ns420p133 Ns420p150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 41717337) qz345 0 1 Ns420p150 Ns420p134 Ns420p150 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p152 := Ns420p83 128132 BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 28710646 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 143 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 41549613 268435456) qz10 rfl rfl (Ns420p145 rfl) (Ns420p116 rfl) RS421to432.d35 RS421to432.d37 RS421to432.d39 RS421to432.d41 RS421to432.d17 (Ns420p149 rfl rfl) (Ns420p151 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p153 := nat_lit 9377611466790591278321306613201 

noncomputable def Ns420p154 := BSN.sin_dyadic_bound_f 55337949 268435456 2 1 268435456 134217728 Ns420p153 Ns420p133 Ns420p153 Ns420p153 Ns420p134 Ns420p153 54946824 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 55337949) qz344 0 1 Ns420p153 Ns420p133 Ns420p153 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 55337949) qz345 0 1 Ns420p153 Ns420p134 Ns420p153 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p155 := nat_lit 442971991644009470786684266642255235152326267826086099818255096190625 

noncomputable def Ns420p156 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120 

noncomputable def Ns420p157 := nat_lit 2578753830728217755778063904237494253803412486985765176875390625 

noncomputable def Ns420p158 := nat_lit 1328910817424366955924541243798957230468471196653284327924411537790625 

noncomputable def Ns420p159 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400 

noncomputable def Ns420p160 := BSN.cos_dyadic_bound_f 84416285 268435456 3 2 268435456 134217728 Ns420p155 Ns420p156 Ns420p157 Ns420p158 Ns420p159 Ns420p157 255271072 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 84416285) qz346 0 2 Ns420p155 Ns420p156 Ns420p157 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 84416285) qz347 0 2 Ns420p158 Ns420p159 Ns420p157 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz348 := (BSN.cos_quad_nat2 242 rfl)

noncomputable def Ns420p161 := Ns420p81 149359 BSN.abs_quadSignPos (BSN.cos_quad_nat3 195 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 54946824 268435456) BSN.abs_quadSignNeg qz348 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 255271072 268435456) qz10 rfl rfl (Ns420p152 rfl) (Ns420p116 rfl) RS421to432.d43 RS421to432.d45 RS421to432.d47 RS421to432.d49 RS421to432.d17 (Ns420p154 rfl rfl) (Ns420p160 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p162 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 11) 103278745 268435456 149359 268435456 103278745 268435456 149359 268435456 55447354018365440 103278745 134217728 149359 134217728 (Ns420p161 rfl) 

noncomputable def Ns420p163 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz330) (Zeta.RiemannSiegel.correction qz9) 10066213 33554432 1 33554432 97141237030937 140737488355328 499534054081391 29730794415063040000 977844383036899431581 4722366482869645213696 

noncomputable def Ns420p164 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz330 1 1 0 1 10066213 33554432 1 33554432 10066213 33554432 1 33554432 

noncomputable abbrev qz19 := (@Enclosure.Real.IsNear.of_eq qz327 (@HMul.hMul Real Real Real qz326 qz325 qz324) Bool.false 2071357377757 16777216000 387869 16777216000 (BSN.t_div_two_pi_mk qz325 775738 1000 (@Eq.refl Real qz325)) (@Enclosure.Real.IsNear.mulLit_ff qz325 qz324 775738 1000 0 1 5340353 33554432 1 33554432 2071357377757 16777216000 387869 16777216000 (Enclosure.Real.IsNear.const Bool.false 775738 1000) RS421to432.d52 rfl))

noncomputable def Ns420p165 := @Enclosure.Real.IsNear.sqrt_image qz7 2071357377757 16777216000 387869 16777216000 186417820 186417855 16777216 qz19 

noncomputable abbrev qz799 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 775738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz631 := qz799

noncomputable abbrev qz349 := qz631

noncomputable abbrev qz20 := qz349

noncomputable def Ns420p166 := @Enclosure.Real.IsNear.sqrt_image qz20 372835675 33554432 35 33554432 55924699 55924705 16777216 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 372835675 33554432 35 33554432 372835675 33554432 35 33554432 (Ns420p165 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz800 := (Real.sqrt (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 775738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))))

noncomputable abbrev qz632 := qz800

noncomputable abbrev qz350 := qz632

noncomputable abbrev qz21 := qz350

noncomputable def Ns420p167 := @Enclosure.Real.IsNear.inv_image qz21 27962351 8388608 3 16777216 5033106 5033107 16777216 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 111849404 33554432 6 33554432 27962351 8388608 3 16777216 (Ns420p166 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p168 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz21) Bool.false 10066213 33554432 1 33554432 10066213 33554432 1 33554432 (Ns420p167 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz326 qz322 qz329)

noncomputable abbrev qz633 := (@HMul.hMul Real Real Real qz795 qz797 qz797)

noncomputable abbrev qz634 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz351 := (@HSub.hSub Real Real Real qz624 (@HSub.hSub Real Real Real qz624 qz633 qz622) qz634)

noncomputable abbrev qz23 := (Real.cos (@HMul.hMul Real Real Real qz326 qz322 qz351))

noncomputable def Ns420p169 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz9) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz22)) qz23) Bool.false 97141237030937 

noncomputable def Ns420p170 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz22)) qz23 43861891 33554432 387 

noncomputable def Ns420p171 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz22)) Bool.false 43861891 33554432 387 33554432 43861891 33554432 387 

noncomputable def Ns420p172 := @Enclosure.Real.IsNear.recentre' (Real.cos qz22) Bool.false 12834603 16777216 1527514432 226827960320000 12834603 16777216 23867413 3544186880000 

noncomputable def Ns420p173 := @Enclosure.Real.IsNear.cos_image qz22 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23479779) qz342) Bool.false 23479779 33554432 221 33554432 Bool.false 12834603 16777216 1 

noncomputable def Ns420p174 := nat_lit 944512639348641515076254261 

noncomputable def Ns420p175 := nat_lit 144115188075855872000000000000000 

noncomputable def Ns420p176 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz9 884279719003555 140737488355328 1 500000000000000 3736923 33554432 35 33554432 3304485220377921761265 4722366482869645213696 Ns420p174 

noncomputable def Ns420p177 := @Enclosure.Real.IsNear.subLit_ff_p qz20 qz1 372835675 33554432 35 33554432 11 1 0 1 3736923 3736923 33554432 35 

noncomputable abbrev qz352 := (Enclosure.Real.IsNear.const Bool.false 11 1)

noncomputable def Ns420p178 := @Ns420p177 33554432 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 372835675 33554432 35 33554432 372835675 33554432 35 33554432 (Ns420p165 rfl rfl rfl rfl rfl rfl) rfl) qz352 

noncomputable def Ns420p179 := @Enclosure.Real.IsNear.recentre' qz22 Bool.false 3304485220377921761265 4722366482869645213696 Ns420p174 Ns420p175 23479779 33554432 221 33554432 (@Ns420p176 Ns420p175 RS421to432.d51 (Ns420p178 rfl rfl) rfl) 

noncomputable def Ns420p180 := nat_lit 647361463836816835013205887578273335239320687570777768057147041 

noncomputable def Ns420p181 := nat_lit 64791741944522487909851911563195676133695224709322207119351480320 

noncomputable def Ns420p182 := nat_lit 92374486856818440391660383762019044896047455534068830604961 

noncomputable def Ns420p183 := nat_lit 1941899642536736868158834341967295967628169967801265166510231201 

noncomputable def Ns420p184 := nat_lit 2915628387503511955943336020343805426016285111919499320370816614400 

noncomputable abbrev qz635 := (BSN.cosEvenQ 33554432)

noncomputable def Ns420p185 := BSN.cos_dyadic_bound_f 23479779 33554432 3 2 16777216 6760000 Ns420p180 Ns420p181 Ns420p182 Ns420p183 Ns420p184 Ns420p182 12834603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 23479779) qz635 0 2 Ns420p180 Ns420p181 Ns420p182 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 23479779) (BSN.cosOddQ 33554432) 0 2 Ns420p183 Ns420p184 Ns420p182 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p186 := @Enclosure.Real.IsNear.inv_image (Real.cos qz22) 12834603 16777216 23867413 3544186880000 21930752 21931139 16777216 (Ns420p172 (@Ns420p173 6760000 (Ns420p179 rfl) (Enclosure.sfrac_false_div 23479779 33554432) (Ns420p185 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns420p187 := @Enclosure.Real.IsNear.recentre' qz23 Bool.false 8858828 16777216 

noncomputable abbrev qz24 := (@HMul.hMul Real Real Real qz326 qz322 qz351)

noncomputable def Ns420p188 := @Enclosure.Real.IsNear.cos_image qz24 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 34041655)) qz342) Bool.true 34041655 33554432 

noncomputable def Ns420p189 := nat_lit 160757171127043434399782584405 

noncomputable def Ns420p190 := nat_lit 158456325028528675187087900672 

noncomputable def Ns420p191 := nat_lit 38751760199896777157141814358190317 

noncomputable def Ns420p192 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true Ns420p189 Ns420p190 Ns420p191 

noncomputable def Ns420p193 := nat_lit 4835703278458516698824704000000000000000 

noncomputable abbrev qz25 := qz351

noncomputable def Ns420p194 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz25 884279719003555 140737488355328 1 500000000000000 181794479362471 

noncomputable abbrev qz353 := (@HSub.hSub Real Real Real qz624 qz633 qz622)

noncomputable abbrev qz26 := qz353

noncomputable abbrev qz354 := qz634

noncomputable abbrev qz27 := qz354

noncomputable def Ns420p195 := @Enclosure.Real.IsNear.subLit_tf qz26 qz27 111425735184807 1125899906842624 1435990955 1125899906842624 1 16 

noncomputable abbrev qz355 := qz633

noncomputable abbrev qz28 := qz355

noncomputable def Ns420p196 := @Enclosure.Real.IsNear.subLit_ff_n qz28 qz9 13964593507929 1125899906842624 261585835 1125899906842624 3736923 33554432 35 33554432 

noncomputable def Ns420p197 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz9 3736923 33554432 35 33554432 3736923 33554432 35 33554432 13964593507929 1125899906842624 

noncomputable def Ns420p198 := nat_lit 2861707746579355030262856872096609932867720134403654075038690625 

noncomputable def Ns420p199 := nat_lit 1803372022892858034982487867110875523412024904755049937890625 

noncomputable def Ns420p200 := nat_lit 8581516495692279374718605640555608047556336353401452125240290625 

noncomputable def Ns420p201 := BSN.cos_dyadic_bound_f 34041655 33554432 3 2 16777216 6760000 Ns420p198 Ns420p181 Ns420p199 Ns420p200 Ns420p184 Ns420p199 8858828 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 34041655) qz635 0 2 Ns420p198 Ns420p181 Ns420p199 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 34041655) (BSN.cosOddQ 33554432) 0 2 Ns420p200 Ns420p184 Ns420p199 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz356 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns420p202 := @Ns420p187 929377216 113413980160000 2214707 4194304 14521519 1772093440000 (@Ns420p188 135 16777216 Bool.false 8858828 16777216 1 6760000 (@Ns420p192 Ns420p193 34041655 33554432 135 16777216 (@Ns420p194 1125899906842624 1435990955 1125899906842624 Ns420p189 Ns420p190 Ns420p191 Ns420p193 RS421to432.d51 (@Ns420p195 0 1 2908711669799536 181794479362471 1125899906842624 1435990955 1125899906842624 (@Ns420p196 3738827254308613914624 111425735184807 1125899906842624 1435990955 1125899906842624 (@Ns420p197 261585835 1125899906842624 (Ns420p178 rfl rfl) (Ns420p178 rfl rfl) rfl) (Ns420p178 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 34041655 33554432) (BSN.cos_neg_of_bound 34041655 33554432 Bool.false 8858828 16777216 1 6760000 (Ns420p201 rfl rfl)) rfl rfl) 

noncomputable abbrev qz29 := (@Enclosure.Real.IsNear.of_eq qz620 (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1))

noncomputable def Ns420p203 := @Ns420p163 1262234443748410166231 Ns420p77 (Ns420p164 qz29 (@Enclosure.Real.IsNear.of_eq qz330 (@Inv.inv Real Real.instInv qz21) Bool.false 10066213 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz7 (BSN.t_div_two_pi_nonneg qz4 775738 1000 qz10)) Ns420p168) rfl) (@Ns420p169 140737488355328 499534054081391 29730794415063040000 (BSN.correction_mk qz9 (BSN.cos_two_pi_p_ne_zero_mk qz4 775738 1000 11 qz10 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 775738 1000 11 qz10 rfl rfl rfl))) (@Ns420p170 33554432 2214707 4194304 14521519 1772093440000 97141237030937 140737488355328 499534054081391 29730794415063040000 (@Ns420p171 33554432 (Ns420p186 rfl rfl rfl rfl rfl) rfl) (Ns420p202 rfl) rfl)) 

noncomputable def Ns420p204 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 2655953409910698044259 4722366482869645213696 278797342133710947126231 Ns420p77 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz330) (Zeta.RiemannSiegel.correction qz9))) Bool.true 2655953409910698044259 4722366482869645213696 278797342133710947126231 Ns420p77 (BSN.hardyZApproximantRS₀_eq qz4 11 (@BSN.floor_sqrt_eq_dec qz4 775738 1000 11 qz10 rfl rfl rfl)) (@Ns420p79 2655953409910698044259 4722366482869645213696 278797342133710947126231 Ns420p77 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 11)) Bool.true 103278745 134217728 149359 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 11) (Ns420p162 (Ns420p161 rfl) rfl rfl)) (Ns420p203 rfl) rfl rfl)) 

theorem RS421to432.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 2655953409910698044259 4722366482869645213696 278797342133710947126231 Ns420p77 := Ns420p204 

theorem RS421to432.d54 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS421to432.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS421to432.d3 a b h)) 

noncomputable def Ns420p205 := nat_lit 2234873641799415010602027 

noncomputable def Ns420p206 := nat_lit 1995199839012425102786560000 

noncomputable def Ns420p207 := nat_lit 3187014992047526250576626057216 

noncomputable abbrev qz801 := (Enclosure.sfrac Bool.false 777042 1000)

noncomputable abbrev qz636 := qz801

noncomputable abbrev qz357 := qz636

noncomputable abbrev qz30 := qz357

noncomputable abbrev qz802 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 777042 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz637 := qz802

noncomputable abbrev qz358 := qz637

noncomputable abbrev qz31 := qz358

noncomputable abbrev qz803 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 777042 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz638 := qz803

noncomputable abbrev qz359 := qz638

noncomputable abbrev qz32 := qz359

noncomputable abbrev qz360 := (@HPow.hPow Real Real Real qz623 qz31 qz8)

noncomputable def Ns420p208 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz360) (Zeta.RiemannSiegel.correction qz32)) 141593449 134217728 149605 134217728 3817605682026418430525 18889465931478580854784 10935892566661961002027 Ns420p206 Ns420p207 

noncomputable def Ns420p209 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 777042 1000 195 242 268435456 134217728 4503599627370496 Bool.false 398044639443 2530 

noncomputable def Ns420p210 := Ns420p209 618095470 41 84886744 8 643680110 41 80936328 8 Bool.false 213112740 128342 Bool.true 18302244 Bool.true 80742951 14148475504056880 1 Bool.false 18288067 Bool.false Bool.false 256383362 Bool.true Bool.false 141593449 

noncomputable def Ns420p211 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 777042 1000 84 142 268435456 134217728 4503599627370496 Bool.false 398044639443 2530 

noncomputable def Ns420p212 := Ns420p211 558195838 41 94906264 8 589812974 41 89478488 8 Bool.false 175342365 104701 Bool.true 277746933 Bool.true 389458686 14148475504056880 1 Bool.false 137115280 Bool.false Bool.false 32121585 Bool.true Bool.false 213112740 

noncomputable def Ns420p213 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 777042 1000 57 18 268435456 134217728 4503599627370496 Bool.false 398044639443 2530 

noncomputable def Ns420p214 := Ns420p213 480971758 41 109588312 8 522351262 41 101459064 8 Bool.false 328165483 77644 Bool.false 274909251 Bool.true 254396175 14148475504056880 1 Bool.false 229312429 Bool.true Bool.false 156646242 Bool.true Bool.false 175342365 

noncomputable def Ns420p215 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 777042 1000 258 147 268435456 134217728 4503599627370496 Bool.false 398044639443 2530 

noncomputable def Ns420p216 := Ns420p215 372130544 40 134217720 8 432030192 40 120047984 16 Bool.false 337489247 45778 Bool.false 95960779 Bool.false 355393035 14148475504056880 1 Bool.false 251465225 Bool.true Bool.false 260298085 Bool.false Bool.false 328165483 

noncomputable def Ns420p217 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 777042 1000 601 400 268435456 134217728 4503599627370496 Bool.false 398044639443 2530 

noncomputable def Ns420p218 := Ns420p217 186065264 40 189812528 16 294906480 40 154981288 8 Bool.false 268435448 2576 Bool.false 48000185 Bool.false 226947104 14148475504056880 1 Bool.false 47744795 Bool.true Bool.false 178079875 Bool.false Bool.false 337489247 

noncomputable def Ns420p219 := nat_lit 9187538956185072238672962794305154840839147211963178167 

noncomputable def Ns420p220 := nat_lit 6195941270978232667791925741796007145417659016806400 

noncomputable def Ns420p221 := nat_lit 135976594643672433751541784591360000 

noncomputable def Ns420p222 := nat_lit 633957272825729137481713811168493342720 

noncomputable abbrev qz33 := (@Eq.refl Real qz357)

noncomputable def Ns420p223 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz30 777042 1000 2415178079056 16000000 1554084 4000 2000 Ns420p221 Ns420p222 qz33 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns420p224 := nat_lit 1693447180404032515032200502246326140263471614109052999741440 

noncomputable abbrev qz361 := (@HMul.hMul Real Real Real qz619 qz625 (@HSub.hSub Real Real Real qz624 qz626 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 (@Nat.cast Real Real.instNatCast 1554084)))))

noncomputable abbrev qz639 := (Real.log (Enclosure.sfrac Bool.false 2415178079056 16000000))

noncomputable abbrev qz640 := (Enclosure.sfrac Bool.false 777042 2000)

noncomputable abbrev qz34 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 777042 4000) qz639) qz361) qz640)

noncomputable abbrev qz362 := (@HSub.hSub Real Real Real qz11 qz34 (@HMul.hMul Real Real Real qz5 qz640 (Real.log Real.pi)))

noncomputable def Ns420p225 := @Enclosure.Real.IsNear.addLit_ft_p qz362 (Enclosure.sfrac Bool.true Ns420p221 Ns420p222) 2671232743824372745427 1801439850948198400 3259854018102225117 346112000000000000000000 Ns420p221 Ns420p222 0 1 Ns420p224 

noncomputable def Ns420p226 := nat_lit 448158487294141676145417912320000 

noncomputable abbrev qz363 := (@HMul.hMul Real Real Real qz5 qz640 (Real.log Real.pi))

noncomputable def Ns420p227 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz363 17362129987211768125471 9007199254740992000 1226629241263083 338000000000000000000 14923387274481 33554432000 388521 67108864000 Ns420p226 2671232743824372745427 1801439850948198400 

noncomputable def Ns420p228 := nat_lit 34724259974423536250942000 

noncomputable abbrev qz35 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 777042 4000) qz639) qz361)

noncomputable def Ns420p229 := @Enclosure.Real.IsNear.subLit_ff_p qz35 qz640 20861616048862993078303 9007199254740992000 1226629241263083 338000000000000000000 777042 2000 0 1 Ns420p228 17362129987211768125471 9007199254740992000 1226629241263083 338000000000000000000 

noncomputable def Ns420p230 := nat_lit 46976183132002867350594258038259974144 

noncomputable def Ns420p231 := nat_lit 57664286009363726474412032 

noncomputable def Ns420p232 := nat_lit 886327991095256358600593170966082676470488204996340662720989921570368394362880 

noncomputable def Ns420p233 := nat_lit 1471953140186096447001610164440574716039089241913898015524135297662243045376 

noncomputable def Ns420p234 := nat_lit 15519140613141388963935932369512439376494060489878577787662786982051840 

noncomputable def Ns420p235 := BSN.log_dyadic_bound 318026079056 4512330079056 4 3 Ns420p232 134217728 54080000 Ns420p233 Ns420p234 18950575 4830356158112 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 318026079056) (BSN.artanhQ 4512330079056) 0 3 Ns420p233 Ns420p232 Ns420p234 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns420p236 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 777042 4000) qz639 777042 4000 0 1 53704051309603943 4503599627370496 3125002873 169000000000000000 20865151718858633538303 9007199254740992000 1214129241220833 338000000000000000000 (Enclosure.Real.IsNear.const Bool.false 777042 4000) (BSN.isNear_log_sfrac 2415178079056 16000000 53704051309603943 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2415178079056) qz335)) Bool.false Ns420p231 Ns420p103 1000000919360000 54080000000000000000000 53704051309603943 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2415178079056 16000000 17 4830356158112 4194304000000 18950575 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns420p235 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns420p237 := BSN.arctan_dyadic_bound_f 1000 1554084 1 0 16777216 6760000 0 1 1 0 1 1 10795 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1554084) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1554084) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns420p238 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1554084))) 884279719003555 562949953421312 1 2000000000000000 10795 16777216 1 6760000 14829674805394763939840 883917498910115 562949953421312 50000000169 338000000000000000 qz16 (Ns420p237 rfl) rfl rfl 

noncomputable abbrev qz36 := qz361

noncomputable def Ns420p239 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 777042 4000) qz639) qz36 20865151718858633538303 9007199254740992000 1214129241220833 338000000000000000000 883917498910115 2251799813685248 50000000169 1352000000000000000 Ns420p230 20861616048862993078303 9007199254740992000 1226629241263083 338000000000000000000 (Ns420p236 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1554084)))) 1 4 0 1 883917498910115 562949953421312 50000000169 338000000000000000 883917498910115 2251799813685248 50000000169 1352000000000000000 qz340 Ns420p238 rfl) 

noncomputable def Ns420p240 := @Ns420p225 Ns420p219 Ns420p220 3259854018102225117 346112000000000000000000 (@Ns420p227 3259854018102225117 346112000000000000000000 (Ns420p229 (Ns420p239 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 777042 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz640 (Real.log Real.pi) 777042 2000 0 1 38410761 33554432 1 67108864 14923387274481 33554432000 388521 67108864000 (Enclosure.Real.IsNear.const Bool.false 777042 2000) RS421to432.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns420p221 Ns420p222) 

noncomputable def Ns420p241 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz30) Bool.false Ns420p219 Ns420p220 3259854018102225117 346112000000000000000000 24877789965 16777216 317 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz30) (@HAdd.hAdd Real Real Real qz341 qz362 (Enclosure.sfrac Bool.true Ns420p221 Ns420p222)) Bool.false Ns420p219 Ns420p220 3259854018102225117 346112000000000000000000 Ns420p223 (Ns420p240 rfl rfl)) 

noncomputable def Ns420p242 := nat_lit 2417851639229258349412352 

noncomputable def Ns420p243 := BSN.cos_dyadic_bound_f 6952089 68719476736 1 0 33554432 13533204 0 1 1 0 1 1 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 6952089) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 6952089) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable abbrev qz364 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns420p244 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz30) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24877789965) qz364) Bool.false 24877789965 16777216 317 33554432 Bool.false 33554431 33554432 1 6760000 (Ns420p241 rfl) (Enclosure.sfrac_false_div 24877789965 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24877789965) qz364) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 244604911390723932160) (@Nat.cast Real Real.instNatCast Ns420p242)) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 236 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q0 24877789965 16777216 226375608064910080 72057594037927936 236 244604911390723932160 Ns420p242 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554431 33554432 244604911390723932160 Ns420p242 6952089 68719476736 13533204 13520000 (Ns420p243 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns420p245 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz30) Bool.false Ns420p219 Ns420p220 3259854018102225117 346112000000000000000000 398044639443 268435456 2530 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz30) (@HAdd.hAdd Real Real Real qz341 qz362 (Enclosure.sfrac Bool.true Ns420p221 Ns420p222)) Bool.false Ns420p219 Ns420p220 3259854018102225117 346112000000000000000000 Ns420p223 (Ns420p240 rfl rfl)) 

noncomputable def Ns420p246 := Ns420p218 45778 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 601 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 47744795 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 400 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 178079875 268435456) qz33 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 1) Bool.false 33554431 33554432 34007413 3544186880000 268435448 268435456 2576 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz30)) Bool.false 33554431 33554432 34007413 3544186880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz30) qz30) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz30)) Bool.false 33554431 33554432 2176474432 226827960320000 33554431 33554432 34007413 3544186880000 (Ns420p244 rfl rfl) rfl)) rfl) (Ns420p245 rfl) RS421to432.d7 

noncomputable def Ns420p247 := nat_lit 5308497838553127615673171350625 

noncomputable def Ns420p248 := BSN.sin_dyadic_bound_f 48000185 268435456 2 1 268435456 134217728 Ns420p247 Ns420p133 Ns420p247 Ns420p247 Ns420p134 Ns420p247 47744795 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 48000185) qz344 0 1 Ns420p247 Ns420p133 Ns420p247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 48000185) qz345 0 1 Ns420p247 Ns420p134 Ns420p247 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p249 := nat_lit 23147251475189955083242553343139704181654395907341630081439089521852416 

noncomputable def Ns420p250 := nat_lit 7037155727237843619486053637641187305448463381847209818482840436736 

noncomputable def Ns420p251 := nat_lit 69427680114115389562488687922143830170352290795261195824680302884683776 

noncomputable def Ns420p252 := BSN.cos_dyadic_bound_f 226947104 268435456 3 2 268435456 134217728 Ns420p249 Ns420p156 Ns420p250 Ns420p251 Ns420p159 Ns420p250 178079875 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 226947104) qz346 0 2 Ns420p249 Ns420p156 Ns420p250 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 226947104) qz347 0 2 Ns420p251 Ns420p159 Ns420p250 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p253 := nat_lit 739687155393292649368553164295797721138980314856349224218021640076641 

noncomputable def Ns420p254 := nat_lit 7190351460040867329934700795474637900748159793870375706285636961 

noncomputable def Ns420p255 := nat_lit 2219047085476957866370999623485802214141139448249459931902652348956001 

noncomputable def Ns420p256 := BSN.cos_dyadic_bound_f 95960779 268435456 3 2 268435456 134217728 Ns420p253 Ns420p156 Ns420p254 Ns420p255 Ns420p159 Ns420p254 251465225 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 95960779) qz346 0 2 Ns420p253 Ns420p156 Ns420p254 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 95960779) qz347 0 2 Ns420p255 Ns420p159 Ns420p254 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p257 := nat_lit 22340600722566779741307936692556067096186772336264197725627865904138840091770576911702723431541164214307540625 

noncomputable def Ns420p258 := nat_lit 871683568514489007341798292243696146469029465094156570908284878217177001794361422139649254553384847460322508800 

noncomputable def Ns420p259 := nat_lit 4059821572075339639358277431895855141937472644635758668635996098502105412876165513809349591015869140625 

noncomputable def Ns420p260 := nat_lit 111632900880795897128149256020492882050047348702613982523303811904821277058895321250267531001875983344061140625 

noncomputable def Ns420p261 := nat_lit 30508924898007115256962940228529365126416031278295479981789970737601195062802649774887723909368469661111287808000 

noncomputable def Ns420p262 := BSN.sin_dyadic_bound_f 355393035 268435456 4 3 268435456 134217728 Ns420p257 Ns420p258 Ns420p259 Ns420p260 Ns420p261 Ns420p259 260298085 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 355393035) qz344 0 3 Ns420p257 Ns420p258 Ns420p259 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 355393035) qz345 0 3 Ns420p260 Ns420p261 Ns420p259 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p263 := Ns420p216 77644 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 258 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 251465225 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 260298085 268435456) qz33 rfl rfl (Ns420p246 RS421to432.d9 RS421to432.d11 RS421to432.d13 RS421to432.d17 (Ns420p248 rfl rfl) (Ns420p252 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns420p245 rfl) RS421to432.d19 RS421to432.d21 RS421to432.d23 RS421to432.d25 RS421to432.d17 (Ns420p256 rfl rfl) (Ns420p262 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns420p264 := nat_lit 89713266572689816658911234347333981677179441045447903553147476464742305 

noncomputable def Ns420p265 := nat_lit 32622319483574025968450368995736236819168697084571749632640107524001 

noncomputable def Ns420p266 := nat_lit 234910500125499923778913836978929236199667501038036155044552449614524321 

noncomputable def Ns420p267 := BSN.sin_dyadic_bound_f 274909251 268435456 3 2 268435456 134217728 Ns420p264 Ns420p119 Ns420p265 Ns420p266 Ns420p122 Ns420p265 229312429 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 274909251) qz344 0 2 Ns420p264 Ns420p119 Ns420p265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 274909251) qz345 0 2 Ns420p266 Ns420p122 Ns420p265 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p268 := nat_lit 36552709883478075329971454728294338335962570140297047493963964962890625 

noncomputable def Ns420p269 := nat_lit 17542222581019613308669654903490530730446172265198593896636962890625 

noncomputable def Ns420p270 := nat_lit 109623045205272186763297024875076033946426818076360745294098620962890625 

noncomputable def Ns420p271 := BSN.cos_dyadic_bound_f 254396175 268435456 3 2 268435456 134217728 Ns420p268 Ns420p156 Ns420p269 Ns420p270 Ns420p159 Ns420p269 156646242 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 254396175) qz346 0 2 Ns420p268 Ns420p156 Ns420p269 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 254396175) qz347 0 2 Ns420p270 Ns420p159 Ns420p269 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p272 := Ns420p214 104701 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 229312429 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 156646242 268435456) qz33 rfl rfl (Ns420p263 rfl rfl) (Ns420p245 rfl) RS421to432.d27 RS421to432.d29 RS421to432.d31 RS421to432.d33 RS421to432.d17 (Ns420p267 rfl rfl) (Ns420p271 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p273 := nat_lit 3204336033458020545080040777621060186042174700780097652241392619853339428017196266767238256191451937422762641 

noncomputable def Ns420p274 := nat_lit 210761491695890863739336935767149042044299425341416640557607458160477921414301767085240607088539132561 

noncomputable def Ns420p275 := nat_lit 19430802078376755361158628719584132397424167637799133765328493195699425043499237831079922098769877649682915985 

noncomputable def Ns420p276 := BSN.cos_dyadic_bound_f 277746933 268435456 4 3 268435456 134217728 Ns420p273 Ns420p140 Ns420p274 Ns420p275 Ns420p143 Ns420p274 137115280 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 277746933) qz346 0 3 Ns420p273 Ns420p140 Ns420p274 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 277746933) qz347 0 3 Ns420p275 Ns420p143 Ns420p274 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p277 := nat_lit 12411796793327491092585316535953342027457997443518873696657414245701034224321864701628781639857943009170558976 

noncomputable def Ns420p278 := nat_lit 12176899759820209410857070332927416005123265702216457773573573901763561794317975027413122038930708893696 

noncomputable def Ns420p279 := nat_lit 75166125960271889405974961556766340318021413182418857916939312478899398258091260143296550715763898136116858880 

noncomputable def Ns420p280 := BSN.cos_dyadic_bound_f 389458686 268435456 4 3 268435456 134217728 Ns420p277 Ns420p140 Ns420p278 Ns420p279 Ns420p143 Ns420p278 32121585 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 389458686) qz346 0 3 Ns420p277 Ns420p140 Ns420p278 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 389458686) qz347 0 3 Ns420p279 Ns420p143 Ns420p278 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p281 := Ns420p212 128342 BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 137115280 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 142 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 32121585 268435456) qz33 rfl rfl (Ns420p272 rfl) (Ns420p245 rfl) RS421to432.d35 RS421to432.d37 RS421to432.d39 RS421to432.d41 RS421to432.d17 (Ns420p276 rfl rfl) (Ns420p280 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p282 := nat_lit 112206331518243072768411607296 

noncomputable def Ns420p283 := BSN.sin_dyadic_bound_f 18302244 268435456 2 1 268435456 134217728 Ns420p282 Ns420p133 Ns420p282 Ns420p282 Ns420p134 Ns420p282 18288067 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 18302244) qz344 0 1 Ns420p282 Ns420p133 Ns420p282 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 18302244) qz345 0 1 Ns420p282 Ns420p134 Ns420p282 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p284 := nat_lit 42502891067515878549328566936801 

noncomputable def Ns420p285 := nat_lit 124615124604835863084731911901282304 

noncomputable def Ns420p286 := nat_lit 1869226869072537946270978678519234560 

noncomputable def Ns420p287 := BSN.cos_dyadic_bound_f 80742951 268435456 2 1 268435456 134217728 Ns420p284 Ns420p285 Ns420p284 Ns420p284 Ns420p286 Ns420p284 256383362 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 80742951) qz346 0 1 Ns420p284 Ns420p285 Ns420p284 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 80742951) qz347 0 1 Ns420p284 Ns420p286 Ns420p284 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p288 := Ns420p210 149605 BSN.abs_quadSignPos (BSN.cos_quad_nat3 195 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 18288067 268435456) BSN.abs_quadSignNeg qz348 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 256383362 268435456) qz33 rfl rfl (Ns420p281 rfl) (Ns420p245 rfl) RS421to432.d43 RS421to432.d45 RS421to432.d47 RS421to432.d49 RS421to432.d17 (Ns420p283 rfl rfl) (Ns420p287 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p289 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 11) 141593449 268435456 149605 268435456 141593449 268435456 149605 268435456 76017404097855488 141593449 134217728 149605 134217728 (Ns420p288 rfl) 

noncomputable def Ns420p290 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz360) (Zeta.RiemannSiegel.correction qz32) 10061987 33554432 1 33554432 379408727324575 562949953421312 1082869262002529 59461588830126080000 3817605682026418430525 18889465931478580854784 

noncomputable def Ns420p291 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz360 1 1 0 1 10061987 33554432 1 33554432 10061987 33554432 1 33554432 

noncomputable def Ns420p292 := @Enclosure.Real.IsNear.sqrt_image qz31 2074839287913 16777216000 388521 16777216000 186574436 186574472 16777216 (@Enclosure.Real.IsNear.of_eq qz31 (@HMul.hMul Real Real Real qz5 qz30 qz3) Bool.false 2074839287913 16777216000 388521 16777216000 (BSN.t_div_two_pi_mk qz30 777042 1000 qz33) (@Enclosure.Real.IsNear.mulLit_ff qz30 qz3 777042 1000 0 1 5340353 33554432 1 33554432 2074839287913 16777216000 388521 16777216000 (Enclosure.Real.IsNear.const Bool.false 777042 1000) RS421to432.d52 rfl)) 

noncomputable abbrev qz804 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 777042 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz641 := qz804

noncomputable abbrev qz365 := qz641

noncomputable abbrev qz37 := qz365

noncomputable def Ns420p293 := @Enclosure.Real.IsNear.sqrt_image qz37 93287227 8388608 9 8388608 55948186 55948193 16777216 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 373148908 33554432 36 33554432 93287227 8388608 9 8388608 (Ns420p292 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns420p294 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz37) 111896379 33554432 7 33554432 5030993 5030994 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz37) Bool.false 111896379 33554432 7 33554432 111896379 33554432 7 33554432 (Ns420p293 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p295 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz37)) Bool.false 10061987 33554432 1 33554432 10061987 33554432 1 33554432 (Ns420p294 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz326 qz322 qz359)

noncomputable abbrev qz642 := (@HMul.hMul Real Real Real qz795 qz803 qz803)

noncomputable abbrev qz366 := (@HSub.hSub Real Real Real qz624 (@HSub.hSub Real Real Real qz624 qz642 qz638) qz634)

noncomputable abbrev qz39 := (Real.cos (@HMul.hMul Real Real Real qz326 qz322 qz366))

noncomputable def Ns420p296 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz32) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz38)) qz39) Bool.false 379408727324575 

noncomputable def Ns420p297 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz38)) qz39 46222475 33554432 441 

noncomputable def Ns420p298 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz38)) Bool.false 46222475 33554432 441 33554432 46222475 33554432 441 

noncomputable def Ns420p299 := @Enclosure.Real.IsNear.recentre' (Real.cos qz38) Bool.false 12179139 16777216 1568074432 226827960320000 12179139 16777216 24501163 3544186880000 

noncomputable abbrev qz643 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns420p300 := @Enclosure.Real.IsNear.cos_image qz38 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3180985) qz643) Bool.false 3180985 4194304 227 33554432 Bool.false 12179139 16777216 1 

noncomputable def Ns420p301 := nat_lit 242874678690094052878369791 

noncomputable def Ns420p302 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns420p303 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz32 884279719003555 140737488355328 1 500000000000000 1012539 8388608 9 8388608 895367702400140576145 1180591620717411303424 Ns420p301 

noncomputable def Ns420p304 := @Enclosure.Real.IsNear.subLit_ff_p qz37 qz1 93287227 8388608 9 8388608 11 1 0 1 1012539 1012539 8388608 9 

noncomputable def Ns420p305 := @Ns420p304 8388608 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 373148908 33554432 36 33554432 93287227 8388608 9 8388608 (Ns420p292 rfl rfl rfl rfl rfl rfl) rfl) qz352 

noncomputable def Ns420p306 := @Enclosure.Real.IsNear.recentre' qz38 Bool.false 895367702400140576145 1180591620717411303424 Ns420p301 Ns420p302 3180985 4194304 227 33554432 (@Ns420p303 Ns420p302 RS421to432.d51 (Ns420p305 rfl rfl) rfl) 

noncomputable def Ns420p307 := nat_lit 53245253529058026083736081206881640616373156723020690625 

noncomputable def Ns420p308 := nat_lit 3861888762982039923063034508418779142719222587902677483520 

noncomputable def Ns420p309 := nat_lit 10483178229375651903766119854132532330713410687890625 

noncomputable def Ns420p310 := nat_lit 159714794230715326947400711380936656784458043347686290625 

noncomputable def Ns420p311 := nat_lit 173784994334191796537836552878845061422365016455620486758400 

noncomputable def Ns420p312 := BSN.cos_dyadic_bound_f 3180985 4194304 3 2 16777216 6760000 Ns420p307 Ns420p308 Ns420p309 Ns420p310 Ns420p311 Ns420p309 12179139 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3180985) (BSN.cosEvenQ 4194304) 0 2 Ns420p307 Ns420p308 Ns420p309 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3180985) (BSN.cosOddQ 4194304) 0 2 Ns420p310 Ns420p311 Ns420p309 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p313 := @Enclosure.Real.IsNear.inv_image (Real.cos qz38) 12179139 16777216 24501163 3544186880000 23111017 23111458 16777216 (Ns420p299 (@Ns420p300 6760000 (Ns420p306 rfl) (Enclosure.sfrac_false_div 3180985 4194304) (Ns420p312 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns420p314 := @Enclosure.Real.IsNear.recentre' qz39 Bool.false 8208317 16777216 

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz326 qz322 qz366)

noncomputable def Ns420p315 := @Enclosure.Real.IsNear.cos_image qz40 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8888253)) (@Nat.cast Real Real.instNatCast 8388608)) Bool.true 8888253 8388608 

noncomputable def Ns420p316 := nat_lit 10493397286278513054468248725 

noncomputable def Ns420p317 := nat_lit 9903520314283042199192993792 

noncomputable def Ns420p318 := nat_lit 101168913084519909238467565784489 

noncomputable def Ns420p319 := @Enclosure.Real.IsNear.recentre' qz40 Bool.true Ns420p316 Ns420p317 Ns420p318 

noncomputable def Ns420p320 := nat_lit 12089258196146291747061760000000000000 

noncomputable abbrev qz41 := qz366

noncomputable def Ns420p321 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz41 884279719003555 140737488355328 1 500000000000000 11866604040295 

noncomputable abbrev qz367 := (@HSub.hSub Real Real Real qz624 qz642 qz638)

noncomputable abbrev qz42 := qz367

noncomputable def Ns420p322 := @Enclosure.Real.IsNear.subLit_tf qz42 qz27 7468557529191 70368744177664 93723255 70368744177664 1 16 

noncomputable abbrev qz368 := qz642

noncomputable abbrev qz43 := qz368

noncomputable def Ns420p323 := @Enclosure.Real.IsNear.subLit_ff_n qz43 qz32 1025235226521 70368744177664 18225783 70368744177664 1012539 8388608 9 8388608 

noncomputable def Ns420p324 := @Enclosure.Real.IsNear.mulLit_ff qz32 qz32 1012539 8388608 9 8388608 1012539 8388608 9 8388608 1025235226521 70368744177664 

noncomputable def Ns420p325 := nat_lit 51958931980934714198297166003552594668281980335248196366241 

noncomputable def Ns420p326 := nat_lit 988643523323402220304136834155207460536120982503085435781120 

noncomputable def Ns420p327 := nat_lit 38952134828109344801670800984467087957169648069403078561 

noncomputable def Ns420p328 := nat_lit 155798891673147923905288156408688849828931601709605782941601 

noncomputable def Ns420p329 := nat_lit 44488958549553099913686157536984335724125444212638844610150400 

noncomputable def Ns420p330 := BSN.cos_dyadic_bound_f 8888253 8388608 3 2 16777216 6760000 Ns420p325 Ns420p326 Ns420p327 Ns420p328 Ns420p329 Ns420p327 8208317 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 8888253) (BSN.cosEvenQ 8388608) 0 2 Ns420p325 Ns420p326 Ns420p327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 8888253) (BSN.cosOddQ 8388608) 0 2 Ns420p328 Ns420p329 Ns420p327 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p331 := @Ns420p314 969937216 113413980160000 8208317 16777216 15155269 1772093440000 (@Ns420p315 141 16777216 Bool.false 8208317 16777216 1 6760000 (@Ns420p319 Ns420p320 8888253 8388608 141 16777216 (@Ns420p321 70368744177664 93723255 70368744177664 Ns420p316 Ns420p317 Ns420p318 Ns420p320 RS421to432.d51 (@Ns420p322 0 1 189865664644720 11866604040295 70368744177664 93723255 70368744177664 (@Ns420p323 62650801437831856128 7468557529191 70368744177664 93723255 70368744177664 (@Ns420p324 18225783 70368744177664 (Ns420p305 rfl rfl) (Ns420p305 rfl rfl) rfl) (Ns420p305 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8888253 8388608) (BSN.cos_neg_of_bound 8888253 8388608 Bool.false 8208317 16777216 1 6760000 (Ns420p330 rfl rfl)) rfl rfl) 

noncomputable def Ns420p332 := @Ns420p290 10935892566661961002027 Ns420p206 (Ns420p291 qz29 (@Enclosure.Real.IsNear.of_eq qz360 (@Inv.inv Real Real.instInv (Real.sqrt qz37)) Bool.false 10061987 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz31 (BSN.t_div_two_pi_nonneg qz30 777042 1000 qz33)) Ns420p295) rfl) (@Ns420p296 562949953421312 1082869262002529 59461588830126080000 (BSN.correction_mk qz32 (BSN.cos_two_pi_p_ne_zero_mk qz30 777042 1000 11 qz33 rfl rfl (@BSN.floor_sqrt_eq_dec qz30 777042 1000 11 qz33 rfl rfl rfl))) (@Ns420p297 33554432 8208317 16777216 15155269 1772093440000 379408727324575 562949953421312 1082869262002529 59461588830126080000 (@Ns420p298 33554432 (Ns420p313 rfl rfl rfl rfl rfl) rfl) (Ns420p331 rfl) rfl)) 

noncomputable def Ns420p333 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz30) (hardyZApproximantRS₀ qz30) Bool.false 23745112061854647476797 18889465931478580854784 Ns420p205 Ns420p206 (@Eq.refl Real (hardyZApproximantRS₀ qz30)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz30) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz360) (Zeta.RiemannSiegel.correction qz32))) Bool.false 23745112061854647476797 18889465931478580854784 Ns420p205 Ns420p206 (BSN.hardyZApproximantRS₀_eq qz30 11 (@BSN.floor_sqrt_eq_dec qz30 777042 1000 11 qz33 rfl rfl rfl)) (@Ns420p208 23745112061854647476797 18889465931478580854784 Ns420p205 Ns420p206 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 11)) Bool.false 141593449 134217728 149605 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz30) qz30 11) (Ns420p289 (Ns420p288 rfl) rfl rfl)) (Ns420p332 rfl) rfl rfl)) 

theorem RS421to432.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz30) Bool.false 23745112061854647476797 18889465931478580854784 Ns420p205 Ns420p206 := Ns420p333 

noncomputable abbrev qz805 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 775738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))) (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 775738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz644 := qz805

noncomputable abbrev qz369 := qz644

noncomputable abbrev qz645 := (@HMul.hMul Real Real Real qz795 qz805 qz805)

noncomputable abbrev qz370 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz619 qz645 qz644))

noncomputable abbrev qz44 := (@HAdd.hAdd Real Real Real qz341 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz369)) (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 1 32) qz370))

noncomputable abbrev qz371 := (@HMul.hMul Real Real Real qz619 qz632 qz632)

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz326 qz371 qz350))

noncomputable def Ns420p334 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz341 qz44 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz45)) Bool.false 

noncomputable def Ns420p335 := @Enclosure.Real.IsNear.addLit_ff qz44 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz45) 16306601 1073741824 

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv qz369)

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 1 32) qz370)

noncomputable def Ns420p336 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz46) qz47 2038325 134217728 25 134217728 

noncomputable def Ns420p337 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz46 25 4 0 1 81533 33554432 1 33554432 2038325 

noncomputable def Ns420p338 := @Enclosure.Real.IsNear.recentre' qz46 Bool.false 81533 33554432 1 33554432 81533 33554432 1 33554432 

noncomputable def Ns420p339 := @Enclosure.Real.IsNear.mulLit_ff qz21 qz7 27962351 8388608 3 16777216 2071357377757 16777216000 387869 16777216000 57920022043280826707 140737488355328000 6976382884229 

noncomputable def Ns420p340 := @Enclosure.Real.IsNear.sqrt_image qz7 2071357377757 16777216000 387869 16777216000 186417820 186417855 16777216 qz19 

noncomputable def Ns420p341 := @Enclosure.Real.IsNear.sqrt_image qz20 372835675 33554432 35 33554432 55924699 55924705 16777216 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 372835675 33554432 35 33554432 372835675 33554432 35 33554432 (Ns420p340 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz372 := (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 111849404 33554432 6 33554432 27962351 8388608 3 16777216 (Ns420p341 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns420p342 := @Ns420p339 70368744177664000 qz372 

noncomputable def Ns420p343 := Ns420p342 qz19 

noncomputable abbrev qz48 := qz369

noncomputable def Ns420p344 := @Enclosure.Real.IsNear.inv_image qz48 57920022043280826707 140737488355328000 6976382884229 70368744177664000 40766 40767 16777216 (Ns420p343 rfl) rfl rfl 

noncomputable abbrev qz49 := qz370

noncomputable def Ns420p345 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz49 1 32 0 1 1 

noncomputable def Ns420p346 := @Enclosure.Real.IsNear.recentre' qz49 Bool.false 1 33554432 1 33554432 

noncomputable def Ns420p347 := nat_lit 194305974935612826980561038567002383668680014628476535215243 

noncomputable def Ns420p348 := nat_lit 2787593149816327892691964784081045188247552000000000 

noncomputable def Ns420p349 := nat_lit 70211637870929633994598359993754527554967523245450941 

noncomputable def Ns420p350 := nat_lit 1393796574908163946345982392040522594123776000000000 

noncomputable abbrev qz373 := (@HMul.hMul Real Real Real qz619 qz645 qz644)

noncomputable abbrev qz50 := qz373

noncomputable def Ns420p351 := @Enclosure.Real.IsNear.inv_image qz50 Ns420p347 Ns420p348 Ns420p349 Ns420p350 0 1 

noncomputable def Ns420p352 := nat_lit 3354728953494136871968485068441364463849 

noncomputable def Ns420p353 := nat_lit 19807040628566084398385987584000000 

noncomputable def Ns420p354 := nat_lit 50509037388353612381917126153543 

noncomputable def Ns420p355 := nat_lit 618970019642690137449562112000000 

noncomputable abbrev qz374 := qz645

noncomputable abbrev qz51 := qz374

noncomputable def Ns420p356 := @Enclosure.Real.IsNear.mulLit_ff qz51 qz48 Ns420p352 Ns420p353 Ns420p354 Ns420p355 57920022043280826707 140737488355328000 6976382884229 

noncomputable def Ns420p357 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz48 57920022043280826707 140737488355328000 6976382884229 70368744177664000 57920022043280826707 140737488355328000 6976382884229 70368744177664000 Ns420p352 

noncomputable def Ns420p358 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz45 13 10 0 1 452969 16777216 1 

noncomputable def Ns420p359 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 905938 33554432 2 33554432 452969 16777216 

noncomputable abbrev qz52 := qz371

noncomputable def Ns420p360 := @Enclosure.Real.IsNear.mulLit_ff qz52 qz21 781893073447201 70368744177664 335548221 281474976710656 27962351 8388608 3 16777216 21863568564199414329551 

noncomputable def Ns420p361 := @Enclosure.Real.IsNear.mulLit_ff qz21 qz21 27962351 8388608 3 16777216 27962351 8388608 3 16777216 781893073447201 70368744177664 335548221 

noncomputable def Ns420p362 := @Ns420p361 281474976710656 qz372 

noncomputable def Ns420p363 := Ns420p362 qz372 

noncomputable def Ns420p364 := @Ns420p360 590295810358705651712 28148152154066217 4722366482869645213696 (Ns420p363 rfl) qz372 

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz326 qz371 qz350)

noncomputable def Ns420p365 := @Enclosure.Real.IsNear.inv_image qz53 21863568564199414329551 590295810358705651712 28148152154066217 4722366482869645213696 452968 452970 16777216 (Ns420p364 rfl) 

noncomputable def Ns420p366 := @Ns420p335 201 1073741824 5888597 167772160 13 167772160 9058626555609088 269968109 5368709120 1421 5368709120 (@Ns420p336 1 1073741824 1 1073741824 2188634937622528 16306601 1073741824 201 1073741824 (@Ns420p337 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns420p338 (Ns420p344 rfl rfl rfl rfl) rfl) rfl) (@Ns420p345 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns420p346 1 33554432 1 33554432 (@Ns420p351 16777216 (@Ns420p356 70368744177664000 Ns420p347 Ns420p348 Ns420p349 Ns420p350 (@Ns420p357 Ns420p353 Ns420p354 Ns420p355 (Ns420p343 rfl) (Ns420p343 rfl) rfl) (Ns420p343 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns420p358 16777216 5888597 167772160 13 167772160 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns420p359 1 16777216 (Ns420p365 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS421to432.d56 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 := @Ns420p334 269968109 5368709120 1421 5368709120 (BSN.hardyZErrorBoundRS₀_mk qz4 775738 1000 qz10 rfl rfl) (Ns420p366 rfl rfl) 

noncomputable def Ns420p367 := nat_lit 376809564079262029285762793472 

noncomputable abbrev qz806 := (Enclosure.sfrac Bool.false 778346 1000)

noncomputable abbrev qz646 := qz806

noncomputable abbrev qz375 := qz646

noncomputable abbrev qz54 := qz375

noncomputable abbrev qz807 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 778346 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz647 := qz807

noncomputable abbrev qz376 := qz647

noncomputable abbrev qz55 := qz376

noncomputable abbrev qz808 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 778346 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz648 := qz808

noncomputable abbrev qz377 := qz648

noncomputable abbrev qz56 := qz377

noncomputable abbrev qz378 := (@HPow.hPow Real Real Real qz623 qz55 qz8)

noncomputable def Ns420p368 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz54) qz54 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz378) (Zeta.RiemannSiegel.correction qz56)) 332410863 67108864 149857 134217728 232933691352327782085 1180591620717411303424 1454778747017508953957 Ns420p77 Ns420p367 

noncomputable def Ns420p369 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz54) qz54 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 778346 1000 194 242 268435456 134217728 4503599627370496 Bool.false 398887965342 2534 

noncomputable def Ns420p370 := Ns420p369 618095470 41 84886744 8 643680110 41 80936328 8 Bool.true 581161438 128559 Bool.true 402630266 Bool.true 76775915 14148475504056880 1 Bool.false 19011233 Bool.true Bool.false 257530659 Bool.true Bool.true 664821726 

noncomputable def Ns420p371 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz54) qz54 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 778346 1000 84 142 268435456 134217728 4503599627370496 Bool.false 398887965342 2534 

noncomputable def Ns420p372 := Ns420p371 558195838 41 94906264 8 589812974 41 89478488 8 Bool.true 624693284 104879 Bool.true 162308407 Bool.true 315248905 14148475504056880 1 Bool.false 220842769 Bool.false Bool.false 103643584 Bool.true Bool.true 581161438 

noncomputable def Ns420p373 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz54) qz54 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 778346 1000 58 18 268435456 134217728 4503599627370496 Bool.false 398887965342 2534 

noncomputable def Ns420p374 := Ns420p373 480971758 41 109588312 8 522351262 41 101459064 8 Bool.true 423215212 77777 Bool.false 69390550 Bool.true 92216321 14148475504056880 1 Bool.false 259516560 Bool.true Bool.false 252750965 Bool.true Bool.true 624693284 

noncomputable def Ns420p375 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz54) qz54 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 778346 1000 259 148 268435456 134217728 4503599627370496 Bool.false 398887965342 2534 

noncomputable def Ns420p376 := Ns420p375 372130544 40 134217720 8 432030192 40 120047984 16 Bool.true 523337318 45858 Bool.false 32371020 Bool.false 213694136 14148475504056880 1 Bool.false 32292618 Bool.false Bool.false 187775596 Bool.false Bool.true 423215212 

noncomputable def Ns420p377 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz54) qz54 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 778346 1000 602 401 268435456 134217728 4503599627370496 Bool.false 398887965342 2534 

noncomputable def Ns420p378 := Ns420p377 186065264 40 189812528 16 294906480 40 154981288 8 Bool.true 268435448 2584 Bool.false 227039552 Bool.false 264057525 14148475504056880 1 Bool.false 178010689 Bool.true Bool.false 223485306 Bool.true Bool.true 523337318 

noncomputable def Ns420p379 := nat_lit 83700891022679365166744827428411812105938947133817434571 

noncomputable def Ns420p380 := nat_lit 56327311930751367759472926910667985119889890633318400 

noncomputable def Ns420p381 := nat_lit 137121381698542804974593209748480000 

noncomputable def Ns420p382 := nat_lit 640367397076617723535866013101758484480 

noncomputable abbrev qz57 := (@Eq.refl Real qz375)

noncomputable def Ns420p383 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz54 778346 1000 2423290982864 16000000 1556692 4000 2000 Ns420p381 Ns420p382 qz57 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns420p384 := nat_lit 1714194248144473398614934065733873911929629637300581060014080 

noncomputable abbrev qz379 := (@HMul.hMul Real Real Real qz619 qz625 (@HSub.hSub Real Real Real qz624 qz626 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 (@Nat.cast Real Real.instNatCast 1556692)))))

noncomputable abbrev qz649 := (Real.log (Enclosure.sfrac Bool.false 2423290982864 16000000))

noncomputable abbrev qz650 := (Enclosure.sfrac Bool.false 778346 2000)

noncomputable abbrev qz58 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 778346 4000) qz649) qz379) qz650)

noncomputable abbrev qz380 := (@HSub.hSub Real Real Real qz11 qz58 (@HMul.hMul Real Real Real qz5 qz650 (Real.log Real.pi)))

noncomputable def Ns420p385 := @Enclosure.Real.IsNear.addLit_ft_p qz380 (Enclosure.sfrac Bool.true Ns420p381 Ns420p382) 2676892207482726389271 1801439850948198400 3265303090918815321 346112000000000000000000 Ns420p381 Ns420p382 0 1 Ns420p384 

noncomputable def Ns420p386 := nat_lit 449107987736545169016996495360000 

noncomputable abbrev qz381 := (@HMul.hMul Real Real Real qz5 qz650 (Real.log Real.pi))

noncomputable def Ns420p387 := @Enclosure.Real.IsNear.subLit_ff_p qz58 qz381 17397149953717647339123 9007199254740992000 1228666743136279 338000000000000000000 14948431090653 33554432000 389173 67108864000 Ns420p386 2676892207482726389271 1801439850948198400 

noncomputable def Ns420p388 := nat_lit 34794299907435294678246000 

noncomputable abbrev qz59 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 778346 4000) qz649) qz379)

noncomputable def Ns420p389 := @Enclosure.Real.IsNear.subLit_ff_p qz59 qz650 20902508709282963418739 9007199254740992000 1228666743136279 338000000000000000000 778346 2000 0 1 Ns420p388 17397149953717647339123 9007199254740992000 1228666743136279 338000000000000000000 

noncomputable def Ns420p390 := nat_lit 47068265217117650678421053012571062272 

noncomputable def Ns420p391 := nat_lit 57680502570901962156408832 

noncomputable def Ns420p392 := nat_lit 895932464576517690413984017541354302837878473272175654161212368166654868193280 

noncomputable def Ns420p393 := nat_lit 1559397158528094655414764554354137290175059269562521404550424483017791635456 

noncomputable def Ns420p394 := nat_lit 18051260499403502866632533941183444601072004994757947479738108912599040 

noncomputable def Ns420p395 := BSN.log_dyadic_bound 326138982864 4520442982864 4 3 Ns420p392 134217728 54080000 Ns420p393 Ns420p394 19400675 4846581965728 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 326138982864) (BSN.artanhQ 4520442982864) 0 3 Ns420p393 Ns420p392 Ns420p394 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns420p396 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 778346 4000) qz649 778346 4000 0 1 53719154159447143 4503599627370496 3125002873 169000000000000000 20906044381694522982739 9007199254740992000 1216166743094029 338000000000000000000 (Enclosure.Real.IsNear.const Bool.false 778346 4000) (BSN.isNear_log_sfrac 2423290982864 16000000 53719154159447143 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2423290982864) qz335)) Bool.false Ns420p391 Ns420p103 1000000919360000 54080000000000000000000 53719154159447143 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2423290982864 16000000 17 4846581965728 4194304000000 19400675 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns420p395 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns420p397 := BSN.arctan_dyadic_bound_f 1000 1556692 1 0 16777216 6760000 0 1 1 0 1 1 10777 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1556692) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1556692) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns420p398 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1556692))) 884279719003555 562949953421312 1 2000000000000000 10777 16777216 1 6760000 14829684938493925523456 883918102889891 562949953421312 50000000169 338000000000000000 qz16 (Ns420p397 rfl) rfl rfl 

noncomputable abbrev qz60 := qz379

noncomputable def Ns420p399 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 778346 4000) qz649) qz60 20906044381694522982739 9007199254740992000 1216166743094029 338000000000000000000 883918102889891 2251799813685248 50000000169 1352000000000000000 Ns420p390 20902508709282963418739 9007199254740992000 1228666743136279 338000000000000000000 (Ns420p396 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1556692)))) 1 4 0 1 883918102889891 562949953421312 50000000169 338000000000000000 883918102889891 2251799813685248 50000000169 1352000000000000000 qz340 Ns420p398 rfl) 

noncomputable def Ns420p400 := @Ns420p385 Ns420p379 Ns420p380 3265303090918815321 346112000000000000000000 (@Ns420p387 3265303090918815321 346112000000000000000000 (Ns420p389 (Ns420p399 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 778346 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz650 (Real.log Real.pi) 778346 2000 0 1 38410761 33554432 1 67108864 14948431090653 33554432000 389173 67108864000 (Enclosure.Real.IsNear.const Bool.false 778346 2000) RS421to432.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns420p381 Ns420p382) 

noncomputable def Ns420p401 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz54) Bool.false Ns420p379 Ns420p380 3265303090918815321 346112000000000000000000 49860995667 33554432 159 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz54) (@HAdd.hAdd Real Real Real qz341 qz380 (Enclosure.sfrac Bool.true Ns420p381 Ns420p382)) Bool.false Ns420p379 Ns420p380 3265303090918815321 346112000000000000000000 Ns420p383 (Ns420p400 rfl rfl)) 

noncomputable def Ns420p402 := BSN.cos_dyadic_bound_f 9778193 68719476736 1 0 33554432 13533204 0 1 1 0 1 1 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 9778193) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 9778193) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns420p403 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz54) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49860995667) qz342) Bool.false 49860995667 33554432 159 16777216 Bool.true 33554431 33554432 1 6760000 (Ns420p401 rfl) (Enclosure.sfrac_false_div 49860995667 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49860995667) qz342) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 688079187386369572864) qz343) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 236 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q2 49860995667 33554432 226375608064910080 72057594037927936 236 688079187386369572864 Ns420p103 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554431 33554432 688079187386369572864 Ns420p103 9778193 68719476736 13533204 13520000 (Ns420p402 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns420p404 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz54) Bool.false Ns420p379 Ns420p380 3265303090918815321 346112000000000000000000 398887965342 268435456 2534 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz54) (@HAdd.hAdd Real Real Real qz341 qz380 (Enclosure.sfrac Bool.true Ns420p381 Ns420p382)) Bool.false Ns420p379 Ns420p380 3265303090918815321 346112000000000000000000 Ns420p383 (Ns420p400 rfl rfl)) 

noncomputable def Ns420p405 := Ns420p378 45858 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 602 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 178010689 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 401 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 223485306 268435456) qz57 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 1) Bool.true 33554431 33554432 17056519 1772093440000 268435448 268435456 2584 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz54)) Bool.true 33554431 33554432 17056519 1772093440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz54) qz54) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz54)) Bool.true 33554431 33554432 1091617216 113413980160000 33554431 33554432 17056519 1772093440000 (Ns420p403 rfl rfl) rfl)) rfl) (Ns420p404 rfl) RS421to432.d7 

noncomputable def Ns420p406 := nat_lit 23185002598867208060284128135300713941946635788641155014624937756327936 

noncomputable def Ns420p407 := nat_lit 7060121405620619652353555984487307524890662752208432115371743379456 

noncomputable def Ns420p408 := nat_lit 69540887553790382941547677293933167210790126040419048179644069782224896 

noncomputable def Ns420p409 := BSN.cos_dyadic_bound_f 227039552 268435456 3 2 268435456 134217728 Ns420p406 Ns420p156 Ns420p407 Ns420p408 Ns420p159 Ns420p407 178010689 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 227039552) qz346 0 2 Ns420p406 Ns420p156 Ns420p407 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 227039552) qz347 0 2 Ns420p408 Ns420p159 Ns420p407 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p410 := nat_lit 76360708171626899103569255576709354805917899224157331659905147550390625 

noncomputable def Ns420p411 := nat_lit 23636784012560518991916869136143012271141328264268893188629150390625 

noncomputable def Ns420p412 := nat_lit 199954061846812018716694470627065983424203126293698480901255701150390625 

noncomputable def Ns420p413 := BSN.sin_dyadic_bound_f 264057525 268435456 3 2 268435456 134217728 Ns420p410 Ns420p119 Ns420p411 Ns420p412 Ns420p122 Ns420p411 223485306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 264057525) qz344 0 2 Ns420p410 Ns420p119 Ns420p411 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 264057525) qz345 0 2 Ns420p412 Ns420p122 Ns420p411 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p414 := nat_lit 1098058647225495862854272160000 

noncomputable def Ns420p415 := BSN.sin_dyadic_bound_f 32371020 268435456 2 1 268435456 134217728 Ns420p414 Ns420p133 Ns420p414 Ns420p414 Ns420p134 Ns420p414 32292618 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32371020) qz344 0 1 Ns420p414 Ns420p133 Ns420p414 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32371020) qz345 0 1 Ns420p414 Ns420p134 Ns420p414 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p416 := nat_lit 18194621443847432583326941186934125406536094203735268647495443977076736 

noncomputable def Ns420p417 := nat_lit 4348513658455568822322885514069503027453675838769799898449634656256 

noncomputable def Ns420p418 := nat_lit 54575167304225386612336177789774237213553375259528266342689432661917696 

noncomputable def Ns420p419 := BSN.cos_dyadic_bound_f 213694136 268435456 3 2 268435456 134217728 Ns420p416 Ns420p156 Ns420p417 Ns420p418 Ns420p159 Ns420p417 187775596 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 213694136) qz346 0 2 Ns420p416 Ns420p156 Ns420p417 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 213694136) qz347 0 2 Ns420p418 Ns420p159 Ns420p417 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p420 := Ns420p376 77777 BSN.abs_quadSignPos (BSN.cos_quad_nat3 259 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 32292618 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 148 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 187775596 268435456) qz57 rfl rfl (Ns420p405 RS421to432.d9 RS421to432.d11 RS421to432.d13 RS421to432.d17 (Ns420p409 rfl rfl) (Ns420p413 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns420p404 rfl) RS421to432.d19 RS421to432.d21 RS421to432.d23 RS421to432.d25 RS421to432.d17 (Ns420p415 rfl rfl) (Ns420p419 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns420p421 := nat_lit 23184691376528472340636506250000 

noncomputable def Ns420p422 := BSN.cos_dyadic_bound_f 69390550 268435456 2 1 268435456 134217728 Ns420p421 Ns420p285 Ns420p421 Ns420p421 Ns420p286 Ns420p421 259516560 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 69390550) qz346 0 1 Ns420p421 Ns420p285 Ns420p421 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 69390550) qz347 0 1 Ns420p421 Ns420p286 Ns420p421 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p423 := nat_lit 630817254753960510527064909290486015421003570318830931544479192637441 

noncomputable def Ns420p424 := nat_lit 5229526105103516425335765205704656888313505667205640270279925761 

noncomputable def Ns420p425 := nat_lit 1892441305209671324548344056341046636949234083945158383352897018060801 

noncomputable def Ns420p426 := BSN.cos_dyadic_bound_f 92216321 268435456 3 2 268435456 134217728 Ns420p423 Ns420p156 Ns420p424 Ns420p425 Ns420p159 Ns420p424 252750965 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 92216321) qz346 0 2 Ns420p423 Ns420p156 Ns420p424 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 92216321) qz347 0 2 Ns420p425 Ns420p159 Ns420p424 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p427 := Ns420p374 104879 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 259516560 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 252750965 268435456) qz57 rfl rfl (Ns420p420 rfl rfl) (Ns420p404 rfl) RS421to432.d27 RS421to432.d29 RS421to432.d31 RS421to432.d33 RS421to432.d17 (Ns420p422 rfl rfl) (Ns420p426 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p428 := nat_lit 6054348393329192298949023393551763222527343632885983034730039387151681 

noncomputable def Ns420p429 := nat_lit 481646182658081866642600289210105927634343377459587865225603374401 

noncomputable def Ns420p430 := nat_lit 18162081887622260733113784980076869455726762211903029928459666954706241 

noncomputable def Ns420p431 := BSN.cos_dyadic_bound_f 162308407 268435456 3 2 268435456 134217728 Ns420p428 Ns420p156 Ns420p429 Ns420p430 Ns420p159 Ns420p429 220842769 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 162308407) qz346 0 2 Ns420p428 Ns420p156 Ns420p429 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 162308407) qz347 0 2 Ns420p430 Ns420p159 Ns420p429 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p432 := nat_lit 5320477759984378377820227977990704629426404287869657689100636807193513236371043328631324439627053183964390625 

noncomputable def Ns420p433 := nat_lit 963480747698095046754971553430996267889422614684294334004180437313913327314827962927708503847900390625 

noncomputable def Ns420p434 := nat_lit 32253223392793536229126806038939414929746687339731520359857420195779444957507406824479261415529750351221990625 

noncomputable def Ns420p435 := BSN.cos_dyadic_bound_f 315248905 268435456 4 3 268435456 134217728 Ns420p432 Ns420p140 Ns420p433 Ns420p434 Ns420p143 Ns420p433 103643584 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 315248905) qz346 0 3 Ns420p432 Ns420p140 Ns420p433 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 315248905) qz347 0 3 Ns420p434 Ns420p143 Ns420p433 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p436 := Ns420p372 128559 BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 220842769 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 142 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 103643584 268435456) qz57 rfl rfl (Ns420p427 rfl) (Ns420p404 rfl) RS421to432.d35 RS421to432.d37 RS421to432.d39 RS421to432.d41 RS421to432.d17 (Ns420p431 rfl rfl) (Ns420p435 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p437 := nat_lit 14183304076710482196925045056475854192326726177291322128249007170622488675581342884496454302568349979902939136 

noncomputable def Ns420p438 := nat_lit 18150016158467020292169339194328028006874452833534953823698696406118082942899579742207711360965694918656 

noncomputable def Ns420p439 := nat_lit 85872985749906498476812988844688689479867820781900400045315093744611070666039200236637228403888007433069465600 

noncomputable def Ns420p440 := BSN.cos_dyadic_bound_f 402630266 268435456 4 3 268435456 134217728 Ns420p437 Ns420p140 Ns420p438 Ns420p439 Ns420p143 Ns420p438 19011233 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 402630266) qz346 0 3 Ns420p437 Ns420p140 Ns420p438 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 402630266) qz347 0 3 Ns420p439 Ns420p143 Ns420p438 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p441 := nat_lit 34745615063555486075089408200625 

noncomputable def Ns420p442 := BSN.cos_dyadic_bound_f 76775915 268435456 2 1 268435456 134217728 Ns420p441 Ns420p285 Ns420p441 Ns420p441 Ns420p286 Ns420p441 257530659 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 76775915) qz346 0 1 Ns420p441 Ns420p285 Ns420p441 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 76775915) qz347 0 1 Ns420p441 Ns420p286 Ns420p441 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz651 := (BSN.cos_quad_nat2 194 rfl)

noncomputable def Ns420p443 := Ns420p370 149857 BSN.abs_quadSignNeg qz651 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 19011233 268435456) BSN.abs_quadSignNeg qz348 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 257530659 268435456) qz57 rfl rfl (Ns420p436 rfl) (Ns420p404 rfl) RS421to432.d43 RS421to432.d45 RS421to432.d47 RS421to432.d49 RS421to432.d17 (Ns420p440 rfl rfl) (Ns420p442 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p444 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 11) 664821726 268435456 149857 268435456 664821726 268435456 149857 268435456 356923446355034112 332410863 67108864 149857 134217728 (Ns420p443 rfl) 

noncomputable def Ns420p445 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz378) (Zeta.RiemannSiegel.correction qz56) 5028885 16777216 1 16777216 46319152526321 70368744177664 574677503545049 29730794415063040000 232933691352327782085 1180591620717411303424 

noncomputable def Ns420p446 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz378 1 1 0 1 5028885 16777216 1 16777216 5028885 16777216 1 16777216 

noncomputable def Ns420p447 := @Enclosure.Real.IsNear.sqrt_image qz55 2078321198069 16777216000 389173 16777216000 186730921 186730957 16777216 (@Enclosure.Real.IsNear.of_eq qz55 (@HMul.hMul Real Real Real qz5 qz54 qz3) Bool.false 2078321198069 16777216000 389173 16777216000 (BSN.t_div_two_pi_mk qz54 778346 1000 qz57) (@Enclosure.Real.IsNear.mulLit_ff qz54 qz3 778346 1000 0 1 5340353 33554432 1 33554432 2078321198069 16777216000 389173 16777216000 (Enclosure.Real.IsNear.const Bool.false 778346 1000) RS421to432.d52 rfl)) 

noncomputable abbrev qz809 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 778346 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz652 := qz809

noncomputable abbrev qz382 := qz652

noncomputable abbrev qz61 := qz382

noncomputable def Ns420p448 := @Enclosure.Real.IsNear.sqrt_image qz61 186730939 16777216 9 8388608 55971644 55971650 16777216 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 373461878 33554432 36 33554432 186730939 16777216 9 8388608 (Ns420p447 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns420p449 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz61) 55971647 16777216 3 16777216 5028884 5028886 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz61) Bool.false 111943294 33554432 6 33554432 55971647 16777216 3 16777216 (Ns420p448 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p450 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz61)) Bool.false 10057770 33554432 2 33554432 5028885 16777216 1 16777216 (Ns420p449 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz62 := (@HMul.hMul Real Real Real qz326 qz322 qz377)

noncomputable abbrev qz653 := (@HMul.hMul Real Real Real qz795 qz808 qz808)

noncomputable abbrev qz383 := (@HSub.hSub Real Real Real qz624 (@HSub.hSub Real Real Real qz624 qz653 qz648) qz634)

noncomputable abbrev qz63 := (Real.cos (@HMul.hMul Real Real Real qz326 qz322 qz383))

noncomputable def Ns420p451 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz56) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz62)) qz63) Bool.false 46319152526321 

noncomputable def Ns420p452 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz62)) qz63 24513623 16777216 31 

noncomputable def Ns420p453 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz62)) Bool.false 49027246 33554432 496 33554432 24513623 16777216 31 

noncomputable def Ns420p454 := @Enclosure.Real.IsNear.recentre' (Real.cos qz62) Bool.false 11482390 16777216 1568074432 226827960320000 5741195 8388608 24501163 3544186880000 

noncomputable def Ns420p455 := @Enclosure.Real.IsNear.cos_image qz62 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 27414329) qz342) Bool.false 27414329 33554432 227 33554432 Bool.false 11482390 16777216 1 

noncomputable def Ns420p456 := nat_lit 242874678690766150835684351 

noncomputable def Ns420p457 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz56 884279719003555 140737488355328 1 500000000000000 2181563 16777216 9 8388608 1929111916628552456465 2361183241434822606848 Ns420p456 

noncomputable def Ns420p458 := @Enclosure.Real.IsNear.subLit_ff_p qz61 qz1 186730939 16777216 9 8388608 11 1 0 1 2181563 2181563 16777216 9 

noncomputable def Ns420p459 := @Ns420p458 8388608 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 373461878 33554432 36 33554432 186730939 16777216 9 8388608 (Ns420p447 rfl rfl rfl rfl rfl rfl) rfl) qz352 

noncomputable def Ns420p460 := @Enclosure.Real.IsNear.recentre' qz62 Bool.false 1929111916628552456465 2361183241434822606848 Ns420p456 Ns420p302 27414329 33554432 227 33554432 (@Ns420p457 Ns420p302 RS421to432.d51 (Ns420p459 rfl rfl) rfl) 

noncomputable def Ns420p461 := nat_lit 1203190784765976778490702055257021125401509394653501561213288641 

noncomputable def Ns420p462 := nat_lit 319022242573324575029056250934571779232813730008169073082561 

noncomputable def Ns420p463 := nat_lit 3608934309812783686322048053269194232646062556500488345493700801 

noncomputable def Ns420p464 := BSN.cos_dyadic_bound_f 27414329 33554432 3 2 16777216 6760000 Ns420p461 Ns420p181 Ns420p462 Ns420p463 Ns420p184 Ns420p462 11482390 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 27414329) qz635 0 2 Ns420p461 Ns420p181 Ns420p462 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 27414329) (BSN.cosOddQ 33554432) 0 2 Ns420p463 Ns420p184 Ns420p462 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p465 := @Enclosure.Real.IsNear.inv_image (Real.cos qz62) 5741195 8388608 24501163 3544186880000 24513375 24513871 16777216 (Ns420p454 (@Ns420p455 6760000 (Ns420p460 rfl) (Enclosure.sfrac_false_div 27414329 33554432) (Ns420p464 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns420p466 := @Enclosure.Real.IsNear.recentre' qz63 Bool.false 7558108 16777216 

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz326 qz322 qz383)

noncomputable def Ns420p467 := @Enclosure.Real.IsNear.cos_image qz64 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 37026403)) qz342) Bool.true 37026403 33554432 

noncomputable def Ns420p468 := nat_lit 43713061465289723767352645525 

noncomputable def Ns420p469 := nat_lit 39614081257132168796771975168 

noncomputable def Ns420p470 := nat_lit 128361453560534018846452146217859 

noncomputable def Ns420p471 := @Enclosure.Real.IsNear.recentre' qz64 Bool.true Ns420p468 Ns420p469 Ns420p470 

noncomputable def Ns420p472 := nat_lit 15111572745182864683827200000000000000 

noncomputable abbrev qz65 := qz383

noncomputable def Ns420p473 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz65 884279719003555 140737488355328 1 500000000000000 49433522590055 

noncomputable abbrev qz384 := (@HSub.hSub Real Real Real qz624 qz653 qz648)

noncomputable abbrev qz66 := qz384

noncomputable def Ns420p474 := @Enclosure.Real.IsNear.subLit_tf qz66 qz27 31841336545639 281474976710656 23782905 17592186044416 1 16 

noncomputable abbrev qz385 := qz653

noncomputable abbrev qz67 := qz385

noncomputable def Ns420p475 := @Enclosure.Real.IsNear.subLit_ff_n qz67 qz56 4759217122969 281474976710656 4908537 17592186044416 2181563 16777216 9 8388608 

noncomputable def Ns420p476 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 2181563 16777216 9 8388608 2181563 16777216 9 8388608 4759217122969 281474976710656 

noncomputable def Ns420p477 := nat_lit 4006250110236672621269256762005764887363437094692633135958203041 

noncomputable def Ns420p478 := nat_lit 3532581497498853803814920321580081065223156849310705713420961 

noncomputable def Ns420p479 := nat_lit 12011685167715020156200140445374134499959864970379277996447767201 

noncomputable def Ns420p480 := BSN.cos_dyadic_bound_f 37026403 33554432 3 2 16777216 6760000 Ns420p477 Ns420p181 Ns420p478 Ns420p479 Ns420p184 Ns420p478 7558108 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 37026403) qz635 0 2 Ns420p477 Ns420p181 Ns420p478 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 37026403) (BSN.cosOddQ 33554432) 0 2 Ns420p479 Ns420p184 Ns420p478 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p481 := @Ns420p466 983457216 113413980160000 1889527 4194304 15366519 1772093440000 (@Ns420p467 143 16777216 Bool.false 7558108 16777216 1 6760000 (@Ns420p471 Ns420p472 37026403 33554432 143 16777216 (@Ns420p473 281474976710656 23782905 17592186044416 Ns420p468 Ns420p469 Ns420p470 Ns420p472 RS421to432.d51 (@Ns420p474 0 1 790936361440880 49433522590055 281474976710656 23782905 17592186044416 (@Ns420p475 534208980954879361024 31841336545639 281474976710656 23782905 17592186044416 (@Ns420p476 4908537 17592186044416 (Ns420p459 rfl rfl) (Ns420p459 rfl rfl) rfl) (Ns420p459 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 37026403 33554432) (BSN.cos_neg_of_bound 37026403 33554432 Bool.false 7558108 16777216 1 6760000 (Ns420p480 rfl rfl)) rfl rfl) 

noncomputable def Ns420p482 := @Ns420p445 1454778747017508953957 Ns420p77 (Ns420p446 qz29 (@Enclosure.Real.IsNear.of_eq qz378 (@Inv.inv Real Real.instInv (Real.sqrt qz61)) Bool.false 5028885 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz55 (BSN.t_div_two_pi_nonneg qz54 778346 1000 qz57)) Ns420p450) rfl) (@Ns420p451 70368744177664 574677503545049 29730794415063040000 (BSN.correction_mk qz56 (BSN.cos_two_pi_p_ne_zero_mk qz54 778346 1000 11 qz57 rfl rfl (@BSN.floor_sqrt_eq_dec qz54 778346 1000 11 qz57 rfl rfl rfl))) (@Ns420p452 2097152 1889527 4194304 15366519 1772093440000 46319152526321 70368744177664 574677503545049 29730794415063040000 (@Ns420p453 2097152 (Ns420p465 rfl rfl rfl rfl rfl) rfl) (Ns420p481 rfl) rfl)) 

noncomputable def Ns420p483 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz54) (hardyZApproximantRS₀ qz54) Bool.true 5614900053728551108923 1180591620717411303424 279915257413148883033957 Ns420p77 (@Eq.refl Real (hardyZApproximantRS₀ qz54)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz54) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz54) qz54 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz378) (Zeta.RiemannSiegel.correction qz56))) Bool.true 5614900053728551108923 1180591620717411303424 279915257413148883033957 Ns420p77 (BSN.hardyZApproximantRS₀_eq qz54 11 (@BSN.floor_sqrt_eq_dec qz54 778346 1000 11 qz57 rfl rfl rfl)) (@Ns420p368 5614900053728551108923 1180591620717411303424 279915257413148883033957 Ns420p77 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz54) qz54 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz54) qz54 11)) Bool.true 332410863 67108864 149857 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz54) qz54 11) (Ns420p444 (Ns420p443 rfl) rfl rfl)) (Ns420p482 rfl) rfl rfl)) 

theorem RS421to432.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz54) Bool.true 5614900053728551108923 1180591620717411303424 279915257413148883033957 Ns420p77 := Ns420p483 

noncomputable def Ns420p484 := nat_lit 199519983901242510278656000 

noncomputable def Ns420p485 := nat_lit 1457542804772738748310301442048 

noncomputable abbrev qz810 := (Enclosure.sfrac Bool.false 779649 1000)

noncomputable abbrev qz654 := qz810

noncomputable abbrev qz386 := qz654

noncomputable abbrev qz68 := qz386

noncomputable abbrev qz811 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 779649 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz655 := qz811

noncomputable abbrev qz387 := qz655

noncomputable abbrev qz69 := qz387

noncomputable abbrev qz812 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 779649 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz656 := qz812

noncomputable abbrev qz388 := qz656

noncomputable abbrev qz70 := qz388

noncomputable abbrev qz389 := (@HPow.hPow Real Real Real qz623 qz69 qz8)

noncomputable def Ns420p486 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz68) qz68 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz389) (Zeta.RiemannSiegel.correction qz70)) 141393549 67108864 150103 134217728 1819707324945406109685 9444732965739290427392 1206292302162623321091 Ns420p484 Ns420p485 

noncomputable def Ns420p487 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz68) qz68 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 779649 1000 194 242 268435456 134217728 4503599627370496 Bool.false 399730936912 2538 

noncomputable def Ns420p488 := Ns420p487 618095470 41 84886744 8 643680110 41 80936328 8 Bool.false 378560251 128769 Bool.true 365037094 Bool.true 72519528 14148475504056880 1 Bool.false 56201424 Bool.true Bool.false 258699086 Bool.true Bool.false 282787098 

noncomputable def Ns420p489 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz68) qz68 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 779649 1000 84 142 268435456 134217728 4503599627370496 Bool.false 399730936912 2538 

noncomputable def Ns420p490 := Ns420p489 558195838 41 94906264 8 589812974 41 89478488 8 Bool.false 340910807 105049 Bool.true 46666014 Bool.true 240803640 14148475504056880 1 Bool.false 264389347 Bool.false Bool.false 167478908 Bool.true Bool.false 378560251 

noncomputable def Ns420p491 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz68) qz68 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 779649 1000 58 17 268435456 134217728 4503599627370496 Bool.false 399730936912 2538 

noncomputable def Ns420p492 := Ns420p491 480971758 41 109588312 8 522351262 41 101459064 8 Bool.false 492104225 77902 Bool.false 285655919 Bool.true 351525874 14148475504056880 1 Bool.false 130257375 Bool.true Bool.false 259326148 Bool.true Bool.false 340910807 

noncomputable def Ns420p493 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz68) qz68 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 779649 1000 259 149 268435456 134217728 4503599627370496 Bool.false 399730936912 2538 

noncomputable def Ns420p494 := Ns420p493 372130544 40 134217720 8 432030192 40 120047984 16 Bool.false 390638259 45930 Bool.false 390456491 Bool.false 72072937 14148475504056880 1 Bool.false 266624214 Bool.false Bool.false 71210117 Bool.true Bool.false 492104225 

noncomputable def Ns420p495 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz68) qz68 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 779649 1000 603 402 268435456 134217728 4503599627370496 Bool.false 399730936912 2538 

noncomputable def Ns420p496 := Ns420p495 186065264 40 189812528 16 294906480 40 154981288 8 Bool.false 268435280 2584 Bool.false 405910655 Bool.false 301108523 14148475504056880 1 Bool.false 267973725 Bool.false Bool.false 116537666 Bool.true Bool.false 390638259 

noncomputable def Ns420p497 := nat_lit 6024804260973162727575654380124374220344822194784823425783 

noncomputable def Ns420p498 := nat_lit 4045899203092016897452534205971429408802220890128384000 

noncomputable def Ns420p499 := nat_lit 138272979408473426948271779159520000 

noncomputable def Ns420p500 := nat_lit 646826464884287447835348101210379650880 

noncomputable abbrev qz71 := (@Eq.refl Real qz386)

noncomputable def Ns420p501 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz68 779649 1000 2431411252804 16000000 1559298 4000 2000 Ns420p499 Ns420p500 qz71 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns420p502 := nat_lit 17351436271602708655417884614758197754593087920980291466255040 

noncomputable abbrev qz390 := (@HMul.hMul Real Real Real qz619 qz625 (@HSub.hSub Real Real Real qz624 qz626 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 (@Nat.cast Real Real.instNatCast 1559298)))))

noncomputable abbrev qz657 := (Real.log (Enclosure.sfrac Bool.false 2431411252804 16000000))

noncomputable abbrev qz658 := (Enclosure.sfrac Bool.false 779649 2000)

noncomputable abbrev qz72 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 779649 4000) qz657) qz390) qz658)

noncomputable abbrev qz391 := (@HSub.hSub Real Real Real qz11 qz72 (@HMul.hMul Real Real Real qz5 qz658 (Real.log Real.pi)))

noncomputable def Ns420p503 := @Enclosure.Real.IsNear.addLit_ft_p qz391 (Enclosure.sfrac Bool.true Ns420p499 Ns420p500) 26825492932808970738983 18014398509481984000 6541495969997165973 692224000000000000000000 Ns420p499 Ns420p500 0 1 Ns420p502 

noncomputable def Ns420p504 := nat_lit 1800228356960838355302389645312000 

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz5 qz658 (Real.log Real.pi))

noncomputable def Ns420p505 := @Enclosure.Real.IsNear.subLit_ff_p qz72 qz392 34864305751035079171367 18014398509481984000 2461405365016077 676000000000000000000 29946911402889 67108864000 779649 134217728000 Ns420p504 26825492932808970738983 18014398509481984000 

noncomputable def Ns420p506 := nat_lit 2789144460082806333709360 

noncomputable abbrev qz73 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 779649 4000) qz657) qz390)

noncomputable def Ns420p507 := @Enclosure.Real.IsNear.subLit_ff_p qz73 qz658 1675470385711785553727 720575940379279360 2461405365016077 676000000000000000000 779649 2000 0 1 Ns420p506 34864305751035079171367 18014398509481984000 2461405365016077 676000000000000000000 

noncomputable def Ns420p508 := nat_lit 3772823902380949312646789680171319296 

noncomputable def Ns420p509 := nat_lit 57696679536792273997004800 

noncomputable def Ns420p510 := nat_lit 905632350816907502906967043088262985607614657433849219630227094896395534766080 

noncomputable def Ns420p511 := nat_lit 1650059159114843620790838949087180957610471615538266839615470765539423318016 

noncomputable def Ns420p512 := nat_lit 20921455126613275903460664011047576754482787435120308007003902722109440 

noncomputable def Ns420p513 := BSN.log_dyadic_bound 334259252804 4528563252804 4 3 Ns420p510 134217728 54080000 Ns420p511 Ns420p512 19849676 4862822505608 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 334259252804) (BSN.artanhQ 4528563252804) 0 3 Ns420p511 Ns420p510 Ns420p512 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns420p514 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 779649 4000) qz657 779649 4000 0 1 53734220132969575 4503599627370496 3125002873 169000000000000000 1675753239697983847167 720575940379279360 187415797302429 52000000000000000000 (Enclosure.Real.IsNear.const Bool.false 779649 4000) (BSN.isNear_log_sfrac 2431411252804 16000000 53734220132969575 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2431411252804) qz335)) Bool.false Ns420p509 Ns420p103 1000000919360000 54080000000000000000000 53734220132969575 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2431411252804 16000000 17 4862822505608 4194304000000 19849676 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns420p513 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns420p515 := BSN.arctan_dyadic_bound_f 1000 1559298 1 0 16777216 6760000 0 1 1 0 1 1 10759 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1559298) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1559298) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns420p516 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1559298))) 884279719003555 562949953421312 1 2000000000000000 10759 16777216 1 6760000 14829695071593087107072 883918706869667 562949953421312 50000000169 338000000000000000 qz16 (Ns420p515 rfl) rfl rfl 

noncomputable abbrev qz74 := qz390

noncomputable def Ns420p517 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 779649 4000) qz657) qz74 1675753239697983847167 720575940379279360 187415797302429 52000000000000000000 883918706869667 2251799813685248 50000000169 1352000000000000000 Ns420p508 1675470385711785553727 720575940379279360 2461405365016077 676000000000000000000 (Ns420p514 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1559298)))) 1 4 0 1 883918706869667 562949953421312 50000000169 338000000000000000 883918706869667 2251799813685248 50000000169 1352000000000000000 qz340 Ns420p516 rfl) 

noncomputable def Ns420p518 := @Ns420p503 Ns420p497 Ns420p498 6541495969997165973 692224000000000000000000 (@Ns420p505 6541495969997165973 692224000000000000000000 (Ns420p507 (Ns420p517 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 779649 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz658 (Real.log Real.pi) 779649 2000 0 1 38410761 33554432 1 67108864 29946911402889 67108864000 779649 134217728000 (Enclosure.Real.IsNear.const Bool.false 779649 2000) RS421to432.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns420p499 Ns420p500) 

noncomputable def Ns420p519 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz68) Bool.false Ns420p497 Ns420p498 6541495969997165973 692224000000000000000000 24983183557 16777216 159 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz68) (@HAdd.hAdd Real Real Real qz341 qz391 (Enclosure.sfrac Bool.true Ns420p499 Ns420p500)) Bool.false Ns420p497 Ns420p498 6541495969997165973 692224000000000000000000 Ns420p501 (Ns420p518 rfl rfl)) 

noncomputable def Ns420p520 := nat_lit 3795204517072394250092544 

noncomputable def Ns420p521 := nat_lit 3500665291357621188046501834174408429976183113421625621515882095377334052796975175322684105904374634829319545014824221075496493736055509681 

noncomputable def Ns420p522 := nat_lit 69061887427279807374175457422696049589758900585025510522285359577850094671315332446731519433112496475662717985575392155893264493730122956800 

noncomputable def Ns420p523 := nat_lit 2480987364339577432520652413719104077430858930829708338211765306891985106566077753382515990789650050363784816464135766729544277922481 

noncomputable def Ns420p524 := nat_lit 17481639196004869467814749547549505215412672665214511288506784322078782210021514145874117462633112682553275077376046072499296243933418853041 

noncomputable def Ns420p525 := nat_lit 2417166059954793258096141009794361735641561520475892868279987585224753313496036635635603180158937376648195129495138725456264257280554303488000 

noncomputable abbrev qz659 := (BSN.sinEvenQ 68719476736)

noncomputable abbrev qz660 := (BSN.sinOddQ 68719476736)

noncomputable def Ns420p526 := BSN.sin_dyadic_bound_f 107866200013 68719476736 4 3 33554432 13533204 Ns420p521 Ns420p522 Ns420p523 Ns420p524 Ns420p525 Ns420p523 33554410 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107866200013) qz659 0 3 Ns420p521 Ns420p522 Ns420p523 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107866200013) qz660 0 3 Ns420p524 Ns420p525 Ns420p523 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p527 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz68) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24983183557) qz364) Bool.false 24983183557 16777216 159 16777216 Bool.false 33554410 33554432 1 6760000 (Ns420p519 rfl) (Enclosure.sfrac_false_div 24983183557 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24983183557) qz364) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns420p520) (@Nat.cast Real Real.instNatCast Ns420p242)) 226375608064910080 72057594037927936 Bool.false 33554410 33554432 236 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q3 24983183557 16777216 226375608064910080 72057594037927936 236 Ns420p520 Ns420p242 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554410 33554432 Ns420p520 Ns420p242 107866200013 68719476736 13533204 13520000 (Ns420p526 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns420p528 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz68) Bool.false Ns420p497 Ns420p498 6541495969997165973 692224000000000000000000 399730936912 268435456 2538 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz68) (@HAdd.hAdd Real Real Real qz341 qz391 (Enclosure.sfrac Bool.true Ns420p499 Ns420p500)) Bool.false Ns420p497 Ns420p498 6541495969997165973 692224000000000000000000 Ns420p501 (Ns420p518 rfl rfl)) 

noncomputable def Ns420p529 := Ns420p496 45930 BSN.abs_quadSignPos (BSN.cos_quad_nat3 603 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267973725 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 402 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 116537666 268435456) qz71 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 1) Bool.false 16777205 16777216 17056519 1772093440000 268435280 268435456 2584 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz68)) Bool.false 16777205 16777216 17056519 1772093440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz68) qz68) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz68)) Bool.false 33554410 33554432 1091617216 113413980160000 16777205 16777216 17056519 1772093440000 (Ns420p527 rfl rfl) rfl)) rfl) (Ns420p528 rfl) RS421to432.d7 

noncomputable def Ns420p530 := nat_lit 38044366371894808322406366299017065012940999766042182072922004306114523512894985570278567109813371875539290625 

noncomputable def Ns420p531 := nat_lit 20006237418911787792321606408704051727109913298361903240940099457790427862076327946044900466543212890625 

noncomputable def Ns420p532 := nat_lit 190018793616081525849964333195989827372954866441157758992238235045774323462316257462705965097294828980844890625 

noncomputable def Ns420p533 := BSN.sin_dyadic_bound_f 405910655 268435456 4 3 268435456 134217728 Ns420p530 Ns420p258 Ns420p531 Ns420p532 Ns420p261 Ns420p531 267973725 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 405910655) qz344 0 3 Ns420p530 Ns420p258 Ns420p531 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 405910655) qz345 0 3 Ns420p532 Ns420p261 Ns420p531 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p534 := nat_lit 4427372621293296929875672133699163136956368760770207671204655134889196388623909066396985534806661371147939601 

noncomputable def Ns420p535 := nat_lit 555490431957485776375925557700511974555847734636529983687407038916339057296301374434891028663745474321 

noncomputable def Ns420p536 := nat_lit 26842532576867259944772633969991587652939484192926796087911587323856467374212580773265203654472607845048479505 

noncomputable def Ns420p537 := BSN.cos_dyadic_bound_f 301108523 268435456 4 3 268435456 134217728 Ns420p534 Ns420p140 Ns420p535 Ns420p536 Ns420p143 Ns420p535 116537666 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 301108523) qz346 0 3 Ns420p534 Ns420p140 Ns420p535 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 301108523) qz347 0 3 Ns420p536 Ns420p143 Ns420p535 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p538 := nat_lit 32565013653389634581716515303173153693272399893347007235414882292703854680691351738878989513194344206568004881 

noncomputable def Ns420p539 := nat_lit 12556591448460670718562922692588665888981308810203942397123489893476298472275739628863380556911059934481 

noncomputable def Ns420p540 := nat_lit 162676238160026530785559937028256825802119326182861502126513322457485640806152962453863015547063614244349549841 

noncomputable def Ns420p541 := BSN.sin_dyadic_bound_f 390456491 268435456 4 3 268435456 134217728 Ns420p538 Ns420p258 Ns420p539 Ns420p540 Ns420p261 Ns420p539 266624214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 390456491) qz344 0 3 Ns420p538 Ns420p258 Ns420p539 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 390456491) qz345 0 3 Ns420p540 Ns420p261 Ns420p539 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p542 := nat_lit 26982915936524238244302272028961 

noncomputable def Ns420p543 := BSN.sin_dyadic_bound_f 72072937 268435456 2 1 268435456 134217728 Ns420p542 Ns420p133 Ns420p542 Ns420p542 Ns420p134 Ns420p542 71210117 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 72072937) qz344 0 1 Ns420p542 Ns420p133 Ns420p542 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 72072937) qz345 0 1 Ns420p542 Ns420p134 Ns420p542 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p544 := Ns420p494 77902 BSN.abs_quadSignPos (BSN.cos_quad_nat3 259 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266624214 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 149 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 71210117 268435456) qz71 rfl rfl (Ns420p529 RS421to432.d9 RS421to432.d11 RS421to432.d13 RS421to432.d17 (Ns420p533 rfl rfl) (Ns420p537 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns420p528 rfl) RS421to432.d19 RS421to432.d21 RS421to432.d23 RS421to432.d25 RS421to432.d17 (Ns420p541 rfl rfl) (Ns420p543 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns420p545 := nat_lit 3585494607717207271344652563425024759753537194899244353718635964451131171194791828983778847663689791142197441 

noncomputable def Ns420p546 := nat_lit 295201614704455465640696563246246390482264379187562650174768993806195110017141926732638929065226631361 

noncomputable def Ns420p547 := nat_lit 21740938474501478566857536957123031407299035855171809239947145194103024460489494401223321957500679236680251585 

noncomputable def Ns420p548 := BSN.cos_dyadic_bound_f 285655919 268435456 4 3 268435456 134217728 Ns420p545 Ns420p140 Ns420p546 Ns420p547 Ns420p143 Ns420p546 130257375 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 285655919) qz346 0 3 Ns420p545 Ns420p140 Ns420p546 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 285655919) qz347 0 3 Ns420p547 Ns420p143 Ns420p546 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p549 := nat_lit 21383042673404145219100920530136261297204867656372410458681042354212180582953956516464634386656320780928946176 

noncomputable def Ns420p550 := nat_lit 3560307920264761513277632624173101060267120195161132202152370626958323257293091432882164949102213861376 

noncomputable def Ns420p551 := nat_lit 106850986356006906310479074338397533290626124066578880058788613582263408946196230059261358189363913223326273536 

noncomputable def Ns420p552 := BSN.sin_dyadic_bound_f 351525874 268435456 4 3 268435456 134217728 Ns420p549 Ns420p258 Ns420p550 Ns420p551 Ns420p261 Ns420p550 259326148 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 351525874) qz344 0 3 Ns420p549 Ns420p258 Ns420p550 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 351525874) qz345 0 3 Ns420p551 Ns420p261 Ns420p550 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p553 := Ns420p492 105049 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130257375 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 259326148 268435456) qz71 rfl rfl (Ns420p544 rfl rfl) (Ns420p528 rfl) RS421to432.d27 RS421to432.d29 RS421to432.d31 RS421to432.d33 RS421to432.d17 (Ns420p548 rfl rfl) (Ns420p552 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p554 := nat_lit 4742450733862301762582062054416 

noncomputable def Ns420p555 := BSN.cos_dyadic_bound_f 46666014 268435456 2 1 268435456 134217728 Ns420p554 Ns420p285 Ns420p554 Ns420p554 Ns420p286 Ns420p554 264389347 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 46666014) qz346 0 1 Ns420p554 Ns420p285 Ns420p554 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 46666014) qz347 0 1 Ns420p554 Ns420p286 Ns420p554 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p556 := nat_lit 29341908494353640834247430614542960559036671797738069786520243404800000 

noncomputable def Ns420p557 := nat_lit 11305880209607129429210177223620368934539664616856692464025600000000 

noncomputable def Ns420p558 := nat_lit 88003113722641708243883871489181640939240936063980495974632679014400000 

noncomputable def Ns420p559 := BSN.cos_dyadic_bound_f 240803640 268435456 3 2 268435456 134217728 Ns420p556 Ns420p156 Ns420p557 Ns420p558 Ns420p159 Ns420p557 167478908 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 240803640) qz346 0 2 Ns420p556 Ns420p156 Ns420p557 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 240803640) qz347 0 2 Ns420p558 Ns420p159 Ns420p557 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p560 := Ns420p490 128769 BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 264389347 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 142 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 167478908 268435456) qz71 rfl rfl (Ns420p553 rfl) (Ns420p528 rfl) RS421to432.d35 RS421to432.d37 RS421to432.d39 RS421to432.d41 RS421to432.d17 (Ns420p555 rfl rfl) (Ns420p559 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p561 := nat_lit 9573618630218365791996648146751671047093382076424643991622520887710172776892144863502870123067356445789065216 

noncomputable def Ns420p562 := nat_lit 5598142912482226005079380234776486770374251331634110848031865745410643829834434294966979338593666011136 

noncomputable def Ns420p563 := nat_lit 58001268847792481161972096104717778409565772737256398128871234420859351415633516186753814989220351745569525760 

noncomputable def Ns420p564 := BSN.cos_dyadic_bound_f 365037094 268435456 4 3 268435456 134217728 Ns420p561 Ns420p140 Ns420p562 Ns420p563 Ns420p143 Ns420p562 56201424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 365037094) qz346 0 3 Ns420p561 Ns420p140 Ns420p562 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 365037094) qz347 0 3 Ns420p563 Ns420p143 Ns420p562 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p565 := nat_lit 27657942865757785769244988870656 

noncomputable def Ns420p566 := BSN.cos_dyadic_bound_f 72519528 268435456 2 1 268435456 134217728 Ns420p565 Ns420p285 Ns420p565 Ns420p565 Ns420p286 Ns420p565 258699086 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 72519528) qz346 0 1 Ns420p565 Ns420p285 Ns420p565 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 72519528) qz347 0 1 Ns420p565 Ns420p286 Ns420p565 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p567 := Ns420p488 150103 BSN.abs_quadSignNeg qz651 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 56201424 268435456) BSN.abs_quadSignNeg qz348 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 258699086 268435456) qz71 rfl rfl (Ns420p560 rfl) (Ns420p528 rfl) RS421to432.d43 RS421to432.d45 RS421to432.d47 RS421to432.d49 RS421to432.d17 (Ns420p564 rfl rfl) (Ns420p566 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p568 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 11) 282787098 268435456 150103 268435456 282787098 268435456 150103 268435456 151820167205093376 141393549 67108864 150103 134217728 (Ns420p567 rfl) 

noncomputable def Ns420p569 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz389) (Zeta.RiemannSiegel.correction qz70) 10053565 33554432 1 33554432 181001199569049 281474976710656 119606182703901 5946158883012608000 1819707324945406109685 9444732965739290427392 

noncomputable def Ns420p570 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz389 1 1 0 1 10053565 33554432 1 33554432 10053565 33554432 1 33554432 

noncomputable def Ns420p571 := @Enclosure.Real.IsNear.sqrt_image qz69 4163600876097 33554432000 779649 33554432000 186887156 186887191 16777216 (@Enclosure.Real.IsNear.of_eq qz69 (@HMul.hMul Real Real Real qz5 qz68 qz3) Bool.false 4163600876097 33554432000 779649 33554432000 (BSN.t_div_two_pi_mk qz68 779649 1000 qz71) (@Enclosure.Real.IsNear.mulLit_ff qz68 qz3 779649 1000 0 1 5340353 33554432 1 33554432 4163600876097 33554432000 779649 33554432000 (Enclosure.Real.IsNear.const Bool.false 779649 1000) RS421to432.d52 rfl)) 

noncomputable abbrev qz813 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 779649 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz661 := qz813

noncomputable abbrev qz393 := qz661

noncomputable abbrev qz75 := qz393

noncomputable def Ns420p572 := @Enclosure.Real.IsNear.sqrt_image qz75 373774347 33554432 35 33554432 55995054 55995061 16777216 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 373774347 33554432 35 33554432 373774347 33554432 35 33554432 (Ns420p571 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns420p573 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz75) 111990115 33554432 7 33554432 5026782 5026783 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz75) Bool.false 111990115 33554432 7 33554432 111990115 33554432 7 33554432 (Ns420p572 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p574 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz75)) Bool.false 10053565 33554432 1 33554432 10053565 33554432 1 33554432 (Ns420p573 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz326 qz322 qz388)

noncomputable abbrev qz662 := (@HMul.hMul Real Real Real qz795 qz812 qz812)

noncomputable abbrev qz394 := (@HSub.hSub Real Real Real qz624 (@HSub.hSub Real Real Real qz624 qz662 qz656) qz634)

noncomputable abbrev qz77 := (Real.cos (@HMul.hMul Real Real Real qz326 qz322 qz394))

noncomputable def Ns420p575 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz70) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz76)) qz77) Bool.false 181001199569049 

noncomputable def Ns420p576 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz76)) qz77 52379989 33554432 551 

noncomputable def Ns420p577 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz76)) Bool.false 52379989 33554432 551 33554432 52379989 33554432 551 

noncomputable def Ns420p578 := @Enclosure.Real.IsNear.recentre' (Real.cos qz76) Bool.false 10747424 16777216 1527514432 226827960320000 335857 524288 23867413 3544186880000 

noncomputable def Ns420p579 := @Enclosure.Real.IsNear.cos_image qz76 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 29377629) qz342) Bool.false 29377629 33554432 221 33554432 Bool.false 10747424 16777216 1 

noncomputable def Ns420p580 := nat_lit 188902527871340929231919217 

noncomputable def Ns420p581 := nat_lit 28823037615171174400000000000000 

noncomputable def Ns420p582 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz70 884279719003555 140737488355328 1 500000000000000 4675595 33554432 35 33554432 4134533832774426740225 4722366482869645213696 Ns420p580 

noncomputable def Ns420p583 := @Enclosure.Real.IsNear.subLit_ff_p qz75 qz1 373774347 33554432 35 33554432 11 1 0 1 4675595 4675595 33554432 35 

noncomputable def Ns420p584 := @Ns420p583 33554432 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 373774347 33554432 35 33554432 373774347 33554432 35 33554432 (Ns420p571 rfl rfl rfl rfl rfl rfl) rfl) qz352 

noncomputable def Ns420p585 := @Enclosure.Real.IsNear.recentre' qz76 Bool.false 4134533832774426740225 4722366482869645213696 Ns420p580 Ns420p581 29377629 33554432 221 33554432 (@Ns420p582 Ns420p581 RS421to432.d51 (Ns420p584 rfl rfl) rfl) 

noncomputable def Ns420p586 := nat_lit 1586820067537390821162237762436814621623692903524234830908590241 

noncomputable def Ns420p587 := nat_lit 554796785092364505381010547355054033839289311318245131520161 

noncomputable def Ns420p588 := nat_lit 4759350609041987734475951266215733756803400131950068002462730401 

noncomputable def Ns420p589 := BSN.cos_dyadic_bound_f 29377629 33554432 3 2 16777216 6760000 Ns420p586 Ns420p181 Ns420p587 Ns420p588 Ns420p184 Ns420p587 10747424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 29377629) qz635 0 2 Ns420p586 Ns420p181 Ns420p587 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 29377629) (BSN.cosOddQ 33554432) 0 2 Ns420p588 Ns420p184 Ns420p587 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p590 := @Enclosure.Real.IsNear.inv_image (Real.cos qz76) 335857 524288 23867413 3544186880000 26189719 26190270 16777216 (Ns420p578 (@Ns420p579 6760000 (Ns420p585 rfl) (Enclosure.sfrac_false_div 29377629 33554432) (Ns420p589 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns420p591 := @Enclosure.Real.IsNear.recentre' qz77 Bool.false 6911082 16777216 

noncomputable abbrev qz78 := (@HMul.hMul Real Real Real qz326 qz322 qz394)

noncomputable def Ns420p592 := @Enclosure.Real.IsNear.cos_image qz78 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4807605)) qz643) Bool.true 4807605 4194304 

noncomputable def Ns420p593 := nat_lit 181626181955735696481366713845 

noncomputable def Ns420p594 := nat_lit 40524935336444573161894526851229133 

noncomputable def Ns420p595 := @Enclosure.Real.IsNear.recentre' qz78 Bool.true Ns420p593 Ns420p190 Ns420p594 

noncomputable abbrev qz79 := qz394

noncomputable def Ns420p596 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz79 884279719003555 140737488355328 1 500000000000000 205394490060679 

noncomputable abbrev qz395 := (@HSub.hSub Real Real Real qz624 qz662 qz656)

noncomputable abbrev qz80 := qz395

noncomputable def Ns420p597 := @Enclosure.Real.IsNear.subLit_tf qz80 qz27 135025745883015 1125899906842624 1501697995 1125899906842624 1 16 

noncomputable abbrev qz396 := qz662

noncomputable abbrev qz81 := qz396

noncomputable def Ns420p598 := @Enclosure.Real.IsNear.subLit_ff_n qz81 qz70 21861188604025 1125899906842624 327292875 1125899906842624 4675595 33554432 35 33554432 

noncomputable def Ns420p599 := @Enclosure.Real.IsNear.mulLit_ff qz70 qz70 4675595 33554432 35 33554432 4675595 33554432 35 33554432 21861188604025 1125899906842624 

noncomputable def Ns420p600 := nat_lit 278041744888205194558030512423894739540040142947083190625 

noncomputable def Ns420p601 := nat_lit 285384397295291920834049226945594467187009074750390625 

noncomputable def Ns420p602 := nat_lit 833554465870024999832423438817793029685746410691748790625 

noncomputable def Ns420p603 := BSN.cos_dyadic_bound_f 4807605 4194304 3 2 16777216 6760000 Ns420p600 Ns420p308 Ns420p601 Ns420p602 Ns420p311 Ns420p601 6911082 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 4807605) (BSN.cosEvenQ 4194304) 0 2 Ns420p600 Ns420p308 Ns420p601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 4807605) (BSN.cosOddQ 4194304) 0 2 Ns420p602 Ns420p311 Ns420p601 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p604 := @Ns420p591 969937216 113413980160000 3455541 8388608 15155269 1772093440000 (@Ns420p592 141 16777216 Bool.false 6911082 16777216 1 6760000 (@Ns420p595 Ns420p193 4807605 4194304 141 16777216 (@Ns420p596 1125899906842624 1501697995 1125899906842624 Ns420p593 Ns420p190 Ns420p594 Ns420p193 RS421to432.d51 (@Ns420p597 0 1 3286311840970864 205394490060679 1125899906842624 1501697995 1125899906842624 (@Ns420p598 4530712208480906772480 135025745883015 1125899906842624 1501697995 1125899906842624 (@Ns420p599 327292875 1125899906842624 (Ns420p584 rfl rfl) (Ns420p584 rfl rfl) rfl) (Ns420p584 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4807605 4194304) (BSN.cos_neg_of_bound 4807605 4194304 Bool.false 6911082 16777216 1 6760000 (Ns420p603 rfl rfl)) rfl rfl) 

noncomputable def Ns420p605 := @Ns420p569 1206292302162623321091 Ns420p484 (Ns420p570 qz29 (@Enclosure.Real.IsNear.of_eq qz389 (@Inv.inv Real Real.instInv (Real.sqrt qz75)) Bool.false 10053565 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz69 (BSN.t_div_two_pi_nonneg qz68 779649 1000 qz71)) Ns420p574) rfl) (@Ns420p575 281474976710656 119606182703901 5946158883012608000 (BSN.correction_mk qz70 (BSN.cos_two_pi_p_ne_zero_mk qz68 779649 1000 11 qz71 rfl rfl (@BSN.floor_sqrt_eq_dec qz68 779649 1000 11 qz71 rfl rfl rfl))) (@Ns420p576 33554432 3455541 8388608 15155269 1772093440000 181001199569049 281474976710656 119606182703901 5946158883012608000 (@Ns420p577 33554432 (Ns420p590 rfl rfl rfl rfl rfl) rfl) (Ns420p604 rfl) rfl)) 

noncomputable def Ns420p606 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz68) (hardyZApproximantRS₀ qz68) Bool.false 21719080280851405088757 9444732965739290427392 224340364006372997977091 Ns420p484 (@Eq.refl Real (hardyZApproximantRS₀ qz68)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz68) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz68) qz68 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz389) (Zeta.RiemannSiegel.correction qz70))) Bool.false 21719080280851405088757 9444732965739290427392 224340364006372997977091 Ns420p484 (BSN.hardyZApproximantRS₀_eq qz68 11 (@BSN.floor_sqrt_eq_dec qz68 779649 1000 11 qz71 rfl rfl rfl)) (@Ns420p486 21719080280851405088757 9444732965739290427392 224340364006372997977091 Ns420p484 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz68) qz68 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz68) qz68 11)) Bool.false 141393549 67108864 150103 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz68) qz68 11) (Ns420p568 (Ns420p567 rfl) rfl rfl)) (Ns420p605 rfl) rfl rfl)) 

theorem RS421to432.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz68) Bool.false 21719080280851405088757 9444732965739290427392 224340364006372997977091 Ns420p484 := Ns420p606 

noncomputable def Ns420p607 := nat_lit 498799959753106275696640000 

noncomputable def Ns420p608 := nat_lit 1871123415677002325599232983040 

noncomputable abbrev qz814 := (Enclosure.sfrac Bool.false 780953 1000)

noncomputable abbrev qz663 := qz814

noncomputable abbrev qz397 := qz663

noncomputable abbrev qz82 := qz397

noncomputable abbrev qz815 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 780953 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz664 := qz815

noncomputable abbrev qz398 := qz664

noncomputable abbrev qz83 := qz398

noncomputable abbrev qz816 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 780953 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz665 := qz816

noncomputable abbrev qz399 := qz665

noncomputable abbrev qz84 := qz399

noncomputable abbrev qz400 := (@HPow.hPow Real Real Real qz623 qz83 qz8)

noncomputable def Ns420p609 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz82) qz82 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz400) (Zeta.RiemannSiegel.correction qz84)) 421484615 134217728 150355 134217728 888715708585189152375 4722366482869645213696 3359242394936516625409 Ns420p607 Ns420p608 

noncomputable def Ns420p610 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz82) qz82 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 780953 1000 194 242 268435456 134217728 4503599627370496 Bool.false 400574848453 2542 

noncomputable def Ns420p611 := Ns420p610 618095470 41 84886744 8 643680110 41 80936328 8 Bool.true 313848218 128986 Bool.true 327122046 Bool.true 67966851 14148475504056880 1 Bool.false 92593340 Bool.true Bool.false 259876850 Bool.true Bool.true 421484615 

noncomputable def Ns420p612 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz82) qz82 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 780953 1000 83 142 268435456 134217728 4503599627370496 Bool.false 400574848453 2542 

noncomputable def Ns420p613 := Ns420p612 558195838 41 94906264 8 589812974 41 89478488 8 Bool.true 332697893 105227 Bool.true 352299274 Bool.true 166008217 14148475504056880 1 Bool.false 259524840 Bool.false Bool.false 218718625 Bool.true Bool.true 313848218 

noncomputable def Ns420p614 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz82) qz82 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 780953 1000 59 17 268435456 134217728 4503599627370496 Bool.false 400574848453 2542 

noncomputable def Ns420p615 := Ns420p614 480971758 41 109588312 8 522351262 41 101459064 8 Bool.true 299549695 78035 Bool.false 80722859 Bool.true 188760379 14148475504056880 1 Bool.false 79511717 Bool.false Bool.false 173584357 Bool.true Bool.true 332697893 

noncomputable def Ns420p616 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz82) qz82 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 780953 1000 260 149 268435456 134217728 4503599627370496 Bool.false 400574848453 2542 

noncomputable def Ns420p617 := Ns420p616 372130544 40 134217720 8 432030192 40 120047984 16 Bool.true 229592027 46010 Bool.false 327452375 Bool.false 352617108 14148475504056880 1 Bool.false 92283215 Bool.false Bool.false 259605869 Bool.true Bool.true 299549695 

noncomputable def Ns420p618 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz82) qz82 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 780953 1000 605 403 268435456 134217728 4503599627370496 Bool.false 400574848453 2542 

noncomputable def Ns420p619 := Ns420p618 186065264 40 189812528 16 294906480 40 154981288 8 Bool.true 268435296 2592 Bool.false 163878235 Bool.false 338804586 14148475504056880 1 Bool.false 153886610 Bool.true Bool.false 255750340 Bool.false Bool.true 229592027 

noncomputable def Ns420p620 := nat_lit 54885293791981575814506298688106400509894020883611590588487 

noncomputable def Ns420p621 := nat_lit 36780039794400811759886753913904164986104139558682624000 

noncomputable def Ns420p622 := nat_lit 139433194110711107088515388796640000 

noncomputable def Ns420p623 := nat_lit 653344752421972638954037540662230387520 

noncomputable abbrev qz85 := (@Eq.refl Real qz397)

noncomputable def Ns420p624 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz82 780953 1000 2439551352836 16000000 1561906 4000 2000 Ns420p622 Ns420p623 qz85 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns420p625 := nat_lit 17563294013434104260642015580194048163166086682755708988315840 

noncomputable abbrev qz401 := (@HMul.hMul Real Real Real qz619 qz625 (@HSub.hSub Real Real Real qz624 qz626 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 (@Nat.cast Real Real.instNatCast 1561906)))))

noncomputable abbrev qz666 := (Real.log (Enclosure.sfrac Bool.false 2439551352836 16000000))

noncomputable abbrev qz667 := (Enclosure.sfrac Bool.false 780953 2000)

noncomputable abbrev qz86 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 780953 4000) qz666) qz401) qz667)

noncomputable abbrev qz402 := (@HSub.hSub Real Real Real qz11 qz86 (@HMul.hMul Real Real Real qz5 qz667 (Real.log Real.pi)))

noncomputable def Ns420p626 := @Enclosure.Real.IsNear.addLit_ft_p qz402 (Enclosure.sfrac Bool.true Ns420p622 Ns420p623) 26882126871198479305167 18014398509481984000 6552394115630346381 692224000000000000000000 Ns420p622 Ns420p623 0 1 Ns420p625 

noncomputable def Ns420p627 := nat_lit 360805799246000852939453340057600 

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz5 qz667 (Real.log Real.pi))

noncomputable def Ns420p628 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz403 6986876997170561945283 3602879701896396800 2465480368762469 676000000000000000000 29996999035233 67108864000 780953 134217728000 Ns420p627 26882126871198479305167 18014398509481984000 

noncomputable def Ns420p629 := nat_lit 69868769971705619452830000 

noncomputable abbrev qz87 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 780953 4000) qz666) qz401)

noncomputable def Ns420p630 := @Enclosure.Real.IsNear.subLit_ff_p qz87 qz667 41968584265440551651791 18014398509481984000 2465480368762469 676000000000000000000 780953 2000 0 1 Ns420p629 6986876997170561945283 3602879701896396800 2465480368762469 676000000000000000000 

noncomputable def Ns420p631 := nat_lit 94504850229552665002844422053369479168 

noncomputable def Ns420p632 := nat_lit 57712841911019793157193728 

noncomputable def Ns420p633 := nat_lit 915443601795987514115735372432051099400980185219574201692515556414496912609280 

noncomputable def Ns420p634 := nat_lit 1744147576187689882692982582860473490465249909160768919370283526609793478656 

noncomputable def Ns420p635 := nat_lit 24170680070712849920618871231198817854208559320081616090506467056087040 

noncomputable def Ns420p636 := BSN.log_dyadic_bound 342399352836 4536703352836 4 3 Ns420p633 134217728 54080000 Ns420p634 Ns420p635 20298272 4879102705672 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 342399352836) (BSN.artanhQ 4536703352836) 0 3 Ns420p634 Ns420p633 Ns420p635 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns420p637 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 780953 4000) qz666 780953 4000 0 1 53749272516947047 4503599627370496 3125002873 169000000000000000 41975655619927347195791 18014398509481984000 2440480368677969 676000000000000000000 (Enclosure.Real.IsNear.const Bool.false 780953 4000) (BSN.isNear_log_sfrac 2439551352836 16000000 53749272516947047 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2439551352836) qz335)) Bool.false Ns420p632 Ns420p103 1000000919360000 54080000000000000000000 53749272516947047 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2439551352836 16000000 17 4879102705672 4194304000000 20298272 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns420p636 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns420p638 := BSN.arctan_dyadic_bound_f 1000 1561906 1 0 16777216 6760000 0 1 1 0 1 1 10741 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1561906) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1561906) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns420p639 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1561906))) 884279719003555 562949953421312 1 2000000000000000 10741 16777216 1 6760000 14829705204692248690688 883919310849443 562949953421312 50000000169 338000000000000000 qz16 (Ns420p638 rfl) rfl rfl 

noncomputable abbrev qz88 := qz401

noncomputable def Ns420p640 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 780953 4000) qz666) qz88 41975655619927347195791 18014398509481984000 2440480368677969 676000000000000000000 883919310849443 2251799813685248 50000000169 1352000000000000000 Ns420p631 41968584265440551651791 18014398509481984000 2465480368762469 676000000000000000000 (Ns420p637 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1561906)))) 1 4 0 1 883919310849443 562949953421312 50000000169 338000000000000000 883919310849443 2251799813685248 50000000169 1352000000000000000 qz340 Ns420p639 rfl) 

noncomputable def Ns420p641 := @Ns420p626 Ns420p620 Ns420p621 6552394115630346381 692224000000000000000000 (@Ns420p628 6552394115630346381 692224000000000000000000 (Ns420p630 (Ns420p640 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 780953 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz667 (Real.log Real.pi) 780953 2000 0 1 38410761 33554432 1 67108864 29996999035233 67108864000 780953 134217728000 (Enclosure.Real.IsNear.const Bool.false 780953 2000) RS421to432.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns420p622 Ns420p623) 

noncomputable def Ns420p642 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz82) Bool.false Ns420p620 Ns420p621 6552394115630346381 692224000000000000000000 6258982007 4194304 319 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz82) (@HAdd.hAdd Real Real Real qz341 qz402 (Enclosure.sfrac Bool.true Ns420p622 Ns420p623)) Bool.false Ns420p620 Ns420p621 6552394115630346381 692224000000000000000000 Ns420p624 (Ns420p641 rfl rfl)) 

noncomputable def Ns420p643 := BSN.cos_dyadic_bound_f 74648320 68719476736 1 0 33554432 13533204 0 1 1 0 1 1 33554412 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 74648320) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 74648320) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns420p644 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz82) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6258982007) qz643) Bool.false 6258982007 4194304 319 33554432 Bool.true 33554412 33554432 1 6760000 (Ns420p642 rfl) (Enclosure.sfrac_false_div 6258982007 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6258982007) qz643) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 656613572476198191104) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 33554412 33554432 237 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q2 6258982007 4194304 226375608064910080 72057594037927936 237 656613572476198191104 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554412 33554432 656613572476198191104 604462909807314587353088 74648320 68719476736 13533204 13520000 (Ns420p643 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns420p645 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz82) Bool.false Ns420p620 Ns420p621 6552394115630346381 692224000000000000000000 400574848453 268435456 2542 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz82) (@HAdd.hAdd Real Real Real qz341 qz402 (Enclosure.sfrac Bool.true Ns420p622 Ns420p623)) Bool.false Ns420p620 Ns420p621 6552394115630346381 692224000000000000000000 Ns420p624 (Ns420p641 rfl rfl)) 

noncomputable def Ns420p646 := Ns420p619 46010 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 605 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 153886610 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 403 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 255750340 268435456) qz85 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz82) qz82 1) Bool.true 8388603 8388608 34218663 3544186880000 268435296 268435456 2592 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz82) qz82 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz82)) Bool.true 8388603 8388608 34218663 3544186880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz82) qz82) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz82)) Bool.true 33554412 33554432 2189994432 226827960320000 8388603 8388608 34218663 3544186880000 (Ns420p644 rfl rfl) rfl)) rfl) (Ns420p645 rfl) RS421to432.d7 

noncomputable def Ns420p647 := nat_lit 11325212550123100017667459895944779099022412376612811801749271509030625 

noncomputable def Ns420p648 := nat_lit 520199850408616831633954880879375150239756235074837621798500390625 

noncomputable def Ns420p649 := nat_lit 29660428736278886095211178086238711985291644238176766886527084951590625 

noncomputable def Ns420p650 := BSN.sin_dyadic_bound_f 163878235 268435456 3 2 268435456 134217728 Ns420p647 Ns420p119 Ns420p648 Ns420p649 Ns420p122 Ns420p648 153886610 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 163878235) qz344 0 2 Ns420p647 Ns420p119 Ns420p648 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 163878235) qz345 0 2 Ns420p649 Ns420p122 Ns420p648 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p651 := nat_lit 18449286404511642994180178127907929984770861955029194172798131946357779616059046093339632780826711162829213696 

noncomputable def Ns420p652 := nat_lit 2287659390226053620073901453634339805323197956382566528197839325532830521696768310131821950437951082496 

noncomputable def Ns420p653 := nat_lit 92198608630323780649181550042279749689026220113761494468166161902420479119258456421405647412337246499201683456 

noncomputable def Ns420p654 := BSN.sin_dyadic_bound_f 338804586 268435456 4 3 268435456 134217728 Ns420p651 Ns420p258 Ns420p652 Ns420p653 Ns420p261 Ns420p652 255750340 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 338804586) qz344 0 3 Ns420p651 Ns420p258 Ns420p652 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 338804586) qz345 0 3 Ns420p653 Ns420p261 Ns420p652 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p655 := nat_lit 6194545834502152098939531219963429442330351535852142096720159143108580241364075498464913943403565191650390625 

noncomputable def Ns420p656 := nat_lit 1519769541639190228311939324922946327941541372127333543873154525280079331932371133007109165191650390625 

noncomputable def Ns420p657 := nat_lit 37547259357704714676148481706682660058002660843821103433549723577853042088584915718865404020628525191650390625 

noncomputable def Ns420p658 := BSN.cos_dyadic_bound_f 327452375 268435456 4 3 268435456 134217728 Ns420p655 Ns420p140 Ns420p656 Ns420p657 Ns420p143 Ns420p656 92283215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 327452375) qz346 0 3 Ns420p655 Ns420p140 Ns420p656 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 327452375) qz347 0 3 Ns420p657 Ns420p143 Ns420p656 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p659 := nat_lit 21650059701512642076536944454363509950447179167621437595948918907569170947070886973255918811826573558086107136 

noncomputable def Ns420p660 := nat_lit 3695222135467844595713282182337647100867053191253587140221899469327968836828497921375137017525893595136 

noncomputable def Ns420p661 := nat_lit 108184458848557715754073703901687725297916493173482792736531271168635278506751739013268530262680127375142813696 

noncomputable def Ns420p662 := BSN.sin_dyadic_bound_f 352617108 268435456 4 3 268435456 134217728 Ns420p659 Ns420p258 Ns420p660 Ns420p661 Ns420p261 Ns420p660 259605869 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 352617108) qz344 0 3 Ns420p659 Ns420p258 Ns420p660 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 352617108) qz345 0 3 Ns420p661 Ns420p261 Ns420p660 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p663 := Ns420p617 78035 BSN.abs_quadSignPos (BSN.cos_quad_nat0 260 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 92283215 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 149 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 259605869 268435456) qz85 rfl rfl (Ns420p646 RS421to432.d9 RS421to432.d11 RS421to432.d13 RS421to432.d17 (Ns420p650 rfl rfl) (Ns420p654 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns420p645 rfl) RS421to432.d19 RS421to432.d21 RS421to432.d23 RS421to432.d25 RS421to432.d17 (Ns420p658 rfl rfl) (Ns420p662 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns420p664 := nat_lit 42460601338012186604806254122161 

noncomputable def Ns420p665 := BSN.sin_dyadic_bound_f 80722859 268435456 2 1 268435456 134217728 Ns420p664 Ns420p133 Ns420p664 Ns420p664 Ns420p134 Ns420p664 79511717 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 80722859) qz344 0 1 Ns420p664 Ns420p133 Ns420p664 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 80722859) qz345 0 1 Ns420p664 Ns420p134 Ns420p664 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p666 := nat_lit 19935162352682789113649689904164003634804509277053094412120003841749985 

noncomputable def Ns420p667 := nat_lit 1611709349716663951318186868718084001106444293214386143735688328161 

noncomputable def Ns420p668 := nat_lit 52208530060936334984589910779784942145629066244378614454176818947290081 

noncomputable def Ns420p669 := BSN.sin_dyadic_bound_f 188760379 268435456 3 2 268435456 134217728 Ns420p666 Ns420p119 Ns420p667 Ns420p668 Ns420p122 Ns420p667 173584357 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 188760379) qz344 0 2 Ns420p666 Ns420p119 Ns420p667 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 188760379) qz345 0 2 Ns420p668 Ns420p122 Ns420p667 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p670 := Ns420p615 105227 BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 79511717 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 173584357 268435456) qz85 rfl rfl (Ns420p663 rfl rfl) (Ns420p645 rfl) RS421to432.d27 RS421to432.d29 RS421to432.d31 RS421to432.d33 RS421to432.d17 (Ns420p665 rfl rfl) (Ns420p669 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p671 := nat_lit 21572030989777456613285714596900621906848511338002038251614822740313403285767060212938774750552734273477349376 

noncomputable def Ns420p672 := nat_lit 3655451099402248702688083586576007201520094973941360033024843669146891637590681691805132797849161240576 

noncomputable def Ns420p673 := nat_lit 107794788608116498395161692810090511661697928569262796488274988459483499004489331939558481580995667015196020736 

noncomputable def Ns420p674 := BSN.sin_dyadic_bound_f 352299274 268435456 4 3 268435456 134217728 Ns420p671 Ns420p258 Ns420p672 Ns420p673 Ns420p261 Ns420p672 259524840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 352299274) qz344 0 3 Ns420p671 Ns420p258 Ns420p672 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 352299274) qz345 0 3 Ns420p673 Ns420p261 Ns420p672 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p675 := nat_lit 6625595941798429751437776254335196815811466447061617022887623588445121 

noncomputable def Ns420p676 := nat_lit 576815179366727668605585587999912605064638769145656119320700386241 

noncomputable def Ns420p677 := nat_lit 19875634195036555798976117591829590622224270063646559756424229364562881 

noncomputable def Ns420p678 := BSN.cos_dyadic_bound_f 166008217 268435456 3 2 268435456 134217728 Ns420p675 Ns420p156 Ns420p676 Ns420p677 Ns420p159 Ns420p676 218718625 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 166008217) qz346 0 2 Ns420p675 Ns420p156 Ns420p676 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 166008217) qz347 0 2 Ns420p677 Ns420p159 Ns420p676 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p679 := Ns420p613 128986 BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 259524840 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 142 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 218718625 268435456) qz85 rfl rfl (Ns420p670 rfl) (Ns420p645 rfl) RS421to432.d35 RS421to432.d37 RS421to432.d39 RS421to432.d41 RS421to432.d17 (Ns420p674 rfl rfl) (Ns420p678 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p680 := nat_lit 6169555044035581966297302292637490380313821224182836195577310434430963897148523698659164334479599430297194496 

noncomputable def Ns420p681 := nat_lit 1501473827889385302789144301849760837970470105985784197928585931854490977887923369708591937595737378816 

noncomputable def Ns420p682 := nat_lit 37395913856136506643878396782244981126665933426918489341139484369648792526508028995411447523232051795590123520 

noncomputable def Ns420p683 := BSN.cos_dyadic_bound_f 327122046 268435456 4 3 268435456 134217728 Ns420p680 Ns420p140 Ns420p681 Ns420p682 Ns420p143 Ns420p681 92593340 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 327122046) qz346 0 3 Ns420p680 Ns420p140 Ns420p681 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 327122046) qz347 0 3 Ns420p682 Ns420p143 Ns420p681 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p684 := nat_lit 21339714051287780324660348152401 

noncomputable def Ns420p685 := BSN.cos_dyadic_bound_f 67966851 268435456 2 1 268435456 134217728 Ns420p684 Ns420p285 Ns420p684 Ns420p684 Ns420p286 Ns420p684 259876850 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 67966851) qz346 0 1 Ns420p684 Ns420p285 Ns420p684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 67966851) qz347 0 1 Ns420p684 Ns420p286 Ns420p684 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p686 := Ns420p611 150355 BSN.abs_quadSignNeg qz651 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 92593340 268435456) BSN.abs_quadSignNeg qz348 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 259876850 268435456) qz85 rfl rfl (Ns420p679 rfl) (Ns420p645 rfl) RS421to432.d43 RS421to432.d45 RS421to432.d47 RS421to432.d49 RS421to432.d17 (Ns420p683 rfl rfl) (Ns420p685 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p687 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz82) qz82 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz82) qz82 11) 421484615 268435456 150355 268435456 421484615 268435456 150355 268435456 226282829649018880 421484615 134217728 150355 134217728 (Ns420p686 rfl) 

noncomputable def Ns420p688 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz400) (Zeta.RiemannSiegel.correction qz84) 5024683 16777216 1 16777216 176870005249125 281474976710656 664829967542651 29730794415063040000 888715708585189152375 4722366482869645213696 

noncomputable def Ns420p689 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz400 1 1 0 1 5024683 16777216 1 16777216 5024683 16777216 1 16777216 

noncomputable def Ns420p690 := @Enclosure.Real.IsNear.sqrt_image qz83 4170564696409 33554432000 780953 33554432000 187043379 187043415 16777216 (@Enclosure.Real.IsNear.of_eq qz83 (@HMul.hMul Real Real Real qz5 qz82 qz3) Bool.false 4170564696409 33554432000 780953 33554432000 (BSN.t_div_two_pi_mk qz82 780953 1000 qz85) (@Enclosure.Real.IsNear.mulLit_ff qz82 qz3 780953 1000 0 1 5340353 33554432 1 33554432 4170564696409 33554432000 780953 33554432000 (Enclosure.Real.IsNear.const Bool.false 780953 1000) RS421to432.d52 rfl)) 

noncomputable abbrev qz817 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 780953 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz668 := qz817

noncomputable abbrev qz404 := qz668

noncomputable abbrev qz89 := qz404

noncomputable def Ns420p691 := @Enclosure.Real.IsNear.sqrt_image qz89 187043397 16777216 9 8388608 56018453 56018460 16777216 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 374086794 33554432 36 33554432 187043397 16777216 9 8388608 (Ns420p690 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns420p692 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz89) 112036913 33554432 7 33554432 5024682 5024684 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz89) Bool.false 112036913 33554432 7 33554432 112036913 33554432 7 33554432 (Ns420p691 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p693 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 10049366 33554432 2 33554432 5024683 16777216 1 16777216 (Ns420p692 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz90 := (@HMul.hMul Real Real Real qz326 qz322 qz399)

noncomputable abbrev qz669 := (@HMul.hMul Real Real Real qz795 qz816 qz816)

noncomputable abbrev qz405 := (@HSub.hSub Real Real Real qz624 (@HSub.hSub Real Real Real qz624 qz669 qz665) qz634)

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz326 qz322 qz405))

noncomputable def Ns420p694 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz84) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz90)) qz91) Bool.false 176870005249125 

noncomputable def Ns420p695 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz90)) qz91 28215975 16777216 329 

noncomputable def Ns420p696 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz90)) Bool.false 56431950 33554432 658 33554432 28215975 16777216 329 

noncomputable def Ns420p697 := @Enclosure.Real.IsNear.recentre' (Real.cos qz90) Bool.false 9975731 16777216 1568074432 226827960320000 9975731 16777216 24501163 3544186880000 

noncomputable def Ns420p698 := @Enclosure.Real.IsNear.cos_image qz90 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3917599) qz643) Bool.false 3917599 4194304 227 33554432 Bool.false 9975731 16777216 1 

noncomputable def Ns420p699 := nat_lit 242874678692108147727057919 

noncomputable def Ns420p700 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz84 884279719003555 140737488355328 1 500000000000000 2494021 16777216 9 8388608 2205412189068965244655 2361183241434822606848 Ns420p699 

noncomputable def Ns420p701 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz1 187043397 16777216 9 8388608 11 1 0 1 2494021 2494021 16777216 9 

noncomputable def Ns420p702 := @Ns420p701 8388608 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 374086794 33554432 36 33554432 187043397 16777216 9 8388608 (Ns420p690 rfl rfl rfl rfl rfl rfl) rfl) qz352 

noncomputable def Ns420p703 := @Enclosure.Real.IsNear.recentre' qz90 Bool.false 2205412189068965244655 2361183241434822606848 Ns420p699 Ns420p302 3917599 4194304 227 33554432 (@Ns420p700 Ns420p302 RS421to432.d51 (Ns420p702 rfl rfl) rfl) 

noncomputable def Ns420p704 := nat_lit 122525230015199096096645983315108902983696164766159681281 

noncomputable def Ns420p705 := nat_lit 55482987942106812919287192912478927837659153025939201 

noncomputable def Ns420p706 := nat_lit 367464724069713074664099375559501751095413175992427165441 

noncomputable def Ns420p707 := BSN.cos_dyadic_bound_f 3917599 4194304 3 2 16777216 6760000 Ns420p704 Ns420p308 Ns420p705 Ns420p706 Ns420p311 Ns420p705 9975731 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3917599) (BSN.cosEvenQ 4194304) 0 2 Ns420p704 Ns420p308 Ns420p705 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3917599) (BSN.cosOddQ 4194304) 0 2 Ns420p706 Ns420p311 Ns420p705 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p708 := @Enclosure.Real.IsNear.inv_image (Real.cos qz90) 9975731 16777216 24501163 3544186880000 28215646 28216304 16777216 (Ns420p697 (@Ns420p698 6760000 (Ns420p703 rfl) (Enclosure.sfrac_false_div 3917599 4194304) (Ns420p707 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns420p709 := @Enclosure.Real.IsNear.recentre' qz91 Bool.false 6268435 16777216 

noncomputable abbrev qz92 := (@HMul.hMul Real Real Real qz326 qz322 qz405)

noncomputable def Ns420p710 := @Enclosure.Real.IsNear.cos_image qz92 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 39858613)) qz342) Bool.true 39858613 33554432 

noncomputable def Ns420p711 := nat_lit 47056745683863341258121971605 

noncomputable def Ns420p712 := nat_lit 1321558603785116156192398518703321 

noncomputable def Ns420p713 := @Enclosure.Real.IsNear.recentre' qz92 Bool.true Ns420p711 Ns420p469 Ns420p712 

noncomputable def Ns420p714 := nat_lit 151115727451828646838272000000000000000 

noncomputable abbrev qz93 := qz405

noncomputable def Ns420p715 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz93 884279719003555 140737488355328 1 500000000000000 53214774321511 

noncomputable abbrev qz406 := (@HSub.hSub Real Real Real qz624 qz669 qz665)

noncomputable abbrev qz94 := qz406

noncomputable def Ns420p716 := @Enclosure.Real.IsNear.subLit_tf qz94 qz27 35622588277095 281474976710656 48971871 35184372088832 1 16 

noncomputable abbrev qz407 := qz669

noncomputable abbrev qz95 := qz407

noncomputable def Ns420p717 := @Enclosure.Real.IsNear.subLit_ff_n qz95 qz84 6220140748441 281474976710656 11223135 35184372088832 2494021 16777216 9 8388608 

noncomputable def Ns420p718 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz84 2494021 16777216 9 8388608 2494021 16777216 9 8388608 6220140748441 281474976710656 

noncomputable def Ns420p719 := nat_lit 5381607047743848235831265127947243301242708636144437597329256801 

noncomputable def Ns420p720 := nat_lit 6370557740918500897567816485185188855616402974225010043220321 

noncomputable def Ns420p721 := nat_lit 16132080027749707705698659750871359526016893102484862771901329761 

noncomputable def Ns420p722 := BSN.cos_dyadic_bound_f 39858613 33554432 3 2 16777216 6760000 Ns420p719 Ns420p181 Ns420p720 Ns420p721 Ns420p184 Ns420p720 6268435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 39858613) qz635 0 2 Ns420p719 Ns420p181 Ns420p720 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 39858613) (BSN.cosOddQ 33554432) 0 2 Ns420p721 Ns420p184 Ns420p720 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p723 := @Ns420p709 2027754432 226827960320000 6268435 16777216 31683663 3544186880000 (@Ns420p710 295 33554432 Bool.false 6268435 16777216 1 6760000 (@Ns420p713 Ns420p714 39858613 33554432 295 33554432 (@Ns420p715 281474976710656 48971871 35184372088832 Ns420p711 Ns420p469 Ns420p712 Ns420p714 RS421to432.d51 (@Ns420p716 0 1 851436389144176 53214774321511 281474976710656 48971871 35184372088832 (@Ns420p717 597647858003890667520 35622588277095 281474976710656 48971871 35184372088832 (@Ns420p718 11223135 35184372088832 (Ns420p702 rfl rfl) (Ns420p702 rfl rfl) rfl) (Ns420p702 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 39858613 33554432) (BSN.cos_neg_of_bound 39858613 33554432 Bool.false 6268435 16777216 1 6760000 (Ns420p722 rfl rfl)) rfl rfl) 

noncomputable def Ns420p724 := @Ns420p688 3359242394936516625409 Ns420p607 (Ns420p689 qz29 (@Enclosure.Real.IsNear.of_eq qz400 (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 5024683 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz83 (BSN.t_div_two_pi_nonneg qz82 780953 1000 qz85)) Ns420p693) rfl) (@Ns420p694 281474976710656 664829967542651 29730794415063040000 (BSN.correction_mk qz84 (BSN.cos_two_pi_p_ne_zero_mk qz82 780953 1000 11 qz85 rfl rfl (@BSN.floor_sqrt_eq_dec qz82 780953 1000 11 qz85 rfl rfl rfl))) (@Ns420p695 16777216 6268435 16777216 31683663 3544186880000 176870005249125 281474976710656 664829967542651 29730794415063040000 (@Ns420p696 16777216 (Ns420p708 rfl rfl rfl rfl rfl) rfl) (Ns420p723 rfl) rfl)) 

noncomputable def Ns420p725 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz82) (hardyZApproximantRS₀ qz82) Bool.true 13940955815292912167305 4722366482869645213696 562130941679536939025409 Ns420p607 (@Eq.refl Real (hardyZApproximantRS₀ qz82)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz82) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz82) qz82 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz400) (Zeta.RiemannSiegel.correction qz84))) Bool.true 13940955815292912167305 4722366482869645213696 562130941679536939025409 Ns420p607 (BSN.hardyZApproximantRS₀_eq qz82 11 (@BSN.floor_sqrt_eq_dec qz82 780953 1000 11 qz85 rfl rfl rfl)) (@Ns420p609 13940955815292912167305 4722366482869645213696 562130941679536939025409 Ns420p607 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz82) qz82 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz82) qz82 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz82) qz82 11)) Bool.true 421484615 134217728 150355 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz82) qz82 11) (Ns420p687 (Ns420p686 rfl) rfl rfl)) (Ns420p724 rfl) rfl rfl)) 

theorem RS421to432.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz82) Bool.true 13940955815292912167305 4722366482869645213696 562130941679536939025409 Ns420p607 := Ns420p725 

noncomputable def Ns420p726 := nat_lit 99759991950621255139328000 

noncomputable def Ns420p727 := nat_lit 122431547428314069512744861696 

noncomputable abbrev qz818 := (Enclosure.sfrac Bool.false 782255 1000)

noncomputable abbrev qz670 := qz818

noncomputable abbrev qz408 := qz670

noncomputable abbrev qz96 := qz408

noncomputable abbrev qz819 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 782255 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz671 := qz819

noncomputable abbrev qz409 := qz671

noncomputable abbrev qz97 := qz409

noncomputable abbrev qz820 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 782255 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz672 := qz820

noncomputable abbrev qz410 := qz672

noncomputable abbrev qz98 := qz410

noncomputable abbrev qz411 := (@HPow.hPow Real Real Real qz623 qz97 qz8)

noncomputable def Ns420p728 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz411) (Zeta.RiemannSiegel.correction qz98)) 1245641 134217728 150601 134217728 868359015287651432895 4722366482869645213696 730760430443834716357 Ns420p726 Ns420p727 

noncomputable def Ns420p729 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 782255 1000 194 242 268435456 134217728 4503599627370496 Bool.false 401417757114 2546 

noncomputable def Ns420p730 := Ns420p729 618095470 41 84886744 8 643680110 41 80936328 8 Bool.false 120224560 129196 Bool.true 288973687 Bool.true 63129693 14148475504056880 1 Bool.false 127346519 Bool.true Bool.false 261046298 Bool.true Bool.false 1245641 

noncomputable def Ns420p731 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 782255 1000 83 142 268435456 134217728 4503599627370496 Bool.false 401417757114 2546 

noncomputable def Ns420p732 := Ns420p731 558195838 41 94906264 8 589812974 41 89478488 8 Bool.false 131472514 105397 Bool.true 236161594 Bool.true 91036048 14148475504056880 1 Bool.false 206854383 Bool.false Bool.false 253146055 Bool.true Bool.false 120224560 

noncomputable def Ns420p733 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 782255 1000 59 17 268435456 134217728 4503599627370496 Bool.false 401417757114 2546 

noncomputable def Ns420p734 := Ns420p733 480971758 41 109588312 8 522351262 41 101459064 8 Bool.false 43209804 78160 Bool.false 297406291 Bool.true 25953061 14148475504056880 1 Bool.false 240189061 Bool.false Bool.false 25912647 Bool.true Bool.false 131472514 

noncomputable def Ns420p735 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 782255 1000 261 150 268435456 134217728 4503599627370496 Bool.false 401417757114 2546 

noncomputable def Ns420p736 := Ns420p735 372130544 40 134217720 8 432030192 40 120047984 16 Bool.false 239706006 46082 Bool.false 264189639 Bool.false 211365031 14148475504056880 1 Bool.false 223558464 Bool.true Bool.false 189432919 Bool.true Bool.false 43209804 

noncomputable def Ns420p737 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 782255 1000 606 404 268435456 134217728 4503599627370496 Bool.false 401417757114 2546 

noncomputable def Ns420p738 := Ns420p737 186065264 40 189812528 16 294906480 40 154981288 8 Bool.false 268435424 2592 Bool.false 342872494 Bool.false 376087582 14148475504056880 1 Bool.false 77658702 Bool.true Bool.false 45351283 Bool.false Bool.false 239706006 

noncomputable def Ns420p739 := nat_lit 711081803294454524698366303030537785013539254137516069 

noncomputable def Ns420p740 := nat_lit 475513513634072941880604702527774926735116809011200 

noncomputable def Ns420p741 := nat_lit 140599386470466191013048876500000000 

noncomputable def Ns420p742 := nat_lit 659907564196195092599279561529045000000 

noncomputable abbrev qz99 := (@Eq.refl Real qz408)

noncomputable def Ns420p743 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz96 782255 1000 2447692540100 16000000 1564510 4000 2000 Ns420p741 Ns420p742 qz99 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns420p744 := nat_lit 3555409016472272623491831515152688925067696270687580345000000 

noncomputable abbrev qz412 := (@HMul.hMul Real Real Real qz619 qz625 (@HSub.hSub Real Real Real qz624 qz626 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 (@Nat.cast Real Real.instNatCast 1564510)))))

noncomputable abbrev qz673 := (Real.log (Enclosure.sfrac Bool.false 2447692540100 16000000))

noncomputable abbrev qz674 := (Enclosure.sfrac Bool.false 782255 2000)

noncomputable abbrev qz100 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 782255 4000) qz673) qz412) qz674)

noncomputable abbrev qz413 := (@HSub.hSub Real Real Real qz11 qz100 (@HMul.hMul Real Real Real qz5 qz674 (Real.log Real.pi)))

noncomputable def Ns420p745 := @Enclosure.Real.IsNear.addLit_ft_p qz413 (Enclosure.sfrac Bool.true Ns420p741 Ns420p742) 5387738701503806893141 3602879701896396800 1312655109263247327 138444800000000000000000 Ns420p741 Ns420p742 0 1 Ns420p744 

noncomputable def Ns420p746 := nat_lit 72313004757351114454812380364800 

noncomputable abbrev qz414 := (@HMul.hMul Real Real Real qz5 qz674 (Real.log Real.pi))

noncomputable def Ns420p747 := @Enclosure.Real.IsNear.subLit_ff_p qz100 qz414 7000875259396259638357 3602879701896396800 493909824500623 135200000000000000000 6009401969211 13421772800 156451 26843545600 Ns420p746 5387738701503806893141 3602879701896396800 

noncomputable def Ns420p748 := nat_lit 14001750518792519276714000 

noncomputable abbrev qz101 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 782255 4000) qz673) qz412)

noncomputable def Ns420p749 := @Enclosure.Real.IsNear.subLit_ff_p qz101 qz674 8410060589999742577749 3602879701896396800 493909824500623 135200000000000000000 782255 2000 0 1 Ns420p748 7000875259396259638357 3602879701896396800 493909824500623 135200000000000000000 

noncomputable def Ns420p750 := nat_lit 18937772869643067205799479762854346752 

noncomputable def Ns420p751 := nat_lit 57728952583923590104088576 

noncomputable def Ns420p752 := nat_lit 925344597385316877320122457163696066263943602372294528277247602105000000000000 

noncomputable def Ns420p753 := nat_lit 1841512332039927948104257172357988396565419791563889287831380471000000000000 

noncomputable def Ns420p754 := nat_lit 27830484555432936087335499682429814497807475764643247486015000000000000 

noncomputable def Ns420p755 := BSN.log_dyadic_bound 350540540100 4544844540100 4 3 Ns420p752 134217728 54080000 Ns420p753 Ns420p754 20745433 4895385080200 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 350540540100) (BSN.artanhQ 4544844540100) 0 3 Ns420p753 Ns420p752 Ns420p754 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns420p756 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 782255 4000) qz673 782255 4000 0 1 53764276750314599 4503599627370496 3125002873 169000000000000000 8411474861863469328149 3602879701896396800 488909824483723 135200000000000000000 (Enclosure.Real.IsNear.const Bool.false 782255 4000) (BSN.isNear_log_sfrac 2447692540100 16000000 53764276750314599 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2447692540100) qz335)) Bool.false Ns420p751 Ns420p103 1000000919360000 54080000000000000000000 53764276750314599 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2447692540100 16000000 17 4895385080200 4194304000000 20745433 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns420p755 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns420p757 := BSN.arctan_dyadic_bound_f 1000 1564510 1 0 16777216 6760000 0 1 1 0 1 1 10723 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1564510) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1564510) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns420p758 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1564510))) 884279719003555 562949953421312 1 2000000000000000 10723 16777216 1 6760000 14829715337791410274304 883919914829219 562949953421312 50000000169 338000000000000000 qz16 (Ns420p757 rfl) rfl rfl 

noncomputable abbrev qz102 := qz412

noncomputable def Ns420p759 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 782255 4000) qz673) qz102 8411474861863469328149 3602879701896396800 488909824483723 135200000000000000000 883919914829219 2251799813685248 50000000169 1352000000000000000 Ns420p750 8410060589999742577749 3602879701896396800 493909824500623 135200000000000000000 (Ns420p756 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1564510)))) 1 4 0 1 883919914829219 562949953421312 50000000169 338000000000000000 883919914829219 2251799813685248 50000000169 1352000000000000000 qz340 Ns420p758 rfl) 

noncomputable def Ns420p760 := @Ns420p745 Ns420p739 Ns420p740 1312655109263247327 138444800000000000000000 (@Ns420p747 1312655109263247327 138444800000000000000000 (Ns420p749 (Ns420p759 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 782255 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz674 (Real.log Real.pi) 782255 2000 0 1 38410761 33554432 1 67108864 6009401969211 13421772800 156451 26843545600 (Enclosure.Real.IsNear.const Bool.false 782255 2000) RS421to432.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns420p741 Ns420p742) 

noncomputable def Ns420p761 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz96) Bool.false Ns420p739 Ns420p740 1312655109263247327 138444800000000000000000 50177219639 33554432 319 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz96) (@HAdd.hAdd Real Real Real qz341 qz413 (Enclosure.sfrac Bool.true Ns420p741 Ns420p742)) Bool.false Ns420p739 Ns420p740 1312655109263247327 138444800000000000000000 Ns420p743 (Ns420p760 rfl rfl)) 

noncomputable def Ns420p762 := nat_lit 7593840541698183185563648 

noncomputable def Ns420p763 := nat_lit 3507012696767597427849292136213515438836397090551395400762452064243432827006380361800402780949586366998592138443540687025442130317463781376 

noncomputable def Ns420p764 := nat_lit 2494480277275220601904164459344377693435675075184575335066248973474268550395156884084330204179605135496995335830504041012655634251776 

noncomputable def Ns420p765 := nat_lit 17513297644986296603498513455985206846474447982726453526765299358041208354132594913461636442906792008122877632072016842606292851511720411136 

noncomputable def Ns420p766 := BSN.sin_dyadic_bound_f 107914964668 68719476736 4 3 33554432 13533204 Ns420p763 Ns420p522 Ns420p764 Ns420p765 Ns420p525 Ns420p764 33554428 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107914964668) qz659 0 3 Ns420p763 Ns420p522 Ns420p764 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107914964668) qz660 0 3 Ns420p765 Ns420p525 Ns420p764 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p767 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz96) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50177219639) qz342) Bool.false 50177219639 33554432 319 33554432 Bool.false 33554428 33554432 1 6760000 (Ns420p761 rfl) (Enclosure.sfrac_false_div 50177219639 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50177219639) qz342) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns420p762) qz343) 226375608064910080 72057594037927936 Bool.false 33554428 33554432 237 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q3 50177219639 33554432 226375608064910080 72057594037927936 237 Ns420p762 Ns420p103 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554428 33554432 Ns420p762 Ns420p103 107914964668 68719476736 13533204 13520000 (Ns420p766 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns420p768 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz96) Bool.false Ns420p739 Ns420p740 1312655109263247327 138444800000000000000000 401417757114 268435456 2546 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz96) (@HAdd.hAdd Real Real Real qz341 qz413 (Enclosure.sfrac Bool.true Ns420p741 Ns420p742)) Bool.false Ns420p739 Ns420p740 1312655109263247327 138444800000000000000000 Ns420p743 (Ns420p760 rfl rfl)) 

noncomputable def Ns420p769 := Ns420p738 46082 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 606 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 77658702 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 404 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 45351283 268435456) qz99 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 1) Bool.false 8388607 8388608 34218663 3544186880000 268435424 268435456 2592 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz96)) Bool.false 8388607 8388608 34218663 3544186880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz96) qz96) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz96)) Bool.false 33554428 33554432 2189994432 226827960320000 8388607 8388608 34218663 3544186880000 (Ns420p767 rfl rfl) rfl)) rfl) (Ns420p768 rfl) RS421to432.d7 

noncomputable def Ns420p770 := nat_lit 7448400791764312273005674026158636922677825793497709357436697668329695686988739519640584111974593774280380416 

noncomputable def Ns420p771 := nat_lit 2639926023909753096295908531455999087306688794459076137758998919148227014463631286682323529016776462336 

noncomputable def Ns420p772 := nat_lit 45139297796403260154169770329223455787572825984771260594650235493558519445666052935708137385443074892101980160 

noncomputable def Ns420p773 := BSN.cos_dyadic_bound_f 342872494 268435456 4 3 268435456 134217728 Ns420p770 Ns420p140 Ns420p771 Ns420p772 Ns420p143 Ns420p771 77658702 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 342872494) qz346 0 3 Ns420p770 Ns420p140 Ns420p771 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 342872494) qz347 0 3 Ns420p772 Ns420p143 Ns420p771 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p774 := nat_lit 10789366252441639016257447479081788694828464459187825178243460247606396005620872931817931771601635909662150656 

noncomputable def Ns420p775 := nat_lit 8006964901308258695864559306617092844187087140403043135205402808125294654832186392182680909529440587776 

noncomputable def Ns420p776 := nat_lit 65355598326142858993605049407075185358140999202000065237998514303938358604250544335605206036569357445995171840 

noncomputable def Ns420p777 := BSN.cos_dyadic_bound_f 376087582 268435456 4 3 268435456 134217728 Ns420p774 Ns420p140 Ns420p775 Ns420p776 Ns420p143 Ns420p775 45351283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 376087582) qz346 0 3 Ns420p774 Ns420p140 Ns420p775 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 376087582) qz347 0 3 Ns420p776 Ns420p143 Ns420p775 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p778 := nat_lit 76513690346281396000453183603733771257404968886161765207352200652542145 

noncomputable def Ns420p779 := nat_lit 23731558025126067452216545019401290351107513719455296314419005247681 

noncomputable def Ns420p780 := nat_lit 200354576003458213987216654079747513108825506346306457444270513795780801 

noncomputable def Ns420p781 := BSN.sin_dyadic_bound_f 264189639 268435456 3 2 268435456 134217728 Ns420p778 Ns420p119 Ns420p779 Ns420p780 Ns420p122 Ns420p779 223558464 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 264189639) qz344 0 2 Ns420p778 Ns420p119 Ns420p779 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 264189639) qz345 0 2 Ns420p780 Ns420p122 Ns420p779 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p782 := nat_lit 17414086753270045620528059651359711947057631264443390971679477331024321 

noncomputable def Ns420p783 := nat_lit 3983502565836887958369527184092765072682138239021778122579763157441 

noncomputable def Ns420p784 := nat_lit 52234293254678463085667439899710950311027529516852129358793272466758081 

noncomputable def Ns420p785 := BSN.cos_dyadic_bound_f 211365031 268435456 3 2 268435456 134217728 Ns420p782 Ns420p156 Ns420p783 Ns420p784 Ns420p159 Ns420p783 189432919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 211365031) qz346 0 2 Ns420p782 Ns420p156 Ns420p783 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 211365031) qz347 0 2 Ns420p784 Ns420p159 Ns420p783 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p786 := Ns420p736 78160 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 261 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 223558464 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 150 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 189432919 268435456) qz99 rfl rfl (Ns420p769 RS421to432.d9 RS421to432.d11 RS421to432.d13 RS421to432.d17 (Ns420p773 rfl rfl) (Ns420p777 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns420p768 rfl) RS421to432.d19 RS421to432.d21 RS421to432.d23 RS421to432.d25 RS421to432.d17 (Ns420p781 rfl rfl) (Ns420p785 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns420p787 := nat_lit 122901800117594344445198128005026097401761323953793413169686625380530465 

noncomputable def Ns420p788 := nat_lit 61207015980790413868389677853117775419373982449960550019557700729121 

noncomputable def Ns420p789 := nat_lit 321786569901159146210208180534734731082505433431206622172957115909732641 

noncomputable def Ns420p790 := BSN.sin_dyadic_bound_f 297406291 268435456 3 2 268435456 134217728 Ns420p787 Ns420p119 Ns420p788 Ns420p789 Ns420p122 Ns420p788 240189061 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 297406291) qz344 0 2 Ns420p787 Ns420p119 Ns420p788 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 297406291) qz345 0 2 Ns420p789 Ns420p122 Ns420p788 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p791 := nat_lit 453684926255237920325499417841 

noncomputable def Ns420p792 := BSN.sin_dyadic_bound_f 25953061 268435456 2 1 268435456 134217728 Ns420p791 Ns420p133 Ns420p791 Ns420p791 Ns420p134 Ns420p791 25912647 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 25953061) qz344 0 1 Ns420p791 Ns420p133 Ns420p791 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 25953061) qz345 0 1 Ns420p791 Ns420p134 Ns420p791 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p793 := Ns420p734 105397 BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 240189061 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 25912647 268435456) qz99 rfl rfl (Ns420p786 rfl rfl) (Ns420p768 rfl) RS421to432.d27 RS421to432.d29 RS421to432.d31 RS421to432.d33 RS421to432.d17 (Ns420p790 rfl rfl) (Ns420p792 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p794 := nat_lit 48849982733148331427813539749373234031547235439563254319682012492243200 

noncomputable def Ns420p795 := nat_lit 9675516809693402901006101209259509525671218885611562521129474498816 

noncomputable def Ns420p796 := nat_lit 127924765845315650134814784703543478495772625130184199736037727854305536 

noncomputable def Ns420p797 := BSN.sin_dyadic_bound_f 236161594 268435456 3 2 268435456 134217728 Ns420p794 Ns420p119 Ns420p795 Ns420p796 Ns420p122 Ns420p795 206854383 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 236161594) qz344 0 2 Ns420p794 Ns420p119 Ns420p795 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 236161594) qz345 0 2 Ns420p796 Ns420p122 Ns420p795 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p798 := nat_lit 599136530535049445085201542886888946814392411842031579398790275137536 

noncomputable def Ns420p799 := nat_lit 4717448515337504054627217329060030887375282469751559825502765056 

noncomputable def Ns420p800 := nat_lit 1797400156708117660247495374226008720381402484961155235076719819882496 

noncomputable def Ns420p801 := BSN.cos_dyadic_bound_f 91036048 268435456 3 2 268435456 134217728 Ns420p798 Ns420p156 Ns420p799 Ns420p800 Ns420p159 Ns420p799 253146055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 91036048) qz346 0 2 Ns420p798 Ns420p156 Ns420p799 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 91036048) qz347 0 2 Ns420p800 Ns420p159 Ns420p799 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p802 := Ns420p732 129196 BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 206854383 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 142 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 253146055 268435456) qz99 rfl rfl (Ns420p793 rfl) (Ns420p768 rfl) RS421to432.d35 RS421to432.d37 RS421to432.d39 RS421to432.d41 RS421to432.d17 (Ns420p797 rfl rfl) (Ns420p801 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p803 := nat_lit 3755130404185140453764929765422044214986734351543482391664488157679588905265286953832436151227499276121448161 

noncomputable def Ns420p804 := nat_lit 339077981704508985593641931702134133893571071044742178791006536116215548638728511133145651265144659681 

noncomputable def Ns420p805 := nat_lit 22768991605027129603188457313791627875037196393328798753029362527036428955150446067088033047439391480396685025 

noncomputable def Ns420p806 := BSN.cos_dyadic_bound_f 288973687 268435456 4 3 268435456 134217728 Ns420p803 Ns420p140 Ns420p804 Ns420p805 Ns420p143 Ns420p804 127346519 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 288973687) qz346 0 3 Ns420p803 Ns420p140 Ns420p804 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 288973687) qz347 0 3 Ns420p805 Ns420p143 Ns420p804 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p807 := nat_lit 15883079490308788012051936514001 

noncomputable def Ns420p808 := BSN.cos_dyadic_bound_f 63129693 268435456 2 1 268435456 134217728 Ns420p807 Ns420p285 Ns420p807 Ns420p807 Ns420p286 Ns420p807 261046298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 63129693) qz346 0 1 Ns420p807 Ns420p285 Ns420p807 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 63129693) qz347 0 1 Ns420p807 Ns420p286 Ns420p807 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p809 := Ns420p730 150601 BSN.abs_quadSignNeg qz651 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127346519 268435456) BSN.abs_quadSignNeg qz348 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 261046298 268435456) qz99 rfl rfl (Ns420p802 rfl) (Ns420p768 rfl) RS421to432.d43 RS421to432.d45 RS421to432.d47 RS421to432.d49 RS421to432.d17 (Ns420p806 rfl rfl) (Ns420p808 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p810 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 11) 1245641 268435456 150601 268435456 1245641 268435456 150601 268435456 668748419694592 1245641 134217728 150601 134217728 (Ns420p809 rfl) 

noncomputable def Ns420p811 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz411) (Zeta.RiemannSiegel.correction qz98) 5022591 16777216 1 16777216 172890648529345 281474976710656 144767505601421 5946158883012608000 868359015287651432895 4722366482869645213696 

noncomputable def Ns420p812 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz411 1 1 0 1 5022591 16777216 1 16777216 5022591 16777216 1 16777216 

noncomputable def Ns420p813 := @Enclosure.Real.IsNear.sqrt_image qz97 835503567203 6710886400 156451 6710886400 187199233 187199269 16777216 (@Enclosure.Real.IsNear.of_eq qz97 (@HMul.hMul Real Real Real qz5 qz96 qz3) Bool.false 835503567203 6710886400 156451 6710886400 (BSN.t_div_two_pi_mk qz96 782255 1000 qz99) (@Enclosure.Real.IsNear.mulLit_ff qz96 qz3 782255 1000 0 1 5340353 33554432 1 33554432 835503567203 6710886400 156451 6710886400 (Enclosure.Real.IsNear.const Bool.false 782255 1000) RS421to432.d52 rfl)) 

noncomputable abbrev qz821 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 782255 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz675 := qz821

noncomputable abbrev qz415 := qz675

noncomputable abbrev qz103 := qz415

noncomputable def Ns420p814 := @Enclosure.Real.IsNear.sqrt_image qz103 187199251 16777216 9 8388608 56041787 56041794 16777216 (@Enclosure.Real.IsNear.recentre' qz103 Bool.false 374398502 33554432 36 33554432 187199251 16777216 9 8388608 (Ns420p813 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns420p815 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz103) 112083581 33554432 7 33554432 5022590 5022592 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz103) Bool.false 112083581 33554432 7 33554432 112083581 33554432 7 33554432 (Ns420p814 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p816 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz103)) Bool.false 10045182 33554432 2 33554432 5022591 16777216 1 16777216 (Ns420p815 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz104 := (@HMul.hMul Real Real Real qz326 qz322 qz410)

noncomputable abbrev qz676 := (@HMul.hMul Real Real Real qz795 qz820 qz820)

noncomputable abbrev qz416 := (@HSub.hSub Real Real Real qz624 (@HSub.hSub Real Real Real qz624 qz676 qz672) qz634)

noncomputable abbrev qz105 := (Real.cos (@HMul.hMul Real Real Real qz326 qz322 qz416))

noncomputable def Ns420p817 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz98) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz104)) qz105) Bool.false 172890648529345 

noncomputable def Ns420p818 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz104)) qz105 61378063 33554432 777 

noncomputable def Ns420p819 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz104)) Bool.false 61378063 33554432 777 33554432 61378063 33554432 777 

noncomputable def Ns420p820 := @Enclosure.Real.IsNear.recentre' (Real.cos qz104) Bool.false 9171843 16777216 1568074432 226827960320000 9171843 16777216 24501163 3544186880000 

noncomputable def Ns420p821 := @Enclosure.Real.IsNear.cos_image qz104 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 33299311) qz342) Bool.false 33299311 33554432 227 33554432 Bool.false 9171843 16777216 1 

noncomputable def Ns420p822 := nat_lit 242874678692777535560008703 

noncomputable def Ns420p823 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz98 884279719003555 140737488355328 1 500000000000000 2649875 16777216 9 8388608 2343230720394545305625 2361183241434822606848 Ns420p822 

noncomputable def Ns420p824 := @Enclosure.Real.IsNear.subLit_ff_p qz103 qz1 187199251 16777216 9 8388608 11 1 0 1 2649875 2649875 16777216 9 

noncomputable def Ns420p825 := @Ns420p824 8388608 (@Enclosure.Real.IsNear.recentre' qz103 Bool.false 374398502 33554432 36 33554432 187199251 16777216 9 8388608 (Ns420p813 rfl rfl rfl rfl rfl rfl) rfl) qz352 

noncomputable def Ns420p826 := @Enclosure.Real.IsNear.recentre' qz104 Bool.false 2343230720394545305625 2361183241434822606848 Ns420p822 Ns420p302 33299311 33554432 227 33554432 (@Ns420p823 Ns420p302 RS421to432.d51 (Ns420p825 rfl rfl) rfl) 

noncomputable def Ns420p827 := nat_lit 2619995237467066837882453955967887719126958361553580573412524161 

noncomputable def Ns420p828 := nat_lit 1511756973043810951846543956638177917358227869723187689521281 

noncomputable def Ns420p829 := nat_lit 7856962198455112891743668779990386801546158628921295344858529921 

noncomputable def Ns420p830 := BSN.cos_dyadic_bound_f 33299311 33554432 3 2 16777216 6760000 Ns420p827 Ns420p181 Ns420p828 Ns420p829 Ns420p184 Ns420p828 9171843 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 33299311) qz635 0 2 Ns420p827 Ns420p181 Ns420p828 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 33299311) (BSN.cosOddQ 33554432) 0 2 Ns420p829 Ns420p184 Ns420p828 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p831 := @Enclosure.Real.IsNear.inv_image (Real.cos qz104) 9171843 16777216 24501163 3544186880000 30688643 30689420 16777216 (Ns420p820 (@Ns420p821 6760000 (Ns420p826 rfl) (Enclosure.sfrac_false_div 33299311 33554432) (Ns420p830 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns420p832 := @Enclosure.Real.IsNear.recentre' qz105 Bool.false 5633630 16777216 

noncomputable abbrev qz106 := (@HMul.hMul Real Real Real qz326 qz322 qz416)

noncomputable def Ns420p833 := @Enclosure.Real.IsNear.cos_image qz106 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 20608325)) qz364) Bool.true 20608325 16777216 

noncomputable def Ns420p834 := nat_lit 48660032760703838293005492005 

noncomputable def Ns420p835 := nat_lit 670242549436334067440134420578361 

noncomputable def Ns420p836 := @Enclosure.Real.IsNear.recentre' qz106 Bool.true Ns420p834 Ns420p469 Ns420p835 

noncomputable def Ns420p837 := nat_lit 75557863725914323419136000000000000000 

noncomputable abbrev qz107 := qz416

noncomputable def Ns420p838 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz107 884279719003555 140737488355328 1 500000000000000 55027873776791 

noncomputable abbrev qz417 := (@HSub.hSub Real Real Real qz624 qz676 qz672)

noncomputable abbrev qz108 := qz417

noncomputable def Ns420p839 := @Enclosure.Real.IsNear.subLit_tf qz108 qz27 37435687732375 281474976710656 24836607 17592186044416 1 16 

noncomputable abbrev qz418 := qz676

noncomputable abbrev qz109 := qz418

noncomputable def Ns420p840 := @Enclosure.Real.IsNear.subLit_ff_n qz109 qz98 7021837515625 281474976710656 5962239 17592186044416 2649875 16777216 9 8388608 

noncomputable def Ns420p841 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz98 2649875 16777216 9 8388608 2649875 16777216 9 8388608 7021837515625 281474976710656 

noncomputable def Ns420p842 := nat_lit 24040736736298071838536444629933464861549690884044003400390625 

noncomputable def Ns420p843 := nat_lit 253092741970790968397859029543733109897246971520789871559966720 

noncomputable def Ns420p844 := nat_lit 32534306786860915217933199321618749509827701880035400390625 

noncomputable def Ns420p845 := nat_lit 72057141595320493685173467491157157085629417248371939400390625 

noncomputable def Ns420p846 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400 

noncomputable def Ns420p847 := BSN.cos_dyadic_bound_f 20608325 16777216 3 2 16777216 6760000 Ns420p842 Ns420p843 Ns420p844 Ns420p845 Ns420p846 Ns420p844 5633630 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 20608325) (BSN.cosEvenQ 16777216) 0 2 Ns420p842 Ns420p843 Ns420p844 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 20608325) (BSN.cosOddQ 16777216) 0 2 Ns420p845 Ns420p846 Ns420p844 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p848 := @Ns420p832 2054794432 226827960320000 2816815 8388608 32106163 3544186880000 (@Ns420p833 299 33554432 Bool.false 5633630 16777216 1 6760000 (@Ns420p836 Ns420p837 20608325 16777216 299 33554432 (@Ns420p838 281474976710656 24836607 17592186044416 Ns420p834 Ns420p469 Ns420p835 Ns420p837 RS421to432.d51 (@Ns420p839 0 1 880445980428656 55027873776791 281474976710656 24836607 17592186044416 (@Ns420p840 628066619194605568000 37435687732375 281474976710656 24836607 17592186044416 (@Ns420p841 5962239 17592186044416 (Ns420p825 rfl rfl) (Ns420p825 rfl rfl) rfl) (Ns420p825 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 20608325 16777216) (BSN.cos_neg_of_bound 20608325 16777216 Bool.false 5633630 16777216 1 6760000 (Ns420p847 rfl rfl)) rfl rfl) 

noncomputable def Ns420p849 := @Ns420p811 730760430443834716357 Ns420p726 (Ns420p812 qz29 (@Enclosure.Real.IsNear.of_eq qz411 (@Inv.inv Real Real.instInv (Real.sqrt qz103)) Bool.false 5022591 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz97 (BSN.t_div_two_pi_nonneg qz96 782255 1000 qz99)) Ns420p816) rfl) (@Ns420p817 281474976710656 144767505601421 5946158883012608000 (BSN.correction_mk qz98 (BSN.cos_two_pi_p_ne_zero_mk qz96 782255 1000 11 qz99 rfl rfl (@BSN.floor_sqrt_eq_dec qz96 782255 1000 11 qz99 rfl rfl rfl))) (@Ns420p818 33554432 2816815 8388608 32106163 3544186880000 172890648529345 281474976710656 144767505601421 5946158883012608000 (@Ns420p819 33554432 (Ns420p831 rfl rfl rfl rfl rfl) rfl) (Ns420p848 rfl) rfl)) 

noncomputable def Ns420p850 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz96) (hardyZApproximantRS₀ qz96) Bool.false 912186111720756214207 4722366482869645213696 112667944673016556892357 Ns420p726 (@Eq.refl Real (hardyZApproximantRS₀ qz96)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz96) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz411) (Zeta.RiemannSiegel.correction qz98))) Bool.false 912186111720756214207 4722366482869645213696 112667944673016556892357 Ns420p726 (BSN.hardyZApproximantRS₀_eq qz96 11 (@BSN.floor_sqrt_eq_dec qz96 782255 1000 11 qz99 rfl rfl rfl)) (@Ns420p728 912186111720756214207 4722366482869645213696 112667944673016556892357 Ns420p726 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 11)) Bool.false 1245641 134217728 150601 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz96) qz96 11) (Ns420p810 (Ns420p809 rfl) rfl rfl)) (Ns420p849 rfl) rfl rfl)) 

theorem RS421to432.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz96) Bool.false 912186111720756214207 4722366482869645213696 112667944673016556892357 Ns420p726 := Ns420p850 

noncomputable def Ns420p851 := nat_lit 49879995975310627569664000 

noncomputable def Ns420p852 := nat_lit 185890657675699312704568164352 

noncomputable abbrev qz822 := (Enclosure.sfrac Bool.false 783557 1000)

noncomputable abbrev qz677 := qz822

noncomputable abbrev qz419 := qz677

noncomputable abbrev qz110 := qz419

noncomputable abbrev qz823 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 783557 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz678 := qz823

noncomputable abbrev qz420 := qz678

noncomputable abbrev qz111 := qz420

noncomputable abbrev qz824 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 783557 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz679 := qz824

noncomputable abbrev qz421 := qz679

noncomputable abbrev qz112 := qz421

noncomputable abbrev qz422 := (@HPow.hPow Real Real Real qz623 qz111 qz8)

noncomputable def Ns420p853 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz110) qz110 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz422) (Zeta.RiemannSiegel.correction qz112)) 84758417 33554432 37715 33554432 424370053864868287077 2361183241434822606848 402796610929025406601 Ns420p851 Ns420p852 

noncomputable def Ns420p854 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz110) qz110 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 783557 1000 194 242 268435456 134217728 4503599627370496 Bool.false 402260956887 2551 

noncomputable def Ns420p855 := Ns420p854 618095470 41 84886744 8 643680110 41 80936328 8 Bool.true 209456860 129419 Bool.true 250534216 Bool.true 58001423 14148475504056880 1 Bool.false 159766124 Bool.true Bool.false 262193551 Bool.true Bool.true 339033668 

noncomputable def Ns420p856 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz110) qz110 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 783557 1000 83 142 268435456 134217728 4503599627370496 Bool.false 402260956887 2551 

noncomputable def Ns420p857 := Ns420p856 558195838 41 94906264 8 589812974 41 89478488 8 Bool.true 161074960 105580 Bool.true 119732802 Bool.true 15772767 14148475504056880 1 Bool.false 115801945 Bool.false Bool.false 267972200 Bool.true Bool.true 209456860 

noncomputable def Ns420p858 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz110) qz110 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 783557 1000 60 16 268435456 134217728 4503599627370496 Bool.false 402260956887 2551 

noncomputable def Ns420p859 := Ns420p858 480971758 41 109588312 8 522351262 41 101459064 8 Bool.true 313800433 78297 Bool.false 92723407 Bool.true 284512059 14148475504056880 1 Bool.false 252579720 Bool.false Bool.false 131256355 Bool.false Bool.true 161074960 

noncomputable def Ns420p860 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz110) qz110 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 783557 1000 262 151 268435456 134217728 4503599627370496 Bool.false 402260956887 2551 

noncomputable def Ns420p861 := Ns420p860 372130544 40 134217720 8 432030192 40 120047984 16 Bool.true 246683743 46164 Bool.false 201218016 Bool.false 70404065 14148475504056880 1 Bool.false 196485228 Bool.true Bool.false 69599671 Bool.false Bool.true 313800433 

noncomputable def Ns420p862 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz110) qz110 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 783557 1000 608 405 268435456 134217728 4503599627370496 Bool.false 402260956887 2551 

noncomputable def Ns420p863 := Ns420p862 186065264 40 189812528 16 294906480 40 154981288 8 Bool.true 268435352 2600 Bool.false 100500437 Bool.false 413661689 14148475504056880 1 Bool.false 249840842 Bool.false Bool.false 268316382 Bool.true Bool.true 246683743 

noncomputable def Ns420p864 := nat_lit 56228225555323441597054795859501818846164768842441312552579 

noncomputable def Ns420p865 := nat_lit 37522034163570351154534168979849154043007850610950144000 

noncomputable def Ns420p866 := nat_lit 141773368857547855394992164587360000 

noncomputable def Ns420p867 := nat_lit 666525220146680495406140369493804237120 

noncomputable abbrev qz113 := (@Eq.refl Real qz419)

noncomputable def Ns420p868 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz110 783557 1000 2455847288996 16000000 1567114 4000 2000 Ns420p866 Ns420p867 qz113 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns420p869 := nat_lit 17993032177703501311057534675040582030772726029581220016825280 

noncomputable abbrev qz423 := (@HMul.hMul Real Real Real qz619 qz625 (@HSub.hSub Real Real Real qz624 qz626 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 (@Nat.cast Real Real.instNatCast 1567114)))))

noncomputable abbrev qz680 := (Real.log (Enclosure.sfrac Bool.false 2455847288996 16000000))

noncomputable abbrev qz681 := (Enclosure.sfrac Bool.false 783557 2000)

noncomputable abbrev qz114 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 783557 4000) qz680) qz423) qz681)

noncomputable abbrev qz424 := (@HSub.hSub Real Real Real qz11 qz114 (@HMul.hMul Real Real Real qz5 qz681 (Real.log Real.pi)))

noncomputable def Ns420p870 := @Enclosure.Real.IsNear.addLit_ft_p qz424 (Enclosure.sfrac Bool.true Ns420p866 Ns420p867) 26995279680048393286019 18014398509481984000 505704382846317453 53248000000000000000000 Ns420p866 Ns420p867 0 1 Ns420p869 

noncomputable def Ns420p871 := nat_lit 1811622552690331138449962172416000 

noncomputable abbrev qz425 := (@HMul.hMul Real Real Real qz5 qz681 (Real.log Real.pi))

noncomputable def Ns420p872 := @Enclosure.Real.IsNear.subLit_ff_p qz114 qz425 35074387144318590316931 18014398509481984000 190278298172597 52000000000000000000 30097020656877 67108864000 783557 134217728000 Ns420p871 26995279680048393286019 18014398509481984000 

noncomputable def Ns420p873 := nat_lit 2805950971545487225354480 

noncomputable abbrev qz115 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 783557 4000) qz680) qz423)

noncomputable def Ns420p874 := @Enclosure.Real.IsNear.subLit_ff_p qz115 qz681 1685281646830627111419 720575940379279360 190278298172597 52000000000000000000 783557 2000 0 1 Ns420p873 35074387144318590316931 18014398509481984000 190278298172597 52000000000000000000 

noncomputable def Ns420p875 := nat_lit 3794916898340374050093427931492646912 

noncomputable def Ns420p876 := nat_lit 57745036487431201960755200 

noncomputable def Ns420p877 := nat_lit 935351385746707191786197163677857400013739916082014600647983906521565880750080 

noncomputable def Ns420p878 := nat_lit 1942366430444183400194737062068330939639290447200226688778741109063819554816 

noncomputable def Ns420p879 := nat_lit 31948119183986061973994962513654058766075769001193235406924651765821440 

noncomputable def Ns420p880 := BSN.log_dyadic_bound 358695288996 4552999288996 4 3 Ns420p877 134217728 54080000 Ns420p878 Ns420p879 21191851 4911694577992 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 358695288996) (BSN.artanhQ 4552999288996) 0 3 Ns420p878 Ns420p877 Ns420p879 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns420p881 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 783557 4000) qz680 783557 4000 0 1 53779256052739175 4503599627370496 3125002873 169000000000000000 1685564501396645989819 720575940379279360 2448617876159261 676000000000000000000 (Enclosure.Real.IsNear.const Bool.false 783557 4000) (BSN.isNear_log_sfrac 2455847288996 16000000 53779256052739175 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2455847288996) qz335)) Bool.false Ns420p876 Ns420p103 1000000919360000 54080000000000000000000 53779256052739175 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2455847288996 16000000 17 4911694577992 4194304000000 21191851 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns420p880 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns420p882 := BSN.arctan_dyadic_bound_f 1000 1567114 1 0 16777216 6760000 0 1 1 0 1 1 10705 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1567114) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1567114) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns420p883 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1567114))) 884279719003555 562949953421312 1 2000000000000000 10705 16777216 1 6760000 14829725470890571857920 883920518808995 562949953421312 50000000169 338000000000000000 qz16 (Ns420p882 rfl) rfl rfl 

noncomputable abbrev qz116 := qz423

noncomputable def Ns420p884 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 783557 4000) qz680) qz116 1685564501396645989819 720575940379279360 2448617876159261 676000000000000000000 883920518808995 2251799813685248 50000000169 1352000000000000000 Ns420p875 1685281646830627111419 720575940379279360 190278298172597 52000000000000000000 (Ns420p881 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1567114)))) 1 4 0 1 883920518808995 562949953421312 50000000169 338000000000000000 883920518808995 2251799813685248 50000000169 1352000000000000000 qz340 Ns420p883 rfl) 

noncomputable def Ns420p885 := @Ns420p870 Ns420p864 Ns420p865 505704382846317453 53248000000000000000000 (@Ns420p872 505704382846317453 53248000000000000000000 (Ns420p874 (Ns420p884 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 783557 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz681 (Real.log Real.pi) 783557 2000 0 1 38410761 33554432 1 67108864 30097020656877 67108864000 783557 134217728000 (Enclosure.Real.IsNear.const Bool.false 783557 2000) RS421to432.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns420p866 Ns420p867) 

noncomputable def Ns420p886 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz110) Bool.false Ns420p864 Ns420p865 505704382846317453 53248000000000000000000 25141309805 16777216 5 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz110) (@HAdd.hAdd Real Real Real qz341 qz424 (Enclosure.sfrac Bool.true Ns420p866 Ns420p867)) Bool.false Ns420p864 Ns420p865 505704382846317453 53248000000000000000000 Ns420p868 (Ns420p885 rfl rfl)) 

noncomputable def Ns420p887 := nat_lit 3795883645503792081797120 

noncomputable def Ns420p888 := nat_lit 3503176682243733121086374986881447551085403528928224159570795531417478083286184777848281571107814794903247571951848019454030576659900399616 

noncomputable def Ns420p889 := nat_lit 2486320099320519839523443821334890474363945339887195752165220544164033154547354144580353920759710641290749338672367026326047048073216 

noncomputable def Ns420p890 := nat_lit 17494165077456470275927630607630705444786637757575871847627672271656324412591225549099140619308573316652961003795850135328531650014322098176 

noncomputable def Ns420p891 := BSN.sin_dyadic_bound_f 107885502004 68719476736 4 3 33554432 13533204 Ns420p888 Ns420p522 Ns420p889 Ns420p890 Ns420p525 Ns420p889 33554419 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107885502004) qz659 0 3 Ns420p888 Ns420p522 Ns420p889 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107885502004) qz660 0 3 Ns420p890 Ns420p525 Ns420p889 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p892 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz110) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 25141309805) qz364) Bool.false 25141309805 16777216 5 524288 Bool.true 33554419 33554432 1 6760000 (Ns420p886 rfl) (Enclosure.sfrac_false_div 25141309805 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 25141309805) qz364) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns420p887) (@Nat.cast Real Real.instNatCast Ns420p242)) 226375608064910080 72057594037927936 Bool.false 33554419 33554432 238 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q1 25141309805 16777216 226375608064910080 72057594037927936 238 Ns420p887 Ns420p242 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554419 33554432 Ns420p887 Ns420p242 107885502004 68719476736 13533204 13520000 (Ns420p891 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns420p893 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz110) Bool.false Ns420p864 Ns420p865 505704382846317453 53248000000000000000000 402260956887 268435456 2551 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz110) (@HAdd.hAdd Real Real Real qz341 qz424 (Enclosure.sfrac Bool.true Ns420p866 Ns420p867)) Bool.false Ns420p864 Ns420p865 505704382846317453 53248000000000000000000 Ns420p868 (Ns420p885 rfl rfl)) 

noncomputable def Ns420p894 := Ns420p863 46164 BSN.abs_quadSignPos (BSN.cos_quad_nat0 608 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 249840842 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 405 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268316382 268435456) qz113 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz110) qz110 1) Bool.true 33554419 33554432 536317 55377920000 268435352 268435456 2600 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz110) qz110 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz110)) Bool.true 33554419 33554432 536317 55377920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz110) qz110) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz110)) Bool.true 33554419 33554432 34324288 3544186880000 33554419 33554432 536317 55377920000 (Ns420p892 rfl rfl) rfl)) rfl) (Ns420p893 rfl) RS421to432.d7 

noncomputable def Ns420p895 := nat_lit 889909157561653922322634427986465107793816553123791086026795961429601 

noncomputable def Ns420p896 := nat_lit 10407432465841164201515265421953224358272468699481497558418599521 

noncomputable def Ns420p897 := nat_lit 2669706657820030084639500253428551416932733114433974295085271047089761 

noncomputable def Ns420p898 := BSN.cos_dyadic_bound_f 100500437 268435456 3 2 268435456 134217728 Ns420p895 Ns420p156 Ns420p896 Ns420p897 Ns420p159 Ns420p896 249840842 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 100500437) qz346 0 2 Ns420p895 Ns420p156 Ns420p896 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 100500437) qz347 0 2 Ns420p897 Ns420p159 Ns420p896 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p899 := nat_lit 41040127428484613989417618902801921747808619367929408765838272827553345853917718887706606202505498796756287521 

noncomputable def Ns420p900 := nat_lit 25104039546429621112988514593514679950476672532289715000202712223131219218237091735272073754213931532321 

noncomputable def Ns420p901 := nat_lit 204964420715726425791553665067164900539648860189948795752452870230750679957816470340501388569983095587747381281 

noncomputable def Ns420p902 := BSN.sin_dyadic_bound_f 413661689 268435456 4 3 268435456 134217728 Ns420p899 Ns420p258 Ns420p900 Ns420p901 Ns420p261 Ns420p900 268316382 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 413661689) qz344 0 3 Ns420p899 Ns420p258 Ns420p900 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 413661689) qz345 0 3 Ns420p901 Ns420p261 Ns420p900 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p903 := nat_lit 14302694293669260863656768571513444224962074481718602930956731076837376 

noncomputable def Ns420p904 := nat_lit 2687416012467216051042410725592507699891653743403988781858130231296 

noncomputable def Ns420p905 := nat_lit 42902708048982848158868220893089147659486440137669000815306476970049536 

noncomputable def Ns420p906 := BSN.cos_dyadic_bound_f 201218016 268435456 3 2 268435456 134217728 Ns420p903 Ns420p156 Ns420p904 Ns420p905 Ns420p159 Ns420p904 196485228 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 201218016) qz346 0 2 Ns420p903 Ns420p156 Ns420p904 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 201218016) qz347 0 2 Ns420p905 Ns420p159 Ns420p904 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p907 := nat_lit 24569195773175773475504411850625 

noncomputable def Ns420p908 := BSN.sin_dyadic_bound_f 70404065 268435456 2 1 268435456 134217728 Ns420p907 Ns420p133 Ns420p907 Ns420p907 Ns420p134 Ns420p907 69599671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 70404065) qz344 0 1 Ns420p907 Ns420p133 Ns420p907 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 70404065) qz345 0 1 Ns420p907 Ns420p134 Ns420p907 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p909 := Ns420p861 78297 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 262 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 196485228 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 151 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 69599671 268435456) qz113 rfl rfl (Ns420p894 RS421to432.d9 RS421to432.d11 RS421to432.d13 RS421to432.d17 (Ns420p898 rfl rfl) (Ns420p902 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns420p893 rfl) RS421to432.d19 RS421to432.d21 RS421to432.d23 RS421to432.d25 RS421to432.d17 (Ns420p906 rfl rfl) (Ns420p908 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns420p910 := nat_lit 644807380241924781684140087319840215958066790338959687731557200311681 

noncomputable def Ns420p911 := nat_lit 5464054804100583990210803747413736046200832773389954493970134401 

noncomputable def Ns420p912 := nat_lit 1934411212616166143884439840352025820402107969351332283285683660666241 

noncomputable def Ns420p913 := BSN.cos_dyadic_bound_f 92723407 268435456 3 2 268435456 134217728 Ns420p910 Ns420p156 Ns420p911 Ns420p912 Ns420p159 Ns420p911 252579720 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 92723407) qz346 0 2 Ns420p910 Ns420p156 Ns420p911 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 92723407) qz347 0 2 Ns420p912 Ns420p159 Ns420p911 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p914 := nat_lit 3528365797160989787325663365498982449254364255097009434155608306411508277431788430887576618634798227310145361 

noncomputable def Ns420p915 := nat_lit 281324880791560360873426176540401774561644247034771679526659342990971694748570955437017635789805612881 

noncomputable def Ns420p916 := nat_lit 21394706491538594897445121629567994892326599071747405629550481931124015906617432609773425095208586450894745425 

noncomputable def Ns420p917 := BSN.cos_dyadic_bound_f 284512059 268435456 4 3 268435456 134217728 Ns420p914 Ns420p140 Ns420p915 Ns420p916 Ns420p143 Ns420p915 131256355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 284512059) qz346 0 3 Ns420p914 Ns420p140 Ns420p915 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 284512059) qz347 0 3 Ns420p916 Ns420p143 Ns420p915 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p918 := Ns420p859 105580 BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 252579720 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131256355 268435456) qz113 rfl rfl (Ns420p909 rfl rfl) (Ns420p893 rfl) RS421to432.d27 RS421to432.d29 RS421to432.d31 RS421to432.d33 RS421to432.d17 (Ns420p913 rfl rfl) (Ns420p917 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p919 := nat_lit 3227004491065626414308693207201417875991392017518118773507474866110720 

noncomputable def Ns420p920 := nat_lit 42238177238802396511403923205131978067489504619354822941135667456 

noncomputable def Ns420p921 := nat_lit 8451610043361111119309368507747095652012965062873308308520529477304576 

noncomputable def Ns420p922 := BSN.sin_dyadic_bound_f 119732802 268435456 3 2 268435456 134217728 Ns420p919 Ns420p119 Ns420p920 Ns420p921 Ns420p122 Ns420p920 115801945 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 119732802) qz344 0 2 Ns420p919 Ns420p119 Ns420p920 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 119732802) qz345 0 2 Ns420p921 Ns420p122 Ns420p920 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p923 := nat_lit 61891577381815937258263291521 

noncomputable def Ns420p924 := BSN.cos_dyadic_bound_f 15772767 268435456 2 1 268435456 134217728 Ns420p923 Ns420p285 Ns420p923 Ns420p923 Ns420p286 Ns420p923 267972200 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 15772767) qz346 0 1 Ns420p923 Ns420p285 Ns420p923 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 15772767) qz347 0 1 Ns420p923 Ns420p286 Ns420p923 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p925 := Ns420p857 129419 BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 115801945 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 142 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267972200 268435456) qz113 rfl rfl (Ns420p918 rfl) (Ns420p893 rfl) RS421to432.d35 RS421to432.d37 RS421to432.d39 RS421to432.d41 RS421to432.d17 (Ns420p922 rfl rfl) (Ns420p924 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p926 := nat_lit 34382154448828904525422117616156414234869531364824767109977876490878976 

noncomputable def Ns420p927 := nat_lit 15521595964495443405028317879586862514306043687141341005889610448896 

noncomputable def Ns420p928 := nat_lit 103115420154557722689456296212710068979579982007100018647921850251739136 

noncomputable def Ns420p929 := BSN.cos_dyadic_bound_f 250534216 268435456 3 2 268435456 134217728 Ns420p926 Ns420p156 Ns420p927 Ns420p928 Ns420p159 Ns420p927 159766124 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 250534216) qz346 0 2 Ns420p926 Ns420p156 Ns420p927 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 250534216) qz347 0 2 Ns420p928 Ns420p159 Ns420p927 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p930 := nat_lit 11317606618375835442060681455041 

noncomputable def Ns420p931 := BSN.cos_dyadic_bound_f 58001423 268435456 2 1 268435456 134217728 Ns420p930 Ns420p285 Ns420p930 Ns420p930 Ns420p286 Ns420p930 262193551 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 58001423) qz346 0 1 Ns420p930 Ns420p285 Ns420p930 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 58001423) qz347 0 1 Ns420p930 Ns420p286 Ns420p930 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p932 := Ns420p855 150860 BSN.abs_quadSignNeg qz651 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 159766124 268435456) BSN.abs_quadSignNeg qz348 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 262193551 268435456) qz113 rfl rfl (Ns420p925 rfl) (Ns420p893 rfl) RS421to432.d43 RS421to432.d45 RS421to432.d47 RS421to432.d49 RS421to432.d17 (Ns420p929 rfl rfl) (Ns420p931 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p933 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz110) qz110 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz110) qz110 11) 339033668 268435456 150860 268435456 339033668 268435456 150860 268435456 182017314537865216 84758417 33554432 37715 33554432 (Ns420p932 rfl) 

noncomputable def Ns420p934 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz422) (Zeta.RiemannSiegel.correction qz112) 5020503 16777216 1 16777216 84527397725859 140737488355328 319498575961351 11892317766025216000 424370053864868287077 2361183241434822606848 

noncomputable def Ns420p935 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz422 1 1 0 1 5020503 16777216 1 16777216 5020503 16777216 1 16777216 

noncomputable def Ns420p936 := @Enclosure.Real.IsNear.sqrt_image qz111 4184470975621 33554432000 783557 33554432000 187354957 187354993 16777216 (@Enclosure.Real.IsNear.of_eq qz111 (@HMul.hMul Real Real Real qz5 qz110 qz3) Bool.false 4184470975621 33554432000 783557 33554432000 (BSN.t_div_two_pi_mk qz110 783557 1000 qz113) (@Enclosure.Real.IsNear.mulLit_ff qz110 qz3 783557 1000 0 1 5340353 33554432 1 33554432 4184470975621 33554432000 783557 33554432000 (Enclosure.Real.IsNear.const Bool.false 783557 1000) RS421to432.d52 rfl)) 

noncomputable abbrev qz825 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 783557 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz682 := qz825

noncomputable abbrev qz426 := qz682

noncomputable abbrev qz117 := qz426

noncomputable def Ns420p937 := @Enclosure.Real.IsNear.sqrt_image qz117 187354975 16777216 9 8388608 56065092 56065098 16777216 (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 374709950 33554432 36 33554432 187354975 16777216 9 8388608 (Ns420p936 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns420p938 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz117) 56065095 16777216 3 16777216 5020502 5020504 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz117) Bool.false 112130190 33554432 6 33554432 56065095 16777216 3 16777216 (Ns420p937 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p939 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz117)) Bool.false 10041006 33554432 2 33554432 5020503 16777216 1 16777216 (Ns420p938 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz118 := (@HMul.hMul Real Real Real qz326 qz322 qz421)

noncomputable abbrev qz683 := (@HMul.hMul Real Real Real qz795 qz824 qz824)

noncomputable abbrev qz427 := (@HSub.hSub Real Real Real qz624 (@HSub.hSub Real Real Real qz624 qz683 qz679) qz634)

noncomputable abbrev qz119 := (Real.cos (@HMul.hMul Real Real Real qz326 qz322 qz427))

noncomputable def Ns420p940 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz112) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz118)) qz119) Bool.false 84527397725859 

noncomputable def Ns420p941 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz118)) qz119 33760413 16777216 59 

noncomputable def Ns420p942 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz118)) Bool.false 67520826 33554432 944 33554432 33760413 16777216 59 

noncomputable def Ns420p943 := @Enclosure.Real.IsNear.recentre' (Real.cos qz118) Bool.false 8337427 16777216 393708608 56706990080000 8337427 16777216 6151697 886046720000 

noncomputable def Ns420p944 := @Enclosure.Real.IsNear.cos_image qz118 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8814049) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 8814049 8388608 57 8388608 Bool.false 8337427 16777216 1 

noncomputable def Ns420p945 := nat_lit 242874678693446365047211007 

noncomputable def Ns420p946 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz112 884279719003555 140737488355328 1 500000000000000 2805599 16777216 9 8388608 2480934295356654904445 2361183241434822606848 Ns420p945 

noncomputable def Ns420p947 := @Enclosure.Real.IsNear.subLit_ff_p qz117 qz1 187354975 16777216 9 8388608 11 1 0 1 2805599 2805599 16777216 9 

noncomputable def Ns420p948 := @Ns420p947 8388608 (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 374709950 33554432 36 33554432 187354975 16777216 9 8388608 (Ns420p936 rfl rfl rfl rfl rfl rfl) rfl) qz352 

noncomputable def Ns420p949 := @Enclosure.Real.IsNear.recentre' qz118 Bool.false 2480934295356654904445 2361183241434822606848 Ns420p945 Ns420p302 8814049 8388608 57 8388608 (@Ns420p946 Ns420p302 RS421to432.d51 (Ns420p948 rfl rfl) rfl) 

noncomputable def Ns420p950 := nat_lit 50244171370628143135901742348132138340011161045996844506881 

noncomputable def Ns420p951 := nat_lit 36425345889382216663023621806249726573810948099947257601 

noncomputable def Ns420p952 := nat_lit 150659663420105664974379179800783915566885861241790639005441 

noncomputable def Ns420p953 := BSN.cos_dyadic_bound_f 8814049 8388608 3 2 16777216 6760000 Ns420p950 Ns420p326 Ns420p951 Ns420p952 Ns420p329 Ns420p951 8337427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 8814049) (BSN.cosEvenQ 8388608) 0 2 Ns420p950 Ns420p326 Ns420p951 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 8814049) (BSN.cosOddQ 8388608) 0 2 Ns420p952 Ns420p329 Ns420p951 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p954 := @Enclosure.Real.IsNear.inv_image (Real.cos qz118) 8337427 16777216 6151697 886046720000 33759941 33760885 16777216 (Ns420p943 (@Ns420p944 6760000 (Ns420p949 rfl) (Enclosure.sfrac_false_div 8814049 8388608) (Ns420p953 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns420p955 := @Enclosure.Real.IsNear.recentre' qz119 Bool.false 5007486 16777216 

noncomputable abbrev qz120 := (@HMul.hMul Real Real Real qz326 qz322 qz427)

noncomputable def Ns420p956 := @Enclosure.Real.IsNear.cos_image qz120 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 10634303)) (@Nat.cast Real Real.instNatCast 8388608)) Bool.true 10634303 8388608 

noncomputable def Ns420p957 := nat_lit 50219077108902502946569036445 

noncomputable def Ns420p958 := nat_lit 13593958071060521008093663330571 

noncomputable def Ns420p959 := @Enclosure.Real.IsNear.recentre' qz120 Bool.true Ns420p957 Ns420p469 Ns420p958 

noncomputable def Ns420p960 := nat_lit 1511157274518286468382720000000000000 

noncomputable abbrev qz121 := qz427

noncomputable def Ns420p961 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz121 884279719003555 140737488355328 1 500000000000000 56790940727999 

noncomputable abbrev qz428 := (@HSub.hSub Real Real Real qz624 qz683 qz679)

noncomputable abbrev qz122 := qz428

noncomputable def Ns420p962 := @Enclosure.Real.IsNear.subLit_tf qz122 qz27 39198754683583 281474976710656 12593493 8796093022208 1 16 

noncomputable abbrev qz429 := qz683

noncomputable abbrev qz123 := qz429

noncomputable def Ns420p963 := @Enclosure.Real.IsNear.subLit_ff_n qz123 qz112 7871385748801 281474976710656 3156309 8796093022208 2805599 16777216 9 8388608 

noncomputable def Ns420p964 := @Enclosure.Real.IsNear.mulLit_ff qz112 qz112 2805599 16777216 9 8388608 2805599 16777216 9 8388608 7871385748801 281474976710656 

noncomputable def Ns420p965 := nat_lit 106554585937672259247237955311363259603671175885474329239041 

noncomputable def Ns420p966 := nat_lit 163558170107503373109078263341192916368275722577547599361 

noncomputable def Ns420p967 := nat_lit 319336641472801770995495709407407392978276976211267892518401 

noncomputable def Ns420p968 := BSN.cos_dyadic_bound_f 10634303 8388608 3 2 16777216 6760000 Ns420p965 Ns420p326 Ns420p966 Ns420p967 Ns420p329 Ns420p966 5007486 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 10634303) (BSN.cosEvenQ 8388608) 0 2 Ns420p965 Ns420p326 Ns420p966 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 10634303) (BSN.cosOddQ 8388608) 0 2 Ns420p967 Ns420p329 Ns420p966 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p969 := @Ns420p955 2081834432 226827960320000 2503743 8388608 32528663 3544186880000 (@Ns420p956 303 33554432 Bool.false 5007486 16777216 1 6760000 (@Ns420p959 Ns420p960 10634303 8388608 303 33554432 (@Ns420p961 281474976710656 12593493 8796093022208 Ns420p957 Ns420p469 Ns420p958 Ns420p960 RS421to432.d51 (@Ns420p962 0 1 908655051647984 56790940727999 281474976710656 12593493 8796093022208 (@Ns420p963 657645974257483644928 39198754683583 281474976710656 12593493 8796093022208 (@Ns420p964 3156309 8796093022208 (Ns420p948 rfl rfl) (Ns420p948 rfl rfl) rfl) (Ns420p948 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 10634303 8388608) (BSN.cos_neg_of_bound 10634303 8388608 Bool.false 5007486 16777216 1 6760000 (Ns420p968 rfl rfl)) rfl rfl) 

noncomputable def Ns420p970 := @Ns420p934 402796610929025406601 Ns420p851 (Ns420p935 qz29 (@Enclosure.Real.IsNear.of_eq qz422 (@Inv.inv Real Real.instInv (Real.sqrt qz117)) Bool.false 5020503 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz111 (BSN.t_div_two_pi_nonneg qz110 783557 1000 qz113)) Ns420p939) rfl) (@Ns420p940 140737488355328 319498575961351 11892317766025216000 (BSN.correction_mk qz112 (BSN.cos_two_pi_p_ne_zero_mk qz110 783557 1000 11 qz113 rfl rfl (@BSN.floor_sqrt_eq_dec qz110 783557 1000 11 qz113 rfl rfl rfl))) (@Ns420p941 2097152 2503743 8388608 32528663 3544186880000 84527397725859 140737488355328 319498575961351 11892317766025216000 (@Ns420p942 2097152 (Ns420p954 rfl rfl rfl rfl rfl) rfl) (Ns420p969 rfl) rfl)) 

noncomputable def Ns420p971 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz110) (hardyZApproximantRS₀ qz110) Bool.true 5539973308911899110811 2361183241434822606848 56467642179134153086601 Ns420p851 (@Eq.refl Real (hardyZApproximantRS₀ qz110)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz110) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz110) qz110 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz422) (Zeta.RiemannSiegel.correction qz112))) Bool.true 5539973308911899110811 2361183241434822606848 56467642179134153086601 Ns420p851 (BSN.hardyZApproximantRS₀_eq qz110 11 (@BSN.floor_sqrt_eq_dec qz110 783557 1000 11 qz113 rfl rfl rfl)) (@Ns420p853 5539973308911899110811 2361183241434822606848 56467642179134153086601 Ns420p851 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz110) qz110 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz110) qz110 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz110) qz110 11)) Bool.true 84758417 33554432 37715 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz110) qz110 11) (Ns420p933 (Ns420p932 rfl) rfl rfl)) (Ns420p970 rfl) rfl rfl)) 

theorem RS421to432.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz110) Bool.true 5539973308911899110811 2361183241434822606848 56467642179134153086601 Ns420p851 := Ns420p971 

noncomputable def Ns420p972 := nat_lit 280506296243671328591418753024 

noncomputable abbrev qz826 := (Enclosure.sfrac Bool.false 784859 1000)

noncomputable abbrev qz684 := qz826

noncomputable abbrev qz430 := qz684

noncomputable abbrev qz124 := qz430

noncomputable abbrev qz827 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 784859 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz685 := qz827

noncomputable abbrev qz431 := qz685

noncomputable abbrev qz125 := qz431

noncomputable abbrev qz828 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 784859 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz686 := qz828

noncomputable abbrev qz432 := qz686

noncomputable abbrev qz126 := qz432

noncomputable abbrev qz433 := (@HPow.hPow Real Real Real qz623 qz125 qz8)

noncomputable def Ns420p973 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz124) qz124 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz433) (Zeta.RiemannSiegel.correction qz126)) 53503095 33554432 37775 33554432 829847862895751837097 4722366482869645213696 896767203866615660251 Ns420p726 Ns420p972 

noncomputable def Ns420p974 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz124) qz124 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 784859 1000 194 242 268435456 134217728 4503599627370496 Bool.false 403104446718 2554 

noncomputable def Ns420p975 := Ns420p974 618095470 41 84886744 8 643680110 41 80936328 8 Bool.false 353206192 129625 Bool.true 211804687 Bool.true 52583096 14148475504056880 1 Bool.false 189121161 Bool.true Bool.false 263301723 Bool.true Bool.false 214012380 

noncomputable def Ns420p976 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz124) qz124 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 784859 1000 83 141 268435456 134217728 4503599627370496 Bool.false 403104446718 2554 

noncomputable def Ns420p977 := Ns420p976 558195838 41 94906264 8 589812974 41 89478488 8 Bool.false 439409410 105748 Bool.true 3013952 Bool.true 361876857 14148475504056880 1 Bool.false 3013888 Bool.false Bool.false 261806355 Bool.true Bool.false 353206192 

noncomputable def Ns420p978 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz124) qz124 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 784859 1000 60 16 268435456 134217728 4503599627370496 Bool.false 403104446718 2554 

noncomputable def Ns420p979 := Ns420p978 480971758 41 109588312 8 522351262 41 101459064 8 Bool.false 303819551 78420 Bool.false 309988009 Bool.true 121123571 14148475504056880 1 Bool.false 108476314 Bool.false Bool.false 241569246 Bool.false Bool.false 439409410 

noncomputable def Ns420p980 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz124) qz124 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 784859 1000 263 151 268435456 134217728 4503599627370496 Bool.false 403104446718 2554 

noncomputable def Ns420p981 := Ns420p980 372130544 40 134217720 8 432030192 40 120047984 16 Bool.false 121627005 46235 Bool.false 138536450 Bool.false 351390586 14148475504056880 1 Bool.false 132468029 Bool.false Bool.false 259291171 Bool.false Bool.false 303819551 

noncomputable def Ns420p982 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz124) qz124 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 784859 1000 609 407 268435456 134217728 4503599627370496 Bool.false 403104446718 2554 

noncomputable def Ns420p983 := Ns420p982 186065264 40 189812528 16 294906480 40 154981288 8 Bool.false 268435448 2600 Bool.false 280075866 Bool.false 29868427 14148475504056880 1 Bool.false 231955673 Bool.true Bool.false 29806833 Bool.false Bool.false 121627005 

noncomputable def Ns420p984 := nat_lit 56910233913080937222716763001643618795513568768444663926429 

noncomputable def Ns420p985 := nat_lit 37897683133726228043667238438585023633648818791120896000 

noncomputable def Ns420p986 := nat_lit 142955180234295792791949338383520000 

noncomputable def Ns420p987 := nat_lit 673198086320181020235282404204202742080 

noncomputable abbrev qz434 := (@Eq.refl Real qz684)

noncomputable abbrev qz127 := qz434

noncomputable def Ns420p988 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz124 784859 1000 2464015599524 16000000 1569718 4000 2000 Ns420p986 Ns420p987 qz127 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns420p989 := nat_lit 18211274852185899911269364160525958014564342005902292456457280 

noncomputable abbrev qz435 := (@HMul.hMul Real Real Real qz619 qz625 (@HSub.hSub Real Real Real qz624 qz626 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 (@Nat.cast Real Real.instNatCast 1569718)))))

noncomputable abbrev qz687 := (Real.log (Enclosure.sfrac Bool.false 2464015599524 16000000))

noncomputable abbrev qz688 := (Enclosure.sfrac Bool.false 784859 2000)

noncomputable abbrev qz128 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 784859 4000) qz687) qz435) qz688)

noncomputable abbrev qz436 := (@HSub.hSub Real Real Real qz11 qz128 (@HMul.hMul Real Real Real qz5 qz688 (Real.log Real.pi)))

noncomputable def Ns420p990 := @Enclosure.Real.IsNear.addLit_ft_p qz436 (Enclosure.sfrac Bool.true Ns420p986 Ns420p987) 27051885318010225902941 18014398509481984000 6585038407688017143 692224000000000000000000 Ns420p986 Ns420p987 0 1 Ns420p989 

noncomputable def Ns420p991 := nat_lit 363084258549989000145948953804800 

noncomputable abbrev qz437 := (@HMul.hMul Real Real Real qz5 qz688 (Real.log Real.pi))

noncomputable def Ns420p992 := @Enclosure.Real.IsNear.subLit_ff_p qz128 qz437 7028883491417671247737 3602879701896396800 2477686629984407 676000000000000000000 30147031467699 67108864000 784859 134217728000 Ns420p991 27051885318010225902941 18014398509481984000 

noncomputable def Ns420p993 := nat_lit 70288834914176712477370000 

noncomputable abbrev qz129 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 784859 4000) qz687) qz435)

noncomputable def Ns420p994 := @Enclosure.Real.IsNear.subLit_ff_p qz129 qz688 42213798856965116478813 18014398509481984000 2477686629984407 676000000000000000000 784859 2000 0 1 Ns420p993 7028883491417671247737 3602879701896396800 2477686629984407 676000000000000000000 

noncomputable def Ns420p995 := nat_lit 95057024401060584273651963998842650624 

noncomputable def Ns420p996 := nat_lit 57761093657571425746157568 

noncomputable def Ns420p997 := nat_lit 945465057558895267787504825194887904316579303070936139272046928603491551252480 

noncomputable def Ns420p998 := nat_lit 2046782321743836248986350560597063045528287512364100098567074640634367799296 

noncomputable def Ns420p999 := nat_lit 36569497799333045374565428773354468460970721110870815016657894724464640 

noncomputable def Ns420p1000 := BSN.log_dyadic_bound 366863599524 4561167599524 4 3 Ns420p997 134217728 54080000 Ns420p998 Ns420p999 21637527 4928031199048 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 366863599524) (BSN.artanhQ 4561167599524) 0 3 Ns420p998 Ns420p997 Ns420p999 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns420p1001 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 784859 4000) qz687 784859 4000 0 1 53794210457775207 4503599627370496 3125002873 169000000000000000 42220870225678991190813 18014398509481984000 2452686629899907 676000000000000000000 (Enclosure.Real.IsNear.const Bool.false 784859 4000) (BSN.isNear_log_sfrac 2464015599524 16000000 53794210457775207 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2464015599524) qz335)) Bool.false Ns420p996 Ns420p103 1000000919360000 54080000000000000000000 53794210457775207 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2464015599524 16000000 17 4928031199048 4194304000000 21637527 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns420p1000 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns420p1002 := BSN.arctan_dyadic_bound_f 1000 1569718 1 0 16777216 6760000 0 1 1 0 1 1 10688 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1569718) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1569718) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns420p1003 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1569718))) 884279719003555 562949953421312 1 2000000000000000 10688 16777216 1 6760000 14829735041039780020224 883921089234339 562949953421312 50000000169 338000000000000000 qz16 (Ns420p1002 rfl) rfl rfl 

noncomputable abbrev qz130 := qz435

noncomputable def Ns420p1004 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 784859 4000) qz687) qz130 42220870225678991190813 18014398509481984000 2452686629899907 676000000000000000000 883921089234339 2251799813685248 50000000169 1352000000000000000 Ns420p995 42213798856965116478813 18014398509481984000 2477686629984407 676000000000000000000 (Ns420p1001 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1569718)))) 1 4 0 1 883921089234339 562949953421312 50000000169 338000000000000000 883921089234339 2251799813685248 50000000169 1352000000000000000 qz340 Ns420p1003 rfl) 

noncomputable def Ns420p1005 := @Ns420p990 Ns420p984 Ns420p985 6585038407688017143 692224000000000000000000 (@Ns420p992 6585038407688017143 692224000000000000000000 (Ns420p994 (Ns420p1004 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 784859 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz688 (Real.log Real.pi) 784859 2000 0 1 38410761 33554432 1 67108864 30147031467699 67108864000 784859 134217728000 (Enclosure.Real.IsNear.const Bool.false 784859 2000) RS421to432.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns420p986 Ns420p987) 

noncomputable def Ns420p1006 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz124) Bool.false Ns420p984 Ns420p985 6585038407688017143 692224000000000000000000 50388055839 33554432 5 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz124) (@HAdd.hAdd Real Real Real qz341 qz436 (Enclosure.sfrac Bool.true Ns420p986 Ns420p987)) Bool.false Ns420p984 Ns420p985 6585038407688017143 692224000000000000000000 Ns420p988 (Ns420p1005 rfl rfl)) 

noncomputable def Ns420p1007 := nat_lit 7594919368806239523831808 

noncomputable def Ns420p1008 := nat_lit 3509010037334071701621800957428517887861286564621826457943823696255819271327500049524194685416839313935843613211508560080643634040239055121 

noncomputable def Ns420p1009 := nat_lit 2498736173790568404224107729346354482609664354061042787505648894698117031146253794680429959610106549752279247528179285046966711247121 

noncomputable def Ns420p1010 := nat_lit 17523259592339553251530311120410508334220151287414751521905765973475594967004696466072949551519369480432616643443303240192684543772197675281 

noncomputable def Ns420p1011 := BSN.sin_dyadic_bound_f 107930295723 68719476736 4 3 33554432 13533204 Ns420p1008 Ns420p522 Ns420p1009 Ns420p1010 Ns420p525 Ns420p1009 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107930295723) qz659 0 3 Ns420p1008 Ns420p522 Ns420p1009 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107930295723) qz660 0 3 Ns420p1010 Ns420p525 Ns420p1009 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1012 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz124) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50388055839) qz342) Bool.false 50388055839 33554432 5 524288 Bool.false 33554431 33554432 1 6760000 (Ns420p1006 rfl) (Enclosure.sfrac_false_div 50388055839 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50388055839) qz342) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns420p1007) qz343) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 238 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q3 50388055839 33554432 226375608064910080 72057594037927936 238 Ns420p1007 Ns420p103 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns420p1007 Ns420p103 107930295723 68719476736 13533204 13520000 (Ns420p1011 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns420p1013 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz124) Bool.false Ns420p984 Ns420p985 6585038407688017143 692224000000000000000000 403104446718 268435456 2554 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz124) (@HAdd.hAdd Real Real Real qz341 qz436 (Enclosure.sfrac Bool.true Ns420p986 Ns420p987)) Bool.false Ns420p984 Ns420p985 6585038407688017143 692224000000000000000000 Ns420p988 (Ns420p1005 rfl rfl)) 

noncomputable def Ns420p1014 := Ns420p983 46235 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 609 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 231955673 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 407 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 29806833 268435456) qz127 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz124) qz124 1) Bool.false 33554431 33554432 536317 55377920000 268435448 268435456 2600 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz124) qz124 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz124)) Bool.false 33554431 33554432 536317 55377920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz124) qz124) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz124)) Bool.false 33554431 33554432 34324288 3544186880000 33554431 33554432 536317 55377920000 (Ns420p1012 rfl rfl) rfl)) rfl) (Ns420p1013 rfl) RS421to432.d7 

noncomputable def Ns420p1015 := nat_lit 96652749370983545716624689993052375239406663698750939973328434416656640 

noncomputable def Ns420p1016 := nat_lit 37862169897431228991854013393938767523579245779300919063272285348096 

noncomputable def Ns420p1017 := nat_lit 253076852458456302506125472055356510479598324241657403204043458819727616 

noncomputable def Ns420p1018 := BSN.sin_dyadic_bound_f 280075866 268435456 3 2 268435456 134217728 Ns420p1015 Ns420p119 Ns420p1016 Ns420p1017 Ns420p122 Ns420p1016 231955673 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 280075866) qz344 0 2 Ns420p1015 Ns420p119 Ns420p1016 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 280075866) qz345 0 2 Ns420p1017 Ns420p122 Ns420p1016 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1019 := nat_lit 795883324826665399443012840241 

noncomputable def Ns420p1020 := BSN.sin_dyadic_bound_f 29868427 268435456 2 1 268435456 134217728 Ns420p1019 Ns420p133 Ns420p1019 Ns420p1019 Ns420p134 Ns420p1019 29806833 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 29868427) qz344 0 1 Ns420p1019 Ns420p133 Ns420p1019 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 29868427) qz345 0 1 Ns420p1019 Ns420p134 Ns420p1019 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1021 := nat_lit 5783725966549182691197840610423654318144388070061860304556188900000000 

noncomputable def Ns420p1022 := nat_lit 135678938474714450232812371982070788980364757082162539062500000000 

noncomputable def Ns420p1023 := nat_lit 15147634051252233701170157997745409385291238640555310629726774500000000 

noncomputable def Ns420p1024 := BSN.sin_dyadic_bound_f 138536450 268435456 3 2 268435456 134217728 Ns420p1021 Ns420p119 Ns420p1022 Ns420p1023 Ns420p122 Ns420p1022 132468029 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 138536450) qz344 0 2 Ns420p1021 Ns420p119 Ns420p1022 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 138536450) qz345 0 2 Ns420p1023 Ns420p122 Ns420p1022 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1025 := nat_lit 21350111896065811870829879427281246454556534721001188788987316837132047963786311589539702894387643315976605696 

noncomputable def Ns420p1026 := nat_lit 3543900069009454871420175799169885966651897009214822392964729500429828382528034435096542256559933034496 

noncomputable def Ns420p1027 := nat_lit 106686529971894435409870972189202013330097688257836493990000312754975037738195431604487226513525858890490515456 

noncomputable def Ns420p1028 := BSN.sin_dyadic_bound_f 351390586 268435456 4 3 268435456 134217728 Ns420p1025 Ns420p258 Ns420p1026 Ns420p1027 Ns420p261 Ns420p1026 259291171 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 351390586) qz344 0 3 Ns420p1025 Ns420p258 Ns420p1026 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 351390586) qz345 0 3 Ns420p1027 Ns420p261 Ns420p1026 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1029 := Ns420p981 78420 BSN.abs_quadSignPos (BSN.cos_quad_nat3 263 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 132468029 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 151 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 259291171 268435456) qz127 rfl rfl (Ns420p1014 RS421to432.d9 RS421to432.d11 RS421to432.d13 RS421to432.d17 (Ns420p1018 rfl rfl) (Ns420p1020 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns420p1013 rfl) RS421to432.d19 RS421to432.d21 RS421to432.d23 RS421to432.d25 RS421to432.d17 (Ns420p1024 rfl rfl) (Ns420p1028 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns420p1030 := nat_lit 4973749143532606463434402398035253597347348614796056003971210089891198820346421521152400345146815285286564961 

noncomputable def Ns420p1031 := nat_lit 787297253903434200431932973616809946727764551745707938979237355496453491836741492798540976822429840481 

noncomputable def Ns420p1032 := nat_lit 30152802850698848242019405927907934246344291926039869249593006719481047741300301464659250057083048045685142625 

noncomputable def Ns420p1033 := BSN.cos_dyadic_bound_f 309988009 268435456 4 3 268435456 134217728 Ns420p1030 Ns420p140 Ns420p1031 Ns420p1032 Ns420p143 Ns420p1031 108476314 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 309988009) qz346 0 3 Ns420p1030 Ns420p140 Ns420p1031 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 309988009) qz347 0 3 Ns420p1032 Ns420p143 Ns420p1031 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1034 := nat_lit 1877561525601393177682989681273103239878911342950564522930023869585441 

noncomputable def Ns420p1035 := nat_lit 46326482989440903949982797526963468366482295841700954188532553761 

noncomputable def Ns420p1036 := nat_lit 5632591923838200651241069078224255792700001064260010166881694543648801 

noncomputable def Ns420p1037 := BSN.cos_dyadic_bound_f 121123571 268435456 3 2 268435456 134217728 Ns420p1034 Ns420p156 Ns420p1035 Ns420p1036 Ns420p159 Ns420p1035 241569246 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 121123571) qz346 0 2 Ns420p1034 Ns420p156 Ns420p1035 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 121123571) qz347 0 2 Ns420p1036 Ns420p159 Ns420p1035 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1038 := Ns420p979 105748 BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 108476314 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 241569246 268435456) qz127 rfl rfl (Ns420p1029 rfl rfl) (Ns420p1013 rfl) RS421to432.d27 RS421to432.d29 RS421to432.d31 RS421to432.d33 RS421to432.d17 (Ns420p1033 rfl rfl) (Ns420p1037 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p1039 := BSN.sin_dyadic_bound_f 3013952 268435456 1 0 268435456 134217728 0 1 1 0 1 1 3013888 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 3013952) qz344 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 3013952) qz345 0 0 rfl) rfl rfl 

noncomputable def Ns420p1040 := nat_lit 24017926219076426067659918910167013649588760013920868078373935707622431829039027134583165786245060698203437601 

noncomputable def Ns420p1041 := nat_lit 5043473187360661581966059052391972866718004684488834484541981407433168950443576215231126411243264096801 

noncomputable def Ns420p1042 := nat_lit 120008617544458754445860278378283018912407717979075342122552568806916797110244916357946890978922517466195900961 

noncomputable def Ns420p1043 := BSN.sin_dyadic_bound_f 361876857 268435456 4 3 268435456 134217728 Ns420p1040 Ns420p258 Ns420p1041 Ns420p1042 Ns420p261 Ns420p1041 261806355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 361876857) qz344 0 3 Ns420p1040 Ns420p258 Ns420p1041 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 361876857) qz345 0 3 Ns420p1042 Ns420p261 Ns420p1041 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1044 := Ns420p977 129625 BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 3013888 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 141 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 261806355 268435456) qz127 rfl rfl (Ns420p1038 rfl) (Ns420p1013 rfl) RS421to432.d35 RS421to432.d37 RS421to432.d39 RS421to432.d41 RS421to432.d17 (Ns420p1039 rfl rfl) (Ns420p1043 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p1045 := nat_lit 17559463698855794099498643993690177274381396974013241006017266113481601 

noncomputable def Ns420p1046 := nat_lit 4050275179741527569793837041679650273620305550677295337175225371521 

noncomputable def Ns420p1047 := nat_lit 52670290546207899243356344306987172522596950310938368427377447889701761 

noncomputable def Ns420p1048 := BSN.cos_dyadic_bound_f 211804687 268435456 3 2 268435456 134217728 Ns420p1045 Ns420p156 Ns420p1046 Ns420p1047 Ns420p159 Ns420p1046 189121161 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 211804687) qz346 0 2 Ns420p1045 Ns420p156 Ns420p1046 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 211804687) qz347 0 2 Ns420p1047 Ns420p159 Ns420p1046 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1049 := nat_lit 7645125377071586678870521286656 

noncomputable def Ns420p1050 := BSN.cos_dyadic_bound_f 52583096 268435456 2 1 268435456 134217728 Ns420p1049 Ns420p285 Ns420p1049 Ns420p1049 Ns420p286 Ns420p1049 263301723 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 52583096) qz346 0 1 Ns420p1049 Ns420p285 Ns420p1049 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 52583096) qz347 0 1 Ns420p1049 Ns420p286 Ns420p1049 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1051 := Ns420p975 151100 BSN.abs_quadSignNeg qz651 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 189121161 268435456) BSN.abs_quadSignNeg qz348 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 263301723 268435456) qz127 rfl rfl (Ns420p1044 rfl) (Ns420p1013 rfl) RS421to432.d43 RS421to432.d45 RS421to432.d47 RS421to432.d49 RS421to432.d17 (Ns420p1048 rfl rfl) (Ns420p1050 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p1052 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz124) qz124 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz124) qz124 11) 214012380 268435456 151100 268435456 214012380 268435456 151100 268435456 114897021629890560 53503095 33554432 37775 33554432 (Ns420p1051 rfl) 

noncomputable def Ns420p1053 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz433) (Zeta.RiemannSiegel.correction qz126) 10036839 33554432 1 33554432 82680200698223 140737488355328 222933857824491 7432698603765760000 829847862895751837097 4722366482869645213696 

noncomputable def Ns420p1054 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz433 1 1 0 1 10036839 33554432 1 33554432 10036839 33554432 1 33554432 

noncomputable def Ns420p1055 := @Enclosure.Real.IsNear.sqrt_image qz125 4191424115227 33554432000 784859 33554432000 187510552 187510588 16777216 (@Enclosure.Real.IsNear.of_eq qz125 (@HMul.hMul Real Real Real qz5 qz124 qz3) Bool.false 4191424115227 33554432000 784859 33554432000 (BSN.t_div_two_pi_mk qz124 784859 1000 qz127) (@Enclosure.Real.IsNear.mulLit_ff qz124 qz3 784859 1000 0 1 5340353 33554432 1 33554432 4191424115227 33554432000 784859 33554432000 (Enclosure.Real.IsNear.const Bool.false 784859 1000) RS421to432.d52 rfl)) 

noncomputable abbrev qz829 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 784859 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz689 := qz829

noncomputable abbrev qz438 := qz689

noncomputable abbrev qz131 := qz438

noncomputable def Ns420p1056 := @Enclosure.Real.IsNear.sqrt_image qz131 93755285 8388608 9 8388608 56088368 56088374 16777216 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 375021140 33554432 36 33554432 93755285 8388608 9 8388608 (Ns420p1055 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns420p1057 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz131) 56088371 16777216 3 16777216 5018419 5018420 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz131) Bool.false 112176742 33554432 6 33554432 56088371 16777216 3 16777216 (Ns420p1056 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p1058 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz131)) Bool.false 10036839 33554432 1 33554432 10036839 33554432 1 33554432 (Ns420p1057 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz132 := (@HMul.hMul Real Real Real qz326 qz322 qz432)

noncomputable abbrev qz690 := (@HMul.hMul Real Real Real qz795 qz828 qz828)

noncomputable abbrev qz439 := (@HSub.hSub Real Real Real qz624 (@HSub.hSub Real Real Real qz624 qz690 qz686) qz634)

noncomputable abbrev qz133 := (Real.cos (@HMul.hMul Real Real Real qz326 qz322 qz439))

noncomputable def Ns420p1059 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz126) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz132)) qz133) Bool.false 82680200698223 

noncomputable def Ns420p1060 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz132)) qz133 37653571 16777216 585 

noncomputable def Ns420p1061 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz132)) Bool.false 75307142 33554432 1170 33554432 37653571 16777216 585 

noncomputable def Ns420p1062 := @Enclosure.Real.IsNear.recentre' (Real.cos qz132) Bool.false 7475386 16777216 1568074432 226827960320000 3737693 8388608 24501163 3544186880000 

noncomputable def Ns420p1063 := @Enclosure.Real.IsNear.cos_image qz132 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 37211461) qz342) Bool.false 37211461 33554432 227 33554432 Bool.false 7475386 16777216 1 

noncomputable def Ns420p1064 := nat_lit 242874678694114640483632127 

noncomputable def Ns420p1065 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz126 884279719003555 140737488355328 1 500000000000000 1480597 8388608 9 8388608 1309261899117506522335 1180591620717411303424 Ns420p1064 

noncomputable def Ns420p1066 := @Enclosure.Real.IsNear.subLit_ff_p qz131 qz1 93755285 8388608 9 8388608 11 1 0 1 1480597 1480597 8388608 9 

noncomputable def Ns420p1067 := @Ns420p1066 8388608 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 375021140 33554432 36 33554432 93755285 8388608 9 8388608 (Ns420p1055 rfl rfl rfl rfl rfl rfl) rfl) qz352 

noncomputable def Ns420p1068 := @Enclosure.Real.IsNear.recentre' qz132 Bool.false 1309261899117506522335 1180591620717411303424 Ns420p1064 Ns420p302 37211461 33554432 227 33554432 (@Ns420p1065 Ns420p302 RS421to432.d51 (Ns420p1067 rfl rfl) rfl) 

noncomputable def Ns420p1069 := nat_lit 4087018126971627015489588316604658939236532691694939752973883361 

noncomputable def Ns420p1070 := nat_lit 3676323948504085576363398118004097723481461001716247507392481 

noncomputable def Ns420p1071 := nat_lit 12253701733017872875316038153577968622262635153081386763906865121 

noncomputable def Ns420p1072 := BSN.cos_dyadic_bound_f 37211461 33554432 3 2 16777216 6760000 Ns420p1069 Ns420p181 Ns420p1070 Ns420p1071 Ns420p184 Ns420p1070 7475386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 37211461) qz635 0 2 Ns420p1069 Ns420p181 Ns420p1070 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 37211461) (BSN.cosOddQ 33554432) 0 2 Ns420p1071 Ns420p184 Ns420p1070 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1073 := @Enclosure.Real.IsNear.inv_image (Real.cos qz132) 3737693 8388608 24501163 3544186880000 37652986 37654156 16777216 (Ns420p1062 (@Ns420p1063 6760000 (Ns420p1068 rfl) (Enclosure.sfrac_false_div 37211461 33554432) (Ns420p1072 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns420p1074 := @Enclosure.Real.IsNear.recentre' qz133 Bool.false 4391626 16777216 

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz326 qz322 qz439)

noncomputable def Ns420p1075 := @Enclosure.Real.IsNear.cos_image qz134 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 21910199)) qz364) Bool.true 21910199 16777216 

noncomputable def Ns420p1076 := nat_lit 12933498933988235903984900405 

noncomputable def Ns420p1077 := nat_lit 551316339969043014701971774712873 

noncomputable def Ns420p1078 := @Enclosure.Real.IsNear.recentre' qz134 Bool.true Ns420p1076 Ns420p317 Ns420p1077 

noncomputable def Ns420p1079 := nat_lit 60446290980731458735308800000000000000 

noncomputable abbrev qz135 := qz439

noncomputable def Ns420p1080 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz135 884279719003555 140737488355328 1 500000000000000 14626026873671 

noncomputable abbrev qz440 := (@HSub.hSub Real Real Real qz624 qz690 qz686)

noncomputable abbrev qz136 := qz440

noncomputable def Ns420p1081 := @Enclosure.Real.IsNear.subLit_tf qz136 qz27 10227980362567 70368744177664 102148299 70368744177664 1 16 

noncomputable abbrev qz441 := qz690

noncomputable abbrev qz137 := qz441

noncomputable def Ns420p1082 := @Enclosure.Real.IsNear.subLit_ff_n qz137 qz126 2192167476409 70368744177664 26650827 70368744177664 1480597 8388608 9 8388608 

noncomputable def Ns420p1083 := @Enclosure.Real.IsNear.mulLit_ff qz126 qz126 1480597 8388608 9 8388608 1480597 8388608 9 8388608 2192167476409 70368744177664 

noncomputable def Ns420p1084 := nat_lit 28921555525817892303507983190815240279537156127313013424961323537202844170889255799336880627681 

noncomputable def Ns420p1085 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns420p1086 := nat_lit 12239279845618872562366493052976401831113895451692607965964439743307279756793879003717601 

noncomputable def Ns420p1087 := nat_lit 175255200764442293194243857355942400445048296503476595842502661050504482595404049837879288979425 

noncomputable def Ns420p1088 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns420p1089 := BSN.cos_dyadic_bound_f 21910199 16777216 4 3 16777216 6760000 Ns420p1084 Ns420p1085 Ns420p1086 Ns420p1087 Ns420p1088 Ns420p1086 4391626 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 21910199) (BSN.cosEvenQ 16777216) 0 3 Ns420p1084 Ns420p1085 Ns420p1086 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 21910199) (BSN.cosOddQ 16777216) 0 3 Ns420p1087 Ns420p1088 Ns420p1086 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1090 := @Ns420p1074 2108874432 226827960320000 2195813 8388608 32951163 3544186880000 (@Ns420p1075 307 33554432 Bool.false 4391626 16777216 1 6760000 (@Ns420p1078 Ns420p1079 21910199 16777216 307 33554432 (@Ns420p1080 70368744177664 102148299 70368744177664 Ns420p1076 Ns420p317 Ns420p1077 Ns420p1079 RS421to432.d51 (@Ns420p1081 0 1 234016429978736 14626026873671 70368744177664 102148299 70368744177664 (@Ns420p1082 85798517893272436736 10227980362567 70368744177664 102148299 70368744177664 (@Ns420p1083 26650827 70368744177664 (Ns420p1067 rfl rfl) (Ns420p1067 rfl rfl) rfl) (Ns420p1067 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 21910199 16777216) (BSN.cos_neg_of_bound 21910199 16777216 Bool.false 4391626 16777216 1 6760000 (Ns420p1089 rfl rfl)) rfl rfl) 

noncomputable def Ns420p1091 := @Ns420p1053 896767203866615660251 Ns420p726 (Ns420p1054 qz29 (@Enclosure.Real.IsNear.of_eq qz433 (@Inv.inv Real Real.instInv (Real.sqrt qz131)) Bool.false 10036839 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz125 (BSN.t_div_two_pi_nonneg qz124 784859 1000 qz127)) Ns420p1058) rfl) (@Ns420p1059 140737488355328 222933857824491 7432698603765760000 (BSN.correction_mk qz126 (BSN.cos_two_pi_p_ne_zero_mk qz124 784859 1000 11 qz127 rfl rfl (@BSN.floor_sqrt_eq_dec qz124 784859 1000 11 qz127 rfl rfl rfl))) (@Ns420p1060 16777216 2195813 8388608 32951163 3544186880000 82680200698223 140737488355328 222933857824491 7432698603765760000 (@Ns420p1061 16777216 (Ns420p1073 rfl rfl rfl rfl rfl) rfl) (Ns420p1090 rfl) rfl)) 

noncomputable def Ns420p1092 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz124) (hardyZApproximantRS₀ qz124) Bool.false 8359739072432259577257 4722366482869645213696 113204843106767249260251 Ns420p726 (@Eq.refl Real (hardyZApproximantRS₀ qz124)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz124) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz124) qz124 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz433) (Zeta.RiemannSiegel.correction qz126))) Bool.false 8359739072432259577257 4722366482869645213696 113204843106767249260251 Ns420p726 (BSN.hardyZApproximantRS₀_eq qz124 11 (@BSN.floor_sqrt_eq_dec qz124 784859 1000 11 qz127 rfl rfl rfl)) (@Ns420p973 8359739072432259577257 4722366482869645213696 113204843106767249260251 Ns420p726 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz124) qz124 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz124) qz124 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz124) qz124 11)) Bool.false 53503095 33554432 37775 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz124) qz124 11) (Ns420p1052 (Ns420p1051 rfl) rfl rfl)) (Ns420p1091 rfl) rfl rfl)) 

theorem RS421to432.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz124) Bool.false 8359739072432259577257 4722366482869645213696 113204843106767249260251 Ns420p726 := Ns420p1092 

noncomputable def Ns420p1093 := nat_lit 72815317910217507768937480192 

noncomputable abbrev qz830 := (Enclosure.sfrac Bool.false 786160 1000)

noncomputable abbrev qz691 := qz830

noncomputable abbrev qz442 := qz691

noncomputable abbrev qz138 := qz442

noncomputable abbrev qz443 := qz623

noncomputable abbrev qz831 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 786160 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz692 := qz831

noncomputable abbrev qz444 := qz692

noncomputable abbrev qz139 := (@HMul.hMul Real Real Real qz326 qz620 (@HPow.hPow Real Real Real qz443 qz444 qz328))

noncomputable abbrev qz832 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 786160 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz693 := qz832

noncomputable abbrev qz445 := qz693

noncomputable abbrev qz140 := (Zeta.RiemannSiegel.correction qz445)

noncomputable def Ns420p1094 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (@HMul.hMul Real Real Real qz5 qz139 qz140) 84746413 134217728 37837 33554432 202920937265750667765 1180591620717411303424 1050025017568186145521 Ns420p726 Ns420p1093 

noncomputable def Ns420p1095 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 786160 1000 194 242 268435456 134217728 4503599627370496 Bool.false 403947578329 2559 

noncomputable def Ns420p1096 := Ns420p1095 618095470 41 84886744 8 643680110 41 80936328 8 Bool.false 62853645 129837 Bool.true 172815282 Bool.true 46879308 14148475504056880 1 Bool.false 214702294 Bool.true Bool.false 264352370 Bool.true Bool.true 84746413 

noncomputable def Ns420p1097 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 786160 1000 82 141 268435456 134217728 4503599627370496 Bool.false 403947578329 2559 

noncomputable def Ns420p1098 := Ns420p1097 558195838 41 94906264 8 589812974 41 89478488 8 Bool.false 180235806 105920 Bool.true 307752555 Bool.true 286091925 14148475504056880 1 Bool.false 110517327 Bool.true Bool.false 234925150 Bool.true Bool.false 62853645 

noncomputable def Ns420p1099 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 786160 1000 61 15 268435456 134217728 4503599627370496 Bool.false 403947578329 2559 

noncomputable def Ns420p1100 := Ns420p1099 480971758 41 109588312 8 522351262 41 101459064 8 Bool.false 122093594 78547 Bool.false 105717935 Bool.true 379228380 14148475504056880 1 Bool.false 103006205 Bool.true Bool.false 265089252 Bool.false Bool.false 180235806 

noncomputable def Ns420p1101 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 786160 1000 264 152 268435456 134217728 4503599627370496 Bool.false 403947578329 2559 

noncomputable def Ns420p1102 := Ns420p1101 372130544 40 134217720 8 432030192 40 120047984 16 Bool.true 91696836 46308 Bool.false 75868795 Bool.false 210793489 14148475504056880 1 Bool.false 257785113 Bool.false Bool.false 189837437 Bool.false Bool.false 122093594 

noncomputable def Ns420p1103 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 786160 1000 611 408 268435456 134217728 4503599627370496 Bool.false 403947578329 2559 

noncomputable def Ns420p1104 := Ns420p1103 186065264 40 189812528 16 294906480 40 154981288 8 Bool.true 268435344 2600 Bool.false 37821712 Bool.false 67669279 14148475504056880 1 Bool.false 37696697 Bool.false Bool.false 259951232 Bool.false Bool.true 91696836 

noncomputable def Ns420p1105 := nat_lit 11249769648596539161119053204376575931534312454257 

noncomputable def Ns420p1106 := nat_lit 7475814208373005611780788712195205901372620800 

noncomputable def Ns420p1107 := nat_lit 144143942931208210782619648000000000 

noncomputable def Ns420p1108 := nat_lit 679921341395402633841585039790080000000 

noncomputable abbrev qz446 := (@Eq.refl Real qz691)

noncomputable abbrev qz141 := qz446

noncomputable def Ns420p1109 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz138 786160 1000 2472191182400 16000000 1572320 4000 2000 Ns420p1107 Ns420p1108 qz141 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns420p1110 := nat_lit 230395282403257122019718209625632275077822719063183360000000 

noncomputable abbrev qz447 := (@HMul.hMul Real Real Real qz619 qz625 (@HSub.hSub Real Real Real qz624 qz626 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 (@Nat.cast Real Real.instNatCast 1572320)))))

noncomputable abbrev qz694 := (Real.log (Enclosure.sfrac Bool.false 2472191182400 16000000))

noncomputable abbrev qz695 := (Enclosure.sfrac Bool.false 786160 2000)

noncomputable abbrev qz142 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 786160 4000) qz694) qz447) qz695)

noncomputable abbrev qz448 := (@HSub.hSub Real Real Real qz11 qz142 (@HMul.hMul Real Real Real qz5 qz695 (Real.log Real.pi)))

noncomputable def Ns420p1111 := @Enclosure.Real.IsNear.addLit_ft_p qz448 (Enclosure.sfrac Bool.true Ns420p1107 Ns420p1108) 338855836454180389417 225179981368524800 82448893511253279 8652800000000000000000 Ns420p1107 Ns420p1108 0 1 Ns420p1110 

noncomputable def Ns420p1112 := nat_lit 284252878052622924810656153600 

noncomputable abbrev qz449 := (@HMul.hMul Real Real Real qz5 qz695 (Real.log Real.pi))

noncomputable def Ns420p1113 := @Enclosure.Real.IsNear.subLit_ff_p qz142 qz449 440180167742629380649 225179981368524800 124087612936109 33800000000000000000 377462548347 838860800 9827 1677721600 Ns420p1112 338855836454180389417 225179981368524800 

noncomputable abbrev qz143 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 786160 4000) qz694) qz447)

noncomputable def Ns420p1114 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz695 528693914818969109033 225179981368524800 124087612936109 33800000000000000000 786160 2000 0 1 880360335485258761298000 440180167742629380649 225179981368524800 124087612936109 33800000000000000000 

noncomputable def Ns420p1115 := nat_lit 1190512858885879016315154954855645184 

noncomputable def Ns420p1116 := nat_lit 57777111916610869050474496 

noncomputable def Ns420p1117 := nat_lit 955678821714675687781604824677156057828863934293853387948011028480000000000000 

noncomputable def Ns420p1118 := nat_lit 2154749234357805117568161938902521775120848554499733319892074496000000000000 

noncomputable def Ns420p1119 := nat_lit 41739872526860454873089514185617667665702098510434418032640000000000000 

noncomputable def Ns420p1120 := BSN.log_dyadic_bound 375039182400 4569343182400 4 3 Ns420p1117 134217728 54080000 Ns420p1118 Ns420p1119 22082123 4944382364800 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 375039182400) (BSN.artanhQ 4569343182400) 0 3 Ns420p1118 Ns420p1117 Ns420p1119 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns420p1121 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 786160 4000) qz694 786160 4000 0 1 53809128624024679 4503599627370496 3125002873 169000000000000000 528782306988290520533 225179981368524800 30709403232971 8450000000000000000 (Enclosure.Real.IsNear.const Bool.false 786160 4000) (BSN.isNear_log_sfrac 2472191182400 16000000 53809128624024679 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2472191182400) qz335)) Bool.false Ns420p1116 Ns420p103 1000000919360000 54080000000000000000000 53809128624024679 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2472191182400 16000000 17 4944382364800 4194304000000 22082123 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns420p1120 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns420p1122 := BSN.arctan_dyadic_bound_f 1000 1572320 1 0 16777216 6760000 0 1 1 0 1 1 10670 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1572320) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1572320) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns420p1123 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1572320))) 884279719003555 562949953421312 1 2000000000000000 10670 16777216 1 6760000 14829745174138941603840 883921693214115 562949953421312 50000000169 338000000000000000 qz16 (Ns420p1122 rfl) rfl rfl 

noncomputable abbrev qz144 := qz447

noncomputable def Ns420p1124 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 786160 4000) qz694) qz144 528782306988290520533 225179981368524800 30709403232971 8450000000000000000 883921693214115 2251799813685248 50000000169 1352000000000000000 Ns420p1115 528693914818969109033 225179981368524800 124087612936109 33800000000000000000 (Ns420p1121 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1572320)))) 1 4 0 1 883921693214115 562949953421312 50000000169 338000000000000000 883921693214115 2251799813685248 50000000169 1352000000000000000 qz340 Ns420p1123 rfl) 

noncomputable def Ns420p1125 := @Ns420p1111 Ns420p1105 Ns420p1106 82448893511253279 8652800000000000000000 (@Ns420p1113 82448893511253279 8652800000000000000000 (Ns420p1114 (Ns420p1124 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 786160 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz695 (Real.log Real.pi) 786160 2000 0 1 38410761 33554432 1 67108864 377462548347 838860800 9827 1677721600 (Enclosure.Real.IsNear.const Bool.false 786160 2000) RS421to432.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns420p1107 Ns420p1108) 

noncomputable def Ns420p1126 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz138) Bool.false Ns420p1105 Ns420p1106 82448893511253279 8652800000000000000000 50493447291 33554432 5 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz138) (@HAdd.hAdd Real Real Real qz341 qz448 (Enclosure.sfrac Bool.true Ns420p1107 Ns420p1108)) Bool.false Ns420p1105 Ns420p1106 82448893511253279 8652800000000000000000 Ns420p1109 (Ns420p1125 rfl rfl)) 

noncomputable def Ns420p1127 := nat_lit 7591618400828422285688832 

noncomputable def Ns420p1128 := nat_lit 3502901320978803367518929115155626084866583597002610589568001193540106960599561412170354091368968642169980349813174244814979172707166384241 

noncomputable def Ns420p1129 := nat_lit 2485735020108919258714781082763218217133805654563308112695841726472234372116141208513272486892517826454295240427334473576103739977841 

noncomputable def Ns420p1130 := nat_lit 17492791679208192594832406718964758429201920116811508759052285330255694387889624157782338333571435691542906224152805325223348330266254962801 

noncomputable def Ns420p1131 := BSN.sin_dyadic_bound_f 107883386147 68719476736 4 3 33554432 13533204 Ns420p1128 Ns420p522 Ns420p1129 Ns420p1130 Ns420p525 Ns420p1129 33554418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107883386147) qz659 0 3 Ns420p1128 Ns420p522 Ns420p1129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107883386147) qz660 0 3 Ns420p1130 Ns420p525 Ns420p1129 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1132 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz138) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50493447291) qz342) Bool.false 50493447291 33554432 5 524288 Bool.true 33554418 33554432 1 6760000 (Ns420p1126 rfl) (Enclosure.sfrac_false_div 50493447291 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50493447291) qz342) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns420p1127) qz343) 226375608064910080 72057594037927936 Bool.false 33554418 33554432 239 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q1 50493447291 33554432 226375608064910080 72057594037927936 239 Ns420p1127 Ns420p103 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554418 33554432 Ns420p1127 Ns420p103 107883386147 68719476736 13533204 13520000 (Ns420p1131 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns420p1133 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz138) Bool.false Ns420p1105 Ns420p1106 82448893511253279 8652800000000000000000 403947578329 268435456 2559 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz138) (@HAdd.hAdd Real Real Real qz341 qz448 (Enclosure.sfrac Bool.true Ns420p1107 Ns420p1108)) Bool.false Ns420p1105 Ns420p1106 82448893511253279 8652800000000000000000 Ns420p1109 (Ns420p1125 rfl rfl)) 

noncomputable def Ns420p1134 := Ns420p1104 46308 BSN.abs_quadSignPos (BSN.cos_quad_nat3 611 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 37696697 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 408 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 259951232 268435456) qz141 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 1) Bool.true 16777209 16777216 536317 55377920000 268435344 268435456 2600 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz138)) Bool.true 16777209 16777216 536317 55377920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz138) qz138) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz138)) Bool.true 33554418 33554432 34324288 3544186880000 16777209 16777216 536317 55377920000 (Ns420p1132 rfl rfl) rfl)) rfl) (Ns420p1133 rfl) RS421to432.d7 

noncomputable def Ns420p1135 := nat_lit 2046278462253571069756676571136 

noncomputable def Ns420p1136 := BSN.sin_dyadic_bound_f 37821712 268435456 2 1 268435456 134217728 Ns420p1135 Ns420p133 Ns420p1135 Ns420p1135 Ns420p134 Ns420p1135 37696697 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 37821712) qz344 0 1 Ns420p1135 Ns420p133 Ns420p1135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 37821712) qz345 0 1 Ns420p1135 Ns420p134 Ns420p1135 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1137 := nat_lit 20968443649283626039584519185281 

noncomputable def Ns420p1138 := BSN.cos_dyadic_bound_f 67669279 268435456 2 1 268435456 134217728 Ns420p1137 Ns420p285 Ns420p1137 Ns420p1137 Ns420p286 Ns420p1137 259951232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 67669279) qz346 0 1 Ns420p1137 Ns420p285 Ns420p1137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 67669279) qz347 0 1 Ns420p1137 Ns420p286 Ns420p1137 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1139 := nat_lit 33132388523789418097484241600625 

noncomputable def Ns420p1140 := BSN.cos_dyadic_bound_f 75868795 268435456 2 1 268435456 134217728 Ns420p1139 Ns420p285 Ns420p1139 Ns420p1139 Ns420p286 Ns420p1139 257785113 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 75868795) qz346 0 1 Ns420p1139 Ns420p285 Ns420p1139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 75868795) qz347 0 1 Ns420p1139 Ns420p286 Ns420p1139 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1141 := nat_lit 17226452534294773322482363416061722682170411471023827008162226990431361 

noncomputable def Ns420p1142 := nat_lit 3898140945532244368723944508803919406889081022905237152625835850881 

noncomputable def Ns420p1143 := nat_lit 51671561320993255478709642359167560207697456251025670550181429299592321 

noncomputable def Ns420p1144 := BSN.cos_dyadic_bound_f 210793489 268435456 3 2 268435456 134217728 Ns420p1141 Ns420p156 Ns420p1142 Ns420p1143 Ns420p159 Ns420p1142 189837437 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 210793489) qz346 0 2 Ns420p1141 Ns420p156 Ns420p1142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 210793489) qz347 0 2 Ns420p1143 Ns420p159 Ns420p1142 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1145 := Ns420p1102 78547 BSN.abs_quadSignPos (BSN.cos_quad_nat0 264 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 257785113 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 152 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 189837437 268435456) qz141 rfl rfl (Ns420p1134 RS421to432.d9 RS421to432.d11 RS421to432.d13 RS421to432.d17 (Ns420p1136 rfl rfl) (Ns420p1138 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns420p1133 rfl) RS421to432.d19 RS421to432.d21 RS421to432.d23 RS421to432.d25 RS421to432.d17 (Ns420p1140 rfl rfl) (Ns420p1144 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns420p1146 := nat_lit 124909274440807099931082194850625 

noncomputable def Ns420p1147 := BSN.sin_dyadic_bound_f 105717935 268435456 2 1 268435456 134217728 Ns420p1146 Ns420p133 Ns420p1146 Ns420p1146 Ns420p134 Ns420p1146 103006205 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 105717935) qz344 0 1 Ns420p1146 Ns420p133 Ns420p1146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 105717935) qz345 0 1 Ns420p1146 Ns420p134 Ns420p1146 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1148 := nat_lit 28972985214292248286057562897310791413668047246704651677186946651439511759723655407451914954900037592678400000 

noncomputable def Ns420p1149 := nat_lit 8847284027829146826889580158728027872790500738790922347461094074911330608166546888234438656000000000000 

noncomputable def Ns420p1150 := nat_lit 144747084067608680537694803335533455852474123107419843676275189062050332350262866822275051554843549499392000000 

noncomputable def Ns420p1151 := BSN.sin_dyadic_bound_f 379228380 268435456 4 3 268435456 134217728 Ns420p1148 Ns420p258 Ns420p1149 Ns420p1150 Ns420p261 Ns420p1149 265089252 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 379228380) qz344 0 3 Ns420p1148 Ns420p258 Ns420p1149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 379228380) qz345 0 3 Ns420p1150 Ns420p261 Ns420p1149 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1152 := Ns420p1100 105920 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 103006205 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 265089252 268435456) qz141 rfl rfl (Ns420p1145 rfl rfl) (Ns420p1133 rfl) RS421to432.d27 RS421to432.d29 RS421to432.d31 RS421to432.d33 RS421to432.d17 (Ns420p1147 rfl rfl) (Ns420p1151 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p1153 := nat_lit 4831676610951169023807630161664366321173178791850438615662402952804516909746670850152506769641031557763140625 

noncomputable def Ns420p1154 := nat_lit 721805199601274118810736564581872707429605274836044829969083545830137234546893478594959263359619140625 

noncomputable def Ns420p1155 := nat_lit 29292093124092287962769930518064261733293946811769965804343912436606799257878781187945736889763412900892740625 

noncomputable def Ns420p1156 := BSN.cos_dyadic_bound_f 307752555 268435456 4 3 268435456 134217728 Ns420p1153 Ns420p140 Ns420p1154 Ns420p1155 Ns420p143 Ns420p1154 110517327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 307752555) qz346 0 3 Ns420p1153 Ns420p140 Ns420p1154 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 307752555) qz347 0 3 Ns420p1155 Ns420p143 Ns420p1154 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1157 := nat_lit 105232274440778240109801216829954202007152170794639806101632471050390625 

noncomputable def Ns420p1158 := nat_lit 44879168245689790895377630549920365584735440854746672680816650390625 

noncomputable def Ns420p1159 := nat_lit 275535676310592845388029718390894467522070875653148949938982768650390625 

noncomputable def Ns420p1160 := BSN.sin_dyadic_bound_f 286091925 268435456 3 2 268435456 134217728 Ns420p1157 Ns420p119 Ns420p1158 Ns420p1159 Ns420p122 Ns420p1158 234925150 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 286091925) qz344 0 2 Ns420p1157 Ns420p119 Ns420p1158 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 286091925) qz345 0 2 Ns420p1159 Ns420p122 Ns420p1158 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1161 := Ns420p1098 129837 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 82 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 110517327 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 141 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 234925150 268435456) qz141 rfl rfl (Ns420p1152 rfl) (Ns420p1133 rfl) RS421to432.d35 RS421to432.d37 RS421to432.d39 RS421to432.d41 RS421to432.d17 (Ns420p1156 rfl rfl) (Ns420p1160 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p1162 := nat_lit 7781113988775354901653027939533986984729170470035994022121412945101056 

noncomputable def Ns420p1163 := nat_lit 795531086351484790627875735568038950365893597745207169409247723776 

noncomputable def Ns420p1164 := nat_lit 23341750904153361735377828067130824876286779622912491652025420339855616 

noncomputable def Ns420p1165 := BSN.cos_dyadic_bound_f 172815282 268435456 3 2 268435456 134217728 Ns420p1162 Ns420p156 Ns420p1163 Ns420p1164 Ns420p159 Ns420p1163 214702294 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 172815282) qz346 0 2 Ns420p1162 Ns420p156 Ns420p1163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 172815282) qz347 0 2 Ns420p1164 Ns420p159 Ns420p1163 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1166 := nat_lit 4829751312802749079327432970496 

noncomputable def Ns420p1167 := BSN.cos_dyadic_bound_f 46879308 268435456 2 1 268435456 134217728 Ns420p1166 Ns420p285 Ns420p1166 Ns420p1166 Ns420p286 Ns420p1166 264352370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 46879308) qz346 0 1 Ns420p1166 Ns420p285 Ns420p1166 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 46879308) qz347 0 1 Ns420p1166 Ns420p286 Ns420p1166 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1168 := Ns420p1096 151348 BSN.abs_quadSignNeg qz651 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 214702294 268435456) BSN.abs_quadSignNeg qz348 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 264352370 268435456) qz141 rfl rfl (Ns420p1161 rfl) (Ns420p1133 rfl) RS421to432.d43 RS421to432.d45 RS421to432.d47 RS421to432.d49 RS421to432.d17 (Ns420p1165 rfl rfl) (Ns420p1167 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p1169 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) 84746413 268435456 151348 268435456 84746413 268435456 151348 268435456 45497884036038656 84746413 134217728 37837 33554432 (Ns420p1168 rfl) 

noncomputable def Ns420p1170 := @Enclosure.Real.IsNear.mulLit_tf qz139 qz140 2508171 8388608 1 16777216 80903948441215 140737488355328 208639406385597 5946158883012608000 202920937265750667765 1180591620717411303424 

noncomputable abbrev qz145 := (@HPow.hPow Real Real Real qz443 qz444 qz328)

noncomputable def Ns420p1171 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz145 1 1 0 1 2508171 8388608 1 16777216 2508171 8388608 1 16777216 

noncomputable abbrev qz146 := qz444

noncomputable def Ns420p1172 := @Enclosure.Real.IsNear.sqrt_image qz146 52479648931 419430400 9827 419430400 187665898 187665935 16777216 (@Enclosure.Real.IsNear.of_eq qz146 (@HMul.hMul Real Real Real qz5 qz138 qz3) Bool.false 52479648931 419430400 9827 419430400 (BSN.t_div_two_pi_mk qz138 786160 1000 qz141) (@Enclosure.Real.IsNear.mulLit_ff qz138 qz3 786160 1000 0 1 5340353 33554432 1 33554432 52479648931 419430400 9827 419430400 (Enclosure.Real.IsNear.const Bool.false 786160 1000) RS421to432.d52 rfl)) 

noncomputable abbrev qz833 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 786160 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz696 := qz833

noncomputable abbrev qz450 := qz696

noncomputable abbrev qz147 := qz450

noncomputable abbrev qz451 := (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 375331833 33554432 37 33554432 375331833 33554432 37 33554432 (Ns420p1172 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns420p1173 := @Enclosure.Real.IsNear.sqrt_image qz147 375331833 33554432 37 33554432 56111596 56111603 16777216 qz451 rfl 

noncomputable def Ns420p1174 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz147) 112223199 33554432 7 33554432 5016341 5016343 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz147) Bool.false 112223199 33554432 7 33554432 112223199 33554432 7 33554432 (Ns420p1173 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p1175 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz147)) Bool.false 10032684 33554432 2 33554432 2508171 8388608 1 16777216 (Ns420p1174 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz834 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 786160 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1)))

noncomputable abbrev qz697 := (Real.cos qz834)

noncomputable abbrev qz452 := qz697

noncomputable abbrev qz148 := (@Inv.inv Real Real.instInv qz452)

noncomputable abbrev qz698 := (@HSub.hSub Real Real Real qz798 (@HMul.hMul Real Real Real qz795 qz832 qz832) qz832)

noncomputable abbrev qz453 := (@HMul.hMul Real Real Real qz619 qz617 (@HSub.hSub Real Real Real qz624 qz698 qz634))

noncomputable abbrev qz149 := (Real.cos qz453)

noncomputable def Ns420p1176 := @Enclosure.Real.IsNear.of_eq qz140 (@HMul.hMul Real Real Real qz5 qz148 qz149) Bool.false 80903948441215 

noncomputable def Ns420p1177 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz149 21358145 8388608 775 

noncomputable def Ns420p1178 := @Enclosure.Real.IsNear.recentre' qz148 Bool.false 85432580 33554432 1550 33554432 21358145 8388608 775 

noncomputable abbrev qz150 := qz452

noncomputable def Ns420p1179 := @Enclosure.Real.IsNear.recentre' qz150 Bool.false 6589406 16777216 807697216 113413980160000 3294703 8388608 12620269 1772093440000 

noncomputable abbrev qz699 := qz834

noncomputable abbrev qz454 := qz699

noncomputable abbrev qz151 := qz454

noncomputable def Ns420p1180 := @Enclosure.Real.IsNear.cos_image qz151 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19581801) qz364) Bool.false 19581801 16777216 117 16777216 Bool.false 6589406 16777216 1 

noncomputable def Ns420p1181 := nat_lit 998484790188171439937889731 

noncomputable abbrev qz152 := qz445

noncomputable def Ns420p1182 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz152 884279719003555 140737488355328 1 500000000000000 6233081 33554432 37 33554432 5511787115206397602955 4722366482869645213696 Ns420p1181 

noncomputable def Ns420p1183 := @Enclosure.Real.IsNear.subLit_ff_p qz147 qz1 375331833 33554432 37 33554432 11 1 0 1 6233081 6233081 33554432 37 

noncomputable def Ns420p1184 := @Ns420p1183 33554432 qz451 qz352 

noncomputable def Ns420p1185 := @Enclosure.Real.IsNear.recentre' qz151 Bool.false 5511787115206397602955 4722366482869645213696 Ns420p1181 Ns420p175 19581801 16777216 117 16777216 (@Ns420p1182 Ns420p175 RS421to432.d51 (Ns420p1184 rfl rfl) rfl) 

noncomputable def Ns420p1186 := nat_lit 19592004492103066732776303064251268701259809421510276848994881 

noncomputable def Ns420p1187 := nat_lit 21618276235471355026607606888348729135296192171697303374401 

noncomputable def Ns420p1188 := nat_lit 58732776923838257488275693978977108645508835880187435940235841 

noncomputable def Ns420p1189 := BSN.cos_dyadic_bound_f 19581801 16777216 3 2 16777216 6760000 Ns420p1186 Ns420p843 Ns420p1187 Ns420p1188 Ns420p846 Ns420p1187 6589406 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 19581801) (BSN.cosEvenQ 16777216) 0 2 Ns420p1186 Ns420p843 Ns420p1187 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 19581801) (BSN.cosOddQ 16777216) 0 2 Ns420p1188 Ns420p846 Ns420p1187 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1190 := @Enclosure.Real.IsNear.inv_image qz150 3294703 8388608 12620269 1772093440000 42715515 42717065 16777216 (Ns420p1179 (@Ns420p1180 6760000 (Ns420p1185 rfl) (Enclosure.sfrac_false_div 19581801 16777216) (Ns420p1189 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns420p1191 := @Enclosure.Real.IsNear.recentre' qz149 Bool.false 3787967 16777216 

noncomputable abbrev qz153 := qz453

noncomputable def Ns420p1192 := @Enclosure.Real.IsNear.cos_image qz153 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 45065355)) qz342) Bool.true 45065355 33554432 

noncomputable def Ns420p1193 := nat_lit 212815123739889195237859787725 

noncomputable def Ns420p1194 := nat_lit 45950900087965528985586300693318789 

noncomputable def Ns420p1195 := @Enclosure.Real.IsNear.recentre' qz153 Bool.true Ns420p1193 Ns420p190 Ns420p1194 

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz624 qz698 qz634)

noncomputable abbrev qz154 := qz455

noncomputable def Ns420p1196 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz154 884279719003555 140737488355328 1 500000000000000 240664937990095 

noncomputable abbrev qz456 := qz698

noncomputable abbrev qz155 := qz456

noncomputable def Ns420p1197 := @Enclosure.Real.IsNear.subLit_tf qz155 qz27 170296193812431 1125899906842624 1702763347 1125899906842624 1 16 

noncomputable abbrev qz700 := (@HMul.hMul Real Real Real qz795 qz832 qz832)

noncomputable abbrev qz457 := qz700

noncomputable abbrev qz156 := qz457

noncomputable def Ns420p1198 := @Enclosure.Real.IsNear.subLit_ff_n qz156 qz152 38851298752561 1125899906842624 461249363 1125899906842624 6233081 33554432 37 33554432 

noncomputable def Ns420p1199 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz152 6233081 33554432 37 33554432 6233081 33554432 37 33554432 38851298752561 1125899906842624 

noncomputable def Ns420p1200 := nat_lit 132536822969945601544767314538283310546761703614144408327574273442453326262476831160774997413140625 

noncomputable def Ns420p1201 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600 

noncomputable def Ns420p1202 := nat_lit 70163873773460089140780247529692222061241237014556070359220326994521172566947121640869140625 

noncomputable def Ns420p1203 := nat_lit 803020233350858018955357540617545775618800022200622233975790921531448574602605331518954295102740625 

noncomputable def Ns420p1204 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600 

noncomputable def Ns420p1205 := BSN.cos_dyadic_bound_f 45065355 33554432 4 3 16777216 6760000 Ns420p1200 Ns420p1201 Ns420p1202 Ns420p1203 Ns420p1204 Ns420p1202 3787967 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 45065355) qz635 0 3 Ns420p1200 Ns420p1201 Ns420p1202 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 45065355) (BSN.cosOddQ 33554432) 0 3 Ns420p1203 Ns420p1204 Ns420p1202 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1206 := @Ns420p1191 34324288 3544186880000 3787967 16777216 536317 55377920000 (@Ns420p1192 5 524288 Bool.false 3787967 16777216 1 6760000 (@Ns420p1195 Ns420p193 45065355 33554432 5 524288 (@Ns420p1196 1125899906842624 1702763347 1125899906842624 Ns420p1193 Ns420p190 Ns420p1194 Ns420p193 RS421to432.d51 (@Ns420p1197 0 1 3850639007841520 240664937990095 1125899906842624 1702763347 1125899906842624 (@Ns420p1198 5714192055138036744192 170296193812431 1125899906842624 1702763347 1125899906842624 (@Ns420p1199 461249363 1125899906842624 (Ns420p1184 rfl rfl) (Ns420p1184 rfl rfl) rfl) (Ns420p1184 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 45065355 33554432) (BSN.cos_neg_of_bound 45065355 33554432 Bool.false 3787967 16777216 1 6760000 (Ns420p1205 rfl rfl)) rfl rfl) 

noncomputable abbrev qz157 := (BSN.correction_mk qz445 (BSN.cos_two_pi_p_ne_zero_mk qz442 786160 1000 11 qz446 rfl rfl (@BSN.floor_sqrt_eq_dec qz442 786160 1000 11 qz446 rfl rfl rfl)))

noncomputable def Ns420p1207 := @Ns420p1170 1050025017568186145521 Ns420p726 (Ns420p1171 qz29 (@Enclosure.Real.IsNear.of_eq qz145 (@Inv.inv Real Real.instInv (Real.sqrt qz147)) Bool.false 2508171 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz146 (BSN.t_div_two_pi_nonneg qz138 786160 1000 qz141)) Ns420p1175) rfl) (@Ns420p1176 140737488355328 208639406385597 5946158883012608000 qz157 (@Ns420p1177 16777216 3787967 16777216 536317 55377920000 80903948441215 140737488355328 208639406385597 5946158883012608000 (@Ns420p1178 16777216 (Ns420p1190 rfl rfl rfl rfl rfl) rfl) (Ns420p1206 rfl) rfl)) 

noncomputable def Ns420p1208 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz138) (hardyZApproximantRS₀ qz138) Bool.true 542516394780706672139 1180591620717411303424 113542431845842210593521 Ns420p726 (@Eq.refl Real (hardyZApproximantRS₀ qz138)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz138) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (@HMul.hMul Real Real Real qz5 qz139 qz140)) Bool.true 542516394780706672139 1180591620717411303424 113542431845842210593521 Ns420p726 (BSN.hardyZApproximantRS₀_eq qz138 11 (@BSN.floor_sqrt_eq_dec qz138 786160 1000 11 qz141 rfl rfl rfl)) (@Ns420p1094 542516394780706672139 1180591620717411303424 113542431845842210593521 Ns420p726 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 11)) Bool.true 84746413 134217728 37837 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (Ns420p1169 (Ns420p1168 rfl) rfl rfl)) (Ns420p1207 rfl) rfl rfl)) 

theorem RS421to432.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz138) Bool.true 542516394780706672139 1180591620717411303424 113542431845842210593521 Ns420p726 := Ns420p1208 

theorem RS421to432.d64 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal (RS421to432.d3 a b h)) (hardyZApproximantRS a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal (RS421to432.d3 a b h)) 

theorem RS421to432.d65 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

theorem RS421to432.d66 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 qz323 RS421to432.d65 rfl 

theorem RS421to432.d67 : Enclosure.Real.IsNear qz3 Bool.false 1367130551 8589934592 1 8589934592 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 1367130551 8589934592 1 8589934592 1367130551 8589934592 1 8589934592 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 683565275 683565276 4294967296 RS421to432.d66 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz326 qz319 Real.pi)

theorem RS421to432.d68 : Enclosure.Real.IsNear qz158 Bool.false 884279719003555 70368744177664 1 250000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz319 Real.pi 4 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 70368744177664 1 250000000000000 (Enclosure.Real.IsNear.const Bool.false 4 1) RS421to432.d65 rfl 

noncomputable def Ns420p1209 := nat_lit 781950621441006189802102638025 

noncomputable def Ns420p1210 := nat_lit 79228162514264337593543950336 

noncomputable def Ns420p1211 := nat_lit 26986075409044041160201671 

noncomputable def Ns420p1212 := nat_lit 4294967296000000000000000000000000000000 

theorem RS421to432.d69 : Enclosure.Real.IsNear RSCompact.c2 Bool.false Ns420p1209 Ns420p1210 Ns420p1211 Ns420p1212 := @Enclosure.Real.IsNear.mulLit_ff Real.pi Real.pi 226375608064910080 72057594037927936 1 1000000000000000 226375608064910080 72057594037927936 1 1000000000000000 Ns420p1209 Ns420p1210 Ns420p1211 Ns420p1212 RS421to432.d65 RS421to432.d65 rfl 

noncomputable def Ns420p1213 := nat_lit 19807040628566084398385987584 

noncomputable def Ns420p1214 := nat_lit 1073741824000000000000000000000000000000 

noncomputable abbrev qz701 := (@HMul.hMul Real Real Real qz795 (Enclosure.sfrac Bool.false 4 1) RSCompact.c2)

noncomputable abbrev qz458 := qz701

noncomputable abbrev qz159 := qz458

theorem RS421to432.d70 : Enclosure.Real.IsNear qz159 Bool.false Ns420p1209 Ns420p1213 Ns420p1211 Ns420p1214 := @Enclosure.Real.IsNear.mulLit_ff qz319 RSCompact.c2 4 1 0 1 Ns420p1209 Ns420p1210 Ns420p1211 Ns420p1212 Ns420p1209 Ns420p1213 Ns420p1211 Ns420p1214 (Enclosure.Real.IsNear.const Bool.false 4 1) RS421to432.d69 rfl 

noncomputable def Ns420p1215 := nat_lit 691463075802508163054686763366652189853178875 

noncomputable def Ns420p1216 := nat_lit 2787593149816327892691964784081045188247552 

noncomputable def Ns420p1217 := nat_lit 2184744797947834540264818678394244808492865883128339 

noncomputable def Ns420p1218 := nat_lit 9223372036854775808000000000000000000000000000000000000000000000 

noncomputable def Ns420p1219 := nat_lit 22300745198530623141535718272648361505980416 

noncomputable def Ns420p1220 := nat_lit 73786976294838206464000000000000000000000000000000000000000000000 

noncomputable def Ns420p1221 := @Enclosure.Real.IsNear.mulLit_ff qz320 (@HMul.hMul Real Real Real qz5 RSCompact.c2 Real.pi) 8 1 0 1 Ns420p1215 Ns420p1219 Ns420p1217 Ns420p1220 Ns420p1215 Ns420p1216 Ns420p1217 Ns420p1218 (Enclosure.Real.IsNear.const Bool.false 8 1) (@Enclosure.Real.IsNear.mulLit_ff RSCompact.c2 Real.pi Ns420p1209 Ns420p1210 Ns420p1211 Ns420p1212 226375608064910080 72057594037927936 1 1000000000000000 Ns420p1215 Ns420p1219 Ns420p1217 Ns420p1220 RS421to432.d69 RS421to432.d65 rfl) rfl 

noncomputable abbrev qz702 := (@HMul.hMul Real Real Real qz5 qz320 RSCompact.c10)

theorem RS421to432.d71 : Enclosure.Real.IsNear qz702 Bool.false Ns420p1215 Ns420p1216 Ns420p1217 Ns420p1218 := Ns420p1221 

noncomputable def Ns420p1222 := nat_lit 2345851864323018569406307914075 

noncomputable def Ns420p1223 := nat_lit 2475880078570760549798248448 

noncomputable def Ns420p1224 := nat_lit 80958226227132123480605013 

noncomputable def Ns420p1225 := nat_lit 134217728000000000000000000000000000000 

noncomputable abbrev qz459 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 96 1) RSCompact.c2)

noncomputable abbrev qz460 := (Enclosure.sfrac Bool.false 96 1)

noncomputable def Ns420p1226 := @Enclosure.Real.IsNear.inv_image qz459 Ns420p1222 Ns420p1223 Ns420p1224 Ns420p1225 4533033 4533034 4294967296 (@Enclosure.Real.IsNear.mulLit_ff qz460 RSCompact.c2 96 1 0 1 Ns420p1209 Ns420p1210 Ns420p1211 Ns420p1212 Ns420p1222 Ns420p1223 Ns420p1224 Ns420p1225 (Enclosure.Real.IsNear.const Bool.false 96 1) RS421to432.d69 rfl) rfl rfl 

noncomputable abbrev qz461 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 96 1) RSCompact.c2))

theorem RS421to432.d72 : Enclosure.Real.IsNear qz461 Bool.false 9066067 8589934592 1 8589934592 := @Enclosure.Real.IsNear.recentre' qz461 Bool.false 9066067 8589934592 1 8589934592 9066067 8589934592 1 8589934592 (Ns420p1226 rfl rfl rfl rfl) rfl 

noncomputable def Ns420p1227 := nat_lit 179219426963482335273332210225833980843570437782311912911285639316589766168007115679481366764196203151689909829459123722670950249341690674585667 

noncomputable def Ns420p1228 := nat_lit 390218568789499028922699653724145788218574767833121393857394619953171467352470702515038262882936496394978366390175827861930996959911035663286272 

noncomputable def Ns420p1229 := nat_lit 392840682087582908802202534599902114363695229294058554226126045518256760923752303733991428578530306667318154188567561773629636241122701599313809198645788046805393667834062829076301239065192417 

noncomputable def Ns420p1230 := nat_lit 345115943707278711931062859873606023646172331721106903202448426240622354516333910726695638139782192859805410878999151431278133919088640000000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz703 := (Zeta.RiemannSiegel.correctionLinear qz152)

noncomputable abbrev qz462 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) qz140 (@HMul.hMul Real Real Real qz5 qz703 (@Inv.inv Real Real.instInv qz147)))

noncomputable def Ns420p1231 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz138) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (@HMul.hMul Real Real Real qz5 qz139 qz462)) Bool.true Ns420p1227 Ns420p1228 Ns420p1229 Ns420p1230 

noncomputable def Ns420p1232 := nat_lit 67168471890712207255222958950203979213255077444445767884610619384269108689928929294693515238574004493769919174405103889676289348294510346330045 

noncomputable def Ns420p1233 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (@HMul.hMul Real Real Real qz5 qz139 qz462) 84746413 134217728 37837 33554432 Ns420p1232 Ns420p1228 

noncomputable def Ns420p1234 := nat_lit 3677427526984039975109129203034388612884650371681865016454992118621564362102081785189468220657497756815442313465909249597319046882701599313809198645788046805393667834062829076301239065192417 

noncomputable def Ns420p1235 := nat_lit 24054424300500538008520908245729803814019547567107263538286624068100151123121181354333165265425126133246259057834871054927797034067675218021675566104576 

noncomputable def Ns420p1236 := nat_lit 26779861457098502157637162278889269995249557324618523970100371698847131511339908361389042150066325020809952421268368021827973191737927895 

noncomputable def Ns420p1237 := nat_lit 46517678354918840995156723704832290198633047083988355858015372747560914439257467092876227245680868195888801382801035387746214504231337984 

noncomputable def Ns420p1238 := nat_lit 5845828715225912432105197664252165436114337612868145377100884203348375437560178636775085433792172089201820083071461077037167292812755489425690565977809618256632248289720508681180023427 

noncomputable def Ns420p1239 := @Enclosure.Real.IsNear.mulLit_tf qz139 qz462 2508171 8388608 1 16777216 Ns420p1236 Ns420p1237 Ns420p1238 

noncomputable def Ns420p1240 := nat_lit 164564105847968440976649694382479678938947835789254619218086445923148324258963542331073588437930199079420762481212211337699000320000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1241 := nat_lit 38842449216649744403089194860968427318429458924391061866790949937386475300738353998924440148005008673109047788657475501184873287772375 

noncomputable def Ns420p1242 := nat_lit 71587220504674638027926003294503974885527510086719121782458041060741759666132099323400975082592019503360379626659683900404412812755489425690565977809618256632248289720508681180023427 

noncomputable abbrev qz463 := (@HMul.hMul Real Real Real qz5 qz703 (@Inv.inv Real Real.instInv qz147))

noncomputable def Ns420p1243 := @Enclosure.Real.IsNear.addLit_ff qz140 qz463 80903948441215 140737488355328 208639406385597 5946158883012608000 Ns420p1241 Ns420p1237 Ns420p1242 Ns420p1240 

noncomputable def Ns420p1244 := nat_lit 3768930439975697574056330809248128887518361159850846326861764306009862659919575762593476941162099185919107566163186663196044787596628384541282203074560 

noncomputable def Ns420p1245 := nat_lit 12948583701831237122851840693448418888415334944934006679498073982083968904269647586352986719872858750696825159691065574302106775 

noncomputable def Ns420p1246 := nat_lit 1386334847060407429789207092071541851718218537687908287585239790307310653902812811519987203052069789048695605480701785914487078912 

noncomputable def Ns420p1247 := nat_lit 372643074996173237922524142120569566391722746071181092730771966623136904746014053149685667923624146882504984840215902825402747008987719512790591212744843635647955613149070783 

noncomputable def Ns420p1248 := nat_lit 76631133373812046356801732621379047138126490539524061241227409766590373711177866128773236851175408381699008159903907840000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1249 := @Enclosure.Real.IsNear.mulLit_ff qz703 (@Inv.inv Real Real.instInv qz147) Ns420p1245 Ns420p1246 Ns420p1247 Ns420p1248 2999745 33554432 1 33554432 Ns420p1241 

noncomputable def Ns420p1250 := nat_lit 1428247078014230109136833060405181087721427047134552025646630891000912402728729843531157084971119091740313099350695905325 

noncomputable def Ns420p1251 := nat_lit 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336 

noncomputable def Ns420p1252 := nat_lit 10520152346378861440187648830252981103303569402145286406766916401446199034682276359770283763137706630100784576728036086643358886191628537910960133449908917723122975903411 

noncomputable def Ns420p1253 := nat_lit 2283785741740824173593572754304976676050618008957030214107853465276669672464664761089481021498900901725858693120000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1254 := @Enclosure.Real.IsNear.mulLit_tf (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz152) qz461 Ns420p1250 Ns420p1251 Ns420p1252 Ns420p1253 9066067 8589934592 1 8589934592 Ns420p1245 

noncomputable abbrev qz835 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 786160 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1)))

noncomputable abbrev qz836 := (Enclosure.sfrac Bool.false 1 1)

noncomputable abbrev qz704 := (@HMul.hMul Real Real Real qz795 qz793 (@HSub.hSub Real Real Real qz798 qz835 qz836))

noncomputable abbrev qz464 := (@HMul.hMul Real Real Real qz619 qz704 qz704)

noncomputable abbrev qz465 := qz704

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz326 qz464 qz465)

noncomputable abbrev qz161 := (Real.sin qz453)

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz326 qz318 qz465)

noncomputable def Ns420p1255 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz160 qz161) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz162 qz158) qz149) 

noncomputable abbrev qz705 := (Real.sin qz834)

noncomputable abbrev qz466 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz619 qz617 qz705))

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz326 qz318 qz466)

noncomputable abbrev qz467 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz619 qz701 qz697))

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz326 qz318 qz467)

noncomputable abbrev qz468 := qz705

noncomputable abbrev qz165 := qz468

noncomputable abbrev qz469 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 8 1) RSCompact.c9)

noncomputable def Ns420p1256 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns420p1255 (@HMul.hMul Real Real Real qz5 qz163 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz152))) (@HMul.hMul Real Real Real qz5 qz164 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz152))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz469 qz165) qz140) 

noncomputable abbrev qz166 := (BSN.cos_two_pi_p_ne_zero_mk qz442 786160 1000 11 qz446 rfl rfl (@BSN.floor_sqrt_eq_dec qz442 786160 1000 11 qz446 rfl rfl rfl))

noncomputable def Ns420p1257 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz152) (@HMul.hMul Real Real Real qz5 qz148 Ns420p1256) Bool.true Ns420p1250 Ns420p1251 Ns420p1252 Ns420p1253 (BSN.iteratedDeriv_three_correction_mk qz152 qz166) 

noncomputable def Ns420p1258 := nat_lit 65303293722117405598202898274375059183310915924543922771200127884787064767891340300320366460036764427282451325 

noncomputable def Ns420p1259 := nat_lit 18788340662190665823115844774314696219005460391266558965658327772257672200916867547709591987078149624255479808 

noncomputable def Ns420p1260 := nat_lit 961892016461939739987558046952664070345110763045760430800052374140681017050696215513797458234895722616152779928935593608132683333560213102205280191350428372247 

noncomputable def Ns420p1261 := @Enclosure.Real.IsNear.mulLit_ft qz148 Ns420p1256 21870980721 8589934592 1505 8589934592 Ns420p1258 Ns420p1259 Ns420p1260 

noncomputable def Ns420p1262 := nat_lit 531735304217046167141192768305767484952373897879624323478865778370916301492756409824239327921276190720000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1263 := @Enclosure.Real.IsNear.recentre' qz148 Bool.false 21870980721 8589934592 1505 8589934592 21870980721 8589934592 1505 

noncomputable def Ns420p1264 := @Enclosure.Real.IsNear.recentre' qz150 Bool.false 1686869401 4294967296 401427054592 14865397207531520000 1686869401 4294967296 24501163 907311841280000 

noncomputable def Ns420p1265 := @Enclosure.Real.IsNear.cos_image qz151 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10025922871) (@Nat.cast Real Real.instNatCast 8589934592)) Bool.false 10025922871 8589934592 227 8589934592 Bool.false 1686869401 4294967296 1 

noncomputable def Ns420p1266 := nat_lit 48574936421616554851182387 

noncomputable def Ns420p1267 := nat_lit 1844674407370955161600000000000000 

noncomputable def Ns420p1268 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz152 884279719003555 140737488355328 1 500000000000000 99729699 536870912 9 2147483648 88188950208029120079945 75557863725914323419136 Ns420p1266 

noncomputable def Ns420p1269 := @Enclosure.Real.IsNear.subLit_ff_p qz147 qz1 6005309731 536870912 9 2147483648 11 1 0 1 99729699 99729699 536870912 9 

noncomputable def Ns420p1270 := @Enclosure.Real.IsNear.sqrt_image qz146 13434791924677 107374182400 9827 107374182400 48042477830 48042477866 4294967296 (@Enclosure.Real.IsNear.of_eq qz146 (@HMul.hMul Real Real Real qz5 qz138 qz3) Bool.false 13434791924677 107374182400 9827 107374182400 (BSN.t_div_two_pi_mk qz138 786160 1000 qz141) (@Enclosure.Real.IsNear.mulLit_ff qz138 qz3 786160 1000 0 1 1367130551 8589934592 1 8589934592 13434791924677 107374182400 9827 107374182400 (Enclosure.Real.IsNear.const Bool.false 786160 1000) RS421to432.d67 rfl)) 

noncomputable def Ns420p1271 := @Ns420p1269 2147483648 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 96084955696 8589934592 36 8589934592 6005309731 536870912 9 2147483648 (Ns420p1270 rfl rfl rfl rfl rfl rfl) rfl) qz352 

noncomputable def Ns420p1272 := @Enclosure.Real.IsNear.recentre' qz151 Bool.false 88188950208029120079945 75557863725914323419136 Ns420p1266 Ns420p1267 10025922871 8589934592 227 8589934592 (@Ns420p1268 Ns420p1267 RS421to432.d66 (Ns420p1271 rfl rfl) rfl) 

noncomputable def Ns420p1273 := nat_lit 5984413207038703607616918642867912676777239591904212498626441527006285797247560839220650768130690882716450775902132734597079521 

noncomputable def Ns420p1274 := nat_lit 77306363950214634593683045803757368288933000143404161837719147552371292248891384948344470728359454342395494801251325357693337600 

noncomputable def Ns420p1275 := nat_lit 1031554816915175200784375243067602239835029131854625687769157717728939069248902943308684437696878962884676122357413519841 

noncomputable def Ns420p1276 := nat_lit 36278727618792319610981240930344791578832164954188975638904156699725652203624805123428191374196576717663331439947528368021643745 

noncomputable def Ns420p1277 := nat_lit 7034879119469531748025157168141920514292903013049778727232442427265787594649116030299346836280710345157990026913870607550093721600 

noncomputable def Ns420p1278 := BSN.cos_dyadic_bound_f 10025922871 8589934592 4 3 4294967296 1730560000 Ns420p1273 Ns420p1274 Ns420p1275 Ns420p1276 Ns420p1277 Ns420p1275 1686869401 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 10025922871) (BSN.cosEvenQ 8589934592) 0 3 Ns420p1273 Ns420p1274 Ns420p1275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 10025922871) (BSN.cosOddQ 8589934592) 0 3 Ns420p1276 Ns420p1277 Ns420p1275 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz470 := (Ns420p1264 (@Ns420p1265 1730560000 (Ns420p1272 rfl) (Enclosure.sfrac_false_div 10025922871 8589934592) (Ns420p1278 rfl rfl) rfl rfl) rfl)

noncomputable def Ns420p1279 := @Enclosure.Real.IsNear.inv_image qz150 1686869401 4294967296 24501163 907311841280000 10935489608 10935491113 4294967296 qz470 rfl 

noncomputable def Ns420p1280 := @Enclosure.Real.IsNear.subLit_ff_n (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns420p1255 (@HMul.hMul Real Real Real qz5 qz163 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz152))) (@HMul.hMul Real Real Real qz5 qz164 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz152))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz469 qz165) qz140) 

noncomputable def Ns420p1281 := nat_lit 2398502836411904229027403951003636012200619349805267833901783163415424628253169308742325950865449791738419180675 

noncomputable def Ns420p1282 := nat_lit 943650272919205513744914842041561976085327113066113130658351279633728687322422799914924491100959175195615411403749991082448700192656683766563545233065628372247 

noncomputable def Ns420p1283 := nat_lit 14480950937469320885730832306804662278599529044419052902076425268862384625 

noncomputable def Ns420p1284 := nat_lit 110427941548649020598956093796432407239217743554726184882600387580788736 

noncomputable def Ns420p1285 := nat_lit 2402500358797859944804009357881243556716400037897329964537135374530574377959460784468490591613220015580761959 

noncomputable def Ns420p1286 := nat_lit 70031368228273042693716399107903968949335692909897378797977600000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1287 := nat_lit 7211308302080239402997091982908753110913330161501609680062132547345270431428357826265274575816395497212761007711150391744864181321032848510264314906393537811865623004801595028275200 

noncomputable def Ns420p1288 := nat_lit 3567168371908216503832905172398419138424262332796077936850574620055023778362892971026821795988900293209823212675 

noncomputable def Ns420p1289 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 Ns420p1255 (@HMul.hMul Real Real Real qz5 qz163 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz152))) (@HMul.hMul Real Real Real qz5 qz164 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz152)) Ns420p1288 Ns420p1259 

noncomputable def Ns420p1290 := nat_lit 871967715495683738845567845145181047046497354856406651094816517814239803820321007274166564577621745484925925558160116776253583456027311516733396498907517652247 

noncomputable def Ns420p1291 := nat_lit 253413942498807433137907826674238375531173239746821177744913002188777660934399408076900911125 

noncomputable def Ns420p1292 := nat_lit 4074071952668972172536891376818756322102936787331872501272280898708762599526673412366794752 

noncomputable def Ns420p1293 := nat_lit 36789767804922713233269003006978462802092072186384762213856043781728127425894999858028906966676816300307122467950507905180044723451713 

noncomputable def Ns420p1294 := nat_lit 272903466044668431599732052040429624910807735065417902964223741019360920587993088000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1295 := nat_lit 9771673134222714991701098425051223121144771661972911951373527977669897473847234369547960046263011979810780420375200959159955279176346643935470309077272640354791034658747626577083057426491825347729817600 

noncomputable def Ns420p1296 := nat_lit 21675541664079556768932783611037965048352048157460599868638761671669826031141825 

noncomputable def Ns420p1297 := nat_lit 231584178474632390847141970017375815706539969331281128078915168015826259279872 

noncomputable def Ns420p1298 := nat_lit 36326547630996403362923176641074037641344402728566655283331915771441915264489920379284815162950394238155528357 

noncomputable def Ns420p1299 := nat_lit 3422649479228108567682335899719289050364090600517846115765106769920000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1300 := @Enclosure.Real.IsNear.subLit_ft Ns420p1255 (@HMul.hMul Real Real Real qz5 qz163 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz152)) Ns420p1296 Ns420p1297 Ns420p1298 Ns420p1299 

noncomputable def Ns420p1301 := nat_lit 1808639514260700056666093269375646625340448828567540007769937759141439397232643136059497588257364045225282335875 

noncomputable def Ns420p1302 := nat_lit 866324102857886208221337539915640838271027427134547685968668588397426131077257131278275543812319172581923023022262967099898968218287715031490221586907517652247 

noncomputable def Ns420p1303 := nat_lit 826099756889056263399280895515493775758269953095871702386594780604324927045539519914053124555481092764567815131163255265586556518610778821064752501211233701844522331067460769226275002777600 

noncomputable def Ns420p1304 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz5 qz160 qz161) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz162 qz158) qz149) 

noncomputable def Ns420p1305 := nat_lit 13891760146610695413346959163237596841832834424508330178083921647711135881970625 

noncomputable def Ns420p1306 := nat_lit 207885641123378744236505231504156424355746111057751276085975347235583732852551889277756518390163125096021868641 

noncomputable def Ns420p1307 := nat_lit 44494443229965411379870366696350757654733177806731999504946388008960000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1308 := nat_lit 191885029184783340137287423600556767574805514725 

noncomputable def Ns420p1309 := nat_lit 5708990770823839524233143877797980545530986496 

noncomputable def Ns420p1310 := nat_lit 13346742859622871501053699766180216150465205425717875839733440628163 

noncomputable def Ns420p1311 := nat_lit 2246395312876507825207433931873782333440000000000000000000000000000000000 

noncomputable def Ns420p1312 := nat_lit 123745467312837798071559274169406775082069378787323545441024453254773892695504036781982592218497983003560328879000209535795200 

noncomputable def Ns420p1313 := nat_lit 3320157625606043442574087691739971859943327411731640428278981923510375 

noncomputable def Ns420p1314 := nat_lit 53919893334301279589334030174039261347274288845081144962207220498432 

noncomputable def Ns420p1315 := @Enclosure.Real.IsNear.mulLit_tt qz160 qz161 Ns420p1313 Ns420p1314 

noncomputable def Ns420p1316 := nat_lit 241636623019434424759286259450016626008476550239362142612148421196388312865388594349973110845139 

noncomputable def Ns420p1317 := nat_lit 98079714615416886934934209737619787751599303819750539264000000000000000000000000000000000000000000000 

noncomputable def Ns420p1318 := nat_lit 22255591177548721555275665828117011173786838225 

noncomputable def Ns420p1319 := nat_lit 1427247692705959881058285969449495136382746624 

noncomputable def Ns420p1320 := nat_lit 8845896869863405804916834884416121971089002829982433173692841 

noncomputable def Ns420p1321 := nat_lit 21267647932558653966460912964485513216000000000000000000000000000000 

noncomputable abbrev qz167 := qz464

noncomputable abbrev qz168 := qz465

noncomputable def Ns420p1322 := @Enclosure.Real.IsNear.mulLit_ft qz167 qz168 Ns420p1318 Ns420p1319 Ns420p1320 Ns420p1321 

noncomputable def Ns420p1323 := nat_lit 242874684478082080791905279 

noncomputable def Ns420p1324 := nat_lit 4611686018427387904000000000000000 

noncomputable def Ns420p1325 := @Enclosure.Real.IsNear.mulLit_tt qz168 qz168 149183079394242031966135 37778931862957161709568 Ns420p1323 Ns420p1324 149183079394242031966135 37778931862957161709568 

noncomputable abbrev qz706 := (@HSub.hSub Real Real Real qz798 qz835 qz836)

noncomputable abbrev qz471 := qz706

noncomputable abbrev qz169 := qz471

noncomputable def Ns420p1326 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz169 884279719003555 140737488355328 1 500000000000000 168705757 268435456 9 1073741824 

noncomputable abbrev qz707 := qz835

noncomputable abbrev qz472 := qz707

noncomputable abbrev qz170 := qz472

noncomputable abbrev qz708 := qz836

noncomputable abbrev qz473 := qz708

noncomputable abbrev qz171 := qz473

noncomputable def Ns420p1327 := @Enclosure.Real.IsNear.subLit_ff_n qz170 qz171 99729699 268435456 9 1073741824 1 1 0 1 168705757 

noncomputable def Ns420p1328 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz152 2 1 0 1 99729699 536870912 9 2147483648 99729699 268435456 9 

noncomputable def Ns420p1329 := @Enclosure.Real.IsNear.recentre' qz161 Bool.true 4184066455 4294967296 

noncomputable abbrev qz709 := (@Nat.cast Real Real.instNatCast 2147483648)

noncomputable def Ns420p1330 := @Enclosure.Real.IsNear.sin_image qz153 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2884189109)) qz709) Bool.true 2884189109 2147483648 

noncomputable def Ns420p1331 := nat_lit 54480791919117240724853518726405 

noncomputable def Ns420p1332 := nat_lit 40564819207303340847894502572032 

noncomputable def Ns420p1333 := nat_lit 715343960432027560220388754304744159 

noncomputable def Ns420p1334 := @Enclosure.Real.IsNear.recentre' qz153 Bool.true Ns420p1331 Ns420p1332 Ns420p1333 

noncomputable def Ns420p1335 := nat_lit 19807040628566084398385987584000000000000000 

noncomputable def Ns420p1336 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz154 884279719003555 140737488355328 1 500000000000000 61610360102466871 

noncomputable def Ns420p1337 := @Enclosure.Real.IsNear.subLit_tf qz155 qz27 43595961592984887 288230376151711744 26507891241 4611686018427387904 1 16 

noncomputable def Ns420p1338 := @Enclosure.Real.IsNear.subLit_ff_n qz156 qz152 9946012862630601 288230376151711744 7180538409 4611686018427387904 99729699 536870912 9 2147483648 

noncomputable def Ns420p1339 := nat_lit 23405403659942769085906944 

noncomputable def Ns420p1340 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz152 99729699 536870912 9 2147483648 99729699 536870912 9 2147483648 9946012862630601 288230376151711744 

noncomputable def Ns420p1341 := nat_lit 1625923258001351174073410829304185148729565793277454708593962433776088991574587018123277410608335451766999032362433134481 

noncomputable def Ns420p1342 := nat_lit 59901638707684889418952440944245206579931318871036416524073417078305888130401850004701502291481072095104541326538755276800 

noncomputable def Ns420p1343 := nat_lit 331348333665910018222354636790782358012809783164486551371146155443429457927208626276149758737747663685718951739281 

noncomputable def Ns420p1344 := nat_lit 8124213483793183285544763199980799118812503942078027453879710961072841517402162478386696752154250685635174154805820669841 

noncomputable def Ns420p1345 := nat_lit 2096557354768971129663335433048582230297596160486274578342569597740706084564064750164552580201837523328658946428856434688000 

noncomputable def Ns420p1346 := BSN.sin_dyadic_bound_f 2884189109 2147483648 4 3 4294967296 1730560000 Ns420p1341 Ns420p1342 Ns420p1343 Ns420p1344 Ns420p1345 Ns420p1343 4184066455 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 2884189109) (BSN.sinEvenQ 2147483648) 0 3 Ns420p1341 Ns420p1342 Ns420p1343 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 2884189109) (BSN.sinOddQ 2147483648) 0 3 Ns420p1344 Ns420p1345 Ns420p1343 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1347 := @Ns420p1329 68565581824 1858174650941440000 4184066455 4294967296 4184911 113413980160000 (@Ns420p1330 39 1073741824 Bool.true 4184066455 4294967296 1 1730560000 (@Ns420p1334 Ns420p1335 2884189109 2147483648 39 1073741824 (@Ns420p1336 288230376151711744 26507891241 4611686018427387904 Ns420p1331 Ns420p1332 Ns420p1333 Ns420p1335 RS421to432.d66 (@Ns420p1337 0 1 985765761639469936 61610360102466871 288230376151711744 26507891241 4611686018427387904 (@Ns420p1338 Ns420p1339 43595961592984887 288230376151711744 26507891241 4611686018427387904 (@Ns420p1340 7180538409 4611686018427387904 (Ns420p1271 rfl rfl) (Ns420p1271 rfl rfl) rfl) (Ns420p1271 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2884189109 2147483648) (BSN.sin_neg_of_bound 2884189109 2147483648 Bool.false 4184066455 4294967296 1 1730560000 (Ns420p1346 rfl rfl)) rfl rfl) 

noncomputable def Ns420p1348 := nat_lit 395758714580476140276748217219113829775 

noncomputable def Ns420p1349 := nat_lit 2658455991569831745807614120560689152 

noncomputable def Ns420p1350 := nat_lit 19662704120109297074596726729167576582826868412830379 

noncomputable def Ns420p1351 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz162 qz158) qz149 Ns420p1348 Ns420p1349 Ns420p1350 

noncomputable def Ns420p1352 := nat_lit 9903520314283042199192993792000000000000000000000000000000 

noncomputable def Ns420p1353 := nat_lit 728624053434246242375715837 

noncomputable def Ns420p1354 := @Enclosure.Real.IsNear.mulLit_tf qz162 qz158 447549238182726095898405 37778931862957161709568 Ns420p1353 Ns420p1324 884279719003555 

noncomputable def Ns420p1355 := @Enclosure.Real.IsNear.mulLit_ft qz318 qz168 3 1 0 1 149183079394242031966135 37778931862957161709568 Ns420p1323 

noncomputable def Ns420p1356 := @Enclosure.Real.IsNear.recentre' qz149 Bool.false 969707158 4294967296 

noncomputable def Ns420p1357 := @Enclosure.Real.IsNear.cos_image qz153 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2884189109)) qz709) Bool.true 2884189109 2147483648 

noncomputable def Ns420p1358 := nat_lit 625893007111011143104123058768149725547255328408401158759382349582580548682402147129166641522263879739723243526950633361 

noncomputable def Ns420p1359 := nat_lit 4607818362129606878380956995711169736917793759310493578774878236792760625415526923438577099344697853469580102041442713600 

noncomputable def Ns420p1360 := nat_lit 3792189458153773263659774342890400141477396720464158986234902789093766709336812278317599471791511639439423406953539977105 

noncomputable def Ns420p1361 := nat_lit 419311470953794225932667086609716446059519232097254915668513919548141216912812950032910516040367504665731789285771286937600 

noncomputable def Ns420p1362 := BSN.cos_dyadic_bound_f 2884189109 2147483648 4 3 4294967296 1730560000 Ns420p1358 Ns420p1359 Ns420p1343 Ns420p1360 Ns420p1361 Ns420p1343 969707158 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 2884189109) (BSN.cosEvenQ 2147483648) 0 3 Ns420p1358 Ns420p1359 Ns420p1343 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 2884189109) (BSN.cosOddQ 2147483648) 0 3 Ns420p1360 Ns420p1361 Ns420p1343 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1363 := @Ns420p1356 68565581824 1858174650941440000 484853579 2147483648 4184911 113413980160000 (@Ns420p1357 39 1073741824 Bool.false 969707158 4294967296 1 1730560000 (@Ns420p1334 Ns420p1335 2884189109 2147483648 39 1073741824 (@Ns420p1336 288230376151711744 26507891241 4611686018427387904 Ns420p1331 Ns420p1332 Ns420p1333 Ns420p1335 RS421to432.d66 (@Ns420p1337 0 1 985765761639469936 61610360102466871 288230376151711744 26507891241 4611686018427387904 (@Ns420p1338 Ns420p1339 43595961592984887 288230376151711744 26507891241 4611686018427387904 (@Ns420p1340 7180538409 4611686018427387904 (Ns420p1271 rfl rfl) (Ns420p1271 rfl rfl) rfl) (Ns420p1271 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2884189109 2147483648) (BSN.cos_neg_of_bound 2884189109 2147483648 Bool.false 969707158 4294967296 1 1730560000 (Ns420p1362 rfl rfl)) rfl rfl) 

noncomputable abbrev qz172 := (@Ns420p1326 149183079394242031966135 37778931862957161709568 Ns420p1323 Ns420p1324 RS421to432.d66 (@Ns420p1327 168705757 268435456 9 1073741824 (@Ns420p1328 1073741824 qz323 (Ns420p1271 rfl rfl) rfl) (Enclosure.Real.IsNear.const Bool.false 1 1) rfl rfl) rfl)

noncomputable abbrev qz474 := (Enclosure.Real.IsNear.const Bool.false 3 1)

noncomputable def Ns420p1364 := @Ns420p1304 Ns420p1305 Ns420p1297 Ns420p1306 Ns420p1307 Ns420p1308 Ns420p1309 Ns420p1310 Ns420p1311 Ns420p1312 Ns420p1296 Ns420p1297 Ns420p1298 Ns420p1299 (@Ns420p1315 Ns420p1316 Ns420p1317 4184066455 4294967296 4184911 113413980160000 Ns420p1305 Ns420p1297 Ns420p1306 Ns420p1307 (@Ns420p1322 149183079394242031966135 37778931862957161709568 Ns420p1323 Ns420p1324 Ns420p1313 Ns420p1314 Ns420p1316 Ns420p1317 (@Ns420p1325 Ns420p1323 Ns420p1324 Ns420p1318 Ns420p1319 Ns420p1320 Ns420p1321 qz172 qz172 rfl) qz172 rfl) (Ns420p1347 rfl) rfl) (@Ns420p1351 Ns420p1352 484853579 2147483648 4184911 113413980160000 Ns420p1308 Ns420p1309 Ns420p1310 Ns420p1311 (@Ns420p1354 70368744177664 1 250000000000000 Ns420p1348 Ns420p1349 Ns420p1350 Ns420p1352 (@Ns420p1355 Ns420p1324 447549238182726095898405 37778931862957161709568 Ns420p1353 Ns420p1324 qz474 qz172 rfl) RS421to432.d68 rfl) (Ns420p1363 rfl) rfl) rfl rfl 

noncomputable def Ns420p1365 := nat_lit 5239141693759507449074145 

noncomputable def Ns420p1366 := nat_lit 1983570718484245102073806630705863 

noncomputable def Ns420p1367 := nat_lit 3896874685571142778880000000000000000000 

noncomputable def Ns420p1368 := nat_lit 345216758770815965567439819791868801549190896968122650335197248808314161006089620495075 

noncomputable def Ns420p1369 := @Enclosure.Real.IsNear.mulLit_tf qz163 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz152) Ns420p1365 302231454903657293676544 Ns420p1366 Ns420p1367 Ns420p1368 

noncomputable def Ns420p1370 := nat_lit 62165404551223330269422781018352605012557018849668464680057997111644937126566671941632 

noncomputable def Ns420p1371 := nat_lit 12802339040584910277464738925705258006625094873838916923095653405173518219038331636035090966326378620958344133580361719 

noncomputable def Ns420p1372 := nat_lit 136451733022334215799866026020214812455403867532708951482111870509680460293996544000000000000000000000000000000000000000000 

noncomputable def Ns420p1373 := nat_lit 1746380564586502483024715 

noncomputable def Ns420p1374 := nat_lit 661190239494748367357935543568621 

noncomputable abbrev qz173 := qz466

noncomputable def Ns420p1375 := @Enclosure.Real.IsNear.mulLit_ft qz318 qz173 3 1 0 1 Ns420p1373 302231454903657293676544 Ns420p1374 

noncomputable def Ns420p1376 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz165 884279719003555 140737488355328 1 500000000000000 1974918713 2147483648 24501163 907311841280000 Ns420p1373 

noncomputable def Ns420p1377 := @Enclosure.Real.IsNear.recentre' qz165 Bool.false 3949837426 4294967296 401427054592 14865397207531520000 1974918713 2147483648 24501163 907311841280000 

noncomputable def Ns420p1378 := @Enclosure.Real.IsNear.sin_image qz151 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10025922871) (@Nat.cast Real Real.instNatCast 8589934592)) Bool.false 10025922871 8589934592 227 8589934592 Bool.false 3949837426 4294967296 1 

noncomputable def Ns420p1379 := nat_lit 15551842037137281390283558208203046779714837277414157113029713101360172285669019829423598744636563511495557691911447354003497441 

noncomputable def Ns420p1380 := nat_lit 1004982731352790249717879595448845787756129001864254103890348918180826799235588004328478119468672906451141432416267229650013388800 

noncomputable def Ns420p1381 := nat_lit 77729724000038526625016566735263503987342310516651272903017431373473403886491965691689964284731827686885833950582489674571653601 

noncomputable def Ns420p1382 := nat_lit 35174395597347658740125785840709602571464515065248893636162212136328937973245580151496734181403551725789950134569353037750468608000 

noncomputable def Ns420p1383 := BSN.sin_dyadic_bound_f 10025922871 8589934592 4 3 4294967296 1730560000 Ns420p1379 Ns420p1380 Ns420p1275 Ns420p1381 Ns420p1382 Ns420p1275 3949837426 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 10025922871) (BSN.sinEvenQ 8589934592) 0 3 Ns420p1379 Ns420p1380 Ns420p1275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 10025922871) (BSN.sinOddQ 8589934592) 0 3 Ns420p1381 Ns420p1382 Ns420p1275 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz475 := (@HMul.hMul Real Real Real qz619 qz617 qz705)

noncomputable abbrev qz174 := qz475

noncomputable abbrev qz476 := (@Enclosure.Real.IsNear.neg qz174 Bool.false Ns420p1373 302231454903657293676544 Ns420p1374 Ns420p1367 (@Ns420p1376 302231454903657293676544 Ns420p1374 Ns420p1367 RS421to432.d66 (Ns420p1377 (@Ns420p1378 1730560000 (Ns420p1272 rfl) (Enclosure.sfrac_false_div 10025922871 8589934592) (Ns420p1383 rfl rfl) rfl rfl) rfl) rfl))

noncomputable def Ns420p1384 := @Ns420p1375 Ns420p1367 Ns420p1365 302231454903657293676544 Ns420p1366 Ns420p1367 qz474 qz476 rfl 

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz326 qz464 (Real.cos qz453))

noncomputable def Ns420p1385 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz175) (@HMul.hMul Real Real Real qz5 qz158 qz161) 

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz326 qz316 qz466)

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz326 qz467 (Zeta.RiemannSiegel.correction qz445))

noncomputable def Ns420p1386 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz152) (@HMul.hMul Real Real Real qz5 qz148 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns420p1385 (@HMul.hMul Real Real Real qz5 qz176 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz152))) qz177)) 

noncomputable def Ns420p1387 := @Enclosure.Real.IsNear.mulLit_ff qz148 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns420p1385 (@HMul.hMul Real Real Real qz5 qz176 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz152))) qz177) 21870980721 

noncomputable def Ns420p1388 := nat_lit 15784237715474138457014088636389905468893897479473830968459809324904125821075 

noncomputable def Ns420p1389 := nat_lit 7237005577332262213973186563042994240829374041602535252466099000494570602496 

noncomputable def Ns420p1390 := nat_lit 1165946419997657993354636994311135900255813758404718297790007688806955038234455508140900547986234684522629513 

noncomputable def Ns420p1391 := nat_lit 31770144827276052860511938580361849734420857283451815946519344698097664000000000000000000000000000000000000000000 

noncomputable def Ns420p1392 := nat_lit 48721654150172642591980296944443655045699869233948059703921801773230313705325 

noncomputable def Ns420p1393 := @Enclosure.Real.IsNear.subLit_tt_p (@HSub.hSub Real Real Real qz11 Ns420p1385 (@HMul.hMul Real Real Real qz5 qz176 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz152))) qz177 Ns420p1392 Ns420p1389 

noncomputable def Ns420p1394 := nat_lit 1080709521823994441018450577625759154581907170034999778784460048864637732450140337534806531558675587055749513 

noncomputable def Ns420p1395 := nat_lit 13987485619769853743700989061334366323493089213875443268475 

noncomputable def Ns420p1396 := nat_lit 1569275433846670190958947355801916604025588861116008628224 

noncomputable def Ns420p1397 := nat_lit 21873143236878520389227076326497487584836963042648223157227257312741675419576672601 

noncomputable def Ns420p1398 := nat_lit 8152724270274984032581141114689406118045525265612800000000000000000000000000000000000000 

noncomputable def Ns420p1399 := nat_lit 24769816488889652988134643600060383670159702699188867554534794173913838648415541331604867506259787483508723033120730202395808419020800 

noncomputable def Ns420p1400 := nat_lit 26730589599612274796871400433602744156012436137808297925 

noncomputable def Ns420p1401 := nat_lit 3064991081731777716716694054300618367237478244367204352 

noncomputable def Ns420p1402 := nat_lit 5465635553681201885678046179329394825667241693606716252467016365717737901177 

noncomputable def Ns420p1403 := nat_lit 4824097201346144397977006576739293560973683589120000000000000000000000000000000000 

noncomputable def Ns420p1404 := @Enclosure.Real.IsNear.subLit_ff_n Ns420p1385 (@HMul.hMul Real Real Real qz5 qz176 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz152)) Ns420p1400 Ns420p1401 Ns420p1402 Ns420p1403 

noncomputable def Ns420p1405 := nat_lit 111837474346449110592527172777701539809642745580487504329315801775264642895725 

noncomputable def Ns420p1406 := nat_lit 1044714386181805002748970708970850050646658514631823912171083460138240746399918283705542596840042012655749513 

noncomputable def Ns420p1407 := nat_lit 149331435457499204983294109509214796975990935764513246312352285113146912899179735642698884561858479922201258889396202740220585574400 

noncomputable def Ns420p1408 := @Enclosure.Real.IsNear.subLit_tt_p (@Neg.neg Real Real.instNeg qz175) (@HMul.hMul Real Real Real qz5 qz158 qz161) 

noncomputable def Ns420p1409 := nat_lit 10790703035195322092949852908370531698393539496485257275 

noncomputable def Ns420p1410 := nat_lit 3228740794499114685422583332292806102494177662026589955796808365717737901177 

noncomputable def Ns420p1411 := nat_lit 3699885109119600501247525 

noncomputable def Ns420p1412 := nat_lit 112934324775201185140819682456937 

noncomputable def Ns420p1413 := nat_lit 243554667848196423680000000000000000000 

noncomputable def Ns420p1414 := nat_lit 8078824985123387904070000106657009249784688172357048912050432000260394136371200 

noncomputable def Ns420p1415 := @Enclosure.Real.IsNear.neg qz175 Bool.false Ns420p1409 

noncomputable def Ns420p1416 := @Enclosure.Real.IsNear.mulLit_ff qz167 qz149 Ns420p1318 Ns420p1319 Ns420p1320 

noncomputable def Ns420p1417 := @Enclosure.Real.IsNear.mulLit_ft qz158 qz161 884279719003555 70368744177664 1 

noncomputable def Ns420p1418 := nat_lit 1948437342785571389440000000000000000000 

noncomputable def Ns420p1419 := nat_lit 64039577978771950588498741616233635460083795845535015 

noncomputable def Ns420p1420 := @Enclosure.Real.IsNear.mulLit_tt qz176 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz152) Ns420p1373 151115727451828646838272 Ns420p1374 Ns420p1418 Ns420p1419 

noncomputable def Ns420p1421 := nat_lit 47890485652059026823698344598447161988085597568237568 

noncomputable def Ns420p1422 := nat_lit 22877952429494086963915406501344838951779757170356869039805832484389 

noncomputable def Ns420p1423 := nat_lit 8152724270274984032581141114689406118045525265612800000000000000000000000 

noncomputable def Ns420p1424 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz173 2 1 0 1 Ns420p1373 302231454903657293676544 Ns420p1374 

noncomputable def Ns420p1425 := @Ns420p1424 Ns420p1367 Ns420p1373 151115727451828646838272 Ns420p1374 Ns420p1418 qz323 qz476 rfl 

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz326 qz465 (Real.sin qz453))

noncomputable def Ns420p1426 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz178) (@HMul.hMul Real Real Real qz5 qz173 qz140) 

noncomputable def Ns420p1427 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz152) (@HMul.hMul Real Real Real qz5 qz148 Ns420p1426) Bool.true Ns420p1419 Ns420p1421 Ns420p1422 Ns420p1423 (BSN.deriv_correction_mk qz152 qz166) 

noncomputable def Ns420p1428 := nat_lit 2928061562291198847813146568784524487080215 

noncomputable def Ns420p1429 := nat_lit 5575186299632655785383929568162090376495104 

noncomputable def Ns420p1430 := nat_lit 4046963052964484285600782716650710409166067009062460839831 

noncomputable def Ns420p1431 := @Enclosure.Real.IsNear.mulLit_ft qz148 Ns420p1426 21870980721 8589934592 1505 8589934592 Ns420p1428 Ns420p1429 Ns420p1430 

noncomputable def Ns420p1432 := nat_lit 3796408078761298224600563344866692143513600000000000000000000000 

noncomputable def Ns420p1433 := @Enclosure.Real.IsNear.subLit_tt_n (@Neg.neg Real Real.instNeg qz178) (@HMul.hMul Real Real Real qz5 qz173 qz140) 

noncomputable def Ns420p1434 := nat_lit 624191918147049806100543149501425 

noncomputable def Ns420p1435 := nat_lit 162259276829213363391578010288128 

noncomputable def Ns420p1436 := nat_lit 412179262040954330497154828647828480121301 

noncomputable def Ns420p1437 := nat_lit 2092118666392292664579519938560000000000000000000 

noncomputable def Ns420p1438 := nat_lit 18519009436661503840866646350779148156094185 

noncomputable def Ns420p1439 := nat_lit 3299012802604864516857256305887302107221104032944250279831 

noncomputable def Ns420p1440 := nat_lit 475105151608786602503278847992860812352436738977653642930933771485598187520 

noncomputable def Ns420p1441 := @Enclosure.Real.IsNear.neg qz178 Bool.false Ns420p1434 

noncomputable def Ns420p1442 := @Enclosure.Real.IsNear.mulLit_tt qz168 qz161 149183079394242031966135 37778931862957161709568 Ns420p1323 

noncomputable def Ns420p1443 := @Enclosure.Real.IsNear.mulLit_tf qz173 qz140 Ns420p1373 302231454903657293676544 Ns420p1374 Ns420p1367 10604223278816850459 18446744073709551616 

noncomputable def Ns420p1444 := nat_lit 1948437342785571389440000 

noncomputable def Ns420p1445 := @Enclosure.Real.IsNear.of_eq qz140 (@HMul.hMul Real Real Real qz5 qz148 qz149) Bool.false 10604223278816850459 

noncomputable def Ns420p1446 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz149 21870980721 8589934592 1505 

noncomputable abbrev qz477 := (@Ns420p1445 18446744073709551616 260131280416005647 Ns420p1444 qz157 (@Ns420p1446 8589934592 484853579 2147483648 4184911 113413980160000 10604223278816850459 18446744073709551616 260131280416005647 Ns420p1444 (@Ns420p1263 8589934592 (Ns420p1279 rfl rfl rfl rfl rfl) rfl) (Ns420p1363 rfl) rfl))

noncomputable def Ns420p1447 := @Ns420p1443 260131280416005647 Ns420p1444 Ns420p1438 Ns420p1429 Ns420p1439 Ns420p1432 qz476 qz477 

noncomputable abbrev qz478 := (@Ns420p1263 8589934592 (Ns420p1279 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns420p1448 := @Ns420p1420 Ns420p1421 Ns420p1422 Ns420p1423 Ns420p1405 Ns420p1389 Ns420p1406 Ns420p1391 Ns420p1425 (Ns420p1427 (@Ns420p1431 Ns420p1432 Ns420p1419 Ns420p1421 Ns420p1422 Ns420p1423 qz478 (@Ns420p1433 Ns420p1434 Ns420p1435 Ns420p1436 Ns420p1437 Ns420p1438 Ns420p1429 Ns420p1439 Ns420p1432 Ns420p1440 Ns420p1428 Ns420p1429 Ns420p1430 Ns420p1432 (@Ns420p1441 Ns420p1435 Ns420p1436 Ns420p1437 (@Ns420p1442 Ns420p1324 4184066455 4294967296 4184911 113413980160000 Ns420p1434 Ns420p1435 Ns420p1436 Ns420p1437 qz172 (Ns420p1347 rfl) rfl)) (Ns420p1447 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns420p1449 := @Ns420p1404 Ns420p1405 Ns420p1389 Ns420p1406 Ns420p1391 Ns420p1407 Ns420p1392 Ns420p1389 Ns420p1394 Ns420p1391 (@Ns420p1408 Ns420p1409 Ns420p1401 Ns420p1410 Ns420p1403 Ns420p1411 302231454903657293676544 Ns420p1412 Ns420p1413 Ns420p1414 Ns420p1400 Ns420p1401 Ns420p1402 Ns420p1403 (@Ns420p1415 Ns420p1401 Ns420p1410 Ns420p1403 (@Ns420p1416 Ns420p1321 484853579 2147483648 4184911 113413980160000 Ns420p1409 Ns420p1401 Ns420p1410 Ns420p1403 (@Ns420p1325 Ns420p1323 Ns420p1324 Ns420p1318 Ns420p1319 Ns420p1320 Ns420p1321 qz172 qz172 rfl) (Ns420p1363 rfl) rfl)) (@Ns420p1417 250000000000000 4184066455 4294967296 4184911 113413980160000 Ns420p1411 302231454903657293676544 Ns420p1412 Ns420p1413 RS421to432.d68 (Ns420p1347 rfl) rfl) rfl rfl) Ns420p1448 

noncomputable def Ns420p1450 := nat_lit 1319048576401767868228765185545751573025 

noncomputable def Ns420p1451 := nat_lit 85070591730234615865843651857942052864 

noncomputable def Ns420p1452 := nat_lit 17842929634517869145947069381819848026305624270316466184507 

noncomputable def Ns420p1453 := nat_lit 16736949331138341316636159508480000000000000000000000000000000000 

noncomputable abbrev qz179 := qz467

noncomputable def Ns420p1454 := @Enclosure.Real.IsNear.mulLit_tf qz179 qz140 Ns420p1450 Ns420p1451 Ns420p1452 Ns420p1453 10604223278816850459 18446744073709551616 

noncomputable def Ns420p1455 := @Enclosure.Real.IsNear.mulLit_ff qz159 qz150 Ns420p1209 Ns420p1213 Ns420p1211 Ns420p1214 1686869401 4294967296 24501163 907311841280000 Ns420p1450 

noncomputable abbrev qz479 := (@HMul.hMul Real Real Real qz619 qz701 qz697)

noncomputable abbrev qz180 := qz479

noncomputable def Ns420p1456 := @Ns420p1454 260131280416005647 Ns420p1444 Ns420p1395 Ns420p1396 Ns420p1397 Ns420p1398 (@Enclosure.Real.IsNear.neg qz180 Bool.false Ns420p1450 Ns420p1451 Ns420p1452 Ns420p1453 (@Ns420p1455 Ns420p1451 Ns420p1452 Ns420p1453 RS421to432.d70 qz470 rfl)) qz477 

noncomputable def Ns420p1457 := nat_lit 3957145729205303604686295556637254719075 

noncomputable def Ns420p1458 := nat_lit 53528788903553607437841208145459544078916872810949398553521 

noncomputable def Ns420p1459 := @Enclosure.Real.IsNear.mulLit_tt qz164 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz152) Ns420p1457 Ns420p1451 Ns420p1458 Ns420p1453 Ns420p1419 

noncomputable def Ns420p1460 := @Enclosure.Real.IsNear.mulLit_ft qz318 qz179 3 1 0 1 Ns420p1450 Ns420p1451 Ns420p1452 

noncomputable def Ns420p1461 := @Ns420p1460 Ns420p1453 Ns420p1457 Ns420p1451 Ns420p1458 Ns420p1453 qz474 (@Enclosure.Real.IsNear.neg qz180 Bool.false Ns420p1450 Ns420p1451 Ns420p1452 Ns420p1453 (@Ns420p1455 Ns420p1451 Ns420p1452 Ns420p1453 RS421to432.d70 qz470 rfl)) rfl 

noncomputable def Ns420p1462 := @Ns420p1459 Ns420p1421 Ns420p1422 Ns420p1423 Ns420p1291 Ns420p1292 Ns420p1293 Ns420p1294 Ns420p1461 (Ns420p1427 (@Ns420p1431 Ns420p1432 Ns420p1419 Ns420p1421 Ns420p1422 Ns420p1423 qz478 (@Ns420p1433 Ns420p1434 Ns420p1435 Ns420p1436 Ns420p1437 Ns420p1438 Ns420p1429 Ns420p1439 Ns420p1432 Ns420p1440 Ns420p1428 Ns420p1429 Ns420p1430 Ns420p1432 (@Ns420p1441 Ns420p1435 Ns420p1436 Ns420p1437 (@Ns420p1442 Ns420p1324 4184066455 4294967296 4184911 113413980160000 Ns420p1434 Ns420p1435 Ns420p1436 Ns420p1437 qz172 (Ns420p1347 rfl) rfl)) (Ns420p1447 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns420p1463 := @Ns420p1289 Ns420p1290 Ns420p1262 Ns420p1291 Ns420p1292 Ns420p1293 Ns420p1294 Ns420p1295 Ns420p1281 Ns420p1259 Ns420p1282 Ns420p1262 (@Ns420p1300 Ns420p1301 Ns420p1259 Ns420p1302 Ns420p1262 Ns420p1303 Ns420p1288 Ns420p1259 Ns420p1290 Ns420p1262 Ns420p1364 (@Ns420p1369 Ns420p1370 Ns420p1371 Ns420p1372 Ns420p1301 Ns420p1259 Ns420p1302 Ns420p1262 Ns420p1384 (@Ns420p1386 Bool.false Ns420p1368 Ns420p1370 Ns420p1371 Ns420p1372 (BSN.iteratedDeriv_two_correction_mk qz152 qz166) (@Ns420p1387 8589934592 1505 8589934592 Ns420p1388 Ns420p1389 Ns420p1390 Ns420p1391 Ns420p1368 Ns420p1370 Ns420p1371 Ns420p1372 qz478 (@Ns420p1393 Ns420p1394 Ns420p1391 Ns420p1395 Ns420p1396 Ns420p1397 Ns420p1398 Ns420p1399 Ns420p1388 Ns420p1389 Ns420p1390 Ns420p1391 (Ns420p1449 rfl rfl) (Ns420p1456 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns420p1462 

noncomputable def Ns420p1464 := nat_lit 1365583367750910863551956131326204289903471682773787875 

noncomputable def Ns420p1465 := nat_lit 481510655836071335197686290572703560470785285995049411102088435887746206758298594269 

noncomputable def Ns420p1466 := nat_lit 71884650012048250406637885819961034670080000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1467 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz320 RSCompact.c11) qz165) qz140 Ns420p1464 Ns420p25 Ns420p1465 Ns420p1466 10604223278816850459 18446744073709551616 260131280416005647 

noncomputable def Ns420p1468 := @Enclosure.Real.IsNear.mulLit_ff qz702 qz165 Ns420p1215 Ns420p1216 Ns420p1217 Ns420p1218 1974918713 2147483648 24501163 907311841280000 Ns420p1464 

noncomputable abbrev qz480 := (Ns420p1377 (@Ns420p1378 1730560000 (Ns420p1272 rfl) (Enclosure.sfrac_false_div 10025922871 8589934592) (Ns420p1383 rfl rfl) rfl rfl) rfl)

noncomputable def Ns420p1469 := Ns420p1257 (@Ns420p1261 Ns420p1262 Ns420p1250 Ns420p1251 Ns420p1252 Ns420p1253 qz478 (@Ns420p1280 Ns420p1281 Ns420p1259 Ns420p1282 Ns420p1262 Ns420p1283 Ns420p1284 Ns420p1285 Ns420p1286 Ns420p1287 Ns420p1258 Ns420p1259 Ns420p1260 Ns420p1262 (Ns420p1463 rfl rfl) (@Ns420p1467 Ns420p1444 Ns420p1283 Ns420p1284 Ns420p1285 Ns420p1286 (@Ns420p1468 Ns420p25 Ns420p1465 Ns420p1466 RS421to432.d71 qz480 rfl) qz477 rfl) rfl rfl) rfl) 

noncomputable def Ns420p1470 := @Enclosure.Real.IsNear.of_eq qz703 (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz152) qz461)) Bool.false Ns420p1245 Ns420p1246 Ns420p1247 Ns420p1248 (BSN.correctionLinear_mk qz152) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz152) qz461) Bool.true Ns420p1245 Ns420p1246 Ns420p1247 Ns420p1248 (@Ns420p1254 Ns420p1246 Ns420p1247 Ns420p1248 Ns420p1469 RS421to432.d72 rfl)) 

noncomputable def Ns420p1471 := @Enclosure.Real.IsNear.inv_image qz147 375331833 33554432 37 33554432 1499872 1499873 16777216 qz451 rfl 

noncomputable def Ns420p1472 := @Ns420p1249 Ns420p1237 Ns420p1242 Ns420p1240 Ns420p1470 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz147) Bool.false 2999745 33554432 1 33554432 2999745 33554432 1 33554432 (Ns420p1471 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p1473 := @Ns420p1239 Ns420p1240 Ns420p1232 Ns420p1228 Ns420p1234 Ns420p1230 (Ns420p1171 qz29 (@Enclosure.Real.IsNear.of_eq qz145 (@Inv.inv Real Real.instInv (Real.sqrt qz147)) Bool.false 2508171 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz146 (BSN.t_div_two_pi_nonneg qz138 786160 1000 qz141)) Ns420p1175) rfl) (@Ns420p1243 Ns420p1244 Ns420p1236 Ns420p1237 Ns420p1238 Ns420p1240 (@Ns420p1176 140737488355328 208639406385597 5946158883012608000 qz157 (@Ns420p1177 16777216 3787967 16777216 536317 55377920000 80903948441215 140737488355328 208639406385597 5946158883012608000 (@Ns420p1178 16777216 (Ns420p1190 rfl rfl rfl rfl rfl) rfl) (Ns420p1206 rfl) rfl)) (Ns420p1472 rfl) rfl rfl) 

noncomputable def Ns420p1474 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz138) (hardyZApproximantRS qz138) Bool.true Ns420p1227 Ns420p1228 Ns420p1229 Ns420p1230 (@Eq.refl Real (hardyZApproximantRS qz138)) (Ns420p1231 (BSN.hardyZApproximantRS_eq qz138 11 (@BSN.floor_sqrt_eq_dec qz138 786160 1000 11 qz141 rfl rfl rfl)) (@Ns420p1233 Ns420p1234 Ns420p1230 Ns420p1235 Ns420p1227 Ns420p1228 Ns420p1229 Ns420p1230 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 11)) Bool.true 84746413 134217728 37837 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (Ns420p1169 (Ns420p1168 rfl) rfl rfl)) (Ns420p1473 rfl) rfl rfl)) 

theorem RS421to432.d73 : Enclosure.Real.IsNear (hardyZApproximantRS qz138) Bool.true Ns420p1227 Ns420p1228 Ns420p1229 Ns420p1230 := Ns420p1474 

theorem RS421to432.d74 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal (RS421to432.d3 a b h)) (hardyZApproximantRS b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal (RS421to432.d3 a b h)) 

noncomputable def Ns420p1475 := nat_lit 3956472988543490360151155688233223374301305844304780666185559339174134930937934108400398313269638802111656314757710981189679300683973601521325 

noncomputable def Ns420p1476 := nat_lit 97554642197374757230674913431036447054643691958280348464348654988292866838117675628759565720734124098744591597543956965482749239977758915821568 

noncomputable def Ns420p1477 := nat_lit 126116787019189167881879266550463468717878189845890055998917395614866966231256277028741628377846349728052699303253724773793888834629992746479015516257470663972436683041428386920711416825683 

noncomputable def Ns420p1478 := nat_lit 110437101986329187817940115159553927566775146150754209024783496396999153445226851432542604204730301715137731481279728458009002854108364800000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz837 := (Enclosure.sfrac Bool.false 787461 1000)

noncomputable abbrev qz710 := qz837

noncomputable abbrev qz481 := qz710

noncomputable abbrev qz181 := qz481

noncomputable abbrev qz838 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 787461 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz711 := qz838

noncomputable abbrev qz482 := qz711

noncomputable abbrev qz182 := qz482

noncomputable abbrev qz839 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 787461 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz712 := qz839

noncomputable abbrev qz483 := qz712

noncomputable abbrev qz183 := (Zeta.RiemannSiegel.correction qz483)

noncomputable abbrev qz184 := qz483

noncomputable abbrev qz840 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 787461 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz713 := qz840

noncomputable abbrev qz484 := qz713

noncomputable abbrev qz185 := qz484

noncomputable abbrev qz485 := (@HPow.hPow Real Real Real qz623 qz182 qz8)

noncomputable abbrev qz714 := (Zeta.RiemannSiegel.correctionLinear qz184)

noncomputable abbrev qz486 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) qz183 (@HMul.hMul Real Real Real qz5 qz714 (@Inv.inv Real Real.instInv qz185)))

noncomputable def Ns420p1479 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz181) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz181) qz181 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz485) qz486)) Bool.false Ns420p1475 Ns420p1476 Ns420p1477 Ns420p1478 

noncomputable def Ns420p1480 := nat_lit 16432329706296752430901989457622040052422963247324843128517970811559380301167605979637277608034366356303380411944460680574018912930004780707501 

noncomputable def Ns420p1481 := @Enclosure.Real.IsNear.subLit_tt_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz181) qz181 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz485) qz486) 8582273 67108864 151603 134217728 Ns420p1480 Ns420p1476 

noncomputable def Ns420p1482 := nat_lit 1374726324841370094964148463128134886971646100098215812319598308431689218098027488652882238068689872865570031057650396647981107065192746479015516257470663972436683041428386920711416825683 

noncomputable def Ns420p1483 := nat_lit 265514407707838652664694926524469787707607428927854700276876100456566893397963212521603587951041585700034056441816419187964746393215891404084792524800 

noncomputable def Ns420p1484 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz181) qz181 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 787461 1000 194 242 268435456 134217728 4503599627370496 Bool.false 404790998968 2563 

noncomputable def Ns420p1485 := Ns420p1484 618095470 41 84886744 8 643680110 41 80936328 8 Bool.false 137432865 130056 Bool.true 133536850 Bool.true 40886492 14148475504056880 1 Bool.false 235899947 Bool.true Bool.false 265327677 Bool.true Bool.true 17164546 

noncomputable def Ns420p1486 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz181) qz181 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 787461 1000 82 141 268435456 134217728 4503599627370496 Bool.false 404790998968 2563 

noncomputable def Ns420p1487 := Ns420p1486 558195838 41 94906264 8 589812974 41 89478488 8 Bool.false 272495868 106099 Bool.true 190544701 Bool.true 210017965 14148475504056880 1 Bool.false 203600202 Bool.true Bool.false 189238380 Bool.true Bool.false 137432865 

noncomputable def Ns420p1488 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz181) qz181 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 787461 1000 61 15 268435456 134217728 4503599627370496 Bool.false 404790998968 2563 

noncomputable def Ns420p1489 := Ns420p1488 480971758 41 109588312 8 522351262 41 101459064 8 Bool.false 301873274 78680 Bool.false 323394317 Bool.true 215386733 14148475504056880 1 Bool.false 250650362 Bool.true Bool.false 193008019 Bool.false Bool.false 272495868 

noncomputable def Ns420p1490 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz181) qz181 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 787461 1000 265 153 268435456 134217728 4503599627370496 Bool.false 404790998968 2563 

noncomputable def Ns420p1491 := Ns420p1490 372130544 40 134217720 8 432030192 40 120047984 16 Bool.false 339776575 46388 Bool.false 13490168 Bool.false 70485420 14148475504056880 1 Bool.false 13484490 Bool.true Bool.false 69678241 Bool.true Bool.false 301873274 

noncomputable def Ns420p1492 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz181) qz181 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 787461 1000 612 409 268435456 134217728 4503599627370496 Bool.false 404790998968 2563 

noncomputable def Ns420p1493 := Ns420p1492 186065264 40 189812528 16 294906480 40 154981288 8 Bool.false 268435416 2608 Bool.false 217514014 Bool.false 105759159 14148475504056880 1 Bool.false 185026937 Bool.false Bool.false 103044272 Bool.true Bool.false 339776575 

noncomputable def Ns420p1494 := nat_lit 6477174291748242034605609374537558130545446341293911461483 

noncomputable def Ns420p1495 := nat_lit 4295311009946555972095282224587900861828102644301824000 

noncomputable def Ns420p1496 := nat_lit 145340600759903286480277206384480000 

noncomputable def Ns420p1497 := nat_lit 686700458088278575787511571016550031680 

noncomputable abbrev qz715 := (@Eq.refl Real qz837)

noncomputable abbrev qz487 := qz715

noncomputable abbrev qz186 := qz487

noncomputable def Ns420p1498 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz181 787461 1000 2480380306084 16000000 1574922 4000 2000 Ns420p1496 Ns420p1497 qz186 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns420p1499 := nat_lit 18654261960234937059664154998668167415970885462926465009071040 

noncomputable abbrev qz488 := (@HMul.hMul Real Real Real qz619 qz625 (@HSub.hSub Real Real Real qz624 qz626 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 (@Nat.cast Real Real.instNatCast 1574922)))))

noncomputable abbrev qz716 := (Real.log (Enclosure.sfrac Bool.false 2480380306084 16000000))

noncomputable abbrev qz717 := (Enclosure.sfrac Bool.false 787461 2000)

noncomputable abbrev qz187 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 787461 4000) qz716) qz488) qz717)

noncomputable abbrev qz489 := (@HSub.hSub Real Real Real qz11 qz187 (@HMul.hMul Real Real Real qz5 qz717 (Real.log Real.pi)))

noncomputable def Ns420p1500 := @Enclosure.Real.IsNear.addLit_ft_p qz489 (Enclosure.sfrac Bool.true Ns420p1496 Ns420p1497) 27165067910964383323203 18014398509481984000 6606784554112507497 692224000000000000000000 Ns420p1496 Ns420p1497 0 1 Ns420p1499 

noncomputable def Ns420p1501 := nat_lit 1823016847987672909280698171392000 

noncomputable abbrev qz490 := (@HMul.hMul Real Real Real qz5 qz717 (Real.log Real.pi))

noncomputable def Ns420p1502 := @Enclosure.Real.IsNear.subLit_ff_p qz187 qz490 35284428778038091584579 18014398509481984000 2485817887459953 676000000000000000000 30246976267821 67108864000 787461 134217728000 Ns420p1501 27165067910964383323203 18014398509481984000 

noncomputable def Ns420p1503 := nat_lit 70568857556076183169158000 

noncomputable abbrev qz188 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 787461 4000) qz716) qz488)

noncomputable def Ns420p1504 := @Enclosure.Real.IsNear.subLit_ff_p qz188 qz717 42377246910375687885891 18014398509481984000 2485817887459953 676000000000000000000 787461 2000 0 1 Ns420p1503 35284428778038091584579 18014398509481984000 2485817887459953 676000000000000000000 

noncomputable def Ns420p1505 := nat_lit 95425076697277725432036838510814035968 

noncomputable def Ns420p1506 := nat_lit 57793103694484503416274944 

noncomputable def Ns420p1507 := nat_lit 966001514406875725121939107048226028866192493927537359749424653817187892039680 

noncomputable def Ns420p1508 := nat_lit 2266420644311766088014618659133255486684544613954197274290417070969379188736 

noncomputable def Ns420p1509 := nat_lit 47515656740149853436274295710083843890488450514179174356677460487434240 

noncomputable def Ns420p1510 := BSN.log_dyadic_bound 383228306084 4577532306084 4 3 Ns420p1507 134217728 54080000 Ns420p1508 Ns420p1509 22525984 4960760612168 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 383228306084) (BSN.artanhQ 4577532306084) 0 3 Ns420p1508 Ns420p1507 Ns420p1509 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns420p1511 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 787461 4000) qz716 787461 4000 0 1 53824022127766631 4503599627370496 3125002873 169000000000000000 42384318288753239013891 18014398509481984000 2460817887375453 676000000000000000000 (Enclosure.Real.IsNear.const Bool.false 787461 4000) (BSN.isNear_log_sfrac 2480380306084 16000000 53824022127766631 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2480380306084) qz335)) Bool.false Ns420p1506 Ns420p103 1000000919360000 54080000000000000000000 53824022127766631 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2480380306084 16000000 17 4960760612168 4194304000000 22525984 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns420p1510 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns420p1512 := BSN.arctan_dyadic_bound_f 1000 1574922 1 0 16777216 6760000 0 1 1 0 1 1 10652 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1574922) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1574922) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns420p1513 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1574922))) 884279719003555 562949953421312 1 2000000000000000 10652 16777216 1 6760000 14829755307238103187456 883922297193891 562949953421312 50000000169 338000000000000000 qz16 (Ns420p1512 rfl) rfl rfl 

noncomputable abbrev qz189 := qz488

noncomputable def Ns420p1514 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 787461 4000) qz716) qz189 42384318288753239013891 18014398509481984000 2460817887375453 676000000000000000000 883922297193891 2251799813685248 50000000169 1352000000000000000 Ns420p1505 42377246910375687885891 18014398509481984000 2485817887459953 676000000000000000000 (Ns420p1511 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1574922)))) 1 4 0 1 883922297193891 562949953421312 50000000169 338000000000000000 883922297193891 2251799813685248 50000000169 1352000000000000000 qz340 Ns420p1513 rfl) 

noncomputable def Ns420p1515 := @Ns420p1500 Ns420p1494 Ns420p1495 6606784554112507497 692224000000000000000000 (@Ns420p1502 6606784554112507497 692224000000000000000000 (Ns420p1504 (Ns420p1514 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 787461 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz717 (Real.log Real.pi) 787461 2000 0 1 38410761 33554432 1 67108864 30246976267821 67108864000 787461 134217728000 (Enclosure.Real.IsNear.const Bool.false 787461 2000) RS421to432.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns420p1496 Ns420p1497) 

noncomputable def Ns420p1516 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz181) Bool.false Ns420p1494 Ns420p1495 6606784554112507497 692224000000000000000000 50598874871 33554432 321 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz181) (@HAdd.hAdd Real Real Real qz341 qz489 (Enclosure.sfrac Bool.true Ns420p1496 Ns420p1497)) Bool.false Ns420p1494 Ns420p1495 6606784554112507497 692224000000000000000000 Ns420p1498 (Ns420p1515 rfl rfl)) 

noncomputable def Ns420p1517 := nat_lit 7593524026365409568489472 

noncomputable def Ns420p1518 := nat_lit 3506426862657499819592112677849091760272396419856809416657437493846804404087800303848126954503988728049305557807522737993658860861188540625 

noncomputable def Ns420p1519 := nat_lit 2493232908109662257035362974296732673879202577905158815559145589924417797209047437999676463608220273591657345148473275291406494140625 

noncomputable def Ns420p1520 := nat_lit 17510375732733731828438104084281585844536801531639870439955228573138173828478990264727224310373981099415460475569258140898555641335966140625 

noncomputable def Ns420p1521 := BSN.sin_dyadic_bound_f 107910466715 68719476736 4 3 33554432 13533204 Ns420p1518 Ns420p522 Ns420p1519 Ns420p1520 Ns420p525 Ns420p1519 33554427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107910466715) qz659 0 3 Ns420p1518 Ns420p522 Ns420p1519 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107910466715) qz660 0 3 Ns420p1520 Ns420p525 Ns420p1519 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1522 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz181) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50598874871) qz342) Bool.false 50598874871 33554432 321 33554432 Bool.false 33554427 33554432 1 6760000 (Ns420p1516 rfl) (Enclosure.sfrac_false_div 50598874871 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50598874871) qz342) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns420p1517) qz343) 226375608064910080 72057594037927936 Bool.false 33554427 33554432 239 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q3 50598874871 33554432 226375608064910080 72057594037927936 239 Ns420p1517 Ns420p103 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554427 33554432 Ns420p1517 Ns420p103 107910466715 68719476736 13533204 13520000 (Ns420p1521 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns420p1523 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz181) Bool.false Ns420p1494 Ns420p1495 6606784554112507497 692224000000000000000000 404790998968 268435456 2563 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz181) (@HAdd.hAdd Real Real Real qz341 qz489 (Enclosure.sfrac Bool.true Ns420p1496 Ns420p1497)) Bool.false Ns420p1494 Ns420p1495 6606784554112507497 692224000000000000000000 Ns420p1498 (Ns420p1515 rfl rfl)) 

noncomputable def Ns420p1524 := Ns420p1493 46388 BSN.abs_quadSignPos (BSN.cos_quad_nat0 612 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 185026937 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 409 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 103044272 268435456) qz186 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz181) qz181 1) Bool.false 33554427 33554432 34429913 3544186880000 268435416 268435456 2608 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz181) qz181 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz181)) Bool.false 33554427 33554432 34429913 3544186880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz181) qz181) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz181)) Bool.false 33554427 33554432 2203514432 226827960320000 33554427 33554432 34429913 3544186880000 (Ns420p1522 rfl rfl) rfl)) rfl) (Ns420p1523 rfl) RS421to432.d7 

noncomputable def Ns420p1525 := nat_lit 19531212245540395528147700617302020797329269107158220391025941195489536 

noncomputable def Ns420p1526 := nat_lit 5010694715254540107423537868574490177284924958548558699254316237056 

noncomputable def Ns420p1527 := nat_lit 58583615347190677504228254776168913411633237471557564055679314953994496 

noncomputable def Ns420p1528 := BSN.cos_dyadic_bound_f 217514014 268435456 3 2 268435456 134217728 Ns420p1525 Ns420p156 Ns420p1526 Ns420p1527 Ns420p159 Ns420p1526 185026937 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 217514014) qz346 0 2 Ns420p1525 Ns420p156 Ns420p1526 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 217514014) qz347 0 2 Ns420p1527 Ns420p159 Ns420p1526 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1529 := nat_lit 125104218566103558691076130572961 

noncomputable def Ns420p1530 := BSN.sin_dyadic_bound_f 105759159 268435456 2 1 268435456 134217728 Ns420p1529 Ns420p133 Ns420p1529 Ns420p1529 Ns420p134 Ns420p1529 103044272 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 105759159) qz344 0 1 Ns420p1529 Ns420p133 Ns420p1529 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 105759159) qz345 0 1 Ns420p1529 Ns420p134 Ns420p1529 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1531 := nat_lit 33118406527388421913659314176 

noncomputable def Ns420p1532 := BSN.sin_dyadic_bound_f 13490168 268435456 2 1 268435456 134217728 Ns420p1531 Ns420p133 Ns420p1531 Ns420p1531 Ns420p134 Ns420p1531 13484490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 13490168) qz344 0 1 Ns420p1531 Ns420p133 Ns420p1531 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 13490168) qz345 0 1 Ns420p1531 Ns420p134 Ns420p1531 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1533 := nat_lit 24682955919883137165541836960000 

noncomputable def Ns420p1534 := BSN.sin_dyadic_bound_f 70485420 268435456 2 1 268435456 134217728 Ns420p1533 Ns420p133 Ns420p1533 Ns420p1533 Ns420p134 Ns420p1533 69678241 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 70485420) qz344 0 1 Ns420p1533 Ns420p133 Ns420p1533 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 70485420) qz345 0 1 Ns420p1533 Ns420p134 Ns420p1533 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1535 := Ns420p1491 78680 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 265 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 13484490 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 153 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 69678241 268435456) qz186 rfl rfl (Ns420p1524 RS421to432.d9 RS421to432.d11 RS421to432.d13 RS421to432.d17 (Ns420p1528 rfl rfl) (Ns420p1530 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns420p1523 rfl) RS421to432.d19 RS421to432.d21 RS421to432.d23 RS421to432.d25 RS421to432.d17 (Ns420p1532 rfl rfl) (Ns420p1534 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns420p1536 := nat_lit 171859389178258500160509217256996166845044253315327019168622630984763425 

noncomputable def Ns420p1537 := nat_lit 119635224895700263296216746504252929045349946256146010596007812548641 

noncomputable def Ns420p1538 := nat_lit 449914228912274461898854075226364027470947239722394147138760973263587361 

noncomputable def Ns420p1539 := BSN.sin_dyadic_bound_f 323394317 268435456 3 2 268435456 134217728 Ns420p1536 Ns420p119 Ns420p1537 Ns420p1538 Ns420p122 Ns420p1537 250650362 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 323394317) qz344 0 2 Ns420p1536 Ns420p119 Ns420p1537 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 323394317) qz345 0 2 Ns420p1538 Ns420p122 Ns420p1537 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1540 := nat_lit 33796880831732333110402074997479098608717424342389451062378028348161825 

noncomputable def Ns420p1541 := nat_lit 4631819120919152323583141079115555319567534743667372787478485745441 

noncomputable def Ns420p1542 := nat_lit 88508141137865098566338680860221928314218716316673100845524632887312161 

noncomputable def Ns420p1543 := BSN.sin_dyadic_bound_f 215386733 268435456 3 2 268435456 134217728 Ns420p1540 Ns420p119 Ns420p1541 Ns420p1542 Ns420p122 Ns420p1541 193008019 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 215386733) qz344 0 2 Ns420p1540 Ns420p119 Ns420p1541 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 215386733) qz345 0 2 Ns420p1542 Ns420p122 Ns420p1541 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1544 := Ns420p1489 106099 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 250650362 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 193008019 268435456) qz186 rfl rfl (Ns420p1535 rfl rfl) (Ns420p1523 rfl) RS421to432.d27 RS421to432.d29 RS421to432.d31 RS421to432.d33 RS421to432.d17 (Ns420p1539 rfl rfl) (Ns420p1543 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p1545 := nat_lit 11500637742160763008702195358734179409058472095953166678037590216702881 

noncomputable def Ns420p1546 := nat_lit 1737700816779083140615394256220195775350399113215394089182958877601 

noncomputable def Ns420p1547 := nat_lit 34498437824848730859825355287690097835624715489633069245934404732353441 

noncomputable def Ns420p1548 := BSN.cos_dyadic_bound_f 190544701 268435456 3 2 268435456 134217728 Ns420p1545 Ns420p156 Ns420p1546 Ns420p1547 Ns420p159 Ns420p1546 203600202 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 190544701) qz346 0 2 Ns420p1545 Ns420p156 Ns420p1546 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 190544701) qz347 0 2 Ns420p1547 Ns420p159 Ns420p1546 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1549 := nat_lit 30550680797761577822532994448129592571327382111786661916382911714830625 

noncomputable def Ns420p1550 := nat_lit 3784875235731109035361183359347581159170753107930870764393125390625 

noncomputable def Ns420p1551 := nat_lit 80007559910422472501529162591090941603028295740123655037860513240590625 

noncomputable def Ns420p1552 := BSN.sin_dyadic_bound_f 210017965 268435456 3 2 268435456 134217728 Ns420p1549 Ns420p119 Ns420p1550 Ns420p1551 Ns420p122 Ns420p1550 189238380 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 210017965) qz344 0 2 Ns420p1549 Ns420p119 Ns420p1550 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 210017965) qz345 0 2 Ns420p1551 Ns420p122 Ns420p1550 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1553 := Ns420p1487 130056 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 82 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 203600202 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 141 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 189238380 268435456) qz186 rfl rfl (Ns420p1544 rfl) (Ns420p1523 rfl) RS421to432.d35 RS421to432.d37 RS421to432.d39 RS421to432.d41 RS421to432.d17 (Ns420p1548 rfl rfl) (Ns420p1552 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p1554 := nat_lit 2773889374756027088385342522230300404736220541941287726830550500000000 

noncomputable def Ns420p1555 := nat_lit 101113471135014970466593126774906574738131293584325039062500000000 

noncomputable def Ns420p1556 := nat_lit 8321465897325811235215094380437351401059185363236694530413526500000000 

noncomputable def Ns420p1557 := BSN.cos_dyadic_bound_f 133536850 268435456 3 2 268435456 134217728 Ns420p1554 Ns420p156 Ns420p1555 Ns420p1556 Ns420p159 Ns420p1555 235899947 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 133536850) qz346 0 2 Ns420p1554 Ns420p156 Ns420p1555 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 133536850) qz347 0 2 Ns420p1556 Ns420p159 Ns420p1555 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1558 := nat_lit 2794598369543411052369548452096 

noncomputable def Ns420p1559 := BSN.cos_dyadic_bound_f 40886492 268435456 2 1 268435456 134217728 Ns420p1558 Ns420p285 Ns420p1558 Ns420p1558 Ns420p286 Ns420p1558 265327677 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 40886492) qz346 0 1 Ns420p1558 Ns420p285 Ns420p1558 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 40886492) qz347 0 1 Ns420p1558 Ns420p286 Ns420p1558 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1560 := Ns420p1485 151603 BSN.abs_quadSignNeg qz651 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 235899947 268435456) BSN.abs_quadSignNeg qz348 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 265327677 268435456) qz186 rfl rfl (Ns420p1553 rfl) (Ns420p1523 rfl) RS421to432.d43 RS421to432.d45 RS421to432.d47 RS421to432.d49 RS421to432.d17 (Ns420p1557 rfl rfl) (Ns420p1559 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p1561 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz181) qz181 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz181) qz181 11) 17164546 268435456 151603 268435456 17164546 268435456 151603 268435456 9215145465085952 8582273 67108864 151603 134217728 (Ns420p1560 rfl) 

noncomputable def Ns420p1562 := nat_lit 3277113714141932239954017117474559113685955669176273376741050552245876777087070115232604714273280184270804061757448728932177135476777329 

noncomputable def Ns420p1563 := nat_lit 5814709794364855124394590463104036274829130885498544482251921593445114304907183386609528405710108524486100172850129423468276813028917248 

noncomputable def Ns420p1564 := nat_lit 1367114710472285718878702865377712700583887774501581842828383360822217905348101806840833602119021770342390950324034870959404830549834960008942081450866382513373092968363851685602027 

noncomputable def Ns420p1565 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz485) qz486 5014269 16777216 1 16777216 Ns420p1562 Ns420p1563 Ns420p1564 

noncomputable def Ns420p1566 := nat_lit 32912821169593688195329938876495935787789567157850923843617289184629664851792708466214717687586039815884152496242442267539800064000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1567 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz485 1 1 0 1 5014269 16777216 1 16777216 5014269 16777216 1 16777216 

noncomputable def Ns420p1568 := @Enclosure.Real.IsNear.sqrt_image qz182 4205319713733 33554432000 787461 33554432000 187821116 187821153 16777216 (@Enclosure.Real.IsNear.of_eq qz182 (@HMul.hMul Real Real Real qz5 qz181 qz3) Bool.false 4205319713733 33554432000 787461 33554432000 (BSN.t_div_two_pi_mk qz181 787461 1000 qz186) (@Enclosure.Real.IsNear.mulLit_ff qz181 qz3 787461 1000 0 1 5340353 33554432 1 33554432 4205319713733 33554432000 787461 33554432000 (Enclosure.Real.IsNear.const Bool.false 787461 1000) RS421to432.d52 rfl)) 

noncomputable abbrev qz491 := (@Enclosure.Real.IsNear.recentre' qz185 Bool.false 375642269 33554432 37 33554432 375642269 33554432 37 33554432 (Ns420p1568 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns420p1569 := @Enclosure.Real.IsNear.sqrt_image qz185 375642269 33554432 37 33554432 56134796 56134803 16777216 qz491 rfl 

noncomputable def Ns420p1570 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz185) 112269599 33554432 7 33554432 5014268 5014270 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz185) Bool.false 112269599 33554432 7 33554432 112269599 33554432 7 33554432 (Ns420p1569 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p1571 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz185)) Bool.false 10028538 33554432 2 33554432 5014269 16777216 1 16777216 (Ns420p1570 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns420p1572 := nat_lit 5047964824248060840051928090996811887076982765314916597183877733561349233995702427674232880490132660775199995839501124681377451975025 

noncomputable def Ns420p1573 := nat_lit 24754817214672815022816399757721036842582196517214111250465203809868748984970720114885450675040731439543018673461677784980868949834960008942081450866382513373092968363851685602027 

noncomputable abbrev qz492 := (@HMul.hMul Real Real Real qz5 qz714 (@Inv.inv Real Real.instInv qz185))

noncomputable def Ns420p1574 := @Enclosure.Real.IsNear.addLit_ff qz183 qz492 39598048017697 70368744177664 606289959341713 14865397207531520000 Ns420p1572 Ns420p1563 Ns420p1573 Ns420p1566 

noncomputable def Ns420p1575 := nat_lit 230606376591567940367983051790375673942833981253515500130439973807370733296596554373250886544575083283873088354258232527429137186024980406750943379456 

noncomputable abbrev qz841 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 787461 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1)))

noncomputable abbrev qz718 := (Real.cos qz841)

noncomputable abbrev qz493 := qz718

noncomputable abbrev qz190 := (@Inv.inv Real Real.instInv qz493)

noncomputable abbrev qz719 := (@HSub.hSub Real Real Real qz798 (@HMul.hMul Real Real Real qz795 qz839 qz839) qz839)

noncomputable abbrev qz494 := (@HMul.hMul Real Real Real qz619 qz617 (@HSub.hSub Real Real Real qz624 qz719 qz634))

noncomputable abbrev qz191 := (Real.cos qz494)

noncomputable def Ns420p1576 := @Enclosure.Real.IsNear.of_eq qz183 (@HMul.hMul Real Real Real qz5 qz190 qz191) Bool.false 39598048017697 

noncomputable def Ns420p1577 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz191 49538987 16777216 521 

noncomputable def Ns420p1578 := @Enclosure.Real.IsNear.recentre' qz190 Bool.false 99077974 33554432 2084 33554432 49538987 16777216 521 

noncomputable abbrev qz192 := qz493

noncomputable def Ns420p1579 := @Enclosure.Real.IsNear.recentre' qz192 Bool.false 5681888 16777216 807697216 113413980160000 177559 524288 12620269 1772093440000 

noncomputable abbrev qz720 := qz841

noncomputable abbrev qz495 := qz720

noncomputable abbrev qz193 := qz495

noncomputable def Ns420p1580 := @Enclosure.Real.IsNear.cos_image qz193 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41114129) qz342) Bool.false 41114129 33554432 117 16777216 Bool.false 5681888 16777216 1 

noncomputable def Ns420p1581 := nat_lit 998484790190838064872891843 

noncomputable def Ns420p1582 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz184 884279719003555 140737488355328 1 500000000000000 6543517 33554432 37 33554432 5786299374054985202935 4722366482869645213696 Ns420p1581 

noncomputable def Ns420p1583 := @Enclosure.Real.IsNear.subLit_ff_p qz185 qz1 375642269 33554432 37 33554432 11 1 0 1 6543517 6543517 33554432 37 

noncomputable def Ns420p1584 := @Ns420p1583 33554432 qz491 qz352 

noncomputable def Ns420p1585 := @Enclosure.Real.IsNear.recentre' qz193 Bool.false 5786299374054985202935 4722366482869645213696 Ns420p1581 Ns420p175 41114129 33554432 117 16777216 (@Ns420p1582 Ns420p175 RS421to432.d51 (Ns420p1584 rfl rfl) rfl) 

noncomputable def Ns420p1586 := nat_lit 6093341621433496267492396838650629579628138833574788236312538241 

noncomputable def Ns420p1587 := nat_lit 8164484211819896463397413874701647035739499320307984021548161 

noncomputable def Ns420p1588 := nat_lit 18263695895876849009550395688202485444812937502083748740894518401 

noncomputable def Ns420p1589 := BSN.cos_dyadic_bound_f 41114129 33554432 3 2 16777216 6760000 Ns420p1586 Ns420p181 Ns420p1587 Ns420p1588 Ns420p184 Ns420p1587 5681888 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 41114129) qz635 0 2 Ns420p1586 Ns420p181 Ns420p1587 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 41114129) (BSN.cosOddQ 33554432) 0 2 Ns420p1588 Ns420p184 Ns420p1587 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1590 := @Enclosure.Real.IsNear.inv_image qz192 177559 524288 12620269 1772093440000 49537945 49540029 16777216 (Ns420p1579 (@Ns420p1580 6760000 (Ns420p1585 rfl) (Enclosure.sfrac_false_div 41114129 33554432) (Ns420p1589 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns420p1591 := @Enclosure.Real.IsNear.recentre' qz191 Bool.false 3197324 16777216 

noncomputable abbrev qz194 := qz494

noncomputable def Ns420p1592 := @Enclosure.Real.IsNear.cos_image qz194 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 46273175)) qz342) Bool.true 46273175 33554432 

noncomputable def Ns420p1593 := nat_lit 218518893885210179524702631045 

noncomputable def Ns420p1594 := nat_lit 9314166267328280695130035408127097 

noncomputable def Ns420p1595 := @Enclosure.Real.IsNear.recentre' qz194 Bool.true Ns420p1593 Ns420p190 Ns420p1594 

noncomputable def Ns420p1596 := nat_lit 967140655691703339764940800000000000000 

noncomputable abbrev qz496 := (@HSub.hSub Real Real Real qz624 qz719 qz634)

noncomputable abbrev qz195 := qz496

noncomputable def Ns420p1597 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz195 884279719003555 140737488355328 1 500000000000000 247115125665719 

noncomputable abbrev qz497 := qz719

noncomputable abbrev qz196 := qz497

noncomputable def Ns420p1598 := @Enclosure.Real.IsNear.subLit_tf qz196 qz27 176746381488055 1125899906842624 1725735611 1125899906842624 1 16 

noncomputable abbrev qz721 := (@HMul.hMul Real Real Real qz795 qz839 qz839)

noncomputable abbrev qz498 := qz721

noncomputable abbrev qz197 := qz498

noncomputable def Ns420p1599 := @Enclosure.Real.IsNear.subLit_ff_n qz197 qz184 42817614729289 1125899906842624 484221627 1125899906842624 6543517 33554432 37 33554432 

noncomputable def Ns420p1600 := @Enclosure.Real.IsNear.mulLit_ff qz184 qz184 6543517 33554432 37 33554432 6543517 33554432 37 33554432 42817614729289 1125899906842624 

noncomputable def Ns420p1601 := nat_lit 147358872774120263248573626439570565465969997651906442017310806057092811874026515093656119150390625 

noncomputable def Ns420p1602 := nat_lit 96372159746031730972756632773307619833958881006493292481142176916803287715971469879150390625 

noncomputable def Ns420p1603 := nat_lit 892696380491309892670315770458365516808125400912554604026179905558390721493135477899399735150390625 

noncomputable def Ns420p1604 := BSN.cos_dyadic_bound_f 46273175 33554432 4 3 16777216 6760000 Ns420p1601 Ns420p1201 Ns420p1602 Ns420p1603 Ns420p1204 Ns420p1602 3197324 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 46273175) qz635 0 3 Ns420p1601 Ns420p1201 Ns420p1602 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 46273175) (BSN.cosOddQ 33554432) 0 3 Ns420p1603 Ns420p1204 Ns420p1602 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1605 := @Ns420p1591 555948608 56706990080000 799331 4194304 8686697 886046720000 (@Ns420p1592 81 8388608 Bool.false 3197324 16777216 1 6760000 (@Ns420p1595 Ns420p1596 46273175 33554432 81 8388608 (@Ns420p1597 1125899906842624 1725735611 1125899906842624 Ns420p1593 Ns420p190 Ns420p1594 Ns420p1596 RS421to432.d51 (@Ns420p1598 0 1 3953842010651504 247115125665719 1125899906842624 1725735611 1125899906842624 (@Ns420p1599 5930624438887000309760 176746381488055 1125899906842624 1725735611 1125899906842624 (@Ns420p1600 484221627 1125899906842624 (Ns420p1584 rfl rfl) (Ns420p1584 rfl rfl) rfl) (Ns420p1584 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 46273175 33554432) (BSN.cos_neg_of_bound 46273175 33554432 Bool.false 3197324 16777216 1 6760000 (Ns420p1604 rfl rfl)) rfl rfl) 

noncomputable def Ns420p1606 := nat_lit 3368379599440330514576903145064076319603920883441720953151223637515888969477985889590201790892188188018814476819542292663632425 

noncomputable def Ns420p1607 := nat_lit 346583711765101857447301773017885462929554634421977071896309947576827663475703202879996800763017447262173901370175446478621769728 

noncomputable def Ns420p1608 := nat_lit 16505531891236397184800998068258639031710223490239052529275796806998026386998081822812787166992585846080793424952840393125141845254991210341077418041150530432871499348892003 

noncomputable def Ns420p1609 := nat_lit 1961757014369588386734124355107303606736038157811815967775421690024713567006153372896594863390090454571494608893540040704000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1610 := @Enclosure.Real.IsNear.mulLit_ff qz714 (@Inv.inv Real Real.instInv qz185) Ns420p1606 Ns420p1607 Ns420p1608 Ns420p1609 1498633 16777216 1 16777216 Ns420p1572 

noncomputable def Ns420p1611 := nat_lit 371537029170458426413228927721808841651393143624652338566571771145733753068225272280714646261955508162339245542696992275 

noncomputable def Ns420p1612 := nat_lit 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584 

noncomputable def Ns420p1613 := nat_lit 1820351324492038674087996189042791682403152725694547904335986912005830298342041628168575083335082091102679064424597761160957356189000786048648722342196555600184801421 

noncomputable def Ns420p1614 := nat_lit 228378574174082417359357275430497667605061800895703021410785346527666967246466476108948102149890090172585869312000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1615 := @Enclosure.Real.IsNear.mulLit_tf (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz184) qz461 Ns420p1611 Ns420p1612 Ns420p1613 Ns420p1614 9066067 8589934592 1 8589934592 Ns420p1606 

noncomputable abbrev qz842 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 787461 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1)))

noncomputable abbrev qz722 := (@HMul.hMul Real Real Real qz795 qz793 (@HSub.hSub Real Real Real qz798 qz842 qz836))

noncomputable abbrev qz499 := (@HMul.hMul Real Real Real qz619 qz722 qz722)

noncomputable abbrev qz500 := qz722

noncomputable abbrev qz198 := (@HMul.hMul Real Real Real qz326 qz499 qz500)

noncomputable abbrev qz199 := (Real.sin qz494)

noncomputable abbrev qz200 := (@HMul.hMul Real Real Real qz326 qz318 qz500)

noncomputable def Ns420p1616 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz198 qz199) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz200 qz158) qz191) 

noncomputable abbrev qz723 := (Real.sin qz841)

noncomputable abbrev qz501 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz619 qz617 qz723))

noncomputable abbrev qz201 := (@HMul.hMul Real Real Real qz326 qz318 qz501)

noncomputable abbrev qz502 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz619 qz701 qz718))

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz326 qz318 qz502)

noncomputable abbrev qz503 := qz723

noncomputable abbrev qz203 := qz503

noncomputable def Ns420p1617 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns420p1616 (@HMul.hMul Real Real Real qz5 qz201 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz184))) (@HMul.hMul Real Real Real qz5 qz202 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz184))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz469 qz203) qz183) 

noncomputable abbrev qz724 := (BSN.cos_two_pi_p_ne_zero_mk qz181 787461 1000 11 qz186 rfl rfl (@BSN.floor_sqrt_eq_dec qz181 787461 1000 11 qz186 rfl rfl rfl))

noncomputable abbrev qz504 := qz724

noncomputable def Ns420p1618 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz184) (@HMul.hMul Real Real Real qz5 qz190 Ns420p1617) Bool.true Ns420p1611 Ns420p1612 Ns420p1613 Ns420p1614 (BSN.iteratedDeriv_three_correction_mk qz184 qz504) 

noncomputable def Ns420p1619 := nat_lit 14648034775231549899809565486573672398639327154492470030663382424811914317037866446937669230981972932371279075 

noncomputable def Ns420p1620 := nat_lit 4697085165547666455778961193578674054751365097816639741414581943064418050229216886927397996769537406063869952 

noncomputable def Ns420p1621 := nat_lit 717616505509477988521890688715424474475032182008055806575616918006733444660642494250537016900462801014415393272269183700336253763509393138189670992740943667 

noncomputable def Ns420p1622 := @Enclosure.Real.IsNear.mulLit_ft qz190 Ns420p1617 25364291857 8589934592 2023 8589934592 Ns420p1619 Ns420p1620 Ns420p1621 

noncomputable def Ns420p1623 := nat_lit 265867652108523083570596384152883742476186948939812161739432889185458150746378204912119663960638095360000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1624 := @Enclosure.Real.IsNear.recentre' qz190 Bool.false 25364291857 8589934592 2023 8589934592 25364291857 8589934592 2023 

noncomputable def Ns420p1625 := @Enclosure.Real.IsNear.recentre' qz192 Bool.false 1454544379 4294967296 401427054592 14865397207531520000 1454544379 4294967296 24501163 907311841280000 

noncomputable def Ns420p1626 := @Enclosure.Real.IsNear.cos_image qz193 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2631314481) qz709) Bool.false 2631314481 2147483648 227 8589934592 Bool.false 1454544379 4294967296 1 

noncomputable def Ns420p1627 := nat_lit 242874682278746825930621951 

noncomputable def Ns420p1628 := nat_lit 9223372036854775808000000000000000 

noncomputable def Ns420p1629 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz184 884279719003555 140737488355328 1 500000000000000 837573413 4294967296 9 2147483648 740649182292488520483215 604462909807314587353088 Ns420p1627 

noncomputable def Ns420p1630 := @Enclosure.Real.IsNear.subLit_ff_p qz185 qz1 48082213669 4294967296 9 2147483648 11 1 0 1 837573413 837573413 4294967296 9 

noncomputable def Ns420p1631 := @Enclosure.Real.IsNear.sqrt_image qz182 1076561990821011 8589934592000 787461 8589934592000 48082213651 48082213687 4294967296 (@Enclosure.Real.IsNear.of_eq qz182 (@HMul.hMul Real Real Real qz5 qz181 qz3) Bool.false 1076561990821011 8589934592000 787461 8589934592000 (BSN.t_div_two_pi_mk qz181 787461 1000 qz186) (@Enclosure.Real.IsNear.mulLit_ff qz181 qz3 787461 1000 0 1 1367130551 8589934592 1 8589934592 1076561990821011 8589934592000 787461 8589934592000 (Enclosure.Real.IsNear.const Bool.false 787461 1000) RS421to432.d67 rfl)) 

noncomputable def Ns420p1632 := @Ns420p1630 2147483648 (@Enclosure.Real.IsNear.recentre' qz185 Bool.false 96164427338 8589934592 36 8589934592 48082213669 4294967296 9 2147483648 (Ns420p1631 rfl rfl rfl rfl rfl rfl) rfl) qz352 

noncomputable def Ns420p1633 := @Enclosure.Real.IsNear.recentre' qz193 Bool.false 740649182292488520483215 604462909807314587353088 Ns420p1627 Ns420p1628 2631314481 2147483648 227 8589934592 (@Ns420p1629 Ns420p1628 RS421to432.d66 (Ns420p1632 rfl rfl) rfl) 

noncomputable def Ns420p1634 := nat_lit 433349292847496037402143387232674542120162757758130915063606910471334035565689382390740339590939145417923671166379467841 

noncomputable def Ns420p1635 := nat_lit 110172465804516466481952378369122567225583138613931963354466792362052020363189141816494953096032479049431549060161 

noncomputable def Ns420p1636 := nat_lit 2626636726038807846034985463123480649833225276723326249022804544733219576271847059339021269112473649689097498866337817665 

noncomputable def Ns420p1637 := BSN.cos_dyadic_bound_f 2631314481 2147483648 4 3 4294967296 1730560000 Ns420p1634 Ns420p1359 Ns420p1635 Ns420p1636 Ns420p1361 Ns420p1635 1454544379 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 2631314481) (BSN.cosEvenQ 2147483648) 0 3 Ns420p1634 Ns420p1359 Ns420p1635 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 2631314481) (BSN.cosOddQ 2147483648) 0 3 Ns420p1636 Ns420p1361 Ns420p1635 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz505 := (Ns420p1625 (@Ns420p1626 1730560000 (Ns420p1633 rfl) (Enclosure.sfrac_false_div 2631314481 2147483648) (Ns420p1637 rfl rfl) rfl rfl) rfl)

noncomputable def Ns420p1638 := @Enclosure.Real.IsNear.inv_image qz192 1454544379 4294967296 24501163 907311841280000 12682144917 12682146940 4294967296 qz505 rfl 

noncomputable def Ns420p1639 := @Enclosure.Real.IsNear.subLit_ff_n (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns420p1616 (@HMul.hMul Real Real Real qz5 qz201 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz184))) (@HMul.hMul Real Real Real qz5 qz202 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz184))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz469 qz203) qz183) 

noncomputable def Ns420p1640 := nat_lit 602242861836656969947268618262097502265790637169764749166350976602524285246084454018403030719733666796592304925 

noncomputable def Ns420p1641 := nat_lit 707004512807953690749786425362889170186070007005494748754462214832127926506844593608800383275292313555808737066416230406299948469280514445792936643428943667 

noncomputable def Ns420p1642 := nat_lit 14503035280819415519473851551590519599581421855774496405708001340361071375 

noncomputable def Ns420p1643 := nat_lit 559054373574444926245214793743926370286558381426557624542263744481977972513862906368291603184176092108248409 

noncomputable def Ns420p1644 := nat_lit 14006273645654608538743279821580793789867138581979475759595520000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1645 := nat_lit 1617552327961847786804966425165601974310656501964312517225169412603832687217344126244631706734098242123833183472372450543024147458973336951004506906659121056327637458130681672499200 

noncomputable def Ns420p1646 := nat_lit 844563589089633510545011810168940519969111355211366399750538629097618010644813140401496766412929658693934256925 

noncomputable def Ns420p1647 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 Ns420p1616 (@HMul.hMul Real Real Real qz5 qz201 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz184))) (@HMul.hMul Real Real Real qz5 qz202 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz184)) Ns420p1646 Ns420p1620 

noncomputable def Ns420p1648 := nat_lit 666857760432718722065514780260798812194307681732896978819590169093534968404863466688050027632321420166108696489525104754605182371071534563158651768046159667 

noncomputable def Ns420p1649 := nat_lit 210179727140755637051480052198938594610576958665594570784148191213471760194494193637373392625 

noncomputable def Ns420p1650 := nat_lit 824183595615949601836972585974760582751708770699749214651443216864006946806978153317000134936786997183839835855809931967584156563569 

noncomputable def Ns420p1651 := nat_lit 5458069320893368631994641040808592498216154701308358059284474820387218411759861760000000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1652 := nat_lit 2453580752103819082385177318346720230101656382145132787572243209568652415961757850506907113953448495332626180483061793204505188215782255501803326586756774305262819079460078143968971101500863030073753600 

noncomputable def Ns420p1653 := nat_lit 2454385120157332980559459120287694161129159737225878283208549989621021567833168875 

noncomputable def Ns420p1654 := nat_lit 29642774844752946028434172162224104410437116074403984394101141506025761187823616 

noncomputable def Ns420p1655 := nat_lit 7215495401001507845003130048073593626940639088313505951526305493026586608995966281795452371830891332567202503513 

noncomputable def Ns420p1656 := nat_lit 711911091679446582077925867141612122475730844907711992079142208143360000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1657 := @Enclosure.Real.IsNear.subLit_ft Ns420p1616 (@HMul.hMul Real Real Real qz5 qz201 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz184)) Ns420p1653 Ns420p1654 Ns420p1655 Ns420p1656 

noncomputable def Ns420p1658 := nat_lit 455650742744798748767273212940427535374815524803907975648353505751331373308196403968545148351997424940932272925 

noncomputable def Ns420p1659 := nat_lit 664163088522861889211869744428351782679288634583772508372096505473287880693907764529582259633518848762368164048023535315104604541963769342801212280046159667 

noncomputable def Ns420p1660 := nat_lit 25035208313460451887728234503510132411423012162354138780000079648592933099315272891647264851210139413704934668365864972578862264355734126674154596137571730986434893181797518983214326926540800 

noncomputable def Ns420p1661 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz5 qz198 qz199) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz200 qz158) qz191) 

noncomputable def Ns420p1662 := nat_lit 1638175279909153934974748685752800424161673119090148547942253936683455929865296875 

noncomputable def Ns420p1663 := nat_lit 3114715905529296521091989366440452252756915211573265470262950538662821001645178731283521271859307332567202503513 

noncomputable def Ns420p1664 := nat_lit 2515140755579984206601795050285424088318397483875 

noncomputable def Ns420p1665 := nat_lit 91343852333181432387730302044767688728495783936 

noncomputable def Ns420p1666 := nat_lit 103518227997119126631088044414282213827348847259546536316892809058313 

noncomputable def Ns420p1667 := nat_lit 17971162503012062601659471454990258667520000000000000000000000000000000000 

noncomputable def Ns420p1668 := nat_lit 224192991984409190456093862820024236864294732146039455332768057303481429914057884368392367614684635377587160851099160456200192000 

noncomputable def Ns420p1669 := nat_lit 1554152388665146399891692942513976100016049146339840090961821069636140625 

noncomputable def Ns420p1670 := nat_lit 27606985387162255149739023449108101809804435888681546220650096895197184 

noncomputable def Ns420p1671 := @Enclosure.Real.IsNear.mulLit_tt qz198 qz199 Ns420p1669 Ns420p1670 

noncomputable def Ns420p1672 := nat_lit 910470837910260003034108433875299101820766374760240999843462945519904462769266681798179524147663 

noncomputable def Ns420p1673 := nat_lit 392318858461667547739736838950479151006397215279002157056000000000000000000000000000000000000000000000 

noncomputable def Ns420p1674 := nat_lit 1341721565246139259895608717602484684524727430625 

noncomputable def Ns420p1675 := nat_lit 2146364743237217347566552224926293690576349858617852545827761 

noncomputable def Ns420p1676 := nat_lit 5316911983139663491615228241121378304000000000000000000000000000000 

noncomputable abbrev qz204 := qz499

noncomputable abbrev qz205 := qz500

noncomputable def Ns420p1677 := @Enclosure.Real.IsNear.mulLit_ft qz204 qz205 Ns420p1674 Ns420p1665 Ns420p1675 Ns420p1676 

noncomputable def Ns420p1678 := nat_lit 242874684307418029117195263 

noncomputable def Ns420p1679 := @Enclosure.Real.IsNear.mulLit_tt qz205 qz205 1158327054525680695885425 302231454903657293676544 Ns420p1678 Ns420p1324 1158327054525680695885425 302231454903657293676544 

noncomputable abbrev qz725 := (@HSub.hSub Real Real Real qz798 qz842 qz836)

noncomputable abbrev qz506 := qz725

noncomputable abbrev qz206 := qz506

noncomputable def Ns420p1680 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz206 884279719003555 140737488355328 1 500000000000000 1309910235 2147483648 9 1073741824 

noncomputable abbrev qz726 := qz842

noncomputable abbrev qz507 := qz726

noncomputable abbrev qz207 := qz507

noncomputable def Ns420p1681 := @Enclosure.Real.IsNear.subLit_ff_n qz207 qz171 837573413 2147483648 9 1073741824 1 1 0 1 1309910235 

noncomputable def Ns420p1682 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz184 2 1 0 1 837573413 4294967296 9 2147483648 837573413 2147483648 9 

noncomputable def Ns420p1683 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true 4216253932 4294967296 

noncomputable abbrev qz727 := (@Nat.cast Real Real.instNatCast 4294967296)

noncomputable def Ns420p1684 := @Enclosure.Real.IsNear.sin_image qz194 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5922978893)) qz727) Bool.true 5922978893 4294967296 

noncomputable def Ns420p1685 := nat_lit 3580221056433900212928544830173525 

noncomputable def Ns420p1686 := nat_lit 2596148429267413814265248164610048 

noncomputable def Ns420p1687 := nat_lit 14499895708329787402036058540174033 

noncomputable def Ns420p1688 := @Enclosure.Real.IsNear.recentre' qz194 Bool.true Ns420p1685 Ns420p1686 Ns420p1687 

noncomputable def Ns420p1689 := nat_lit 396140812571321687967719751680000000000000 

noncomputable def Ns420p1690 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz195 884279719003555 140737488355328 1 500000000000000 4048742699276479655 

noncomputable def Ns420p1691 := @Enclosure.Real.IsNear.subLit_tf qz196 qz27 2895821194669632679 18446744073709551616 13432756815 2305843009213693952 1 16 

noncomputable def Ns420p1692 := @Enclosure.Real.IsNear.subLit_ff_n qz197 qz184 701529222164468569 18446744073709551616 3769080399 2305843009213693952 837573413 4294967296 9 2147483648 

noncomputable def Ns420p1693 := nat_lit 12437457326169721880637865984 

noncomputable def Ns420p1694 := @Enclosure.Real.IsNear.mulLit_ff qz184 qz184 837573413 4294967296 9 2147483648 837573413 4294967296 9 2147483648 701529222164468569 18446744073709551616 

noncomputable def Ns420p1695 := nat_lit 7403855352702589270169121906094399438788756358547671548467833898539666272930640306636903910925297649236191570915337546318001 

noncomputable def Ns420p1696 := nat_lit 245357112146677307060029198107628366151398682095765162082604716352740917782125977619257353385906471301548201273502741613772800 

noncomputable def Ns420p1697 := nat_lit 1864155858282348115842349484869277819561881329057292193535672784977929596657819624883959583484874586851616992425754801 

noncomputable def Ns420p1698 := nat_lit 36991931451592722740876158273222522414761796992128002019788445028503838208155272989996342940336789382810368009563809423376561 

noncomputable def Ns420p1699 := nat_lit 8587498925133705747101021933766992815298953873351780672891165072345932122374409216674007368506726495554187044572595956482048000 

noncomputable def Ns420p1700 := BSN.sin_dyadic_bound_f 5922978893 4294967296 4 3 4294967296 1730560000 Ns420p1695 Ns420p1696 Ns420p1697 Ns420p1698 Ns420p1699 Ns420p1697 4216253932 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 5922978893) (BSN.sinEvenQ 4294967296) 0 3 Ns420p1695 Ns420p1696 Ns420p1697 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 5922978893) (BSN.sinOddQ 4294967296) 0 3 Ns420p1698 Ns420p1699 Ns420p1697 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1701 := @Ns420p1683 553716334592 14865397207531520000 1054063483 1073741824 33796163 907311841280000 (@Ns420p1684 315 8589934592 Bool.true 4216253932 4294967296 1 1730560000 (@Ns420p1688 Ns420p1689 5922978893 4294967296 315 8589934592 (@Ns420p1690 18446744073709551616 13432756815 2305843009213693952 Ns420p1685 Ns420p1686 Ns420p1687 Ns420p1689 RS421to432.d66 (@Ns420p1691 0 1 64779883188423674480 4048742699276479655 18446744073709551616 13432756815 2305843009213693952 (@Ns420p1692 Ns420p1693 2895821194669632679 18446744073709551616 13432756815 2305843009213693952 (@Ns420p1694 3769080399 2305843009213693952 (Ns420p1632 rfl rfl) (Ns420p1632 rfl rfl) rfl) (Ns420p1632 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5922978893 4294967296) (BSN.sin_neg_of_bound 5922978893 4294967296 Bool.false 4216253932 4294967296 1 1730560000 (Ns420p1700 rfl rfl)) rfl rfl) 

noncomputable def Ns420p1702 := nat_lit 3072855366870553370160380610208343057625 

noncomputable def Ns420p1703 := nat_lit 21267647932558653966460912964485513216 

noncomputable def Ns420p1704 := nat_lit 19662704092475979265956445892223164348425574391009963 

noncomputable def Ns420p1705 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz200 qz158) qz191 Ns420p1702 Ns420p1703 Ns420p1704 

noncomputable def Ns420p1706 := nat_lit 3474981163577042087656275 

noncomputable def Ns420p1707 := nat_lit 728624052922254087351585789 

noncomputable def Ns420p1708 := @Enclosure.Real.IsNear.mulLit_tf qz200 qz158 Ns420p1706 302231454903657293676544 Ns420p1707 Ns420p1324 884279719003555 

noncomputable def Ns420p1709 := @Enclosure.Real.IsNear.mulLit_ft qz318 qz205 3 1 0 1 1158327054525680695885425 302231454903657293676544 Ns420p1678 

noncomputable def Ns420p1710 := @Enclosure.Real.IsNear.recentre' qz191 Bool.false 818502811 4294967296 

noncomputable def Ns420p1711 := @Enclosure.Real.IsNear.cos_image qz194 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5922978893)) qz727) Bool.true 5922978893 4294967296 

noncomputable def Ns420p1712 := nat_lit 2850359236748625361703225566109898964544720792127980553239398684617394396301717165563885576348794943227191986405894346850481 

noncomputable def Ns420p1713 := nat_lit 18873624011282869773848399854432951242415283238135781698661901257903147521701998278404411798915882407811400097961749354905600 

noncomputable def Ns420p1714 := nat_lit 17267405043871356599011137570050096440256497951798684905367079187241554274704483888522510711425641636470634460301531187069105 

noncomputable def Ns420p1715 := nat_lit 1717499785026741149420204386753398563059790774670356134578233014469186424474881843334801473701345299110837408914519191296409600 

noncomputable def Ns420p1716 := BSN.cos_dyadic_bound_f 5922978893 4294967296 4 3 4294967296 1730560000 Ns420p1712 Ns420p1713 Ns420p1697 Ns420p1714 Ns420p1715 Ns420p1697 818502811 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 5922978893) (BSN.cosEvenQ 4294967296) 0 3 Ns420p1712 Ns420p1713 Ns420p1697 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 5922978893) (BSN.cosOddQ 4294967296) 0 3 Ns420p1714 Ns420p1715 Ns420p1697 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1717 := @Ns420p1710 553716334592 14865397207531520000 818502811 4294967296 33796163 907311841280000 (@Ns420p1711 315 8589934592 Bool.false 818502811 4294967296 1 1730560000 (@Ns420p1688 Ns420p1689 5922978893 4294967296 315 8589934592 (@Ns420p1690 18446744073709551616 13432756815 2305843009213693952 Ns420p1685 Ns420p1686 Ns420p1687 Ns420p1689 RS421to432.d66 (@Ns420p1691 0 1 64779883188423674480 4048742699276479655 18446744073709551616 13432756815 2305843009213693952 (@Ns420p1692 Ns420p1693 2895821194669632679 18446744073709551616 13432756815 2305843009213693952 (@Ns420p1694 3769080399 2305843009213693952 (Ns420p1632 rfl rfl) (Ns420p1632 rfl rfl) rfl) (Ns420p1632 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5922978893 4294967296) (BSN.cos_neg_of_bound 5922978893 4294967296 Bool.false 818502811 4294967296 1 1730560000 (Ns420p1716 rfl rfl)) rfl rfl) 

noncomputable abbrev qz208 := (@Ns420p1680 1158327054525680695885425 302231454903657293676544 Ns420p1678 Ns420p1324 RS421to432.d66 (@Ns420p1681 1309910235 2147483648 9 1073741824 (@Ns420p1682 1073741824 qz323 (Ns420p1632 rfl rfl) rfl) (Enclosure.Real.IsNear.const Bool.false 1 1) rfl rfl) rfl)

noncomputable def Ns420p1718 := @Ns420p1661 Ns420p1662 Ns420p1654 Ns420p1663 Ns420p1656 Ns420p1664 Ns420p1665 Ns420p1666 Ns420p1667 Ns420p1668 Ns420p1653 Ns420p1654 Ns420p1655 Ns420p1656 (@Ns420p1671 Ns420p1672 Ns420p1673 1054063483 1073741824 33796163 907311841280000 Ns420p1662 Ns420p1654 Ns420p1663 Ns420p1656 (@Ns420p1677 1158327054525680695885425 302231454903657293676544 Ns420p1678 Ns420p1324 Ns420p1669 Ns420p1670 Ns420p1672 Ns420p1673 (@Ns420p1679 Ns420p1678 Ns420p1324 Ns420p1674 Ns420p1665 Ns420p1675 Ns420p1676 qz208 qz208 rfl) qz208 rfl) (Ns420p1701 rfl) rfl) (@Ns420p1705 Ns420p1352 818502811 4294967296 33796163 907311841280000 Ns420p1664 Ns420p1665 Ns420p1666 Ns420p1667 (@Ns420p1708 70368744177664 1 250000000000000 Ns420p1702 Ns420p1703 Ns420p1704 Ns420p1352 (@Ns420p1709 Ns420p1324 Ns420p1706 302231454903657293676544 Ns420p1707 Ns420p1324 qz474 qz208 rfl) RS421to432.d68 rfl) (Ns420p1717 rfl) rfl) rfl rfl 

noncomputable def Ns420p1719 := nat_lit 2680142663084184497131695 

noncomputable def Ns420p1720 := nat_lit 1983570718981440954554009300785863 

noncomputable def Ns420p1721 := nat_lit 170009883809862905119286931400808698207152283490695867240816706484917907061161391510515 

noncomputable def Ns420p1722 := @Enclosure.Real.IsNear.mulLit_tf qz201 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz184) Ns420p1719 151115727451828646838272 Ns420p1720 Ns420p1367 Ns420p1721 

noncomputable def Ns420p1723 := nat_lit 31082702275611665134711390509176302506278509424834232340028998555822468563283335970816 

noncomputable def Ns420p1724 := nat_lit 38395978546320956008677060751547327324220905201960300274949388236629596785260822917930026454119888906031652019990861 

noncomputable def Ns420p1725 := nat_lit 272903466044668431599732052040429624910807735065417902964223741019360920587993088000000000000000000000000000000000000000 

noncomputable def Ns420p1726 := nat_lit 661190239660480318184669766928621 

noncomputable abbrev qz209 := qz501

noncomputable def Ns420p1727 := @Enclosure.Real.IsNear.mulLit_ft qz318 qz209 3 1 0 1 893380887694728165710565 151115727451828646838272 Ns420p1726 

noncomputable def Ns420p1728 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz203 884279719003555 140737488355328 1 500000000000000 1010292183 1073741824 24501163 907311841280000 893380887694728165710565 

noncomputable def Ns420p1729 := @Enclosure.Real.IsNear.recentre' qz203 Bool.false 4041168732 4294967296 401427054592 14865397207531520000 1010292183 1073741824 24501163 907311841280000 

noncomputable def Ns420p1730 := @Enclosure.Real.IsNear.sin_image qz193 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2631314481) qz709) Bool.false 2631314481 2147483648 227 8589934592 Bool.false 4041168732 4294967296 1 

noncomputable def Ns420p1731 := nat_lit 1126037006357399256308391889720378561161623749031995075414866204984945778398103045397159427735527830354136326202151248961 

noncomputable def Ns420p1732 := nat_lit 5627592173121572242320596411398495787992904019303761861162546535104801741186805353507785479572187472329747575198363001921 

noncomputable def Ns420p1733 := BSN.sin_dyadic_bound_f 2631314481 2147483648 4 3 4294967296 1730560000 Ns420p1731 Ns420p1342 Ns420p1635 Ns420p1732 Ns420p1345 Ns420p1635 4041168732 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 2631314481) (BSN.sinEvenQ 2147483648) 0 3 Ns420p1731 Ns420p1342 Ns420p1635 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 2631314481) (BSN.sinOddQ 2147483648) 0 3 Ns420p1732 Ns420p1345 Ns420p1635 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz508 := (@HMul.hMul Real Real Real qz619 qz617 qz723)

noncomputable abbrev qz210 := qz508

noncomputable abbrev qz509 := (@Enclosure.Real.IsNear.neg qz210 Bool.false 893380887694728165710565 151115727451828646838272 Ns420p1726 Ns420p1367 (@Ns420p1728 151115727451828646838272 Ns420p1726 Ns420p1367 RS421to432.d66 (Ns420p1729 (@Ns420p1730 1730560000 (Ns420p1633 rfl) (Enclosure.sfrac_false_div 2631314481 2147483648) (Ns420p1733 rfl rfl) rfl rfl) rfl) rfl))

noncomputable def Ns420p1734 := @Ns420p1727 Ns420p1367 Ns420p1719 151115727451828646838272 Ns420p1720 Ns420p1367 qz474 qz509 rfl 

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz326 qz499 (Real.cos qz494))

noncomputable def Ns420p1735 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz211) (@HMul.hMul Real Real Real qz5 qz158 qz199) 

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz326 qz316 qz501)

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz326 qz502 (Zeta.RiemannSiegel.correction qz483))

noncomputable def Ns420p1736 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz184) (@HMul.hMul Real Real Real qz5 qz190 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns420p1735 (@HMul.hMul Real Real Real qz5 qz212 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz184))) qz213)) 

noncomputable def Ns420p1737 := @Enclosure.Real.IsNear.mulLit_ff qz190 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns420p1735 (@HMul.hMul Real Real Real qz5 qz212 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz184))) qz213) 25364291857 

noncomputable def Ns420p1738 := nat_lit 6702725420774711168364984462290588529524358228200459680620395034627199411395 

noncomputable def Ns420p1739 := nat_lit 3618502788666131106986593281521497120414687020801267626233049500247285301248 

noncomputable def Ns420p1740 := nat_lit 15090870055767933179651244085026241903534656248536423012903844114597679716051110049254466016689787983575547 

noncomputable def Ns420p1741 := nat_lit 317701448272760528605119385803618497344208572834518159465193446980976640000000000000000000000000000000000000000 

noncomputable def Ns420p1742 := nat_lit 20521088171929674583944241955520224854824590621069244856674686365282361727805 

noncomputable def Ns420p1743 := @Enclosure.Real.IsNear.subLit_tt_p (@HSub.hSub Real Real Real qz11 Ns420p1735 (@HMul.hMul Real Real Real qz5 qz212 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz184))) qz213 Ns420p1742 Ns420p1739 

noncomputable def Ns420p1744 := nat_lit 14242453823081902552504298722099053366132028804175986006012106280911315152108799611396168678532459747031547 

noncomputable def Ns420p1745 := nat_lit 23612894272440400477143888234759725404690718129621048359825 

noncomputable def Ns420p1746 := nat_lit 3138550867693340381917894711603833208051177722232017256448 

noncomputable def Ns420p1747 := nat_lit 17417367529470516314588534953423222757578627328722079950260650147877096850911649729 

noncomputable def Ns420p1748 := nat_lit 6522179416219987226064912891751524894436420212490240000000000000000000000000000000000000 

noncomputable def Ns420p1749 := nat_lit 21036844685282679752277224730264474006929990063894640857850725693802499203611484261345977730245000860365672160763101708099668368424960 

noncomputable def Ns420p1750 := nat_lit 3741469324459257505440617272972947391018901007907446791365 

noncomputable def Ns420p1751 := nat_lit 392318858461667547739736838950479151006397215279002157056 

noncomputable def Ns420p1752 := nat_lit 84297928657621062274191755086913589112412926369645461797620132501572071923563 

noncomputable def Ns420p1753 := nat_lit 77185555221538310367632105227828696975578937425920000000000000000000000000000000000 

noncomputable def Ns420p1754 := @Enclosure.Real.IsNear.subLit_ff_n Ns420p1735 (@HMul.hMul Real Real Real qz5 qz212 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz184)) Ns420p1750 Ns420p1751 Ns420p1752 Ns420p1753 

noncomputable def Ns420p1755 := nat_lit 55030051715897118545870225166930554431171687393154677520614655854728387025725 

noncomputable def Ns420p1756 := nat_lit 13895477320236888778576987957846084685897871050198731087940548318934939828730125883194821292330855651031547 

noncomputable def Ns420p1757 := nat_lit 8050809886002678042370322157470489477806520561922984811077900079134176713875947632631544586724800620798540352421591335642654132142080 

noncomputable def Ns420p1758 := @Enclosure.Real.IsNear.subLit_tt_p (@Neg.neg Real Real.instNeg qz211) (@HMul.hMul Real Real Real qz5 qz158 qz199) 

noncomputable def Ns420p1759 := nat_lit 1098202872733284891122015301913738894867937600975369986875 

noncomputable def Ns420p1760 := nat_lit 48168864075818295118338481496918623460134851190082486457616804501572071923563 

noncomputable def Ns420p1761 := nat_lit 912025810905258471076219427193621 

noncomputable def Ns420p1762 := nat_lit 282697429352181300936097654467873419889435416756923864382996230057541839240560640 

noncomputable def Ns420p1763 := @Enclosure.Real.IsNear.neg qz211 Bool.false Ns420p1759 

noncomputable def Ns420p1764 := @Enclosure.Real.IsNear.mulLit_ff qz204 qz191 Ns420p1674 Ns420p1665 Ns420p1675 

noncomputable def Ns420p1765 := @Enclosure.Real.IsNear.mulLit_ft qz158 qz199 884279719003555 70368744177664 1 

noncomputable def Ns420p1766 := nat_lit 61597525169691237050631320436972580137126757708300665 

noncomputable def Ns420p1767 := @Enclosure.Real.IsNear.mulLit_tt qz212 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz184) 893380887694728165710565 75557863725914323419136 Ns420p1726 Ns420p1418 Ns420p1766 

noncomputable def Ns420p1768 := nat_lit 2388549774942612242374994943721230728846620832384663270162012865703 

noncomputable def Ns420p1769 := nat_lit 652217941621998722606491289175152489443642021249024000000000000000000000 

noncomputable def Ns420p1770 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz209 2 1 0 1 893380887694728165710565 151115727451828646838272 Ns420p1726 

noncomputable def Ns420p1771 := @Ns420p1770 Ns420p1367 893380887694728165710565 75557863725914323419136 Ns420p1726 Ns420p1418 qz323 qz509 rfl 

noncomputable abbrev qz214 := (@HMul.hMul Real Real Real qz326 qz500 (Real.sin qz494))

noncomputable def Ns420p1772 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz214) (@HMul.hMul Real Real Real qz5 qz209 qz183) 

noncomputable def Ns420p1773 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz184) (@HMul.hMul Real Real Real qz5 qz190 Ns420p1772) Bool.true Ns420p1766 Ns420p1421 Ns420p1768 Ns420p1769 (BSN.deriv_correction_mk qz184 qz504) 

noncomputable def Ns420p1774 := nat_lit 2428513499094264780625896597723910196730345 

noncomputable def Ns420p1775 := nat_lit 915318794160105096434794147990765933366668319663806531881 

noncomputable def Ns420p1776 := @Enclosure.Real.IsNear.mulLit_ft qz190 Ns420p1772 25364291857 8589934592 2023 8589934592 Ns420p1774 Ns420p1429 Ns420p1775 

noncomputable def Ns420p1777 := nat_lit 759281615752259644920112668973338428702720000000000000000000000 

noncomputable def Ns420p1778 := @Enclosure.Real.IsNear.subLit_tt_n (@Neg.neg Real Real.instNeg qz214) (@HMul.hMul Real Real Real qz5 qz209 qz183) 

noncomputable def Ns420p1779 := nat_lit 1220950249546469907250854844435275 

noncomputable def Ns420p1780 := nat_lit 324518553658426726783156020576256 

noncomputable def Ns420p1781 := nat_lit 1627320967971814488367779338870136945346113 

noncomputable def Ns420p1782 := nat_lit 8368474665569170658318079754240000000000000000000 

noncomputable def Ns420p1783 := nat_lit 18547252068286243554936402701846784658335255 

noncomputable def Ns420p1784 := nat_lit 767670035779699205376439046613265430697894668371712067881 

noncomputable def Ns420p1785 := nat_lit 788097688266035811364924090971987243553985067171317201527213597753941688320 

noncomputable def Ns420p1786 := @Enclosure.Real.IsNear.neg qz214 Bool.false Ns420p1779 

noncomputable def Ns420p1787 := @Enclosure.Real.IsNear.mulLit_tt qz205 qz199 1158327054525680695885425 302231454903657293676544 Ns420p1678 

noncomputable def Ns420p1788 := @Enclosure.Real.IsNear.mulLit_tf qz209 qz183 893380887694728165710565 151115727451828646838272 Ns420p1726 Ns420p1367 20760744183978910027 36893488147419103232 

noncomputable def Ns420p1789 := @Enclosure.Real.IsNear.of_eq qz183 (@HMul.hMul Real Real Real qz5 qz190 qz191) Bool.false 20760744183978910027 

noncomputable def Ns420p1790 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz191 25364291857 8589934592 2023 

noncomputable abbrev qz510 := (@Ns420p1789 36893488147419103232 120701014852882869 779374937114228555776000 (BSN.correction_mk qz184 qz724) (@Ns420p1790 8589934592 818502811 4294967296 33796163 907311841280000 20760744183978910027 36893488147419103232 120701014852882869 779374937114228555776000 (@Ns420p1624 8589934592 (Ns420p1638 rfl rfl rfl rfl rfl) rfl) (Ns420p1717 rfl) rfl))

noncomputable def Ns420p1791 := @Ns420p1788 120701014852882869 779374937114228555776000 Ns420p1783 Ns420p1429 Ns420p1784 Ns420p1777 qz509 qz510 

noncomputable abbrev qz511 := (@Ns420p1624 8589934592 (Ns420p1638 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns420p1792 := @Ns420p1767 Ns420p1421 Ns420p1768 Ns420p1769 Ns420p1755 Ns420p1739 Ns420p1756 Ns420p1741 Ns420p1771 (Ns420p1773 (@Ns420p1776 Ns420p1777 Ns420p1766 Ns420p1421 Ns420p1768 Ns420p1769 qz511 (@Ns420p1778 Ns420p1779 Ns420p1780 Ns420p1781 Ns420p1782 Ns420p1783 Ns420p1429 Ns420p1784 Ns420p1777 Ns420p1785 Ns420p1774 Ns420p1429 Ns420p1775 Ns420p1777 (@Ns420p1786 Ns420p1780 Ns420p1781 Ns420p1782 (@Ns420p1787 Ns420p1324 1054063483 1073741824 33796163 907311841280000 Ns420p1779 Ns420p1780 Ns420p1781 Ns420p1782 qz208 (Ns420p1701 rfl) rfl)) (Ns420p1791 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns420p1793 := @Ns420p1754 Ns420p1755 Ns420p1739 Ns420p1756 Ns420p1741 Ns420p1757 Ns420p1742 Ns420p1739 Ns420p1744 Ns420p1741 (@Ns420p1758 Ns420p1759 Ns420p1751 Ns420p1760 Ns420p1753 932086960559148472682065 75557863725914323419136 Ns420p1761 Ns420p1418 Ns420p1762 Ns420p1750 Ns420p1751 Ns420p1752 Ns420p1753 (@Ns420p1763 Ns420p1751 Ns420p1760 Ns420p1753 (@Ns420p1764 Ns420p1676 818502811 4294967296 33796163 907311841280000 Ns420p1759 Ns420p1751 Ns420p1760 Ns420p1753 (@Ns420p1679 Ns420p1678 Ns420p1324 Ns420p1674 Ns420p1665 Ns420p1675 Ns420p1676 qz208 qz208 rfl) (Ns420p1717 rfl) rfl)) (@Ns420p1765 250000000000000 1054063483 1073741824 33796163 907311841280000 932086960559148472682065 75557863725914323419136 Ns420p1761 Ns420p1418 RS421to432.d68 (Ns420p1701 rfl) rfl) rfl rfl) Ns420p1792 

noncomputable def Ns420p1794 := nat_lit 1137381881072572433480855514520335411475 

noncomputable def Ns420p1795 := nat_lit 17842929611764155576804101566867485553670309596567924744507 

noncomputable abbrev qz215 := qz502

noncomputable def Ns420p1796 := @Enclosure.Real.IsNear.mulLit_tf qz215 qz183 Ns420p1794 Ns420p1451 Ns420p1795 Ns420p1453 20760744183978910027 36893488147419103232 

noncomputable def Ns420p1797 := @Enclosure.Real.IsNear.mulLit_ff qz159 qz192 Ns420p1209 Ns420p1213 Ns420p1211 Ns420p1214 1454544379 4294967296 24501163 907311841280000 Ns420p1794 

noncomputable abbrev qz512 := (@HMul.hMul Real Real Real qz619 qz701 qz718)

noncomputable abbrev qz216 := qz512

noncomputable def Ns420p1798 := @Ns420p1796 120701014852882869 779374937114228555776000 Ns420p1745 Ns420p1746 Ns420p1747 Ns420p1748 (@Enclosure.Real.IsNear.neg qz216 Bool.false Ns420p1794 Ns420p1451 Ns420p1795 Ns420p1453 (@Ns420p1797 Ns420p1451 Ns420p1795 Ns420p1453 RS421to432.d70 qz505 rfl)) qz510 

noncomputable def Ns420p1799 := nat_lit 3412145643217717300442566543561006234425 

noncomputable def Ns420p1800 := nat_lit 53528788835292466730412304700602456661010928789703774233521 

noncomputable def Ns420p1801 := @Enclosure.Real.IsNear.mulLit_tt qz202 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz184) Ns420p1799 Ns420p1451 Ns420p1800 Ns420p1453 Ns420p1766 

noncomputable def Ns420p1802 := @Enclosure.Real.IsNear.mulLit_ft qz318 qz215 3 1 0 1 Ns420p1794 Ns420p1451 Ns420p1795 

noncomputable def Ns420p1803 := @Ns420p1802 Ns420p1453 Ns420p1799 Ns420p1451 Ns420p1800 Ns420p1453 qz474 (@Enclosure.Real.IsNear.neg qz216 Bool.false Ns420p1794 Ns420p1451 Ns420p1795 Ns420p1453 (@Ns420p1797 Ns420p1451 Ns420p1795 Ns420p1453 RS421to432.d70 qz505 rfl)) rfl 

noncomputable def Ns420p1804 := @Ns420p1801 Ns420p1421 Ns420p1768 Ns420p1769 Ns420p1649 Ns420p1292 Ns420p1650 Ns420p1651 Ns420p1803 (Ns420p1773 (@Ns420p1776 Ns420p1777 Ns420p1766 Ns420p1421 Ns420p1768 Ns420p1769 qz511 (@Ns420p1778 Ns420p1779 Ns420p1780 Ns420p1781 Ns420p1782 Ns420p1783 Ns420p1429 Ns420p1784 Ns420p1777 Ns420p1785 Ns420p1774 Ns420p1429 Ns420p1775 Ns420p1777 (@Ns420p1786 Ns420p1780 Ns420p1781 Ns420p1782 (@Ns420p1787 Ns420p1324 1054063483 1073741824 33796163 907311841280000 Ns420p1779 Ns420p1780 Ns420p1781 Ns420p1782 qz208 (Ns420p1701 rfl) rfl)) (Ns420p1791 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns420p1805 := @Ns420p1647 Ns420p1648 Ns420p1623 Ns420p1649 Ns420p1292 Ns420p1650 Ns420p1651 Ns420p1652 Ns420p1640 Ns420p1620 Ns420p1641 Ns420p1623 (@Ns420p1657 Ns420p1658 Ns420p1620 Ns420p1659 Ns420p1623 Ns420p1660 Ns420p1646 Ns420p1620 Ns420p1648 Ns420p1623 Ns420p1718 (@Ns420p1722 Ns420p1723 Ns420p1724 Ns420p1725 Ns420p1658 Ns420p1620 Ns420p1659 Ns420p1623 Ns420p1734 (@Ns420p1736 Bool.false Ns420p1721 Ns420p1723 Ns420p1724 Ns420p1725 (BSN.iteratedDeriv_two_correction_mk qz184 qz504) (@Ns420p1737 8589934592 2023 8589934592 Ns420p1738 Ns420p1739 Ns420p1740 Ns420p1741 Ns420p1721 Ns420p1723 Ns420p1724 Ns420p1725 qz511 (@Ns420p1743 Ns420p1744 Ns420p1741 Ns420p1745 Ns420p1746 Ns420p1747 Ns420p1748 Ns420p1749 Ns420p1738 Ns420p1739 Ns420p1740 Ns420p1741 (Ns420p1793 rfl rfl) (Ns420p1798 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns420p1804 

noncomputable def Ns420p1806 := nat_lit 698579740316410448927839438542899470288498535113234125 

noncomputable def Ns420p1807 := nat_lit 2993155353253689176481146537402947624255349848014848 

noncomputable def Ns420p1808 := nat_lit 481510656198153352620140200979348586877103865697436228644481566607544077130097634269 

noncomputable def Ns420p1809 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz320 RSCompact.c11) qz203) qz183 Ns420p1806 Ns420p1807 Ns420p1808 Ns420p1466 20760744183978910027 36893488147419103232 120701014852882869 

noncomputable def Ns420p1810 := @Enclosure.Real.IsNear.mulLit_ff qz702 qz203 Ns420p1215 Ns420p1216 Ns420p1217 Ns420p1218 1010292183 1073741824 24501163 907311841280000 Ns420p1806 

noncomputable abbrev qz513 := (Ns420p1729 (@Ns420p1730 1730560000 (Ns420p1633 rfl) (Enclosure.sfrac_false_div 2631314481 2147483648) (Ns420p1733 rfl rfl) rfl rfl) rfl)

noncomputable def Ns420p1811 := Ns420p1618 (@Ns420p1622 Ns420p1623 Ns420p1611 Ns420p1612 Ns420p1613 Ns420p1614 qz511 (@Ns420p1639 Ns420p1640 Ns420p1620 Ns420p1641 Ns420p1623 Ns420p1642 Ns420p1284 Ns420p1643 Ns420p1644 Ns420p1645 Ns420p1619 Ns420p1620 Ns420p1621 Ns420p1623 (Ns420p1805 rfl rfl) (@Ns420p1809 779374937114228555776000 Ns420p1642 Ns420p1284 Ns420p1643 Ns420p1644 (@Ns420p1810 Ns420p1807 Ns420p1808 Ns420p1466 RS421to432.d71 qz513 rfl) qz510 rfl) rfl rfl) rfl) 

noncomputable def Ns420p1812 := @Enclosure.Real.IsNear.of_eq qz714 (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz184) qz461)) Bool.false Ns420p1606 Ns420p1607 Ns420p1608 Ns420p1609 (BSN.correctionLinear_mk qz184) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz184) qz461) Bool.true Ns420p1606 Ns420p1607 Ns420p1608 Ns420p1609 (@Ns420p1615 Ns420p1607 Ns420p1608 Ns420p1609 Ns420p1811 RS421to432.d72 rfl)) 

noncomputable def Ns420p1813 := @Enclosure.Real.IsNear.inv_image qz185 375642269 33554432 37 33554432 1498632 1498634 16777216 qz491 rfl 

noncomputable def Ns420p1814 := @Ns420p1610 Ns420p1563 Ns420p1573 Ns420p1566 Ns420p1812 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz185) Bool.false 2997266 33554432 2 33554432 1498633 16777216 1 16777216 (Ns420p1813 rfl rfl rfl rfl rfl) rfl) 

noncomputable abbrev qz514 := (BSN.correction_mk qz184 qz724)

noncomputable def Ns420p1815 := @Ns420p1565 Ns420p1566 Ns420p1480 Ns420p1476 Ns420p1482 Ns420p1478 (Ns420p1567 qz29 (@Enclosure.Real.IsNear.of_eq qz485 (@Inv.inv Real Real.instInv (Real.sqrt qz185)) Bool.false 5014269 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz182 (BSN.t_div_two_pi_nonneg qz181 787461 1000 qz186)) Ns420p1571) rfl) (@Ns420p1574 Ns420p1575 Ns420p1562 Ns420p1563 Ns420p1564 Ns420p1566 (@Ns420p1576 70368744177664 606289959341713 14865397207531520000 qz514 (@Ns420p1577 8388608 799331 4194304 8686697 886046720000 39598048017697 70368744177664 606289959341713 14865397207531520000 (@Ns420p1578 8388608 (Ns420p1590 rfl rfl rfl rfl rfl) rfl) (Ns420p1605 rfl) rfl)) (Ns420p1814 rfl) rfl rfl) 

noncomputable abbrev qz728 := (@BSN.floor_sqrt_eq_dec qz181 787461 1000 11 qz186 rfl rfl rfl)

noncomputable abbrev qz515 := qz728

noncomputable def Ns420p1816 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz181) (hardyZApproximantRS qz181) Bool.false Ns420p1475 Ns420p1476 Ns420p1477 Ns420p1478 (@Eq.refl Real (hardyZApproximantRS qz181)) (Ns420p1479 (BSN.hardyZApproximantRS_eq qz181 11 qz515) (@Ns420p1481 Ns420p1482 Ns420p1478 Ns420p1483 Ns420p1475 Ns420p1476 Ns420p1477 Ns420p1478 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz181) qz181 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz181) qz181 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz181) qz181 11)) Bool.true 8582273 67108864 151603 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz181) qz181 11) (Ns420p1561 (Ns420p1560 rfl) rfl rfl)) (Ns420p1815 rfl) rfl rfl)) 

theorem RS421to432.d75 : Enclosure.Real.IsNear (hardyZApproximantRS qz181) Bool.false Ns420p1475 Ns420p1476 Ns420p1477 Ns420p1478 := Ns420p1816 

noncomputable def Ns420p1817 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) qz44 Bool.false 16306601 1073741824 

theorem RS421to432.d76 : Enclosure.Real.IsNear (hardyZErrorBoundRS qz4) Bool.false 16306601 1073741824 201 1073741824 := @Ns420p1817 201 1073741824 (BSN.hardyZErrorBoundRS_mk qz4 775738 1000 qz10 rfl rfl) (@Ns420p336 1 1073741824 1 1073741824 2188634937622528 16306601 1073741824 201 1073741824 (@Ns420p337 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns420p338 (Ns420p344 rfl rfl rfl rfl) rfl) rfl) (@Ns420p345 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns420p346 1 33554432 1 33554432 (@Ns420p351 16777216 (@Ns420p356 70368744177664000 Ns420p347 Ns420p348 Ns420p349 Ns420p350 (@Ns420p357 Ns420p353 Ns420p354 Ns420p355 (Ns420p343 rfl) (Ns420p343 rfl) rfl) (Ns420p343 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) 

noncomputable def Ns420p1818 := nat_lit 3379663657523394578429588457995329558681953536751036489186700028592008571714859635667084799950838012756756604493932698811994144048775203232071 

noncomputable def Ns420p1819 := nat_lit 381072821083495145432323880589986121307201921712032611188861933548019011086397170424842053596617672260721060927906081896416989218663120764928 

noncomputable def Ns420p1820 := nat_lit 791300408291379731206471486952319739960011775691232296227641082928559900590710368244216370631974972038003942233569477176670720497651867383304418389822613535227641596343561231294698491211203967 

noncomputable def Ns420p1821 := nat_lit 690231887414557423862125719747212047292344663442213806404896852481244709032667821453391276279564385719610821757998302862556267838177280000000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz843 := (Enclosure.sfrac Bool.false 788762 1000)

noncomputable abbrev qz729 := qz843

noncomputable abbrev qz516 := qz729

noncomputable abbrev qz217 := qz516

noncomputable abbrev qz844 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 788762 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz730 := qz844

noncomputable abbrev qz517 := qz730

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz326 qz620 (@HPow.hPow Real Real Real qz443 qz517 qz328))

noncomputable abbrev qz845 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 788762 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz731 := qz845

noncomputable abbrev qz518 := qz731

noncomputable abbrev qz219 := (Zeta.RiemannSiegel.correction qz518)

noncomputable abbrev qz220 := qz518

noncomputable abbrev qz846 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 788762 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz732 := qz846

noncomputable abbrev qz519 := qz732

noncomputable abbrev qz221 := qz519

noncomputable abbrev qz733 := (Zeta.RiemannSiegel.correctionLinear qz220)

noncomputable abbrev qz520 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) qz219 (@HMul.hMul Real Real Real qz5 qz733 (@Inv.inv Real Real.instInv qz221)))

noncomputable def Ns420p1822 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz217) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz217) qz217 11) (@HMul.hMul Real Real Real qz5 qz218 qz520)) Bool.true Ns420p1818 Ns420p1819 Ns420p1820 Ns420p1821 

noncomputable def Ns420p1823 := nat_lit 62838021801950625630616026709964353348915632011622930152281079849035674309442052701392682695725687379400259250521187908418927111853899671225 

noncomputable def Ns420p1824 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz217) qz217 11) (@HMul.hMul Real Real Real qz5 qz218 qz520) 606242073 67108864 151851 134217728 Ns420p1823 Ns420p1819 

noncomputable def Ns420p1825 := nat_lit 10387157131384239620682963775009686005069031552666571762464679807435019745464341165595886947970638900218873373114617681641629947891867383304418389822613535227641596343561231294698491211203967 

noncomputable def Ns420p1826 := nat_lit 226805388758480063582168585403578283988767239152144309611867722827577214726046762069071943116367994884123444052085118309727076581765664480273413177344 

noncomputable def Ns420p1827 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz217) qz217 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 788762 1000 194 242 268435456 134217728 4503599627370496 Bool.false 405634707992 2568 

noncomputable def Ns420p1828 := Ns420p1827 618095470 41 84886744 8 643680110 41 80936328 8 Bool.true 1052481048 130268 Bool.true 93970032 Bool.true 34605291 14148475504056880 1 Bool.false 252154899 Bool.true Bool.false 266207977 Bool.true Bool.true 1212484146 

noncomputable def Ns420p1829 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz217) qz217 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 788762 1000 82 141 268435456 134217728 4503599627370496 Bool.false 405634707992 2568 

noncomputable def Ns420p1830 := Ns420p1829 558195838 41 94906264 8 589812974 41 89478488 8 Bool.true 918333450 106271 Bool.true 73048462 Bool.true 133655620 14148475504056880 1 Bool.false 258557420 Bool.true Bool.false 128201235 Bool.true Bool.true 1052481048 

noncomputable def Ns420p1831 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz217) qz217 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 788762 1000 62 15 268435456 134217728 4503599627370496 Bool.false 405634707992 2568 

noncomputable def Ns420p1832 := Ns420p1831 480971758 41 109588312 8 522351262 41 101459064 8 Bool.true 838717173 78807 Bool.false 119701655 Bool.true 51256701 14148475504056880 1 Bool.false 242185901 Bool.true Bool.false 50945794 Bool.false Bool.true 918333450 

noncomputable def Ns420p1833 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz217) qz217 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 788762 1000 265 153 268435456 134217728 4503599627370496 Bool.false 405634707992 2568 

noncomputable def Ns420p1834 := Ns420p1833 372130544 40 134217720 8 432030192 40 120047984 16 Bool.true 590650318 46461 Bool.false 373057354 Bool.false 352123164 14148475504056880 1 Bool.false 264047953 Bool.true Bool.false 259479785 Bool.true Bool.true 838717173 

noncomputable def Ns420p1835 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz217) qz217 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 788762 1000 613 410 268435456 134217728 4503599627370496 Bool.false 405634707992 2568 

noncomputable def Ns420p1836 := Ns420p1835 186065264 40 189812528 16 294906480 40 154981288 8 Bool.true 268435328 2608 Bool.false 397494701 Bool.false 144137425 14148475504056880 1 Bool.false 267348708 Bool.true Bool.false 230658771 Bool.true Bool.true 590650318 

noncomputable def Ns420p1837 := nat_lit 460918283621518861129397662246848370938304877377638594031 

noncomputable def Ns420p1838 := nat_lit 305020273671586873571726559424468758136932708384768000 

noncomputable def Ns420p1839 := nat_lit 146545192981711484994048679439360000 

noncomputable def Ns420p1840 := nat_lit 693535807094092146079962184158986833920 

noncomputable abbrev qz847 := (@Eq.refl Real (Enclosure.sfrac Bool.false 788762 1000))

noncomputable abbrev qz734 := qz847

noncomputable abbrev qz521 := qz734

noncomputable abbrev qz222 := qz521

noncomputable def Ns420p1841 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz217 788762 1000 2488582970576 16000000 1577524 4000 2000 Ns420p1839 Ns420p1840 qz222 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns420p1842 := nat_lit 9439606448568706275930064122815454636816483888694038405754880 

noncomputable abbrev qz522 := (@HMul.hMul Real Real Real qz619 qz625 (@HSub.hSub Real Real Real qz624 qz626 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 (@Nat.cast Real Real.instNatCast 1577524)))))

noncomputable abbrev qz735 := (Real.log (Enclosure.sfrac Bool.false 2488582970576 16000000))

noncomputable abbrev qz736 := (Enclosure.sfrac Bool.false 788762 2000)

noncomputable abbrev qz223 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 788762 4000) qz735) qz522) qz736)

noncomputable abbrev qz523 := (@HSub.hSub Real Real Real qz11 qz223 (@HMul.hMul Real Real Real qz5 qz736 (Real.log Real.pi)))

noncomputable def Ns420p1843 := @Enclosure.Real.IsNear.addLit_ft_p qz523 (Enclosure.sfrac Bool.true Ns420p1839 Ns420p1840) 13610844129421836402139 9007199254740992000 3308828813662376337 346112000000000000000000 Ns420p1839 Ns420p1840 0 1 Ns420p1842 

noncomputable def Ns420p1844 := nat_lit 91340828760656841774139546009600 

noncomputable abbrev qz524 := (@HMul.hMul Real Real Real qz5 qz736 (Real.log Real.pi))

noncomputable def Ns420p1845 := @Enclosure.Real.IsNear.subLit_ff_p qz223 qz524 3535446348991517002847 1801439850948198400 1244941758098863 338000000000000000000 15148474333941 33554432000 394381 67108864000 Ns420p1844 13610844129421836402139 9007199254740992000 

noncomputable def Ns420p1846 := nat_lit 35354463489915170028470000 

noncomputable abbrev qz224 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 788762 4000) qz735) qz522)

noncomputable def Ns420p1847 := @Enclosure.Real.IsNear.subLit_ff_p qz224 qz736 21229499994241592180187 9007199254740992000 1244941758098863 338000000000000000000 788762 2000 0 1 Ns420p1846 3535446348991517002847 1801439850948198400 1244941758098863 338000000000000000000 

noncomputable def Ns420p1848 := nat_lit 47804584131664190760221411463319781376 

noncomputable def Ns420p1849 := nat_lit 57809069063249922881486848 

noncomputable def Ns420p1850 := nat_lit 976434256017559865979881223679075070025901094481391601895876842722871979540480 

noncomputable def Ns420p1851 := nat_lit 2381872417057710975361856294162736558852249913301053296647971875799638736896 

noncomputable def Ns420p1852 := nat_lit 53953840922894395260984468045636448743582335973644709619969620065648640 

noncomputable def Ns420p1853 := BSN.log_dyadic_bound 391430970576 4585734970576 4 3 Ns420p1850 134217728 54080000 Ns420p1851 Ns420p1852 22969112 4977165941152 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 391430970576) (BSN.artanhQ 4585734970576) 0 3 Ns420p1851 Ns420p1850 Ns420p1852 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns420p1854 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 788762 4000) qz735 788762 4000 0 1 53838891036109927 4503599627370496 3125002873 169000000000000000 21233035685712069120187 9007199254740992000 94803212158201 26000000000000000000 (Enclosure.Real.IsNear.const Bool.false 788762 4000) (BSN.isNear_log_sfrac 2488582970576 16000000 53838891036109927 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2488582970576) qz335)) Bool.false Ns420p1849 Ns420p103 1000000919360000 54080000000000000000000 53838891036109927 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2488582970576 16000000 17 4977165941152 4194304000000 22969112 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns420p1853 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns420p1855 := BSN.arctan_dyadic_bound_f 1000 1577524 1 0 16777216 6760000 0 1 1 0 1 1 10635 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1577524) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1577524) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns420p1856 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1577524))) 884279719003555 562949953421312 1 2000000000000000 10635 16777216 1 6760000 14829764877387311349760 883922867619235 562949953421312 50000000169 338000000000000000 qz16 (Ns420p1855 rfl) rfl rfl 

noncomputable abbrev qz225 := qz522

noncomputable def Ns420p1857 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 788762 4000) qz735) qz225 21233035685712069120187 9007199254740992000 94803212158201 26000000000000000000 883922867619235 2251799813685248 50000000169 1352000000000000000 Ns420p1848 21229499994241592180187 9007199254740992000 1244941758098863 338000000000000000000 (Ns420p1854 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1577524)))) 1 4 0 1 883922867619235 562949953421312 50000000169 338000000000000000 883922867619235 2251799813685248 50000000169 1352000000000000000 qz340 Ns420p1856 rfl) 

noncomputable def Ns420p1858 := @Ns420p1843 Ns420p1837 Ns420p1838 3308828813662376337 346112000000000000000000 (@Ns420p1845 3308828813662376337 346112000000000000000000 (Ns420p1847 (Ns420p1857 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 788762 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz736 (Real.log Real.pi) 788762 2000 0 1 38410761 33554432 1 67108864 15148474333941 33554432000 394381 67108864000 (Enclosure.Real.IsNear.const Bool.false 788762 2000) RS421to432.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns420p1839 Ns420p1840) 

noncomputable def Ns420p1859 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz217) Bool.false Ns420p1837 Ns420p1838 3308828813662376337 346112000000000000000000 50704338499 33554432 321 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz217) (@HAdd.hAdd Real Real Real qz341 qz523 (Enclosure.sfrac Bool.true Ns420p1839 Ns420p1840)) Bool.false Ns420p1837 Ns420p1838 3308828813662376337 346112000000000000000000 Ns420p1841 (Ns420p1858 rfl rfl)) 

noncomputable def Ns420p1860 := BSN.cos_dyadic_bound_f 67071950 68719476736 1 0 33554432 13533204 0 1 1 0 1 1 33554416 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 67071950) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 67071950) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns420p1861 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz217) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50704338499) qz342) Bool.false 50704338499 33554432 321 33554432 Bool.true 33554416 33554432 1 6760000 (Ns420p1859 rfl) (Enclosure.sfrac_false_div 50704338499 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50704338499) qz342) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4719768929478438289408) qz343) 226375608064910080 72057594037927936 Bool.false 33554416 33554432 240 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q2 50704338499 33554432 226375608064910080 72057594037927936 240 4719768929478438289408 Ns420p103 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554416 33554432 4719768929478438289408 Ns420p103 67071950 68719476736 13533204 13520000 (Ns420p1860 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns420p1862 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz217) Bool.false Ns420p1837 Ns420p1838 3308828813662376337 346112000000000000000000 405634707992 268435456 2568 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz217) (@HAdd.hAdd Real Real Real qz341 qz523 (Enclosure.sfrac Bool.true Ns420p1839 Ns420p1840)) Bool.false Ns420p1837 Ns420p1838 3308828813662376337 346112000000000000000000 Ns420p1841 (Ns420p1858 rfl rfl)) 

noncomputable def Ns420p1863 := Ns420p1836 46461 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 613 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267348708 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 410 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 230658771 268435456) qz222 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 1) Bool.true 2097151 2097152 34429913 3544186880000 268435328 268435456 2608 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz217)) Bool.true 2097151 2097152 34429913 3544186880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz217) qz217) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz217)) Bool.true 33554416 33554432 2203514432 226827960320000 2097151 2097152 34429913 3544186880000 (Ns420p1861 rfl rfl) rfl)) rfl) (Ns420p1862 rfl) RS421to432.d7 

noncomputable def Ns420p1864 := nat_lit 34981113143888150173131129967798683922324981758695432464285341344378936662180919296639218061230380574528529201 

noncomputable def Ns420p1865 := nat_lit 15558800832084868080562647368299469941533479808543070778973464132994337286153698789067252233412183876401 

noncomputable def Ns420p1866 := nat_lit 174733865352993269495958157248556928641849810758798892919478849958910393383615288665106456982058952423970464561 

noncomputable def Ns420p1867 := BSN.sin_dyadic_bound_f 397494701 268435456 4 3 268435456 134217728 Ns420p1864 Ns420p258 Ns420p1865 Ns420p1866 Ns420p261 Ns420p1865 267348708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 397494701) qz344 0 3 Ns420p1864 Ns420p258 Ns420p1865 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 397494701) qz345 0 3 Ns420p1866 Ns420p261 Ns420p1865 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1868 := nat_lit 3765280382157157109029713489876507516459028306823876659751302462890625 

noncomputable def Ns420p1869 := nat_lit 186300522677807886034553523306977203389669857194491357574462890625 

noncomputable def Ns420p1870 := nat_lit 11295468545426115711317071362582908594970305580757240996538758462890625 

noncomputable def Ns420p1871 := BSN.cos_dyadic_bound_f 144137425 268435456 3 2 268435456 134217728 Ns420p1868 Ns420p156 Ns420p1869 Ns420p1870 Ns420p159 Ns420p1869 230658771 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 144137425) qz346 0 2 Ns420p1868 Ns420p156 Ns420p1869 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 144137425) qz347 0 2 Ns420p1870 Ns420p159 Ns420p1869 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1872 := nat_lit 27130390001923617290171613009645199803504797864795285116435844990543150482173405839079687603091665731482095616 

noncomputable def Ns420p1873 := nat_lit 7266198649054944752352188236361650034344903658046140022112534229722520680895721947690717223022680150016 

noncomputable def Ns420p1874 := nat_lit 135548604875674599406508564233283373853323213011104648796904106330551620159709072709914210624461980981461323776 

noncomputable def Ns420p1875 := BSN.sin_dyadic_bound_f 373057354 268435456 4 3 268435456 134217728 Ns420p1872 Ns420p258 Ns420p1873 Ns420p1874 Ns420p261 Ns420p1873 264047953 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 373057354) qz344 0 3 Ns420p1872 Ns420p258 Ns420p1873 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 373057354) qz345 0 3 Ns420p1874 Ns420p261 Ns420p1873 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1876 := nat_lit 21528886793379346581624815842238416178609781109183771481740765438111207022857074659240173784575685031358365696 

noncomputable def Ns420p1877 := nat_lit 3633583515537678279612654409263548647900664175096906232041131465696952081391103843897256081769151594496 

noncomputable def Ns420p1878 := nat_lit 107579328604851344991546572210880787025259031647660767760277666051461637819386476096536298692403826828515475456 

noncomputable def Ns420p1879 := BSN.sin_dyadic_bound_f 352123164 268435456 4 3 268435456 134217728 Ns420p1876 Ns420p258 Ns420p1877 Ns420p1878 Ns420p261 Ns420p1877 259479785 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 352123164) qz344 0 3 Ns420p1876 Ns420p258 Ns420p1877 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 352123164) qz345 0 3 Ns420p1878 Ns420p261 Ns420p1877 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1880 := Ns420p1834 78807 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 265 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 264047953 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 153 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 259479785 268435456) qz222 rfl rfl (Ns420p1863 RS421to432.d9 RS421to432.d11 RS421to432.d13 RS421to432.d17 (Ns420p1867 rfl rfl) (Ns420p1871 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns420p1862 rfl) RS421to432.d19 RS421to432.d21 RS421to432.d23 RS421to432.d25 RS421to432.d17 (Ns420p1875 rfl rfl) (Ns420p1879 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns420p1881 := nat_lit 1790934231713177331454162487508173817201238885509789556527753714690625 

noncomputable def Ns420p1882 := nat_lit 42150355336374967873379558593201909990594776129225251462437890625 

noncomputable def Ns420p1883 := nat_lit 5372718394428859244426740703407335047783735466977110219080336268290625 

noncomputable def Ns420p1884 := BSN.cos_dyadic_bound_f 119701655 268435456 3 2 268435456 134217728 Ns420p1881 Ns420p156 Ns420p1882 Ns420p1883 Ns420p159 Ns420p1882 242185901 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 119701655) qz346 0 2 Ns420p1881 Ns420p156 Ns420p1882 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 119701655) qz347 0 2 Ns420p1883 Ns420p159 Ns420p1882 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1885 := nat_lit 6902439396156533677161126366801 

noncomputable def Ns420p1886 := BSN.sin_dyadic_bound_f 51256701 268435456 2 1 268435456 134217728 Ns420p1885 Ns420p133 Ns420p1885 Ns420p1885 Ns420p134 Ns420p1885 50945794 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 51256701) qz344 0 1 Ns420p1885 Ns420p133 Ns420p1885 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 51256701) qz345 0 1 Ns420p1885 Ns420p134 Ns420p1885 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1887 := Ns420p1832 106271 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 242185901 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 50945794 268435456) qz222 rfl rfl (Ns420p1880 rfl rfl) (Ns420p1862 rfl) RS421to432.d27 RS421to432.d29 RS421to432.d31 RS421to432.d33 RS421to432.d17 (Ns420p1884 rfl rfl) (Ns420p1886 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p1888 := nat_lit 28473726293687346351406126917136 

noncomputable def Ns420p1889 := BSN.cos_dyadic_bound_f 73048462 268435456 2 1 268435456 134217728 Ns420p1888 Ns420p285 Ns420p1888 Ns420p1888 Ns420p286 Ns420p1888 258557420 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 73048462) qz346 0 1 Ns420p1888 Ns420p285 Ns420p1888 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 73048462) qz347 0 1 Ns420p1888 Ns420p286 Ns420p1888 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1890 := nat_lit 5010707217577272048220723759227489767006091553033076130101194301440000 

noncomputable def Ns420p1891 := nat_lit 101835171421227429410991095730890862585830571104705777689600000000 

noncomputable def Ns420p1892 := nat_lit 13123115931948649567597134907631289852190815103685791769482106675200000 

noncomputable def Ns420p1893 := BSN.sin_dyadic_bound_f 133655620 268435456 3 2 268435456 134217728 Ns420p1890 Ns420p119 Ns420p1891 Ns420p1892 Ns420p122 Ns420p1891 128201235 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 133655620) qz344 0 2 Ns420p1890 Ns420p119 Ns420p1891 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 133655620) qz345 0 2 Ns420p1892 Ns420p122 Ns420p1891 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1894 := Ns420p1830 130268 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 82 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 258557420 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 141 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128201235 268435456) qz222 rfl rfl (Ns420p1887 rfl) (Ns420p1862 rfl) RS421to432.d35 RS421to432.d37 RS421to432.d39 RS421to432.d41 RS421to432.d17 (Ns420p1889 rfl rfl) (Ns420p1893 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p1895 := nat_lit 680189897377251273970898129778412712543189379820507405219465638445056 

noncomputable def Ns420p1896 := nat_lit 6080159860770716494941009638409768913916873642720333899839307776 

noncomputable def Ns420p1897 := nat_lit 2040557531812032280479704507315961318091740305714236774990597236719616 

noncomputable def Ns420p1898 := BSN.cos_dyadic_bound_f 93970032 268435456 3 2 268435456 134217728 Ns420p1895 Ns420p156 Ns420p1896 Ns420p1897 Ns420p159 Ns420p1896 252154899 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 93970032) qz346 0 2 Ns420p1895 Ns420p156 Ns420p1896 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 93970032) qz347 0 2 Ns420p1897 Ns420p159 Ns420p1896 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1899 := nat_lit 1434068916325878407694630691761 

noncomputable def Ns420p1900 := BSN.cos_dyadic_bound_f 34605291 268435456 2 1 268435456 134217728 Ns420p1899 Ns420p285 Ns420p1899 Ns420p1899 Ns420p286 Ns420p1899 266207977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 34605291) qz346 0 1 Ns420p1899 Ns420p285 Ns420p1899 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 34605291) qz347 0 1 Ns420p1899 Ns420p286 Ns420p1899 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1901 := Ns420p1828 151851 BSN.abs_quadSignNeg qz651 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 252154899 268435456) BSN.abs_quadSignNeg qz348 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 266207977 268435456) qz222 rfl rfl (Ns420p1894 rfl) (Ns420p1862 rfl) RS421to432.d43 RS421to432.d45 RS421to432.d47 RS421to432.d49 RS421to432.d17 (Ns420p1898 rfl rfl) (Ns420p1900 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p1902 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 11) 1212484146 268435456 151851 268435456 1212484146 268435456 151851 268435456 650947469248561152 606242073 67108864 151851 134217728 (Ns420p1901 rfl) 

noncomputable def Ns420p1903 := nat_lit 100296112368940785492384225226390572361702457222972635014215043053406766385127573044000930043854095813256069990058158746129726845463309 

noncomputable def Ns420p1904 := nat_lit 181709681073901722637330951972001133588410340171829515070372549795159822028349480831547762678440891390190630401566544483383650407153664 

noncomputable def Ns420p1905 := nat_lit 2067843849967289400242189505356191658374616284243234651745752810435155878982993207083235239681378232943868430356700296137018873747080436626214889793232193637693664701915359662695086567 

noncomputable def Ns420p1906 := @Enclosure.Real.IsNear.mulLit_tf qz218 qz520 626525 2097152 1 16777216 Ns420p1903 Ns420p1904 Ns420p1905 

noncomputable def Ns420p1907 := nat_lit 41141026461992110244162423595619919734736958947313654804521611480787081064740885582768397109482549769855190620303052834424750080000000000000000000000000000000000000000000000000000000000000 

noncomputable abbrev qz226 := (@HPow.hPow Real Real Real qz443 qz517 qz328)

noncomputable def Ns420p1908 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz226 1 1 0 1 626525 2097152 1 16777216 626525 2097152 1 16777216 

noncomputable abbrev qz227 := qz517

noncomputable def Ns420p1909 := @Enclosure.Real.IsNear.sqrt_image qz227 2106133756493 16777216000 394381 16777216000 187976206 187976243 16777216 (@Enclosure.Real.IsNear.of_eq qz227 (@HMul.hMul Real Real Real qz5 qz217 qz3) Bool.false 2106133756493 16777216000 394381 16777216000 (BSN.t_div_two_pi_mk qz217 788762 1000 qz222) (@Enclosure.Real.IsNear.mulLit_ff qz217 qz3 788762 1000 0 1 5340353 33554432 1 33554432 2106133756493 16777216000 394381 16777216000 (Enclosure.Real.IsNear.const Bool.false 788762 1000) RS421to432.d52 rfl)) 

noncomputable abbrev qz525 := (@Enclosure.Real.IsNear.recentre' qz221 Bool.false 375952449 33554432 37 33554432 375952449 33554432 37 33554432 (Ns420p1909 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns420p1910 := @Enclosure.Real.IsNear.sqrt_image qz221 375952449 33554432 37 33554432 56157968 56157974 16777216 qz525 rfl 

noncomputable def Ns420p1911 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz221) 56157971 16777216 3 16777216 5012199 5012201 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz221) Bool.false 112315942 33554432 6 33554432 56157971 16777216 3 16777216 (Ns420p1910 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p1912 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz221)) Bool.false 10024400 33554432 2 33554432 626525 2097152 1 16777216 (Ns420p1911 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns420p1913 := nat_lit 162362375222863267609624687386880576141798304155378918864904000815814280558420649660338755393365728700383459008787245747579601005325 

noncomputable def Ns420p1914 := nat_lit 60344888263373666145665209006689674827693389923906956431858355115539884071685555148801694319255570596941822606606553986239993747080436626214889793232193637693664701915359662695086567 

noncomputable abbrev qz526 := (@HMul.hMul Real Real Real qz5 qz733 (@Inv.inv Real Real.instInv qz221))

noncomputable def Ns420p1915 := @Enclosure.Real.IsNear.addLit_ff qz219 qz526 77555430125843 140737488355328 145073042778869 2973079441506304000 Ns420p1913 Ns420p1904 Ns420p1914 Ns420p1907 

noncomputable def Ns420p1916 := nat_lit 14115422946608472386775990416626342442311140529127635264765889905479320961326614675843814638614517753891564548285623073262912909301453885372578660352 

noncomputable abbrev qz848 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 788762 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1)))

noncomputable abbrev qz737 := (Real.cos qz848)

noncomputable abbrev qz527 := qz737

noncomputable abbrev qz228 := (@Inv.inv Real Real.instInv qz527)

noncomputable abbrev qz738 := (@HSub.hSub Real Real Real qz798 (@HMul.hMul Real Real Real qz795 qz845 qz845) qz845)

noncomputable abbrev qz528 := (@HMul.hMul Real Real Real qz619 qz617 (@HSub.hSub Real Real Real qz624 qz738 qz634))

noncomputable abbrev qz229 := (Real.cos qz528)

noncomputable def Ns420p1917 := @Enclosure.Real.IsNear.of_eq qz219 (@HMul.hMul Real Real Real qz5 qz228 qz229) Bool.false 77555430125843 

noncomputable def Ns420p1918 := @Enclosure.Real.IsNear.mulLit_ff qz228 qz229 59183779 16777216 1481 

noncomputable def Ns420p1919 := @Enclosure.Real.IsNear.recentre' qz228 Bool.false 118367558 33554432 2962 33554432 59183779 16777216 1481 

noncomputable abbrev qz230 := qz527

noncomputable def Ns420p1920 := @Enclosure.Real.IsNear.recentre' qz230 Bool.false 4755948 16777216 1608634432 226827960320000 1188987 4194304 25134913 3544186880000 

noncomputable abbrev qz739 := qz848

noncomputable abbrev qz529 := qz739

noncomputable abbrev qz231 := qz529

noncomputable def Ns420p1921 := @Enclosure.Real.IsNear.cos_image qz231 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5382881) qz643) Bool.false 5382881 4194304 233 33554432 Bool.false 4755948 16777216 1 

noncomputable def Ns420p1922 := nat_lit 998484790193502490784638403 

noncomputable def Ns420p1923 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz220 884279719003555 140737488355328 1 500000000000000 6853697 33554432 37 33554432 6060585257295507892835 4722366482869645213696 Ns420p1922 

noncomputable def Ns420p1924 := @Enclosure.Real.IsNear.subLit_ff_p qz221 qz1 375952449 33554432 37 33554432 11 1 0 1 6853697 6853697 33554432 37 

noncomputable def Ns420p1925 := @Ns420p1924 33554432 qz525 qz352 

noncomputable def Ns420p1926 := @Enclosure.Real.IsNear.recentre' qz231 Bool.false 6060585257295507892835 4722366482869645213696 Ns420p1922 Ns420p175 5382881 4194304 233 33554432 (@Ns420p1923 Ns420p175 RS421to432.d51 (Ns420p1925 rfl rfl) rfl) 

noncomputable def Ns420p1927 := nat_lit 1607551718968794335573702160962697277524808173618780734956761874753018945954907913267841 

noncomputable def Ns420p1928 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns420p1929 := nat_lit 591803251653631800177777604560426140010015829266047202393740455955298931009464961 

noncomputable def Ns420p1930 := nat_lit 9741995695205992776658567413281088084737433080075762297263591847968118075570473613994625 

noncomputable def Ns420p1931 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns420p1932 := BSN.cos_dyadic_bound_f 5382881 4194304 4 3 16777216 6760000 Ns420p1927 Ns420p1928 Ns420p1929 Ns420p1930 Ns420p1931 Ns420p1929 4755948 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 5382881) (BSN.cosEvenQ 4194304) 0 3 Ns420p1927 Ns420p1928 Ns420p1929 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 5382881) (BSN.cosOddQ 4194304) 0 3 Ns420p1930 Ns420p1931 Ns420p1929 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1933 := @Enclosure.Real.IsNear.inv_image qz230 1188987 4194304 25134913 3544186880000 59182298 59185260 16777216 (Ns420p1920 (@Ns420p1921 6760000 (Ns420p1926 rfl) (Enclosure.sfrac_false_div 5382881 4194304) (Ns420p1932 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns420p1934 := @Enclosure.Real.IsNear.recentre' qz229 Bool.false 2620834 16777216 

noncomputable abbrev qz232 := qz528

noncomputable def Ns420p1935 := @Enclosure.Real.IsNear.cos_image qz232 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 47443953)) qz342) Bool.true 47443953 33554432 

noncomputable def Ns420p1936 := nat_lit 224047734228011941818963329245 

noncomputable def Ns420p1937 := nat_lit 9438050272220605951805028032985201 

noncomputable def Ns420p1938 := @Enclosure.Real.IsNear.recentre' qz232 Bool.true Ns420p1936 Ns420p190 Ns420p1937 

noncomputable abbrev qz530 := (@HSub.hSub Real Real Real qz624 qz738 qz634)

noncomputable abbrev qz233 := qz530

noncomputable def Ns420p1939 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz233 884279719003555 140737488355328 1 500000000000000 253367491544959 

noncomputable abbrev qz531 := qz738

noncomputable abbrev qz234 := qz531

noncomputable def Ns420p1940 := @Enclosure.Real.IsNear.subLit_tf qz234 qz27 182998747367295 1125899906842624 1748688931 1125899906842624 1 16 

noncomputable abbrev qz740 := (@HMul.hMul Real Real Real qz795 qz845 qz845)

noncomputable abbrev qz532 := qz740

noncomputable abbrev qz235 := qz532

noncomputable def Ns420p1941 := @Enclosure.Real.IsNear.subLit_ff_n qz235 qz220 46973162567809 1125899906842624 507174947 1125899906842624 6853697 33554432 37 33554432 

noncomputable def Ns420p1942 := @Enclosure.Real.IsNear.mulLit_ff qz220 qz220 6853697 33554432 37 33554432 6853697 33554432 37 33554432 46973162567809 1125899906842624 

noncomputable def Ns420p1943 := nat_lit 162884844437264579322590519953917848711817018999373921827045029035817223977951429635702550722560321 

noncomputable def Ns420p1944 := nat_lit 130067982542904542851477167798082051195630436257218811783792254965151980292426204234330194241 

noncomputable def Ns420p1945 := nat_lit 986603811082918234669329336360052883442549885407829874319313366008047843153049109299273632761299265 

noncomputable def Ns420p1946 := BSN.cos_dyadic_bound_f 47443953 33554432 4 3 16777216 6760000 Ns420p1943 Ns420p1201 Ns420p1944 Ns420p1945 Ns420p1204 Ns420p1944 2620834 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 47443953) qz635 0 3 Ns420p1943 Ns420p1201 Ns420p1944 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 47443953) (BSN.cosOddQ 33554432) 0 3 Ns420p1945 Ns420p1204 Ns420p1944 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p1947 := @Ns420p1934 281354304 28353495040000 1310417 8388608 4396161 443023360000 (@Ns420p1935 41 4194304 Bool.false 2620834 16777216 1 6760000 (@Ns420p1938 Ns420p1596 47443953 33554432 41 4194304 (@Ns420p1939 1125899906842624 1748688931 1125899906842624 Ns420p1936 Ns420p190 Ns420p1937 Ns420p1596 RS421to432.d51 (@Ns420p1940 0 1 4053879864719344 253367491544959 1125899906842624 1748688931 1125899906842624 (@Ns420p1941 6140419024621079101440 182998747367295 1125899906842624 1748688931 1125899906842624 (@Ns420p1942 507174947 1125899906842624 (Ns420p1925 rfl rfl) (Ns420p1925 rfl rfl) rfl) (Ns420p1925 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 47443953 33554432) (BSN.cos_neg_of_bound 47443953 33554432 Bool.false 2620834 16777216 1 6760000 (Ns420p1946 rfl rfl)) rfl rfl) 

noncomputable def Ns420p1948 := nat_lit 54214890719613431582625138828253096672056567567567748042987946350821001838330946299239632052487677345440389038169665064523525 

noncomputable def Ns420p1949 := nat_lit 5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991351228465152 

noncomputable def Ns420p1950 := nat_lit 40291661749636499677381302535151899315987508431237545359837654281656165866282398973042626587100078856169037805782716129505273932178983821506180590994844397766170954317072741611 

noncomputable def Ns420p1951 := nat_lit 2452196267961985483417655443884129508420047697264769959719277112530891958757691716120743579237613068214368261116925050880000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1952 := @Enclosure.Real.IsNear.mulLit_ff qz733 (@Inv.inv Real Real.instInv qz221) Ns420p1948 Ns420p1949 Ns420p1950 Ns420p1951 2994793 33554432 1 33554432 Ns420p1913 

noncomputable def Ns420p1953 := nat_lit 5979979049306985221113536755050795088107838555303832195701614200603304811042202346313967462681191010990806602043605575 

noncomputable def Ns420p1954 := nat_lit 630432099142311667396464641602297820881275828327447146687172694467931548343955369782628260078158650252906047844909056 

noncomputable def Ns420p1955 := nat_lit 17775712199144618308633764707791590039215704774283190944399475598427385517010592432726241765299555188031664304565958006830925196478297738678762655591316587440784674557183 

noncomputable def Ns420p1956 := nat_lit 1141892870870412086796786377152488338025309004478515107053926732638334836232332380544740510749450450862929346560000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1957 := @Enclosure.Real.IsNear.mulLit_tf (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz220) qz461 Ns420p1953 Ns420p1954 Ns420p1955 Ns420p1956 9066067 8589934592 1 8589934592 Ns420p1948 

noncomputable abbrev qz849 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 788762 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1)))

noncomputable abbrev qz741 := (@HMul.hMul Real Real Real qz795 qz793 (@HSub.hSub Real Real Real qz798 qz849 qz836))

noncomputable abbrev qz533 := (@HMul.hMul Real Real Real qz619 qz741 qz741)

noncomputable abbrev qz534 := qz741

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz326 qz533 qz534)

noncomputable abbrev qz237 := (Real.sin qz528)

noncomputable abbrev qz238 := (@HMul.hMul Real Real Real qz326 qz318 qz534)

noncomputable def Ns420p1958 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz236 qz237) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz238 qz158) qz229) 

noncomputable abbrev qz742 := (Real.sin qz848)

noncomputable abbrev qz535 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz619 qz617 qz742))

noncomputable abbrev qz239 := (@HMul.hMul Real Real Real qz326 qz318 qz535)

noncomputable abbrev qz536 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz619 qz701 qz737))

noncomputable abbrev qz240 := (@HMul.hMul Real Real Real qz326 qz318 qz536)

noncomputable abbrev qz537 := qz742

noncomputable abbrev qz241 := qz537

noncomputable def Ns420p1959 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns420p1958 (@HMul.hMul Real Real Real qz5 qz239 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz220))) (@HMul.hMul Real Real Real qz5 qz240 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz220))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz469 qz241) qz219) 

noncomputable abbrev qz242 := (BSN.cos_two_pi_p_ne_zero_mk qz516 788762 1000 11 qz521 rfl rfl (@BSN.floor_sqrt_eq_dec qz516 788762 1000 11 qz521 rfl rfl rfl))

noncomputable def Ns420p1960 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz220) (@HMul.hMul Real Real Real qz5 qz228 Ns420p1959) Bool.true Ns420p1953 Ns420p1954 Ns420p1955 Ns420p1956 (BSN.iteratedDeriv_three_correction_mk qz220 qz242) 

noncomputable def Ns420p1961 := nat_lit 394684532202685939854790150322745670950215444814721380524199633529158394198701498369098593997157714197414525 

noncomputable def Ns420p1962 := nat_lit 146783911423364576743092537299333564210980159306769991919205685720763064069663027716481187399048043939495936 

noncomputable def Ns420p1963 := nat_lit 1173146343169916112476049155198809405482366033026856633929129868110070710114296373933323156459048186619594061147036871773516866873050107947321982642809423796729 

noncomputable def Ns420p1964 := @Enclosure.Real.IsNear.mulLit_ft qz228 Ns420p1959 15151288083 4294967296 361 1073741824 Ns420p1961 Ns420p1962 Ns420p1963 

noncomputable def Ns420p1965 := nat_lit 265867652108523083570596384152883742476186948939812161739432889185458150746378204912119663960638095360000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1966 := @Enclosure.Real.IsNear.recentre' qz228 Bool.false 30302576166 8589934592 2888 8589934592 15151288083 4294967296 361 

noncomputable def Ns420p1967 := @Enclosure.Real.IsNear.recentre' qz230 Bool.false 1217503355 4294967296 401427054592 14865397207531520000 1217503355 4294967296 24501163 907311841280000 

noncomputable def Ns420p1968 := @Enclosure.Real.IsNear.cos_image qz231 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5512090331) qz727) Bool.false 5512090331 4294967296 227 8589934592 Bool.false 1217503355 4294967296 1 

noncomputable def Ns420p1969 := nat_lit 242874682449269955433382911 

noncomputable def Ns420p1970 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz220 884279719003555 140737488355328 1 500000000000000 877276423 4294967296 9 2147483648 775757748818883854683765 604462909807314587353088 Ns420p1969 

noncomputable def Ns420p1971 := @Enclosure.Real.IsNear.subLit_ff_p qz221 qz1 48121916679 4294967296 9 2147483648 11 1 0 1 877276423 877276423 4294967296 9 

noncomputable def Ns420p1972 := @Enclosure.Real.IsNear.sqrt_image qz227 539170313833931 4294967296000 394381 4294967296000 48121916661 48121916697 4294967296 (@Enclosure.Real.IsNear.of_eq qz227 (@HMul.hMul Real Real Real qz5 qz217 qz3) Bool.false 539170313833931 4294967296000 394381 4294967296000 (BSN.t_div_two_pi_mk qz217 788762 1000 qz222) (@Enclosure.Real.IsNear.mulLit_ff qz217 qz3 788762 1000 0 1 1367130551 8589934592 1 8589934592 539170313833931 4294967296000 394381 4294967296000 (Enclosure.Real.IsNear.const Bool.false 788762 1000) RS421to432.d67 rfl)) 

noncomputable def Ns420p1973 := @Ns420p1971 2147483648 (@Enclosure.Real.IsNear.recentre' qz221 Bool.false 96243833358 8589934592 36 8589934592 48121916679 4294967296 9 2147483648 (Ns420p1972 rfl rfl rfl rfl rfl rfl) rfl) qz352 

noncomputable def Ns420p1974 := @Enclosure.Real.IsNear.recentre' qz231 Bool.false 775757748818883854683765 604462909807314587353088 Ns420p1969 Ns420p1628 5512090331 4294967296 227 8589934592 (@Ns420p1970 Ns420p1628 RS421to432.d66 (Ns420p1973 rfl rfl) rfl) 

noncomputable def Ns420p1975 := nat_lit 2136834102863048390476940171070829741172871510011452425361930798899447603477563900800700932636307604226151772682689686604241 

noncomputable def Ns420p1976 := nat_lit 786676022043911527198205891889523978241340797016404373201438492407030379407900782231815363728611686885217721489361361 

noncomputable def Ns420p1977 := nat_lit 12949523214745139242905556845699032158037181366068514742514321770761246922229333335115894141621596367353430368127586888387025 

noncomputable def Ns420p1978 := BSN.cos_dyadic_bound_f 5512090331 4294967296 4 3 4294967296 1730560000 Ns420p1975 Ns420p1713 Ns420p1976 Ns420p1977 Ns420p1715 Ns420p1976 1217503355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 5512090331) (BSN.cosEvenQ 4294967296) 0 3 Ns420p1975 Ns420p1713 Ns420p1976 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 5512090331) (BSN.cosOddQ 4294967296) 0 3 Ns420p1977 Ns420p1715 Ns420p1976 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz538 := (Ns420p1967 (@Ns420p1968 1730560000 (Ns420p1974 rfl) (Enclosure.sfrac_false_div 5512090331 4294967296) (Ns420p1978 rfl rfl) rfl rfl) rfl)

noncomputable def Ns420p1979 := @Enclosure.Real.IsNear.inv_image qz230 1217503355 4294967296 24501163 907311841280000 15151286639 15151289527 4294967296 qz538 rfl 

noncomputable def Ns420p1980 := @Enclosure.Real.IsNear.subLit_ff_n (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns420p1958 (@HMul.hMul Real Real Real qz5 qz239 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz220))) (@HMul.hMul Real Real Real qz5 qz240 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz220))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz469 qz241) qz219) 

noncomputable def Ns420p1981 := nat_lit 18846403566255653800789103976164846100728136803699416135542738621986683327736175805915301210305243051623513475 

noncomputable def Ns420p1982 := nat_lit 1160403324374537409582844070603239055737648027453363358116452682303616871893673429043560962348289624300275426076271121135148995214883881786791116230879823796729 

noncomputable def Ns420p1983 := nat_lit 1809423229072938276687646935461291159542975536725927182533005125594181625 

noncomputable def Ns420p1984 := nat_lit 13803492693581127574869511724554050904902217944340773110325048447598592 

noncomputable def Ns420p1985 := nat_lit 1678299399196375088327938652893714869726512476114991089901140202134921461527363125784831006910255103821965843 

noncomputable def Ns420p1986 := nat_lit 35015684114136521346858199553951984474667846454948689398988800000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1987 := nat_lit 5448025056529260630796887905790481864206339384831045122966636207324191213520752516155486987325087385813076449128999354235908461412133995520587966369195804635308823223351430348800 

noncomputable def Ns420p1988 := nat_lit 24937657548284923571442099996106878340690059103131905670343709611049991322498988570171759575449296725771353475 

noncomputable def Ns420p1989 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 Ns420p1958 (@HMul.hMul Real Real Real qz5 qz239 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz220))) (@HMul.hMul Real Real Real qz5 qz240 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz220)) Ns420p1988 Ns420p1962 

noncomputable def Ns420p1990 := nat_lit 1114006697247700874654948982261823933302412764535785725908667549348095230918142644484693383769169024898468008223583153472228919695449782962193345603420506036729 

noncomputable def Ns420p1991 := nat_lit 10566641280763382511770694140062404747726913615117077969303724017015498606105622308060883125 

noncomputable def Ns420p1992 := nat_lit 254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672 

noncomputable def Ns420p1993 := nat_lit 23812224344102276379099323593655071010234967471674274835463900193471983618749344196141841867793895318602348322116898441514190056325879 

noncomputable def Ns420p1994 := nat_lit 136451733022334215799866026020214812455403867532708951482111870509680460293996544000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns420p1995 := nat_lit 4798850261122665771840134135354233464618896551768779886567560872164566812275875620695014879863778759206849911295708258858665767130324584840801321672592028142271126755110505623723810982887282651955200 

noncomputable def Ns420p1996 := nat_lit 1075828442964296712327701263402255774688090670116056201624699152108840556045191875 

noncomputable def Ns420p1997 := nat_lit 14821387422376473014217086081112052205218558037201992197050570753012880593911808 

noncomputable def Ns420p1998 := nat_lit 215969676209318959417680865675468166138842547535894775905920690619158087953335931490998315296410564653311776269 

noncomputable def Ns420p1999 := nat_lit 22247221614982705689935183348175378827366588903365999752473194004480000000000000000000000000000000000000000000000000 

noncomputable def Ns420p2000 := @Enclosure.Real.IsNear.subLit_ft Ns420p1958 (@HMul.hMul Real Real Real qz5 qz239 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz220)) Ns420p1996 Ns420p1997 Ns420p1998 Ns420p1999 

noncomputable def Ns420p2001 := nat_lit 14283168708704515855730307478384335205309037228268312454295837385820551949555386365533427038137813497447513475 

noncomputable def Ns420p2002 := nat_lit 1111425729982029384488171123832769704330609638748674222093654964212204776487413762260385933386705369920975859732623603512958579070025572278585699395420506036729 

noncomputable def Ns420p2003 := nat_lit 369610683929681878998719553340536749169191051693816850560177632362486800438224083259092457672013208684380990253852494674406820119885596134766958332607214177197913364292082439102736944332800 

noncomputable def Ns420p2004 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz5 qz236 qz237) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz238 qz158) qz229) 

noncomputable def Ns420p2005 := nat_lit 751446506853187721043210086700859395902369821889689735608176576813297812513671875 

noncomputable def Ns420p2006 := nat_lit 91152789742415255329967279821717578463897229516154840331483238688208798634029358244409616541338564653311776269 

noncomputable def Ns420p2007 := nat_lit 499789507339753626486697285139399327791196506875 

noncomputable def Ns420p2008 := nat_lit 22835963083295358096932575511191922182123945984 

noncomputable def Ns420p2009 := nat_lit 6301642370889594494618052909253057470133913894391847109540682565983 

noncomputable def Ns420p2010 := nat_lit 1123197656438253912603716965936891166720000000000000000000000000000000000 

noncomputable def Ns420p2011 := nat_lit 24567578607491805451313527582390780126535430123520330836081863475128235836091661901191006682801993268039555558076799705415680000 

noncomputable def Ns420p2012 := nat_lit 1417074652492554856650281521496280204463126494599826216013830744607421875 

noncomputable def Ns420p2013 := @Enclosure.Real.IsNear.mulLit_tt qz236 qz237 Ns420p2012 Ns420p1670 

noncomputable def Ns420p2014 := nat_lit 856115039200363849867584474270171044898446373128813117150978455504476687488736322440739839528883 

noncomputable def Ns420p2015 := nat_lit 1261619771783400754064437370645921444698803765625 

noncomputable def Ns420p2016 := nat_lit 4162618063697350570637750304360109368101043037813501129868217 

noncomputable def Ns420p2017 := nat_lit 10633823966279326983230456482242756608000000000000000000000000000000 

noncomputable abbrev qz243 := qz533

noncomputable abbrev qz244 := qz534

noncomputable def Ns420p2018 := @Enclosure.Real.IsNear.mulLit_ft qz243 qz244 Ns420p2015 Ns420p1665 Ns420p2016 Ns420p2017 

noncomputable def Ns420p2019 := nat_lit 242874684136894899614434303 

noncomputable def Ns420p2020 := @Enclosure.Real.IsNear.mulLit_tt qz244 qz244 1123218487999285361684875 302231454903657293676544 Ns420p2019 Ns420p1324 1123218487999285361684875 302231454903657293676544 

noncomputable abbrev qz743 := (@HSub.hSub Real Real Real qz798 qz849 qz836)

noncomputable abbrev qz539 := qz743

noncomputable abbrev qz245 := qz539

noncomputable def Ns420p2021 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz245 884279719003555 140737488355328 1 500000000000000 1270207225 2147483648 9 1073741824 

noncomputable abbrev qz744 := qz849

noncomputable abbrev qz540 := qz744

noncomputable abbrev qz246 := qz540

noncomputable def Ns420p2022 := @Enclosure.Real.IsNear.subLit_ff_n qz246 qz171 877276423 2147483648 9 1073741824 1 1 0 1 1270207225 

noncomputable def Ns420p2023 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz220 2 1 0 1 877276423 4294967296 9 2147483648 877276423 2147483648 9 

noncomputable def Ns420p2024 := @Enclosure.Real.IsNear.recentre' qz237 Bool.true 4242240904 4294967296 

noncomputable def Ns420p2025 := @Enclosure.Real.IsNear.sin_image qz232 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6072837923)) qz727) Bool.true 6072837923 4294967296 

noncomputable def Ns420p2026 := nat_lit 3670805281924224365561919026776525 

noncomputable def Ns420p2027 := nat_lit 9182970517911356130351043937453731 

noncomputable def Ns420p2028 := @Enclosure.Real.IsNear.recentre' qz232 Bool.true Ns420p2026 Ns420p1686 Ns420p2027 

noncomputable def Ns420p2029 := nat_lit 247588007857076054979824844800000000000000 

noncomputable def Ns420p2030 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz233 884279719003555 140737488355328 1 500000000000000 4151181128592034255 

noncomputable def Ns420p2031 := @Enclosure.Real.IsNear.subLit_tf qz234 qz27 2998259623985187279 18446744073709551616 1701427545 288230376151711744 1 16 

noncomputable def Ns420p2032 := @Enclosure.Real.IsNear.subLit_ff_n qz235 qz220 769613922351674929 18446744073709551616 493467993 288230376151711744 877276423 4294967296 9 2147483648 

noncomputable def Ns420p2033 := nat_lit 12877427029933636551740227584 

noncomputable def Ns420p2034 := @Enclosure.Real.IsNear.mulLit_ff qz220 qz220 877276423 4294967296 9 2147483648 877276423 4294967296 9 2147483648 769613922351674929 18446744073709551616 

noncomputable def Ns420p2035 := nat_lit 8183112096267526690065709073588542970845525078357099715448419284331154110926831892831292551718723029915351412425879179409521 

noncomputable def Ns420p2036 := nat_lit 2515940032845191040474896472083733965233698322540075357598957673833344161748200384916019235137678324470412021479159921 

noncomputable def Ns420p2037 := nat_lit 40882163487769877988481937241929492478374561419050322888269753603554986276261752469214896767625015307201632353359539940538481 

noncomputable def Ns420p2038 := BSN.sin_dyadic_bound_f 6072837923 4294967296 4 3 4294967296 1730560000 Ns420p2035 Ns420p1696 Ns420p2036 Ns420p2037 Ns420p1699 Ns420p2036 4242240904 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 6072837923) (BSN.sinEvenQ 4294967296) 0 3 Ns420p2035 Ns420p1696 Ns420p2036 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 6072837923) (BSN.sinOddQ 4294967296) 0 3 Ns420p2037 Ns420p1699 Ns420p2036 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2039 := @Ns420p2024 8787017728 232271831367680000 530280113 536870912 536317 14176747520000 (@Ns420p2025 5 134217728 Bool.true 4242240904 4294967296 1 1730560000 (@Ns420p2028 Ns420p2029 6072837923 4294967296 5 134217728 (@Ns420p2030 18446744073709551616 1701427545 288230376151711744 Ns420p2026 Ns420p1686 Ns420p2027 Ns420p2029 RS421to432.d66 (@Ns420p2031 0 1 66418898057472548080 4151181128592034255 18446744073709551616 1701427545 288230376151711744 (@Ns420p2032 Ns420p2033 2998259623985187279 18446744073709551616 1701427545 288230376151711744 (@Ns420p2034 493467993 288230376151711744 (Ns420p1973 rfl rfl) (Ns420p1973 rfl rfl) rfl) (Ns420p1973 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6072837923 4294967296) (BSN.sin_neg_of_bound 6072837923 4294967296 Bool.false 4242240904 4294967296 1 1730560000 (Ns420p2038 rfl rfl)) rfl rfl) 

noncomputable def Ns420p2040 := nat_lit 2979717986842817920669056273032744191875 

noncomputable def Ns420p2041 := nat_lit 19662704064865479075470306031868640192839184957625003 

noncomputable def Ns420p2042 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz238 qz158) qz229 Ns420p2040 Ns420p1703 Ns420p2041 

noncomputable def Ns420p2043 := nat_lit 3369655463997856085054625 

noncomputable def Ns420p2044 := nat_lit 728624052410684698843302909 

noncomputable def Ns420p2045 := @Enclosure.Real.IsNear.mulLit_tf qz238 qz158 Ns420p2043 302231454903657293676544 Ns420p2044 Ns420p1324 884279719003555 

noncomputable def Ns420p2046 := @Enclosure.Real.IsNear.mulLit_ft qz318 qz244 3 1 0 1 1123218487999285361684875 302231454903657293676544 Ns420p2019 

noncomputable def Ns420p2047 := @Enclosure.Real.IsNear.recentre' qz229 Bool.false 670921892 4294967296 

noncomputable def Ns420p2048 := @Enclosure.Real.IsNear.cos_image qz232 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6072837923)) qz727) Bool.true 6072837923 4294967296 

noncomputable def Ns420p2049 := nat_lit 3150675940300235137490409922273066537601209820262655307213232334463048405219427279153813550526352672776548363026758336166001 

noncomputable def Ns420p2050 := nat_lit 19083843326526981015610959913276383678560449444092233260229520133398551936861868477183161449629186237376639626529154963781745 

noncomputable def Ns420p2051 := BSN.cos_dyadic_bound_f 6072837923 4294967296 4 3 4294967296 1730560000 Ns420p2049 Ns420p1713 Ns420p2036 Ns420p2050 Ns420p1715 Ns420p2036 670921892 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6072837923) (BSN.cosEvenQ 4294967296) 0 3 Ns420p2049 Ns420p1713 Ns420p2036 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6072837923) (BSN.cosOddQ 4294967296) 0 3 Ns420p2050 Ns420p1715 Ns420p2036 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2052 := @Ns420p2047 8787017728 232271831367680000 167730473 1073741824 536317 14176747520000 (@Ns420p2048 5 134217728 Bool.false 670921892 4294967296 1 1730560000 (@Ns420p2028 Ns420p2029 6072837923 4294967296 5 134217728 (@Ns420p2030 18446744073709551616 1701427545 288230376151711744 Ns420p2026 Ns420p1686 Ns420p2027 Ns420p2029 RS421to432.d66 (@Ns420p2031 0 1 66418898057472548080 4151181128592034255 18446744073709551616 1701427545 288230376151711744 (@Ns420p2032 Ns420p2033 2998259623985187279 18446744073709551616 1701427545 288230376151711744 (@Ns420p2034 493467993 288230376151711744 (Ns420p1973 rfl rfl) (Ns420p1973 rfl rfl) rfl) (Ns420p1973 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6072837923 4294967296) (BSN.cos_neg_of_bound 6072837923 4294967296 Bool.false 670921892 4294967296 1 1730560000 (Ns420p2051 rfl rfl)) rfl rfl) 

noncomputable abbrev qz247 := (@Ns420p2021 1123218487999285361684875 302231454903657293676544 Ns420p2019 Ns420p1324 RS421to432.d66 (@Ns420p2022 1270207225 2147483648 9 1073741824 (@Ns420p2023 1073741824 qz323 (Ns420p1973 rfl rfl) rfl) (Enclosure.Real.IsNear.const Bool.false 1 1) rfl rfl) rfl)

noncomputable def Ns420p2053 := @Ns420p2004 Ns420p2005 Ns420p1997 Ns420p2006 Ns420p1999 Ns420p2007 Ns420p2008 Ns420p2009 Ns420p2010 Ns420p2011 Ns420p1996 Ns420p1997 Ns420p1998 Ns420p1999 (@Ns420p2013 Ns420p2014 Ns420p1673 530280113 536870912 536317 14176747520000 Ns420p2005 Ns420p1997 Ns420p2006 Ns420p1999 (@Ns420p2018 1123218487999285361684875 302231454903657293676544 Ns420p2019 Ns420p1324 Ns420p2012 Ns420p1670 Ns420p2014 Ns420p1673 (@Ns420p2020 Ns420p2019 Ns420p1324 Ns420p2015 Ns420p1665 Ns420p2016 Ns420p2017 qz247 qz247 rfl) qz247 rfl) (Ns420p2039 rfl) rfl) (@Ns420p2042 Ns420p1352 167730473 1073741824 536317 14176747520000 Ns420p2007 Ns420p2008 Ns420p2009 Ns420p2010 (@Ns420p2045 70368744177664 1 250000000000000 Ns420p2040 Ns420p1703 Ns420p2041 Ns420p1352 (@Ns420p2046 Ns420p1324 Ns420p2043 302231454903657293676544 Ns420p2044 Ns420p1324 qz474 qz247 rfl) RS421to432.d68 rfl) (Ns420p2052 rfl) rfl) rfl rfl 

noncomputable def Ns420p2054 := nat_lit 2731621733803905472378905 

noncomputable def Ns420p2055 := nat_lit 1983570719404000191757599158065863 

noncomputable def Ns420p2056 := nat_lit 5228823790625858150741682625176347907551103425534133494522300355172778901105072473595 

noncomputable def Ns420p2057 := @Enclosure.Real.IsNear.mulLit_tf qz239 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz220) Ns420p2054 151115727451828646838272 Ns420p2055 Ns420p1367 Ns420p2056 

noncomputable def Ns420p2058 := nat_lit 971334446112864535459730953411759453321203419526069760625906204869452142602604249088 

noncomputable def Ns420p2059 := nat_lit 15767699750691608332206726163027982650769932835130901204712163969711400145901312646422200230938217079832116717886357783 

noncomputable def Ns420p2060 := nat_lit 68225866511167107899933013010107406227701933766354475741055935254840230146998272000000000000000000000000000000000000000000 

noncomputable def Ns420p2061 := nat_lit 661190239801333397252533052688621 

noncomputable abbrev qz248 := qz535

noncomputable def Ns420p2062 := @Enclosure.Real.IsNear.mulLit_ft qz318 qz248 3 1 0 1 910540577934635157459635 151115727451828646838272 Ns420p2061 

noncomputable def Ns420p2063 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz241 884279719003555 140737488355328 1 500000000000000 1029697457 1073741824 24501163 907311841280000 910540577934635157459635 

noncomputable def Ns420p2064 := @Enclosure.Real.IsNear.recentre' qz241 Bool.false 4118789828 4294967296 401427054592 14865397207531520000 1029697457 1073741824 24501163 907311841280000 

noncomputable def Ns420p2065 := @Enclosure.Real.IsNear.sin_image qz231 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5512090331) qz727) Bool.false 5512090331 4294967296 227 8589934592 Bool.false 4118789828 4294967296 1 

noncomputable def Ns420p2066 := nat_lit 5551786544915002172552226912067830485290124728872808197341860805711154867341449947618362794376248222356149830423512612407761 

noncomputable def Ns420p2067 := nat_lit 27743548967551853975456080707293471933160030636455675875640275646633859740931787694902881178085540081765029348189144098605521 

noncomputable def Ns420p2068 := BSN.sin_dyadic_bound_f 5512090331 4294967296 4 3 4294967296 1730560000 Ns420p2066 Ns420p1696 Ns420p1976 Ns420p2067 Ns420p1699 Ns420p1976 4118789828 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 5512090331) (BSN.sinEvenQ 4294967296) 0 3 Ns420p2066 Ns420p1696 Ns420p1976 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 5512090331) (BSN.sinOddQ 4294967296) 0 3 Ns420p2067 Ns420p1699 Ns420p1976 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz541 := (@HMul.hMul Real Real Real qz619 qz617 qz742)

noncomputable abbrev qz249 := qz541

noncomputable abbrev qz542 := (@Enclosure.Real.IsNear.neg qz249 Bool.false 910540577934635157459635 151115727451828646838272 Ns420p2061 Ns420p1367 (@Ns420p2063 151115727451828646838272 Ns420p2061 Ns420p1367 RS421to432.d66 (Ns420p2064 (@Ns420p2065 1730560000 (Ns420p1974 rfl) (Enclosure.sfrac_false_div 5512090331 4294967296) (Ns420p2068 rfl rfl) rfl rfl) rfl) rfl))

noncomputable def Ns420p2069 := @Ns420p2062 Ns420p1367 Ns420p2054 151115727451828646838272 Ns420p2055 Ns420p1367 qz474 qz542 rfl 

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz326 qz533 (Real.cos qz528))

noncomputable def Ns420p2070 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz250) (@HMul.hMul Real Real Real qz5 qz158 qz237) 

noncomputable abbrev qz251 := (@HMul.hMul Real Real Real qz326 qz316 qz535)

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz326 qz536 (Zeta.RiemannSiegel.correction qz518))

noncomputable def Ns420p2071 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz220) (@HMul.hMul Real Real Real qz5 qz228 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns420p2070 (@HMul.hMul Real Real Real qz5 qz251 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz220))) qz252)) 

noncomputable def Ns420p2072 := @Enclosure.Real.IsNear.mulLit_ff qz228 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns420p2070 (@HMul.hMul Real Real Real qz5 qz251 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz220))) qz252) 15151288083 

noncomputable def Ns420p2073 := nat_lit 345107542143079331134494845653602236212665076387098717573918916763875705465 

noncomputable def Ns420p2074 := nat_lit 226156424291633194186662080095093570025917938800079226639565593765455331328 

noncomputable def Ns420p2075 := nat_lit 1038373466033400265794727808465423211077690570964234966259089294159913396832517307587417388834800202619674529 

noncomputable def Ns420p2076 := nat_lit 15885072413638026430255969290180924867210428641725907973259672349048832000000000000000000000000000000000000000000 

noncomputable def Ns420p2077 := nat_lit 1049592350550877709241665603777939232009497177897606592006417096780383878535 

noncomputable def Ns420p2078 := @Enclosure.Real.IsNear.subLit_tt_p (@HSub.hSub Real Real Real qz11 Ns420p2070 (@HMul.hMul Real Real Real qz5 qz251 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz220))) qz252 Ns420p2077 Ns420p2074 

noncomputable def Ns420p2079 := nat_lit 995980619063748025171689893149985849439808818622231592848691374952416920640205736253037078435662056069914529 

noncomputable def Ns420p2080 := nat_lit 2419418645798541018341055399961429577368053370012126508625 

noncomputable def Ns420p2081 := nat_lit 21757357056730173984440195375452692599956503064837245977084186614719171869338142429 

noncomputable def Ns420p2082 := nat_lit 135392196980084708481772182407861227032885824285637868113998855938025607100796395609661369070290858825739590240500520818408727511040 

noncomputable def Ns420p2083 := nat_lit 1005763324209901453557166411706468078270925398310698241695 

noncomputable def Ns420p2084 := nat_lit 98079714615416886934934209737619787751599303819750539264 

noncomputable def Ns420p2085 := nat_lit 638622215870996177704179034394108047718406118383708297732598773722639664031 

noncomputable def Ns420p2086 := nat_lit 603012150168268049747125822092411695121710448640000000000000000000000000000000000 

noncomputable def Ns420p2087 := @Enclosure.Real.IsNear.subLit_ff_n Ns420p2070 (@HMul.hMul Real Real Real qz5 qz251 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz220)) Ns420p2083 Ns420p2084 Ns420p2085 Ns420p2086 

noncomputable def Ns420p2088 := nat_lit 3368724680603804964032467075202089758811389543160429917589612388182639607175 

noncomputable def Ns420p2089 := nat_lit 979157475216251830615547226056071912001982578717871803719483469042588506606096933432683511959796763269914529 

noncomputable def Ns420p2090 := nat_lit 102943718204554685098139058499432518899829575785616240864537662819757734512526194345341313636055053117822286058571623710998124298240 

noncomputable def Ns420p2091 := @Enclosure.Real.IsNear.subLit_tt_p (@Neg.neg Real Real.instNeg qz250) (@HMul.hMul Real Real Real qz5 qz158 qz237) 

noncomputable def Ns420p2092 := nat_lit 211612081067381862027784752657316719440173698142462390625 

noncomputable def Ns420p2093 := nat_lit 351953111928573191263844165434050752308473976363958608568822773722639664031 

noncomputable def Ns420p2094 := nat_lit 14473091125434631756428971034539 

noncomputable def Ns420p2095 := nat_lit 30444333481024552960000000000000000000 

noncomputable def Ns420p2096 := nat_lit 37996664095587160142492491307813282231122204512466097366355071654334557858037760 

noncomputable def Ns420p2097 := @Enclosure.Real.IsNear.neg qz250 Bool.false Ns420p2092 

noncomputable def Ns420p2098 := @Enclosure.Real.IsNear.mulLit_ff qz243 qz229 Ns420p2015 Ns420p1665 Ns420p2016 

noncomputable def Ns420p2099 := @Enclosure.Real.IsNear.mulLit_ft qz158 qz237 884279719003555 70368744177664 1 

noncomputable def Ns420p2100 := nat_lit 3699697478881204904617136567347640216108995206333405 

noncomputable def Ns420p2101 := @Enclosure.Real.IsNear.mulLit_tt qz251 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz220) 910540577934635157459635 75557863725914323419136 Ns420p2061 Ns420p1418 Ns420p2100 

noncomputable def Ns420p2102 := nat_lit 41417232592272555843917410569793093122763694248524856019394301110149 

noncomputable def Ns420p2103 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz248 2 1 0 1 910540577934635157459635 151115727451828646838272 Ns420p2061 

noncomputable def Ns420p2104 := @Ns420p2103 Ns420p1367 910540577934635157459635 75557863725914323419136 Ns420p2061 Ns420p1418 qz323 qz542 rfl 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz326 qz534 (Real.sin qz528))

noncomputable def Ns420p2105 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz253) (@HMul.hMul Real Real Real qz5 qz248 qz219) 

noncomputable def Ns420p2106 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz220) (@HMul.hMul Real Real Real qz5 qz228 Ns420p2105) Bool.true Ns420p2100 Ns420p1807 Ns420p2102 Ns420p1423 (BSN.deriv_correction_mk qz220 qz242) 

noncomputable def Ns420p2107 := nat_lit 244183693070447765217714299555084251123535 

noncomputable def Ns420p2108 := nat_lit 696898287454081973172991196020261297061888 

noncomputable def Ns420p2109 := nat_lit 2670189955158034281573204454276981986377822175719701161987 

noncomputable def Ns420p2110 := @Enclosure.Real.IsNear.mulLit_ft qz228 Ns420p2105 15151288083 4294967296 361 1073741824 Ns420p2107 Ns420p2108 Ns420p2109 

noncomputable def Ns420p2111 := nat_lit 1898204039380649112300281672433346071756800000000000000000000000 

noncomputable def Ns420p2112 := @Enclosure.Real.IsNear.subLit_tt_n (@Neg.neg Real Real.instNeg qz253) (@HMul.hMul Real Real Real qz5 qz248 qz219) 

noncomputable def Ns420p2113 := nat_lit 595620426739950185513501385390875 

noncomputable def Ns420p2114 := nat_lit 50371264375668188992118594691718990916329 

noncomputable def Ns420p2115 := nat_lit 261514833299036583072439992320000000000000000000 

noncomputable def Ns420p2116 := nat_lit 2313986560607202178231907117149416050700465 

noncomputable def Ns420p2117 := nat_lit 2304570398131720888095107257814025253444717700453612201987 

noncomputable def Ns420p2118 := nat_lit 39621069451097452796367056610003279043469547148116347937706414573071892480 

noncomputable def Ns420p2119 := @Enclosure.Real.IsNear.neg qz253 Bool.false Ns420p2113 

noncomputable def Ns420p2120 := @Enclosure.Real.IsNear.mulLit_tt qz244 qz237 1123218487999285361684875 302231454903657293676544 Ns420p2019 

noncomputable def Ns420p2121 := @Enclosure.Real.IsNear.mulLit_tf qz248 qz219 910540577934635157459635 151115727451828646838272 Ns420p2061 Ns420p1367 2541332716720853259 4611686018427387904 

noncomputable def Ns420p2122 := @Enclosure.Real.IsNear.of_eq qz219 (@HMul.hMul Real Real Real qz5 qz228 qz229) Bool.false 2541332716720853259 

noncomputable def Ns420p2123 := @Enclosure.Real.IsNear.mulLit_ff qz228 qz229 15151288083 4294967296 361 

noncomputable abbrev qz254 := (BSN.correction_mk qz518 (BSN.cos_two_pi_p_ne_zero_mk qz516 788762 1000 11 qz521 rfl rfl (@BSN.floor_sqrt_eq_dec qz516 788762 1000 11 qz521 rfl rfl rfl)))

noncomputable abbrev qz543 := (@Ns420p2122 4611686018427387904 22647456057539743 121777333924098211840000 qz254 (@Ns420p2123 1073741824 167730473 1073741824 536317 14176747520000 2541332716720853259 4611686018427387904 22647456057539743 121777333924098211840000 (@Ns420p1966 1073741824 (Ns420p1979 rfl rfl rfl rfl rfl) rfl) (Ns420p2052 rfl) rfl))

noncomputable def Ns420p2124 := @Ns420p2121 22647456057539743 121777333924098211840000 Ns420p2116 Ns420p2108 Ns420p2117 Ns420p2111 qz542 qz543 

noncomputable abbrev qz544 := (@Ns420p1966 1073741824 (Ns420p1979 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns420p2125 := @Ns420p2101 Ns420p1807 Ns420p2102 Ns420p1423 Ns420p2088 Ns420p2074 Ns420p2089 Ns420p2076 Ns420p2104 (Ns420p2106 (@Ns420p2110 Ns420p2111 Ns420p2100 Ns420p1807 Ns420p2102 Ns420p1423 qz544 (@Ns420p2112 Ns420p2113 Ns420p1435 Ns420p2114 Ns420p2115 Ns420p2116 Ns420p2108 Ns420p2117 Ns420p2111 Ns420p2118 Ns420p2107 Ns420p2108 Ns420p2109 Ns420p2111 (@Ns420p2119 Ns420p1435 Ns420p2114 Ns420p2115 (@Ns420p2120 Ns420p1324 530280113 536870912 536317 14176747520000 Ns420p2113 Ns420p1435 Ns420p2114 Ns420p2115 qz247 (Ns420p2039 rfl) rfl)) (Ns420p2124 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns420p2126 := @Ns420p2087 Ns420p2088 Ns420p2074 Ns420p2089 Ns420p2076 Ns420p2090 Ns420p2077 Ns420p2074 Ns420p2079 Ns420p2076 (@Ns420p2091 Ns420p2092 Ns420p2084 Ns420p2093 Ns420p2086 468915949316813392801715 37778931862957161709568 Ns420p2094 Ns420p2095 Ns420p2096 Ns420p2083 Ns420p2084 Ns420p2085 Ns420p2086 (@Ns420p2097 Ns420p2084 Ns420p2093 Ns420p2086 (@Ns420p2098 Ns420p2017 167730473 1073741824 536317 14176747520000 Ns420p2092 Ns420p2084 Ns420p2093 Ns420p2086 (@Ns420p2020 Ns420p2019 Ns420p1324 Ns420p2015 Ns420p1665 Ns420p2016 Ns420p2017 qz247 qz247 rfl) (Ns420p2052 rfl) rfl)) (@Ns420p2099 250000000000000 530280113 536870912 536317 14176747520000 468915949316813392801715 37778931862957161709568 Ns420p2094 Ns420p2095 RS421to432.d68 (Ns420p2039 rfl) rfl) rfl rfl) Ns420p2125 

noncomputable def Ns420p2127 := nat_lit 952027505048759970659826747849788073875 

noncomputable def Ns420p2128 := nat_lit 17842929588548560813049623612894234615023472972884832264507 

noncomputable abbrev qz255 := qz536

noncomputable def Ns420p2129 := @Enclosure.Real.IsNear.mulLit_tf qz255 qz219 Ns420p2127 Ns420p1451 Ns420p2128 Ns420p1453 2541332716720853259 4611686018427387904 

noncomputable def Ns420p2130 := @Enclosure.Real.IsNear.mulLit_ff qz159 qz230 Ns420p1209 Ns420p1213 Ns420p1211 Ns420p1214 1217503355 4294967296 24501163 907311841280000 Ns420p2127 

noncomputable abbrev qz545 := (@HMul.hMul Real Real Real qz619 qz701 qz737)

noncomputable abbrev qz256 := qz545

noncomputable def Ns420p2131 := @Ns420p2129 22647456057539743 121777333924098211840000 Ns420p2080 Ns420p1751 Ns420p2081 Ns420p1398 (@Enclosure.Real.IsNear.neg qz256 Bool.false Ns420p2127 Ns420p1451 Ns420p2128 Ns420p1453 (@Ns420p2130 Ns420p1451 Ns420p2128 Ns420p1453 RS421to432.d70 qz538 rfl)) qz543 

noncomputable def Ns420p2132 := nat_lit 2856082515146279911979480243549364221625 

noncomputable def Ns420p2133 := nat_lit 53528788765645682439148870838682703845070418918654496793521 

noncomputable def Ns420p2134 := @Enclosure.Real.IsNear.mulLit_tt qz240 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz220) Ns420p2132 Ns420p1451 Ns420p2133 Ns420p1453 Ns420p2100 

noncomputable def Ns420p2135 := @Enclosure.Real.IsNear.mulLit_ft qz318 qz255 3 1 0 1 Ns420p2127 Ns420p1451 Ns420p2128 

noncomputable def Ns420p2136 := @Ns420p2135 Ns420p1453 Ns420p2132 Ns420p1451 Ns420p2133 Ns420p1453 qz474 (@Enclosure.Real.IsNear.neg qz256 Bool.false Ns420p2127 Ns420p1451 Ns420p2128 Ns420p1453 (@Ns420p2130 Ns420p1451 Ns420p2128 Ns420p1453 RS421to432.d70 qz538 rfl)) rfl 

noncomputable def Ns420p2137 := @Ns420p2134 Ns420p1807 Ns420p2102 Ns420p1423 Ns420p1991 Ns420p1992 Ns420p1993 Ns420p1994 Ns420p2136 (Ns420p2106 (@Ns420p2110 Ns420p2111 Ns420p2100 Ns420p1807 Ns420p2102 Ns420p1423 qz544 (@Ns420p2112 Ns420p2113 Ns420p1435 Ns420p2114 Ns420p2115 Ns420p2116 Ns420p2108 Ns420p2117 Ns420p2111 Ns420p2118 Ns420p2107 Ns420p2108 Ns420p2109 Ns420p2111 (@Ns420p2119 Ns420p1435 Ns420p2114 Ns420p2115 (@Ns420p2120 Ns420p1324 530280113 536870912 536317 14176747520000 Ns420p2113 Ns420p1435 Ns420p2114 Ns420p2115 qz247 (Ns420p2039 rfl) rfl)) (Ns420p2124 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns420p2138 := @Ns420p1989 Ns420p1990 Ns420p1965 Ns420p1991 Ns420p1992 Ns420p1993 Ns420p1994 Ns420p1995 Ns420p1981 Ns420p1962 Ns420p1982 Ns420p1965 (@Ns420p2000 Ns420p2001 Ns420p1962 Ns420p2002 Ns420p1965 Ns420p2003 Ns420p1988 Ns420p1962 Ns420p1990 Ns420p1965 Ns420p2053 (@Ns420p2057 Ns420p2058 Ns420p2059 Ns420p2060 Ns420p2001 Ns420p1962 Ns420p2002 Ns420p1965 Ns420p2069 (@Ns420p2071 Bool.false Ns420p2056 Ns420p2058 Ns420p2059 Ns420p2060 (BSN.iteratedDeriv_two_correction_mk qz220 qz242) (@Ns420p2072 4294967296 361 1073741824 Ns420p2073 Ns420p2074 Ns420p2075 Ns420p2076 Ns420p2056 Ns420p2058 Ns420p2059 Ns420p2060 qz544 (@Ns420p2078 Ns420p2079 Ns420p2076 Ns420p2080 Ns420p1751 Ns420p2081 Ns420p1398 Ns420p2082 Ns420p2073 Ns420p2074 Ns420p2075 Ns420p2076 (Ns420p2126 rfl rfl) (Ns420p2131 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns420p2137 

noncomputable def Ns420p2139 := nat_lit 711997770763240889719152312170202518495299490953620875 

noncomputable def Ns420p2140 := nat_lit 481510656505881384388589537894005130084833638899875911195310099261418309441250274269 

noncomputable def Ns420p2141 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz320 RSCompact.c11) qz241) qz219 Ns420p2139 Ns420p1807 Ns420p2140 Ns420p1466 2541332716720853259 4611686018427387904 22647456057539743 

noncomputable def Ns420p2142 := @Enclosure.Real.IsNear.mulLit_ff qz702 qz241 Ns420p1215 Ns420p1216 Ns420p1217 Ns420p1218 1029697457 1073741824 24501163 907311841280000 Ns420p2139 

noncomputable abbrev qz546 := (Ns420p2064 (@Ns420p2065 1730560000 (Ns420p1974 rfl) (Enclosure.sfrac_false_div 5512090331 4294967296) (Ns420p2068 rfl rfl) rfl rfl) rfl)

noncomputable def Ns420p2143 := Ns420p1960 (@Ns420p1964 Ns420p1965 Ns420p1953 Ns420p1954 Ns420p1955 Ns420p1956 qz544 (@Ns420p1980 Ns420p1981 Ns420p1962 Ns420p1982 Ns420p1965 Ns420p1983 Ns420p1984 Ns420p1985 Ns420p1986 Ns420p1987 Ns420p1961 Ns420p1962 Ns420p1963 Ns420p1965 (Ns420p2138 rfl rfl) (@Ns420p2141 121777333924098211840000 Ns420p1983 Ns420p1984 Ns420p1985 Ns420p1986 (@Ns420p2142 Ns420p1807 Ns420p2140 Ns420p1466 RS421to432.d71 qz546 rfl) qz543 rfl) rfl rfl) rfl) 

noncomputable def Ns420p2144 := @Enclosure.Real.IsNear.of_eq qz733 (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz220) qz461)) Bool.false Ns420p1948 Ns420p1949 Ns420p1950 Ns420p1951 (BSN.correctionLinear_mk qz220) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz220) qz461) Bool.true Ns420p1948 Ns420p1949 Ns420p1950 Ns420p1951 (@Ns420p1957 Ns420p1949 Ns420p1950 Ns420p1951 Ns420p2143 RS421to432.d72 rfl)) 

noncomputable def Ns420p2145 := @Enclosure.Real.IsNear.inv_image qz221 375952449 33554432 37 33554432 1497396 1497397 16777216 qz525 rfl 

noncomputable def Ns420p2146 := @Ns420p1952 Ns420p1904 Ns420p1914 Ns420p1907 Ns420p2144 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz221) Bool.false 2994793 33554432 1 33554432 2994793 33554432 1 33554432 (Ns420p2145 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p2147 := @Ns420p1906 Ns420p1907 Ns420p1823 Ns420p1819 Ns420p1825 Ns420p1821 (Ns420p1908 qz29 (@Enclosure.Real.IsNear.of_eq qz226 (@Inv.inv Real Real.instInv (Real.sqrt qz221)) Bool.false 626525 2097152 1 16777216 (BSN.rpow_neg_quarter_mk qz227 (BSN.t_div_two_pi_nonneg qz217 788762 1000 qz222)) Ns420p1912) rfl) (@Ns420p1915 Ns420p1916 Ns420p1903 Ns420p1904 Ns420p1905 Ns420p1907 (@Ns420p1917 140737488355328 145073042778869 2973079441506304000 qz254 (@Ns420p1918 16777216 1310417 8388608 4396161 443023360000 77555430125843 140737488355328 145073042778869 2973079441506304000 (@Ns420p1919 16777216 (Ns420p1933 rfl rfl rfl rfl rfl) rfl) (Ns420p1947 rfl) rfl)) (Ns420p2146 rfl) rfl rfl) 

noncomputable def Ns420p2148 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz217) (hardyZApproximantRS qz217) Bool.true Ns420p1818 Ns420p1819 Ns420p1820 Ns420p1821 (@Eq.refl Real (hardyZApproximantRS qz217)) (Ns420p1822 (BSN.hardyZApproximantRS_eq qz217 11 (@BSN.floor_sqrt_eq_dec qz217 788762 1000 11 qz222 rfl rfl rfl)) (@Ns420p1824 Ns420p1825 Ns420p1821 Ns420p1826 Ns420p1818 Ns420p1819 Ns420p1820 Ns420p1821 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz217) qz217 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 11)) Bool.true 606242073 67108864 151851 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz217) qz217 11) (Ns420p1902 (Ns420p1901 rfl) rfl rfl)) (Ns420p2147 rfl) rfl rfl)) 

theorem RS421to432.d77 : Enclosure.Real.IsNear (hardyZApproximantRS qz217) Bool.true Ns420p1818 Ns420p1819 Ns420p1820 Ns420p1821 := Ns420p2148 

noncomputable def Ns420p2149 := nat_lit 12469998993827656892416000 

noncomputable def Ns420p2150 := nat_lit 175670230267913371493951602688 

noncomputable def Ns420p2151 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz217) qz217 11) (@HMul.hMul Real Real Real qz5 qz218 qz219) 606242073 67108864 151851 134217728 48590415859593785575 295147905179352825856 182193402137674603511 Ns420p2149 Ns420p2150 

noncomputable def Ns420p2152 := @Enclosure.Real.IsNear.mulLit_tf qz218 qz219 626525 2097152 1 16777216 77555430125843 140737488355328 145073042778869 2973079441506304000 48590415859593785575 295147905179352825856 

noncomputable def Ns420p2153 := @Ns420p2152 182193402137674603511 Ns420p2149 (Ns420p1908 qz29 (@Enclosure.Real.IsNear.of_eq qz226 (@Inv.inv Real Real.instInv (Real.sqrt qz221)) Bool.false 626525 2097152 1 16777216 (BSN.rpow_neg_quarter_mk qz227 (BSN.t_div_two_pi_nonneg qz217 788762 1000 qz222)) Ns420p1912) rfl) (@Ns420p1917 140737488355328 145073042778869 2973079441506304000 qz254 (@Ns420p1918 16777216 1310417 8388608 4396161 443023360000 77555430125843 140737488355328 145073042778869 2973079441506304000 (@Ns420p1919 16777216 (Ns420p1933 rfl rfl rfl rfl rfl) rfl) (Ns420p1947 rfl) rfl)) 

noncomputable def Ns420p2154 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz217) (hardyZApproximantRS₀ qz217) Bool.true 2617690418182512693017 295147905179352825856 14290477348143104875511 Ns420p2149 (@Eq.refl Real (hardyZApproximantRS₀ qz217)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz217) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz217) qz217 11) (@HMul.hMul Real Real Real qz5 qz218 qz219)) Bool.true 2617690418182512693017 295147905179352825856 14290477348143104875511 Ns420p2149 (BSN.hardyZApproximantRS₀_eq qz217 11 (@BSN.floor_sqrt_eq_dec qz217 788762 1000 11 qz222 rfl rfl rfl)) (@Ns420p2151 2617690418182512693017 295147905179352825856 14290477348143104875511 Ns420p2149 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz217) qz217 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 11)) Bool.true 606242073 67108864 151851 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz217) qz217 11) (Ns420p1902 (Ns420p1901 rfl) rfl rfl)) (Ns420p2153 rfl) rfl rfl)) 

theorem RS421to432.d78 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz217) Bool.true 2617690418182512693017 295147905179352825856 14290477348143104875511 Ns420p2149 := Ns420p2154 

noncomputable def Ns420p2155 := nat_lit 15587498742284571115520000 

noncomputable def Ns420p2156 := nat_lit 4324000001942198193852776448 

noncomputable abbrev qz850 := (Enclosure.sfrac Bool.false 790386 1000)

noncomputable abbrev qz745 := qz850

noncomputable abbrev qz547 := qz745

noncomputable abbrev qz257 := qz547

noncomputable abbrev qz851 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 790386 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz746 := qz851

noncomputable abbrev qz548 := qz746

noncomputable abbrev qz258 := qz548

noncomputable abbrev qz852 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 790386 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz747 := qz852

noncomputable abbrev qz549 := qz747

noncomputable abbrev qz259 := qz549

noncomputable abbrev qz550 := (@HPow.hPow Real Real Real qz623 qz258 qz8)

noncomputable def Ns420p2157 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz257) qz257 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz550) (Zeta.RiemannSiegel.correction qz259)) 95674101 134217728 152173 134217728 5917613883940279647 36893488147419103232 295190352525624899383 Ns420p2155 Ns420p2156 

noncomputable def Ns420p2158 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz257) qz257 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 790386 1000 194 242 268435456 134217728 4503599627370496 Bool.false 406688289564 2573 

noncomputable def Ns420p2159 := Ns420p2158 618095470 41 84886744 8 643680110 41 80936328 8 Bool.false 259960381 130546 Bool.true 44175503 Bool.true 26360218 14148475504056880 1 Bool.false 264808746 Bool.true Bool.false 267142216 Bool.true Bool.false 95674101 

noncomputable def Ns420p2160 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz257) qz257 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 790386 1000 81 141 268435456 134217728 4503599627370496 Bool.false 406688289564 2573 

noncomputable def Ns420p2161 := Ns420p2160 558195838 41 94906264 8 589812974 41 89478488 8 Bool.false 363882423 106500 Bool.true 347634359 Bool.true 37930318 14148475504056880 1 Bool.false 258293762 Bool.true Bool.false 37804223 Bool.true Bool.false 259960381 

noncomputable def Ns420p2162 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz257) qz257 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 790386 1000 62 14 268435456 134217728 4503599627370496 Bool.false 406688289564 2573 

noncomputable def Ns420p2163 := Ns420p2162 480971758 41 109588312 8 522351262 41 101459064 8 Bool.false 430964466 78979 Bool.false 392185092 Bool.true 267631007 14148475504056880 1 Bool.false 29413159 Bool.true Bool.false 145712564 Bool.true Bool.false 363882423 

noncomputable def Ns420p2164 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz257) qz257 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 790386 1000 266 154 268435456 134217728 4503599627370496 Bool.false 406688289564 2573 

noncomputable def Ns420p2165 := Ns420p2164 372130544 40 134217720 8 432030192 40 120047984 16 Bool.false 500971667 46567 Bool.false 400641495 Bool.false 282430276 14148475504056880 1 Bool.false 20994470 Bool.true Bool.false 133068332 Bool.true Bool.false 430964466 

noncomputable def Ns420p2166 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz257) qz257 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 790386 1000 615 411 268435456 134217728 4503599627370496 Bool.false 406688289564 2573 

noncomputable def Ns420p2167 := Ns420p2166 186065264 40 189812528 16 294906480 40 154981288 8 Bool.false 190024544 2624 Bool.false 305591428 Bool.false 297133445 14148475504056880 1 Bool.false 243731666 Bool.false Bool.false 240067106 Bool.false Bool.false 500971667 

noncomputable def Ns420p2168 := nat_lit 51983742236710404599858080586638460665807635799160225763 

noncomputable def Ns420p2169 := nat_lit 34311977772533444291388466126970568559759361835008000 

noncomputable def Ns420p2170 := nat_lit 148060043590393770713125389204480000 

noncomputable def Ns420p2171 := nat_lit 702147644808067067566517369284008775680 

noncomputable abbrev qz853 := (@Eq.refl Real (Enclosure.sfrac Bool.false 790386 1000))

noncomputable abbrev qz748 := qz853

noncomputable abbrev qz551 := qz748

noncomputable abbrev qz260 := qz551

noncomputable def Ns420p2172 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz257 790386 1000 2498841115984 16000000 1580772 4000 2000 Ns420p2170 Ns420p2171 qz260 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns420p2173 := nat_lit 9581643369070461775845841413729201069921663430501212812636160 

noncomputable abbrev qz552 := (@HMul.hMul Real Real Real qz619 qz625 (@HSub.hSub Real Real Real qz624 qz626 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 (@Nat.cast Real Real.instNatCast 1580772)))))

noncomputable abbrev qz749 := (Real.log (Enclosure.sfrac Bool.false 2498841115984 16000000))

noncomputable abbrev qz750 := (Enclosure.sfrac Bool.false 790386 2000)

noncomputable abbrev qz261 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 790386 4000) qz749) qz552) qz750)

noncomputable abbrev qz553 := (@HSub.hSub Real Real Real qz11 qz261 (@HMul.hMul Real Real Real qz5 qz750 (Real.log Real.pi)))

noncomputable def Ns420p2174 := @Enclosure.Real.IsNear.addLit_ft_p qz553 (Enclosure.sfrac Bool.true Ns420p2170 Ns420p2171) 13646196456723757241487 9007199254740992000 3315615082262178861 346112000000000000000000 Ns420p2170 Ns420p2171 0 1 Ns420p2173 

noncomputable def Ns420p2175 := nat_lit 18315614842631130205759324815360 

noncomputable abbrev qz554 := (@HMul.hMul Real Real Real qz5 qz750 (Real.log Real.pi))

noncomputable def Ns420p2176 := @Enclosure.Real.IsNear.subLit_ff_p qz261 qz554 708838258003868462823 360287970189639680 1247479260431739 338000000000000000000 15179663871873 33554432000 395193 67108864000 Ns420p2175 13646196456723757241487 9007199254740992000 

noncomputable def Ns420p2177 := nat_lit 35441912900193423141150000 

noncomputable abbrev qz262 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 790386 4000) qz749) qz552)

noncomputable def Ns420p2178 := @Enclosure.Real.IsNear.subLit_ff_p qz262 qz750 21280538545175568422031 9007199254740992000 1247479260431739 338000000000000000000 790386 2000 0 1 Ns420p2177 708838258003868462823 360287970189639680 1247479260431739 338000000000000000000 

noncomputable def Ns420p2179 := nat_lit 47919512731148083501902578790262898688 

noncomputable def Ns420p2180 := nat_lit 57828961282660033267499008 

noncomputable def Ns420p2181 := nat_lit 989613283532877164889617122065487531625592913104304462672856231614267187527680 

noncomputable def Ns420p2182 := nat_lit 2531409412363042746557177718592285791394643895406970212682789314714807566336 

noncomputable def Ns420p2183 := nat_lit 63013216043547673014376866200878633645743695501562326128739808958218240 

noncomputable def Ns420p2184 := BSN.log_dyadic_bound 401689115984 4595993115984 4 3 Ns420p2181 134217728 54080000 Ns420p2182 Ns420p2183 23521232 4997682231968 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 401689115984) (BSN.artanhQ 4595993115984) 0 3 Ns420p2182 Ns420p2181 Ns420p2183 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns420p2185 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 790386 4000) qz749 790386 4000 0 1 53857417109105767 4503599627370496 3125002873 169000000000000000 21284074239598835378031 9007199254740992000 1234979260389489 338000000000000000000 (Enclosure.Real.IsNear.const Bool.false 790386 4000) (BSN.isNear_log_sfrac 2498841115984 16000000 53857417109105767 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2498841115984) qz335)) Bool.false Ns420p2180 Ns420p103 1000000919360000 54080000000000000000000 53857417109105767 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2498841115984 16000000 17 4997682231968 4194304000000 23521232 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns420p2184 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns420p2186 := BSN.arctan_dyadic_bound_f 1000 1580772 1 0 16777216 6760000 0 1 1 0 1 1 10613 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1580772) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1580772) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns420p2187 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1580772))) 884279719003555 562949953421312 1 2000000000000000 10613 16777216 1 6760000 14829777262286286618624 883923605816739 562949953421312 50000000169 338000000000000000 qz16 (Ns420p2186 rfl) rfl rfl 

noncomputable abbrev qz263 := qz552

noncomputable def Ns420p2188 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 790386 4000) qz749) qz263 21284074239598835378031 9007199254740992000 1234979260389489 338000000000000000000 883923605816739 2251799813685248 50000000169 1352000000000000000 Ns420p2179 21280538545175568422031 9007199254740992000 1247479260431739 338000000000000000000 (Ns420p2185 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1580772)))) 1 4 0 1 883923605816739 562949953421312 50000000169 338000000000000000 883923605816739 2251799813685248 50000000169 1352000000000000000 qz340 Ns420p2187 rfl) 

noncomputable def Ns420p2189 := @Ns420p2174 Ns420p2168 Ns420p2169 3315615082262178861 346112000000000000000000 (@Ns420p2176 3315615082262178861 346112000000000000000000 (Ns420p2178 (Ns420p2188 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 790386 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz750 (Real.log Real.pi) 790386 2000 0 1 38410761 33554432 1 67108864 15179663871873 33554432000 395193 67108864000 (Enclosure.Real.IsNear.const Bool.false 790386 2000) RS421to432.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns420p2170 Ns420p2171) 

noncomputable def Ns420p2190 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz257) Bool.false Ns420p2168 Ns420p2169 3315615082262178861 346112000000000000000000 50836036195 33554432 323 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz257) (@HAdd.hAdd Real Real Real qz341 qz553 (Enclosure.sfrac Bool.true Ns420p2170 Ns420p2171)) Bool.false Ns420p2168 Ns420p2169 3315615082262178861 346112000000000000000000 Ns420p2172 (Ns420p2189 rfl rfl)) 

noncomputable def Ns420p2191 := nat_lit 3792548102581016277811200 

noncomputable def Ns420p2192 := nat_lit 316177994540720496204398808824496096359215944708728766661256367619177932937924281140551936 

noncomputable def Ns420p2193 := nat_lit 20052072892042597411705012245279816272850392000149059967199507548332190919545345701492817920 

noncomputable def Ns420p2194 := nat_lit 71188587909989049447530676075483859774231994670256442552255224720762993717327379865856 

noncomputable def Ns420p2195 := nat_lit 948391606446341510514301365121337321358099370136845787098664592408092272826338188661924096 

noncomputable def Ns420p2196 := nat_lit 902343280141916883526725551037591732278267640006707698523977839674948591379540556567176806400 

noncomputable def Ns420p2197 := BSN.cos_dyadic_bound_f 53895350086 68719476736 3 2 33554432 13533204 Ns420p2192 Ns420p2193 Ns420p2194 Ns420p2195 Ns420p2196 Ns420p2194 23753068 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 53895350086) (BSN.cosEvenQ 68719476736) 0 2 Ns420p2192 Ns420p2193 Ns420p2194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 53895350086) (BSN.cosOddQ 68719476736) 0 2 Ns420p2195 Ns420p2196 Ns420p2194 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2198 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz257) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50836036195) qz342) Bool.false 50836036195 33554432 323 33554432 Bool.false 23753068 33554432 1 6760000 (Ns420p2190 rfl) (Enclosure.sfrac_false_div 50836036195 33554432) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50836036195) qz342) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns420p2191) qz343) 226375608064910080 72057594037927936 Bool.false 23753068 33554432 241 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q0 50836036195 33554432 226375608064910080 72057594037927936 241 Ns420p2191 Ns420p103 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 23753068 33554432 Ns420p2191 Ns420p103 53895350086 68719476736 13533204 13520000 (Ns420p2197 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns420p2199 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz257) Bool.false Ns420p2168 Ns420p2169 3315615082262178861 346112000000000000000000 406688289564 268435456 2573 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz257) (@HAdd.hAdd Real Real Real qz341 qz553 (Enclosure.sfrac Bool.true Ns420p2170 Ns420p2171)) Bool.false Ns420p2168 Ns420p2169 3315615082262178861 346112000000000000000000 Ns420p2172 (Ns420p2189 rfl rfl)) 

noncomputable def Ns420p2200 := Ns420p2167 46567 BSN.abs_quadSignPos (BSN.cos_quad_nat3 615 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 243731666 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 411 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 240067106 268435456) qz260 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 1) Bool.false 5938267 8388608 34641163 3544186880000 190024544 268435456 2624 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz257)) Bool.false 5938267 8388608 34641163 3544186880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz257) qz257) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz257)) Bool.false 23753068 33554432 2217034432 226827960320000 5938267 8388608 34641163 3544186880000 (Ns420p2198 rfl rfl) rfl)) rfl) (Ns420p2199 rfl) RS421to432.d7 

noncomputable def Ns420p2201 := nat_lit 137008377296495323605774939605217242827947438367464508968338474007592960 

noncomputable def Ns420p2202 := nat_lit 76055275367469462635008955619722181205289776978043429197381317492736 

noncomputable def Ns420p2203 := nat_lit 358708327235464230313715779704565609589339488466347357936471671696326656 

noncomputable def Ns420p2204 := BSN.sin_dyadic_bound_f 305591428 268435456 3 2 268435456 134217728 Ns420p2201 Ns420p119 Ns420p2202 Ns420p2203 Ns420p122 Ns420p2202 243731666 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 305591428) qz344 0 2 Ns420p2201 Ns420p119 Ns420p2202 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 305591428) qz345 0 2 Ns420p2203 Ns420p122 Ns420p2202 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2205 := nat_lit 122451187420523997882372412585822141335521605678810739228523728711430625 

noncomputable def Ns420p2206 := nat_lit 60759236229752695303232133459888746268698861559080379157638000390625 

noncomputable def Ns420p2207 := nat_lit 320607118766524204375722514270599121718121550049599139270354542243590625 

noncomputable def Ns420p2208 := BSN.sin_dyadic_bound_f 297133445 268435456 3 2 268435456 134217728 Ns420p2205 Ns420p119 Ns420p2206 Ns420p2207 Ns420p122 Ns420p2206 240067106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 297133445) qz344 0 2 Ns420p2205 Ns420p119 Ns420p2206 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 297133445) qz345 0 2 Ns420p2207 Ns420p122 Ns420p2206 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2209 := nat_lit 13904322985002785677593356130061109168995767722650057377343628403140571345572398236777886676743651961234390625 

noncomputable def Ns420p2210 := nat_lit 17102954222039943947289264332762490551832937603862989948604703381460275737209114594819779589941650390625 

noncomputable def Ns420p2211 := nat_lit 84187197762626327074193939340424116275093728655779574932653242732887892450740205297530457371509194703659990625 

noncomputable def Ns420p2212 := BSN.cos_dyadic_bound_f 400641495 268435456 4 3 268435456 134217728 Ns420p2209 Ns420p140 Ns420p2210 Ns420p2211 Ns420p143 Ns420p2210 20994470 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 400641495) qz346 0 3 Ns420p2209 Ns420p140 Ns420p2210 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 400641495) qz347 0 3 Ns420p2211 Ns420p143 Ns420p2210 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2213 := nat_lit 3426150624630519062688889847712365891586081190146488234796781540079979358278196797641031745134287719871021056 

noncomputable def Ns420p2214 := nat_lit 257593562394165152214875774214130551288458216467943180147281569579258073196089483772009653218549170176 

noncomputable def Ns420p2215 := nat_lit 20775212403843032637769868207832740406799868966740313919899501583507292338867446694477520757768190627036528640 

noncomputable def Ns420p2216 := BSN.cos_dyadic_bound_f 282430276 268435456 4 3 268435456 134217728 Ns420p2213 Ns420p140 Ns420p2214 Ns420p2215 Ns420p143 Ns420p2214 133068332 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 282430276) qz346 0 3 Ns420p2213 Ns420p140 Ns420p2214 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 282430276) qz347 0 3 Ns420p2215 Ns420p143 Ns420p2214 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2217 := Ns420p2165 78979 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 266 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 20994470 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 154 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133068332 268435456) qz260 rfl rfl (Ns420p2200 RS421to432.d9 RS421to432.d11 RS421to432.d13 RS421to432.d17 (Ns420p2204 rfl rfl) (Ns420p2208 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns420p2199 rfl) RS421to432.d19 RS421to432.d21 RS421to432.d23 RS421to432.d25 RS421to432.d17 (Ns420p2212 rfl rfl) (Ns420p2216 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns420p2218 := nat_lit 12763969378774613265206024899481627724171491865161598727930697011282363109657186658691848694211934522930364416 

noncomputable def Ns420p2219 := nat_lit 13240152016226492628827674019868693818101166598931055934948252022108657112272735931648896575560887566336 

noncomputable def Ns420p2220 := nat_lit 77295055387656377422640078025794961395396439421197910166339788302918744071103222183798976993686538164539228160 

noncomputable def Ns420p2221 := BSN.cos_dyadic_bound_f 392185092 268435456 4 3 268435456 134217728 Ns420p2218 Ns420p140 Ns420p2219 Ns420p2220 Ns420p143 Ns420p2219 29413159 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 392185092) qz346 0 3 Ns420p2218 Ns420p140 Ns420p2219 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 392185092) qz347 0 3 Ns420p2220 Ns420p143 Ns420p2219 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2222 := nat_lit 2762140932125486512076483931747347108202118915352599857876790144254282368513021990289994573710796052797822081 

noncomputable def Ns420p2223 := nat_lit 135032136207335602060188574306788137844785790608040756846253349614520388112845172622265455120385283201 

noncomputable def Ns420p2224 := nat_lit 16750421253728321674968323649002764790547991767897514467383396676105986967036002862183183749193250168343336065 

noncomputable def Ns420p2225 := BSN.cos_dyadic_bound_f 267631007 268435456 4 3 268435456 134217728 Ns420p2222 Ns420p140 Ns420p2223 Ns420p2224 Ns420p143 Ns420p2223 145712564 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 267631007) qz346 0 3 Ns420p2222 Ns420p140 Ns420p2223 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 267631007) qz347 0 3 Ns420p2224 Ns420p143 Ns420p2223 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2226 := Ns420p2163 106500 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 29413159 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 145712564 268435456) qz260 rfl rfl (Ns420p2217 rfl rfl) (Ns420p2199 rfl) RS421to432.d27 RS421to432.d29 RS421to432.d31 RS421to432.d33 RS421to432.d17 (Ns420p2221 rfl rfl) (Ns420p2225 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p2227 := nat_lit 20450913394777488086892463836184260667663645150869271944121608386090819317074337537835191077501941362081267681 

noncomputable def Ns420p2228 := nat_lit 3115102412030838579554062100314238984899833358735726412802175860153990506361797594547522806959036301281 

noncomputable def Ns420p2229 := nat_lit 102195813074318782315018299847707037762381929680175254077079846018228942987063146555311252028662850688227868641 

noncomputable def Ns420p2230 := BSN.sin_dyadic_bound_f 347634359 268435456 4 3 268435456 134217728 Ns420p2227 Ns420p258 Ns420p2228 Ns420p2229 Ns420p261 Ns420p2228 258293762 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 347634359) qz344 0 3 Ns420p2227 Ns420p258 Ns420p2228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 347634359) qz345 0 3 Ns420p2229 Ns420p261 Ns420p2228 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2231 := nat_lit 2069883654533751213901409103376 

noncomputable def Ns420p2232 := BSN.sin_dyadic_bound_f 37930318 268435456 2 1 268435456 134217728 Ns420p2231 Ns420p133 Ns420p2231 Ns420p2231 Ns420p134 Ns420p2231 37804223 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 37930318) qz344 0 1 Ns420p2231 Ns420p133 Ns420p2231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 37930318) qz345 0 1 Ns420p2231 Ns420p134 Ns420p2231 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2233 := Ns420p2161 130546 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 258293762 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 141 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 37804223 268435456) qz260 rfl rfl (Ns420p2226 rfl) (Ns420p2199 rfl) RS421to432.d35 RS421to432.d37 RS421to432.d39 RS421to432.d41 RS421to432.d17 (Ns420p2230 rfl rfl) (Ns420p2232 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p2234 := nat_lit 3808254930499383241032984454081 

noncomputable def Ns420p2235 := BSN.cos_dyadic_bound_f 44175503 268435456 2 1 268435456 134217728 Ns420p2234 Ns420p285 Ns420p2234 Ns420p2234 Ns420p286 Ns420p2234 264808746 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 44175503) qz346 0 1 Ns420p2234 Ns420p285 Ns420p2234 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 44175503) qz347 0 1 Ns420p2234 Ns420p286 Ns420p2234 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2236 := nat_lit 482831938575610918727520610576 

noncomputable def Ns420p2237 := BSN.cos_dyadic_bound_f 26360218 268435456 2 1 268435456 134217728 Ns420p2236 Ns420p285 Ns420p2236 Ns420p2236 Ns420p286 Ns420p2236 267142216 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 26360218) qz346 0 1 Ns420p2236 Ns420p285 Ns420p2236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 26360218) qz347 0 1 Ns420p2236 Ns420p286 Ns420p2236 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2238 := Ns420p2159 152173 BSN.abs_quadSignNeg qz651 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 264808746 268435456) BSN.abs_quadSignNeg qz348 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267142216 268435456) qz260 rfl rfl (Ns420p2233 rfl) (Ns420p2199 rfl) RS421to432.d43 RS421to432.d45 RS421to432.d47 RS421to432.d49 RS421to432.d17 (Ns420p2235 rfl rfl) (Ns420p2237 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p2239 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 11) 95674101 268435456 152173 268435456 95674101 268435456 152173 268435456 51364641858650112 95674101 134217728 152173 134217728 (Ns420p2238 rfl) 

noncomputable def Ns420p2240 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz550) (Zeta.RiemannSiegel.correction qz259) 10019247 33554432 1 33554432 590624613201 1099511627776 470998723459561 7432698603765760000 5917613883940279647 36893488147419103232 

noncomputable def Ns420p2241 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz550 1 1 0 1 10019247 33554432 1 33554432 10019247 33554432 1 33554432 

noncomputable def Ns420p2242 := @Enclosure.Real.IsNear.sqrt_image qz258 2110470123129 16777216000 395193 16777216000 188169621 188169657 16777216 (@Enclosure.Real.IsNear.of_eq qz258 (@HMul.hMul Real Real Real qz5 qz257 qz3) Bool.false 2110470123129 16777216000 395193 16777216000 (BSN.t_div_two_pi_mk qz257 790386 1000 qz260) (@Enclosure.Real.IsNear.mulLit_ff qz257 qz3 790386 1000 0 1 5340353 33554432 1 33554432 2110470123129 16777216000 395193 16777216000 (Enclosure.Real.IsNear.const Bool.false 790386 1000) RS421to432.d52 rfl)) 

noncomputable abbrev qz854 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 790386 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz751 := qz854

noncomputable abbrev qz555 := qz751

noncomputable abbrev qz264 := qz555

noncomputable def Ns420p2243 := @Enclosure.Real.IsNear.sqrt_image qz264 188169639 16777216 9 8388608 56186852 56186858 16777216 (@Enclosure.Real.IsNear.recentre' qz264 Bool.false 376339278 33554432 36 33554432 188169639 16777216 9 8388608 (Ns420p2242 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns420p2244 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz264) 56186855 16777216 3 16777216 5009623 5009624 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz264) Bool.false 112373710 33554432 6 33554432 56186855 16777216 3 16777216 (Ns420p2243 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p2245 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz264)) Bool.false 10019247 33554432 1 33554432 10019247 33554432 1 33554432 (Ns420p2244 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz265 := (@HMul.hMul Real Real Real qz326 qz322 qz549)

noncomputable abbrev qz752 := (@HMul.hMul Real Real Real qz795 qz852 qz852)

noncomputable abbrev qz556 := (@HSub.hSub Real Real Real qz624 (@HSub.hSub Real Real Real qz624 qz752 qz747) qz634)

noncomputable abbrev qz266 := (Real.cos (@HMul.hMul Real Real Real qz326 qz322 qz556))

noncomputable def Ns420p2246 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz259) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz265)) qz266) Bool.false 590624613201 

noncomputable def Ns420p2247 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz265)) qz266 614409 131072 2549 

noncomputable def Ns420p2248 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz265)) Bool.false 157288704 33554432 5098 33554432 614409 131072 2549 

noncomputable def Ns420p2249 := @Enclosure.Real.IsNear.recentre' (Real.cos qz265) Bool.false 3579087 16777216 1568074432 226827960320000 3579087 16777216 24501163 3544186880000 

noncomputable def Ns420p2250 := @Enclosure.Real.IsNear.cos_image qz265 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22746783) qz364) Bool.false 22746783 16777216 227 33554432 Bool.false 3579087 16777216 1 

noncomputable def Ns420p2251 := nat_lit 242874678696945320284439551 

noncomputable def Ns420p2252 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz259 884279719003555 140737488355328 1 500000000000000 3620263 16777216 9 8388608 3201325148358967034965 2361183241434822606848 Ns420p2251 

noncomputable def Ns420p2253 := @Enclosure.Real.IsNear.subLit_ff_p qz264 qz1 188169639 16777216 9 8388608 11 1 0 1 3620263 3620263 16777216 9 

noncomputable def Ns420p2254 := @Ns420p2253 8388608 (@Enclosure.Real.IsNear.recentre' qz264 Bool.false 376339278 33554432 36 33554432 188169639 16777216 9 8388608 (Ns420p2242 rfl rfl rfl rfl rfl rfl) rfl) qz352 

noncomputable def Ns420p2255 := @Enclosure.Real.IsNear.recentre' qz265 Bool.false 3201325148358967034965 2361183241434822606848 Ns420p2251 Ns420p302 22746783 16777216 227 33554432 (@Ns420p2252 Ns420p302 RS421to432.d51 (Ns420p2254 rfl rfl) rfl) 

noncomputable def Ns420p2256 := nat_lit 33607617351772775195579282248827695705991338311891932138402104266072163267399897198251517786241 

noncomputable def Ns420p2257 := nat_lit 19188446454421300610861062907438070750638760575960340928777096170052053138601075813496961 

noncomputable def Ns420p2258 := nat_lit 203613270481969305576052431955738866946202016089369968390500487120064307967353263045001079535745 

noncomputable def Ns420p2259 := BSN.cos_dyadic_bound_f 22746783 16777216 4 3 16777216 6760000 Ns420p2256 Ns420p1085 Ns420p2257 Ns420p2258 Ns420p1088 Ns420p2257 3579087 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 22746783) (BSN.cosEvenQ 16777216) 0 3 Ns420p2256 Ns420p1085 Ns420p2257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 22746783) (BSN.cosOddQ 16777216) 0 3 Ns420p2258 Ns420p1088 Ns420p2257 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2260 := @Enclosure.Real.IsNear.inv_image (Real.cos qz265) 3579087 16777216 24501163 3544186880000 78641803 78646901 16777216 (Ns420p2249 (@Ns420p2250 6760000 (Ns420p2255 rfl) (Enclosure.sfrac_false_div 22746783 16777216) (Ns420p2259 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns420p2261 := @Enclosure.Real.IsNear.recentre' qz266 Bool.false 1922578 16777216 

noncomputable abbrev qz267 := (@HMul.hMul Real Real Real qz326 qz322 qz556)

noncomputable def Ns420p2262 := @Enclosure.Real.IsNear.cos_image qz267 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 48853555)) qz342) Bool.true 48853555 33554432 

noncomputable def Ns420p2263 := nat_lit 57676097846691398628075760525 

noncomputable def Ns420p2264 := nat_lit 36458160893293934849803674087841 

noncomputable def Ns420p2265 := @Enclosure.Real.IsNear.recentre' qz267 Bool.true Ns420p2263 Ns420p469 Ns420p2264 

noncomputable def Ns420p2266 := nat_lit 3777893186295716170956800000000000000 

noncomputable abbrev qz268 := qz556

noncomputable def Ns420p2267 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz268 884279719003555 140737488355328 1 500000000000000 65223816183055 

noncomputable abbrev qz557 := (@HSub.hSub Real Real Real qz624 qz752 qz747)

noncomputable abbrev qz269 := qz557

noncomputable def Ns420p2268 := @Enclosure.Real.IsNear.subLit_tf qz269 qz27 47631630138639 281474976710656 6754995 4398046511104 1 16 

noncomputable abbrev qz558 := qz752

noncomputable abbrev qz270 := qz558

noncomputable def Ns420p2269 := @Enclosure.Real.IsNear.subLit_ff_n qz270 qz259 13106304189169 281474976710656 2036403 4398046511104 3620263 16777216 9 8388608 

noncomputable def Ns420p2270 := @Enclosure.Real.IsNear.mulLit_ff qz259 qz259 3620263 16777216 9 8388608 3620263 16777216 9 8388608 13106304189169 281474976710656 

noncomputable def Ns420p2271 := nat_lit 183176619871967926226763330160862839221607753048304803263207402208288948261781359477087523465640625 

noncomputable def Ns420p2272 := nat_lit 184822170410602757748789857668474008447930887536877230656074941888876981546826047148681640625 

noncomputable def Ns420p2273 := nat_lit 1109294296647357468485044649314564186158358570102323547593853117505310978651527028765670337571240625 

noncomputable def Ns420p2274 := BSN.cos_dyadic_bound_f 48853555 33554432 4 3 16777216 6760000 Ns420p2271 Ns420p1201 Ns420p2272 Ns420p2273 Ns420p1204 Ns420p2272 1922578 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 48853555) qz635 0 3 Ns420p2271 Ns420p1201 Ns420p2272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 48853555) (BSN.cosOddQ 33554432) 0 3 Ns420p2273 Ns420p1204 Ns420p2272 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2275 := @Ns420p2261 555948608 56706990080000 961289 8388608 8686697 886046720000 (@Ns420p2262 81 8388608 Bool.false 1922578 16777216 1 6760000 (@Ns420p2265 Ns420p2266 48853555 33554432 81 8388608 (@Ns420p2267 281474976710656 6754995 4398046511104 Ns420p2263 Ns420p469 Ns420p2264 Ns420p2266 RS421to432.d51 (@Ns420p2268 0 1 1043581058928880 65223816183055 281474976710656 6754995 4398046511104 (@Ns420p2269 799126147268056449024 47631630138639 281474976710656 6754995 4398046511104 (@Ns420p2270 2036403 4398046511104 (Ns420p2254 rfl rfl) (Ns420p2254 rfl rfl) rfl) (Ns420p2254 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 48853555 33554432) (BSN.cos_neg_of_bound 48853555 33554432 Bool.false 1922578 16777216 1 6760000 (Ns420p2274 rfl rfl)) rfl rfl) 

noncomputable def Ns420p2276 := @Ns420p2240 295190352525624899383 Ns420p2155 (Ns420p2241 qz29 (@Enclosure.Real.IsNear.of_eq qz550 (@Inv.inv Real Real.instInv (Real.sqrt qz264)) Bool.false 10019247 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz258 (BSN.t_div_two_pi_nonneg qz257 790386 1000 qz260)) Ns420p2245) rfl) (@Ns420p2246 1099511627776 470998723459561 7432698603765760000 (BSN.correction_mk qz259 (BSN.cos_two_pi_p_ne_zero_mk qz257 790386 1000 11 qz260 rfl rfl (@BSN.floor_sqrt_eq_dec qz257 790386 1000 11 qz260 rfl rfl rfl))) (@Ns420p2247 16777216 961289 8388608 8686697 886046720000 590624613201 1099511627776 470998723459561 7432698603765760000 (@Ns420p2248 16777216 (Ns420p2260 rfl rfl rfl rfl rfl) rfl) (Ns420p2275 rfl) rfl)) 

noncomputable def Ns420p2277 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz257) (hardyZApproximantRS₀ qz257) Bool.false 32216310515569136991 36893488147419103232 17967941049882609219383 Ns420p2155 (@Eq.refl Real (hardyZApproximantRS₀ qz257)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz257) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz257) qz257 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz550) (Zeta.RiemannSiegel.correction qz259))) Bool.false 32216310515569136991 36893488147419103232 17967941049882609219383 Ns420p2155 (BSN.hardyZApproximantRS₀_eq qz257 11 (@BSN.floor_sqrt_eq_dec qz257 790386 1000 11 qz260 rfl rfl rfl)) (@Ns420p2157 32216310515569136991 36893488147419103232 17967941049882609219383 Ns420p2155 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz257) qz257 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz257) qz257 11)) Bool.false 95674101 134217728 152173 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz257) qz257 11) (Ns420p2239 (Ns420p2238 rfl) rfl rfl)) (Ns420p2276 rfl) rfl rfl)) 

theorem RS421to432.d79 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz257) Bool.false 32216310515569136991 36893488147419103232 17967941049882609219383 Ns420p2155 := Ns420p2277 

noncomputable def Ns420p2278 := nat_lit 399039967802485020557312000 

noncomputable def Ns420p2279 := nat_lit 4040499389416809441905461952512 

noncomputable abbrev qz855 := (Enclosure.sfrac Bool.false 791361 1000)

noncomputable abbrev qz753 := qz855

noncomputable abbrev qz559 := qz753

noncomputable abbrev qz271 := qz559

noncomputable abbrev qz856 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 791361 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz754 := qz856

noncomputable abbrev qz560 := qz754

noncomputable abbrev qz272 := qz560

noncomputable abbrev qz857 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 791361 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz755 := qz857

noncomputable abbrev qz561 := qz755

noncomputable abbrev qz273 := qz561

noncomputable abbrev qz562 := (@HPow.hPow Real Real Real qz623 qz272 qz8)

noncomputable def Ns420p2280 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz271) qz271 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz562) (Zeta.RiemannSiegel.correction qz273)) 235103353 134217728 152357 134217728 2983789052464613055705 18889465931478580854784 9484644387844780175427 Ns420p2278 Ns420p2279 

noncomputable def Ns420p2281 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz271) qz271 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 791361 1000 194 242 268435456 134217728 4503599627370496 Bool.false 407321042875 2576 

noncomputable def Ns420p2282 := Ns420p2281 618095470 41 84886744 8 643680110 41 80936328 8 Bool.true 69648941 130703 Bool.true 14065276 Bool.true 21195014 14148475504056880 1 Bool.false 268067049 Bool.true Bool.false 267599137 Bool.true Bool.true 235103353 

noncomputable def Ns420p2283 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz271) qz271 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 791361 1000 81 140 268435456 134217728 4503599627370496 Bool.false 407321042875 2576 

noncomputable def Ns420p2284 := Ns420p2283 558195838 41 94906264 8 589812974 41 89478488 8 Bool.false 1805938 106627 Bool.true 259121990 Bool.true 401902085 14148475504056880 1 Bool.false 220713629 Bool.true Bool.false 19737515 Bool.false Bool.true 69648941 

noncomputable def Ns420p2285 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz271) qz271 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 791361 1000 63 14 268435456 134217728 4503599627370496 Bool.false 407321042875 2576 

noncomputable def Ns420p2286 := Ns420p2285 480971758 41 109588312 8 522351262 41 101459064 8 Bool.false 36399513 79073 Bool.false 134333511 Bool.true 144170176 14148475504056880 1 Bool.false 128796410 Bool.false Bool.false 230642017 Bool.true Bool.false 1805938 

noncomputable def Ns420p2287 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz271) qz271 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 791361 1000 267 155 268435456 134217728 4503599627370496 Bool.false 407321042875 2576 

noncomputable def Ns420p2288 := Ns420p2287 372130544 40 134217720 8 432030192 40 120047984 16 Bool.true 102914632 46621 Bool.false 248910097 Bool.false 72296722 14148475504056880 1 Bool.false 214743074 Bool.false Bool.false 71425859 Bool.false Bool.false 36399513 

noncomputable def Ns420p2289 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz271) qz271 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 791361 1000 616 412 268435456 134217728 4503599627370496 Bool.false 407321042875 2576 

noncomputable def Ns420p2290 := Ns420p2289 186065264 40 189812528 16 294906480 40 154981288 8 Bool.true 268435448 2624 Bool.false 335273678 Bool.false 220695509 14148475504056880 1 Bool.false 84900494 Bool.false Bool.false 182709015 Bool.false Bool.true 102914632 

noncomputable def Ns420p2291 := nat_lit 6713749225204632687381518166648639126581352476989492134071 

noncomputable def Ns420p2292 := nat_lit 4424540215288088771920910990729829324261211896807424000 

noncomputable def Ns420p2293 := nat_lit 148975514495426343114381462144480000 

noncomputable def Ns420p2294 := nat_lit 707360604536560781015598545390483023680 

noncomputable def Ns420p2295 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz271 791361 1000 2505009929284 16000000 1582722 4000 2000 Ns420p2293 Ns420p2294 (@Eq.refl Real qz271) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns420p2296 := nat_lit 19335597768589342139658772319948080684554295133729737346124480 

noncomputable abbrev qz563 := (@HMul.hMul Real Real Real qz619 qz625 (@HSub.hSub Real Real Real qz624 qz626 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 (@Nat.cast Real Real.instNatCast 1582722)))))

noncomputable abbrev qz756 := (Real.log (Enclosure.sfrac Bool.false 2505009929284 16000000))

noncomputable abbrev qz757 := (Enclosure.sfrac Bool.false 791361 2000)

noncomputable abbrev qz274 := (@HSub.hSub Real Real Real qz331 (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 791361 4000) qz756) qz563) qz757)

noncomputable abbrev qz564 := (@HSub.hSub Real Real Real qz11 qz274 (@HMul.hMul Real Real Real qz5 qz757 (Real.log Real.pi)))

noncomputable def Ns420p2297 := @Enclosure.Real.IsNear.addLit_ft_p qz564 (Enclosure.sfrac Bool.true Ns420p2293 Ns420p2294) 27334856264665280382311 18014398509481984000 6639378701328307797 692224000000000000000000 Ns420p2293 Ns420p2294 0 1 Ns420p2296 

noncomputable def Ns420p2298 := nat_lit 1834411151524970306698376904704000 

noncomputable abbrev qz565 := (@HMul.hMul Real Real Real qz5 qz757 (Real.log Real.pi))

noncomputable def Ns420p2299 := @Enclosure.Real.IsNear.subLit_ff_p qz274 qz565 35494429291301922506087 18014398509481984000 2498005398664653 676000000000000000000 30396778235721 67108864000 791361 134217728000 Ns420p2298 27334856264665280382311 18014398509481984000 

noncomputable def Ns420p2300 := nat_lit 70988858582603845012174000 

noncomputable abbrev qz275 := (@HSub.hSub Real Real Real qz331 (@HMul.hMul Real Real Real qz326 (Enclosure.sfrac Bool.false 791361 4000) qz756) qz563)

noncomputable def Ns420p2301 := @Enclosure.Real.IsNear.subLit_ff_p qz275 qz757 42622375500733008676199 18014398509481984000 2498005398664653 676000000000000000000 791361 2000 0 1 Ns420p2300 35494429291301922506087 18014398509481984000 2498005398664653 676000000000000000000 

noncomputable def Ns420p2302 := nat_lit 95977057211373267867118578480135012352 

noncomputable def Ns420p2303 := nat_lit 57840884328486316032393216 

noncomputable def Ns420p2304 := nat_lit 997609719756426562478509895246618957367925446741727208949074745106767633223680 

noncomputable def Ns420p2305 := nat_lit 2624137880642144792824731794798889631264240820631165475819076180794918465536 

noncomputable def Ns420p2306 := nat_lit 69046984906814458328895939099551538184695264697629121602654326164746240 

noncomputable def Ns420p2307 := BSN.log_dyadic_bound 407857929284 4602161929284 4 3 Ns420p2304 134217728 54080000 Ns420p2305 Ns420p2306 23852163 5010019858568 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 407857929284) (BSN.artanhQ 4602161929284) 0 3 Ns420p2305 Ns420p2304 Ns420p2306 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns420p2308 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 791361 4000) qz756 791361 4000 0 1 53868521310841959 4503599627370496 3125002873 169000000000000000 42629446893069203516199 18014398509481984000 2473005398580153 676000000000000000000 (Enclosure.Real.IsNear.const Bool.false 791361 4000) (BSN.isNear_log_sfrac 2505009929284 16000000 53868521310841959 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2505009929284) qz335)) Bool.false Ns420p2303 Ns420p103 1000000919360000 54080000000000000000000 53868521310841959 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2505009929284 16000000 17 5010019858568 4194304000000 23852163 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns420p2307 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns420p2309 := BSN.arctan_dyadic_bound_f 1000 1582722 1 0 16777216 6760000 0 1 1 0 1 1 10600 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1582722) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1582722) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns420p2310 := @Enclosure.Real.IsNear.subLit_ff_p qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1582722))) 884279719003555 562949953421312 1 2000000000000000 10600 16777216 1 6760000 14829784580635681095680 883924042024355 562949953421312 50000000169 338000000000000000 qz16 (Ns420p2309 rfl) rfl rfl 

noncomputable abbrev qz276 := qz563

noncomputable def Ns420p2311 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 791361 4000) qz756) qz276 42629446893069203516199 18014398509481984000 2473005398580153 676000000000000000000 883924042024355 2251799813685248 50000000169 1352000000000000000 Ns420p2302 42622375500733008676199 18014398509481984000 2498005398664653 676000000000000000000 (Ns420p2308 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz11 qz14 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 1582722)))) 1 4 0 1 883924042024355 562949953421312 50000000169 338000000000000000 883924042024355 2251799813685248 50000000169 1352000000000000000 qz340 Ns420p2310 rfl) 

noncomputable def Ns420p2312 := @Ns420p2297 Ns420p2291 Ns420p2292 6639378701328307797 692224000000000000000000 (@Ns420p2299 6639378701328307797 692224000000000000000000 (Ns420p2301 (Ns420p2311 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 791361 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz757 (Real.log Real.pi) 791361 2000 0 1 38410761 33554432 1 67108864 30396778235721 67108864000 791361 134217728000 (Enclosure.Real.IsNear.const Bool.false 791361 2000) RS421to432.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns420p2293 Ns420p2294) 

noncomputable def Ns420p2313 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz271) Bool.false Ns420p2291 Ns420p2292 6639378701328307797 692224000000000000000000 50915130359 33554432 323 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz271) (@HAdd.hAdd Real Real Real qz341 qz564 (Enclosure.sfrac Bool.true Ns420p2293 Ns420p2294)) Bool.false Ns420p2291 Ns420p2292 6639378701328307797 692224000000000000000000 Ns420p2295 (Ns420p2312 rfl rfl)) 

noncomputable def Ns420p2314 := nat_lit 7595313475870928192667648 

noncomputable def Ns420p2315 := nat_lit 3509739900715503805730314778548090758159480398853636880201065485367618064451676861362959417874787280689502967253483878729334501903244988416 

noncomputable def Ns420p2316 := nat_lit 2500292557630980455765410079377196739232046913746971275588215383969409008517528082895944811684330609094540884054124738430641551446016 

noncomputable def Ns420p2317 := nat_lit 17526899859661539651274301364496721347363911476117762298771474493592609254411837065105049249271170092444509312936525884720691405121524862976 

noncomputable def Ns420p2318 := BSN.sin_dyadic_bound_f 107935896322 68719476736 4 3 33554432 13533204 Ns420p2315 Ns420p522 Ns420p2316 Ns420p2317 Ns420p525 Ns420p2316 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107935896322) qz659 0 3 Ns420p2315 Ns420p522 Ns420p2316 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107935896322) qz660 0 3 Ns420p2317 Ns420p525 Ns420p2316 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2319 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz271) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50915130359) qz342) Bool.false 50915130359 33554432 323 33554432 Bool.true 33554431 33554432 1 6760000 (Ns420p2313 rfl) (Enclosure.sfrac_false_div 50915130359 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50915130359) qz342) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns420p2314) qz343) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 241 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q1 50915130359 33554432 226375608064910080 72057594037927936 241 Ns420p2314 Ns420p103 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns420p2314 Ns420p103 107935896322 68719476736 13533204 13520000 (Ns420p2318 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns420p2320 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz271) Bool.false Ns420p2291 Ns420p2292 6639378701328307797 692224000000000000000000 407321042875 268435456 2576 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz271) (@HAdd.hAdd Real Real Real qz341 qz564 (Enclosure.sfrac Bool.true Ns420p2293 Ns420p2294)) Bool.false Ns420p2291 Ns420p2292 6639378701328307797 692224000000000000000000 Ns420p2295 (Ns420p2312 rfl rfl)) 

noncomputable def Ns420p2321 := Ns420p2290 46621 BSN.abs_quadSignPos (BSN.cos_quad_nat0 616 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 84900494 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 412 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 182709015 268435456) (@Eq.refl Real qz271) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 1) Bool.true 33554431 33554432 34641163 3544186880000 268435448 268435456 2624 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz271)) Bool.true 33554431 33554432 34641163 3544186880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz271) qz271) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz271)) Bool.true 33554431 33554432 2217034432 226827960320000 33554431 33554432 34641163 3544186880000 (Ns420p2319 rfl rfl) rfl)) rfl) (Ns420p2320 rfl) RS421to432.d7 

noncomputable def Ns420p2322 := nat_lit 6808812117098246525992185249352873447810239020668443534628905027000217677340656228956611613227534715574685696 

noncomputable def Ns420p2323 := nat_lit 2017406914103063786074736323431481854218482650689930347579303365974176764860798124414814701838858326016 

noncomputable def Ns420p2324 := nat_lit 41266951436907174502148979877657738622323377422447977056236301931005076175084725817583444531924307837231697920 

noncomputable def Ns420p2325 := BSN.cos_dyadic_bound_f 335273678 268435456 4 3 268435456 134217728 Ns420p2322 Ns420p140 Ns420p2323 Ns420p2324 Ns420p143 Ns420p2323 84900494 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 335273678) qz346 0 3 Ns420p2322 Ns420p140 Ns420p2323 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 335273678) qz347 0 3 Ns420p2324 Ns420p143 Ns420p2323 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2326 := nat_lit 20699548535705022541296479938570366305649454252360017147825598433160801 

noncomputable def Ns420p2327 := nat_lit 5627920646778455518520087848289812952272083135483628281180569562721 

noncomputable def Ns420p2328 := nat_lit 62087389765821510712852399640014519291043818590809084186914434160356961 

noncomputable def Ns420p2329 := BSN.cos_dyadic_bound_f 220695509 268435456 3 2 268435456 134217728 Ns420p2326 Ns420p156 Ns420p2327 Ns420p2328 Ns420p159 Ns420p2327 182709015 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 220695509) qz346 0 2 Ns420p2326 Ns420p156 Ns420p2327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 220695509) qz347 0 2 Ns420p2328 Ns420p159 Ns420p2327 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2330 := nat_lit 60286145474010979867640204983704681181693712132119841466864190591968385 

noncomputable def Ns420p2331 := nat_lit 14734659776668556218305586163316707829055731720477525417067649016961 

noncomputable def Ns420p2332 := nat_lit 157868429649437960086132804008295461758426965351814049753016675356746881 

noncomputable def Ns420p2333 := BSN.sin_dyadic_bound_f 248910097 268435456 3 2 268435456 134217728 Ns420p2330 Ns420p119 Ns420p2331 Ns420p2332 Ns420p122 Ns420p2331 214743074 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 248910097) qz344 0 2 Ns420p2330 Ns420p119 Ns420p2331 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 248910097) qz345 0 2 Ns420p2332 Ns420p122 Ns420p2331 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2334 := nat_lit 27319605622727603214177809840656 

noncomputable def Ns420p2335 := BSN.sin_dyadic_bound_f 72296722 268435456 2 1 268435456 134217728 Ns420p2334 Ns420p133 Ns420p2334 Ns420p2334 Ns420p134 Ns420p2334 71425859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 72296722) qz344 0 1 Ns420p2334 Ns420p133 Ns420p2334 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 72296722) qz345 0 1 Ns420p2334 Ns420p134 Ns420p2334 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2336 := Ns420p2288 79073 BSN.abs_quadSignPos (BSN.cos_quad_nat3 267 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 214743074 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 71425859 268435456) (@Eq.refl Real qz271) rfl rfl (Ns420p2321 RS421to432.d9 RS421to432.d11 RS421to432.d13 RS421to432.d17 (Ns420p2325 rfl rfl) (Ns420p2329 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns420p2320 rfl) RS421to432.d19 RS421to432.d21 RS421to432.d23 RS421to432.d25 RS421to432.d17 (Ns420p2333 rfl rfl) (Ns420p2335 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns420p2337 := nat_lit 5113141027690654932646899812865462006758384958164292044355358828823745 

noncomputable def Ns420p2338 := nat_lit 106041271483979794516110330022706074833829267540550711041401586881 

noncomputable def Ns420p2339 := nat_lit 13391388148559788856312663902684744684055562976378080176922348949112001 

noncomputable def Ns420p2340 := BSN.sin_dyadic_bound_f 134333511 268435456 3 2 268435456 134217728 Ns420p2337 Ns420p119 Ns420p2338 Ns420p2339 Ns420p122 Ns420p2338 128796410 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 134333511) qz344 0 2 Ns420p2337 Ns420p119 Ns420p2338 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 134333511) qz345 0 2 Ns420p2339 Ns420p122 Ns420p2338 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2341 := nat_lit 3768703916148330614031763734129194948847803050703682450018971529773056 

noncomputable def Ns420p2342 := nat_lit 186639442732773096001601298559641094839563333770217648382621515776 

noncomputable def Ns420p2343 := nat_lit 11305738469559526295903287999790465564353730025443506914760149346287616 

noncomputable def Ns420p2344 := BSN.cos_dyadic_bound_f 144170176 268435456 3 2 268435456 134217728 Ns420p2341 Ns420p156 Ns420p2342 Ns420p2343 Ns420p159 Ns420p2342 230642017 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 144170176) qz346 0 2 Ns420p2341 Ns420p156 Ns420p2342 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 144170176) qz347 0 2 Ns420p2343 Ns420p159 Ns420p2342 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2345 := Ns420p2286 106627 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 128796410 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 230642017 268435456) (@Eq.refl Real qz271) rfl rfl (Ns420p2336 rfl rfl) (Ns420p2320 rfl) RS421to432.d27 RS421to432.d29 RS421to432.d31 RS421to432.d33 RS421to432.d17 (Ns420p2340 rfl rfl) (Ns420p2344 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p2346 := nat_lit 70808119824814070554153895227762232617011185726759826864762165051040000 

noncomputable def Ns420p2347 := nat_lit 20325168861972760180955224587662877556682849491835535222240100000000 

noncomputable def Ns420p2348 := nat_lit 185416930220165086030110083804330583623747047528050860445922043543200000 

noncomputable def Ns420p2349 := BSN.sin_dyadic_bound_f 259121990 268435456 3 2 268435456 134217728 Ns420p2346 Ns420p119 Ns420p2347 Ns420p2348 Ns420p122 Ns420p2347 220713629 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 259121990) qz344 0 2 Ns420p2346 Ns420p119 Ns420p2347 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 259121990) qz345 0 2 Ns420p2348 Ns420p122 Ns420p2347 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2350 := nat_lit 14080671269090211512778007037280678930127605740062133258101781279995108628462216800098139316850731367508140625 

noncomputable def Ns420p2351 := nat_lit 17760006113119155140076858480352981355817251585940014539612010916327092139172672895757772897500244140625 

noncomputable def Ns420p2352 := nat_lit 85252825894166660068437892106532474758995380499892537696377617914996324991320759741499637283889469412845740625 

noncomputable def Ns420p2353 := BSN.cos_dyadic_bound_f 401902085 268435456 4 3 268435456 134217728 Ns420p2350 Ns420p140 Ns420p2351 Ns420p2352 Ns420p143 Ns420p2351 19737515 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 401902085) qz346 0 3 Ns420p2350 Ns420p140 Ns420p2351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 401902085) qz347 0 3 Ns420p2352 Ns420p143 Ns420p2351 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2354 := Ns420p2284 130703 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 220713629 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 19737515 268435456) (@Eq.refl Real qz271) rfl rfl (Ns420p2345 rfl) (Ns420p2320 rfl) RS421to432.d35 RS421to432.d37 RS421to432.d39 RS421to432.d41 RS421to432.d17 (Ns420p2349 rfl rfl) (Ns420p2353 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p2355 := nat_lit 39137495854356542830048542976 

noncomputable def Ns420p2356 := BSN.cos_dyadic_bound_f 14065276 268435456 2 1 268435456 134217728 Ns420p2355 Ns420p285 Ns420p2355 Ns420p2355 Ns420p286 Ns420p2355 268067049 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14065276) qz346 0 1 Ns420p2355 Ns420p285 Ns420p2355 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14065276) qz347 0 1 Ns420p2355 Ns420p286 Ns420p2355 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2357 := nat_lit 201806351643656350390036358416 

noncomputable def Ns420p2358 := BSN.cos_dyadic_bound_f 21195014 268435456 2 1 268435456 134217728 Ns420p2357 Ns420p285 Ns420p2357 Ns420p2357 Ns420p286 Ns420p2357 267599137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 21195014) qz346 0 1 Ns420p2357 Ns420p285 Ns420p2357 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 21195014) qz347 0 1 Ns420p2357 Ns420p286 Ns420p2357 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2359 := Ns420p2282 152357 BSN.abs_quadSignNeg qz651 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268067049 268435456) BSN.abs_quadSignNeg qz348 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267599137 268435456) (@Eq.refl Real qz271) rfl rfl (Ns420p2354 rfl) (Ns420p2320 rfl) RS421to432.d43 RS421to432.d45 RS421to432.d47 RS421to432.d49 RS421to432.d17 (Ns420p2356 rfl rfl) (Ns420p2358 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns420p2360 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 11) 235103353 268435456 152357 268435456 235103353 268435456 152357 268435456 126220151539367936 235103353 134217728 152357 134217728 (Ns420p2359 rfl) 

noncomputable def Ns420p2361 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz5 qz6 qz562) (Zeta.RiemannSiegel.correction qz273) 10016159 33554432 1 33554432 297897532623495 562949953421312 4731529499562761 59461588830126080000 2983789052464613055705 18889465931478580854784 

noncomputable def Ns420p2362 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz562 1 1 0 1 10016159 33554432 1 33554432 10016159 33554432 1 33554432 

noncomputable def Ns420p2363 := @Enclosure.Real.IsNear.sqrt_image qz272 4226147090433 33554432000 791361 33554432000 188285646 188285682 16777216 (@Enclosure.Real.IsNear.of_eq qz272 (@HMul.hMul Real Real Real qz5 qz271 qz3) Bool.false 4226147090433 33554432000 791361 33554432000 (BSN.t_div_two_pi_mk qz271 791361 1000 (@Eq.refl Real qz271)) (@Enclosure.Real.IsNear.mulLit_ff qz271 qz3 791361 1000 0 1 5340353 33554432 1 33554432 4226147090433 33554432000 791361 33554432000 (Enclosure.Real.IsNear.const Bool.false 791361 1000) RS421to432.d52 rfl)) 

noncomputable abbrev qz858 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 791361 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz758 := qz858

noncomputable abbrev qz566 := qz758

noncomputable abbrev qz277 := qz566

noncomputable def Ns420p2364 := @Enclosure.Real.IsNear.sqrt_image qz277 5883927 524288 9 8388608 56204172 56204178 16777216 (@Enclosure.Real.IsNear.recentre' qz277 Bool.false 376571328 33554432 36 33554432 5883927 524288 9 8388608 (Ns420p2363 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns420p2365 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz277) 56204175 16777216 3 16777216 5008079 5008080 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz277) Bool.false 112408350 33554432 6 33554432 56204175 16777216 3 16777216 (Ns420p2364 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns420p2366 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz277)) Bool.false 10016159 33554432 1 33554432 10016159 33554432 1 33554432 (Ns420p2365 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz278 := (@HMul.hMul Real Real Real qz326 qz322 qz561)

noncomputable abbrev qz759 := (@HMul.hMul Real Real Real qz795 qz857 qz857)

noncomputable abbrev qz567 := (@HSub.hSub Real Real Real qz624 (@HSub.hSub Real Real Real qz624 qz759 qz755) qz634)

noncomputable abbrev qz279 := (Real.cos (@HMul.hMul Real Real Real qz326 qz322 qz567))

noncomputable def Ns420p2367 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz273) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz278)) qz279) Bool.false 297897532623495 

noncomputable def Ns420p2368 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz278)) qz279 196580781 33554432 7963 

noncomputable def Ns420p2369 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz278)) Bool.false 196580781 33554432 7963 33554432 196580781 33554432 7963 

noncomputable def Ns420p2370 := @Enclosure.Real.IsNear.recentre' (Real.cos qz278) Bool.false 2863708 16777216 1568074432 226827960320000 715927 4194304 24501163 3544186880000 

noncomputable def Ns420p2371 := @Enclosure.Real.IsNear.cos_image qz278 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46951579) qz342) Bool.false 46951579 33554432 227 33554432 Bool.false 2863708 16777216 1 

noncomputable def Ns420p2372 := nat_lit 242874678697443643864957951 

noncomputable def Ns420p2373 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz273 884279719003555 140737488355328 1 500000000000000 116759 524288 9 8388608 103247615711136078245 73786976294838206464 Ns420p2372 

noncomputable def Ns420p2374 := @Enclosure.Real.IsNear.subLit_ff_p qz277 qz1 5883927 524288 9 8388608 11 1 0 1 116759 116759 524288 9 

noncomputable def Ns420p2375 := @Ns420p2374 8388608 (@Enclosure.Real.IsNear.recentre' qz277 Bool.false 376571328 33554432 36 33554432 5883927 524288 9 8388608 (Ns420p2363 rfl rfl rfl rfl rfl rfl) rfl) qz352 

noncomputable def Ns420p2376 := @Enclosure.Real.IsNear.recentre' qz278 Bool.false 103247615711136078245 73786976294838206464 Ns420p2372 Ns420p302 46951579 33554432 227 33554432 (@Ns420p2373 Ns420p302 RS421to432.d51 (Ns420p2375 rfl rfl) rfl) 

noncomputable def Ns420p2377 := nat_lit 156212527975407180168647609912477276720661051070260527890949423961584169721226778812772843256973521 

noncomputable def Ns420p2378 := nat_lit 114763141521535256519126967530818247283651569277795933667327632338783982994809929416750303441 

noncomputable def Ns420p2379 := nat_lit 946250365431267453935867268671464663175029713021431679026593539491098868717044434107008766541203665 

noncomputable def Ns420p2380 := BSN.cos_dyadic_bound_f 46951579 33554432 4 3 16777216 6760000 Ns420p2377 Ns420p1201 Ns420p2378 Ns420p2379 Ns420p1204 Ns420p2378 2863708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 46951579) qz635 0 3 Ns420p2377 Ns420p1201 Ns420p2378 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 46951579) (BSN.cosOddQ 33554432) 0 3 Ns420p2379 Ns420p1204 Ns420p2378 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2381 := @Enclosure.Real.IsNear.inv_image (Real.cos qz278) 715927 4194304 24501163 3544186880000 98286409 98294372 16777216 (Ns420p2370 (@Ns420p2371 6760000 (Ns420p2376 rfl) (Enclosure.sfrac_false_div 46951579 33554432) (Ns420p2380 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns420p2382 := @Enclosure.Real.IsNear.recentre' qz279 Bool.false 1515395 16777216 

noncomputable abbrev qz280 := (@HMul.hMul Real Real Real qz326 qz322 qz567)

noncomputable def Ns420p2383 := @Enclosure.Real.IsNear.cos_image qz280 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 49672251)) qz342) Bool.true 49672251 33554432 

noncomputable def Ns420p2384 := nat_lit 57268207477688928562055725 

noncomputable def Ns420p2385 := nat_lit 38685626227668133590597632 

noncomputable def Ns420p2386 := nat_lit 588966481211974215221309985592171 

noncomputable def Ns420p2387 := @Enclosure.Real.IsNear.recentre' qz280 Bool.true Ns420p2384 Ns420p2385 Ns420p2386 

noncomputable abbrev qz281 := qz567

noncomputable def Ns420p2388 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz281 884279719003555 140737488355328 1 500000000000000 64762547695 

noncomputable abbrev qz568 := (@HSub.hSub Real Real Real qz624 qz759 qz755)

noncomputable abbrev qz282 := qz568

noncomputable def Ns420p2389 := @Enclosure.Real.IsNear.subLit_tf qz282 qz27 47582678511 274877906944 109124145 70368744177664 1 16 

noncomputable abbrev qz569 := qz759

noncomputable abbrev qz283 := qz569

noncomputable def Ns420p2390 := @Enclosure.Real.IsNear.subLit_ff_n qz283 qz273 13632664081 274877906944 33626673 70368744177664 116759 524288 9 8388608 

noncomputable def Ns420p2391 := @Enclosure.Real.IsNear.mulLit_ff qz273 qz273 116759 524288 9 8388608 116759 524288 9 8388608 13632664081 274877906944 

noncomputable def Ns420p2392 := nat_lit 195803479308198196807356338945404028484430549986270582487711387473683701116752084958581605932307281 

noncomputable def Ns420p2393 := nat_lit 225614026634384430844042068748064369104308360437055522111431711829926949421513536329851442001 

noncomputable def Ns420p2394 := nat_lit 1185616017096540418833934951592955845055220717342265034876745240537941110583982444209162524857307985 

noncomputable def Ns420p2395 := BSN.cos_dyadic_bound_f 49672251 33554432 4 3 16777216 6760000 Ns420p2392 Ns420p1201 Ns420p2393 Ns420p2394 Ns420p1204 Ns420p2393 1515395 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 49672251) qz635 0 3 Ns420p2392 Ns420p1201 Ns420p2393 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 49672251) (BSN.cosOddQ 33554432) 0 3 Ns420p2394 Ns420p1204 Ns420p2393 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns420p2396 := @Ns420p2382 281354304 28353495040000 1515395 16777216 4396161 443023360000 (@Ns420p2383 41 4194304 Bool.false 1515395 16777216 1 6760000 (@Ns420p2387 Ns420p1079 49672251 33554432 41 4194304 (@Ns420p2388 274877906944 109124145 70368744177664 Ns420p2384 Ns420p2385 Ns420p2386 Ns420p1079 RS421to432.d51 (@Ns420p2389 0 1 1036200763120 64762547695 274877906944 109124145 70368744177664 (@Ns420p2390 24947027351175168 47582678511 274877906944 109124145 70368744177664 (@Ns420p2391 33626673 70368744177664 (Ns420p2375 rfl rfl) (Ns420p2375 rfl rfl) rfl) (Ns420p2375 rfl rfl) rfl rfl) qz356 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 49672251 33554432) (BSN.cos_neg_of_bound 49672251 33554432 Bool.false 1515395 16777216 1 6760000 (Ns420p2395 rfl rfl)) rfl rfl) 

noncomputable def Ns420p2397 := @Ns420p2361 9484644387844780175427 Ns420p2278 (Ns420p2362 qz29 (@Enclosure.Real.IsNear.of_eq qz562 (@Inv.inv Real Real.instInv (Real.sqrt qz277)) Bool.false 10016159 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz272 (BSN.t_div_two_pi_nonneg qz271 791361 1000 (@Eq.refl Real qz271))) Ns420p2366) rfl) (@Ns420p2367 562949953421312 4731529499562761 59461588830126080000 (BSN.correction_mk qz273 (BSN.cos_two_pi_p_ne_zero_mk qz271 791361 1000 11 (@Eq.refl Real qz271) rfl rfl (@BSN.floor_sqrt_eq_dec qz271 791361 1000 11 (@Eq.refl Real qz271) rfl rfl rfl))) (@Ns420p2368 33554432 1515395 16777216 4396161 443023360000 297897532623495 562949953421312 4731529499562761 59461588830126080000 (@Ns420p2369 33554432 (Ns420p2381 rfl rfl rfl rfl rfl) rfl) (Ns420p2396 rfl) rfl)) 

noncomputable def Ns420p2398 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz271) (hardyZApproximantRS₀ qz271) Bool.true 30104066352671455159079 18889465931478580854784 462454108857420738703427 Ns420p2278 (@Eq.refl Real (hardyZApproximantRS₀ qz271)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz271) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz271) qz271 11) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz562) (Zeta.RiemannSiegel.correction qz273))) Bool.true 30104066352671455159079 18889465931478580854784 462454108857420738703427 Ns420p2278 (BSN.hardyZApproximantRS₀_eq qz271 11 (@BSN.floor_sqrt_eq_dec qz271 791361 1000 11 (@Eq.refl Real qz271) rfl rfl rfl)) (@Ns420p2280 30104066352671455159079 18889465931478580854784 462454108857420738703427 Ns420p2278 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz271) qz271 11) (@HAdd.hAdd Real Real Real qz341 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz271) qz271 11)) Bool.true 235103353 134217728 152357 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz271) qz271 11) (Ns420p2360 (Ns420p2359 rfl) rfl rfl)) (Ns420p2397 rfl) rfl rfl)) 

theorem RS421to432.d80 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz271) Bool.true 30104066352671455159079 18889465931478580854784 462454108857420738703427 Ns420p2278 := Ns420p2398 

noncomputable def RS421to432.d81 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz284 := (RS421to432.d3 qz325 qz357 (@Enclosure.dec_le_dec qz325 qz357 775738 1000 777042 1000 (@Eq.refl Real qz325) (@Eq.refl Real qz357) rfl rfl rfl))

noncomputable abbrev qz760 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz284)

noncomputable def Ns420p2399 := @Enclosure.Real.IsNear.of_eq qz760 (hardyZApproximantRS₀ qz4) Bool.true 2655953409910698044259 4722366482869645213696 278797342133710947126231 Ns420p77 

noncomputable abbrev qz285 := (@Enclosure.dec_le_dec qz325 qz357 775738 1000 777042 1000 (@Eq.refl Real qz325) (@Eq.refl Real qz357) rfl rfl rfl)

noncomputable def Ns420p2400 := @Enclosure.Real.IsNear.neg_val qz760 2655953409910698044259 4722366482869645213696 278797342133710947126231 Ns420p77 (Ns420p2399 (RS421to432.d4 qz4 qz30 qz285) RS421to432.d53) rfl 

noncomputable abbrev qz761 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz284)

noncomputable def Ns420p2401 := @Enclosure.Real.IsNear.of_eq qz761 (hardyZApproximantRS₀ qz30) Bool.false 23745112061854647476797 18889465931478580854784 Ns420p205 Ns420p206 

noncomputable def Ns420p2402 := @Enclosure.Real.IsNear.pos_val qz761 23745112061854647476797 18889465931478580854784 Ns420p205 Ns420p206 (Ns420p2401 (RS421to432.d54 qz4 qz30 qz285) RS421to432.d55) rfl 

noncomputable def Ns420p2403 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz760 qz4 qz4 775738 1000 775738 1000 

noncomputable def Ns420p2404 := @Enclosure.norm_gt_of_isNear qz760 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2655953409910698044259 4722366482869645213696 278797342133710947126231 

noncomputable def Ns420p2405 := @Ns420p2404 Ns420p77 269968109 5368709120 1421 5368709120 (Ns420p2399 (RS421to432.d4 qz4 qz30 qz285) RS421to432.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2406 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz761 qz4 qz30 775738 1000 777042 1000 

noncomputable def Ns420p2407 := @Enclosure.norm_gt_of_isNear qz761 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 23745112061854647476797 18889465931478580854784 Ns420p205 

noncomputable def Ns420p2408 := @Ns420p2407 Ns420p206 269968109 5368709120 1421 5368709120 (Ns420p2401 (RS421to432.d54 qz4 qz30 qz285) RS421to432.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2409 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz4 775738 1000 qz10 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz760 qz761 (Ns420p2400 rfl rfl) (Ns420p2402 rfl rfl)) (Ns420p2403 qz10 qz10 rfl rfl rfl rfl (Ns420p2405 rfl)) (Ns420p2406 qz10 qz33 rfl rfl rfl rfl (Ns420p2408 rfl)) 

noncomputable abbrev qz286 := (RS421to432.d3 qz357 qz375 (@Enclosure.dec_le_dec qz357 qz375 777042 1000 778346 1000 (@Eq.refl Real qz357) (@Eq.refl Real qz375) rfl rfl rfl))

noncomputable abbrev qz762 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz286)

noncomputable def Ns420p2410 := @Enclosure.Real.IsNear.of_eq qz762 (hardyZApproximantRS₀ qz30) Bool.false 23745112061854647476797 18889465931478580854784 Ns420p205 Ns420p206 

noncomputable abbrev qz287 := (@Enclosure.dec_le_dec qz357 qz375 777042 1000 778346 1000 (@Eq.refl Real qz357) (@Eq.refl Real qz375) rfl rfl rfl)

noncomputable def Ns420p2411 := @Enclosure.Real.IsNear.pos_val qz762 23745112061854647476797 18889465931478580854784 Ns420p205 Ns420p206 (Ns420p2410 (RS421to432.d4 qz30 qz54 qz287) RS421to432.d55) rfl 

noncomputable abbrev qz763 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz286)

noncomputable def Ns420p2412 := @Enclosure.Real.IsNear.of_eq qz763 (hardyZApproximantRS₀ qz54) Bool.true 5614900053728551108923 1180591620717411303424 279915257413148883033957 Ns420p77 

noncomputable def Ns420p2413 := @Enclosure.Real.IsNear.neg_val qz763 5614900053728551108923 1180591620717411303424 279915257413148883033957 Ns420p77 (Ns420p2412 (RS421to432.d54 qz30 qz54 qz287) RS421to432.d57) rfl 

noncomputable def Ns420p2414 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz762 qz4 qz30 775738 1000 777042 1000 

noncomputable def Ns420p2415 := @Enclosure.norm_gt_of_isNear qz762 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 23745112061854647476797 18889465931478580854784 Ns420p205 

noncomputable def Ns420p2416 := @Ns420p2415 Ns420p206 269968109 5368709120 1421 5368709120 (Ns420p2410 (RS421to432.d4 qz30 qz54 qz287) RS421to432.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2417 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz763 qz4 qz54 775738 1000 778346 1000 

noncomputable def Ns420p2418 := @Enclosure.norm_gt_of_isNear qz763 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 5614900053728551108923 1180591620717411303424 279915257413148883033957 

noncomputable def Ns420p2419 := @Ns420p2418 Ns420p77 269968109 5368709120 1421 5368709120 (Ns420p2412 (RS421to432.d54 qz30 qz54 qz287) RS421to432.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2420 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz286 (@BSN.thirtyTwoPi_le_dec qz30 777042 1000 qz33 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz762 qz763 (Ns420p2411 rfl rfl) (Ns420p2413 rfl rfl)) (Ns420p2414 qz10 qz33 rfl rfl rfl rfl (Ns420p2416 rfl)) (Ns420p2417 qz10 qz57 rfl rfl rfl rfl (Ns420p2419 rfl)) 

noncomputable abbrev qz288 := (RS421to432.d3 qz375 qz386 (@Enclosure.dec_le_dec qz375 qz386 778346 1000 779649 1000 (@Eq.refl Real qz375) (@Eq.refl Real qz386) rfl rfl rfl))

noncomputable abbrev qz764 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz288)

noncomputable def Ns420p2421 := @Enclosure.Real.IsNear.of_eq qz764 (hardyZApproximantRS₀ qz54) Bool.true 5614900053728551108923 1180591620717411303424 279915257413148883033957 Ns420p77 

noncomputable abbrev qz289 := (@Enclosure.dec_le_dec qz375 qz386 778346 1000 779649 1000 (@Eq.refl Real qz375) (@Eq.refl Real qz386) rfl rfl rfl)

noncomputable def Ns420p2422 := @Enclosure.Real.IsNear.neg_val qz764 5614900053728551108923 1180591620717411303424 279915257413148883033957 Ns420p77 (Ns420p2421 (RS421to432.d4 qz54 qz68 qz289) RS421to432.d57) rfl 

noncomputable abbrev qz765 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz288)

noncomputable def Ns420p2423 := @Enclosure.Real.IsNear.of_eq qz765 (hardyZApproximantRS₀ qz68) Bool.false 21719080280851405088757 9444732965739290427392 224340364006372997977091 Ns420p484 

noncomputable def Ns420p2424 := @Enclosure.Real.IsNear.pos_val qz765 21719080280851405088757 9444732965739290427392 224340364006372997977091 Ns420p484 (Ns420p2423 (RS421to432.d54 qz54 qz68 qz289) RS421to432.d58) rfl 

noncomputable def Ns420p2425 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz764 qz4 qz54 775738 1000 778346 1000 

noncomputable def Ns420p2426 := @Enclosure.norm_gt_of_isNear qz764 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 5614900053728551108923 1180591620717411303424 279915257413148883033957 

noncomputable def Ns420p2427 := @Ns420p2426 Ns420p77 269968109 5368709120 1421 5368709120 (Ns420p2421 (RS421to432.d4 qz54 qz68 qz289) RS421to432.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2428 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz765 qz4 qz68 775738 1000 779649 1000 

noncomputable def Ns420p2429 := @Enclosure.norm_gt_of_isNear qz765 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 21719080280851405088757 9444732965739290427392 224340364006372997977091 

noncomputable def Ns420p2430 := @Ns420p2429 Ns420p484 269968109 5368709120 1421 5368709120 (Ns420p2423 (RS421to432.d54 qz54 qz68 qz289) RS421to432.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2431 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz54 778346 1000 qz57 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz764 qz765 (Ns420p2422 rfl rfl) (Ns420p2424 rfl rfl)) (Ns420p2425 qz10 qz57 rfl rfl rfl rfl (Ns420p2427 rfl)) (Ns420p2428 qz10 qz71 rfl rfl rfl rfl (Ns420p2430 rfl)) 

noncomputable abbrev qz290 := (RS421to432.d3 qz386 qz397 (@Enclosure.dec_le_dec qz386 qz397 779649 1000 780953 1000 (@Eq.refl Real qz386) (@Eq.refl Real qz397) rfl rfl rfl))

noncomputable abbrev qz766 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz290)

noncomputable def Ns420p2432 := @Enclosure.Real.IsNear.of_eq qz766 (hardyZApproximantRS₀ qz68) Bool.false 21719080280851405088757 9444732965739290427392 224340364006372997977091 Ns420p484 

noncomputable abbrev qz291 := (@Enclosure.dec_le_dec qz386 qz397 779649 1000 780953 1000 (@Eq.refl Real qz386) (@Eq.refl Real qz397) rfl rfl rfl)

noncomputable def Ns420p2433 := @Enclosure.Real.IsNear.pos_val qz766 21719080280851405088757 9444732965739290427392 224340364006372997977091 Ns420p484 (Ns420p2432 (RS421to432.d4 qz68 qz82 qz291) RS421to432.d58) rfl 

noncomputable abbrev qz767 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz290)

noncomputable def Ns420p2434 := @Enclosure.Real.IsNear.of_eq qz767 (hardyZApproximantRS₀ qz82) Bool.true 13940955815292912167305 4722366482869645213696 562130941679536939025409 Ns420p607 

noncomputable def Ns420p2435 := @Enclosure.Real.IsNear.neg_val qz767 13940955815292912167305 4722366482869645213696 562130941679536939025409 Ns420p607 (Ns420p2434 (RS421to432.d54 qz68 qz82 qz291) RS421to432.d59) rfl 

noncomputable def Ns420p2436 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz766 qz4 qz68 775738 1000 779649 1000 

noncomputable def Ns420p2437 := @Enclosure.norm_gt_of_isNear qz766 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 21719080280851405088757 9444732965739290427392 224340364006372997977091 

noncomputable def Ns420p2438 := @Ns420p2437 Ns420p484 269968109 5368709120 1421 5368709120 (Ns420p2432 (RS421to432.d4 qz68 qz82 qz291) RS421to432.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2439 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz767 qz4 qz82 775738 1000 780953 1000 

noncomputable def Ns420p2440 := @Enclosure.norm_gt_of_isNear qz767 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 13940955815292912167305 4722366482869645213696 562130941679536939025409 

noncomputable def Ns420p2441 := @Ns420p2440 Ns420p607 269968109 5368709120 1421 5368709120 (Ns420p2434 (RS421to432.d54 qz68 qz82 qz291) RS421to432.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2442 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz290 (@BSN.thirtyTwoPi_le_dec qz68 779649 1000 qz71 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz766 qz767 (Ns420p2433 rfl rfl) (Ns420p2435 rfl rfl)) (Ns420p2436 qz10 qz71 rfl rfl rfl rfl (Ns420p2438 rfl)) (Ns420p2439 qz10 qz85 rfl rfl rfl rfl (Ns420p2441 rfl)) 

noncomputable abbrev qz292 := (RS421to432.d3 qz397 qz408 (@Enclosure.dec_le_dec qz397 qz408 780953 1000 782255 1000 (@Eq.refl Real qz397) (@Eq.refl Real qz408) rfl rfl rfl))

noncomputable abbrev qz768 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz292)

noncomputable def Ns420p2443 := @Enclosure.Real.IsNear.of_eq qz768 (hardyZApproximantRS₀ qz82) Bool.true 13940955815292912167305 4722366482869645213696 562130941679536939025409 Ns420p607 

noncomputable abbrev qz293 := (@Enclosure.dec_le_dec qz397 qz408 780953 1000 782255 1000 (@Eq.refl Real qz397) (@Eq.refl Real qz408) rfl rfl rfl)

noncomputable def Ns420p2444 := @Enclosure.Real.IsNear.neg_val qz768 13940955815292912167305 4722366482869645213696 562130941679536939025409 Ns420p607 (Ns420p2443 (RS421to432.d4 qz82 qz96 qz293) RS421to432.d59) rfl 

noncomputable abbrev qz769 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz292)

noncomputable def Ns420p2445 := @Enclosure.Real.IsNear.of_eq qz769 (hardyZApproximantRS₀ qz96) Bool.false 912186111720756214207 4722366482869645213696 112667944673016556892357 Ns420p726 

noncomputable def Ns420p2446 := @Enclosure.Real.IsNear.pos_val qz769 912186111720756214207 4722366482869645213696 112667944673016556892357 Ns420p726 (Ns420p2445 (RS421to432.d54 qz82 qz96 qz293) RS421to432.d60) rfl 

noncomputable def Ns420p2447 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz768 qz4 qz82 775738 1000 780953 1000 

noncomputable def Ns420p2448 := @Enclosure.norm_gt_of_isNear qz768 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 13940955815292912167305 4722366482869645213696 562130941679536939025409 

noncomputable def Ns420p2449 := @Ns420p2448 Ns420p607 269968109 5368709120 1421 5368709120 (Ns420p2443 (RS421to432.d4 qz82 qz96 qz293) RS421to432.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2450 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz769 qz4 qz96 775738 1000 782255 1000 

noncomputable def Ns420p2451 := @Enclosure.norm_gt_of_isNear qz769 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 912186111720756214207 4722366482869645213696 112667944673016556892357 

noncomputable def Ns420p2452 := @Ns420p2451 Ns420p726 269968109 5368709120 1421 5368709120 (Ns420p2445 (RS421to432.d54 qz82 qz96 qz293) RS421to432.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2453 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz82 780953 1000 qz85 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz768 qz769 (Ns420p2444 rfl rfl) (Ns420p2446 rfl rfl)) (Ns420p2447 qz10 qz85 rfl rfl rfl rfl (Ns420p2449 rfl)) (Ns420p2450 qz10 qz99 rfl rfl rfl rfl (Ns420p2452 rfl)) 

noncomputable abbrev qz294 := (RS421to432.d3 qz408 qz419 (@Enclosure.dec_le_dec qz408 qz419 782255 1000 783557 1000 (@Eq.refl Real qz408) (@Eq.refl Real qz419) rfl rfl rfl))

noncomputable abbrev qz770 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz294)

noncomputable def Ns420p2454 := @Enclosure.Real.IsNear.of_eq qz770 (hardyZApproximantRS₀ qz96) Bool.false 912186111720756214207 4722366482869645213696 112667944673016556892357 Ns420p726 

noncomputable abbrev qz295 := (@Enclosure.dec_le_dec qz408 qz419 782255 1000 783557 1000 (@Eq.refl Real qz408) (@Eq.refl Real qz419) rfl rfl rfl)

noncomputable def Ns420p2455 := @Enclosure.Real.IsNear.pos_val qz770 912186111720756214207 4722366482869645213696 112667944673016556892357 Ns420p726 (Ns420p2454 (RS421to432.d4 qz96 qz110 qz295) RS421to432.d60) rfl 

noncomputable abbrev qz771 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz294)

noncomputable def Ns420p2456 := @Enclosure.Real.IsNear.of_eq qz771 (hardyZApproximantRS₀ qz110) Bool.true 5539973308911899110811 2361183241434822606848 56467642179134153086601 Ns420p851 

noncomputable def Ns420p2457 := @Enclosure.Real.IsNear.neg_val qz771 5539973308911899110811 2361183241434822606848 56467642179134153086601 Ns420p851 (Ns420p2456 (RS421to432.d54 qz96 qz110 qz295) RS421to432.d61) rfl 

noncomputable def Ns420p2458 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz770 qz4 qz96 775738 1000 782255 1000 

noncomputable def Ns420p2459 := @Enclosure.norm_gt_of_isNear qz770 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 912186111720756214207 4722366482869645213696 112667944673016556892357 

noncomputable def Ns420p2460 := @Ns420p2459 Ns420p726 269968109 5368709120 1421 5368709120 (Ns420p2454 (RS421to432.d4 qz96 qz110 qz295) RS421to432.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2461 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz771 qz4 qz110 775738 1000 783557 1000 

noncomputable def Ns420p2462 := @Enclosure.norm_gt_of_isNear qz771 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 5539973308911899110811 2361183241434822606848 56467642179134153086601 

noncomputable def Ns420p2463 := @Ns420p2462 Ns420p851 269968109 5368709120 1421 5368709120 (Ns420p2456 (RS421to432.d54 qz96 qz110 qz295) RS421to432.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2464 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz294 (@BSN.thirtyTwoPi_le_dec qz96 782255 1000 qz99 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz770 qz771 (Ns420p2455 rfl rfl) (Ns420p2457 rfl rfl)) (Ns420p2458 qz10 qz99 rfl rfl rfl rfl (Ns420p2460 rfl)) (Ns420p2461 qz10 qz113 rfl rfl rfl rfl (Ns420p2463 rfl)) 

noncomputable abbrev qz296 := (RS421to432.d3 qz419 qz430 (@Enclosure.dec_le_dec qz419 qz430 783557 1000 784859 1000 (@Eq.refl Real qz419) qz434 rfl rfl rfl))

noncomputable abbrev qz772 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz296)

noncomputable def Ns420p2465 := @Enclosure.Real.IsNear.of_eq qz772 (hardyZApproximantRS₀ qz110) Bool.true 5539973308911899110811 2361183241434822606848 56467642179134153086601 Ns420p851 

noncomputable abbrev qz297 := (@Enclosure.dec_le_dec qz419 qz430 783557 1000 784859 1000 (@Eq.refl Real qz419) qz434 rfl rfl rfl)

noncomputable def Ns420p2466 := @Enclosure.Real.IsNear.neg_val qz772 5539973308911899110811 2361183241434822606848 56467642179134153086601 Ns420p851 (Ns420p2465 (RS421to432.d4 qz110 qz124 qz297) RS421to432.d61) rfl 

noncomputable abbrev qz773 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz296)

noncomputable def Ns420p2467 := @Enclosure.Real.IsNear.of_eq qz773 (hardyZApproximantRS₀ qz124) Bool.false 8359739072432259577257 4722366482869645213696 113204843106767249260251 Ns420p726 

noncomputable def Ns420p2468 := @Enclosure.Real.IsNear.pos_val qz773 8359739072432259577257 4722366482869645213696 113204843106767249260251 Ns420p726 (Ns420p2467 (RS421to432.d54 qz110 qz124 qz297) RS421to432.d62) rfl 

noncomputable def Ns420p2469 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz772 qz4 qz110 775738 1000 783557 1000 

noncomputable def Ns420p2470 := @Enclosure.norm_gt_of_isNear qz772 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 5539973308911899110811 2361183241434822606848 56467642179134153086601 

noncomputable def Ns420p2471 := @Ns420p2470 Ns420p851 269968109 5368709120 1421 5368709120 (Ns420p2465 (RS421to432.d4 qz110 qz124 qz297) RS421to432.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2472 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz773 qz4 qz124 775738 1000 784859 1000 

noncomputable def Ns420p2473 := @Enclosure.norm_gt_of_isNear qz773 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 8359739072432259577257 4722366482869645213696 113204843106767249260251 

noncomputable def Ns420p2474 := @Ns420p2473 Ns420p726 269968109 5368709120 1421 5368709120 (Ns420p2467 (RS421to432.d54 qz110 qz124 qz297) RS421to432.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2475 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz110 783557 1000 qz113 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz772 qz773 (Ns420p2466 rfl rfl) (Ns420p2468 rfl rfl)) (Ns420p2469 qz10 qz113 rfl rfl rfl rfl (Ns420p2471 rfl)) (Ns420p2472 qz10 qz127 rfl rfl rfl rfl (Ns420p2474 rfl)) 

noncomputable abbrev qz570 := (@Enclosure.dec_le_dec qz684 qz691 784859 1000 786160 1000 (@Eq.refl Real qz684) (@Eq.refl Real qz691) rfl rfl rfl)

noncomputable abbrev qz298 := (RS421to432.d3 qz430 qz442 qz570)

noncomputable abbrev qz774 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz298)

noncomputable def Ns420p2476 := @Enclosure.Real.IsNear.of_eq qz774 (hardyZApproximantRS₀ qz124) Bool.false 8359739072432259577257 4722366482869645213696 113204843106767249260251 Ns420p726 

noncomputable abbrev qz299 := qz570

noncomputable def Ns420p2477 := @Enclosure.Real.IsNear.pos_val qz774 8359739072432259577257 4722366482869645213696 113204843106767249260251 Ns420p726 (Ns420p2476 (RS421to432.d4 qz124 qz138 qz299) RS421to432.d62) rfl 

noncomputable abbrev qz775 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz298)

noncomputable def Ns420p2478 := @Enclosure.Real.IsNear.of_eq qz775 (hardyZApproximantRS₀ qz138) Bool.true 542516394780706672139 1180591620717411303424 113542431845842210593521 Ns420p726 

noncomputable def Ns420p2479 := @Enclosure.Real.IsNear.neg_val qz775 542516394780706672139 1180591620717411303424 113542431845842210593521 Ns420p726 (Ns420p2478 (RS421to432.d54 qz124 qz138 qz299) RS421to432.d63) rfl 

noncomputable def Ns420p2480 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz774 qz4 qz124 775738 1000 784859 1000 

noncomputable def Ns420p2481 := @Enclosure.norm_gt_of_isNear qz774 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 8359739072432259577257 4722366482869645213696 113204843106767249260251 

noncomputable def Ns420p2482 := @Ns420p2481 Ns420p726 269968109 5368709120 1421 5368709120 (Ns420p2476 (RS421to432.d4 qz124 qz138 qz299) RS421to432.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2483 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz775 qz4 qz138 775738 1000 786160 1000 

noncomputable def Ns420p2484 := @Enclosure.norm_gt_of_isNear qz775 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 542516394780706672139 1180591620717411303424 113542431845842210593521 

noncomputable def Ns420p2485 := @Ns420p2484 Ns420p726 269968109 5368709120 1421 5368709120 (Ns420p2478 (RS421to432.d54 qz124 qz138 qz299) RS421to432.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2486 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz298 (@BSN.thirtyTwoPi_le_dec qz124 784859 1000 qz127 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz774 qz775 (Ns420p2477 rfl rfl) (Ns420p2479 rfl rfl)) (Ns420p2480 qz10 qz127 rfl rfl rfl rfl (Ns420p2482 rfl)) (Ns420p2483 qz10 qz141 rfl rfl rfl rfl (Ns420p2485 rfl)) 

noncomputable abbrev qz571 := (@Enclosure.dec_le_dec qz691 qz710 786160 1000 787461 1000 (@Eq.refl Real qz691) qz715 rfl rfl rfl)

noncomputable abbrev qz300 := (RS421to432.d3 qz442 qz481 qz571)

noncomputable abbrev qz776 := (Zeta.Certificates.ZIntervalRS.fstVal qz300)

noncomputable def Ns420p2487 := @Enclosure.Real.IsNear.of_eq qz776 (hardyZApproximantRS qz138) Bool.true Ns420p1227 Ns420p1228 Ns420p1229 Ns420p1230 

noncomputable abbrev qz301 := qz571

noncomputable def Ns420p2488 := @Enclosure.Real.IsNear.neg_val qz776 Ns420p1227 Ns420p1228 Ns420p1229 Ns420p1230 (Ns420p2487 (RS421to432.d64 qz138 qz181 qz301) RS421to432.d73) rfl 

noncomputable abbrev qz777 := (Zeta.Certificates.ZIntervalRS.sndVal qz300)

noncomputable def Ns420p2489 := @Enclosure.Real.IsNear.of_eq qz777 (hardyZApproximantRS qz181) Bool.false Ns420p1475 Ns420p1476 Ns420p1477 Ns420p1478 

noncomputable def Ns420p2490 := @Enclosure.Real.IsNear.pos_val qz777 Ns420p1475 Ns420p1476 Ns420p1477 Ns420p1478 (Ns420p2489 (RS421to432.d74 qz138 qz181 qz301) RS421to432.d75) rfl 

noncomputable def Ns420p2491 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz776 qz4 qz138 775738 1000 786160 1000 

noncomputable def Ns420p2492 := @Enclosure.norm_gt_of_isNear qz776 (hardyZErrorBoundRS qz4) Bool.true Bool.false Ns420p1227 Ns420p1228 Ns420p1229 

noncomputable def Ns420p2493 := @Ns420p2492 Ns420p1230 16306601 1073741824 201 1073741824 (Ns420p2487 (RS421to432.d64 qz138 qz181 qz301) RS421to432.d73) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 16306601 1073741824 201 1073741824 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS421to432.d76) rfl rfl rfl rfl 

noncomputable def Ns420p2494 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz777 qz4 qz181 775738 1000 787461 1000 

noncomputable def Ns420p2495 := @Enclosure.norm_gt_of_isNear qz777 (hardyZErrorBoundRS qz4) Bool.false Bool.false Ns420p1475 Ns420p1476 Ns420p1477 

noncomputable def Ns420p2496 := @Ns420p2495 Ns420p1478 16306601 1073741824 201 1073741824 (Ns420p2489 (RS421to432.d74 qz138 qz181 qz301) RS421to432.d75) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 16306601 1073741824 201 1073741824 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS421to432.d76) rfl rfl rfl rfl 

noncomputable def Ns420p2497 := @Zeta.Certificates.ZIntervalRS.Certificate.mk qz300 (@BSN.thirtyTwoPi_le_dec qz138 786160 1000 qz141 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz776 qz777 (Ns420p2488 rfl rfl) (Ns420p2490 rfl rfl)) (Ns420p2491 qz10 qz141 rfl rfl rfl rfl (Ns420p2493 rfl)) (Ns420p2494 qz10 qz186 rfl rfl rfl rfl (Ns420p2496 rfl)) 

noncomputable abbrev qz778 := (@Enclosure.dec_le_dec qz837 qz843 787461 1000 788762 1000 (@Eq.refl Real qz837) qz847 rfl rfl rfl)

noncomputable abbrev qz572 := qz778

noncomputable abbrev qz302 := (RS421to432.d3 qz481 qz516 qz572)

noncomputable abbrev qz779 := (Zeta.Certificates.ZIntervalRS.fstVal qz302)

noncomputable def Ns420p2498 := @Enclosure.Real.IsNear.of_eq qz779 (hardyZApproximantRS qz181) Bool.false Ns420p1475 Ns420p1476 Ns420p1477 Ns420p1478 

noncomputable abbrev qz303 := qz572

noncomputable def Ns420p2499 := @Enclosure.Real.IsNear.pos_val qz779 Ns420p1475 Ns420p1476 Ns420p1477 Ns420p1478 (Ns420p2498 (RS421to432.d64 qz181 qz217 qz303) RS421to432.d75) rfl 

noncomputable abbrev qz780 := (Zeta.Certificates.ZIntervalRS.sndVal qz302)

noncomputable def Ns420p2500 := @Enclosure.Real.IsNear.of_eq qz780 (hardyZApproximantRS qz217) Bool.true Ns420p1818 Ns420p1819 Ns420p1820 Ns420p1821 

noncomputable def Ns420p2501 := @Enclosure.Real.IsNear.neg_val qz780 Ns420p1818 Ns420p1819 Ns420p1820 Ns420p1821 (Ns420p2500 (RS421to432.d74 qz181 qz217 qz303) RS421to432.d77) rfl 

noncomputable def Ns420p2502 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz779 qz4 qz181 775738 1000 787461 1000 

noncomputable def Ns420p2503 := @Enclosure.norm_gt_of_isNear qz779 (hardyZErrorBoundRS qz4) Bool.false Bool.false Ns420p1475 Ns420p1476 Ns420p1477 

noncomputable def Ns420p2504 := @Ns420p2503 Ns420p1478 16306601 1073741824 201 1073741824 (Ns420p2498 (RS421to432.d64 qz181 qz217 qz303) RS421to432.d75) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 16306601 1073741824 201 1073741824 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS421to432.d76) rfl rfl rfl rfl 

noncomputable def Ns420p2505 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz780 qz4 qz217 775738 1000 788762 1000 

noncomputable def Ns420p2506 := @Enclosure.norm_gt_of_isNear qz780 (hardyZErrorBoundRS qz4) Bool.true Bool.false Ns420p1818 Ns420p1819 Ns420p1820 

noncomputable def Ns420p2507 := @Ns420p2506 Ns420p1821 16306601 1073741824 201 1073741824 (Ns420p2500 (RS421to432.d74 qz181 qz217 qz303) RS421to432.d77) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 16306601 1073741824 201 1073741824 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS421to432.d76) rfl rfl rfl rfl 

noncomputable def Ns420p2508 := @Zeta.Certificates.ZIntervalRS.Certificate.mk qz302 (@BSN.thirtyTwoPi_le_dec qz181 787461 1000 qz186 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz779 qz780 (Ns420p2499 rfl rfl) (Ns420p2501 rfl rfl)) (Ns420p2502 qz10 qz186 rfl rfl rfl rfl (Ns420p2504 rfl)) (Ns420p2505 qz10 qz222 rfl rfl rfl rfl (Ns420p2507 rfl)) 

noncomputable abbrev qz781 := (@Enclosure.dec_le_dec qz843 qz850 788762 1000 790386 1000 qz847 qz853 rfl rfl rfl)

noncomputable abbrev qz573 := qz781

noncomputable abbrev qz304 := (RS421to432.d3 qz516 qz547 qz573)

noncomputable abbrev qz782 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz304)

noncomputable def Ns420p2509 := @Enclosure.Real.IsNear.of_eq qz782 (hardyZApproximantRS₀ qz217) Bool.true 2617690418182512693017 295147905179352825856 14290477348143104875511 Ns420p2149 

noncomputable abbrev qz305 := qz573

noncomputable def Ns420p2510 := @Enclosure.Real.IsNear.neg_val qz782 2617690418182512693017 295147905179352825856 14290477348143104875511 Ns420p2149 (Ns420p2509 (RS421to432.d4 qz217 qz257 qz305) RS421to432.d78) rfl 

noncomputable abbrev qz783 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz304)

noncomputable def Ns420p2511 := @Enclosure.Real.IsNear.of_eq qz783 (hardyZApproximantRS₀ qz257) Bool.false 32216310515569136991 36893488147419103232 17967941049882609219383 Ns420p2155 

noncomputable def Ns420p2512 := @Enclosure.Real.IsNear.pos_val qz783 32216310515569136991 36893488147419103232 17967941049882609219383 Ns420p2155 (Ns420p2511 (RS421to432.d54 qz217 qz257 qz305) RS421to432.d79) rfl 

noncomputable def Ns420p2513 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz782 qz4 qz217 775738 1000 788762 1000 

noncomputable def Ns420p2514 := @Enclosure.norm_gt_of_isNear qz782 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2617690418182512693017 295147905179352825856 14290477348143104875511 

noncomputable def Ns420p2515 := @Ns420p2514 Ns420p2149 269968109 5368709120 1421 5368709120 (Ns420p2509 (RS421to432.d4 qz217 qz257 qz305) RS421to432.d78) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2516 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz783 qz4 qz257 775738 1000 790386 1000 

noncomputable def Ns420p2517 := @Enclosure.norm_gt_of_isNear qz783 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 32216310515569136991 36893488147419103232 17967941049882609219383 

noncomputable def Ns420p2518 := @Ns420p2517 Ns420p2155 269968109 5368709120 1421 5368709120 (Ns420p2511 (RS421to432.d54 qz217 qz257 qz305) RS421to432.d79) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2519 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz217 788762 1000 qz222 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz782 qz783 (Ns420p2510 rfl rfl) (Ns420p2512 rfl rfl)) (Ns420p2513 qz10 qz222 rfl rfl rfl rfl (Ns420p2515 rfl)) (Ns420p2516 qz10 qz260 rfl rfl rfl rfl (Ns420p2518 rfl)) 

noncomputable abbrev qz859 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 790386 1000) (Enclosure.sfrac Bool.false 791361 1000) 790386 1000 791361 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 790386 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 791361 1000)) rfl rfl rfl)

noncomputable abbrev qz784 := qz859

noncomputable abbrev qz574 := qz784

noncomputable abbrev qz306 := (RS421to432.d3 qz547 qz559 qz574)

noncomputable abbrev qz785 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz306)

noncomputable def Ns420p2520 := @Enclosure.Real.IsNear.of_eq qz785 (hardyZApproximantRS₀ qz257) Bool.false 32216310515569136991 36893488147419103232 17967941049882609219383 Ns420p2155 

noncomputable abbrev qz307 := qz574

noncomputable def Ns420p2521 := @Enclosure.Real.IsNear.pos_val qz785 32216310515569136991 36893488147419103232 17967941049882609219383 Ns420p2155 (Ns420p2520 (RS421to432.d4 qz257 qz271 qz307) RS421to432.d79) rfl 

noncomputable abbrev qz786 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz306)

noncomputable def Ns420p2522 := @Enclosure.Real.IsNear.of_eq qz786 (hardyZApproximantRS₀ qz271) Bool.true 30104066352671455159079 18889465931478580854784 462454108857420738703427 Ns420p2278 

noncomputable def Ns420p2523 := @Enclosure.Real.IsNear.neg_val qz786 30104066352671455159079 18889465931478580854784 462454108857420738703427 Ns420p2278 (Ns420p2522 (RS421to432.d54 qz257 qz271 qz307) RS421to432.d80) rfl 

noncomputable def Ns420p2524 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz785 qz4 qz257 775738 1000 790386 1000 

noncomputable def Ns420p2525 := @Enclosure.norm_gt_of_isNear qz785 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 32216310515569136991 36893488147419103232 17967941049882609219383 

noncomputable def Ns420p2526 := @Ns420p2525 Ns420p2155 269968109 5368709120 1421 5368709120 (Ns420p2520 (RS421to432.d4 qz257 qz271 qz307) RS421to432.d79) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2527 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz786 qz4 qz271 775738 1000 791361 1000 

noncomputable def Ns420p2528 := @Enclosure.norm_gt_of_isNear qz786 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 30104066352671455159079 18889465931478580854784 462454108857420738703427 

noncomputable def Ns420p2529 := @Ns420p2528 Ns420p2278 269968109 5368709120 1421 5368709120 (Ns420p2522 (RS421to432.d54 qz257 qz271 qz307) RS421to432.d80) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 269968109 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS421to432.d56) rfl rfl rfl rfl 

noncomputable def Ns420p2530 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz306 (@BSN.thirtyTwoPi_le_dec qz257 790386 1000 qz260 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz785 qz786 (Ns420p2521 rfl rfl) (Ns420p2523 rfl rfl)) (Ns420p2524 qz10 qz260 rfl rfl rfl rfl (Ns420p2526 rfl)) (Ns420p2527 qz10 (@Eq.refl Real qz271) rfl rfl rfl rfl (Ns420p2529 rfl)) 

noncomputable def Ns420p2531 := @List.cons RS421to432.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns420p2519)) (@List.cons RS421to432.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz306 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz306) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz306) Ns420p2530)) (@List.nil RS421to432.d0)) 

noncomputable def Ns420p2532 := @List.cons RS421to432.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inl (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns420p2497)) (@List.cons RS421to432.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz302 (@Or.inl (Zeta.Certificates.ZIntervalRS.Certificate qz302) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz302) Ns420p2508)) Ns420p2531) 

noncomputable def Ns420p2533 := @List.cons RS421to432.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns420p2475)) (@List.cons RS421to432.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz298 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz298) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz298) Ns420p2486)) Ns420p2532) 

noncomputable def Ns420p2534 := @List.cons RS421to432.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns420p2453)) (@List.cons RS421to432.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz294 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz294) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz294) Ns420p2464)) Ns420p2533) 

noncomputable def Ns420p2535 := @List.cons RS421to432.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns420p2431)) (@List.cons RS421to432.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz290 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz290) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz290) Ns420p2442)) Ns420p2534) 

noncomputable def Ns420p2536 := @List.cons RS421to432.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns420p2409)) (@List.cons RS421to432.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz286 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz286) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz286) Ns420p2420)) Ns420p2535) 

noncomputable abbrev qz787 := (RS421to432.d2 qz843 qz850 (@Enclosure.dec_le_dec qz843 qz850 788762 1000 790386 1000 qz847 qz853 rfl rfl rfl))

noncomputable abbrev qz788 := (@List.cons RS421to432.d1 (RS421to432.d2 qz850 qz855 qz859) (@List.nil RS421to432.d1))

noncomputable abbrev qz575 := (@List.cons RS421to432.d1 (RS421to432.d2 qz710 qz729 qz778) (@List.cons RS421to432.d1 qz787 qz788))

noncomputable abbrev qz308 := (@List.cons RS421to432.d1 (RS421to432.d2 qz430 qz442 qz570) (@List.cons RS421to432.d1 (RS421to432.d2 qz442 qz481 qz571) qz575))

noncomputable def Ns420p2537 := @List.cons RS421to432.d1 (RS421to432.d2 qz96 qz110 qz295) (@List.cons RS421to432.d1 (RS421to432.d2 qz110 qz124 qz297) qz308) 

noncomputable def Ns420p2538 := @List.IsChain.cons_cons RS421to432.d1 RS421to432.d81 (RS421to432.d2 qz82 qz96 qz293) (RS421to432.d2 qz96 qz110 qz295) (@List.cons RS421to432.d1 (RS421to432.d2 qz110 qz124 qz297) qz308) 

noncomputable def Ns420p2539 := @List.IsChain.cons_cons RS421to432.d1 RS421to432.d81 (RS421to432.d2 qz96 qz110 qz295) (RS421to432.d2 qz110 qz124 qz297) qz308 (@Enclosure.dec_le_dec qz110 qz110 783557 1000 783557 1000 qz113 qz113 rfl rfl rfl) 

noncomputable abbrev qz309 := qz575

noncomputable abbrev qz576 := (RS421to432.d2 qz710 qz729 qz778)

noncomputable abbrev qz310 := qz576

noncomputable abbrev qz577 := (@List.cons RS421to432.d1 qz787 qz788)

noncomputable abbrev qz311 := qz577

noncomputable abbrev qz578 := qz787

noncomputable abbrev qz312 := qz578

noncomputable abbrev qz579 := qz788

noncomputable abbrev qz313 := qz579

noncomputable abbrev qz789 := (RS421to432.d2 qz850 qz855 qz859)

noncomputable abbrev qz580 := qz789

noncomputable abbrev qz314 := qz580

noncomputable def Ns420p2540 := @List.IsChain.cons_cons RS421to432.d1 RS421to432.d81 (RS421to432.d2 qz124 qz138 qz299) (RS421to432.d2 qz138 qz181 qz301) qz309 (@Enclosure.dec_le_dec qz138 qz138 786160 1000 786160 1000 qz141 qz141 rfl rfl rfl) (@List.IsChain.cons_cons RS421to432.d1 RS421to432.d81 (RS421to432.d2 qz138 qz181 qz301) qz310 qz311 (@Enclosure.dec_le_dec qz181 qz181 787461 1000 787461 1000 qz186 qz186 rfl rfl rfl) (@List.IsChain.cons_cons RS421to432.d1 RS421to432.d81 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz217 qz217 788762 1000 788762 1000 qz222 qz222 rfl rfl rfl) (@List.IsChain.cons_cons RS421to432.d1 RS421to432.d81 qz312 qz314 (@List.nil RS421to432.d1) (@Enclosure.dec_le_dec qz257 qz257 790386 1000 790386 1000 qz260 qz260 rfl rfl rfl) (@List.IsChain.singleton RS421to432.d1 RS421to432.d81 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS421to432.d1 (RS421to432.d2 qz442 qz481 qz571) qz575)

noncomputable def Ns420p2541 := @List.IsChain.cons_cons RS421to432.d1 RS421to432.d81 (RS421to432.d2 qz110 qz124 qz297) (RS421to432.d2 qz124 qz138 qz299) qz315 (@Enclosure.dec_le_dec qz124 qz124 784859 1000 784859 1000 qz127 qz127 rfl rfl rfl) Ns420p2540 

noncomputable abbrev qz790 := (@List.cons RS421to432.d1 (RS421to432.d2 qz82 qz96 qz293) Ns420p2537)

noncomputable def Ns420p2542 := @List.IsChain.cons_cons RS421to432.d1 RS421to432.d81 (RS421to432.d2 qz4 qz30 qz285) (RS421to432.d2 qz30 qz54 qz287) (@List.cons RS421to432.d1 (RS421to432.d2 qz54 qz68 qz289) (@List.cons RS421to432.d1 (RS421to432.d2 qz68 qz82 qz291) qz790)) (@Enclosure.dec_le_dec qz30 qz30 777042 1000 777042 1000 qz33 qz33 rfl rfl rfl) (@List.IsChain.cons_cons RS421to432.d1 RS421to432.d81 (RS421to432.d2 qz30 qz54 qz287) (RS421to432.d2 qz54 qz68 qz289) (@List.cons RS421to432.d1 (RS421to432.d2 qz68 qz82 qz291) qz790) (@Enclosure.dec_le_dec qz54 qz54 778346 1000 778346 1000 qz57 qz57 rfl rfl rfl) (@List.IsChain.cons_cons RS421to432.d1 RS421to432.d81 (RS421to432.d2 qz54 qz68 qz289) (RS421to432.d2 qz68 qz82 qz291) qz790 (@Enclosure.dec_le_dec qz68 qz68 779649 1000 779649 1000 qz71 qz71 rfl rfl rfl) (@List.IsChain.cons_cons RS421to432.d1 RS421to432.d81 (RS421to432.d2 qz68 qz82 qz291) (RS421to432.d2 qz82 qz96 qz293) Ns420p2537 (@Enclosure.dec_le_dec qz82 qz82 780953 1000 780953 1000 qz85 qz85 rfl rfl rfl) (Ns420p2538 (@Enclosure.dec_le_dec qz96 qz96 782255 1000 782255 1000 qz99 qz99 rfl rfl rfl) (Ns420p2539 Ns420p2541))))) 

noncomputable abbrev qz581 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz582 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns420p2536 Ns420p2542)

noncomputable abbrev qz583 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns420p2536 Ns420p2542))

theorem RS421to432.d82 : Zeta.Certificates.BatchSpec 12 775738 1000 791361 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz581 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz581 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz581 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz581 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz581 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz271)))) qz582 (@And.intro (@Eq Nat (@List.length qz581 qz583) 12) (And (@Eq (Option Real) (@Option.map qz581 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz581 qz583)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz581 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz581 qz583)) (@Option.some Real qz271))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz581 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz581 qz583)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz581 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz581 qz583)) (@Option.some Real qz271)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz271))))

theorem solution : Zeta.Certificates.BatchSpec 12 775738 1000 791361 1000 := RS421to432.d82
#print axioms solution
#check solution
