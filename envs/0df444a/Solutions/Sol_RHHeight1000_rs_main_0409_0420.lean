-- Prove2me | solution 1 for RHHeight1000.rs_main_0409_0420
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:38:40.076173+00:00
-- url     : https://prove2.me/submissions/15777b40-abb5-4c58-84c5-baad5c97c9a2

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

noncomputable def RS409to420.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS409to420.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS409to420.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS409to420.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS409to420.d2 a b h 

theorem RS409to420.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS409to420.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS409to420.d3 a b h)) 

noncomputable def Ns408p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns408p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns408p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns408p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns408p0 Ns408p1 Ns408p2 Ns408p1 307286088 268435456 1 100000000 307286088 268435456 1 100000000 153643044 134217728 2 134217728 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns408p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns408p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns408p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns408p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns408p8 := nat_lit 6573389678388862351155759458724141871788046104702795740939545775355827438482086890337971184306503456724674701876007739166027855002689342487126242201873902293161938510715598861337724155978462934346539722102807352693564004597780440630880721700532830491857281958381906437104026277614553345439647264822859384496062743250358046048880947907642984145065307980413206151384068885350206914057384338280179177725692904928360597982006748935836093248417685721122261418062303135764477585928239149568275027355236134745000697766005167655784166499502223346815249842007858448160935771607172549259242715110048115445292136446613946552506617916138661398090061483392335970316672263498462800198746102072055363920390651513279180731193678641632192805423820381724597815072905552156968003637925334143020171520625 

noncomputable def Ns408p9 := nat_lit 702614123509571190207434367497643053726389003684617183996726348470791223755418688598787599501240412886827946200799073391711533512528899996899108221816773619593298708861540359234024488137706935294538610329535191474811214152768697527793266408685885408431698677504366547635987768499962038530066773279961750661013789994039311989768445302208965109624014234440840481147386361324656837522786906307734587964680180646868573806366973424595907336814393861048013934514934272026683624090151873353554279683010347128413433843775162422864773798490322287367830744467164676975854073090397461536167654230134598982106570951920409048997311342333559851528447946435833392322432321465286801524775001800171249769824525762984779161997185015423416919065587459911326773695449510414365759468097615398764501522575 

noncomputable def Ns408p10 := nat_lit 541392566138474909591412279139378993255101875047003589935782329109463644892392322173295519240510467068363239080443023466297029982601757003829684821059136286585994161974307047499333049696728682047261006046816072264069316416942594393775486731411634963656291648112663555457379375292741727868294229136381639619442405391741167595634732196900940186574903289828257139713673376723681752760045249773972946001592268830432998579610986951410273979009689762628244990479410235165324966379611071762421902787196495466840333515349387051622842182127210560393625584510287605139387730811840242457253978115925211125629993337408355023684205061830608267784338105681114876710224147942516826039256450164994945245879666660679160980454641866547806615379410050641833332584350523565507268843323231339375 

noncomputable def Ns408p11 := BSN.log_dyadic_bound Ns408p6 Ns408p7 16 15 Ns408p8 268435456 100000000 Ns408p9 Ns408p10 307286088 Ns408p4 Ns408p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns408p6) (BSN.artanhQ Ns408p7) 0 15 Ns408p9 Ns408p8 Ns408p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns408p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns408p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns408p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns408p15 := nat_lit 6573389678388957581038003304946500209472262679236338533996718496177406624059139082449994147026037314666926693076053053862592074936423388863596813530408382584499373597031431853921413941298322255656576695489433951602693567143885654771592106690789036275646003378131729522606930818530515414843848039000889531334935427389830473690579523667466182538201372727149023132371319359578146651783732835416323469915494090659780509855937937675396353734377829186029766969614606089327824892671842834136516654569045504808111725705550748907924941183733134599012581542910476929082687043869700761244349471219210833189555347464155979117619898077496880661665775336657207488512148128426326823595335945176245554694022845325705851563290369414226074229552025260849280553835909109839168582914725334143020171520625 

noncomputable def Ns408p16 := nat_lit 702614123509582134195699383225799303120857312948289364169564431944606347230839067212220070086773571232938822231607515388838247088164426860334641427891924556959013106220289292017417932077264689683982462259236603120411894481357554273197237433243865910367073588753830073256225145709268648257922640132615276470163987114280905050307903018021985933333474523803420109333064989110261463867307642914581311357336787925252212965840242792007601256472655504246146516404729632839909377990937267835233434162343951883521915890115762575574377037535717851480622294463860980162526686236248764915916362237196611189536095144270945605478817014333998082847306947436470576941659846222535334992451365706225994338058508887942119777908276510373758951874822816373072605980596581754554466975502415398764501522575 

noncomputable def Ns408p17 := nat_lit 541392566138490077533790984620311058177654278555980714203107761719673916425133183846751239616284470803704371181920004286935467360846628369375164068764590875438310007353955324186636582299553928814156491749519256774653872128089233575343481607925575468185460509172779152955629338248076232826253005811067688706928164570779608774451502836676056177667078421728722179008027603013170304530594440809888606240685402729798990208830923560422594844623819537735750113690675240496626214395332044296593456069970973486809806367897564108502902289348063943342100923856630472249952347312756547637419241376870243223562839253667975765230153074010838184467350558565952691487980795548332122966513692688198426849374346091985539852378055886379210372820263137502377721028428076000707268843323231339375 

noncomputable def Ns408p18 := BSN.log_dyadic_bound Ns408p13 Ns408p14 16 15 Ns408p15 268435456 100000000 Ns408p16 Ns408p17 307286088 Ns408p12 Ns408p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns408p13) (BSN.artanhQ Ns408p14) 0 15 Ns408p16 Ns408p15 Ns408p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns408p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 153643044 134217728 2 134217728 38410761 33554432 1 67108864 (Ns408p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns408p0 Ns408p1 307286088 268435456 1 100000000 Bool.false (BSN.logfrac_isNear Ns408p4 Ns408p5 1 Ns408p0 Ns408p1 307286088 268435456 100000000 rfl rfl rfl (Ns408p11 rfl))) (BSN.isNear_log_sfrac Ns408p2 Ns408p1 307286088 268435456 1 100000000 Bool.false (BSN.logfrac_isNear Ns408p12 Ns408p5 1 Ns408p2 Ns408p1 307286088 268435456 100000000 rfl rfl rfl (Ns408p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS409to420.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 67108864 := Ns408p19 

noncomputable def Ns408p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 16777216 6250000 385100712855 135135 11629079 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz317 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz317

theorem RS409to420.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 11629079 16777216 1 6250000 := BSN.isNear_log_sfrac 2 1 11629079 16777216 1 6250000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 11629079 16777216 6250000 rfl rfl rfl (Ns408p20 rfl)) 

theorem RS409to420.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 186065264 268435456 43 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 11629079 16777216 1 6250000 186065264 268435456 43 268435456 RS409to420.d6 rfl 

noncomputable abbrev qz318 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz577 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz320 := qz577

noncomputable def Ns408p21 := @Enclosure.Real.IsNear.inv_image qz318 47453133 33554432 1 33554432 11863282 11863284 16777216 (@Enclosure.Real.IsNear.of_eq qz318 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz320)) Bool.false 47453133 33554432 1 33554432 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz320)) Bool.false 47453133 33554432 1 33554432 47453133 33554432 1 33554432 (BSN.sqrt_enclosure 2 1 23726566 23726567 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz321 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS409to420.d8 : Enclosure.Real.IsNear qz321 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz321 Bool.false 23726566 33554432 2 33554432 11863283 16777216 1 16777216 (Ns408p21 rfl rfl) rfl 

theorem RS409to420.d9 : Enclosure.Real.IsNear qz321 Bool.false 189812528 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz321 Bool.false 11863283 16777216 1 16777216 189812528 268435456 16 268435456 RS409to420.d8 rfl 

noncomputable def Ns408p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 16777216 6250000 13079757671720842725 316234143225 18431655 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS409to420.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 6250000 := BSN.isNear_log_sfrac 3 1 18431655 16777216 1 6250000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 18431655 16777216 6250000 rfl rfl rfl (Ns408p22 rfl)) 

theorem RS409to420.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 294906480 268435456 43 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 6250000 294906480 268435456 43 268435456 RS409to420.d10 rfl 

noncomputable abbrev qz322 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz323 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns408p23 := @Enclosure.Real.IsNear.inv_image qz322 58117981 33554432 1 33554432 9686330 9686331 16777216 (@Enclosure.Real.IsNear.of_eq qz322 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz323 qz320)) Bool.false 58117981 33554432 1 33554432 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz323 qz320)) Bool.false 58117981 33554432 1 33554432 58117981 33554432 1 33554432 (BSN.sqrt_enclosure 3 1 29058990 29058991 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz324 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS409to420.d12 : Enclosure.Real.IsNear qz324 Bool.false 19372661 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz324 Bool.false 19372661 33554432 1 33554432 19372661 33554432 1 33554432 (Ns408p23 rfl rfl) rfl 

theorem RS409to420.d13 : Enclosure.Real.IsNear qz324 Bool.false 154981288 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz324 Bool.false 19372661 33554432 1 33554432 154981288 268435456 8 268435456 RS409to420.d12 rfl 

noncomputable def Ns408p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns408p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns408p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns408p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns408p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns408p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns408p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns408p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns408p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns408p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns408p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns408p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns408p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns408p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns408p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns408p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns408p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns408p25 Ns408p26 Ns408p27 Ns408p28 200200021673987500790625 Ns408p29 Ns408p30 Ns408p31 Ns408p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns408p32 Ns408p33 151412625 Ns408p34 Ns408p35 1322214852783825 Ns408p27 Ns408p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns408p32 Ns408p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns408p34 Ns408p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns408p36 Ns408p37 1267389585 Ns408p38 Ns408p39 1927077560082675 Ns408p29 Ns408p30 Ns408p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns408p36 Ns408p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns408p38 Ns408p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz325 := (@Nat.cast Real Real.instNatCast 5)

theorem RS409to420.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz320 qz325)) Bool.false Ns408p24 Ns408p25 1 Ns408p26 := Ns408p40 rfl rfl rfl 

noncomputable def Ns408p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns408p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns408p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns408p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns408p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns408p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns408p25 Ns408p26 Ns408p42 Ns408p43 9945 Ns408p44 Ns408p45 65835 Ns408p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns408p42 Ns408p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns408p44 Ns408p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS409to420.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz320 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns408p41 Ns408p25 1 Ns408p26 := Ns408p46 rfl 

noncomputable def Ns408p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns408p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS409to420.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns408p47 Ns408p25 1 Ns408p48 := BSN.pi_combine Ns408p24 Ns408p41 Ns408p25 Ns408p26 Ns408p48 Ns408p47 rfl rfl rfl rfl RS409to420.d14 RS409to420.d15 

theorem RS409to420.d17 : Enclosure.Real.IsNear Real.pi Bool.false 14148475504056880 4503599627370496 1 4503599627370496 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns408p47 Ns408p25 1 Ns408p48 14148475504056880 4503599627370496 1 4503599627370496 RS409to420.d16 rfl 

noncomputable def Ns408p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns408p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns408p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns408p52 := BSN.log_dyadic_bound 3 5 17 16 Ns408p49 16777216 6250000 Ns408p50 Ns408p51 23258159 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns408p50 Ns408p49 Ns408p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS409to420.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 6250000 := BSN.isNear_log_sfrac 4 1 23258159 16777216 1 6250000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 23258159 16777216 6250000 rfl rfl rfl (Ns408p52 rfl)) 

theorem RS409to420.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 372130544 268435456 43 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 6250000 372130544 268435456 43 268435456 RS409to420.d18 rfl 

noncomputable abbrev qz326 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz327 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns408p53 := @Enclosure.Real.IsNear.inv_image qz326 67108865 33554432 1 33554432 8388607 8388608 16777216 (@Enclosure.Real.IsNear.of_eq qz326 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz327 qz320)) Bool.false 67108865 33554432 1 33554432 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz327 qz320)) Bool.false 67108865 33554432 1 33554432 67108865 33554432 1 33554432 (BSN.sqrt_enclosure 4 1 33554432 33554433 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz328 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS409to420.d20 : Enclosure.Real.IsNear qz328 Bool.false 16777215 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz328 Bool.false 16777215 33554432 1 33554432 16777215 33554432 1 33554432 (Ns408p53 rfl rfl) rfl 

theorem RS409to420.d21 : Enclosure.Real.IsNear qz328 Bool.false 134217720 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz328 Bool.false 16777215 33554432 1 33554432 134217720 268435456 8 268435456 RS409to420.d20 rfl 

noncomputable def Ns408p54 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns408p55 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns408p56 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns408p57 := nat_lit 885951608314392539099884620 

noncomputable def Ns408p58 := nat_lit 1286943652057122751813246125 

noncomputable def Ns408p59 := BSN.log_dyadic_bound 2 3 22 21 Ns408p54 16777216 6250000 Ns408p55 Ns408p56 27001887 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns408p57 Ns408p58 84004523356416638976000 Ns408p55 Ns408p54 Ns408p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns408p57 Ns408p58 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS409to420.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 6250000 := BSN.isNear_log_sfrac 5 1 27001887 16777216 1 6250000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 27001887 16777216 6250000 rfl rfl rfl (Ns408p59 rfl rfl)) 

theorem RS409to420.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 432030192 268435456 43 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 6250000 432030192 268435456 43 268435456 RS409to420.d22 rfl 

noncomputable abbrev qz329 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns408p60 := @Enclosure.Real.IsNear.inv_image qz329 75029991 33554432 1 33554432 7502998 7503000 16777216 (@Enclosure.Real.IsNear.of_eq qz329 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz325 qz320)) Bool.false 75029991 33554432 1 33554432 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz325 qz320)) Bool.false 75029991 33554432 1 33554432 75029991 33554432 1 33554432 (BSN.sqrt_enclosure 5 1 37514995 37514996 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz330 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS409to420.d24 : Enclosure.Real.IsNear qz330 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz330 Bool.false 15005998 33554432 2 33554432 7502999 16777216 1 16777216 (Ns408p60 rfl rfl) rfl 

theorem RS409to420.d25 : Enclosure.Real.IsNear qz330 Bool.false 120047984 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz330 Bool.false 7502999 16777216 1 16777216 120047984 268435456 16 268435456 RS409to420.d24 rfl 

noncomputable def Ns408p61 := BSN.log_dyadic_bound 2 10 6 5 103950000000000 16777216 6250000 1420244935680 967680 6802575 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 2) (BSN.artanhQ 10) 0 5 1420244935680 103950000000000 967680 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz577)

theorem RS409to420.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 80000001 500000000000000 := BSN.isNear_log_sfrac 6 1 4034683545132279 2251799813685248 80000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 1083052117253279893684224 604462909807314587353088 1000000012500000 6250000000000000000000 4034683545132279 2251799813685248 80000001 500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 6802575 16777216 24973259072661432 36028797018963968 6250000 1000000000000000 rfl rfl rfl rfl (Ns408p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS409to420.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 480971758 268435456 44 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 80000001 500000000000000 480971758 268435456 44 268435456 RS409to420.d26 rfl 

noncomputable abbrev qz332 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns408p62 := @Enclosure.Real.IsNear.inv_image qz332 82191237 33554432 1 33554432 6849269 6849270 16777216 (@Enclosure.Real.IsNear.of_eq qz332 (Real.sqrt qz331) Bool.false 82191237 33554432 1 33554432 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz331) Bool.false 82191237 33554432 1 33554432 82191237 33554432 1 33554432 (BSN.sqrt_enclosure 6 1 41095618 41095619 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz333 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS409to420.d28 : Enclosure.Real.IsNear qz333 Bool.false 13698539 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz333 Bool.false 13698539 33554432 1 33554432 13698539 33554432 1 33554432 (Ns408p62 rfl rfl) rfl 

theorem RS409to420.d29 : Enclosure.Real.IsNear qz333 Bool.false 109588312 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz333 Bool.false 13698539 33554432 1 33554432 109588312 268435456 8 268435456 RS409to420.d28 rfl 

noncomputable def Ns408p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 16777216 6250000 11010900719820672 5524329195 9388794 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz577)

theorem RS409to420.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 80000001 500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 80000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 1176230476650867868041216 604462909807314587353088 1000000012500000 6250000000000000000000 4381799983422711 2251799813685248 80000001 500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 9388794 16777216 24973259072661432 36028797018963968 6250000 1000000000000000 rfl rfl rfl rfl (Ns408p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS409to420.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 522351262 268435456 44 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 80000001 500000000000000 522351262 268435456 44 268435456 RS409to420.d30 rfl 

noncomputable abbrev qz335 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns408p64 := @Enclosure.Real.IsNear.inv_image qz335 88776683 33554432 1 33554432 6341191 6341192 16777216 (@Enclosure.Real.IsNear.of_eq qz335 (Real.sqrt qz334) Bool.false 88776683 33554432 1 33554432 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz334) Bool.false 88776683 33554432 1 33554432 88776683 33554432 1 33554432 (BSN.sqrt_enclosure 7 1 44388341 44388342 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz336 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS409to420.d32 : Enclosure.Real.IsNear qz336 Bool.false 12682383 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz336 Bool.false 12682383 33554432 1 33554432 12682383 33554432 1 33554432 (Ns408p64 rfl rfl) rfl 

theorem RS409to420.d33 : Enclosure.Real.IsNear qz336 Bool.false 101459064 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz336 Bool.false 12682383 33554432 1 33554432 101459064 268435456 8 268435456 RS409to420.d32 rfl 

noncomputable def Ns408p65 := nat_lit 1256945285058001618599936 

noncomputable def Ns408p66 := BSN.log_dyadic_bound 0 16 1 0 1 16777216 6250000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz577)

theorem RS409to420.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 160000003 1000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 160000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false Ns408p65 604462909807314587353088 1000000018750000 6250000000000000000000 9364972152248037 4503599627370496 160000003 1000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 16777216 24973259072661432 36028797018963968 6250000 1000000000000000 rfl rfl rfl rfl (Ns408p66 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS409to420.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 558195838 268435456 44 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 160000003 1000000000000000 558195838 268435456 44 268435456 RS409to420.d34 rfl 

noncomputable abbrev qz338 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns408p67 := @Enclosure.Real.IsNear.inv_image qz338 94906265 33554432 1 33554432 5931641 5931642 16777216 (@Enclosure.Real.IsNear.of_eq qz338 (Real.sqrt qz337) Bool.false 94906265 33554432 1 33554432 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz337) Bool.false 94906265 33554432 1 33554432 94906265 33554432 1 33554432 (BSN.sqrt_enclosure 8 1 47453132 47453133 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz339 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS409to420.d36 : Enclosure.Real.IsNear qz339 Bool.false 11863283 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz339 Bool.false 11863283 33554432 1 33554432 11863283 33554432 1 33554432 (Ns408p67 rfl rfl) rfl 

theorem RS409to420.d37 : Enclosure.Real.IsNear qz339 Bool.false 94906264 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz339 Bool.false 11863283 33554432 1 33554432 94906264 268435456 8 268435456 RS409to420.d36 rfl 

noncomputable def Ns408p68 := nat_lit 1328140746012062765809664 

noncomputable def Ns408p69 := BSN.log_dyadic_bound 1 17 3 2 1252815 16777216 6250000 1448 3 1976071 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz577)

theorem RS409to420.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 160000003 1000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 160000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false Ns408p68 604462909807314587353088 1000000018750000 6250000000000000000000 9895419672221413 4503599627370496 160000003 1000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 1976071 16777216 24973259072661432 36028797018963968 6250000 1000000000000000 rfl rfl rfl rfl (Ns408p69 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS409to420.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 589812974 268435456 44 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 160000003 1000000000000000 589812974 268435456 44 268435456 RS409to420.d38 rfl 

noncomputable abbrev qz341 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns408p70 := @Enclosure.Real.IsNear.inv_image qz341 100663297 33554432 1 33554432 5592405 5592406 16777216 (@Enclosure.Real.IsNear.of_eq qz341 (Real.sqrt qz340) Bool.false 100663297 33554432 1 33554432 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz340) Bool.false 100663297 33554432 1 33554432 100663297 33554432 1 33554432 (BSN.sqrt_enclosure 9 1 50331648 50331649 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz342 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS409to420.d40 : Enclosure.Real.IsNear qz342 Bool.false 11184811 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz342 Bool.false 11184811 33554432 1 33554432 11184811 33554432 1 33554432 (Ns408p70 rfl rfl) rfl 

theorem RS409to420.d41 : Enclosure.Real.IsNear qz342 Bool.false 89478488 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz342 Bool.false 11184811 33554432 1 33554432 89478488 268435456 8 268435456 RS409to420.d40 rfl 

noncomputable def Ns408p71 := nat_lit 1391827265235416537628672 

noncomputable def Ns408p72 := BSN.log_dyadic_bound 2 18 4 3 3571283520 16777216 6250000 14806464 960 3743727 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz578 := (Enclosure.sfrac Bool.false 10 1)

noncomputable abbrev qz343 := qz578

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz577)

theorem RS409to420.d42 : Enclosure.Real.IsNear (Real.log qz343) Bool.false 10369921216632549 4503599627370496 160000003 1000000000000000 := BSN.isNear_log_sfrac 10 1 10369921216632549 4503599627370496 160000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz344) Bool.false Ns408p71 604462909807314587353088 1000000018750000 6250000000000000000000 10369921216632549 4503599627370496 160000003 1000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 3743727 16777216 24973259072661432 36028797018963968 6250000 1000000000000000 rfl rfl rfl rfl (Ns408p72 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS409to420.d43 : Enclosure.Real.IsNear (Real.log qz343) Bool.false 618095470 268435456 44 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false 10369921216632549 4503599627370496 160000003 1000000000000000 618095470 268435456 44 268435456 RS409to420.d42 rfl 

noncomputable abbrev qz345 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns408p73 := @Enclosure.Real.IsNear.inv_image qz345 106108431 33554432 1 33554432 5305421 5305422 16777216 (@Enclosure.Real.IsNear.of_eq qz345 (Real.sqrt qz344) Bool.false 106108431 33554432 1 33554432 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz344) Bool.false 106108431 33554432 1 33554432 106108431 33554432 1 33554432 (BSN.sqrt_enclosure 10 1 53054215 53054216 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz346 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS409to420.d44 : Enclosure.Real.IsNear qz346 Bool.false 10610843 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz346 Bool.false 10610843 33554432 1 33554432 10610843 33554432 1 33554432 (Ns408p73 rfl rfl) rfl 

theorem RS409to420.d45 : Enclosure.Real.IsNear qz346 Bool.false 84886744 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz346 Bool.false 10610843 33554432 1 33554432 84886744 268435456 8 268435456 RS409to420.d44 rfl 

theorem RS409to420.d46 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz714 := (@instHMul Real Real.instMul)

noncomputable abbrev qz579 := qz714

noncomputable abbrev qz347 := (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz1 := qz347

theorem RS409to420.d47 : Enclosure.Real.IsNear qz1 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS409to420.d46 rfl 

noncomputable abbrev qz348 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 2 1) Real.pi))

noncomputable abbrev qz2 := qz348

theorem RS409to420.d48 : Enclosure.Real.IsNear qz2 Bool.false 5340353 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz2 Bool.false 5340353 33554432 1 33554432 5340353 33554432 1 33554432 (@Enclosure.Real.IsNear.inv_image qz1 884279719003555 140737488355328 1 500000000000000 2670176 2670177 16777216 RS409to420.d47 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns408p74 := nat_lit 2018021763766754379499027 

noncomputable def Ns408p75 := nat_lit 1844674407370955161600000000 

noncomputable def Ns408p76 := nat_lit 973273271930425544674008629248 

noncomputable abbrev qz715 := (Enclosure.sfrac Bool.false 760048 1000)

noncomputable abbrev qz580 := qz715

noncomputable abbrev qz349 := qz580

noncomputable abbrev qz3 := qz349

noncomputable abbrev qz350 := qz579

noncomputable abbrev qz4 := qz350

noncomputable abbrev qz5 := (@Neg.neg Real Real.instNeg (1 : Real))

noncomputable abbrev qz351 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz716 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 760048 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz581 := qz716

noncomputable abbrev qz352 := qz581

noncomputable abbrev qz353 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz6 := (@HPow.hPow Real Real Real qz351 qz352 qz353)

noncomputable abbrev qz717 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 760048 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz582 := qz717

noncomputable abbrev qz354 := qz582

noncomputable abbrev qz7 := qz354

noncomputable abbrev qz583 := (@HMul.hMul Real Real Real qz4 (@HPow.hPow Real Nat Real RSCompact.c1 qz5 10) qz6)

noncomputable def Ns408p77 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz3) qz3 10) (@HMul.hMul Real Real Real qz4 qz583 (Zeta.RiemannSiegel.correction qz7)) 168861147 134217728 145739 134217728 1310177527954439836787 4722366482869645213696 15000199761173579499027 Ns408p75 Ns408p76 

noncomputable def Ns408p78 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz3) qz3 Real.cos BSN.quadSignPos 9 10 760048 1000 196 268435456 134217728 4503599627370496 Bool.false 387081280624 2552 618095470 44 84886744 8 

noncomputable def Ns408p79 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz3) qz3 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 760048 1000 88 145 268435456 134217728 4503599627370496 Bool.false 387081280624 2552 

noncomputable def Ns408p80 := Ns408p79 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 322420580 109603 Bool.true 68495968 Bool.true 64563540 14148475504056880 1 Bool.false 259743801 Bool.false Bool.false 63942850 Bool.true Bool.true 251901565 

noncomputable def Ns408p81 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz3) qz3 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 760048 1000 51 23 268435456 134217728 4503599627370496 Bool.false 387081280624 2552 

noncomputable def Ns408p82 := Ns408p81 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 405919994 81284 Bool.false 15129058 Bool.true 232630506 14148475504056880 1 Bool.false 15121049 Bool.false Bool.false 204586090 Bool.false Bool.true 322420580 

noncomputable def Ns408p83 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz3) qz3 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 760048 1000 247 139 268435456 134217728 4503599627370496 Bool.false 387081280624 2552 

noncomputable def Ns408p84 := Ns408p83 372130544 43 134217720 8 432030192 43 120047984 16 Bool.true 499033469 47881 Bool.false 94820136 Bool.false 107214725 14148475504056880 1 Bool.false 92860565 Bool.false Bool.false 104386801 Bool.false Bool.true 405919994 

noncomputable def Ns408p85 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz3) qz3 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 760048 1000 582 386 268435456 134217728 4503599627370496 Bool.false 387081280624 2552 

noncomputable def Ns408p86 := Ns408p85 186065264 43 189812528 16 294906480 43 154981288 8 Bool.true 268435344 2595 Bool.false 258125600 Bool.false 178433002 14148475504056880 1 Bool.false 153602648 Bool.true Bool.false 211283609 Bool.true Bool.true 499033469 

noncomputable def Ns408p87 := nat_lit 687687804135936995264024597230249648057269251598417469 

noncomputable def Ns408p88 := nat_lit 476901877018821755377393261502489772984467718144000 

noncomputable def Ns408p89 := nat_lit 121743789603758936708933057904640000 

noncomputable def Ns408p90 := nat_lit 555186854930154228789491184873610936320 

noncomputable abbrev qz355 := (@Eq.refl Real qz580)

noncomputable abbrev qz8 := qz355

noncomputable def Ns408p91 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz3 760048 1000 2310692849216 16000000 1520096 4000 2000 Ns408p89 Ns408p90 qz8 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns408p92 := nat_lit 901366158637055338432462320081632818701623953455077744967680 

noncomputable abbrev qz718 := (@instHSub Real Real.instSub)

noncomputable abbrev qz584 := qz718

noncomputable abbrev qz356 := qz584

noncomputable abbrev qz585 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz719 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz720 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz586 := (@HSub.hSub Real Real Real qz718 qz719 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz720 (@Nat.cast Real Real.instNatCast 1520096))))

noncomputable abbrev qz357 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 760048 4000) (Real.log (Enclosure.sfrac Bool.false 2310692849216 16000000))) (@HMul.hMul Real Real Real qz579 qz585 qz586))

noncomputable abbrev qz587 := (Enclosure.sfrac Bool.false 760048 2000)

noncomputable abbrev qz9 := (@HSub.hSub Real Real Real qz356 (@HSub.hSub Real Real Real qz356 qz357 qz587) (@HMul.hMul Real Real Real qz350 qz587 (Real.log Real.pi)))

noncomputable def Ns408p93 := @Enclosure.Real.IsNear.addLit_ft_p qz9 (Enclosure.sfrac Bool.true Ns408p89 Ns408p90) 1623536810542414395949 1125899906842624000 2432778780636099 256000000000000000000 Ns408p89 Ns408p90 0 1 Ns408p92 

noncomputable def Ns408p94 := nat_lit 6809606938605290870586474496000 

noncomputable abbrev qz10 := (@HSub.hSub Real Real Real qz356 qz357 qz587)

noncomputable def Ns408p95 := @Enclosure.Real.IsNear.subLit_ff_p qz10 (@HMul.hMul Real Real Real qz4 qz587 (Real.log Real.pi)) 2113331224829093181997 1125899906842624000 3840243230329 1000000000000000000 1824626379783 4194304000 47503 8388608000 Ns408p94 1623536810542414395949 1125899906842624000 

noncomputable def Ns408p96 := nat_lit 4226662449658186363994000 

noncomputable abbrev qz11 := qz357

noncomputable def Ns408p97 := @Enclosure.Real.IsNear.subLit_ff_p qz11 qz587 2541200211027054524973 1125899906842624000 3840243230329 1000000000000000000 760048 2000 0 1 Ns408p96 2113331224829093181997 1125899906842624000 3840243230329 1000000000000000000 

noncomputable def Ns408p98 := nat_lit 5722274161727634279480872289177698304 

noncomputable def Ns408p99 := nat_lit 57450424078261941996355584 

noncomputable def Ns408p100 := nat_lit 4835703278458516698824704 

noncomputable def Ns408p101 := nat_lit 5662346695836033093159807186155058468358986965975040 

noncomputable def Ns408p102 := nat_lit 4436042234383103320804735552535605668884867186688 

noncomputable def Ns408p103 := nat_lit 6237996356352813541009052972801764938385195008 

noncomputable def Ns408p104 := BSN.log_dyadic_bound 213540849216 4407844849216 3 2 Ns408p101 134217728 50000000 Ns408p102 Ns408p103 13014714 4621385698432 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 213540849216) (BSN.artanhQ 4407844849216) 0 2 Ns408p102 Ns408p101 Ns408p103 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz358 := (Real.log (Enclosure.sfrac Bool.false 2310692849216 16000000))

noncomputable abbrev qz359 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns408p105 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 760048 4000) qz358 760048 4000 0 1 53504876865317991 4503599627370496 20000017 1000000000000000 2541642165733200526473 1125899906842624000 950060807551 250000000000000000 (Enclosure.Real.IsNear.const Bool.false 760048 4000) (BSN.isNear_log_sfrac 2310692849216 16000000 53504876865317991 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2310692849216) qz359)) Bool.false Ns408p99 Ns408p100 1000000850000000 50000000000000000000000 53504876865317991 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2310692849216 16000000 17 4621385698432 4194304000000 13014714 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns408p104 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns408p106 := BSN.arctan_dyadic_bound_f 1000 1520096 1 0 16777216 6250000 0 1 1 0 1 1 11036 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1520096) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1520096) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz588 := qz719

noncomputable abbrev qz360 := qz588

noncomputable abbrev qz12 := qz360

noncomputable abbrev qz589 := qz720

noncomputable abbrev qz361 := qz589

noncomputable abbrev qz13 := qz361

noncomputable abbrev qz721 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz590 := qz721

noncomputable abbrev qz362 := qz590

noncomputable abbrev qz14 := (@Enclosure.Real.IsNear.mulLit_ff qz362 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz363 := (@Nat.cast Real Real.instNatCast 1520096)

noncomputable def Ns408p107 := @Enclosure.Real.IsNear.subLit_ff_p qz12 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz13 qz363)) 884279719003555 562949953421312 1 2000000000000000 11036 16777216 1 6250000 14829539134455989403648 883909412292003 562949953421312 320000001 2000000000000000 qz14 (Ns408p106 rfl) rfl rfl 

noncomputable abbrev qz364 := (@HMul.hMul Real Real Real qz579 qz585 qz586)

noncomputable abbrev qz15 := qz364

noncomputable abbrev qz365 := qz585

noncomputable abbrev qz16 := qz365

noncomputable abbrev qz366 := qz586

noncomputable abbrev qz17 := qz366

noncomputable abbrev qz367 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns408p108 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 760048 4000) qz358) qz15 2541642165733200526473 1125899906842624000 950060807551 250000000000000000 883909412292003 2251799813685248 320000001 8000000000000000 Ns408p98 2541200211027054524973 1125899906842624000 3840243230329 1000000000000000000 (Ns408p105 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz16 qz17 1 4 0 1 883909412292003 562949953421312 320000001 2000000000000000 883909412292003 2251799813685248 320000001 8000000000000000 qz367 Ns408p107 rfl) 

noncomputable def Ns408p109 := @Ns408p93 Ns408p87 Ns408p88 2432778780636099 256000000000000000000 (@Ns408p95 2432778780636099 256000000000000000000 (Ns408p97 (Ns408p108 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 760048 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz587 (Real.log Real.pi) 760048 2000 0 1 38410761 33554432 1 67108864 1824626379783 4194304000 47503 8388608000 (Enclosure.Real.IsNear.const Bool.false 760048 2000) RS409to420.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns408p89 Ns408p90) 

noncomputable abbrev qz368 := (@instHAdd Real Real.instAdd)

noncomputable def Ns408p110 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz3) Bool.false Ns408p87 Ns408p88 2432778780636099 256000000000000000000 24192580039 16777216 319 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz3) (@HAdd.hAdd Real Real Real qz368 qz9 (Enclosure.sfrac Bool.true Ns408p89 Ns408p90)) Bool.false Ns408p87 Ns408p88 2432778780636099 256000000000000000000 Ns408p91 (Ns408p109 rfl rfl)) 

noncomputable def Ns408p111 := nat_lit 3795804036159243968053248 

noncomputable def Ns408p112 := nat_lit 2417851639229258349412352 

noncomputable def Ns408p113 := nat_lit 3502882219771998260432420787899100877791064676476141426850663237707452463653171478919085695744842405442290614950973922137171423643814400000 

noncomputable def Ns408p114 := nat_lit 69061887427279807374175457422696049589758900585025510522285359577850094671315332446731519433112496475662717985575392155893264493730122956800 

noncomputable def Ns408p115 := nat_lit 2485694437845571402852175967864543685789780664636421666066628015935841517820280417084302752582675070192099788409222423681000000000000 

noncomputable def Ns408p116 := nat_lit 17492696409575064157388210813435115448300659279234674859191783210173521098771465666326746004675878520192243819467335868069859514475072000000 

noncomputable def Ns408p117 := nat_lit 2417166059954793258096141009794361735641561520475892868279987585224753313496036635635603180158937376648195129495138725456264257280554303488000 

noncomputable abbrev qz591 := (BSN.sinEvenQ 68719476736)

noncomputable abbrev qz592 := (BSN.sinOddQ 68719476736)

noncomputable def Ns408p118 := BSN.sin_dyadic_bound_f 107883239370 68719476736 4 3 33554432 12512208 Ns408p113 Ns408p114 Ns408p115 Ns408p116 Ns408p117 Ns408p115 33554418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107883239370) qz591 0 3 Ns408p113 Ns408p114 Ns408p115 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107883239370) qz592 0 3 Ns408p116 Ns408p117 Ns408p115 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz369 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable abbrev qz593 := (@Nat.cast Real Real.instNatCast Ns408p112)

noncomputable def Ns408p119 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz3) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24192580039) qz369) Bool.false 24192580039 16777216 319 33554432 Bool.true 33554418 33554432 1 6250000 (Ns408p110 rfl) (Enclosure.sfrac_false_div 24192580039 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24192580039) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns408p111) qz593) 226375608064910080 72057594037927936 Bool.false 33554418 33554432 229 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q1 24192580039 16777216 226375608064910080 72057594037927936 229 Ns408p111 Ns408p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554418 33554432 Ns408p111 Ns408p112 107883239370 68719476736 12512208 12500000 (Ns408p118 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns408p120 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz3) Bool.false Ns408p87 Ns408p88 2432778780636099 256000000000000000000 387081280624 268435456 2552 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz3) (@HAdd.hAdd Real Real Real qz368 qz9 (Enclosure.sfrac Bool.true Ns408p89 Ns408p90)) Bool.false Ns408p87 Ns408p88 2432778780636099 256000000000000000000 Ns408p91 (Ns408p109 rfl rfl)) 

noncomputable def Ns408p121 := Ns408p86 47881 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 582 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 153602648 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 386 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 211283609 268435456) qz8 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 1) Bool.true 16777209 16777216 126706527 13107200000000 268435344 268435456 2595 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz3)) Bool.true 16777209 16777216 126706527 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz3) qz3) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz3)) Bool.true 33554418 33554432 2027304432 209715200000000 16777209 16777216 126706527 13107200000000 (Ns408p119 rfl rfl) rfl)) rfl) (Ns408p120 rfl) RS409to420.d7 

noncomputable def Ns408p122 := nat_lit 38744858402987102043094408700589867966721069000563645258661888000000000 

noncomputable def Ns408p123 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120 

noncomputable def Ns408p124 := nat_lit 19708275653148981113665583922622147865715381800796160000000000000000 

noncomputable def Ns408p125 := nat_lit 116195158657655008167055894933924359604431776238089343455985664000000000 

noncomputable def Ns408p126 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400 

noncomputable abbrev qz370 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz371 := (BSN.cosOddQ 268435456)

noncomputable def Ns408p127 := BSN.cos_dyadic_bound_f 258125600 268435456 3 2 268435456 134217728 Ns408p122 Ns408p123 Ns408p124 Ns408p125 Ns408p126 Ns408p124 153602648 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 258125600) qz370 0 2 Ns408p122 Ns408p123 Ns408p124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 258125600) qz371 0 2 Ns408p125 Ns408p126 Ns408p124 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p128 := nat_lit 8843414677852812871818387980243784785101371571608338636183857695252736 

noncomputable def Ns408p129 := nat_lit 1027546437199559946494091208266695128364905395882159074083003392256 

noncomputable def Ns408p130 := nat_lit 26528188940684039495562175758314820965047384904033251590403407078973696 

noncomputable def Ns408p131 := BSN.cos_dyadic_bound_f 178433002 268435456 3 2 268435456 134217728 Ns408p128 Ns408p123 Ns408p129 Ns408p130 Ns408p126 Ns408p129 211283609 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 178433002) qz370 0 2 Ns408p128 Ns408p123 Ns408p129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 178433002) qz371 0 2 Ns408p130 Ns408p126 Ns408p129 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p132 := nat_lit 80835531011723650962484893782016 

noncomputable def Ns408p133 := nat_lit 623075623024179315423659559506411520 

noncomputable def Ns408p134 := nat_lit 4361529361169255207965616916544880640 

noncomputable abbrev qz372 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz373 := (BSN.sinOddQ 268435456)

noncomputable def Ns408p135 := BSN.sin_dyadic_bound_f 94820136 268435456 2 1 268435456 134217728 Ns408p132 Ns408p133 Ns408p132 Ns408p132 Ns408p134 Ns408p132 92860565 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 94820136) qz372 0 1 Ns408p132 Ns408p133 Ns408p132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 94820136) qz373 0 1 Ns408p132 Ns408p134 Ns408p132 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p136 := nat_lit 132134961934428643755651656640625 

noncomputable def Ns408p137 := BSN.sin_dyadic_bound_f 107214725 268435456 2 1 268435456 134217728 Ns408p136 Ns408p133 Ns408p136 Ns408p136 Ns408p134 Ns408p136 104386801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 107214725) qz372 0 1 Ns408p136 Ns408p133 Ns408p136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 107214725) qz373 0 1 Ns408p136 Ns408p134 Ns408p136 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p138 := Ns408p84 81284 BSN.abs_quadSignPos (BSN.cos_quad_nat3 247 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 92860565 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 139 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 104386801 268435456) qz8 rfl rfl (Ns408p121 RS409to420.d9 RS409to420.d11 RS409to420.d13 RS409to420.d17 (Ns408p127 rfl rfl) (Ns408p131 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns408p120 rfl) RS409to420.d19 RS409to420.d21 RS409to420.d23 RS409to420.d25 RS409to420.d17 (Ns408p135 rfl rfl) (Ns408p137 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns408p139 := nat_lit 52389897808512812617353108496 

noncomputable def Ns408p140 := BSN.sin_dyadic_bound_f 15129058 268435456 2 1 268435456 134217728 Ns408p139 Ns408p133 Ns408p139 Ns408p139 Ns408p134 Ns408p139 15121049 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15129058) qz372 0 1 Ns408p139 Ns408p133 Ns408p139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15129058) qz373 0 1 Ns408p139 Ns408p134 Ns408p139 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p141 := nat_lit 45992705718501492314845840690830729440731391044370758357546779414585600 

noncomputable def Ns408p142 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080 

noncomputable def Ns408p143 := nat_lit 8576958774908732473062831786302599729156956639952911707898846863616 

noncomputable def Ns408p144 := nat_lit 120443199900915960972020814367378849088068341472125395746047824143278336 

noncomputable def Ns408p145 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800 

noncomputable def Ns408p146 := BSN.sin_dyadic_bound_f 232630506 268435456 3 2 268435456 134217728 Ns408p141 Ns408p142 Ns408p143 Ns408p144 Ns408p145 Ns408p143 204586090 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 232630506) qz372 0 2 Ns408p141 Ns408p142 Ns408p143 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 232630506) qz373 0 2 Ns408p144 Ns408p145 Ns408p143 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p147 := Ns408p82 109603 BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 15121049 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 23 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 204586090 268435456) qz8 rfl rfl (Ns408p138 rfl rfl) (Ns408p120 rfl) RS409to420.d27 RS409to420.d29 RS409to420.d31 RS409to420.d33 RS409to420.d17 (Ns408p140 rfl rfl) (Ns408p146 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p148 := nat_lit 22012026672526165208400397336576 

noncomputable def Ns408p149 := nat_lit 124615124604835863084731911901282304 

noncomputable def Ns408p150 := nat_lit 1869226869072537946270978678519234560 

noncomputable def Ns408p151 := BSN.cos_dyadic_bound_f 68495968 268435456 2 1 268435456 134217728 Ns408p148 Ns408p149 Ns408p148 Ns408p148 Ns408p150 Ns408p148 259743801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 68495968) qz370 0 1 Ns408p148 Ns408p149 Ns408p148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 68495968) qz371 0 1 Ns408p148 Ns408p150 Ns408p148 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p152 := nat_lit 17375981216084302311360358560000 

noncomputable def Ns408p153 := BSN.sin_dyadic_bound_f 64563540 268435456 2 1 268435456 134217728 Ns408p152 Ns408p133 Ns408p152 Ns408p152 Ns408p134 Ns408p152 63942850 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 64563540) qz372 0 1 Ns408p152 Ns408p133 Ns408p152 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 64563540) qz373 0 1 Ns408p152 Ns408p134 Ns408p152 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p154 := Ns408p80 134346 BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 259743801 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 145 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63942850 268435456) qz8 rfl rfl (Ns408p147 rfl) (Ns408p120 rfl) RS409to420.d35 RS409to420.d37 RS409to420.d39 RS409to420.d41 RS409to420.d17 (Ns408p151 rfl rfl) (Ns408p153 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p155 := nat_lit 9897318364857930272368093122576 

noncomputable def Ns408p156 := BSN.cos_dyadic_bound_f 56089218 268435456 2 1 268435456 134217728 Ns408p155 Ns408p149 Ns408p155 Ns408p155 Ns408p150 Ns408p155 262596862 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 56089218) qz370 0 1 Ns408p155 Ns408p149 Ns408p155 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 56089218) qz371 0 1 Ns408p155 Ns408p150 Ns408p155 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p157 := Ns408p78 Bool.true 251901565 134346 Bool.true 56089218 14148475504056880 1 Bool.false 262596862 Bool.false Bool.true 168861147 145739 BSN.abs_quadSignPos (BSN.cos_quad_nat0 196 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 262596862 268435456) qz8 rfl (Ns408p154 rfl) (Ns408p120 rfl) RS409to420.d43 RS409to420.d45 RS409to420.d17 (Ns408p156 rfl rfl) rfl 

noncomputable def Ns408p158 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 10) 168861147 268435456 145739 268435456 168861147 268435456 145739 268435456 90656637991256064 168861147 134217728 145739 134217728 (Ns408p157 rfl rfl rfl rfl) 

noncomputable def Ns408p159 := @Enclosure.Real.IsNear.mulLit_ff qz583 (Zeta.RiemannSiegel.correction qz7) 5058883 16777216 1 16777216 258985536521489 281474976710656 5890245175010881 219902325555200000000 1310177527954439836787 4722366482869645213696 

noncomputable abbrev qz594 := (@HPow.hPow Real Nat Real RSCompact.c1 qz5 10)

noncomputable def Ns408p160 := @Enclosure.Real.IsNear.mulLit_ff qz594 qz6 1 1 0 1 5058883 16777216 1 16777216 5058883 16777216 1 16777216 

noncomputable abbrev qz18 := qz352

noncomputable abbrev qz19 := (@Enclosure.Real.IsNear.of_eq qz352 (@HMul.hMul Real Real Real qz350 qz349 qz348) Bool.false 253682788559 2097152000 47503 2097152000 (BSN.t_div_two_pi_mk qz349 760048 1000 qz355) (@Enclosure.Real.IsNear.mulLit_ff qz349 qz348 760048 1000 0 1 5340353 33554432 1 33554432 253682788559 2097152000 47503 2097152000 (Enclosure.Real.IsNear.const Bool.false 760048 1000) RS409to420.d48 rfl))

noncomputable def Ns408p161 := @Enclosure.Real.IsNear.sqrt_image qz18 253682788559 2097152000 47503 2097152000 184522955 184522991 16777216 qz19 

noncomputable abbrev qz722 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 760048 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz595 := qz722

noncomputable abbrev qz374 := qz595

noncomputable abbrev qz20 := qz374

noncomputable def Ns408p162 := @Enclosure.Real.IsNear.sqrt_image qz20 184522973 16777216 9 8388608 55639747 55639753 16777216 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 369045946 33554432 36 33554432 184522973 16777216 9 8388608 (Ns408p161 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz596 := (Real.sqrt qz722)

noncomputable abbrev qz375 := qz596

noncomputable abbrev qz21 := qz375

noncomputable def Ns408p163 := @Enclosure.Real.IsNear.inv_image qz21 27819875 8388608 3 16777216 5058882 5058884 16777216 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 111279500 33554432 6 33554432 27819875 8388608 3 16777216 (Ns408p162 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns408p164 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz21) Bool.false 10117766 33554432 2 33554432 5058883 16777216 1 16777216 (Ns408p163 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz22 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz354))

noncomputable abbrev qz597 := (@HMul.hMul Real Real Real qz714 qz717 qz717)

noncomputable abbrev qz598 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz376 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz597 qz582) qz598)

noncomputable abbrev qz23 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz376))

noncomputable def Ns408p165 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz7) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv qz22) qz23) Bool.false 258985536521489 

noncomputable def Ns408p166 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz22) qz23 33556073 33554432 233 

noncomputable def Ns408p167 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz22) Bool.false 33556073 33554432 233 33554432 33556073 33554432 233 

noncomputable def Ns408p168 := @Enclosure.Real.IsNear.recentre' qz22 Bool.false 33552791 33554432 1452304432 209715200000000 33552791 33554432 90769027 13107200000000 

noncomputable abbrev qz24 := (@HMul.hMul Real Real Real qz350 qz347 qz354)

noncomputable abbrev qz377 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable def Ns408p169 := @Enclosure.Real.IsNear.cos_image qz24 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 52624231) qz377) Bool.false 52624231 8388608 227 33554432 Bool.false 33552791 33554432 1 

noncomputable def Ns408p170 := nat_lit 242874678753340603112932351 

noncomputable def Ns408p171 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns408p172 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz7 884279719003555 140737488355328 1 500000000000000 16750813 16777216 9 8388608 14812404212721096140215 2361183241434822606848 Ns408p170 

noncomputable def Ns408p173 := @Enclosure.Real.IsNear.subLit_ff_p qz20 qz343 184522973 16777216 9 8388608 10 1 0 1 16750813 16750813 16777216 9 

noncomputable def Ns408p174 := @Ns408p173 8388608 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 369045946 33554432 36 33554432 184522973 16777216 9 8388608 (Ns408p161 rfl rfl rfl rfl rfl rfl) rfl) (Enclosure.Real.IsNear.const Bool.false 10 1) 

noncomputable def Ns408p175 := @Enclosure.Real.IsNear.recentre' qz24 Bool.false 14812404212721096140215 2361183241434822606848 Ns408p170 Ns408p171 52624231 8388608 227 33554432 (@Ns408p172 Ns408p171 RS409to420.d47 (Ns408p174 rfl rfl) rfl) 

noncomputable def Ns408p176 := nat_lit 1887022237457777281728512 

noncomputable def Ns408p177 := nat_lit 1208925819614629174706176 

noncomputable def Ns408p178 := nat_lit 3423092621049639393174249157110888408699925345332399860635407010479963179465813016250018363669297702920814286553243100231709415491905191601 

noncomputable def Ns408p179 := nat_lit 2319992103124567253811676115515760620746540262658963604774524825898071706723251558977004902667150293848917935106721009942782315790001 

noncomputable def Ns408p180 := nat_lit 17094724719769205423660788932140562617551931330401598894287613614267009159482729632870901837372333769088347086944901025226187760361951133361 

noncomputable def Ns408p181 := BSN.sin_dyadic_bound_f 107264795443 68719476736 4 3 33554432 12512208 Ns408p178 Ns408p114 Ns408p179 Ns408p180 Ns408p117 Ns408p179 33552791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107264795443) qz591 0 3 Ns408p178 Ns408p114 Ns408p179 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107264795443) qz592 0 3 Ns408p180 Ns408p117 Ns408p179 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p182 := @Ns408p169 6250000 (Ns408p175 rfl) (Enclosure.sfrac_false_div 52624231 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 52624231) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns408p176) (@Nat.cast Real Real.instNatCast Ns408p177)) 226375608064910080 72057594037927936 Bool.false 33552791 33554432 0 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 52624231 8388608 226375608064910080 72057594037927936 0 Ns408p176 Ns408p177 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33552791 33554432 Ns408p176 Ns408p177 107264795443 68719476736 12512208 12500000 (Ns408p181 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns408p183 := @Enclosure.Real.IsNear.inv_image qz22 33552791 33554432 90769027 13107200000000 16777920 16778153 16777216 (Ns408p168 (Ns408p182 rfl rfl) rfl) rfl 

noncomputable def Ns408p184 := @Enclosure.Real.IsNear.recentre' qz23 Bool.false 15435986 16777216 

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz350 qz347 qz376)

noncomputable def Ns408p185 := @Enclosure.Real.IsNear.cos_image qz25 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6754031)) qz369) Bool.true 6754031 16777216 

noncomputable def Ns408p186 := nat_lit 15947505240442917321881995525 

noncomputable def Ns408p187 := nat_lit 39614081257132168796771975168 

noncomputable def Ns408p188 := nat_lit 610573098352218603187361027669993 

noncomputable def Ns408p189 := @Enclosure.Real.IsNear.recentre' qz25 Bool.true Ns408p186 Ns408p187 Ns408p188 

noncomputable def Ns408p190 := nat_lit 30223145490365729367654400000000000000 

noncomputable abbrev qz26 := qz376

noncomputable def Ns408p191 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz26 884279719003555 140737488355328 1 500000000000000 18034457760055 

noncomputable abbrev qz378 := (@HSub.hSub Real Real Real qz584 qz597 qz582)

noncomputable abbrev qz27 := qz378

noncomputable abbrev qz379 := qz598

noncomputable abbrev qz28 := qz379

noncomputable def Ns408p192 := @Enclosure.Real.IsNear.subLit_tf qz27 qz28 442271715639 281474976710656 113127435 35184372088832 1 16 

noncomputable abbrev qz380 := qz597

noncomputable abbrev qz29 := qz380

noncomputable def Ns408p193 := @Enclosure.Real.IsNear.subLit_ff_n qz29 qz7 280589736160969 281474976710656 75378699 35184372088832 16750813 16777216 9 8388608 

noncomputable def Ns408p194 := @Enclosure.Real.IsNear.mulLit_ff qz7 qz7 16750813 16777216 9 8388608 16750813 16777216 9 8388608 280589736160969 281474976710656 

noncomputable def Ns408p195 := nat_lit 2080904735890965572090579521 

noncomputable def Ns408p196 := nat_lit 1901475900342344102245054808064 

noncomputable def Ns408p197 := nat_lit 28522138505135161533675822120960 

noncomputable def Ns408p198 := BSN.cos_dyadic_bound_f 6754031 16777216 2 1 16777216 6250000 Ns408p195 Ns408p196 Ns408p195 Ns408p195 Ns408p197 Ns408p195 15435986 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 6754031) (BSN.cosEvenQ 16777216) 0 1 Ns408p195 Ns408p196 Ns408p195 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 6754031) (BSN.cosOddQ 16777216) 0 1 Ns408p195 Ns408p197 Ns408p195 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz381 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns408p199 := @Ns408p184 4277304432 209715200000000 7717993 8388608 267331527 13107200000000 (@Ns408p185 679 33554432 Bool.false 15435986 16777216 1 6250000 (@Ns408p189 Ns408p190 6754031 16777216 679 33554432 (@Ns408p191 281474976710656 113127435 35184372088832 Ns408p186 Ns408p187 Ns408p188 Ns408p190 RS409to420.d47 (@Ns408p192 0 1 288551324160880 18034457760055 281474976710656 113127435 35184372088832 (@Ns408p193 7420088103966081024 442271715639 281474976710656 113127435 35184372088832 (@Ns408p194 75378699 35184372088832 (Ns408p174 rfl rfl) (Ns408p174 rfl rfl) rfl) (Ns408p174 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6754031 16777216) (BSN.cos_neg_of_bound 6754031 16777216 Bool.false 15435986 16777216 1 6250000 (Ns408p198 rfl rfl)) rfl rfl) 

noncomputable def Ns408p200 := @Ns408p159 15000199761173579499027 Ns408p75 (Ns408p160 (@Enclosure.Real.IsNear.of_eq qz594 (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 10 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1)) (@Enclosure.Real.IsNear.of_eq qz6 (@Inv.inv Real Real.instInv qz21) Bool.false 5058883 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz18 (BSN.t_div_two_pi_nonneg qz3 760048 1000 qz8)) Ns408p164) rfl) (@Ns408p165 281474976710656 5890245175010881 219902325555200000000 (BSN.correction_mk qz7 (BSN.cos_two_pi_p_ne_zero_mk qz3 760048 1000 10 qz8 rfl rfl (@BSN.floor_sqrt_eq_dec qz3 760048 1000 10 qz8 rfl rfl rfl))) (@Ns408p166 33554432 7717993 8388608 267331527 13107200000000 258985536521489 281474976710656 5890245175010881 219902325555200000000 (@Ns408p167 33554432 (Ns408p183 rfl rfl rfl rfl rfl) rfl) (Ns408p199 rfl) rfl)) 

noncomputable abbrev qz30 := qz356

noncomputable def Ns408p201 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz3) (hardyZApproximantRS₀ qz3) Bool.true 7251450955349397247091 4722366482869645213696 Ns408p74 Ns408p75 (@Eq.refl Real (hardyZApproximantRS₀ qz3)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz3) (@HSub.hSub Real Real Real qz30 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz3) qz3 10) (@HMul.hMul Real Real Real qz4 qz583 (Zeta.RiemannSiegel.correction qz7))) Bool.true 7251450955349397247091 4722366482869645213696 Ns408p74 Ns408p75 (BSN.hardyZApproximantRS₀_eq qz3 10 (@BSN.floor_sqrt_eq_dec qz3 760048 1000 10 qz8 rfl rfl rfl)) (@Ns408p77 7251450955349397247091 4722366482869645213696 Ns408p74 Ns408p75 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz3) qz3 10) (@HAdd.hAdd Real Real Real qz368 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 10)) Bool.true 168861147 134217728 145739 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz3) qz3 10) (Ns408p158 (Ns408p157 rfl rfl rfl rfl) rfl rfl)) (Ns408p200 rfl) rfl rfl)) 

theorem RS409to420.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz3) Bool.true 7251450955349397247091 4722366482869645213696 Ns408p74 Ns408p75 := Ns408p201 

theorem RS409to420.d50 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS409to420.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS409to420.d3 a b h)) 

noncomputable def Ns408p202 := nat_lit 1449438752820620681019392 

noncomputable def Ns408p203 := BSN.log_dyadic_bound 3 19 5 4 16049467073745 16777216 6250000 135406373544 688905 5342767 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 19) 0 4 135406373544 16049467073745 688905 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz723 := (Enclosure.sfrac Bool.false 11 1)

noncomputable abbrev qz599 := qz723

noncomputable abbrev qz382 := qz599

noncomputable abbrev qz31 := qz382

noncomputable abbrev qz383 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11) qz577)

theorem RS409to420.d51 : Enclosure.Real.IsNear (Real.log qz31) Bool.false 10799160248194789 4503599627370496 160000003 1000000000000000 := BSN.isNear_log_sfrac 11 1 10799160248194789 4503599627370496 160000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz383) Bool.false Ns408p202 604462909807314587353088 1000000018750000 6250000000000000000000 10799160248194789 4503599627370496 160000003 1000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 5342767 16777216 24973259072661432 36028797018963968 6250000 1000000000000000 rfl rfl rfl rfl (Ns408p203 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS409to420.d52 : Enclosure.Real.IsNear (Real.log qz31) Bool.false 643680110 268435456 44 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz31) Bool.false 10799160248194789 4503599627370496 160000003 1000000000000000 643680110 268435456 44 268435456 RS409to420.d51 rfl 

noncomputable abbrev qz384 := (Real.sqrt (@Nat.cast Real Real.instNatCast 11))

noncomputable def Ns408p204 := @Enclosure.Real.IsNear.inv_image qz384 111287461 33554432 1 33554432 5058520 5058521 16777216 (@Enclosure.Real.IsNear.of_eq qz384 (Real.sqrt qz383) Bool.false 111287461 33554432 1 33554432 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz383) Bool.false 111287461 33554432 1 33554432 111287461 33554432 1 33554432 (BSN.sqrt_enclosure 11 1 55643730 55643731 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz385 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

theorem RS409to420.d53 : Enclosure.Real.IsNear qz385 Bool.false 10117041 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz385 Bool.false 10117041 33554432 1 33554432 10117041 33554432 1 33554432 (Ns408p204 rfl rfl) rfl 

theorem RS409to420.d54 : Enclosure.Real.IsNear qz385 Bool.false 80936328 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz385 Bool.false 10117041 33554432 1 33554432 80936328 268435456 8 268435456 RS409to420.d53 rfl 

noncomputable def Ns408p205 := nat_lit 11529215046068469760000000 

noncomputable def Ns408p206 := nat_lit 1620758392783662294209870692352 

noncomputable abbrev qz724 := (Enclosure.sfrac Bool.false 762013 1000)

noncomputable abbrev qz600 := qz724

noncomputable abbrev qz386 := qz600

noncomputable abbrev qz32 := qz386

noncomputable abbrev qz33 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 11)

noncomputable abbrev qz725 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 762013 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz601 := qz725

noncomputable abbrev qz387 := qz601

noncomputable abbrev qz34 := (@HPow.hPow Real Real Real qz351 qz387 qz353)

noncomputable abbrev qz726 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 762013 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz602 := qz726

noncomputable abbrev qz388 := qz602

noncomputable abbrev qz35 := qz388

noncomputable def Ns408p207 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz32) qz32 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz34) (Zeta.RiemannSiegel.correction qz35)) 162566103 33554432 19627 16777216 2544074078434507114993 9444732965739290427392 45478155065502554889 Ns408p205 Ns408p206 

noncomputable def Ns408p208 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz32) qz32 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 762013 1000 196 242 268435456 134217728 4503599627370496 Bool.false 388346377141 2559 

noncomputable def Ns408p209 := Ns408p208 618095470 44 84886744 8 643680110 44 80936328 8 Bool.false 640203207 134704 Bool.true 5550299 Bool.true 105136879 14148475504056880 1 Bool.false 268378077 Bool.false Bool.false 248108077 Bool.true Bool.false 650264412 

noncomputable def Ns408p210 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz32) qz32 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 762013 1000 87 144 268435456 134217728 4503599627370496 Bool.false 388346377141 2559 

noncomputable def Ns408p211 := Ns408p210 558195838 44 94906264 8 589812974 44 89478488 8 Bool.false 537978979 109896 Bool.true 321911701 Bool.true 380106945 14148475504056880 1 Bool.false 250115857 Bool.false Bool.false 41384762 Bool.false Bool.false 640203207 

noncomputable def Ns408p212 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz32) qz32 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 762013 1000 51 22 268435456 134217728 4503599627370496 Bool.false 388346377141 2559 

noncomputable def Ns408p213 := Ns408p212 480971758 44 109588312 8 522351262 44 101459064 8 Bool.false 436321515 81504 Bool.false 335116070 Bool.true 415611647 14148475504056880 1 Bool.false 254605758 Bool.false Bool.false 6045270 Bool.true Bool.false 537978979 

noncomputable def Ns408p214 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz32) qz32 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 762013 1000 248 140 268435456 134217728 4503599627370496 Bool.false 388346377141 2559 

noncomputable def Ns408p215 := Ns408p214 372130544 43 134217720 8 432030192 43 120047984 16 Bool.false 228546692 48015 Bool.false 207022705 Bool.false 101714487 14148475504056880 1 Bool.false 192484617 Bool.false Bool.false 249394301 Bool.false Bool.false 436321515 

noncomputable def Ns408p216 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz32) qz32 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 762013 1000 584 388 268435456 134217728 4503599627370496 Bool.false 388346377141 2559 

noncomputable def Ns408p217 := Ns408p216 186065264 43 189812528 16 294906480 43 154981288 8 Bool.false 114296 2611 Bool.false 314289017 Bool.false 20723429 14148475504056880 1 Bool.false 104528374 Bool.false Bool.false 267635920 Bool.false Bool.false 228546692 

noncomputable def Ns408p218 := nat_lit 45921545789392540100761775268843061512897991851597554518171 

noncomputable def Ns408p219 := nat_lit 31742206982662112628816901368477107223104177521557504000 

noncomputable def Ns408p220 := nat_lit 123325706915641105521402823020640000 

noncomputable def Ns408p221 := nat_lit 563854864713102312890969283083057689920 

noncomputable abbrev qz603 := (@Eq.refl Real qz724)

noncomputable abbrev qz389 := qz603

noncomputable abbrev qz36 := qz389

noncomputable def Ns408p222 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz32 762013 1000 2322656248676 16000000 1524026 4000 2000 Ns408p220 Ns408p221 qz36 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns408p223 := nat_lit 14694894652605612832243768086029779684127357392511217445814720 

noncomputable abbrev qz604 := (@HSub.hSub Real Real Real qz718 qz719 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz720 (@Nat.cast Real Real.instNatCast 1524026))))

noncomputable abbrev qz390 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 762013 4000) (Real.log (Enclosure.sfrac Bool.false 2322656248676 16000000))) (@HMul.hMul Real Real Real qz579 qz585 qz604))

noncomputable abbrev qz605 := (Enclosure.sfrac Bool.false 762013 2000)

noncomputable abbrev qz37 := (@HSub.hSub Real Real Real qz356 (@HSub.hSub Real Real Real qz356 qz390 qz605) (@HMul.hMul Real Real Real qz350 qz605 (Real.log Real.pi)))

noncomputable def Ns408p224 := @Enclosure.Real.IsNear.addLit_ft_p qz37 (Enclosure.sfrac Bool.true Ns408p220 Ns408p221) 26061488148587712099691 18014398509481984000 39024670765399929 4096000000000000000000 Ns408p220 Ns408p221 0 1 Ns408p223 

noncomputable def Ns408p225 := nat_lit 1748956863801184563369317761024000 

noncomputable abbrev qz38 := (@HSub.hSub Real Real Real qz356 qz390 qz605)

noncomputable def Ns408p226 := @Enclosure.Real.IsNear.subLit_ff_p qz38 (@HMul.hMul Real Real Real qz4 qz605 (Real.log Real.pi)) 33918459519108204737899 18014398509481984000 15400272954721 4000000000000000000 29269499221893 67108864000 762013 134217728000 Ns408p225 26061488148587712099691 18014398509481984000 

noncomputable def Ns408p227 := nat_lit 13567383807643281895159600 

noncomputable abbrev qz39 := qz390

noncomputable def Ns408p228 := @Enclosure.Real.IsNear.subLit_ff_p qz39 qz605 8156412488962230454959 3602879701896396800 15400272954721 4000000000000000000 762013 2000 0 1 Ns408p227 33918459519108204737899 18014398509481984000 15400272954721 4000000000000000000 

noncomputable def Ns408p229 := nat_lit 18366608122985180447775971617466744832 

noncomputable def Ns408p230 := nat_lit 57475395889677365055324160 

noncomputable def Ns408p231 := nat_lit 5724070465221270340641376555911574856668570992848640 

noncomputable def Ns408p232 := nat_lit 4974668140787683216013768854774405099487974852608 

noncomputable def Ns408p233 := nat_lit 7757828412826792747593147349317717123350569728 

noncomputable def Ns408p234 := BSN.log_dyadic_bound 225504248676 4419808248676 3 2 Ns408p231 134217728 50000000 Ns408p232 Ns408p233 13707821 4645312497352 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 225504248676) (BSN.artanhQ 4419808248676) 0 2 Ns408p232 Ns408p231 Ns408p233 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz391 := (Real.log (Enclosure.sfrac Bool.false 2322656248676 16000000))

noncomputable def Ns408p235 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 762013 4000) qz391 762013 4000 0 1 53528133677018215 4503599627370496 20000017 1000000000000000 8157826745525136213359 3602879701896396800 15240272954221 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 762013 4000) (BSN.isNear_log_sfrac 2322656248676 16000000 53528133677018215 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2322656248676) qz359)) Bool.false Ns408p230 Ns408p100 1000000850000000 50000000000000000000000 53528133677018215 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2322656248676 16000000 17 4645312497352 4194304000000 13707821 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns408p234 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns408p236 := BSN.arctan_dyadic_bound_f 1000 1524026 1 0 16777216 6250000 0 1 1 0 1 1 11008 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1524026) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1524026) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz392 := (@Nat.cast Real Real.instNatCast 1524026)

noncomputable def Ns408p237 := @Enclosure.Real.IsNear.subLit_ff_p qz12 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz13 qz392)) 884279719003555 562949953421312 1 2000000000000000 11008 16777216 1 6250000 14829554897054685200384 883910351816099 562949953421312 320000001 2000000000000000 qz14 (Ns408p236 rfl) rfl rfl 

noncomputable abbrev qz393 := (@HMul.hMul Real Real Real qz579 qz585 qz604)

noncomputable abbrev qz40 := qz393

noncomputable abbrev qz394 := qz604

noncomputable abbrev qz41 := qz394

noncomputable def Ns408p238 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 762013 4000) qz391) qz40 8157826745525136213359 3602879701896396800 15240272954221 4000000000000000000 883910351816099 2251799813685248 320000001 8000000000000000 Ns408p229 8156412488962230454959 3602879701896396800 15400272954721 4000000000000000000 (Ns408p235 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz16 qz41 1 4 0 1 883910351816099 562949953421312 320000001 2000000000000000 883910351816099 2251799813685248 320000001 8000000000000000 qz367 Ns408p237 rfl) 

noncomputable def Ns408p239 := @Ns408p224 Ns408p218 Ns408p219 39024670765399929 4096000000000000000000 (@Ns408p226 39024670765399929 4096000000000000000000 (Ns408p228 (Ns408p238 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 762013 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz605 (Real.log Real.pi) 762013 2000 0 1 38410761 33554432 1 67108864 29269499221893 67108864000 762013 134217728000 (Enclosure.Real.IsNear.const Bool.false 762013 2000) RS409to420.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns408p220 Ns408p221) 

noncomputable def Ns408p240 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz32) Bool.false Ns408p218 Ns408p219 39024670765399929 4096000000000000000000 24271648571 16777216 321 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz32) (@HAdd.hAdd Real Real Real qz368 qz37 (Enclosure.sfrac Bool.true Ns408p220 Ns408p221)) Bool.false Ns408p218 Ns408p219 39024670765399929 4096000000000000000000 Ns408p222 (Ns408p239 rfl rfl)) 

noncomputable def Ns408p241 := nat_lit 3796922975312057112461312 

noncomputable def Ns408p242 := nat_lit 1351022177176673393212619071971917012591877699988538705197371386811245655196364825942815560009069485905305193450274068190084827756302790641 

noncomputable def Ns408p243 := nat_lit 5312452879021523644167342878668926891519915429617346963252719967526930359331948649748578417931730498127901383505799396607174191825394073600 

noncomputable def Ns408p244 := nat_lit 2494501598393555584483721726912756546674544571641862066600985284225111829945047574310939970190621355655294837809447499538220724350961 

noncomputable def Ns408p245 := nat_lit 8176480206605356426868785336129380854040154449553824849800473620804781610840684611120746355129547759291731349834769097209788480456297902065 

noncomputable def Ns408p246 := nat_lit 483433211990958651619228201958872347128312304095178573655997517044950662699207327127120636031787475329639025899027745091252851456110860697600 

noncomputable def Ns408p247 := BSN.cos_dyadic_bound_f 107915041533 68719476736 4 3 33554432 12512208 Ns408p242 Ns408p243 Ns408p244 Ns408p245 Ns408p246 Ns408p244 14287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 107915041533) (BSN.cosEvenQ 68719476736) 0 3 Ns408p242 Ns408p243 Ns408p244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 107915041533) (BSN.cosOddQ 68719476736) 0 3 Ns408p245 Ns408p246 Ns408p244 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p248 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz32) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24271648571) qz369) Bool.false 24271648571 16777216 321 33554432 Bool.false 14287 33554432 1 6250000 (Ns408p240 rfl) (Enclosure.sfrac_false_div 24271648571 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24271648571) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns408p241) qz593) 226375608064910080 72057594037927936 Bool.false 14287 33554432 230 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q0 24271648571 16777216 226375608064910080 72057594037927936 230 Ns408p241 Ns408p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 14287 33554432 Ns408p241 Ns408p112 107915041533 68719476736 12512208 12500000 (Ns408p247 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns408p249 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz32) Bool.false Ns408p218 Ns408p219 39024670765399929 4096000000000000000000 388346377141 268435456 2559 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz32) (@HAdd.hAdd Real Real Real qz368 qz37 (Enclosure.sfrac Bool.true Ns408p220 Ns408p221)) Bool.false Ns408p218 Ns408p219 39024670765399929 4096000000000000000000 Ns408p222 (Ns408p239 rfl rfl)) 

noncomputable def Ns408p250 := Ns408p217 48015 BSN.abs_quadSignPos (BSN.cos_quad_nat0 584 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 104528374 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 388 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267635920 268435456) qz36 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz32) qz32 1) Bool.false 14287 33554432 127487777 13107200000000 114296 268435456 2611 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz32) qz32 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz32)) Bool.false 14287 33554432 127487777 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz32) qz32) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz32)) Bool.false 14287 33554432 2039804432 209715200000000 14287 33554432 127487777 13107200000000 (Ns408p248 rfl rfl) rfl)) rfl) (Ns408p249 rfl) RS409to420.d7 

noncomputable def Ns408p251 := nat_lit 5255900642457128645716632857304314956192391870087534499833036094615504577103055744999474412364213869229367841 

noncomputable def Ns408p252 := nat_lit 67052582193422231333984484018745857420694574238012043916021913709013615522643186318434558042568065189255577600 

noncomputable def Ns408p253 := nat_lit 928860415987484267621957497382476808026225113560951875465918387537185822605209672990192174027566473761 

noncomputable def Ns408p254 := nat_lit 31862042259325615752598549705299575699760802261951768840217539861034650404254543361337914205090017844796580385 

noncomputable def Ns408p255 := nat_lit 6101784979601423051392588045705873025283206255659095996357994147520239012560529954977544781873693932222257561600 

noncomputable def Ns408p256 := BSN.cos_dyadic_bound_f 314289017 268435456 4 3 268435456 134217728 Ns408p251 Ns408p252 Ns408p253 Ns408p254 Ns408p255 Ns408p253 104528374 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 314289017) qz370 0 3 Ns408p251 Ns408p252 Ns408p253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 314289017) qz371 0 3 Ns408p254 Ns408p255 Ns408p253 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p257 := nat_lit 184436329235495384354104477681 

noncomputable def Ns408p258 := BSN.cos_dyadic_bound_f 20723429 268435456 2 1 268435456 134217728 Ns408p257 Ns408p149 Ns408p257 Ns408p257 Ns408p150 Ns408p257 267635920 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20723429) qz370 0 1 Ns408p257 Ns408p149 Ns408p257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20723429) qz371 0 1 Ns408p257 Ns408p150 Ns408p257 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p259 := nat_lit 16026258838484598523960697390311791499636710628599502430654848671690625 

noncomputable def Ns408p260 := nat_lit 3373990309577234916360116505837691846818022693594615476228562890625 

noncomputable def Ns408p261 := nat_lit 48072028534834641102049371937923699115216495840411318061012088889290625 

noncomputable def Ns408p262 := BSN.cos_dyadic_bound_f 207022705 268435456 3 2 268435456 134217728 Ns408p259 Ns408p123 Ns408p260 Ns408p261 Ns408p126 Ns408p260 192484617 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 207022705) qz370 0 2 Ns408p259 Ns408p123 Ns408p260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 207022705) qz371 0 2 Ns408p261 Ns408p126 Ns408p260 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p263 := nat_lit 933695739957531449294815113541686463381608930733357143227209538196801 

noncomputable def Ns408p264 := nat_lit 11456778177168500361297658692930524210698518752556929512739558721 

noncomputable def Ns408p265 := nat_lit 2801064306316240010883722745307673529096405395162566315822603135472961 

noncomputable def Ns408p266 := BSN.cos_dyadic_bound_f 101714487 268435456 3 2 268435456 134217728 Ns408p263 Ns408p123 Ns408p264 Ns408p265 Ns408p126 Ns408p264 249394301 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 101714487) qz370 0 2 Ns408p263 Ns408p123 Ns408p264 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 101714487) qz371 0 2 Ns408p265 Ns408p126 Ns408p264 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p267 := Ns408p215 81504 BSN.abs_quadSignPos (BSN.cos_quad_nat0 248 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 192484617 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 249394301 268435456) qz36 rfl rfl (Ns408p250 RS409to420.d9 RS409to420.d11 RS409to420.d13 RS409to420.d17 (Ns408p256 rfl rfl) (Ns408p258 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns408p249 rfl) RS409to420.d19 RS409to420.d21 RS409to420.d23 RS409to420.d25 RS409to420.d17 (Ns408p262 rfl rfl) (Ns408p266 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns408p268 := nat_lit 17658258237944731364748884389606887448594915791503170331845873549233521695912834447024898165787736629414400000 

noncomputable def Ns408p269 := nat_lit 871683568514489007341798292243696146469029465094156570908284878217177001794361422139649254553384847460322508800 

noncomputable def Ns408p270 := nat_lit 2006055995801904269186859438061852345237294242778010597680414986164316523968914604408952801000000000000 

noncomputable def Ns408p271 := nat_lit 88247478026365368318105255179517389324054962799524561551209490093219186993246246763865391167450253163072000000 

noncomputable def Ns408p272 := nat_lit 30508924898007115256962940228529365126416031278295479981789970737601195062802649774887723909368469661111287808000 

noncomputable def Ns408p273 := BSN.sin_dyadic_bound_f 335116070 268435456 4 3 268435456 134217728 Ns408p268 Ns408p269 Ns408p270 Ns408p271 Ns408p272 Ns408p270 254605758 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 335116070) qz372 0 3 Ns408p268 Ns408p269 Ns408p270 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 335116070) qz373 0 3 Ns408p271 Ns408p272 Ns408p270 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p274 := nat_lit 16109395700933837072284671835770264580880738164060778200165141477066624460496745354696720749639063890341739521 

noncomputable def Ns408p275 := nat_lit 26561495000173872074420650243254857126366387916678354403212338287972604616218812651785952911865269795841 

noncomputable def Ns408p276 := nat_lit 97508105504307048908415450848168071747952297267097152067958740835129561999388376343126817574271939409259346945 

noncomputable def Ns408p277 := BSN.cos_dyadic_bound_f 415611647 268435456 4 3 268435456 134217728 Ns408p274 Ns408p252 Ns408p275 Ns408p276 Ns408p255 Ns408p275 6045270 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 415611647) qz370 0 3 Ns408p274 Ns408p252 Ns408p275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 415611647) qz371 0 3 Ns408p276 Ns408p255 Ns408p275 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p278 := Ns408p213 109896 BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 254605758 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 6045270 268435456) qz36 rfl rfl (Ns408p267 rfl rfl) (Ns408p249 rfl) RS409to420.d27 RS409to420.d29 RS409to420.d31 RS409to420.d33 RS409to420.d17 (Ns408p273 rfl rfl) (Ns408p277 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p279 := nat_lit 168727267908092910660341940308144151731680969404027056845100733433771105 

noncomputable def Ns408p280 := nat_lit 115317203855394134361794018644983647040910335230162634736340616213601 

noncomputable def Ns408p281 := nat_lit 441718045238763175511928843824476138154431541229698218899976417043149921 

noncomputable def Ns408p282 := BSN.sin_dyadic_bound_f 321911701 268435456 3 2 268435456 134217728 Ns408p279 Ns408p142 Ns408p280 Ns408p281 Ns408p145 Ns408p280 250115857 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 321911701) qz372 0 2 Ns408p279 Ns408p142 Ns408p280 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 321911701) qz373 0 2 Ns408p281 Ns408p145 Ns408p280 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p283 := nat_lit 11259169938530523513498509135105167719173560324645787296583358728095625113296826913069227142029697208456890625 

noncomputable def Ns408p284 := nat_lit 9096402250020668482499737493313747890895932104878532622814829295009894173836995358086959187480712890625 

noncomputable def Ns408p285 := nat_lit 68196871925383494913028103918711600089798567019965996595565631311913385031448771988459207031535571528226490625 

noncomputable def Ns408p286 := BSN.cos_dyadic_bound_f 380106945 268435456 4 3 268435456 134217728 Ns408p283 Ns408p252 Ns408p284 Ns408p285 Ns408p255 Ns408p284 41384762 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 380106945) qz370 0 3 Ns408p283 Ns408p252 Ns408p284 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 380106945) qz371 0 3 Ns408p285 Ns408p255 Ns408p284 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz606 := (BSN.cos_quad_nat0 144 rfl)

noncomputable def Ns408p287 := Ns408p211 134704 BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 250115857 268435456) BSN.abs_quadSignPos qz606 (BSN.sfrac_eq_quadSignPos_mul Bool.false 41384762 268435456) qz36 rfl rfl (Ns408p278 rfl) (Ns408p249 rfl) RS409to420.d35 RS409to420.d37 RS409to420.d39 RS409to420.d41 RS409to420.d17 (Ns408p282 rfl rfl) (Ns408p286 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p288 := nat_lit 948998483607739248950338801 

noncomputable def Ns408p289 := BSN.cos_dyadic_bound_f 5550299 268435456 2 1 268435456 134217728 Ns408p288 Ns408p149 Ns408p288 Ns408p288 Ns408p150 Ns408p288 268378077 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 5550299) qz370 0 1 Ns408p288 Ns408p149 Ns408p288 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 5550299) qz371 0 1 Ns408p288 Ns408p150 Ns408p288 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p290 := nat_lit 1065847822972677770501532579295248821491991988821012804877173393523841 

noncomputable def Ns408p291 := nat_lit 14929341292473703757964219825420512765494283419922287332763436161 

noncomputable def Ns408p292 := nat_lit 3197513610235448364097081809446095623450444977896198570056854653699201 

noncomputable def Ns408p293 := BSN.cos_dyadic_bound_f 105136879 268435456 3 2 268435456 134217728 Ns408p290 Ns408p123 Ns408p291 Ns408p292 Ns408p126 Ns408p291 248108077 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 105136879) qz370 0 2 Ns408p290 Ns408p123 Ns408p291 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 105136879) qz371 0 2 Ns408p292 Ns408p126 Ns408p291 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz395 := (BSN.cos_quad_nat2 242 rfl)

noncomputable def Ns408p294 := Ns408p209 157016 BSN.abs_quadSignPos (BSN.cos_quad_nat0 196 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268378077 268435456) BSN.abs_quadSignNeg qz395 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 248108077 268435456) qz36 rfl rfl (Ns408p287 rfl) (Ns408p249 rfl) RS409to420.d43 RS409to420.d45 RS409to420.d52 RS409to420.d54 RS409to420.d17 (Ns408p289 rfl rfl) (Ns408p293 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p295 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz32) qz32 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz32) qz32 11) 650264412 268435456 157016 268435456 650264412 268435456 157016 268435456 349108047911583744 162566103 33554432 19627 16777216 (Ns408p294 rfl) 

noncomputable def Ns408p296 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz4 qz33 qz34) (Zeta.RiemannSiegel.correction qz35) 10111237 33554432 1 33554432 251608589377789 281474976710656 571828099219309 43980465111040000000 2544074078434507114993 9444732965739290427392 

noncomputable def Ns408p297 := @Enclosure.Real.IsNear.mulLit_tf qz33 qz34 1 1 0 1 10111237 33554432 1 33554432 10111237 33554432 1 33554432 

noncomputable abbrev qz42 := qz387

noncomputable def Ns408p298 := @Enclosure.Real.IsNear.sqrt_image qz42 4069418410589 33554432000 762013 33554432000 184761331 184761366 16777216 (@Enclosure.Real.IsNear.of_eq qz42 (@HMul.hMul Real Real Real qz4 qz32 qz2) Bool.false 4069418410589 33554432000 762013 33554432000 (BSN.t_div_two_pi_mk qz32 762013 1000 qz36) (@Enclosure.Real.IsNear.mulLit_ff qz32 qz2 762013 1000 0 1 5340353 33554432 1 33554432 4069418410589 33554432000 762013 33554432000 (Enclosure.Real.IsNear.const Bool.false 762013 1000) RS409to420.d48 rfl)) 

noncomputable abbrev qz727 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 762013 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz607 := qz727

noncomputable abbrev qz396 := qz607

noncomputable abbrev qz43 := qz396

noncomputable def Ns408p299 := @Enclosure.Real.IsNear.sqrt_image qz43 369522697 33554432 35 33554432 55675674 55675681 16777216 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 369522697 33554432 35 33554432 369522697 33554432 35 33554432 (Ns408p298 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns408p300 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz43) 111351355 33554432 7 33554432 5055618 5055619 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz43) Bool.false 111351355 33554432 7 33554432 111351355 33554432 7 33554432 (Ns408p299 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns408p301 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz43)) Bool.false 10111237 33554432 1 33554432 10111237 33554432 1 33554432 (Ns408p300 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz44 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz388))

noncomputable abbrev qz608 := (@HMul.hMul Real Real Real qz714 qz726 qz726)

noncomputable abbrev qz397 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz608 qz602) qz598)

noncomputable abbrev qz45 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz397))

noncomputable def Ns408p302 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz35) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv qz44) qz45) Bool.false 251608589377789 

noncomputable def Ns408p303 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz44) qz45 16830221 16777216 57 

noncomputable def Ns408p304 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz44) Bool.false 33660442 33554432 228 33554432 16830221 16777216 57 

noncomputable def Ns408p305 := @Enclosure.Real.IsNear.recentre' qz44 Bool.false 16724378 16777216 1414804432 209715200000000 8362189 8388608 88425277 13107200000000 

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz350 qz347 qz388)

noncomputable def Ns408p306 := @Enclosure.Real.IsNear.cos_image qz46 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 665931) qz377) Bool.false 665931 8388608 221 33554432 Bool.false 16724378 16777216 1 

noncomputable def Ns408p307 := nat_lit 188902527864036650150303857 

noncomputable def Ns408p308 := nat_lit 28823037615171174400000000000000 

noncomputable def Ns408p309 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz35 884279719003555 140737488355328 1 500000000000000 423945 33554432 35 33554432 374885965472962124475 4722366482869645213696 Ns408p307 

noncomputable def Ns408p310 := @Enclosure.Real.IsNear.subLit_ff_p qz43 qz31 369522697 33554432 35 33554432 11 1 0 1 423945 423945 33554432 35 

noncomputable abbrev qz398 := (Enclosure.Real.IsNear.const Bool.false 11 1)

noncomputable def Ns408p311 := @Ns408p310 33554432 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 369522697 33554432 35 33554432 369522697 33554432 35 33554432 (Ns408p298 rfl rfl rfl rfl rfl rfl) rfl) qz398 

noncomputable def Ns408p312 := @Enclosure.Real.IsNear.recentre' qz46 Bool.false 374885965472962124475 4722366482869645213696 Ns408p307 Ns408p308 665931 8388608 221 33554432 (@Ns408p309 Ns408p308 RS409to420.d47 (Ns408p311 rfl rfl) rfl) 

noncomputable def Ns408p313 := nat_lit 118842243771396506390315925504 

noncomputable def Ns408p314 := nat_lit 1782633656570947595854738882560 

noncomputable def Ns408p315 := BSN.cos_dyadic_bound_f 665931 8388608 2 1 16777216 6250000 196660405116049570691121 Ns408p313 196660405116049570691121 196660405116049570691121 Ns408p314 196660405116049570691121 16724378 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 665931) (BSN.cosEvenQ 8388608) 0 1 196660405116049570691121 Ns408p313 196660405116049570691121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 665931) (BSN.cosOddQ 8388608) 0 1 196660405116049570691121 Ns408p314 196660405116049570691121 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p316 := @Enclosure.Real.IsNear.inv_image qz44 8362189 8388608 88425277 13107200000000 16830107 16830335 16777216 (Ns408p305 (@Ns408p306 6250000 (Ns408p312 rfl) (Enclosure.sfrac_false_div 665931 8388608) (Ns408p315 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns408p317 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 14949809 16777216 

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz350 qz347 qz397)

noncomputable def Ns408p318 := @Enclosure.Real.IsNear.cos_image qz47 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 987929)) (@Nat.cast Real Real.instNatCast 2097152)) Bool.true 987929 2097152 

noncomputable def Ns408p319 := nat_lit 74645807933642189398378964845 

noncomputable def Ns408p320 := nat_lit 158456325028528675187087900672 

noncomputable def Ns408p321 := nat_lit 32493461009505012689705565881335033 

noncomputable def Ns408p322 := @Enclosure.Real.IsNear.recentre' qz47 Bool.true Ns408p319 Ns408p320 Ns408p321 

noncomputable def Ns408p323 := nat_lit 4835703278458516698824704000000000000000 

noncomputable abbrev qz48 := qz397

noncomputable def Ns408p324 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz48 884279719003555 140737488355328 1 500000000000000 84414248488879 

noncomputable abbrev qz399 := (@HSub.hSub Real Real Real qz584 qz608 qz602)

noncomputable abbrev qz49 := qz399

noncomputable def Ns408p325 := @Enclosure.Real.IsNear.subLit_tf qz49 qz28 14045504311215 1125899906842624 1204082495 1125899906842624 1 16 

noncomputable abbrev qz400 := qz608

noncomputable abbrev qz50 := qz400

noncomputable def Ns408p326 := @Enclosure.Real.IsNear.subLit_ff_n qz50 qz35 179729363025 1125899906842624 29677375 1125899906842624 423945 33554432 35 33554432 

noncomputable def Ns408p327 := @Enclosure.Real.IsNear.mulLit_ff qz35 qz35 423945 33554432 35 33554432 423945 33554432 35 33554432 179729363025 1125899906842624 

noncomputable def Ns408p328 := nat_lit 30955981922477251112554696323575479137630948862511041 

noncomputable def Ns408p329 := nat_lit 15085502980398593449464978548510856026246963233994833920 

noncomputable def Ns408p330 := nat_lit 907414829246615903325156237777471719447080781761 

noncomputable def Ns408p331 := nat_lit 92866130937773260105857438658250882469453952425969601 

noncomputable def Ns408p332 := nat_lit 678847634117936705225924034682988521181113345529767526400 

noncomputable def Ns408p333 := BSN.cos_dyadic_bound_f 987929 2097152 3 2 16777216 6250000 Ns408p328 Ns408p329 Ns408p330 Ns408p331 Ns408p332 Ns408p330 14949809 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 987929) (BSN.cosEvenQ 2097152) 0 2 Ns408p328 Ns408p329 Ns408p330 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 987929) (BSN.cosOddQ 2097152) 0 2 Ns408p331 Ns408p332 Ns408p330 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p334 := @Ns408p317 1452304432 209715200000000 14949809 16777216 90769027 13107200000000 (@Ns408p318 227 33554432 Bool.false 14949809 16777216 1 6250000 (@Ns408p322 Ns408p323 987929 2097152 227 33554432 (@Ns408p324 1125899906842624 1204082495 1125899906842624 Ns408p319 Ns408p320 Ns408p321 Ns408p323 RS409to420.d47 (@Ns408p325 0 1 1350627975822064 84414248488879 1125899906842624 1204082495 1125899906842624 (@Ns408p326 471288919316370554880 14045504311215 1125899906842624 1204082495 1125899906842624 (@Ns408p327 29677375 1125899906842624 (Ns408p311 rfl rfl) (Ns408p311 rfl rfl) rfl) (Ns408p311 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 987929 2097152) (BSN.cos_neg_of_bound 987929 2097152 Bool.false 14949809 16777216 1 6250000 (Ns408p333 rfl rfl)) rfl rfl) 

noncomputable abbrev qz51 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 11) (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1))

noncomputable def Ns408p335 := @Ns408p296 45478155065502554889 Ns408p205 (Ns408p297 qz51 (@Enclosure.Real.IsNear.of_eq qz34 (@Inv.inv Real Real.instInv (Real.sqrt qz43)) Bool.false 10111237 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz42 (BSN.t_div_two_pi_nonneg qz32 762013 1000 qz36)) Ns408p301) rfl) (@Ns408p302 281474976710656 571828099219309 43980465111040000000 (BSN.correction_mk qz35 (BSN.cos_two_pi_p_ne_zero_mk qz32 762013 1000 11 qz36 rfl rfl (@BSN.floor_sqrt_eq_dec qz32 762013 1000 11 qz36 rfl rfl rfl))) (@Ns408p303 8388608 14949809 16777216 90769027 13107200000000 251608589377789 281474976710656 571828099219309 43980465111040000000 (@Ns408p304 8388608 (Ns408p316 rfl rfl rfl rfl rfl) rfl) (Ns408p334 rfl) rfl)) 

noncomputable def Ns408p336 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz32) (hardyZApproximantRS₀ qz32) Bool.false 48302364134301611608561 9444732965739290427392 13533049854040222554889 Ns408p205 (@Eq.refl Real (hardyZApproximantRS₀ qz32)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz32) (@HSub.hSub Real Real Real qz30 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz32) qz32 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz34) (Zeta.RiemannSiegel.correction qz35))) Bool.false 48302364134301611608561 9444732965739290427392 13533049854040222554889 Ns408p205 (BSN.hardyZApproximantRS₀_eq qz32 11 (@BSN.floor_sqrt_eq_dec qz32 762013 1000 11 qz36 rfl rfl rfl)) (@Ns408p207 48302364134301611608561 9444732965739290427392 13533049854040222554889 Ns408p205 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz32) qz32 11) (@HAdd.hAdd Real Real Real qz368 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz32) qz32 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz32) qz32 11)) Bool.false 162566103 33554432 19627 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz32) qz32 11) (Ns408p295 (Ns408p294 rfl) rfl rfl)) (Ns408p335 rfl) rfl rfl)) 

theorem RS409to420.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz32) Bool.false 48302364134301611608561 9444732965739290427392 13533049854040222554889 Ns408p205 := Ns408p336 

noncomputable abbrev qz609 := (@HMul.hMul Real Real Real qz714 (Real.sqrt qz722) qz716)

noncomputable abbrev qz401 := qz609

noncomputable abbrev qz52 := (@Inv.inv Real Real.instInv qz401)

noncomputable abbrev qz402 := (@HMul.hMul Real Real Real qz579 (@HMul.hMul Real Real Real qz579 qz609 qz609) qz609)

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz350 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz402))

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz579 qz596 qz596)

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz350 qz403 qz375))

noncomputable abbrev qz610 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 25 4) qz52)

noncomputable def Ns408p337 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (@HAdd.hAdd Real Real Real qz368 (@HAdd.hAdd Real Real Real qz368 qz610 qz53) (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 13 10) qz54)) Bool.false 

noncomputable def Ns408p338 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz368 qz610 qz53) (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 13 10) qz54) 16728201 1073741824 

noncomputable def Ns408p339 := @Enclosure.Real.IsNear.addLit_ff qz610 qz53 2091025 134217728 25 134217728 

noncomputable def Ns408p340 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz52 25 4 0 1 83641 33554432 1 33554432 2091025 

noncomputable def Ns408p341 := @Enclosure.Real.IsNear.recentre' qz52 Bool.false 83641 33554432 1 33554432 83641 33554432 1 33554432 

noncomputable def Ns408p342 := @Enclosure.Real.IsNear.mulLit_ff qz21 qz18 27819875 8388608 3 16777216 253682788559 2097152000 47503 2097152000 56459387738902481 140737488355328 851025888109 

noncomputable def Ns408p343 := @Enclosure.Real.IsNear.sqrt_image qz18 253682788559 2097152000 47503 2097152000 184522955 184522991 16777216 qz19 

noncomputable def Ns408p344 := @Enclosure.Real.IsNear.sqrt_image qz20 184522973 16777216 9 8388608 55639747 55639753 16777216 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 369045946 33554432 36 33554432 184522973 16777216 9 8388608 (Ns408p343 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz404 := (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 111279500 33554432 6 33554432 27819875 8388608 3 16777216 (Ns408p344 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns408p345 := @Ns408p342 8796093022208000 qz404 

noncomputable def Ns408p346 := Ns408p345 qz19 

noncomputable abbrev qz55 := qz401

noncomputable def Ns408p347 := @Enclosure.Real.IsNear.inv_image qz55 56459387738902481 140737488355328 851025888109 8796093022208000 41820 41821 16777216 (Ns408p346 rfl) rfl rfl 

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv qz402)

noncomputable def Ns408p348 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz56 1 32 0 1 1 

noncomputable def Ns408p349 := @Enclosure.Real.IsNear.recentre' qz56 Bool.false 1 33554432 1 33554432 

noncomputable def Ns408p350 := nat_lit 179973471027350139788895258183663597517755000150641 

noncomputable def Ns408p351 := nat_lit 2787593149816327892691964784081045188247552 

noncomputable def Ns408p352 := nat_lit 127161746884599391353244355529869210592571594296241 

noncomputable def Ns408p353 := nat_lit 2722258935367507707706996859454145691648000000000 

noncomputable abbrev qz57 := qz402

noncomputable def Ns408p354 := @Enclosure.Real.IsNear.inv_image qz57 Ns408p350 Ns408p351 Ns408p352 Ns408p353 0 1 

noncomputable def Ns408p355 := nat_lit 3187662463851731806055170427955361 

noncomputable def Ns408p356 := nat_lit 19807040628566084398385987584 

noncomputable def Ns408p357 := nat_lit 3003025399159397947229124949753 

noncomputable def Ns408p358 := nat_lit 38685626227668133590597632000000 

noncomputable abbrev qz405 := (@HMul.hMul Real Real Real qz579 qz609 qz609)

noncomputable abbrev qz58 := qz405

noncomputable def Ns408p359 := @Enclosure.Real.IsNear.mulLit_ff qz58 qz55 Ns408p355 Ns408p356 Ns408p357 Ns408p358 56459387738902481 140737488355328 851025888109 

noncomputable def Ns408p360 := @Enclosure.Real.IsNear.mulLit_ff qz55 qz55 56459387738902481 140737488355328 851025888109 8796093022208000 56459387738902481 140737488355328 851025888109 8796093022208000 Ns408p355 

noncomputable def Ns408p361 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz54 13 10 0 1 919929 33554432 1 

noncomputable def Ns408p362 := @Enclosure.Real.IsNear.recentre' qz54 Bool.false 919929 33554432 1 33554432 919929 33554432 

noncomputable abbrev qz59 := qz403

noncomputable def Ns408p363 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz21 773945445015625 70368744177664 333838509 281474976710656 27819875 8388608 3 16777216 21531065537154060546875 

noncomputable def Ns408p364 := @Enclosure.Real.IsNear.mulLit_ff qz21 qz21 27819875 8388608 3 16777216 27819875 8388608 3 16777216 773945445015625 70368744177664 333838509 

noncomputable def Ns408p365 := @Ns408p364 281474976710656 qz404 

noncomputable def Ns408p366 := Ns408p365 qz404 

noncomputable def Ns408p367 := @Ns408p363 590295810358705651712 27862037522835777 4722366482869645213696 (Ns408p366 rfl) qz404 

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz350 qz403 qz375)

noncomputable def Ns408p368 := @Enclosure.Real.IsNear.inv_image qz60 21531065537154060546875 590295810358705651712 27862037522835777 4722366482869645213696 459964 459965 16777216 (Ns408p367 rfl) 

noncomputable def Ns408p369 := @Ns408p338 201 1073741824 11959077 335544320 13 335544320 18454013980704768 274986237 5368709120 1213 5368709120 (@Ns408p339 1 1073741824 1 1073741824 2245221131747328 16728201 1073741824 201 1073741824 (@Ns408p340 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns408p341 (Ns408p347 rfl rfl rfl rfl) rfl) rfl) (@Ns408p348 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns408p349 1 33554432 1 33554432 (@Ns408p354 16777216 (@Ns408p359 8796093022208000 Ns408p350 Ns408p351 Ns408p352 Ns408p353 (@Ns408p360 Ns408p356 Ns408p357 Ns408p358 (Ns408p346 rfl) (Ns408p346 rfl) rfl) (Ns408p346 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns408p361 33554432 11959077 335544320 13 335544320 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns408p362 1 33554432 (Ns408p368 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS409to420.d56 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 := @Ns408p337 274986237 5368709120 1213 5368709120 (BSN.hardyZErrorBoundRS₀_mk qz3 760048 1000 qz8 rfl rfl) (Ns408p369 rfl rfl) 

noncomputable def Ns408p370 := nat_lit 1734808542421610187022761 

noncomputable def Ns408p371 := nat_lit 1475739525896764129280000000 

noncomputable def Ns408p372 := nat_lit 2018886542411224248653373767680 

noncomputable abbrev qz728 := (Enclosure.sfrac Bool.false 763159 1000)

noncomputable abbrev qz611 := qz728

noncomputable abbrev qz406 := qz611

noncomputable abbrev qz61 := qz406

noncomputable abbrev qz729 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 763159 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz612 := qz729

noncomputable abbrev qz407 := qz612

noncomputable abbrev qz62 := (@HPow.hPow Real Real Real qz351 qz407 qz353)

noncomputable abbrev qz730 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 763159 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz613 := qz730

noncomputable abbrev qz408 := qz613

noncomputable abbrev qz63 := qz408

noncomputable def Ns408p373 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz62) (Zeta.RiemannSiegel.correction qz63)) 142242407 134217728 157249 134217728 4976962198516623385811 18889465931478580854784 5837502860127947022761 Ns408p371 Ns408p372 

noncomputable def Ns408p374 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 763159 1000 195 242 268435456 134217728 4503599627370496 Bool.false 389084503412 2563 

noncomputable def Ns408p375 := Ns408p374 618095470 44 84886744 8 643680110 44 80936328 8 Bool.true 151922088 134903 Bool.true 397418865 Bool.true 104668015 14148475504056880 1 Bool.false 267341880 Bool.false Bool.false 248286677 Bool.true Bool.true 142242407 

noncomputable def Ns408p376 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 763159 1000 87 144 268435456 134217728 4503599627370496 Bool.false 389084503412 2563 

noncomputable def Ns408p377 := Ns408p376 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 255846634 110058 Bool.true 223477861 Bool.true 317906342 14148475504056880 1 Bool.false 198542822 Bool.false Bool.false 101187177 Bool.false Bool.true 151922088 

noncomputable def Ns408p378 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 763159 1000 52 22 268435456 134217728 4503599627370496 Bool.false 389084503412 2563 

noncomputable def Ns408p379 := Ns408p378 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 305501116 81623 Bool.false 100391278 Bool.true 276099922 14148475504056880 1 Bool.false 249880742 Bool.false Bool.false 138528630 Bool.true Bool.true 255846634 

noncomputable def Ns408p380 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 763159 1000 249 140 268435456 134217728 4503599627370496 Bool.false 389084503412 2563 

noncomputable def Ns408p381 := Ns408p380 372130544 43 134217720 8 432030192 43 120047984 16 Bool.true 291967972 48083 Bool.false 97029945 Bool.false 344734158 14148475504056880 1 Bool.false 94930769 Bool.true Bool.false 75874793 Bool.false Bool.true 305501116 

noncomputable def Ns408p382 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 763159 1000 585 388 268435456 134217728 4503599627370496 Bool.false 389084503412 2563 

noncomputable def Ns408p383 := Ns408p382 186065264 43 189812528 16 294906480 43 154981288 8 Bool.true 102622792 2611 Bool.false 417527067 Bool.false 420886874 14148475504056880 1 Bool.false 268403680 Bool.true Bool.false 770553 Bool.false Bool.true 291967972 

noncomputable def Ns408p384 := nat_lit 46425551491326798519905024023579667399842073072251759182697 

noncomputable def Ns408p385 := nat_lit 32029710706333399427522144612389301504446026372612096000 

noncomputable def Ns408p386 := nat_lit 124255854677589615200854921503520000 

noncomputable def Ns408p387 := nat_lit 568961956772067612809034369057124918080 

noncomputable abbrev qz614 := (@Eq.refl Real qz728)

noncomputable abbrev qz409 := qz614

noncomputable abbrev qz64 := qz409

noncomputable def Ns408p388 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz61 763159 1000 2329647637124 16000000 1526318 4000 2000 Ns408p386 Ns408p387 qz64 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns408p389 := nat_lit 14856176477224575526369607687545493567949463383120562938463040 

noncomputable abbrev qz615 := (@HSub.hSub Real Real Real qz718 qz719 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz720 (@Nat.cast Real Real.instNatCast 1526318))))

noncomputable abbrev qz410 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 763159 4000) (Real.log (Enclosure.sfrac Bool.false 2329647637124 16000000))) (@HMul.hMul Real Real Real qz579 qz585 qz615))

noncomputable abbrev qz616 := (Enclosure.sfrac Bool.false 763159 2000)

noncomputable abbrev qz65 := (@HSub.hSub Real Real Real qz356 (@HSub.hSub Real Real Real qz356 qz410 qz616) (@HMul.hMul Real Real Real qz350 qz616 (Real.log Real.pi)))

noncomputable def Ns408p390 := @Enclosure.Real.IsNear.addLit_ft_p qz65 (Enclosure.sfrac Bool.true Ns408p386 Ns408p387) 26111022958202118634113 18014398509481984000 39083114009880747 4096000000000000000000 Ns408p386 Ns408p387 0 1 Ns408p389 

noncomputable def Ns408p391 := nat_lit 1752281088602863663928555077632000 

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz356 qz410 qz616)

noncomputable def Ns408p392 := @Enclosure.Real.IsNear.subLit_ff_p qz66 (@HMul.hMul Real Real Real qz4 qz616 (Real.log Real.pi)) 33979810517148027222657 18014398509481984000 15423192974203 4000000000000000000 29313517953999 67108864000 763159 134217728000 Ns408p391 26111022958202118634113 18014398509481984000 

noncomputable def Ns408p393 := nat_lit 13591924206859210889062800 

noncomputable abbrev qz67 := qz410

noncomputable def Ns408p394 := @Enclosure.Real.IsNear.subLit_ff_p qz67 qz616 8170747138639381587277 3602879701896396800 15423192974203 4000000000000000000 763159 2000 0 1 Ns408p393 33979810517148027222657 18014398509481984000 15423192974203 4000000000000000000 

noncomputable def Ns408p395 := nat_lit 18398886884457432667924350733119389696 

noncomputable def Ns408p396 := nat_lit 57489929906394815120015360 

noncomputable def Ns408p397 := nat_lit 5760374534035372345823692076260204116022402235600640 

noncomputable def Ns408p398 := nat_lit 5305148185522116717879675357005608988446546987008 

noncomputable def Ns408p399 := nat_lit 8765576515111244429001670426083897116095120128 

noncomputable def Ns408p400 := BSN.log_dyadic_bound 232495637124 4426799637124 3 2 Ns408p397 134217728 50000000 Ns408p398 Ns408p399 14111221 4659295274248 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 232495637124) (BSN.artanhQ 4426799637124) 0 2 Ns408p398 Ns408p397 Ns408p399 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz411 := (Real.log (Enclosure.sfrac Bool.false 2329647637124 16000000))

noncomputable def Ns408p401 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 763159 4000) qz411 763159 4000 0 1 53541669534887015 4503599627370496 20000017 1000000000000000 8172161396114967896077 3602879701896396800 15263192973703 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 763159 4000) (BSN.isNear_log_sfrac 2329647637124 16000000 53541669534887015 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2329647637124) qz359)) Bool.false Ns408p396 Ns408p100 1000000850000000 50000000000000000000000 53541669534887015 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2329647637124 16000000 17 4659295274248 4194304000000 14111221 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns408p400 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns408p402 := BSN.arctan_dyadic_bound_f 1000 1526318 1 0 16777216 6250000 0 1 1 0 1 1 10991 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1526318) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1526318) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz412 := (@Nat.cast Real Real.instNatCast 1526318)

noncomputable def Ns408p403 := @Enclosure.Real.IsNear.subLit_ff_p qz12 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz13 qz412)) 884279719003555 562949953421312 1 2000000000000000 10991 16777216 1 6250000 14829564467203893362688 883910922241443 562949953421312 320000001 2000000000000000 qz14 (Ns408p402 rfl) rfl rfl 

noncomputable abbrev qz413 := (@HMul.hMul Real Real Real qz579 qz585 qz615)

noncomputable abbrev qz68 := qz413

noncomputable abbrev qz414 := qz615

noncomputable abbrev qz69 := qz414

noncomputable def Ns408p404 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 763159 4000) qz411) qz68 8172161396114967896077 3602879701896396800 15263192973703 4000000000000000000 883910922241443 2251799813685248 320000001 8000000000000000 Ns408p395 8170747138639381587277 3602879701896396800 15423192974203 4000000000000000000 (Ns408p401 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz16 qz69 1 4 0 1 883910922241443 562949953421312 320000001 2000000000000000 883910922241443 2251799813685248 320000001 8000000000000000 qz367 Ns408p403 rfl) 

noncomputable def Ns408p405 := @Ns408p390 Ns408p384 Ns408p385 39083114009880747 4096000000000000000000 (@Ns408p392 39083114009880747 4096000000000000000000 (Ns408p394 (Ns408p404 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 763159 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz616 (Real.log Real.pi) 763159 2000 0 1 38410761 33554432 1 67108864 29313517953999 67108864000 763159 134217728000 (Enclosure.Real.IsNear.const Bool.false 763159 2000) RS409to420.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns408p386 Ns408p387) 

noncomputable def Ns408p406 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz61) Bool.false Ns408p384 Ns408p385 39083114009880747 4096000000000000000000 24317781463 16777216 321 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz61) (@HAdd.hAdd Real Real Real qz368 qz65 (Enclosure.sfrac Bool.true Ns408p386 Ns408p387)) Bool.false Ns408p384 Ns408p385 39083114009880747 4096000000000000000000 Ns408p388 (Ns408p405 rfl rfl)) 

noncomputable def Ns408p407 := nat_lit 2849468435102526997528576 

noncomputable def Ns408p408 := nat_lit 1613552950922397413633036986183235988994714957982149369505948015119952005003772220844810081 

noncomputable def Ns408p409 := nat_lit 20052072892042597411705012245279816272850392000149059967199507548332190919545345701492817920 

noncomputable def Ns408p410 := nat_lit 1850599176460206757094605315943270064395811010997565165516641652263345856588169909903201 

noncomputable def Ns408p411 := nat_lit 4836957654414271827384921747917821426855353251924452978186810762055329323298140322714623841 

noncomputable def Ns408p412 := nat_lit 902343280141916883526725551037591732278267640006707698523977839674948591379540556567176806400 

noncomputable def Ns408p413 := BSN.cos_dyadic_bound_f 80986763893 68719476736 3 2 33554432 12512208 Ns408p408 Ns408p409 Ns408p410 Ns408p411 Ns408p412 Ns408p410 12827849 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 80986763893) (BSN.cosEvenQ 68719476736) 0 2 Ns408p408 Ns408p409 Ns408p410 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 80986763893) (BSN.cosOddQ 68719476736) 0 2 Ns408p411 Ns408p412 Ns408p410 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p414 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz61) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24317781463) qz369) Bool.false 24317781463 16777216 321 33554432 Bool.true 12827849 33554432 1 6250000 (Ns408p406 rfl) (Enclosure.sfrac_false_div 24317781463 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24317781463) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns408p407) qz593) 226375608064910080 72057594037927936 Bool.false 12827849 33554432 230 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q2 24317781463 16777216 226375608064910080 72057594037927936 230 Ns408p407 Ns408p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 12827849 33554432 Ns408p407 Ns408p112 80986763893 68719476736 12512208 12500000 (Ns408p413 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns408p415 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz61) Bool.false Ns408p384 Ns408p385 39083114009880747 4096000000000000000000 389084503412 268435456 2563 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz61) (@HAdd.hAdd Real Real Real qz368 qz65 (Enclosure.sfrac Bool.true Ns408p386 Ns408p387)) Bool.false Ns408p384 Ns408p385 39083114009880747 4096000000000000000000 Ns408p388 (Ns408p405 rfl rfl)) 

noncomputable def Ns408p416 := Ns408p383 48083 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 585 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268403680 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 388 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 770553 268435456) qz64 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 1) Bool.true 12827849 33554432 127487777 13107200000000 102622792 268435456 2611 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz61)) Bool.true 12827849 33554432 127487777 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz61) qz61) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz61)) Bool.true 12827849 33554432 2039804432 209715200000000 12827849 33554432 127487777 13107200000000 (Ns408p414 rfl rfl) rfl)) rfl) (Ns408p415 rfl) RS409to420.d7 

noncomputable def Ns408p417 := nat_lit 42598734398502761445375812321074552237061032516249161541928152259665660104640927491972865670528307845743524561 

noncomputable def Ns408p418 := nat_lit 28068268126880664182053638832260080191180365767933881485463444808972836643803796574851721452463408036561 

noncomputable def Ns408p419 := nat_lit 212739204820037839623759715069886537157490892993951235397295971454705113674956851395487373687826555278604647121 

noncomputable def Ns408p420 := BSN.sin_dyadic_bound_f 417527067 268435456 4 3 268435456 134217728 Ns408p417 Ns408p269 Ns408p418 Ns408p419 Ns408p272 Ns408p418 268403680 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 417527067) qz372 0 3 Ns408p417 Ns408p269 Ns408p418 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 417527067) qz373 0 3 Ns408p419 Ns408p272 Ns408p418 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p421 := nat_lit 16945976984221092331250949055904203272444194685978634954341672077315466855472044036183003644125405049810784256 

noncomputable def Ns408p422 := nat_lit 30901857241624418558245941455717394051299794360608335307011664418094109234494860906712102926444813029376 

noncomputable def Ns408p423 := nat_lit 102559763877698552415174211745187292976490692568068193996606683178479619898763257383377880978452243300232663040 

noncomputable def Ns408p424 := BSN.cos_dyadic_bound_f 420886874 268435456 4 3 268435456 134217728 Ns408p421 Ns408p252 Ns408p422 Ns408p423 Ns408p255 Ns408p422 770553 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 420886874) qz370 0 3 Ns408p421 Ns408p252 Ns408p422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 420886874) qz371 0 3 Ns408p423 Ns408p255 Ns408p422 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p425 := nat_lit 88638651604831864994761544150625 

noncomputable def Ns408p426 := BSN.sin_dyadic_bound_f 97029945 268435456 2 1 268435456 134217728 Ns408p425 Ns408p133 Ns408p425 Ns408p425 Ns408p134 Ns408p425 94930769 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 97029945) qz372 0 1 Ns408p425 Ns408p133 Ns408p425 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 97029945) qz373 0 1 Ns408p425 Ns408p134 Ns408p425 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p427 := nat_lit 7611754480043217033394179176724281738774651983240736043605511987540431711158839157138608669616247202733756416 

noncomputable def Ns408p428 := nat_lit 2817161934334405581657969308959828113797368011650830326199626296706609778446202041856133617526773518336 

noncomputable def Ns408p429 := nat_lit 46128199582639043089667367185373772518251888543971991194713063780285402747148943921829386869396392741730652160 

noncomputable def Ns408p430 := BSN.cos_dyadic_bound_f 344734158 268435456 4 3 268435456 134217728 Ns408p427 Ns408p252 Ns408p428 Ns408p429 Ns408p255 Ns408p428 75874793 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 344734158) qz370 0 3 Ns408p427 Ns408p252 Ns408p428 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 344734158) qz371 0 3 Ns408p429 Ns408p255 Ns408p428 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p431 := Ns408p381 81623 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 249 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 94930769 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 75874793 268435456) qz64 rfl rfl (Ns408p416 RS409to420.d9 RS409to420.d11 RS409to420.d13 RS409to420.d17 (Ns408p420 rfl rfl) (Ns408p424 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns408p415 rfl) RS409to420.d19 RS409to420.d21 RS409to420.d23 RS409to420.d25 RS409to420.d17 (Ns408p426 rfl rfl) (Ns408p430 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns408p432 := nat_lit 886049091901250938407410094105175581837992059501380019055190700278016 

noncomputable def Ns408p433 := nat_lit 10317342868116624506936041850511569405812581684512841791344558336 

noncomputable def Ns408p434 := nat_lit 2658126641018016581973216410231825722375164553340771031481989411717376 

noncomputable def Ns408p435 := BSN.cos_dyadic_bound_f 100391278 268435456 3 2 268435456 134217728 Ns408p432 Ns408p123 Ns408p433 Ns408p434 Ns408p126 Ns408p433 249880742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 100391278) qz370 0 2 Ns408p432 Ns408p123 Ns408p433 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 100391278) qz371 0 2 Ns408p434 Ns408p126 Ns408p433 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p436 := nat_lit 3128953717656960409847753074747289846567422337674075421075988867795493124658336379516604279571518704513847296 

noncomputable def Ns408p437 := nat_lit 196243557150557838944171258709917780986693715475284840579558292039700068074265708465187955216486895616 

noncomputable def Ns408p438 := nat_lit 18973893319437036844347093734220902121217522184382909772667944524433116616556966887187174465076201490961797120 

noncomputable def Ns408p439 := BSN.cos_dyadic_bound_f 276099922 268435456 4 3 268435456 134217728 Ns408p436 Ns408p252 Ns408p437 Ns408p438 Ns408p255 Ns408p437 138528630 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 276099922) qz370 0 3 Ns408p436 Ns408p252 Ns408p437 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 276099922) qz371 0 3 Ns408p438 Ns408p255 Ns408p437 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p440 := Ns408p379 110058 BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 249880742 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 138528630 268435456) qz64 rfl rfl (Ns408p431 rfl rfl) (Ns408p415 rfl) RS409to420.d27 RS409to420.d29 RS409to420.d31 RS409to420.d33 RS409to420.d17 (Ns408p435 rfl rfl) (Ns408p439 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p441 := nat_lit 39169525314925357622860048956425313834021585372643731637922678391762145 

noncomputable def Ns408p442 := nat_lit 6221226985569295735316136230672282067049677927069374522579002387681 

noncomputable def Ns408p443 := nat_lit 102576779552542157771538187808169019203852738402184994350094267879320801 

noncomputable def Ns408p444 := BSN.sin_dyadic_bound_f 223477861 268435456 3 2 268435456 134217728 Ns408p441 Ns408p142 Ns408p442 Ns408p443 Ns408p145 Ns408p442 198542822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 223477861) qz372 0 2 Ns408p441 Ns408p142 Ns408p442 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 223477861) qz373 0 2 Ns408p443 Ns408p145 Ns408p442 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p445 := nat_lit 5502370500482307069558426343602177821649269591381892369553990682481066342788907667960014552712903421001404416 

noncomputable def Ns408p446 := nat_lit 1065590407537881826511319146993480475819629917678292513555543086869015630134447837970266754870785806336 

noncomputable def Ns408p447 := nat_lit 33355015049112248819471142968616856676801465105924966466160083604714104372174137041513524738559832516598108160 

noncomputable def Ns408p448 := BSN.cos_dyadic_bound_f 317906342 268435456 4 3 268435456 134217728 Ns408p445 Ns408p252 Ns408p446 Ns408p447 Ns408p255 Ns408p446 101187177 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 317906342) qz370 0 3 Ns408p445 Ns408p252 Ns408p446 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 317906342) qz371 0 3 Ns408p447 Ns408p255 Ns408p446 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p449 := Ns408p377 134903 BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 198542822 268435456) BSN.abs_quadSignPos qz606 (BSN.sfrac_eq_quadSignPos_mul Bool.false 101187177 268435456) qz64 rfl rfl (Ns408p440 rfl) (Ns408p415 rfl) RS409to420.d35 RS409to420.d37 RS409to420.d39 RS409to420.d41 RS409to420.d17 (Ns408p444 rfl rfl) (Ns408p448 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p450 := nat_lit 34954382948810259560109221341279710157160207528859979581753953309581029479571580787901476232821793320592290625 

noncomputable def Ns408p451 := nat_lit 15523217568309466857275559525191352025447175598400346105392301345286480566091015796466939362871337890625 

noncomputable def Ns408p452 := nat_lit 174600476312830659627477791523648239743764966488517717636668644464428368037985649748049146554570404333609890625 

noncomputable def Ns408p453 := BSN.sin_dyadic_bound_f 397418865 268435456 4 3 268435456 134217728 Ns408p450 Ns408p269 Ns408p451 Ns408p452 Ns408p272 Ns408p451 267341880 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 397418865) qz372 0 3 Ns408p450 Ns408p269 Ns408p451 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 397418865) qz373 0 3 Ns408p452 Ns408p272 Ns408p451 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p454 := nat_lit 1046961528373752036919859201316489775314979045215545897288259267690625 

noncomputable def Ns408p455 := nat_lit 14404954928770445798515837591014284381997426586613435075062890625 

noncomputable def Ns408p456 := nat_lit 3140855775211398569867980572274287297376173140793464464994627677290625 

noncomputable def Ns408p457 := BSN.cos_dyadic_bound_f 104668015 268435456 3 2 268435456 134217728 Ns408p454 Ns408p123 Ns408p455 Ns408p456 Ns408p126 Ns408p455 248286677 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 104668015) qz370 0 2 Ns408p454 Ns408p123 Ns408p455 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 104668015) qz371 0 2 Ns408p456 Ns408p126 Ns408p455 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz415 := (BSN.cos_quad_nat3 195 rfl)

noncomputable def Ns408p458 := Ns408p375 157249 BSN.abs_quadSignPos qz415 (BSN.sfrac_eq_quadSignPos_mul Bool.false 267341880 268435456) BSN.abs_quadSignNeg qz395 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 248286677 268435456) qz64 rfl rfl (Ns408p449 rfl) (Ns408p415 rfl) RS409to420.d43 RS409to420.d45 RS409to420.d52 RS409to420.d54 RS409to420.d17 (Ns408p453 rfl rfl) (Ns408p457 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p459 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 11) 142242407 268435456 157249 268435456 142242407 268435456 157249 268435456 76365810771165184 142242407 134217728 157249 134217728 (Ns408p458 rfl) 

noncomputable def Ns408p460 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz4 qz33 qz62) (Zeta.RiemannSiegel.correction qz63) 10107439 33554432 1 33554432 492405860526749 562949953421312 2868695561029447 219902325555200000000 4976962198516623385811 18889465931478580854784 

noncomputable def Ns408p461 := @Enclosure.Real.IsNear.mulLit_tf qz33 qz62 1 1 0 1 10107439 33554432 1 33554432 10107439 33554432 1 33554432 

noncomputable abbrev qz70 := qz407

noncomputable def Ns408p462 := @Enclosure.Real.IsNear.sqrt_image qz70 4075538455127 33554432000 763159 33554432000 184900211 184900246 16777216 (@Enclosure.Real.IsNear.of_eq qz70 (@HMul.hMul Real Real Real qz4 qz61 qz2) Bool.false 4075538455127 33554432000 763159 33554432000 (BSN.t_div_two_pi_mk qz61 763159 1000 qz64) (@Enclosure.Real.IsNear.mulLit_ff qz61 qz2 763159 1000 0 1 5340353 33554432 1 33554432 4075538455127 33554432000 763159 33554432000 (Enclosure.Real.IsNear.const Bool.false 763159 1000) RS409to420.d48 rfl)) 

noncomputable abbrev qz731 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 763159 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz617 := qz731

noncomputable abbrev qz416 := qz617

noncomputable abbrev qz71 := qz416

noncomputable def Ns408p463 := @Enclosure.Real.IsNear.sqrt_image qz71 369800457 33554432 35 33554432 55696595 55696602 16777216 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 369800457 33554432 35 33554432 369800457 33554432 35 33554432 (Ns408p462 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns408p464 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz71) 111393197 33554432 7 33554432 5053719 5053720 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz71) Bool.false 111393197 33554432 7 33554432 111393197 33554432 7 33554432 (Ns408p463 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns408p465 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 10107439 33554432 1 33554432 10107439 33554432 1 33554432 (Ns408p464 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz72 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz408))

noncomputable abbrev qz618 := (@HMul.hMul Real Real Real qz714 qz730 qz730)

noncomputable abbrev qz417 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz618 qz613) qz598)

noncomputable abbrev qz73 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz417))

noncomputable def Ns408p466 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz63) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv qz72) qz73) Bool.false 492405860526749 

noncomputable def Ns408p467 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz72) qz73 33846191 33554432 231 

noncomputable def Ns408p468 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz72) Bool.false 33846191 33554432 231 33554432 33846191 33554432 231 

noncomputable def Ns408p469 := @Enclosure.Real.IsNear.recentre' qz72 Bool.false 16632594 16777216 1414804432 209715200000000 8316297 8388608 88425277 13107200000000 

noncomputable abbrev qz74 := (@HMul.hMul Real Real Real qz350 qz347 qz408)

noncomputable def Ns408p470 := @Enclosure.Real.IsNear.cos_image qz74 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2204471) qz369) Bool.false 2204471 16777216 221 33554432 Bool.false 16632594 16777216 1 

noncomputable def Ns408p471 := nat_lit 188902527864513838196758641 

noncomputable def Ns408p472 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz63 884279719003555 140737488355328 1 500000000000000 701705 33554432 35 33554432 620503500223389561275 4722366482869645213696 Ns408p471 

noncomputable def Ns408p473 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz31 369800457 33554432 35 33554432 11 1 0 1 701705 701705 33554432 35 

noncomputable def Ns408p474 := @Ns408p473 33554432 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 369800457 33554432 35 33554432 369800457 33554432 35 33554432 (Ns408p462 rfl rfl rfl rfl rfl rfl) rfl) qz398 

noncomputable def Ns408p475 := @Enclosure.Real.IsNear.recentre' qz74 Bool.false 620503500223389561275 4722366482869645213696 Ns408p471 Ns408p308 2204471 16777216 221 33554432 (@Ns408p472 Ns408p308 RS409to420.d47 (Ns408p474 rfl rfl) rfl) 

noncomputable def Ns408p476 := nat_lit 23616610123878529920005281 

noncomputable def Ns408p477 := BSN.cos_dyadic_bound_f 2204471 16777216 2 1 16777216 6250000 Ns408p476 Ns408p196 Ns408p476 Ns408p476 Ns408p197 Ns408p476 16632594 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 2204471) (BSN.cosEvenQ 16777216) 0 1 Ns408p476 Ns408p196 Ns408p476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 2204471) (BSN.cosOddQ 16777216) 0 1 Ns408p476 Ns408p197 Ns408p476 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p478 := @Enclosure.Real.IsNear.inv_image qz72 8316297 8388608 88425277 13107200000000 16922980 16923211 16777216 (Ns408p469 (@Ns408p470 6250000 (Ns408p475 rfl) (Enclosure.sfrac_false_div 2204471 16777216) (Ns408p477 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns408p479 := @Enclosure.Real.IsNear.recentre' qz73 Bool.false 14548339 16777216 

noncomputable abbrev qz75 := (@HMul.hMul Real Real Real qz350 qz347 qz417)

noncomputable abbrev qz418 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable def Ns408p480 := @Enclosure.Real.IsNear.cos_image qz75 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 17493535)) qz418) Bool.true 17493535 33554432 

noncomputable def Ns408p481 := nat_lit 82610885423441225153184942445 

noncomputable def Ns408p482 := nat_lit 33018156670975511009956947456474873 

noncomputable def Ns408p483 := @Enclosure.Real.IsNear.recentre' qz75 Bool.true Ns408p481 Ns408p320 Ns408p482 

noncomputable abbrev qz76 := qz417

noncomputable def Ns408p484 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz76 884279719003555 140737488355328 1 500000000000000 93421666977199 

noncomputable abbrev qz419 := (@HSub.hSub Real Real Real qz584 qz618 qz613)

noncomputable abbrev qz77 := qz419

noncomputable def Ns408p485 := @Enclosure.Real.IsNear.subLit_tf qz77 qz28 23052922799535 1125899906842624 1223525695 1125899906842624 1 16 

noncomputable abbrev qz420 := qz618

noncomputable abbrev qz78 := qz420

noncomputable def Ns408p486 := @Enclosure.Real.IsNear.subLit_ff_n qz78 qz63 492389907025 1125899906842624 49120575 1125899906842624 701705 33554432 35 33554432 

noncomputable def Ns408p487 := @Enclosure.Real.IsNear.mulLit_ff qz63 qz63 701705 33554432 35 33554432 701705 33554432 35 33554432 492389907025 1125899906842624 

noncomputable def Ns408p488 := nat_lit 199451937118481496347905710315794831937720820886213881197690625 

noncomputable def Ns408p489 := nat_lit 64791741944522487909851911563195676133695224709322207119351480320 

noncomputable def Ns408p490 := nat_lit 8770424736907297550986073595465706828514133113905312890625 

noncomputable def Ns408p491 := nat_lit 598338270505970674448615158800193564399505434392413832967290625 

noncomputable def Ns408p492 := nat_lit 2915628387503511955943336020343805426016285111919499320370816614400 

noncomputable abbrev qz619 := (BSN.cosEvenQ 33554432)

noncomputable def Ns408p493 := BSN.cos_dyadic_bound_f 17493535 33554432 3 2 16777216 6250000 Ns408p488 Ns408p489 Ns408p490 Ns408p491 Ns408p492 Ns408p490 14548339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 17493535) qz619 0 2 Ns408p488 Ns408p489 Ns408p490 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 17493535) (BSN.cosOddQ 33554432) 0 2 Ns408p491 Ns408p492 Ns408p490 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p494 := @Ns408p479 735527216 104857600000000 14548339 16777216 45970451 6553600000000 (@Ns408p480 115 16777216 Bool.false 14548339 16777216 1 6250000 (@Ns408p483 Ns408p323 17493535 33554432 115 16777216 (@Ns408p484 1125899906842624 1223525695 1125899906842624 Ns408p481 Ns408p320 Ns408p482 Ns408p323 RS409to420.d47 (@Ns408p485 0 1 1494746671635184 93421666977199 1125899906842624 1223525695 1125899906842624 (@Ns408p486 773527730478246789120 23052922799535 1125899906842624 1223525695 1125899906842624 (@Ns408p487 49120575 1125899906842624 (Ns408p474 rfl rfl) (Ns408p474 rfl rfl) rfl) (Ns408p474 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 17493535 33554432) (BSN.cos_neg_of_bound 17493535 33554432 Bool.false 14548339 16777216 1 6250000 (Ns408p493 rfl rfl)) rfl rfl) 

noncomputable def Ns408p495 := @Ns408p460 5837502860127947022761 Ns408p371 (Ns408p461 qz51 (@Enclosure.Real.IsNear.of_eq qz62 (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 10107439 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz70 (BSN.t_div_two_pi_nonneg qz61 763159 1000 qz64)) Ns408p465) rfl) (@Ns408p466 562949953421312 2868695561029447 219902325555200000000 (BSN.correction_mk qz63 (BSN.cos_two_pi_p_ne_zero_mk qz61 763159 1000 11 qz64 rfl rfl (@BSN.floor_sqrt_eq_dec qz61 763159 1000 11 qz64 rfl rfl rfl))) (@Ns408p467 33554432 14548339 16777216 45970451 6553600000000 492405860526749 562949953421312 2868695561029447 219902325555200000000 (@Ns408p468 33554432 (Ns408p478 rfl rfl rfl rfl rfl) rfl) (Ns408p494 rfl) rfl)) 

noncomputable def Ns408p496 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz61) (hardyZApproximantRS₀ qz61) Bool.true 15041876900279702608685 18889465931478580854784 Ns408p370 Ns408p371 (@Eq.refl Real (hardyZApproximantRS₀ qz61)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz61) (@HSub.hSub Real Real Real qz30 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz62) (Zeta.RiemannSiegel.correction qz63))) Bool.true 15041876900279702608685 18889465931478580854784 Ns408p370 Ns408p371 (BSN.hardyZApproximantRS₀_eq qz61 11 (@BSN.floor_sqrt_eq_dec qz61 763159 1000 11 qz64 rfl rfl rfl)) (@Ns408p373 15041876900279702608685 18889465931478580854784 Ns408p370 Ns408p371 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 11) (@HAdd.hAdd Real Real Real qz368 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 11)) Bool.true 142242407 134217728 157249 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz61) qz61 11) (Ns408p459 (Ns408p458 rfl) rfl rfl)) (Ns408p495 rfl) rfl rfl)) 

theorem RS409to420.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz61) Bool.true 15041876900279702608685 18889465931478580854784 Ns408p370 Ns408p371 := Ns408p496 

noncomputable def Ns408p497 := nat_lit 46116860184273879040000000 

noncomputable def Ns408p498 := nat_lit 1856327035474460017025875968 

noncomputable abbrev qz732 := (Enclosure.sfrac Bool.false 763813 1000)

noncomputable abbrev qz620 := qz732

noncomputable abbrev qz421 := qz620

noncomputable abbrev qz79 := qz421

noncomputable abbrev qz733 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 763813 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz621 := qz733

noncomputable abbrev qz422 := qz621

noncomputable abbrev qz80 := (@HPow.hPow Real Real Real qz351 qz422 qz353)

noncomputable abbrev qz734 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 763813 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz622 := qz734

noncomputable abbrev qz423 := qz622

noncomputable abbrev qz81 := qz423

noncomputable def Ns408p499 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz79) qz79 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz80) (Zeta.RiemannSiegel.correction qz81)) 15396149 134217728 157375 134217728 9598652979933183925 36893488147419103232 189556768535100639429 Ns408p497 Ns408p498 

noncomputable def Ns408p500 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz79) qz79 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 763813 1000 195 242 268435456 134217728 4503599627370496 Bool.false 389505841258 2564 

noncomputable def Ns408p501 := Ns408p500 618095470 44 84886744 8 643680110 44 80936328 8 Bool.false 6417844 135011 Bool.true 380315457 Bool.true 104296960 14148475504056880 1 Bool.false 265258187 Bool.false Bool.false 248427483 Bool.true Bool.false 15396149 

noncomputable def Ns408p502 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz79) qz79 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 763813 1000 87 144 268435456 134217728 4503599627370496 Bool.false 389505841258 2564 

noncomputable def Ns408p503 := Ns408p502 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 93339435 110146 Bool.true 167200093 Bool.true 282306181 14148475504056880 1 Bool.false 156596571 Bool.false Bool.false 133176092 Bool.false Bool.false 6417844 

noncomputable def Ns408p504 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz79) qz79 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 763813 1000 52 22 268435456 134217728 4503599627370496 Bool.false 389505841258 2564 

noncomputable def Ns408p505 := Ns408p504 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 96379741 81687 Bool.false 207173594 Bool.true 196379802 14148475504056880 1 Bool.false 192379415 Bool.false Bool.false 199749618 Bool.true Bool.true 93339435 

noncomputable def Ns408p506 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz79) qz79 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 763813 1000 249 141 268435456 134217728 4503599627370496 Bool.false 389505841258 2564 

noncomputable def Ns408p507 := Ns408p506 372130544 43 134217720 8 432030192 43 120047984 16 Bool.false 45721996 48120 Bool.false 274994415 Bool.false 61866830 14148475504056880 1 Bool.false 229356691 Bool.true Bool.false 61320582 Bool.true Bool.true 96379741 

noncomputable def Ns408p508 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz79) qz79 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 763813 1000 586 389 268435456 134217728 4503599627370496 Bool.false 389505841258 2564 

noncomputable def Ns408p509 := Ns408p508 186065264 43 189812528 16 294906480 43 154981288 8 Bool.false 247922304 2611 Bool.false 295520802 Bool.false 227698454 14148475504056880 1 Bool.false 121545738 Bool.true Bool.false 201358683 Bool.true Bool.false 45721996 

noncomputable def Ns408p510 := nat_lit 46715306695189655273400799279786093001658502159457216958307 

noncomputable def Ns408p511 := nat_lit 32194753779297102142293858592282993828451222399483904000 

noncomputable def Ns408p512 := nat_lit 124789181890229412355580670540640000 

noncomputable def Ns408p513 := nat_lit 571893710686614691636966131800843161920 

noncomputable abbrev qz623 := (@Eq.refl Real qz732)

noncomputable abbrev qz424 := qz623

noncomputable abbrev qz82 := qz424

noncomputable def Ns408p514 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz79 763813 1000 2333642195876 16000000 1527626 4000 2000 Ns408p512 Ns408p513 qz82 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns408p515 := nat_lit 14948898142460689687488255769531549760530720691026309426658240 

noncomputable abbrev qz624 := (@HSub.hSub Real Real Real qz718 qz719 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz720 (@Nat.cast Real Real.instNatCast 1527626))))

noncomputable abbrev qz425 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 763813 4000) (Real.log (Enclosure.sfrac Bool.false 2333642195876 16000000))) (@HMul.hMul Real Real Real qz579 qz585 qz624))

noncomputable abbrev qz625 := (Enclosure.sfrac Bool.false 763813 2000)

noncomputable abbrev qz83 := (@HSub.hSub Real Real Real qz356 (@HSub.hSub Real Real Real qz356 qz425 qz625) (@HMul.hMul Real Real Real qz350 qz625 (Real.log Real.pi)))

noncomputable def Ns408p516 := @Enclosure.Real.IsNear.addLit_ft_p qz83 (Enclosure.sfrac Bool.true Ns408p512 Ns408p513) 26139298459000564246947 18014398509481984000 39116466437359329 4096000000000000000000 Ns408p512 Ns408p513 0 1 Ns408p515 

noncomputable def Ns408p517 := nat_lit 350835725068095688394325727641600 

noncomputable abbrev qz84 := (@HSub.hSub Real Real Real qz356 qz425 qz625)

noncomputable def Ns408p518 := @Enclosure.Real.IsNear.subLit_ff_p qz84 (@HMul.hMul Real Real Real qz4 qz625 (Real.log Real.pi)) 6802965857556174502791 3602879701896396800 15436272985321 4000000000000000000 29338638591693 67108864000 763813 134217728000 Ns408p517 26139298459000564246947 18014398509481984000 

noncomputable def Ns408p519 := nat_lit 68029658575561745027910000 

noncomputable abbrev qz85 := qz425

noncomputable def Ns408p520 := @Enclosure.Real.IsNear.subLit_ff_p qz85 qz625 40894645172142353836451 18014398509481984000 15436272985321 4000000000000000000 763813 2000 0 1 Ns408p519 6802965857556174502791 3602879701896396800 15436272985321 4000000000000000000 

noncomputable def Ns408p521 := nat_lit 92086554379354478993220398065383374848 

noncomputable def Ns408p522 := nat_lit 57498214404010152713781248 

noncomputable def Ns408p523 := nat_lit 5781194377027674295116126851068838154532891728080640 

noncomputable def Ns408p524 := nat_lit 5499220601163160157151638669375315966398233643008 

noncomputable def Ns408p525 := nat_lit 9383693602221388402492992561316929590697616128 

noncomputable def Ns408p526 := BSN.log_dyadic_bound 236490195876 4430794195876 3 2 Ns408p523 134217728 50000000 Ns408p524 Ns408p525 14341162 4667284391752 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 236490195876) (BSN.artanhQ 4430794195876) 0 2 Ns408p524 Ns408p523 Ns408p525 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz426 := (Real.log (Enclosure.sfrac Bool.false 2333642195876 16000000))

noncomputable def Ns408p527 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 763813 4000) qz426 763813 4000 0 1 53549385074535527 4503599627370496 20000017 1000000000000000 40901716461936204484451 18014398509481984000 15276272984821 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 763813 4000) (BSN.isNear_log_sfrac 2333642195876 16000000 53549385074535527 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2333642195876) qz359)) Bool.false Ns408p522 Ns408p100 1000000850000000 50000000000000000000000 53549385074535527 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2333642195876 16000000 17 4667284391752 4194304000000 14341162 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns408p526 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns408p528 := BSN.arctan_dyadic_bound_f 1000 1527626 1 0 16777216 6250000 0 1 1 0 1 1 10982 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1527626) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1527626) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz427 := (@Nat.cast Real Real.instNatCast 1527626)

noncomputable def Ns408p529 := @Enclosure.Real.IsNear.subLit_ff_p qz12 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz13 qz427)) 884279719003555 562949953421312 1 2000000000000000 10982 16777216 1 6250000 14829569533753474154496 883911224231331 562949953421312 320000001 2000000000000000 qz14 (Ns408p528 rfl) rfl rfl 

noncomputable abbrev qz428 := (@HMul.hMul Real Real Real qz579 qz585 qz624)

noncomputable abbrev qz86 := qz428

noncomputable abbrev qz429 := qz624

noncomputable abbrev qz87 := qz429

noncomputable def Ns408p530 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 763813 4000) qz426) qz86 40901716461936204484451 18014398509481984000 15276272984821 4000000000000000000 883911224231331 2251799813685248 320000001 8000000000000000 Ns408p521 40894645172142353836451 18014398509481984000 15436272985321 4000000000000000000 (Ns408p527 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz16 qz87 1 4 0 1 883911224231331 562949953421312 320000001 2000000000000000 883911224231331 2251799813685248 320000001 8000000000000000 qz367 Ns408p529 rfl) 

noncomputable def Ns408p531 := @Ns408p516 Ns408p510 Ns408p511 39116466437359329 4096000000000000000000 (@Ns408p518 39116466437359329 4096000000000000000000 (Ns408p520 (Ns408p530 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 763813 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz625 (Real.log Real.pi) 763813 2000 0 1 38410761 33554432 1 67108864 29338638591693 67108864000 763813 134217728000 (Enclosure.Real.IsNear.const Bool.false 763813 2000) RS409to420.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns408p512 Ns408p513) 

noncomputable def Ns408p532 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz79) Bool.false Ns408p510 Ns408p511 39116466437359329 4096000000000000000000 48688230157 33554432 321 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz79) (@HAdd.hAdd Real Real Real qz368 qz83 (Enclosure.sfrac Bool.true Ns408p512 Ns408p513)) Bool.false Ns408p510 Ns408p511 39116466437359329 4096000000000000000000 Ns408p514 (Ns408p531 rfl rfl)) 

noncomputable def Ns408p533 := nat_lit 5693179823931923862913024 

noncomputable def Ns408p534 := nat_lit 2891195100438688211406294854374713428577548157607033217073022833820243702709492699105930625 

noncomputable def Ns408p535 := nat_lit 180468656028383376705345110207518346455653528001341539704795567934989718275908111313435361280 

noncomputable def Ns408p536 := nat_lit 1835696197668696804689375927730270490760619078767685467852921373534983802880535562890625 

noncomputable def Ns408p537 := nat_lit 7569205564447957901713656105193638541670442267605177411100440787305391152367817154366090625 

noncomputable def Ns408p538 := nat_lit 3308592027187028572931327020471169685020314680024594894587918745474811501724982040746314956800 

noncomputable def Ns408p539 := BSN.sin_dyadic_bound_f 80904951345 68719476736 3 2 33554432 12512208 Ns408p534 Ns408p535 Ns408p536 Ns408p537 Ns408p538 Ns408p536 30990288 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 80904951345) qz591 0 2 Ns408p534 Ns408p535 Ns408p536 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 80904951345) qz592 0 2 Ns408p537 Ns408p538 Ns408p536 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz430 := (@Nat.cast Real Real.instNatCast Ns408p100)

noncomputable def Ns408p540 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz79) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48688230157) qz418) Bool.false 48688230157 33554432 321 33554432 Bool.false 30990288 33554432 1 6250000 (Ns408p532 rfl) (Enclosure.sfrac_false_div 48688230157 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48688230157) qz418) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns408p533) qz430) 226375608064910080 72057594037927936 Bool.false 30990288 33554432 230 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 48688230157 33554432 226375608064910080 72057594037927936 230 Ns408p533 Ns408p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 30990288 33554432 Ns408p533 Ns408p100 80904951345 68719476736 12512208 12500000 (Ns408p539 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns408p541 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz79) Bool.false Ns408p510 Ns408p511 39116466437359329 4096000000000000000000 389505841258 268435456 2564 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz79) (@HAdd.hAdd Real Real Real qz368 qz83 (Enclosure.sfrac Bool.true Ns408p512 Ns408p513)) Bool.false Ns408p510 Ns408p511 39116466437359329 4096000000000000000000 Ns408p514 (Ns408p531 rfl rfl)) 

noncomputable def Ns408p542 := Ns408p509 48120 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 586 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 121545738 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 389 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 201358683 268435456) qz82 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz79) qz79 1) Bool.false 1936893 2097152 127487777 13107200000000 247922304 268435456 2611 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz79) qz79 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz79)) Bool.false 1936893 2097152 127487777 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz79) qz79) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz79)) Bool.false 30990288 33554432 2039804432 209715200000000 1936893 2097152 127487777 13107200000000 (Ns408p540 rfl rfl) rfl)) rfl) (Ns408p541 rfl) RS409to420.d7 

noncomputable def Ns408p543 := nat_lit 4107490642084842943288480781745670310524824097295754310943437381736128683321644939583598288512264113538994176 

noncomputable def Ns408p544 := nat_lit 443666543826253811546897362598942715792077258521009308779599928004755520672954815187397784337140944896 

noncomputable def Ns408p545 := nat_lit 24904261912643624110722376062681926764465421641189583800025695966471853927305231750817664702765710336697569280 

noncomputable def Ns408p546 := BSN.cos_dyadic_bound_f 295520802 268435456 4 3 268435456 134217728 Ns408p543 Ns408p252 Ns408p544 Ns408p545 Ns408p255 Ns408p544 121545738 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 295520802) qz370 0 3 Ns408p543 Ns408p252 Ns408p544 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 295520802) qz371 0 3 Ns408p545 Ns408p255 Ns408p544 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p547 := nat_lit 42213948196218758301302294584764284375844181220136296268835641977954560 

noncomputable def Ns408p548 := nat_lit 7225712126743029559516405697089720505954875532854934594150481223936 

noncomputable def Ns408p549 := nat_lit 110548641741891544931742983065158790008296547682827582238559961544089856 

noncomputable def Ns408p550 := BSN.sin_dyadic_bound_f 227698454 268435456 3 2 268435456 134217728 Ns408p547 Ns408p142 Ns408p548 Ns408p549 Ns408p145 Ns408p548 201358683 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 227698454) qz372 0 2 Ns408p547 Ns408p142 Ns408p548 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 227698454) qz373 0 2 Ns408p549 Ns408p145 Ns408p548 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p551 := nat_lit 89824527647684405437323729669512744268418772418863797213932275281130625 

noncomputable def Ns408p552 := nat_lit 32703255615766644502699196077796004475003420512164171494453062890625 

noncomputable def Ns408p553 := nat_lit 235201767139605058720938731388407422410042017463814060235022082682090625 

noncomputable def Ns408p554 := BSN.sin_dyadic_bound_f 274994415 268435456 3 2 268435456 134217728 Ns408p551 Ns408p142 Ns408p552 Ns408p553 Ns408p145 Ns408p552 229356691 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 274994415) qz372 0 2 Ns408p551 Ns408p142 Ns408p552 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 274994415) qz373 0 2 Ns408p553 Ns408p145 Ns408p552 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p555 := nat_lit 14649791878296991532823151210000 

noncomputable def Ns408p556 := BSN.sin_dyadic_bound_f 61866830 268435456 2 1 268435456 134217728 Ns408p555 Ns408p133 Ns408p555 Ns408p555 Ns408p134 Ns408p555 61320582 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 61866830) qz372 0 1 Ns408p555 Ns408p133 Ns408p555 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 61866830) qz373 0 1 Ns408p555 Ns408p134 Ns408p555 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p557 := Ns408p507 81687 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 249 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 229356691 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 141 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 61320582 268435456) qz82 rfl rfl (Ns408p542 RS409to420.d9 RS409to420.d11 RS409to420.d13 RS409to420.d17 (Ns408p546 rfl rfl) (Ns408p550 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns408p541 rfl) RS409to420.d19 RS409to420.d21 RS409to420.d23 RS409to420.d25 RS409to420.d17 (Ns408p554 rfl rfl) (Ns408p556 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns408p558 := nat_lit 16073042931047712590373848560442258561726428645197248431940028415549696 

noncomputable def Ns408p559 := nat_lit 3393713696702996888855570771025088383089130282697712355403835842816 

noncomputable def Ns408p560 := nat_lit 48212341365749731777343834539784725508413107675026349871109277574963456 

noncomputable def Ns408p561 := BSN.cos_dyadic_bound_f 207173594 268435456 3 2 268435456 134217728 Ns408p558 Ns408p123 Ns408p559 Ns408p560 Ns408p126 Ns408p559 192379415 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 207173594) qz370 0 2 Ns408p558 Ns408p123 Ns408p559 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 207173594) qz371 0 2 Ns408p560 Ns408p126 Ns408p559 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p562 := nat_lit 12975679420445762737019998842812478331255883329274251557890625402183936 

noncomputable def Ns408p563 := nat_lit 2211946112747811834673778731516762459442086493162152936413644595456 

noncomputable def Ns408p564 := nat_lit 38922614369111792587390648970974401468848765814836430367799048917360896 

noncomputable def Ns408p565 := BSN.cos_dyadic_bound_f 196379802 268435456 3 2 268435456 134217728 Ns408p562 Ns408p123 Ns408p563 Ns408p564 Ns408p126 Ns408p563 199749618 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 196379802) qz370 0 2 Ns408p562 Ns408p123 Ns408p563 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 196379802) qz371 0 2 Ns408p564 Ns408p126 Ns408p563 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p566 := Ns408p505 110146 BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 192379415 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 199749618 268435456) qz82 rfl rfl (Ns408p557 rfl rfl) (Ns408p541 rfl) RS409to420.d27 RS409to420.d29 RS409to420.d31 RS409to420.d33 RS409to420.d17 (Ns408p561 rfl rfl) (Ns408p565 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p567 := nat_lit 12271819985236796039601906988613663053156568018606115044218401452601505 

noncomputable def Ns408p568 := nat_lit 610790280239301219424125779100191660575566226503483028766659850401 

noncomputable def Ns408p569 := nat_lit 32139492015166459330316403052250574352721508179601676619477810164674721 

noncomputable def Ns408p570 := BSN.sin_dyadic_bound_f 167200093 268435456 3 2 268435456 134217728 Ns408p567 Ns408p142 Ns408p568 Ns408p569 Ns408p145 Ns408p568 156596571 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 167200093) qz372 0 2 Ns408p567 Ns408p142 Ns408p568 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 167200093) qz373 0 2 Ns408p569 Ns408p145 Ns408p568 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p571 := nat_lit 3420128646432603078134860914967663597576279525023559520129195032377436128164128581913055967788732395477442641 

noncomputable def Ns408p572 := nat_lit 256238653682940424141919820999549042414281580987785230753775471696171029392115835571325228907336212561 

noncomputable def Ns408p573 := nat_lit 20738714524169576468363853739209818817583282339149830877976268327989055155149804276754405635988871493946875985 

noncomputable def Ns408p574 := BSN.cos_dyadic_bound_f 282306181 268435456 4 3 268435456 134217728 Ns408p571 Ns408p252 Ns408p572 Ns408p573 Ns408p255 Ns408p572 133176092 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 282306181) qz370 0 3 Ns408p571 Ns408p252 Ns408p572 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 282306181) qz371 0 3 Ns408p573 Ns408p255 Ns408p572 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p575 := Ns408p503 135011 BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 156596571 268435456) BSN.abs_quadSignPos qz606 (BSN.sfrac_eq_quadSignPos_mul Bool.false 133176092 268435456) qz82 rfl rfl (Ns408p566 rfl) (Ns408p541 rfl) RS409to420.d35 RS409to420.d37 RS409to420.d39 RS409to420.d41 RS409to420.d17 (Ns408p570 rfl rfl) (Ns408p574 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p576 := nat_lit 29307070565293227591953061477209364094092893727979410741273005267671234774655092514086828606750938369565587201 

noncomputable def Ns408p577 := nat_lit 9156462464083548775155135073104505945930752825476433567422289542525398360308397161415227007094642374401 

noncomputable def Ns408p578 := nat_lit 146414780736987507550063819140393740793204556983140636571560084813758323283470202045790925115289822389134882561 

noncomputable def Ns408p579 := BSN.sin_dyadic_bound_f 380315457 268435456 4 3 268435456 134217728 Ns408p576 Ns408p269 Ns408p577 Ns408p578 Ns408p272 Ns408p577 265258187 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 380315457) qz372 0 3 Ns408p576 Ns408p269 Ns408p577 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 380315457) qz373 0 3 Ns408p578 Ns408p272 Ns408p577 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p580 := nat_lit 1032193897704509149121283859007750689094140573373712519089933516800000 

noncomputable def Ns408p581 := nat_lit 14001455999992146142724248538990192942671768715886434713600000000 

noncomputable def Ns408p582 := nat_lit 3096553690201527463071566128526174086896536376583705784400373350400000 

noncomputable def Ns408p583 := BSN.cos_dyadic_bound_f 104296960 268435456 3 2 268435456 134217728 Ns408p580 Ns408p123 Ns408p581 Ns408p582 Ns408p126 Ns408p581 248427483 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 104296960) qz370 0 2 Ns408p580 Ns408p123 Ns408p581 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 104296960) qz371 0 2 Ns408p582 Ns408p126 Ns408p581 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p584 := Ns408p501 157375 BSN.abs_quadSignPos qz415 (BSN.sfrac_eq_quadSignPos_mul Bool.false 265258187 268435456) BSN.abs_quadSignNeg qz395 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 248427483 268435456) qz82 rfl rfl (Ns408p575 rfl) (Ns408p541 rfl) RS409to420.d43 RS409to420.d45 RS409to420.d52 RS409to420.d54 RS409to420.d17 (Ns408p579 rfl rfl) (Ns408p583 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p585 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz79) qz79 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz79) qz79 11) 15396149 268435456 157375 268435456 15396149 268435456 157375 268435456 8265744554917888 15396149 134217728 157375 134217728 (Ns408p584 rfl) 

noncomputable def Ns408p586 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz4 qz33 qz80) (Zeta.RiemannSiegel.correction qz81) 5052637 16777216 1 16777216 1899731364025 2199023255552 74092822137691 5497558138880000000 9598652979933183925 36893488147419103232 

noncomputable def Ns408p587 := @Enclosure.Real.IsNear.mulLit_tf qz33 qz80 1 1 0 1 5052637 16777216 1 16777216 5052637 16777216 1 16777216 

noncomputable abbrev qz88 := qz422

noncomputable def Ns408p588 := @Enclosure.Real.IsNear.sqrt_image qz88 4079031045989 33554432000 763813 33554432000 184979420 184979456 16777216 (@Enclosure.Real.IsNear.of_eq qz88 (@HMul.hMul Real Real Real qz4 qz79 qz2) Bool.false 4079031045989 33554432000 763813 33554432000 (BSN.t_div_two_pi_mk qz79 763813 1000 qz82) (@Enclosure.Real.IsNear.mulLit_ff qz79 qz2 763813 1000 0 1 5340353 33554432 1 33554432 4079031045989 33554432000 763813 33554432000 (Enclosure.Real.IsNear.const Bool.false 763813 1000) RS409to420.d48 rfl)) 

noncomputable abbrev qz735 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 763813 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz626 := qz735

noncomputable abbrev qz431 := qz626

noncomputable abbrev qz89 := qz431

noncomputable def Ns408p589 := @Enclosure.Real.IsNear.sqrt_image qz89 92489719 8388608 9 8388608 55708524 55708530 16777216 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 369958876 33554432 36 33554432 92489719 8388608 9 8388608 (Ns408p588 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns408p590 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz89) 55708527 16777216 3 16777216 5052636 5052638 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz89) Bool.false 111417054 33554432 6 33554432 55708527 16777216 3 16777216 (Ns408p589 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns408p591 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 10105274 33554432 2 33554432 5052637 16777216 1 16777216 (Ns408p590 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz90 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz423))

noncomputable abbrev qz627 := (@HMul.hMul Real Real Real qz714 qz734 qz734)

noncomputable abbrev qz432 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz627 qz622) qz598)

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz432))

noncomputable def Ns408p592 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz81) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv qz90) qz91) Bool.false 1899731364025 

noncomputable def Ns408p593 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz90) qz91 1062325 1048576 15 

noncomputable def Ns408p594 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz90) Bool.false 33994400 33554432 240 33554432 1062325 1048576 15 

noncomputable def Ns408p595 := @Enclosure.Real.IsNear.recentre' qz90 Bool.false 16560079 16777216 1452304432 209715200000000 16560079 16777216 90769027 13107200000000 

noncomputable abbrev qz92 := (@HMul.hMul Real Real Real qz350 qz347 qz423)

noncomputable def Ns408p596 := @Enclosure.Real.IsNear.cos_image qz92 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2702159) qz369) Bool.false 2702159 16777216 227 33554432 Bool.false 16560079 16777216 1 

noncomputable def Ns408p597 := nat_lit 48574935736648702264354611 

noncomputable def Ns408p598 := nat_lit 7205759403792793600000000000000 

noncomputable def Ns408p599 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz81 884279719003555 140737488355328 1 500000000000000 215031 8388608 9 8388608 190147552257053435205 1180591620717411303424 Ns408p597 

noncomputable def Ns408p600 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz31 92489719 8388608 9 8388608 11 1 0 1 215031 215031 8388608 9 

noncomputable def Ns408p601 := @Ns408p600 8388608 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 369958876 33554432 36 33554432 92489719 8388608 9 8388608 (Ns408p588 rfl rfl rfl rfl rfl rfl) rfl) qz398 

noncomputable def Ns408p602 := @Enclosure.Real.IsNear.recentre' qz92 Bool.false 190147552257053435205 1180591620717411303424 Ns408p597 Ns408p598 2702159 16777216 227 33554432 (@Ns408p599 Ns408p598 RS409to420.d47 (Ns408p601 rfl rfl) rfl) 

noncomputable def Ns408p603 := nat_lit 53314286381140688873760961 

noncomputable def Ns408p604 := BSN.cos_dyadic_bound_f 2702159 16777216 2 1 16777216 6250000 Ns408p603 Ns408p196 Ns408p603 Ns408p603 Ns408p197 Ns408p603 16560079 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 2702159) (BSN.cosEvenQ 16777216) 0 1 Ns408p603 Ns408p196 Ns408p603 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 2702159) (BSN.cosOddQ 16777216) 0 1 Ns408p603 Ns408p197 Ns408p603 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p605 := @Enclosure.Real.IsNear.inv_image qz90 16560079 16777216 90769027 13107200000000 16997080 16997320 16777216 (Ns408p595 (@Ns408p596 6250000 (Ns408p602 rfl) (Enclosure.sfrac_false_div 2702159 16777216) (Ns408p604 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns408p606 := @Enclosure.Real.IsNear.recentre' qz91 Bool.false 14306216 16777216 

noncomputable abbrev qz93 := (@HMul.hMul Real Real Real qz350 qz347 qz432)

noncomputable def Ns408p607 := @Enclosure.Real.IsNear.cos_image qz93 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4610645)) qz377) Bool.true 4610645 8388608 

noncomputable def Ns408p608 := nat_lit 5443288992738160600885553005 

noncomputable def Ns408p609 := nat_lit 9903520314283042199192993792 

noncomputable def Ns408p610 := nat_lit 2141833828572254567702824701824009 

noncomputable def Ns408p611 := @Enclosure.Real.IsNear.recentre' qz93 Bool.true Ns408p608 Ns408p609 Ns408p610 

noncomputable def Ns408p612 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz94 := qz432

noncomputable def Ns408p613 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz94 884279719003555 140737488355328 1 500000000000000 6155618946991 

noncomputable abbrev qz433 := (@HSub.hSub Real Real Real qz584 qz627 qz622)

noncomputable abbrev qz95 := qz433

noncomputable def Ns408p614 := @Enclosure.Real.IsNear.subLit_tf qz95 qz28 1757572435887 70368744177664 79368111 70368744177664 1 16 

noncomputable abbrev qz434 := qz627

noncomputable abbrev qz96 := qz434

noncomputable def Ns408p615 := @Enclosure.Real.IsNear.subLit_ff_n qz96 qz81 46238330961 70368744177664 3870639 70368744177664 215031 8388608 9 8388608 

noncomputable def Ns408p616 := @Enclosure.Real.IsNear.mulLit_ff qz81 qz81 215031 8388608 9 8388608 215031 8388608 9 8388608 46238330961 70368744177664 

noncomputable def Ns408p617 := nat_lit 3759578979937739475472303555145231363775160931394095190625 

noncomputable def Ns408p618 := nat_lit 988643523323402220304136834155207460536120982503085435781120 

noncomputable def Ns408p619 := nat_lit 204217745529882237132869096890544727377928017250390625 

noncomputable def Ns408p620 := nat_lit 11278328504322158661942644927241913001870726938147784790625 

noncomputable def Ns408p621 := nat_lit 44488958549553099913686157536984335724125444212638844610150400 

noncomputable def Ns408p622 := BSN.cos_dyadic_bound_f 4610645 8388608 3 2 16777216 6250000 Ns408p617 Ns408p618 Ns408p619 Ns408p620 Ns408p621 Ns408p619 14306216 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 4610645) (BSN.cosEvenQ 8388608) 0 2 Ns408p617 Ns408p618 Ns408p619 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 4610645) (BSN.cosOddQ 8388608) 0 2 Ns408p620 Ns408p621 Ns408p619 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p623 := @Ns408p606 1527304432 209715200000000 1788277 2097152 95456527 13107200000000 (@Ns408p607 239 33554432 Bool.false 14306216 16777216 1 6250000 (@Ns408p611 Ns408p612 4610645 8388608 239 33554432 (@Ns408p613 70368744177664 79368111 70368744177664 Ns408p608 Ns408p609 Ns408p610 Ns408p612 RS409to420.d47 (@Ns408p614 0 1 98489903151856 6155618946991 70368744177664 79368111 70368744177664 (@Ns408p615 14743586196261175296 1757572435887 70368744177664 79368111 70368744177664 (@Ns408p616 3870639 70368744177664 (Ns408p601 rfl rfl) (Ns408p601 rfl rfl) rfl) (Ns408p601 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4610645 8388608) (BSN.cos_neg_of_bound 4610645 8388608 Bool.false 14306216 16777216 1 6250000 (Ns408p622 rfl rfl)) rfl rfl) 

noncomputable def Ns408p624 := @Ns408p586 189556768535100639429 Ns408p497 (Ns408p587 qz51 (@Enclosure.Real.IsNear.of_eq qz80 (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 5052637 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz88 (BSN.t_div_two_pi_nonneg qz79 763813 1000 qz82)) Ns408p591) rfl) (@Ns408p592 2199023255552 74092822137691 5497558138880000000 (BSN.correction_mk qz81 (BSN.cos_two_pi_p_ne_zero_mk qz79 763813 1000 11 qz82 rfl rfl (@BSN.floor_sqrt_eq_dec qz79 763813 1000 11 qz82 rfl rfl rfl))) (@Ns408p593 2097152 1788277 2097152 95456527 13107200000000 1899731364025 2199023255552 74092822137691 5497558138880000000 (@Ns408p594 2097152 (Ns408p605 rfl rfl rfl rfl rfl) rfl) (Ns408p623 rfl) rfl)) 

noncomputable def Ns408p625 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz79) (hardyZApproximantRS₀ qz79) Bool.false 13830714192051142581 36893488147419103232 54263195025175100639429 Ns408p497 (@Eq.refl Real (hardyZApproximantRS₀ qz79)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz79) (@HSub.hSub Real Real Real qz30 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz79) qz79 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz80) (Zeta.RiemannSiegel.correction qz81))) Bool.false 13830714192051142581 36893488147419103232 54263195025175100639429 Ns408p497 (BSN.hardyZApproximantRS₀_eq qz79 11 (@BSN.floor_sqrt_eq_dec qz79 763813 1000 11 qz82 rfl rfl rfl)) (@Ns408p499 13830714192051142581 36893488147419103232 54263195025175100639429 Ns408p497 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz79) qz79 11) (@HAdd.hAdd Real Real Real qz368 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz79) qz79 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz79) qz79 11)) Bool.false 15396149 134217728 157375 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz79) qz79 11) (Ns408p585 (Ns408p584 rfl) rfl rfl)) (Ns408p624 rfl) rfl rfl)) 

theorem RS409to420.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz79) Bool.false 13830714192051142581 36893488147419103232 54263195025175100639429 Ns408p497 := Ns408p625 

noncomputable def Ns408p626 := nat_lit 2951479051793528258560000 

noncomputable def Ns408p627 := nat_lit 101938389833823584459524407296 

noncomputable abbrev qz736 := (Enclosure.sfrac Bool.false 765286 1000)

noncomputable abbrev qz628 := qz736

noncomputable abbrev qz435 := qz628

noncomputable abbrev qz97 := qz435

noncomputable abbrev qz737 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 765286 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz629 := qz737

noncomputable abbrev qz436 := qz629

noncomputable abbrev qz98 := (@HPow.hPow Real Real Real qz351 qz436 qz353)

noncomputable abbrev qz738 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 765286 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz630 := qz738

noncomputable abbrev qz437 := qz630

noncomputable abbrev qz99 := qz437

noncomputable def Ns408p628 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz97) qz97 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz98) (Zeta.RiemannSiegel.correction qz99)) 379320309 134217728 157681 134217728 74633991416627391161 295147905179352825856 12255969841591368989 Ns408p626 Ns408p627 

noncomputable def Ns408p629 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz97) qz97 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 765286 1000 195 242 268435456 134217728 4503599627370496 Bool.false 390455092812 2569 

noncomputable def Ns408p630 := Ns408p629 618095470 44 84886744 8 643680110 44 80936328 8 Bool.true 385422306 135274 Bool.true 341518530 Bool.true 103186209 14148475504056880 1 Bool.false 256561679 Bool.false Bool.false 248846145 Bool.true Bool.true 379320309 

noncomputable def Ns408p631 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz97) qz97 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 765286 1000 87 144 268435456 134217728 4503599627370496 Bool.false 390455092812 2569 

noncomputable def Ns408p632 := Ns408p631 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 464923510 110361 Bool.true 40171008 Bool.true 201849138 14148475504056880 1 Bool.false 40021239 Bool.false Bool.false 196054675 Bool.false Bool.true 385422306 

noncomputable def Ns408p633 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz97) qz97 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 765286 1000 53 22 268435456 134217728 4503599627370496 Bool.false 390455092812 2569 

noncomputable def Ns408p634 := Ns408p633 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 352938989 81848 Bool.false 26296321 Bool.true 16551657 14148475504056880 1 Bool.false 26254282 Bool.true Bool.false 267925332 Bool.true Bool.true 464923510 

noncomputable def Ns408p635 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz97) qz97 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 765286 1000 250 141 268435456 134217728 4503599627370496 Bool.false 390455092812 2569 

noncomputable def Ns408p636 := Ns408p635 372130544 43 134217720 8 432030192 43 120047984 16 Bool.true 156414922 48216 Bool.false 254440249 Bool.false 374737911 14148475504056880 1 Bool.false 156610448 Bool.true Bool.false 264345381 Bool.true Bool.true 352938989 

noncomputable def Ns408p637 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz97) qz97 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 765286 1000 588 390 268435456 134217728 4503599627370496 Bool.false 390455092812 2569 

noncomputable def Ns408p638 := Ns408p637 186065264 43 189812528 16 294906480 43 154981288 8 Bool.true 268435272 2619 Bool.false 127383365 Bool.false 320895334 14148475504056880 1 Bool.false 238774142 Bool.false Bool.false 98412459 Bool.true Bool.true 156414922 

noncomputable def Ns408p639 := nat_lit 370106477475153262457249085062786496371193235245511150481 

noncomputable def Ns408p640 := nat_lit 254445909090374516431608383494687271249490971983872000 

noncomputable def Ns408p641 := nat_lit 125997100052594017827105993364480000 

noncomputable def Ns408p642 := nat_lit 578543015513729452394746621154552647680 

noncomputable abbrev qz631 := (@Eq.refl Real qz736)

noncomputable abbrev qz438 := qz631

noncomputable abbrev qz100 := qz438

noncomputable def Ns408p643 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz97 765286 1000 2342651647184 16000000 1530572 4000 2000 Ns408p641 Ns408p642 qz100 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns408p644 := nat_lit 7579780658691138815124461262085867445682037457828068361850880 

noncomputable abbrev qz632 := (@HSub.hSub Real Real Real qz718 qz719 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz720 (@Nat.cast Real Real.instNatCast 1530572))))

noncomputable abbrev qz439 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 765286 4000) (Real.log (Enclosure.sfrac Bool.false 2342651647184 16000000))) (@HMul.hMul Real Real Real qz579 qz585 qz632))

noncomputable abbrev qz633 := (Enclosure.sfrac Bool.false 765286 2000)

noncomputable abbrev qz101 := (@HSub.hSub Real Real Real qz356 (@HSub.hSub Real Real Real qz356 qz439 qz633) (@HMul.hMul Real Real Real qz350 qz633 (Real.log Real.pi)))

noncomputable def Ns408p645 := @Enclosure.Real.IsNear.addLit_ft_p qz101 (Enclosure.sfrac Bool.true Ns408p641 Ns408p642) 13101500822443595944741 9007199254740992000 19595792947789719 2048000000000000000000 Ns408p641 Ns408p642 0 1 Ns408p644 

noncomputable def Ns408p646 := nat_lit 439613418444627713963287642112000 

noncomputable abbrev qz102 := (@HSub.hSub Real Real Real qz356 qz439 qz633)

noncomputable def Ns408p647 := @Enclosure.Real.IsNear.subLit_ff_p qz102 (@HMul.hMul Real Real Real qz4 qz633 (Real.log Real.pi)) 17046860148505057973029 9007199254740992000 7732866505181 2000000000000000000 14697608821323 33554432000 382643 67108864000 Ns408p646 13101500822443595944741 9007199254740992000 

noncomputable def Ns408p648 := nat_lit 6818744059402023189211600 

noncomputable abbrev qz103 := qz439

noncomputable def Ns408p649 := @Enclosure.Real.IsNear.subLit_ff_p qz103 qz633 4098680378587383074977 1801439850948198400 7732866505181 2000000000000000000 765286 2000 0 1 Ns408p648 17046860148505057973029 9007199254740992000 7732866505181 2000000000000000000 

noncomputable def Ns408p650 := nat_lit 9229407712858450944458820656662839296 

noncomputable def Ns408p651 := nat_lit 57516847561079638384967680 

noncomputable def Ns408p652 := nat_lit 5828359256121475628430226528800546477719276618711040 

noncomputable def Ns408p653 := nat_lit 5951072946446248473849296534252272840371444645888 

noncomputable def Ns408p654 := nat_lit 10897446460669631155588609308018643904731742208 

noncomputable def Ns408p655 := BSN.log_dyadic_bound 245499647184 4439803647184 3 2 Ns408p652 134217728 50000000 Ns408p653 Ns408p654 14858336 4685303294368 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 245499647184) (BSN.artanhQ 4439803647184) 0 2 Ns408p653 Ns408p652 Ns408p654 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz440 := (Real.log (Enclosure.sfrac Bool.false 2342651647184 16000000))

noncomputable def Ns408p656 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 765286 4000) qz440 765286 4000 0 1 53566738554350695 4503599627370496 20000017 1000000000000000 4099387508130482597377 1801439850948198400 7652866504931 2000000000000000000 (Enclosure.Real.IsNear.const Bool.false 765286 4000) (BSN.isNear_log_sfrac 2342651647184 16000000 53566738554350695 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2342651647184) qz359)) Bool.false Ns408p651 Ns408p100 1000000850000000 50000000000000000000000 53566738554350695 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2342651647184 16000000 17 4685303294368 4194304000000 14858336 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns408p655 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns408p657 := BSN.arctan_dyadic_bound_f 1000 1530572 1 0 16777216 6250000 0 1 1 0 1 1 10961 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1530572) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1530572) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns408p658 := @Enclosure.Real.IsNear.subLit_ff_p qz12 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz13 (@Nat.cast Real Real.instNatCast 1530572))) 884279719003555 562949953421312 1 2000000000000000 10961 16777216 1 6250000 14829581355702496002048 883911928874403 562949953421312 320000001 2000000000000000 qz14 (Ns408p657 rfl) rfl rfl 

noncomputable abbrev qz441 := (@HMul.hMul Real Real Real qz579 qz585 qz632)

noncomputable abbrev qz104 := qz441

noncomputable abbrev qz442 := qz632

noncomputable abbrev qz105 := qz442

noncomputable def Ns408p659 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 765286 4000) qz440) qz104 4099387508130482597377 1801439850948198400 7652866504931 2000000000000000000 883911928874403 2251799813685248 320000001 8000000000000000 Ns408p650 4098680378587383074977 1801439850948198400 7732866505181 2000000000000000000 (Ns408p656 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz16 qz105 1 4 0 1 883911928874403 562949953421312 320000001 2000000000000000 883911928874403 2251799813685248 320000001 8000000000000000 qz367 Ns408p658 rfl) 

noncomputable def Ns408p660 := @Ns408p645 Ns408p639 Ns408p640 19595792947789719 2048000000000000000000 (@Ns408p647 19595792947789719 2048000000000000000000 (Ns408p649 (Ns408p659 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 765286 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz633 (Real.log Real.pi) 765286 2000 0 1 38410761 33554432 1 67108864 14697608821323 33554432000 382643 67108864000 (Enclosure.Real.IsNear.const Bool.false 765286 2000) RS409to420.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns408p641 Ns408p642) 

noncomputable def Ns408p661 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz97) Bool.false Ns408p639 Ns408p640 19595792947789719 2048000000000000000000 48806886601 33554432 161 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz97) (@HAdd.hAdd Real Real Real qz368 qz101 (Enclosure.sfrac Bool.true Ns408p641 Ns408p642)) Bool.false Ns408p639 Ns408p640 19595792947789719 2048000000000000000000 Ns408p643 (Ns408p660 rfl rfl)) 

noncomputable def Ns408p662 := BSN.cos_dyadic_bound_f 80443748 68719476736 1 0 33554432 12512208 0 1 1 0 1 1 33554409 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 80443748) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 80443748) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns408p663 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz97) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48806886601) qz418) Bool.false 48806886601 33554432 161 16777216 Bool.true 33554409 33554432 1 6250000 (Ns408p661 rfl) (Enclosure.sfrac_false_div 48806886601 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48806886601) qz418) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5660725586153294528512) qz430) 226375608064910080 72057594037927936 Bool.false 33554409 33554432 231 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q2 48806886601 33554432 226375608064910080 72057594037927936 231 5660725586153294528512 Ns408p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554409 33554432 5660725586153294528512 Ns408p100 80443748 68719476736 12512208 12500000 (Ns408p662 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns408p664 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz97) Bool.false Ns408p639 Ns408p640 19595792947789719 2048000000000000000000 390455092812 268435456 2569 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz97) (@HAdd.hAdd Real Real Real qz368 qz101 (Enclosure.sfrac Bool.true Ns408p641 Ns408p642)) Bool.false Ns408p639 Ns408p640 19595792947789719 2048000000000000000000 Ns408p643 (Ns408p660 rfl rfl)) 

noncomputable def Ns408p665 := Ns408p638 48216 BSN.abs_quadSignPos (BSN.cos_quad_nat0 588 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 238774142 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 390 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 98412459 268435456) qz100 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz97) qz97 1) Bool.true 33554409 33554432 63939201 6553600000000 268435272 268435456 2619 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz97) qz97 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz97)) Bool.true 33554409 33554432 63939201 6553600000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz97) qz97) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz97)) Bool.true 33554409 33554432 1023027216 104857600000000 33554409 33554432 63939201 6553600000000 (Ns408p663 rfl rfl) rfl)) rfl) (Ns408p664 rfl) RS409to420.d7 

noncomputable def Ns408p666 := nat_lit 2296850738991941228087766963531455950877954861574604268139355733190625 

noncomputable def Ns408p667 := nat_lit 69326893049053416867685847143023001441126940838641722053000390625 

noncomputable def Ns408p668 := nat_lit 6890413563189725577429565518900081806630982330842135520973961198790625 

noncomputable def Ns408p669 := BSN.cos_dyadic_bound_f 127383365 268435456 3 2 268435456 134217728 Ns408p666 Ns408p123 Ns408p667 Ns408p668 Ns408p126 Ns408p667 238774142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 127383365) qz370 0 2 Ns408p666 Ns408p123 Ns408p667 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 127383365) qz371 0 2 Ns408p668 Ns408p126 Ns408p667 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p670 := nat_lit 5712497873062274814716337413989815120678464371727619870141344792161926589877402491781431897486366513713319936 

noncomputable def Ns408p671 := nat_lit 1192232144807672134399453447159364174209487379640493174143926197244124144705832102657180718797595283456 

noncomputable def Ns408p672 := nat_lit 34627763796241619819146221952082397840681977724028689059335426422112403548165824375870894494313621870460211200 

noncomputable def Ns408p673 := BSN.cos_dyadic_bound_f 320895334 268435456 4 3 268435456 134217728 Ns408p670 Ns408p252 Ns408p671 Ns408p672 Ns408p255 Ns408p671 98412459 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 320895334) qz370 0 3 Ns408p670 Ns408p252 Ns408p671 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 320895334) qz371 0 3 Ns408p672 Ns408p255 Ns408p671 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p674 := nat_lit 36578059584436326371029631541749582056025614024429034204757237064409281 

noncomputable def Ns408p675 := nat_lit 17566550773893617658199928714076445424446854697743548783055988728001 

noncomputable def Ns408p676 := nat_lit 109699045651761191877772494767820593277227948363891615516705599215771841 

noncomputable def Ns408p677 := BSN.cos_dyadic_bound_f 254440249 268435456 3 2 268435456 134217728 Ns408p674 Ns408p123 Ns408p675 Ns408p676 Ns408p126 Ns408p675 156610448 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 254440249) qz370 0 2 Ns408p674 Ns408p123 Ns408p675 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 254440249) qz371 0 2 Ns408p676 Ns408p126 Ns408p675 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p678 := nat_lit 27623191325467411063762278074277417637455194154278663856933666659976324308821122269869426649718899352401258721 

noncomputable def Ns408p679 := nat_lit 7668873561271081678711006177739738782496138378895322287418015617513670542978820296082406314197041719521 

noncomputable def Ns408p680 := nat_lit 138008827280897953617776327231752594649469010519002697761490214525664624656343083180704959907744794955619936481 

noncomputable def Ns408p681 := BSN.sin_dyadic_bound_f 374737911 268435456 4 3 268435456 134217728 Ns408p678 Ns408p269 Ns408p679 Ns408p680 Ns408p272 Ns408p679 264345381 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 374737911) qz372 0 3 Ns408p678 Ns408p269 Ns408p679 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 374737911) qz373 0 3 Ns408p680 Ns408p272 Ns408p679 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p682 := Ns408p636 81848 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 250 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 156610448 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 141 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 264345381 268435456) qz100 rfl rfl (Ns408p665 RS409to420.d9 RS409to420.d11 RS409to420.d13 RS409to420.d17 (Ns408p669 rfl rfl) (Ns408p673 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns408p664 rfl) RS409to420.d19 RS409to420.d21 RS409to420.d23 RS409to420.d25 RS409to420.d17 (Ns408p677 rfl rfl) (Ns408p681 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns408p683 := nat_lit 478167406933024761191072071681 

noncomputable def Ns408p684 := BSN.sin_dyadic_bound_f 26296321 268435456 2 1 268435456 134217728 Ns408p683 Ns408p133 Ns408p683 Ns408p683 Ns408p134 Ns408p683 26254282 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26296321) qz372 0 1 Ns408p683 Ns408p133 Ns408p683 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26296321) qz373 0 1 Ns408p683 Ns408p134 Ns408p683 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p685 := nat_lit 75052629315285438447605031201 

noncomputable def Ns408p686 := BSN.cos_dyadic_bound_f 16551657 268435456 2 1 268435456 134217728 Ns408p685 Ns408p149 Ns408p685 Ns408p685 Ns408p150 Ns408p685 267925332 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 16551657) qz370 0 1 Ns408p685 Ns408p149 Ns408p685 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 16551657) qz371 0 1 Ns408p685 Ns408p150 Ns408p685 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p687 := Ns408p634 110361 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 26254282 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267925332 268435456) qz100 rfl rfl (Ns408p682 rfl rfl) (Ns408p664 rfl) RS409to420.d27 RS409to420.d29 RS409to420.d31 RS409to420.d33 RS409to420.d17 (Ns408p684 rfl rfl) (Ns408p686 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p688 := nat_lit 2604059588867461192182814212096 

noncomputable def Ns408p689 := BSN.sin_dyadic_bound_f 40171008 268435456 2 1 268435456 134217728 Ns408p688 Ns408p133 Ns408p688 Ns408p688 Ns408p134 Ns408p688 40021239 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 40171008) qz372 0 1 Ns408p688 Ns408p133 Ns408p688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 40171008) qz373 0 1 Ns408p688 Ns408p134 Ns408p688 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p690 := nat_lit 14483016679047337793199207500332290347428744793107357080360001769554176 

noncomputable def Ns408p691 := nat_lit 2755593760517878068284031195101888600329221998961428533475756196096 

noncomputable def Ns408p692 := nat_lit 43443538849620977623461054438606667265085575935324148384013053796270336 

noncomputable def Ns408p693 := BSN.cos_dyadic_bound_f 201849138 268435456 3 2 268435456 134217728 Ns408p690 Ns408p123 Ns408p691 Ns408p692 Ns408p126 Ns408p691 196054675 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 201849138) qz370 0 2 Ns408p690 Ns408p123 Ns408p691 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 201849138) qz371 0 2 Ns408p692 Ns408p126 Ns408p691 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p694 := Ns408p632 135274 BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 40021239 268435456) BSN.abs_quadSignPos qz606 (BSN.sfrac_eq_quadSignPos_mul Bool.false 196054675 268435456) qz100 rfl rfl (Ns408p687 rfl) (Ns408p664 rfl) RS409to420.d35 RS409to420.d37 RS409to420.d39 RS409to420.d41 RS409to420.d17 (Ns408p689 rfl rfl) (Ns408p693 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p695 := nat_lit 19048086467943163558665640236595442859502294455190084914438271253670239404848467208637441071578980603046400000 

noncomputable def Ns408p696 := nat_lit 2517510378195486152080661570373240643978198309336624275337775914084418680346440752193409841000000000000 

noncomputable def Ns408p697 := nat_lit 95189456661682567425826630720853816016793150942547062892878340785824865429432568940324845518946584391232000000 

noncomputable def Ns408p698 := BSN.sin_dyadic_bound_f 341518530 268435456 4 3 268435456 134217728 Ns408p695 Ns408p269 Ns408p696 Ns408p697 Ns408p272 Ns408p696 256561679 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 341518530) qz372 0 3 Ns408p695 Ns408p269 Ns408p696 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 341518530) qz373 0 3 Ns408p697 Ns408p272 Ns408p696 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p699 := nat_lit 988919790886745849963206197368895826050164556767141007989131853523201 

noncomputable def Ns408p700 := nat_lit 12852075145988479842285021957125502705540089766143112499754789121 

noncomputable def Ns408p701 := nat_lit 2966733668509945572929934022062773227145082590121890737742396050991361 

noncomputable def Ns408p702 := BSN.cos_dyadic_bound_f 103186209 268435456 3 2 268435456 134217728 Ns408p699 Ns408p123 Ns408p700 Ns408p701 Ns408p126 Ns408p700 248846145 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 103186209) qz370 0 2 Ns408p699 Ns408p123 Ns408p700 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 103186209) qz371 0 2 Ns408p701 Ns408p126 Ns408p700 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p703 := Ns408p630 157681 BSN.abs_quadSignPos qz415 (BSN.sfrac_eq_quadSignPos_mul Bool.false 256561679 268435456) BSN.abs_quadSignNeg qz395 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 248846145 268435456) qz100 rfl rfl (Ns408p694 rfl) (Ns408p664 rfl) RS409to420.d43 RS409to420.d45 RS409to420.d52 RS409to420.d54 RS409to420.d17 (Ns408p698 rfl rfl) (Ns408p702 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p704 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz97) qz97 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz97) qz97 11) 379320309 268435456 157681 268435456 379320309 268435456 157681 268435456 203646040232951808 379320309 134217728 157681 134217728 (Ns408p703 rfl) 

noncomputable def Ns408p705 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz4 qz33 qz98) (Zeta.RiemannSiegel.correction qz99) 1262551 4194304 1 16777216 59113644848111 70368744177664 11987816068329 879609302220800000 74633991416627391161 295147905179352825856 

noncomputable def Ns408p706 := @Enclosure.Real.IsNear.mulLit_tf qz33 qz98 1 1 0 1 1262551 4194304 1 16777216 1262551 4194304 1 16777216 

noncomputable abbrev qz106 := qz436

noncomputable def Ns408p707 := @Enclosure.Real.IsNear.sqrt_image qz106 2043448692979 16777216000 382643 16777216000 185157699 185157735 16777216 (@Enclosure.Real.IsNear.of_eq qz106 (@HMul.hMul Real Real Real qz4 qz97 qz2) Bool.false 2043448692979 16777216000 382643 16777216000 (BSN.t_div_two_pi_mk qz97 765286 1000 qz100) (@Enclosure.Real.IsNear.mulLit_ff qz97 qz2 765286 1000 0 1 5340353 33554432 1 33554432 2043448692979 16777216000 382643 16777216000 (Enclosure.Real.IsNear.const Bool.false 765286 1000) RS409to420.d48 rfl)) 

noncomputable abbrev qz739 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 765286 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz634 := qz739

noncomputable abbrev qz443 := qz634

noncomputable abbrev qz107 := qz443

noncomputable def Ns408p708 := @Enclosure.Real.IsNear.sqrt_image qz107 185157717 16777216 9 8388608 55735363 55735369 16777216 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 370315434 33554432 36 33554432 185157717 16777216 9 8388608 (Ns408p707 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns408p709 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 27867683 8388608 3 16777216 5050203 5050205 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 111470732 33554432 6 33554432 27867683 8388608 3 16777216 (Ns408p708 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns408p710 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 10100408 33554432 2 33554432 1262551 4194304 1 16777216 (Ns408p709 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz108 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz437))

noncomputable abbrev qz635 := (@HMul.hMul Real Real Real qz714 qz738 qz738)

noncomputable abbrev qz444 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz635 qz630) qz598)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz444))

noncomputable def Ns408p711 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz99) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv qz108) qz109) Bool.false 59113644848111 

noncomputable def Ns408p712 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz108) qz109 4305563 4194304 123 

noncomputable def Ns408p713 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz108) Bool.false 34444504 33554432 246 33554432 4305563 4194304 123 

noncomputable def Ns408p714 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 16343680 16777216 1452304432 209715200000000 127685 131072 90769027 13107200000000 

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz350 qz347 qz437)

noncomputable def Ns408p715 := @Enclosure.Real.IsNear.cos_image qz110 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3822319) qz369) Bool.false 3822319 16777216 227 33554432 Bool.false 16343680 16777216 1 

noncomputable def Ns408p716 := nat_lit 242874678684009213796336639 

noncomputable def Ns408p717 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz99 884279719003555 140737488355328 1 500000000000000 608341 16777216 9 8388608 537943608538341652255 2361183241434822606848 Ns408p716 

noncomputable def Ns408p718 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz31 185157717 16777216 9 8388608 11 1 0 1 608341 608341 16777216 9 

noncomputable def Ns408p719 := @Ns408p718 8388608 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 370315434 33554432 36 33554432 185157717 16777216 9 8388608 (Ns408p707 rfl rfl rfl rfl rfl rfl) rfl) qz398 

noncomputable def Ns408p720 := @Enclosure.Real.IsNear.recentre' qz110 Bool.false 537943608538341652255 2361183241434822606848 Ns408p716 Ns408p171 3822319 16777216 227 33554432 (@Ns408p717 Ns408p171 RS409to420.d47 (Ns408p719 rfl rfl) rfl) 

noncomputable def Ns408p721 := nat_lit 213455680568391922870893121 

noncomputable def Ns408p722 := BSN.cos_dyadic_bound_f 3822319 16777216 2 1 16777216 6250000 Ns408p721 Ns408p196 Ns408p721 Ns408p721 Ns408p197 Ns408p721 16343680 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 3822319) (BSN.cosEvenQ 16777216) 0 1 Ns408p721 Ns408p196 Ns408p721 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 3822319) (BSN.cosOddQ 16777216) 0 1 Ns408p721 Ns408p197 Ns408p721 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p723 := @Enclosure.Real.IsNear.inv_image qz108 127685 131072 90769027 13107200000000 17222129 17222375 16777216 (Ns408p714 (@Ns408p715 6250000 (Ns408p720 rfl) (Enclosure.sfrac_false_div 3822319 16777216) (Ns408p722 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns408p724 := @Enclosure.Real.IsNear.recentre' qz109 Bool.false 13729597 16777216 

noncomputable abbrev qz111 := (@HMul.hMul Real Real Real qz350 qz347 qz444)

noncomputable def Ns408p725 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 10272119)) qz369) Bool.true 10272119 16777216 

noncomputable def Ns408p726 := nat_lit 24254356295519821103096462005 

noncomputable def Ns408p727 := nat_lit 1092566641709460431075270034413521 

noncomputable def Ns408p728 := @Enclosure.Real.IsNear.recentre' qz111 Bool.true Ns408p726 Ns408p187 Ns408p727 

noncomputable def Ns408p729 := nat_lit 151115727451828646838272000000000000000 

noncomputable abbrev qz112 := qz444

noncomputable def Ns408p730 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz112 884279719003555 140737488355328 1 500000000000000 27428375630791 

noncomputable abbrev qz445 := (@HSub.hSub Real Real Real qz584 qz635 qz630)

noncomputable abbrev qz113 := qz445

noncomputable def Ns408p731 := @Enclosure.Real.IsNear.subLit_tf qz113 qz28 9836189586375 281474976710656 40486311 35184372088832 1 16 

noncomputable abbrev qz446 := qz635

noncomputable abbrev qz114 := qz446

noncomputable def Ns408p732 := @Enclosure.Real.IsNear.subLit_ff_n qz114 qz99 370078772281 281474976710656 2737575 35184372088832 608341 16777216 9 8388608 

noncomputable def Ns408p733 := @Enclosure.Real.IsNear.mulLit_ff qz99 qz99 608341 16777216 9 8388608 608341 16777216 9 8388608 370078772281 281474976710656 

noncomputable def Ns408p734 := nat_lit 1482058543505314576496545291183496866381580056654791774784321 

noncomputable def Ns408p735 := nat_lit 253092741970790968397859029543733109897246971520789871559966720 

noncomputable def Ns408p736 := nat_lit 123959648361668381221211803410211771532366288536586898241 

noncomputable def Ns408p737 := nat_lit 4445927711219220392727193449943670175601675437387302150556481 

noncomputable def Ns408p738 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400 

noncomputable def Ns408p739 := BSN.cos_dyadic_bound_f 10272119 16777216 3 2 16777216 6250000 Ns408p734 Ns408p735 Ns408p736 Ns408p737 Ns408p738 Ns408p736 13729597 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 10272119) (BSN.cosEvenQ 16777216) 0 2 Ns408p734 Ns408p735 Ns408p736 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 10272119) (BSN.cosOddQ 16777216) 0 2 Ns408p737 Ns408p738 Ns408p736 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p740 := @Ns408p724 389638608 52428800000000 13729597 16777216 24352413 3276800000000 (@Ns408p725 61 8388608 Bool.false 13729597 16777216 1 6250000 (@Ns408p728 Ns408p729 10272119 16777216 61 8388608 (@Ns408p730 281474976710656 40486311 35184372088832 Ns408p726 Ns408p187 Ns408p727 Ns408p729 RS409to420.d47 (@Ns408p731 0 1 438854010092656 27428375630791 281474976710656 40486311 35184372088832 (@Ns408p732 165023877307564032000 9836189586375 281474976710656 40486311 35184372088832 (@Ns408p733 2737575 35184372088832 (Ns408p719 rfl rfl) (Ns408p719 rfl rfl) rfl) (Ns408p719 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 10272119 16777216) (BSN.cos_neg_of_bound 10272119 16777216 Bool.false 13729597 16777216 1 6250000 (Ns408p739 rfl rfl)) rfl rfl) 

noncomputable def Ns408p741 := @Ns408p705 12255969841591368989 Ns408p626 (Ns408p706 qz51 (@Enclosure.Real.IsNear.of_eq qz98 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 1262551 4194304 1 16777216 (BSN.rpow_neg_quarter_mk qz106 (BSN.t_div_two_pi_nonneg qz97 765286 1000 qz100)) Ns408p710) rfl) (@Ns408p711 70368744177664 11987816068329 879609302220800000 (BSN.correction_mk qz99 (BSN.cos_two_pi_p_ne_zero_mk qz97 765286 1000 11 qz100 rfl rfl (@BSN.floor_sqrt_eq_dec qz97 765286 1000 11 qz100 rfl rfl rfl))) (@Ns408p712 16777216 13729597 16777216 24352413 3276800000000 59113644848111 70368744177664 11987816068329 879609302220800000 (@Ns408p713 16777216 (Ns408p723 rfl rfl rfl rfl rfl) rfl) (Ns408p740 rfl) rfl)) 

noncomputable def Ns408p742 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz97) (hardyZApproximantRS₀ qz97) Bool.true 759500189377543214407 295147905179352825856 3479697829428540488989 Ns408p626 (@Eq.refl Real (hardyZApproximantRS₀ qz97)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz97) (@HSub.hSub Real Real Real qz30 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz97) qz97 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz98) (Zeta.RiemannSiegel.correction qz99))) Bool.true 759500189377543214407 295147905179352825856 3479697829428540488989 Ns408p626 (BSN.hardyZApproximantRS₀_eq qz97 11 (@BSN.floor_sqrt_eq_dec qz97 765286 1000 11 qz100 rfl rfl rfl)) (@Ns408p628 759500189377543214407 295147905179352825856 3479697829428540488989 Ns408p626 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz97) qz97 11) (@HAdd.hAdd Real Real Real qz368 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz97) qz97 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz97) qz97 11)) Bool.true 379320309 134217728 157681 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz97) qz97 11) (Ns408p704 (Ns408p703 rfl) rfl rfl)) (Ns408p741 rfl) rfl rfl)) 

theorem RS409to420.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz97) Bool.true 759500189377543214407 295147905179352825856 3479697829428540488989 Ns408p626 := Ns408p742 

noncomputable def Ns408p743 := nat_lit 23058430092136939520000000 

noncomputable def Ns408p744 := nat_lit 12642410697808806810444890112 

noncomputable abbrev qz740 := (Enclosure.sfrac Bool.false 766594 1000)

noncomputable abbrev qz636 := qz740

noncomputable abbrev qz447 := qz636

noncomputable abbrev qz115 := qz447

noncomputable abbrev qz741 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 766594 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz637 := qz741

noncomputable abbrev qz448 := qz637

noncomputable abbrev qz116 := (@HPow.hPow Real Real Real qz351 qz448 qz353)

noncomputable abbrev qz742 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 766594 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz638 := qz742

noncomputable abbrev qz449 := qz638

noncomputable abbrev qz117 := qz449

noncomputable def Ns408p745 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz115) qz115 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz116) (Zeta.RiemannSiegel.correction qz117)) 34561095 33554432 78979 67108864 72770592804378323481 295147905179352825856 96299543290924852473 Ns408p743 Ns408p744 

noncomputable def Ns408p746 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz115) qz115 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 766594 1000 195 242 268435456 134217728 4503599627370496 Bool.false 391298331981 2574 

noncomputable def Ns408p747 := Ns408p746 618095470 44 84886744 8 643680110 44 80936328 8 Bool.false 136193749 135512 Bool.true 306748236 Bool.true 101880623 14148475504056880 1 Bool.false 244214142 Bool.false Bool.false 249332797 Bool.true Bool.false 138244380 

noncomputable def Ns408p748 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz115) qz115 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 766594 1000 86 144 268435456 134217728 4503599627370496 Bool.false 391298331981 2574 

noncomputable def Ns408p749 := Ns408p748 558195838 44 94906264 8 589812974 44 89478488 8 Bool.false 82492671 110556 Bool.true 348709423 Bool.true 130085339 14148475504056880 1 Bool.false 72053453 Bool.true Bool.false 237527456 Bool.false Bool.false 136193749 

noncomputable def Ns408p750 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz115) qz115 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 766594 1000 53 21 268435456 134217728 4503599627370496 Bool.false 391298331981 2574 

noncomputable def Ns408p751 := Ns408p750 480971758 44 109588312 8 522351262 44 101459064 8 Bool.false 255352102 81993 Bool.false 240424430 Bool.true 278205367 14148475504056880 1 Bool.false 209545012 Bool.true Bool.false 231008597 Bool.true Bool.false 82492671 

noncomputable def Ns408p752 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz115) qz115 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 766594 1000 251 142 268435456 134217728 4503599627370496 Bool.false 391298331981 2574 

noncomputable def Ns408p753 := Ns408p752 372130544 43 134217720 8 432030192 43 120047984 16 Bool.false 246562166 48303 Bool.false 189275239 Bool.false 231224161 14148475504056880 1 Bool.false 173976765 Bool.false Bool.false 174857032 Bool.true Bool.false 255352102 

noncomputable def Ns408p754 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz115) qz115 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 766594 1000 589 391 268435456 134217728 4503599627370496 Bool.false 391298331981 2574 

noncomputable def Ns408p755 := Ns408p754 186065264 43 189812528 16 294906480 43 154981288 8 Bool.false 268435344 2627 Bool.false 305591741 Bool.false 356739399 14148475504056880 1 Bool.false 243731797 Bool.true Bool.false 260623800 Bool.false Bool.false 246562166 

noncomputable def Ns408p756 := nat_lit 2997805552141659998481369639623852072809654166749330975 

noncomputable def Ns408p757 := nat_lit 2056531384414829453071230429645310492967689305194496 

noncomputable def Ns408p758 := nat_lit 127077535693574066512298156907520000 

noncomputable def Ns408p759 := nat_lit 584501374423447672674919439727236321280 

noncomputable abbrev qz639 := (@Eq.refl Real qz740)

noncomputable abbrev qz450 := qz639

noncomputable abbrev qz118 := qz450

noncomputable def Ns408p760 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz115 766594 1000 2350666443344 16000000 1533188 4000 2000 Ns408p758 Ns408p759 qz118 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns408p761 := nat_lit 61395057707861196768898450219496490451141717335026298368000 

noncomputable abbrev qz640 := (@HSub.hSub Real Real Real qz718 qz719 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz720 (@Nat.cast Real Real.instNatCast 1533188))))

noncomputable abbrev qz451 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 766594 4000) (Real.log (Enclosure.sfrac Bool.false 2350666443344 16000000))) (@HMul.hMul Real Real Real qz579 qz585 qz640))

noncomputable abbrev qz641 := (Enclosure.sfrac Bool.false 766594 2000)

noncomputable abbrev qz119 := (@HSub.hSub Real Real Real qz356 (@HSub.hSub Real Real Real qz356 qz451 qz641) (@HMul.hMul Real Real Real qz350 qz641 (Real.log Real.pi)))

noncomputable def Ns408p762 := @Enclosure.Real.IsNear.addLit_ft_p qz119 (Enclosure.sfrac Bool.true Ns408p758 Ns408p759) 105038361843584691475 72057594037927936 19629145375268301 2048000000000000000000 Ns408p758 Ns408p759 0 1 Ns408p761 

noncomputable def Ns408p763 := nat_lit 440562821233994645792358400000000 

noncomputable abbrev qz120 := (@HSub.hSub Real Real Real qz356 qz451 qz641)

noncomputable def Ns408p764 := @Enclosure.Real.IsNear.subLit_ff_p qz120 (@HMul.hMul Real Real Real qz4 qz641 (Real.log Real.pi)) 17081897826343948141127 9007199254740992000 7745946516299 2000000000000000000 14722729459017 33554432000 383297 67108864000 Ns408p763 105038361843584691475 72057594037927936 

noncomputable def Ns408p765 := nat_lit 34163795652687896282254000 

noncomputable abbrev qz121 := qz451

noncomputable def Ns408p766 := @Enclosure.Real.IsNear.subLit_ff_p qz121 qz641 20534330279088406151751 9007199254740992000 7745946516299 2000000000000000000 766594 2000 0 1 Ns408p765 17081897826343948141127 9007199254740992000 7745946516299 2000000000000000000 

noncomputable def Ns408p767 := nat_lit 46239201096602619538065723561238069248 

noncomputable def Ns408p768 := nat_lit 57533363485892304638574592 

noncomputable def Ns408p769 := nat_lit 5870559099317956065411932030176918572763270113853440 

noncomputable def Ns408p770 := nat_lit 6369645115165001581168787791066199971971602055168 

noncomputable def Ns408p771 := nat_lit 12391734034644120793832781680724875323590770688 

noncomputable def Ns408p772 := BSN.log_dyadic_bound 253514443344 4447818443344 3 2 Ns408p769 134217728 50000000 Ns408p770 Ns408p771 15316745 4701332886688 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 253514443344) (BSN.artanhQ 4447818443344) 0 2 Ns408p770 Ns408p769 Ns408p771 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz452 := (Real.log (Enclosure.sfrac Bool.false 2350666443344 16000000))

noncomputable def Ns408p773 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 766594 4000) qz452 766594 4000 0 1 53582120207969383 4503599627370496 20000017 1000000000000000 20537865929354040595751 9007199254740992000 7665946516049 2000000000000000000 (Enclosure.Real.IsNear.const Bool.false 766594 4000) (BSN.isNear_log_sfrac 2350666443344 16000000 53582120207969383 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2350666443344) qz359)) Bool.false Ns408p768 Ns408p100 1000000850000000 50000000000000000000000 53582120207969383 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2350666443344 16000000 17 4701332886688 4194304000000 15316745 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns408p772 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns408p774 := BSN.arctan_dyadic_bound_f 1000 1533188 1 0 16777216 6250000 0 1 1 0 1 1 10942 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1533188) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1533188) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns408p775 := @Enclosure.Real.IsNear.subLit_ff_p qz12 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz13 (@Nat.cast Real Real.instNatCast 1533188))) 884279719003555 562949953421312 1 2000000000000000 10942 16777216 1 6250000 14829592051751611006976 883912566408611 562949953421312 320000001 2000000000000000 qz14 (Ns408p774 rfl) rfl rfl 

noncomputable abbrev qz453 := (@HMul.hMul Real Real Real qz579 qz585 qz640)

noncomputable abbrev qz122 := qz453

noncomputable abbrev qz454 := qz640

noncomputable abbrev qz123 := qz454

noncomputable def Ns408p776 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 766594 4000) qz452) qz122 20537865929354040595751 9007199254740992000 7665946516049 2000000000000000000 883912566408611 2251799813685248 320000001 8000000000000000 Ns408p767 20534330279088406151751 9007199254740992000 7745946516299 2000000000000000000 (Ns408p773 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz16 qz123 1 4 0 1 883912566408611 562949953421312 320000001 2000000000000000 883912566408611 2251799813685248 320000001 8000000000000000 qz367 Ns408p775 rfl) 

noncomputable def Ns408p777 := @Ns408p762 Ns408p756 Ns408p757 19629145375268301 2048000000000000000000 (@Ns408p764 19629145375268301 2048000000000000000000 (Ns408p766 (Ns408p776 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 766594 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz641 (Real.log Real.pi) 766594 2000 0 1 38410761 33554432 1 67108864 14722729459017 33554432000 383297 67108864000 (Enclosure.Real.IsNear.const Bool.false 766594 2000) RS409to420.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns408p758 Ns408p759) 

noncomputable def Ns408p778 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz115) Bool.false Ns408p756 Ns408p757 19629145375268301 2048000000000000000000 48912291497 33554432 323 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz115) (@HAdd.hAdd Real Real Real qz368 qz119 (Enclosure.sfrac Bool.true Ns408p758 Ns408p759)) Bool.false Ns408p756 Ns408p757 19629145375268301 2048000000000000000000 Ns408p760 (Ns408p777 rfl rfl)) 

noncomputable def Ns408p779 := BSN.cos_dyadic_bound_f 61067484 68719476736 1 0 33554432 12512208 0 1 1 0 1 1 33554418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 61067484) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 61067484) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns408p780 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz115) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48912291497) qz418) Bool.false 48912291497 33554432 323 33554432 Bool.false 33554418 33554432 1 6250000 (Ns408p778 rfl) (Enclosure.sfrac_false_div 48912291497 33554432) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48912291497) qz418) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4297242196827862728704) qz430) 226375608064910080 72057594037927936 Bool.false 33554418 33554432 232 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q0 48912291497 33554432 226375608064910080 72057594037927936 232 4297242196827862728704 Ns408p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554418 33554432 4297242196827862728704 Ns408p100 61067484 68719476736 12512208 12500000 (Ns408p779 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns408p781 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz115) Bool.false Ns408p756 Ns408p757 19629145375268301 2048000000000000000000 391298331981 268435456 2574 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz115) (@HAdd.hAdd Real Real Real qz368 qz119 (Enclosure.sfrac Bool.true Ns408p758 Ns408p759)) Bool.false Ns408p756 Ns408p757 19629145375268301 2048000000000000000000 Ns408p760 (Ns408p777 rfl rfl)) 

noncomputable def Ns408p782 := Ns408p755 48303 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 589 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 243731797 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 391 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 260623800 268435456) qz118 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz115) qz115 1) Bool.false 16777209 16777216 128269027 13107200000000 268435344 268435456 2627 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz115) qz115 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz115)) Bool.false 16777209 16777216 128269027 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz115) qz115) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz115)) Bool.false 33554418 33554432 2052304432 209715200000000 16777209 16777216 128269027 13107200000000 (Ns408p780 rfl rfl) rfl)) rfl) (Ns408p781 rfl) RS409to420.d7 

noncomputable def Ns408p783 := nat_lit 137008938928654901607519561216506950090493121083897839659182812249743265 

noncomputable def Ns408p784 := nat_lit 76055898562607741738268047336242551484091608497281482115316406050721 

noncomputable def Ns408p785 := nat_lit 358709797167851948818784512061830952772698216425022552898244472187150241 

noncomputable def Ns408p786 := BSN.sin_dyadic_bound_f 305591741 268435456 3 2 268435456 134217728 Ns408p783 Ns408p142 Ns408p784 Ns408p785 Ns408p145 Ns408p784 243731797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 305591741) qz372 0 2 Ns408p783 Ns408p142 Ns408p784 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 305591741) qz373 0 2 Ns408p785 Ns408p145 Ns408p784 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p787 := nat_lit 22681419087031303417670023674706185842857688629301001349997486749062364773894809553331006600697841082915316001 

noncomputable def Ns408p788 := nat_lit 4248277876629210901920137176933987523576424828129110455615956232331881828155075890090127557059054887201 

noncomputable def Ns408p789 := nat_lit 113334839456198531539536913683367284734592916651092286283651254742160453189369851557847568028005195137227907361 

noncomputable def Ns408p790 := BSN.sin_dyadic_bound_f 356739399 268435456 4 3 268435456 134217728 Ns408p787 Ns408p269 Ns408p788 Ns408p789 Ns408p272 Ns408p788 260623800 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 356739399) qz372 0 3 Ns408p787 Ns408p269 Ns408p788 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 356739399) qz373 0 3 Ns408p789 Ns408p272 Ns408p788 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p791 := nat_lit 20153571102310223271916278084551003516246711601987207108567965695863745 

noncomputable def Ns408p792 := nat_lit 1647215521619276321827289156131873413369394438921682548799306066881 

noncomputable def Ns408p793 := nat_lit 52780495490444153550497769848523652842738789461827288274503758898392001 

noncomputable def Ns408p794 := BSN.sin_dyadic_bound_f 189275239 268435456 3 2 268435456 134217728 Ns408p791 Ns408p142 Ns408p792 Ns408p793 Ns408p145 Ns408p792 173976765 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 189275239) qz372 0 2 Ns408p791 Ns408p142 Ns408p792 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 189275239) qz373 0 2 Ns408p793 Ns408p145 Ns408p792 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p795 := nat_lit 24942727159380699653937417912143406606379418545137653610753518398114561 

noncomputable def Ns408p796 := nat_lit 8170821033948311878602651665999181014089811527601335640251382926081 

noncomputable def Ns408p797 := nat_lit 74811839836074202338055048433098221457110076012357758160980052428491521 

noncomputable def Ns408p798 := BSN.cos_dyadic_bound_f 231224161 268435456 3 2 268435456 134217728 Ns408p795 Ns408p123 Ns408p796 Ns408p797 Ns408p126 Ns408p796 174857032 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 231224161) qz370 0 2 Ns408p795 Ns408p123 Ns408p796 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 231224161) qz371 0 2 Ns408p797 Ns408p126 Ns408p796 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p799 := Ns408p753 81993 BSN.abs_quadSignPos (BSN.cos_quad_nat3 251 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 173976765 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 142 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 174857032 268435456) qz118 rfl rfl (Ns408p782 RS409to420.d9 RS409to420.d11 RS409to420.d13 RS409to420.d17 (Ns408p786 rfl rfl) (Ns408p790 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns408p781 rfl) RS409to420.d19 RS409to420.d21 RS409to420.d23 RS409to420.d25 RS409to420.d17 (Ns408p794 rfl rfl) (Ns408p798 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns408p800 := nat_lit 52474473511783520247052037268859075546939993061776124879960243643040000 

noncomputable def Ns408p801 := nat_lit 11164229632281161335728195507569245651130310453058659049200100000000 

noncomputable def Ns408p802 := nat_lit 137415069492409335909640347197142466701407675611537279713816218903200000 

noncomputable def Ns408p803 := BSN.sin_dyadic_bound_f 240424430 268435456 3 2 268435456 134217728 Ns408p800 Ns408p142 Ns408p801 Ns408p802 Ns408p145 Ns408p801 209545012 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 240424430) qz372 0 2 Ns408p800 Ns408p142 Ns408p801 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 240424430) qz373 0 2 Ns408p802 Ns408p145 Ns408p801 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p804 := nat_lit 94095526934678675584199738442483568670959413633809726784376069765065025 

noncomputable def Ns408p805 := nat_lit 35885915605325766094460589321694547815173286510666445093285597931841 

noncomputable def Ns408p806 := nat_lit 246382564775083146718274950204745650584621517053246300667024386988042561 

noncomputable def Ns408p807 := BSN.sin_dyadic_bound_f 278205367 268435456 3 2 268435456 134217728 Ns408p804 Ns408p142 Ns408p805 Ns408p806 Ns408p145 Ns408p805 231008597 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 278205367) qz372 0 2 Ns408p804 Ns408p142 Ns408p805 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 278205367) qz373 0 2 Ns408p806 Ns408p145 Ns408p805 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p808 := Ns408p751 110556 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 209545012 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 231008597 268435456) qz118 rfl rfl (Ns408p799 rfl rfl) (Ns408p781 rfl) RS409to420.d27 RS409to420.d29 RS409to420.d31 RS409to420.d33 RS409to420.d17 (Ns408p803 rfl rfl) (Ns408p807 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p809 := nat_lit 7969575581821669471484554429496414625170248540845852194852039650764258778979169280027571893471995888056203201 

noncomputable def Ns408p810 := nat_lit 3232691036898400092967323959709564473201223724261592437344937179873339552306472426217730423258234025921 

noncomputable def Ns408p811 := nat_lit 48294198488417659389402428356952493943002424110815416016277489832084278128897157400812113482883796002011936705 

noncomputable def Ns408p812 := BSN.cos_dyadic_bound_f 348709423 268435456 4 3 268435456 134217728 Ns408p809 Ns408p252 Ns408p810 Ns408p811 Ns408p255 Ns408p810 72053453 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 348709423) qz370 0 3 Ns408p809 Ns408p252 Ns408p810 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 348709423) qz371 0 3 Ns408p811 Ns408p255 Ns408p810 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p813 := nat_lit 2498023186223895827218950938137119921640821720052950918876146752078561 

noncomputable def Ns408p814 := nat_lit 82002449316419066870375865648252747656912437270050846707100730081 

noncomputable def Ns408p815 := nat_lit 7493905553773054643523112062680063259427151335284312654935026054775521 

noncomputable def Ns408p816 := BSN.cos_dyadic_bound_f 130085339 268435456 3 2 268435456 134217728 Ns408p813 Ns408p123 Ns408p814 Ns408p815 Ns408p126 Ns408p814 237527456 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 130085339) qz370 0 2 Ns408p813 Ns408p123 Ns408p814 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 130085339) qz371 0 2 Ns408p815 Ns408p126 Ns408p814 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p817 := Ns408p749 135512 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 72053453 268435456) BSN.abs_quadSignPos qz606 (BSN.sfrac_eq_quadSignPos_mul Bool.false 237527456 268435456) qz118 rfl rfl (Ns408p808 rfl) (Ns408p781 rfl) RS409to420.d35 RS409to420.d37 RS409to420.d39 RS409to420.d41 RS409to420.d17 (Ns408p812 rfl rfl) (Ns408p816 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p818 := nat_lit 139095928557797247193933482496878260107632056787257694938137759248875520 

noncomputable def Ns408p819 := nat_lit 78389264831648032640037100646047975602704005391655200395547660845056 

noncomputable def Ns408p820 := nat_lit 364171944555932026788408584566968508321393866053136044989720387534258176 

noncomputable def Ns408p821 := BSN.sin_dyadic_bound_f 306748236 268435456 3 2 268435456 134217728 Ns408p818 Ns408p142 Ns408p819 Ns408p820 Ns408p145 Ns408p819 244214142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 306748236) qz372 0 2 Ns408p818 Ns408p142 Ns408p819 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 306748236) qz373 0 2 Ns408p820 Ns408p145 Ns408p819 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p822 := nat_lit 939811008887614488458408090123961323860227518990458809345948442911361 

noncomputable def Ns408p823 := nat_lit 11607340806739173178639755045633383510087014894213197076837130881 

noncomputable def Ns408p824 := nat_lit 2819409811981229987028866990861792704813662382941588001643691654472321 

noncomputable def Ns408p825 := BSN.cos_dyadic_bound_f 101880623 268435456 3 2 268435456 134217728 Ns408p822 Ns408p123 Ns408p823 Ns408p824 Ns408p126 Ns408p823 249332797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 101880623) qz370 0 2 Ns408p822 Ns408p123 Ns408p823 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 101880623) qz371 0 2 Ns408p824 Ns408p126 Ns408p823 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p826 := Ns408p747 157958 BSN.abs_quadSignPos qz415 (BSN.sfrac_eq_quadSignPos_mul Bool.false 244214142 268435456) BSN.abs_quadSignNeg qz395 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 249332797 268435456) qz118 rfl rfl (Ns408p817 rfl) (Ns408p781 rfl) RS409to420.d43 RS409to420.d45 RS409to420.d52 RS409to420.d54 RS409to420.d17 (Ns408p821 rfl rfl) (Ns408p825 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p827 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz115) qz115 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz115) qz115 11) 138244380 268435456 157958 268435456 138244380 268435456 157958 268435456 74219386369474560 34561095 33554432 78979 67108864 (Ns408p826 rfl) 

noncomputable def Ns408p828 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz4 qz33 qz116) (Zeta.RiemannSiegel.correction qz117) 10096097 33554432 1 33554432 7207794537273 8796093022208 4741259164813 343597383680000000 72770592804378323481 295147905179352825856 

noncomputable def Ns408p829 := @Enclosure.Real.IsNear.mulLit_tf qz33 qz116 1 1 0 1 10096097 33554432 1 33554432 10096097 33554432 1 33554432 

noncomputable abbrev qz124 := qz448

noncomputable def Ns408p830 := @Enclosure.Real.IsNear.sqrt_image qz124 2046941283841 16777216000 383297 16777216000 185315864 185315900 16777216 (@Enclosure.Real.IsNear.of_eq qz124 (@HMul.hMul Real Real Real qz4 qz115 qz2) Bool.false 2046941283841 16777216000 383297 16777216000 (BSN.t_div_two_pi_mk qz115 766594 1000 qz118) (@Enclosure.Real.IsNear.mulLit_ff qz115 qz2 766594 1000 0 1 5340353 33554432 1 33554432 2046941283841 16777216000 383297 16777216000 (Enclosure.Real.IsNear.const Bool.false 766594 1000) RS409to420.d48 rfl)) 

noncomputable abbrev qz743 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 766594 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz642 := qz743

noncomputable abbrev qz455 := qz642

noncomputable abbrev qz125 := qz455

noncomputable def Ns408p831 := @Enclosure.Real.IsNear.sqrt_image qz125 92657941 8388608 9 8388608 55759163 55759169 16777216 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 370631764 33554432 36 33554432 92657941 8388608 9 8388608 (Ns408p830 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns408p832 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz125) 27879583 8388608 3 16777216 5048048 5048049 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz125) Bool.false 111518332 33554432 6 33554432 27879583 8388608 3 16777216 (Ns408p831 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns408p833 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 10096097 33554432 1 33554432 10096097 33554432 1 33554432 (Ns408p832 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz126 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz449))

noncomputable abbrev qz643 := (@HMul.hMul Real Real Real qz714 qz742 qz742)

noncomputable abbrev qz456 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz643 qz638) qz598)

noncomputable abbrev qz127 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz456))

noncomputable def Ns408p834 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz117) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv qz126) qz127) Bool.false 7207794537273 

noncomputable def Ns408p835 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz126) qz127 34986067 33554432 253 

noncomputable def Ns408p836 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz126) Bool.false 34986067 33554432 253 33554432 34986067 33554432 253 

noncomputable def Ns408p837 := @Enclosure.Real.IsNear.recentre' qz126 Bool.false 16090690 16777216 1452304432 209715200000000 8045345 8388608 90769027 13107200000000 

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz350 qz347 qz449)

noncomputable def Ns408p838 := @Enclosure.Real.IsNear.cos_image qz128 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4816099) qz369) Bool.false 4816099 16777216 227 33554432 Bool.false 16090690 16777216 1 

noncomputable def Ns408p839 := nat_lit 242874678684688527298708479 

noncomputable def Ns408p840 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz117 884279719003555 140737488355328 1 500000000000000 383253 8388608 9 8388608 338902855147269464415 1180591620717411303424 Ns408p839 

noncomputable def Ns408p841 := @Enclosure.Real.IsNear.subLit_ff_p qz125 qz31 92657941 8388608 9 8388608 11 1 0 1 383253 383253 8388608 9 

noncomputable def Ns408p842 := @Ns408p841 8388608 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 370631764 33554432 36 33554432 92657941 8388608 9 8388608 (Ns408p830 rfl rfl rfl rfl rfl rfl) rfl) qz398 

noncomputable def Ns408p843 := @Enclosure.Real.IsNear.recentre' qz128 Bool.false 338902855147269464415 1180591620717411303424 Ns408p839 Ns408p171 4816099 16777216 227 33554432 (@Ns408p840 Ns408p171 RS409to420.d47 (Ns408p842 rfl rfl) rfl) 

noncomputable def Ns408p844 := nat_lit 537999191350449003871995601 

noncomputable def Ns408p845 := BSN.cos_dyadic_bound_f 4816099 16777216 2 1 16777216 6250000 Ns408p844 Ns408p196 Ns408p844 Ns408p844 Ns408p197 Ns408p844 16090690 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4816099) (BSN.cosEvenQ 16777216) 0 1 Ns408p844 Ns408p196 Ns408p844 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4816099) (BSN.cosOddQ 16777216) 0 1 Ns408p844 Ns408p197 Ns408p844 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p846 := @Enclosure.Real.IsNear.inv_image qz126 8045345 8388608 90769027 13107200000000 17492907 17493160 16777216 (Ns408p837 (@Ns408p838 6250000 (Ns408p843 rfl) (Enclosure.sfrac_false_div 4816099 16777216) (Ns408p845 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns408p847 := @Enclosure.Real.IsNear.recentre' qz127 Bool.false 13185216 16777216 

noncomputable abbrev qz129 := (@HMul.hMul Real Real Real qz350 qz347 qz456)

noncomputable def Ns408p848 := @Enclosure.Real.IsNear.cos_image qz129 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 22368923)) qz418) Bool.true 22368923 33554432 

noncomputable def Ns408p849 := nat_lit 6602140998971079898424917045 

noncomputable def Ns408p850 := nat_lit 2223547556977795443810397993261517 

noncomputable def Ns408p851 := @Enclosure.Real.IsNear.recentre' qz129 Bool.true Ns408p849 Ns408p609 Ns408p850 

noncomputable abbrev qz130 := qz456

noncomputable def Ns408p852 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz130 884279719003555 140737488355328 1 500000000000000 7466122830919 

noncomputable abbrev qz457 := (@HSub.hSub Real Real Real qz584 qz643 qz638)

noncomputable abbrev qz131 := qz457

noncomputable def Ns408p853 := @Enclosure.Real.IsNear.subLit_tf qz131 qz28 3068076319815 70368744177664 82396107 70368744177664 1 16 

noncomputable abbrev qz458 := qz643

noncomputable abbrev qz132 := qz458

noncomputable def Ns408p854 := @Enclosure.Real.IsNear.subLit_ff_n qz132 qz117 146882862009 70368744177664 6898635 70368744177664 383253 8388608 9 8388608 

noncomputable def Ns408p855 := @Enclosure.Real.IsNear.mulLit_ff qz117 qz117 383253 8388608 9 8388608 383253 8388608 9 8388608 146882862009 70368744177664 

noncomputable def Ns408p856 := nat_lit 533261463709578842362461368058929522994666513743017238869390561 

noncomputable def Ns408p857 := nat_lit 62684562117670119947734460584603316810320833686623625491681 

noncomputable def Ns408p858 := nat_lit 1599659022004501186847488635255619362350378899561678469357188321 

noncomputable def Ns408p859 := BSN.cos_dyadic_bound_f 22368923 33554432 3 2 16777216 6250000 Ns408p856 Ns408p489 Ns408p857 Ns408p858 Ns408p492 Ns408p857 13185216 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 22368923) qz619 0 2 Ns408p856 Ns408p489 Ns408p857 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 22368923) (BSN.cosOddQ 33554432) 0 2 Ns408p858 Ns408p492 Ns408p857 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p860 := @Ns408p847 197944304 26214400000000 206019 262144 12371519 1638400000000 (@Ns408p848 31 4194304 Bool.false 13185216 16777216 1 6250000 (@Ns408p851 Ns408p612 22368923 33554432 31 4194304 (@Ns408p852 70368744177664 82396107 70368744177664 Ns408p849 Ns408p609 Ns408p850 Ns408p612 RS409to420.d47 (@Ns408p853 0 1 119457965294704 7466122830919 70368744177664 82396107 70368744177664 (@Ns408p854 25736889561010667520 3068076319815 70368744177664 82396107 70368744177664 (@Ns408p855 6898635 70368744177664 (Ns408p842 rfl rfl) (Ns408p842 rfl rfl) rfl) (Ns408p842 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 22368923 33554432) (BSN.cos_neg_of_bound 22368923 33554432 Bool.false 13185216 16777216 1 6250000 (Ns408p859 rfl rfl)) rfl rfl) 

noncomputable def Ns408p861 := @Ns408p828 96299543290924852473 Ns408p743 (Ns408p829 qz51 (@Enclosure.Real.IsNear.of_eq qz116 (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 10096097 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz124 (BSN.t_div_two_pi_nonneg qz115 766594 1000 qz118)) Ns408p833) rfl) (@Ns408p834 8796093022208 4741259164813 343597383680000000 (BSN.correction_mk qz117 (BSN.cos_two_pi_p_ne_zero_mk qz115 766594 1000 11 qz118 rfl rfl (@BSN.floor_sqrt_eq_dec qz115 766594 1000 11 qz118 rfl rfl rfl))) (@Ns408p835 33554432 206019 262144 12371519 1638400000000 7207794537273 8796093022208 4741259164813 343597383680000000 (@Ns408p836 33554432 (Ns408p846 rfl rfl rfl rfl rfl) rfl) (Ns408p860 rfl) rfl)) 

noncomputable def Ns408p862 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz115) (hardyZApproximantRS₀ qz115) Bool.false 376773199373746121241 295147905179352825856 27233277308953644852473 Ns408p743 (@Eq.refl Real (hardyZApproximantRS₀ qz115)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz115) (@HSub.hSub Real Real Real qz30 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz115) qz115 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz116) (Zeta.RiemannSiegel.correction qz117))) Bool.false 376773199373746121241 295147905179352825856 27233277308953644852473 Ns408p743 (BSN.hardyZApproximantRS₀_eq qz115 11 (@BSN.floor_sqrt_eq_dec qz115 766594 1000 11 qz118 rfl rfl rfl)) (@Ns408p745 376773199373746121241 295147905179352825856 27233277308953644852473 Ns408p743 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz115) qz115 11) (@HAdd.hAdd Real Real Real qz368 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz115) qz115 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz115) qz115 11)) Bool.false 34561095 33554432 78979 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz115) qz115 11) (Ns408p827 (Ns408p826 rfl) rfl rfl)) (Ns408p861 rfl) rfl rfl)) 

theorem RS409to420.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz115) Bool.false 376773199373746121241 295147905179352825856 27233277308953644852473 Ns408p743 := Ns408p862 

noncomputable def Ns408p863 := nat_lit 18446744073709551616000000 

noncomputable def Ns408p864 := nat_lit 172226952125327359816750858240 

noncomputable abbrev qz744 := (Enclosure.sfrac Bool.false 767901 1000)

noncomputable abbrev qz644 := qz744

noncomputable abbrev qz459 := qz644

noncomputable abbrev qz133 := qz459

noncomputable abbrev qz745 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 767901 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz645 := qz745

noncomputable abbrev qz460 := qz645

noncomputable abbrev qz134 := (@HPow.hPow Real Real Real qz351 qz460 qz353)

noncomputable abbrev qz746 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 767901 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz646 := qz746

noncomputable abbrev qz461 := qz646

noncomputable abbrev qz135 := qz461

noncomputable def Ns408p865 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz133) qz133 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz134) (Zeta.RiemannSiegel.correction qz135)) 178149345 134217728 158221 134217728 283827422693132564305 1180591620717411303424 78939676527679239503 Ns408p863 Ns408p864 

noncomputable def Ns408p866 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz133) qz133 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 767901 1000 195 242 268435456 134217728 4503599627370496 Bool.false 392141225700 2578 

noncomputable def Ns408p867 := Ns408p866 618095470 44 84886744 8 643680110 44 80936328 8 Bool.true 174777970 135737 Bool.true 271705296 Bool.true 100276808 14148475504056880 1 Bool.false 227630548 Bool.false Bool.false 249922538 Bool.true Bool.true 178149345 

noncomputable def Ns408p868 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz133) qz133 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 767901 1000 86 144 268435456 134217728 4503599627370496 Bool.false 392141225700 2578 

noncomputable def Ns408p869 := Ns408p868 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 201470665 110738 Bool.true 235377665 Bool.true 58077177 14148475504056880 1 Bool.false 171684795 Bool.true Bool.false 262177300 Bool.false Bool.true 174777970 

noncomputable def Ns408p870 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz133) qz133 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 767901 1000 54 21 268435456 134217728 4503599627370496 Bool.false 392141225700 2578 

noncomputable def Ns408p871 := Ns408p870 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 49525228 82127 Bool.false 33030633 Bool.true 118024747 14148475504056880 1 Bool.false 266405830 Bool.true Bool.false 114258667 Bool.true Bool.true 201470665 

noncomputable def Ns408p872 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz133) qz133 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 767901 1000 252 143 268435456 134217728 4503599627370496 Bool.false 392141225700 2578 

noncomputable def Ns408p873 := Ns408p872 372130544 43 134217720 8 432030192 43 120047984 16 Bool.true 208212945 48380 Bool.false 124136908 Bool.false 87796990 14148475504056880 1 Bool.false 240240045 Bool.false Bool.false 86240004 Bool.false Bool.true 49525228 

noncomputable def Ns408p874 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz133) qz133 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 767901 1000 591 392 268435456 134217728 4503599627370496 Bool.false 392141225700 2578 

noncomputable def Ns408p875 := Ns408p874 186065264 43 189812528 16 294906480 43 154981288 8 Bool.true 268435392 2627 Bool.false 61983303 Bool.false 392532921 14148475504056880 1 Bool.false 61433970 Bool.false Bool.false 29067400 Bool.false Bool.true 208212945 

noncomputable def Ns408p876 := nat_lit 5395781322634130907510388928699567396170756254948033872771 

noncomputable def Ns408p877 := nat_lit 3693615781484728125451183831948206619857079012163584000 

noncomputable def Ns408p878 := nat_lit 128164536003162617818932114960480000 

noncomputable def Ns408p879 := nat_lit 590506169000138803132327582679541314880 

noncomputable abbrev qz647 := (@Eq.refl Real qz744)

noncomputable abbrev qz462 := qz647

noncomputable abbrev qz136 := qz462

noncomputable def Ns408p880 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz133 767901 1000 2358688783204 16000000 1535802 4000 2000 Ns408p878 Ns408p879 qz136 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns408p881 := nat_lit 15539850209186297013629920114654754100971778014250337553580480 

noncomputable abbrev qz648 := (@HSub.hSub Real Real Real qz718 qz719 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz720 (@Nat.cast Real Real.instNatCast 1535802))))

noncomputable abbrev qz463 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 767901 4000) (Real.log (Enclosure.sfrac Bool.false 2358688783204 16000000))) (@HMul.hMul Real Real Real qz579 qz585 qz648))

noncomputable abbrev qz649 := (Enclosure.sfrac Bool.false 767901 2000)

noncomputable abbrev qz137 := (@HSub.hSub Real Real Real qz356 (@HSub.hSub Real Real Real qz356 qz463 qz649) (@HMul.hMul Real Real Real qz350 qz649 (Real.log Real.pi)))

noncomputable def Ns408p882 := @Enclosure.Real.IsNear.addLit_ft_p qz137 (Enclosure.sfrac Bool.true Ns408p878 Ns408p879) 26316156094195978827371 18014398509481984000 39324944607898233 4096000000000000000000 Ns408p878 Ns408p879 0 1 Ns408p881 

noncomputable def Ns408p883 := nat_lit 1766047340328169132472919916544000 

noncomputable abbrev qz138 := (@HSub.hSub Real Real Real qz356 qz463 qz649)

noncomputable def Ns408p884 := @Enclosure.Real.IsNear.subLit_ff_p qz138 (@HMul.hMul Real Real Real qz4 qz649 (Real.log Real.pi)) 34233837514846357255787 18014398509481984000 15518033054817 4000000000000000000 29495661782661 67108864000 767901 134217728000 Ns408p883 26316156094195978827371 18014398509481984000 

noncomputable def Ns408p885 := nat_lit 68467675029692714511574000 

noncomputable abbrev qz139 := qz463

noncomputable def Ns408p886 := @Enclosure.Real.IsNear.subLit_ff_p qz139 qz649 41150474829761219753579 18014398509481984000 15518033054817 4000000000000000000 767901 2000 0 1 Ns408p885 34233837514846357255787 18014398509481984000 15518033054817 4000000000000000000 

noncomputable def Ns408p887 := nat_lit 92662631554715802051905314594427502592 

noncomputable def Ns408p888 := nat_lit 57549838662135542443933696 

noncomputable def Ns408p889 := nat_lit 5913027730335622753110205977870824312490680153091840 

noncomputable def Ns408p890 := nat_lit 6804428948011784674214149731824368242545916315648 

noncomputable def Ns408p891 := nat_lit 14036291079403961339770790695301120417758618368 

noncomputable def Ns408p892 := BSN.log_dyadic_bound 261536783204 4455840783204 3 2 Ns408p889 134217728 50000000 Ns408p890 Ns408p891 15774023 4717377566408 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 261536783204) (BSN.artanhQ 4455840783204) 0 2 Ns408p890 Ns408p889 Ns408p891 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz464 := (Real.log (Enclosure.sfrac Bool.false 2358688783204 16000000))

noncomputable def Ns408p893 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 767901 4000) qz464 767901 4000 0 1 53597463911525479 4503599627370496 20000017 1000000000000000 41157546135124326849579 18014398509481984000 15358033054317 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 767901 4000) (BSN.isNear_log_sfrac 2358688783204 16000000 53597463911525479 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2358688783204) qz359)) Bool.false Ns408p888 Ns408p100 1000000850000000 50000000000000000000000 53597463911525479 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2358688783204 16000000 17 4717377566408 4194304000000 15774023 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns408p892 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns408p894 := BSN.arctan_dyadic_bound_f 1000 1535802 1 0 16777216 6250000 0 1 1 0 1 1 10924 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1535802) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1535802) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns408p895 := @Enclosure.Real.IsNear.subLit_ff_p qz12 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz13 (@Nat.cast Real Real.instNatCast 1535802))) 884279719003555 562949953421312 1 2000000000000000 10924 16777216 1 6250000 14829602184850772590592 883913170388387 562949953421312 320000001 2000000000000000 qz14 (Ns408p894 rfl) rfl rfl 

noncomputable abbrev qz465 := (@HMul.hMul Real Real Real qz579 qz585 qz648)

noncomputable abbrev qz140 := qz465

noncomputable abbrev qz466 := qz648

noncomputable abbrev qz141 := qz466

noncomputable def Ns408p896 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 767901 4000) qz464) qz140 41157546135124326849579 18014398509481984000 15358033054317 4000000000000000000 883913170388387 2251799813685248 320000001 8000000000000000 Ns408p887 41150474829761219753579 18014398509481984000 15518033054817 4000000000000000000 (Ns408p893 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz16 qz141 1 4 0 1 883913170388387 562949953421312 320000001 2000000000000000 883913170388387 2251799813685248 320000001 8000000000000000 qz367 Ns408p895 rfl) 

noncomputable def Ns408p897 := @Ns408p882 Ns408p876 Ns408p877 39324944607898233 4096000000000000000000 (@Ns408p884 39324944607898233 4096000000000000000000 (Ns408p886 (Ns408p896 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 767901 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz649 (Real.log Real.pi) 767901 2000 0 1 38410761 33554432 1 67108864 29495661782661 67108864000 767901 134217728000 (Enclosure.Real.IsNear.const Bool.false 767901 2000) RS409to420.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns408p878 Ns408p879) 

noncomputable def Ns408p898 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz133) Bool.false Ns408p876 Ns408p877 39324944607898233 4096000000000000000000 12254413303 8388608 323 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz133) (@HAdd.hAdd Real Real Real qz368 qz137 (Enclosure.sfrac Bool.true Ns408p878 Ns408p879)) Bool.false Ns408p876 Ns408p877 39324944607898233 4096000000000000000000 Ns408p880 (Ns408p897 rfl rfl)) 

noncomputable def Ns408p899 := nat_lit 1898153917035968940998656 

noncomputable def Ns408p900 := nat_lit 3504746002980257575479488458392640272693628249870026507450469685618361766968111666324909112615300729378765084596082569909846178179240165376 

noncomputable def Ns408p901 := nat_lit 2489656293281710037254492887341209834626516727569342987645991948236928982946172718408993257162999446225935381992154183505623463755776 

noncomputable def Ns408p902 := nat_lit 17501992252968444731290012939428472364264580186558184262773508473818737747164827433467513732744753750553348841234060093082587540051917275136 

noncomputable def Ns408p903 := BSN.sin_dyadic_bound_f 107897558168 68719476736 4 3 33554432 12512208 Ns408p900 Ns408p114 Ns408p901 Ns408p902 Ns408p117 Ns408p901 33554424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107897558168) qz591 0 3 Ns408p900 Ns408p114 Ns408p901 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107897558168) qz592 0 3 Ns408p902 Ns408p117 Ns408p901 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p904 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz133) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12254413303) qz377) Bool.false 12254413303 8388608 323 33554432 Bool.true 33554424 33554432 1 6250000 (Ns408p898 rfl) (Enclosure.sfrac_false_div 12254413303 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12254413303) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns408p899) (@Nat.cast Real Real.instNatCast Ns408p177)) 226375608064910080 72057594037927936 Bool.false 33554424 33554432 232 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q1 12254413303 8388608 226375608064910080 72057594037927936 232 Ns408p899 Ns408p177 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554424 33554432 Ns408p899 Ns408p177 107897558168 68719476736 12512208 12500000 (Ns408p903 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns408p905 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz133) Bool.false Ns408p876 Ns408p877 39324944607898233 4096000000000000000000 392141225700 268435456 2578 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz133) (@HAdd.hAdd Real Real Real qz368 qz137 (Enclosure.sfrac Bool.true Ns408p878 Ns408p879)) Bool.false Ns408p876 Ns408p877 39324944607898233 4096000000000000000000 Ns408p880 (Ns408p897 rfl rfl)) 

noncomputable def Ns408p906 := Ns408p875 48380 BSN.abs_quadSignPos (BSN.cos_quad_nat3 591 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 61433970 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 392 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 29067400 268435456) qz136 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz133) qz133 1) Bool.true 4194303 4194304 128269027 13107200000000 268435392 268435456 2627 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz133) qz133 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz133)) Bool.true 4194303 4194304 128269027 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz133) qz133) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz133)) Bool.true 33554424 33554432 2052304432 209715200000000 4194303 4194304 128269027 13107200000000 (Ns408p904 rfl rfl) rfl)) rfl) (Ns408p905 rfl) RS409to420.d7 

noncomputable def Ns408p907 := nat_lit 14760424978389804046421098256481 

noncomputable def Ns408p908 := BSN.sin_dyadic_bound_f 61983303 268435456 2 1 268435456 134217728 Ns408p907 Ns408p133 Ns408p907 Ns408p907 Ns408p134 Ns408p907 61433970 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 61983303) qz372 0 1 Ns408p907 Ns408p133 Ns408p907 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 61983303) qz373 0 1 Ns408p907 Ns408p134 Ns408p907 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p909 := nat_lit 12809434283766447032767754948068923368462593936676524484062154425864372846982802475860287014234869246247673121 

noncomputable def Ns408p910 := nat_lit 13381753722487444862308228829812810353089784326826478967087022399940734247108427745516741218660901297441 

noncomputable def Ns408p911 := nat_lit 77569881345098787092525627057668110151652809855489640289054266616901114497660718781345884025945072764213370145 

noncomputable def Ns408p912 := BSN.cos_dyadic_bound_f 392532921 268435456 4 3 268435456 134217728 Ns408p909 Ns408p252 Ns408p910 Ns408p911 Ns408p255 Ns408p910 29067400 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 392532921) qz370 0 3 Ns408p909 Ns408p252 Ns408p910 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 392532921) qz371 0 3 Ns408p911 Ns408p255 Ns408p910 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p913 := nat_lit 2071497024615423337683296686866171121407054342229145840126200601706496 

noncomputable def Ns408p914 := nat_lit 56390687610966524585927502599840797844270578382523611005405167616 

noncomputable def Ns408p915 := nat_lit 6214378292471048080000718205593313682625474485530672473156590994784256 

noncomputable def Ns408p916 := BSN.cos_dyadic_bound_f 124136908 268435456 3 2 268435456 134217728 Ns408p913 Ns408p123 Ns408p914 Ns408p915 Ns408p126 Ns408p914 240240045 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 124136908) qz370 0 2 Ns408p913 Ns408p123 Ns408p914 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 124136908) qz371 0 2 Ns408p915 Ns408p126 Ns408p914 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p917 := nat_lit 59418065457377510245654212010000 

noncomputable def Ns408p918 := BSN.sin_dyadic_bound_f 87796990 268435456 2 1 268435456 134217728 Ns408p917 Ns408p133 Ns408p917 Ns408p917 Ns408p134 Ns408p917 86240004 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 87796990) qz372 0 1 Ns408p917 Ns408p133 Ns408p917 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 87796990) qz373 0 1 Ns408p917 Ns408p134 Ns408p917 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz650 := (BSN.cos_quad_nat3 143 rfl)

noncomputable def Ns408p919 := Ns408p873 82127 BSN.abs_quadSignPos (BSN.cos_quad_nat0 252 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 240240045 268435456) BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 86240004 268435456) qz136 rfl rfl (Ns408p906 RS409to420.d9 RS409to420.d11 RS409to420.d13 RS409to420.d17 (Ns408p908 rfl rfl) (Ns408p912 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns408p905 rfl) RS409to420.d19 RS409to420.d21 RS409to420.d23 RS409to420.d25 RS409to420.d17 (Ns408p916 rfl rfl) (Ns408p918 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns408p920 := nat_lit 1190330567658697349607572114721 

noncomputable def Ns408p921 := BSN.cos_dyadic_bound_f 33030633 268435456 2 1 268435456 134217728 Ns408p920 Ns408p149 Ns408p920 Ns408p920 Ns408p150 Ns408p920 266405830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 33030633) qz370 0 1 Ns408p920 Ns408p149 Ns408p920 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 33030633) qz371 0 1 Ns408p920 Ns408p150 Ns408p920 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p922 := nat_lit 194040467622285696221819675452081 

noncomputable def Ns408p923 := BSN.sin_dyadic_bound_f 118024747 268435456 2 1 268435456 134217728 Ns408p922 Ns408p133 Ns408p922 Ns408p922 Ns408p134 Ns408p922 114258667 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 118024747) qz372 0 1 Ns408p922 Ns408p133 Ns408p922 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 118024747) qz373 0 1 Ns408p922 Ns408p134 Ns408p922 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p924 := Ns408p871 110738 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 266405830 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 114258667 268435456) qz136 rfl rfl (Ns408p919 rfl rfl) (Ns408p905 rfl) RS409to420.d27 RS409to420.d29 RS409to420.d31 RS409to420.d33 RS409to420.d17 (Ns408p921 rfl rfl) (Ns408p923 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p925 := nat_lit 26784441118301782050891210163293496861074501030805107260021232849690625 

noncomputable def Ns408p926 := nat_lit 9421542290344634702742295004114577687410137107191802149111812890625 

noncomputable def Ns408p927 := nat_lit 80334480270324656883268145899872261427848682818200938175765474923290625 

noncomputable def Ns408p928 := BSN.cos_dyadic_bound_f 235377665 268435456 3 2 268435456 134217728 Ns408p925 Ns408p123 Ns408p926 Ns408p927 Ns408p126 Ns408p926 171684795 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 235377665) qz370 0 2 Ns408p925 Ns408p123 Ns408p926 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 235377665) qz371 0 2 Ns408p927 Ns408p126 Ns408p926 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p929 := nat_lit 11376848963723035556832815270241 

noncomputable def Ns408p930 := BSN.cos_dyadic_bound_f 58077177 268435456 2 1 268435456 134217728 Ns408p929 Ns408p149 Ns408p929 Ns408p929 Ns408p150 Ns408p929 262177300 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 58077177) qz370 0 1 Ns408p929 Ns408p149 Ns408p929 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 58077177) qz371 0 1 Ns408p929 Ns408p150 Ns408p929 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p931 := Ns408p869 135737 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 171684795 268435456) BSN.abs_quadSignPos qz606 (BSN.sfrac_eq_quadSignPos_mul Bool.false 262177300 268435456) qz136 rfl rfl (Ns408p924 rfl) (Ns408p905 rfl) RS409to420.d35 RS409to420.d37 RS409to420.d39 RS409to420.d41 RS409to420.d17 (Ns408p928 rfl rfl) (Ns408p930 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p932 := nat_lit 85602102569701536854586801198955084501567213693384506270245813024194560 

noncomputable def Ns408p933 := nat_lit 29701940867296893992574040897545080105566956135080030857595700903936 

noncomputable def Ns408p934 := nat_lit 224147894064004592028882216597714910231552736982264529705445783928569856 

noncomputable def Ns408p935 := BSN.sin_dyadic_bound_f 271705296 268435456 3 2 268435456 134217728 Ns408p932 Ns408p142 Ns408p933 Ns408p934 Ns408p145 Ns408p933 227630548 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 271705296) qz372 0 2 Ns408p932 Ns408p142 Ns408p933 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 271705296) qz373 0 2 Ns408p934 Ns408p145 Ns408p933 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p936 := nat_lit 882014722692087622475144253851933053824533647325515803195455775440896 

noncomputable def Ns408p937 := nat_lit 10223603753386484917659495632962079349655967843604641201589846016 

noncomputable def Ns408p938 := nat_lit 2646023720868756094455597442564533237314901630040860200303964146630656 

noncomputable def Ns408p939 := BSN.cos_dyadic_bound_f 100276808 268435456 3 2 268435456 134217728 Ns408p936 Ns408p123 Ns408p937 Ns408p938 Ns408p126 Ns408p937 249922538 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 100276808) qz370 0 2 Ns408p936 Ns408p123 Ns408p937 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 100276808) qz371 0 2 Ns408p938 Ns408p126 Ns408p937 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p940 := Ns408p867 158221 BSN.abs_quadSignPos qz415 (BSN.sfrac_eq_quadSignPos_mul Bool.false 227630548 268435456) BSN.abs_quadSignNeg qz395 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 249922538 268435456) qz136 rfl rfl (Ns408p931 rfl) (Ns408p905 rfl) RS409to420.d43 RS409to420.d45 RS409to420.d52 RS409to420.d54 RS409to420.d17 (Ns408p935 rfl rfl) (Ns408p939 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p941 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz133) qz133 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz133) qz133 11) 178149345 268435456 158221 268435456 178149345 268435456 158221 268435456 95643201322352640 178149345 134217728 158221 134217728 (Ns408p940 rfl) 

noncomputable def Ns408p942 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz4 qz33 qz134) (Zeta.RiemannSiegel.correction qz135) 5045899 16777216 1 16777216 56249128786195 70368744177664 386753522118923 27487790694400000000 283827422693132564305 1180591620717411303424 

noncomputable def Ns408p943 := @Enclosure.Real.IsNear.mulLit_tf qz33 qz134 1 1 0 1 5045899 16777216 1 16777216 5045899 16777216 1 16777216 

noncomputable abbrev qz142 := qz460

noncomputable def Ns408p944 := @Enclosure.Real.IsNear.sqrt_image qz142 4100862409053 33554432000 767901 33554432000 185473773 185473809 16777216 (@Enclosure.Real.IsNear.of_eq qz142 (@HMul.hMul Real Real Real qz4 qz133 qz2) Bool.false 4100862409053 33554432000 767901 33554432000 (BSN.t_div_two_pi_mk qz133 767901 1000 qz136) (@Enclosure.Real.IsNear.mulLit_ff qz133 qz2 767901 1000 0 1 5340353 33554432 1 33554432 4100862409053 33554432000 767901 33554432000 (Enclosure.Real.IsNear.const Bool.false 767901 1000) RS409to420.d48 rfl)) 

noncomputable abbrev qz747 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 767901 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz651 := qz747

noncomputable abbrev qz467 := qz651

noncomputable abbrev qz143 := qz467

noncomputable def Ns408p945 := @Enclosure.Real.IsNear.sqrt_image qz143 185473791 16777216 9 8388608 55782914 55782920 16777216 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 370947582 33554432 36 33554432 185473791 16777216 9 8388608 (Ns408p944 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns408p946 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz143) 55782917 16777216 3 16777216 5045898 5045900 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz143) Bool.false 111565834 33554432 6 33554432 55782917 16777216 3 16777216 (Ns408p945 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns408p947 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 10091798 33554432 2 33554432 5045899 16777216 1 16777216 (Ns408p946 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz144 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz461))

noncomputable abbrev qz652 := (@HMul.hMul Real Real Real qz714 qz746 qz746)

noncomputable abbrev qz468 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz652 qz646) qz598)

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz468))

noncomputable def Ns408p948 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz135) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv qz144) qz145) Bool.false 56249128786195 

noncomputable def Ns408p949 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz144) qz145 8917705 8388608 33 

noncomputable def Ns408p950 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz144) Bool.false 35670820 33554432 264 33554432 8917705 8388608 33 

noncomputable def Ns408p951 := @Enclosure.Real.IsNear.recentre' qz144 Bool.false 15781806 16777216 1452304432 209715200000000 7890903 8388608 90769027 13107200000000 

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz350 qz347 qz461)

noncomputable def Ns408p952 := @Enclosure.Real.IsNear.cos_image qz146 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11616541) qz418) Bool.false 11616541 33554432 227 33554432 Bool.false 15781806 16777216 1 

noncomputable def Ns408p953 := nat_lit 242874678685366741289452543 

noncomputable def Ns408p954 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz135 884279719003555 140737488355328 1 500000000000000 924415 16777216 9 8388608 817441436442671295325 2361183241434822606848 Ns408p953 

noncomputable def Ns408p955 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz31 185473791 16777216 9 8388608 11 1 0 1 924415 924415 16777216 9 

noncomputable def Ns408p956 := @Ns408p955 8388608 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 370947582 33554432 36 33554432 185473791 16777216 9 8388608 (Ns408p944 rfl rfl rfl rfl rfl rfl) rfl) qz398 

noncomputable def Ns408p957 := @Enclosure.Real.IsNear.recentre' qz146 Bool.false 817441436442671295325 2361183241434822606848 Ns408p953 Ns408p171 11616541 33554432 227 33554432 (@Ns408p954 Ns408p171 RS409to420.d47 (Ns408p956 rfl rfl) rfl) 

noncomputable def Ns408p958 := nat_lit 18209889830486361000199511761 

noncomputable def Ns408p959 := nat_lit 30423614405477505635920876929024 

noncomputable def Ns408p960 := nat_lit 456354216082162584538813153935360 

noncomputable def Ns408p961 := BSN.cos_dyadic_bound_f 11616541 33554432 2 1 16777216 6250000 Ns408p958 Ns408p959 Ns408p958 Ns408p958 Ns408p960 Ns408p958 15781806 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11616541) qz619 0 1 Ns408p958 Ns408p959 Ns408p958 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11616541) (BSN.cosOddQ 33554432) 0 1 Ns408p958 Ns408p960 Ns408p958 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p962 := @Enclosure.Real.IsNear.inv_image qz144 7890903 8388608 90769027 13107200000000 17835278 17835542 16777216 (Ns408p951 (@Ns408p952 6250000 (Ns408p957 rfl) (Enclosure.sfrac_false_div 11616541 33554432) (Ns408p961 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns408p963 := @Enclosure.Real.IsNear.recentre' qz145 Bool.false 12615158 16777216 

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz350 qz347 qz468)

noncomputable def Ns408p964 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 24153271)) qz418) Bool.true 24153271 33554432 

noncomputable def Ns408p965 := nat_lit 28515149753094258173691354205 

noncomputable def Ns408p966 := nat_lit 282737456827351492192895823806623 

noncomputable def Ns408p967 := @Enclosure.Real.IsNear.recentre' qz147 Bool.true Ns408p965 Ns408p187 Ns408p966 

noncomputable def Ns408p968 := nat_lit 37778931862957161709568000000000000000 

noncomputable abbrev qz148 := qz468

noncomputable def Ns408p969 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz148 884279719003555 140737488355328 1 500000000000000 32246753080831 

noncomputable abbrev qz469 := (@HSub.hSub Real Real Real qz584 qz652 qz646)

noncomputable abbrev qz149 := qz469

noncomputable def Ns408p970 := @Enclosure.Real.IsNear.subLit_tf qz149 qz28 14654567036415 281474976710656 10477161 8796093022208 1 16 

noncomputable abbrev qz470 := qz652

noncomputable abbrev qz150 := qz470

noncomputable def Ns408p971 := @Enclosure.Real.IsNear.subLit_ff_n qz150 qz135 854543092225 281474976710656 1039977 8796093022208 924415 16777216 9 8388608 

noncomputable def Ns408p972 := @Enclosure.Real.IsNear.mulLit_ff qz135 qz135 924415 16777216 9 8388608 924415 16777216 9 8388608 854543092225 281474976710656 

noncomputable def Ns408p973 := nat_lit 724906614359449600227764585000805163903999142507809995728773441 

noncomputable def Ns408p974 := nat_lit 115826420051144651613589866227077147474189159962259644375361 

noncomputable def Ns408p975 := nat_lit 2174488190238246511380066575269961337417049049203505467897569601 

noncomputable def Ns408p976 := BSN.cos_dyadic_bound_f 24153271 33554432 3 2 16777216 6250000 Ns408p973 Ns408p489 Ns408p974 Ns408p975 Ns408p492 Ns408p974 12615158 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 24153271) qz619 0 2 Ns408p973 Ns408p489 Ns408p974 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 24153271) (BSN.cosOddQ 33554432) 0 2 Ns408p975 Ns408p492 Ns408p974 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p977 := @Ns408p963 402138608 52428800000000 6307579 8388608 25133663 3276800000000 (@Ns408p964 63 8388608 Bool.false 12615158 16777216 1 6250000 (@Ns408p967 Ns408p968 24153271 33554432 63 8388608 (@Ns408p969 281474976710656 10477161 8796093022208 Ns408p965 Ns408p187 Ns408p966 Ns408p968 RS409to420.d47 (@Ns408p970 0 1 515948049293296 32246753080831 281474976710656 10477161 8796093022208 (@Ns408p971 245862836556414320640 14654567036415 281474976710656 10477161 8796093022208 (@Ns408p972 1039977 8796093022208 (Ns408p956 rfl rfl) (Ns408p956 rfl rfl) rfl) (Ns408p956 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 24153271 33554432) (BSN.cos_neg_of_bound 24153271 33554432 Bool.false 12615158 16777216 1 6250000 (Ns408p976 rfl rfl)) rfl rfl) 

noncomputable def Ns408p978 := @Ns408p942 78939676527679239503 Ns408p863 (Ns408p943 qz51 (@Enclosure.Real.IsNear.of_eq qz134 (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 5045899 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz142 (BSN.t_div_two_pi_nonneg qz133 767901 1000 qz136)) Ns408p947) rfl) (@Ns408p948 70368744177664 386753522118923 27487790694400000000 (BSN.correction_mk qz135 (BSN.cos_two_pi_p_ne_zero_mk qz133 767901 1000 11 qz136 rfl rfl (@BSN.floor_sqrt_eq_dec qz133 767901 1000 11 qz136 rfl rfl rfl))) (@Ns408p949 4194304 6307579 8388608 25133663 3276800000000 56249128786195 70368744177664 386753522118923 27487790694400000000 (@Ns408p950 4194304 (Ns408p962 rfl rfl rfl rfl rfl) rfl) (Ns408p977 rfl) rfl)) 

noncomputable def Ns408p979 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz133) (hardyZApproximantRS₀ qz133) Bool.true 1283190787772293089455 1180591620717411303424 21824668333820991239503 Ns408p863 (@Eq.refl Real (hardyZApproximantRS₀ qz133)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz133) (@HSub.hSub Real Real Real qz30 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz133) qz133 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz134) (Zeta.RiemannSiegel.correction qz135))) Bool.true 1283190787772293089455 1180591620717411303424 21824668333820991239503 Ns408p863 (BSN.hardyZApproximantRS₀_eq qz133 11 (@BSN.floor_sqrt_eq_dec qz133 767901 1000 11 qz136 rfl rfl rfl)) (@Ns408p865 1283190787772293089455 1180591620717411303424 21824668333820991239503 Ns408p863 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz133) qz133 11) (@HAdd.hAdd Real Real Real qz368 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz133) qz133 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz133) qz133 11)) Bool.true 178149345 134217728 158221 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz133) qz133 11) (Ns408p941 (Ns408p940 rfl) rfl rfl)) (Ns408p978 rfl) rfl rfl)) 

theorem RS409to420.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz133) Bool.true 1283190787772293089455 1180591620717411303424 21824668333820991239503 Ns408p863 := Ns408p979 

noncomputable def Ns408p980 := nat_lit 147573952589676412928000000 

noncomputable def Ns408p981 := nat_lit 697691979022310220883627606016 

noncomputable abbrev qz748 := (Enclosure.sfrac Bool.false 769208 1000)

noncomputable abbrev qz653 := qz748

noncomputable abbrev qz471 := qz653

noncomputable abbrev qz151 := qz471

noncomputable abbrev qz749 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 769208 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz654 := qz749

noncomputable abbrev qz472 := qz654

noncomputable abbrev qz152 := (@HPow.hPow Real Real Real qz351 qz472 qz353)

noncomputable abbrev qz750 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 769208 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz655 := qz750

noncomputable abbrev qz473 := qz655

noncomputable abbrev qz153 := qz473

noncomputable def Ns408p982 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz152) (Zeta.RiemannSiegel.correction qz153)) 66004795 33554432 4953 4194304 2214143150715420626943 9444732965739290427392 640989348527575423047 Ns408p980 Ns408p981 

noncomputable def Ns408p983 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 769208 1000 195 242 268435456 134217728 4503599627370496 Bool.false 392984417855 2583 

noncomputable def Ns408p984 := Ns408p983 618095470 44 84886744 8 643680110 44 80936328 8 Bool.false 274127210 135974 Bool.true 236363920 Bool.true 98374557 14148475504056880 1 Bool.false 206983273 Bool.false Bool.false 250610450 Bool.true Bool.false 264019180 

noncomputable def Ns408p985 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 769208 1000 86 143 268435456 134217728 4503599627370496 Bool.false 392984417855 2583 

noncomputable def Ns408p986 := Ns408p985 558195838 44 94906264 8 589812974 44 89478488 8 Bool.false 270085613 110932 Bool.true 121747470 Bool.true 407428007 14148475504056880 1 Bool.false 241296534 Bool.true Bool.false 268058402 Bool.false Bool.false 274127210 

noncomputable def Ns408p987 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 769208 1000 54 20 268435456 134217728 4503599627370496 Bool.false 392984417855 2583 

noncomputable def Ns408p988 := Ns408p987 480971758 44 109588312 8 522351262 44 101459064 8 Bool.false 320291526 82272 Bool.false 247592700 Bool.true 379203120 14148475504056880 1 Bool.false 162120275 Bool.true Bool.false 42277545 Bool.false Bool.false 270085613 

noncomputable def Ns408p989 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 769208 1000 253 143 268435456 134217728 4503599627370496 Bool.false 392984417855 2583 

noncomputable def Ns408p990 := Ns408p989 372130544 43 134217720 8 432030192 43 120047984 16 Bool.false 232192811 48467 Bool.false 59297014 Bool.false 366325684 14148475504056880 1 Bool.false 58815944 Bool.true Bool.false 262752940 Bool.false Bool.false 320291526 

noncomputable def Ns408p991 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 769208 1000 592 394 268435456 134217728 4503599627370496 Bool.false 392984417855 2583 

noncomputable def Ns408p992 := Ns408p991 186065264 43 189812528 16 294906480 43 154981288 8 Bool.false 268435280 2635 Bool.false 240330730 Bool.false 6967450 14148475504056880 1 Bool.false 167848226 Bool.false Bool.false 268345038 Bool.true Bool.false 232192811 

noncomputable def Ns408p993 := nat_lit 1500413963249330094769273882245668522553246447470837221 

noncomputable def Ns408p994 := nat_lit 1024886199334200956200073710494238809786886914048000 

noncomputable def Ns408p995 := nat_lit 129258962038005448835786071408640000 

noncomputable def Ns408p996 := nat_lit 596562283657375348382672359290438942720 

noncomputable abbrev qz656 := (@Eq.refl Real qz748)

noncomputable abbrev qz474 := qz656

noncomputable abbrev qz154 := qz474

noncomputable def Ns408p997 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz151 769208 1000 2366724789056 16000000 1538416 4000 2000 Ns408p995 Ns408p996 qz154 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns408p998 := nat_lit 1966622589910161941815982662937042645880991183628975762309120 

noncomputable abbrev qz657 := (@HSub.hSub Real Real Real qz718 qz719 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz720 (@Nat.cast Real Real.instNatCast 1538416))))

noncomputable abbrev qz475 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 769208 4000) (Real.log (Enclosure.sfrac Bool.false 2366724789056 16000000))) (@HMul.hMul Real Real Real qz579 qz585 qz657))

noncomputable abbrev qz658 := (Enclosure.sfrac Bool.false 769208 2000)

noncomputable abbrev qz155 := (@HSub.hSub Real Real Real qz356 (@HSub.hSub Real Real Real qz356 qz475 qz658) (@HMul.hMul Real Real Real qz350 qz658 (Real.log Real.pi)))

noncomputable def Ns408p999 := @Enclosure.Real.IsNear.addLit_ft_p qz155 (Enclosure.sfrac Bool.true Ns408p995 Ns408p996) 3296592719403230842121 2251799813685248000 4923949808157483 512000000000000000000 Ns408p995 Ns408p996 0 1 Ns408p998 

noncomputable def Ns408p1000 := nat_lit 27653824058727697468062957568000 

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz356 qz475 qz658)

noncomputable def Ns408p1001 := @Enclosure.Real.IsNear.subLit_ff_p qz156 (@HMul.hMul Real Real Real qz4 qz658 (Real.log Real.pi)) 4287987425591860022537 2251799813685248000 3886043269259 1000000000000000000 3693233080911 8388608000 96151 16777216000 Ns408p1000 3296592719403230842121 2251799813685248000 

noncomputable def Ns408p1002 := nat_lit 8575974851183720045074000 

noncomputable abbrev qz157 := qz475

noncomputable def Ns408p1003 := @Enclosure.Real.IsNear.subLit_ff_p qz157 qz658 5154038641134461144329 2251799813685248000 3886043269259 1000000000000000000 769208 2000 0 1 Ns408p1002 4287987425591860022537 2251799813685248000 3886043269259 1000000000000000000 

noncomputable def Ns408p1004 := nat_lit 11605863251833148383415915440706158592 

noncomputable def Ns408p1005 := nat_lit 57566285807974699495325696 

noncomputable def Ns408p1006 := nat_lit 830734968563536896173531386536188633056005685170386152258974849009416279162880 

noncomputable def Ns408p1007 := nat_lit 1012093605366041271438075857455007692538736522448179332548253680408908005376 

noncomputable def Ns408p1008 := nat_lit 5756355018148170591568338865411822168361635478678377496437508108451840 

noncomputable def Ns408p1009 := BSN.log_dyadic_bound 269572789056 4463876789056 4 3 Ns408p1006 134217728 50000000 Ns408p1007 Ns408p1008 16230523 4733449578112 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 269572789056) (BSN.artanhQ 4463876789056) 0 3 Ns408p1007 Ns408p1006 Ns408p1008 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz476 := (Real.log (Enclosure.sfrac Bool.false 2366724789056 16000000))

noncomputable def Ns408p1010 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 769208 4000) qz476 769208 4000 0 1 53612781509733479 4503599627370496 20000017 1000000000000000 5154922554942383739329 2251799813685248000 1923021634567 500000000000000000 (Enclosure.Real.IsNear.const Bool.false 769208 4000) (BSN.isNear_log_sfrac 2366724789056 16000000 53612781509733479 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2366724789056) qz359)) Bool.false Ns408p1005 Ns408p100 1000000850000000 50000000000000000000000 53612781509733479 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2366724789056 16000000 17 4733449578112 4194304000000 16230523 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns408p1009 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns408p1011 := BSN.arctan_dyadic_bound_f 1000 1538416 1 0 16777216 6250000 0 1 1 0 1 1 10905 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1538416) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1538416) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns408p1012 := @Enclosure.Real.IsNear.subLit_ff_p qz12 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz13 (@Nat.cast Real Real.instNatCast 1538416))) 884279719003555 562949953421312 1 2000000000000000 10905 16777216 1 6250000 14829612880899887595520 883913807922595 562949953421312 320000001 2000000000000000 qz14 (Ns408p1011 rfl) rfl rfl 

noncomputable abbrev qz477 := (@HMul.hMul Real Real Real qz579 qz585 qz657)

noncomputable abbrev qz158 := qz477

noncomputable abbrev qz478 := qz657

noncomputable abbrev qz159 := qz478

noncomputable def Ns408p1013 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 769208 4000) qz476) qz158 5154922554942383739329 2251799813685248000 1923021634567 500000000000000000 883913807922595 2251799813685248 320000001 8000000000000000 Ns408p1004 5154038641134461144329 2251799813685248000 3886043269259 1000000000000000000 (Ns408p1010 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz16 qz159 1 4 0 1 883913807922595 562949953421312 320000001 2000000000000000 883913807922595 2251799813685248 320000001 8000000000000000 qz367 Ns408p1012 rfl) 

noncomputable def Ns408p1014 := @Ns408p999 Ns408p993 Ns408p994 4923949808157483 512000000000000000000 (@Ns408p1001 4923949808157483 512000000000000000000 (Ns408p1003 (Ns408p1013 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 769208 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz658 (Real.log Real.pi) 769208 2000 0 1 38410761 33554432 1 67108864 3693233080911 8388608000 96151 16777216000 (Enclosure.Real.IsNear.const Bool.false 769208 2000) RS409to420.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns408p995 Ns408p996) 

noncomputable def Ns408p1015 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz151) Bool.false Ns408p993 Ns408p994 4923949808157483 512000000000000000000 49123052231 33554432 81 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz151) (@HAdd.hAdd Real Real Real qz368 qz155 (Enclosure.sfrac Bool.true Ns408p995 Ns408p996)) Bool.false Ns408p993 Ns408p994 4923949808157483 512000000000000000000 Ns408p997 (Ns408p1014 rfl rfl)) 

noncomputable def Ns408p1016 := nat_lit 7590405219794228527235072 

noncomputable def Ns408p1017 := nat_lit 3500658240628457909389607644018055343287804495711526713914714206583114074544377966802726580018089903563294439848279197500983565094523764736 

noncomputable def Ns408p1018 := nat_lit 2480972403410384186118318956635051951514317147686283156049812853591380488236852300560825733527168366200750363069356037120771999399936 

noncomputable def Ns408p1019 := nat_lit 17481604029565230028871050099952358734955905698866902921463215117014536897551791196427862872291403522193776456564737789787586995102936989696 

noncomputable def Ns408p1020 := BSN.sin_dyadic_bound_f 107866145808 68719476736 4 3 33554432 12512208 Ns408p1017 Ns408p114 Ns408p1018 Ns408p1019 Ns408p117 Ns408p1018 33554410 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107866145808) qz591 0 3 Ns408p1017 Ns408p114 Ns408p1018 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107866145808) qz592 0 3 Ns408p1019 Ns408p117 Ns408p1018 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1021 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz151) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49123052231) qz418) Bool.false 49123052231 33554432 81 8388608 Bool.false 33554410 33554432 1 6250000 (Ns408p1015 rfl) (Enclosure.sfrac_false_div 49123052231 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49123052231) qz418) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns408p1016) qz430) 226375608064910080 72057594037927936 Bool.false 33554410 33554432 232 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 49123052231 33554432 226375608064910080 72057594037927936 232 Ns408p1016 Ns408p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554410 33554432 Ns408p1016 Ns408p100 107866145808 68719476736 12512208 12500000 (Ns408p1020 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns408p1022 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz151) Bool.false Ns408p993 Ns408p994 4923949808157483 512000000000000000000 392984417855 268435456 2583 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz151) (@HAdd.hAdd Real Real Real qz368 qz155 (Enclosure.sfrac Bool.true Ns408p995 Ns408p996)) Bool.false Ns408p993 Ns408p994 4923949808157483 512000000000000000000 Ns408p997 (Ns408p1014 rfl rfl)) 

noncomputable def Ns408p1023 := Ns408p992 48467 BSN.abs_quadSignPos (BSN.cos_quad_nat0 592 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 167848226 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 394 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268345038 268435456) qz154 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 1) Bool.false 16777205 16777216 32164913 3276800000000 268435280 268435456 2635 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz151)) Bool.false 16777205 16777216 32164913 3276800000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz151) qz151) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz151)) Bool.false 33554410 33554432 514638608 52428800000000 16777205 16777216 32164913 3276800000000 (Ns408p1021 rfl rfl) rfl)) rfl) (Ns408p1022 rfl) RS409to420.d7 

noncomputable def Ns408p1024 := nat_lit 29112002532293011985496177911653554733162675561435115247872750384800000 

noncomputable def Ns408p1025 := nat_lit 11129469021121797970636470000719019534173112546696394550208100000000 

noncomputable def Ns408p1026 := nat_lit 87313748658836792360547260794959226160419680459211952954517834954400000 

noncomputable def Ns408p1027 := BSN.cos_dyadic_bound_f 240330730 268435456 3 2 268435456 134217728 Ns408p1024 Ns408p123 Ns408p1025 Ns408p1026 Ns408p126 Ns408p1025 167848226 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 240330730) qz370 0 2 Ns408p1024 Ns408p123 Ns408p1025 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 240330730) qz371 0 2 Ns408p1026 Ns408p126 Ns408p1025 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1028 := nat_lit 2356651929226967047506250000 

noncomputable def Ns408p1029 := BSN.cos_dyadic_bound_f 6967450 268435456 2 1 268435456 134217728 Ns408p1028 Ns408p149 Ns408p1028 Ns408p1028 Ns408p150 Ns408p1028 268345038 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 6967450) qz370 0 1 Ns408p1028 Ns408p149 Ns408p1028 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 6967450) qz371 0 1 Ns408p1028 Ns408p150 Ns408p1028 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1030 := nat_lit 12363211451491961355568627910416 

noncomputable def Ns408p1031 := BSN.sin_dyadic_bound_f 59297014 268435456 2 1 268435456 134217728 Ns408p1030 Ns408p133 Ns408p1030 Ns408p1030 Ns408p134 Ns408p1030 58815944 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 59297014) qz372 0 1 Ns408p1030 Ns408p133 Ns408p1030 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 59297014) qz373 0 1 Ns408p1030 Ns408p134 Ns408p1030 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1032 := nat_lit 25222346423327989317639881453556048306852176672882062525843817189593674605762267049839556121226360001088454656 

noncomputable def Ns408p1033 := nat_lit 5839940607150535580320196712769079846597908297972955092071293109485306372823730584546963881471305056256 

noncomputable def Ns408p1034 := nat_lit 126022398367400096140009981013898688283290911484297691893374616013380624829862422569790940923227912955930607616 

noncomputable def Ns408p1035 := BSN.sin_dyadic_bound_f 366325684 268435456 4 3 268435456 134217728 Ns408p1032 Ns408p269 Ns408p1033 Ns408p1034 Ns408p272 Ns408p1033 262752940 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 366325684) qz372 0 3 Ns408p1032 Ns408p269 Ns408p1033 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 366325684) qz373 0 3 Ns408p1034 Ns408p272 Ns408p1033 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1036 := Ns408p990 82272 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 253 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58815944 268435456) BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 262752940 268435456) qz154 rfl rfl (Ns408p1023 RS409to420.d9 RS409to420.d11 RS409to420.d13 RS409to420.d17 (Ns408p1027 rfl rfl) (Ns408p1029 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns408p1022 rfl) RS409to420.d19 RS409to420.d21 RS409to420.d23 RS409to420.d25 RS409to420.d17 (Ns408p1031 rfl rfl) (Ns408p1035 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns408p1037 := nat_lit 32794966844762923733469682079924486184656949897415760741086848000000000 

noncomputable def Ns408p1038 := nat_lit 14122210697889119041799180360213469184335348105180810000000000000000 

noncomputable def Ns408p1039 := nat_lit 98356656112892992962325447879053031615602178996036920603260544000000000 

noncomputable def Ns408p1040 := BSN.cos_dyadic_bound_f 247592700 268435456 3 2 268435456 134217728 Ns408p1037 Ns408p123 Ns408p1038 Ns408p1039 Ns408p126 Ns408p1038 162120275 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 247592700) qz370 0 2 Ns408p1037 Ns408p123 Ns408p1038 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 247592700) qz371 0 2 Ns408p1039 Ns408p126 Ns408p1038 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1041 := nat_lit 11152209774812756200301485680809601952183099172600644641246471175003810123282381552276027618660800528384000000 

noncomputable def Ns408p1042 := nat_lit 8840214919547852947107572577150097311018966314734799813693319727444090530125890977641005056000000000000 

noncomputable def Ns408p1043 := nat_lit 67550032431000562022314778253270510086263531578394590160012772321989164579195302125470170878294003128729600000 

noncomputable def Ns408p1044 := BSN.cos_dyadic_bound_f 379203120 268435456 4 3 268435456 134217728 Ns408p1041 Ns408p252 Ns408p1042 Ns408p1043 Ns408p255 Ns408p1042 42277545 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 379203120) qz370 0 3 Ns408p1041 Ns408p252 Ns408p1042 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 379203120) qz371 0 3 Ns408p1043 Ns408p255 Ns408p1042 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1045 := Ns408p988 110932 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 162120275 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 42277545 268435456) qz154 rfl rfl (Ns408p1036 rfl rfl) (Ns408p1022 rfl) RS409to420.d27 RS409to420.d29 RS409to420.d31 RS409to420.d33 RS409to420.d17 (Ns408p1040 rfl rfl) (Ns408p1044 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1046 := nat_lit 1916547178570898347383711891394664406561489072273471928013788336800000 

noncomputable def Ns408p1047 := nat_lit 48270251346956589381729423604944431307883926783377883056100000000 

noncomputable def Ns408p1048 := nat_lit 5749544995210001128972372215336783330821851448966849028275252810400000 

noncomputable def Ns408p1049 := BSN.cos_dyadic_bound_f 121747470 268435456 3 2 268435456 134217728 Ns408p1046 Ns408p123 Ns408p1047 Ns408p1048 Ns408p126 Ns408p1047 241296534 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 121747470) qz370 0 2 Ns408p1046 Ns408p123 Ns408p1047 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 121747470) qz371 0 2 Ns408p1048 Ns408p126 Ns408p1047 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1050 := nat_lit 38617427964983770151728296950716466162671114829205388656167044342526734152919015531819931906007407051964324001 

noncomputable def Ns408p1051 := nat_lit 20922354398010436287473757537575322068487397098999188123419652782886620651385327091208355298430661335201 

noncomputable def Ns408p1052 := nat_lit 192877948415898477185272709272363866178404271227133162628388240305244508176489499084524922428302717183476275361 

noncomputable def Ns408p1053 := BSN.sin_dyadic_bound_f 407428007 268435456 4 3 268435456 134217728 Ns408p1050 Ns408p269 Ns408p1051 Ns408p1052 Ns408p272 Ns408p1051 268058402 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 407428007) qz372 0 3 Ns408p1050 Ns408p269 Ns408p1051 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 407428007) qz373 0 3 Ns408p1052 Ns408p272 Ns408p1051 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1054 := Ns408p986 135974 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 241296534 268435456) BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 268058402 268435456) qz154 rfl rfl (Ns408p1045 rfl) (Ns408p1022 rfl) RS409to420.d35 RS409to420.d37 RS409to420.d39 RS409to420.d41 RS409to420.d17 (Ns408p1049 rfl rfl) (Ns408p1053 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1055 := nat_lit 49017635684564826524683856968887227276775786941385092419221811363840000 

noncomputable def Ns408p1056 := nat_lit 9742030204208793992142178451917956804680640994165403523481600000000 

noncomputable def Ns408p1057 := nat_lit 128363749220196302850565680915306299509109959046779926635114345267200000 

noncomputable def Ns408p1058 := BSN.sin_dyadic_bound_f 236363920 268435456 3 2 268435456 134217728 Ns408p1055 Ns408p142 Ns408p1056 Ns408p1057 Ns408p145 Ns408p1056 206983273 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 236363920) qz372 0 2 Ns408p1055 Ns408p142 Ns408p1056 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 236363920) qz373 0 2 Ns408p1057 Ns408p145 Ns408p1056 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1059 := nat_lit 816967194136250924784568896525850681122720296296775923123665845701281 

noncomputable def Ns408p1060 := nat_lit 8771266717241442392313811524479039107417106077673301905818340001 

noncomputable def Ns408p1061 := nat_lit 2450884039875318291468922061954503085289946054678172422767185900423841 

noncomputable def Ns408p1062 := BSN.cos_dyadic_bound_f 98374557 268435456 3 2 268435456 134217728 Ns408p1059 Ns408p123 Ns408p1060 Ns408p1061 Ns408p126 Ns408p1060 250610450 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 98374557) qz370 0 2 Ns408p1059 Ns408p123 Ns408p1060 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 98374557) qz371 0 2 Ns408p1061 Ns408p126 Ns408p1060 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1063 := Ns408p984 158496 BSN.abs_quadSignPos qz415 (BSN.sfrac_eq_quadSignPos_mul Bool.false 206983273 268435456) BSN.abs_quadSignNeg qz395 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 250610450 268435456) qz154 rfl rfl (Ns408p1054 rfl) (Ns408p1022 rfl) RS409to420.d43 RS409to420.d45 RS409to420.d52 RS409to420.d54 RS409to420.d17 (Ns408p1058 rfl rfl) (Ns408p1062 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1064 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 11) 264019180 268435456 158496 268435456 264019180 268435456 158496 268435456 141744217952092160 66004795 33554432 4953 4194304 (Ns408p1063 rfl) 

noncomputable def Ns408p1065 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz4 qz33 qz152) (Zeta.RiemannSiegel.correction qz153) 10087509 33554432 1 33554432 219493548973827 281474976710656 158007219280293 10995116277760000000 2214143150715420626943 9444732965739290427392 

noncomputable def Ns408p1066 := @Enclosure.Real.IsNear.mulLit_tf qz33 qz152 1 1 0 1 10087509 33554432 1 33554432 10087509 33554432 1 33554432 

noncomputable abbrev qz160 := qz472

noncomputable def Ns408p1067 := @Enclosure.Real.IsNear.sqrt_image qz160 513480281303 4194304000 96151 4194304000 185631548 185631584 16777216 (@Enclosure.Real.IsNear.of_eq qz160 (@HMul.hMul Real Real Real qz4 qz151 qz2) Bool.false 513480281303 4194304000 96151 4194304000 (BSN.t_div_two_pi_mk qz151 769208 1000 qz154) (@Enclosure.Real.IsNear.mulLit_ff qz151 qz2 769208 1000 0 1 5340353 33554432 1 33554432 513480281303 4194304000 96151 4194304000 (Enclosure.Real.IsNear.const Bool.false 769208 1000) RS409to420.d48 rfl)) 

noncomputable abbrev qz751 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 769208 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz659 := qz751

noncomputable abbrev qz479 := qz659

noncomputable abbrev qz161 := qz479

noncomputable def Ns408p1068 := @Enclosure.Real.IsNear.sqrt_image qz161 92815783 8388608 9 8388608 55806635 55806642 16777216 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 371263132 33554432 36 33554432 92815783 8388608 9 8388608 (Ns408p1067 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns408p1069 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz161) 111613277 33554432 7 33554432 5043754 5043755 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz161) Bool.false 111613277 33554432 7 33554432 111613277 33554432 7 33554432 (Ns408p1068 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns408p1070 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 10087509 33554432 1 33554432 10087509 33554432 1 33554432 (Ns408p1069 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz162 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz473))

noncomputable abbrev qz660 := (@HMul.hMul Real Real Real qz714 qz750 qz750)

noncomputable abbrev qz480 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz660 qz655) qz598)

noncomputable abbrev qz163 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz480))

noncomputable def Ns408p1071 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz153) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv qz162) qz163) Bool.false 219493548973827 

noncomputable def Ns408p1072 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz162) qz163 18256167 16777216 69 

noncomputable def Ns408p1073 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz162) Bool.false 36512334 33554432 276 33554432 18256167 16777216 69 

noncomputable def Ns408p1074 := @Enclosure.Real.IsNear.recentre' qz162 Bool.false 15418076 16777216 1452304432 209715200000000 3854519 4194304 90769027 13107200000000 

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz350 qz347 qz473)

noncomputable def Ns408p1075 := @Enclosure.Real.IsNear.cos_image qz164 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 424975) (@Nat.cast Real Real.instNatCast 1048576)) Bool.false 424975 1048576 227 33554432 Bool.false 15418076 16777216 1 

noncomputable def Ns408p1076 := nat_lit 242874678686044379754578943 

noncomputable def Ns408p1077 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz153 884279719003555 140737488355328 1 500000000000000 541095 8388608 9 8388608 478479334554228592725 1180591620717411303424 Ns408p1076 

noncomputable def Ns408p1078 := @Enclosure.Real.IsNear.subLit_ff_p qz161 qz31 92815783 8388608 9 8388608 11 1 0 1 541095 541095 8388608 9 

noncomputable def Ns408p1079 := @Ns408p1078 8388608 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 371263132 33554432 36 33554432 92815783 8388608 9 8388608 (Ns408p1067 rfl rfl rfl rfl rfl rfl) rfl) qz398 

noncomputable def Ns408p1080 := @Enclosure.Real.IsNear.recentre' qz164 Bool.false 478479334554228592725 1180591620717411303424 Ns408p1076 Ns408p171 424975 1048576 227 33554432 (@Ns408p1077 Ns408p171 RS409to420.d47 (Ns408p1079 rfl rfl) rfl) 

noncomputable def Ns408p1081 := nat_lit 29014219670751100192948224 

noncomputable def Ns408p1082 := nat_lit 435213295061266502894223360 

noncomputable def Ns408p1083 := BSN.cos_dyadic_bound_f 424975 1048576 2 1 16777216 6250000 32617714739817187890625 Ns408p1081 32617714739817187890625 32617714739817187890625 Ns408p1082 32617714739817187890625 15418076 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 424975) (BSN.cosEvenQ 1048576) 0 1 32617714739817187890625 Ns408p1081 32617714739817187890625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 424975) (BSN.cosOddQ 1048576) 0 1 32617714739817187890625 Ns408p1082 32617714739817187890625 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1084 := @Enclosure.Real.IsNear.inv_image qz162 3854519 4194304 90769027 13107200000000 18256029 18256305 16777216 (Ns408p1074 (@Ns408p1075 6250000 (Ns408p1080 rfl) (Enclosure.sfrac_false_div 424975 1048576) (Ns408p1083 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns408p1085 := @Enclosure.Real.IsNear.recentre' qz163 Bool.false 12022981 16777216 

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz350 qz347 qz480)

noncomputable def Ns408p1086 := @Enclosure.Real.IsNear.cos_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 12949399)) qz369) Bool.true 12949399 16777216 

noncomputable def Ns408p1087 := nat_lit 7643976131149268641504117645 

noncomputable def Ns408p1088 := nat_lit 2300219207052773823071879704484009 

noncomputable def Ns408p1089 := @Enclosure.Real.IsNear.recentre' qz165 Bool.true Ns408p1087 Ns408p609 Ns408p1088 

noncomputable abbrev qz166 := qz480

noncomputable def Ns408p1090 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz166 884279719003555 140737488355328 1 500000000000000 8644296557839 

noncomputable abbrev qz481 := (@HSub.hSub Real Real Real qz584 qz660 qz655)

noncomputable abbrev qz167 := qz481

noncomputable def Ns408p1091 := @Enclosure.Real.IsNear.subLit_tf qz167 qz28 4246250046735 70368744177664 85237263 70368744177664 1 16 

noncomputable abbrev qz482 := qz660

noncomputable abbrev qz168 := qz482

noncomputable def Ns408p1092 := @Enclosure.Real.IsNear.subLit_ff_n qz168 qz153 292783799025 70368744177664 9739791 70368744177664 541095 8388608 9 8388608 

noncomputable def Ns408p1093 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz153 541095 8388608 9 8388608 541095 8388608 9 8388608 292783799025 70368744177664 

noncomputable def Ns408p1094 := nat_lit 3743510484937755482737126401862476263066385779185247206601281 

noncomputable def Ns408p1095 := nat_lit 790672986493573555919827683264120703293424039662882484801 

noncomputable def Ns408p1096 := nat_lit 11228950108840279301099539550220900547792570489476415854834241 

noncomputable def Ns408p1097 := BSN.cos_dyadic_bound_f 12949399 16777216 3 2 16777216 6250000 Ns408p1094 Ns408p735 Ns408p1095 Ns408p1096 Ns408p738 Ns408p1095 12022981 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 12949399) (BSN.cosEvenQ 16777216) 0 2 Ns408p1094 Ns408p735 Ns408p1095 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 12949399) (BSN.cosOddQ 16777216) 0 2 Ns408p1096 Ns408p738 Ns408p1095 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1098 := @Ns408p1085 6381072 819200000000 12022981 16777216 398817 51200000000 (@Ns408p1086 1 131072 Bool.false 12022981 16777216 1 6250000 (@Ns408p1089 Ns408p612 12949399 16777216 1 131072 (@Ns408p1090 70368744177664 85237263 70368744177664 Ns408p1087 Ns408p609 Ns408p1088 Ns408p612 RS409to420.d47 (@Ns408p1091 0 1 138308744925424 8644296557839 70368744177664 85237263 70368744177664 (@Ns408p1092 35620127112041594880 4246250046735 70368744177664 85237263 70368744177664 (@Ns408p1093 9739791 70368744177664 (Ns408p1079 rfl rfl) (Ns408p1079 rfl rfl) rfl) (Ns408p1079 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 12949399 16777216) (BSN.cos_neg_of_bound 12949399 16777216 Bool.false 12022981 16777216 1 6250000 (Ns408p1097 rfl rfl)) rfl rfl) 

noncomputable def Ns408p1099 := @Ns408p1065 640989348527575423047 Ns408p980 (Ns408p1066 qz51 (@Enclosure.Real.IsNear.of_eq qz152 (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 10087509 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz160 (BSN.t_div_two_pi_nonneg qz151 769208 1000 qz154)) Ns408p1070) rfl) (@Ns408p1071 281474976710656 158007219280293 10995116277760000000 (BSN.correction_mk qz153 (BSN.cos_two_pi_p_ne_zero_mk qz151 769208 1000 11 qz154 rfl rfl (@BSN.floor_sqrt_eq_dec qz151 769208 1000 11 qz154 rfl rfl rfl))) (@Ns408p1072 8388608 12022981 16777216 398817 51200000000 219493548973827 281474976710656 158007219280293 10995116277760000000 (@Ns408p1073 8388608 (Ns408p1084 rfl rfl rfl rfl rfl) rfl) (Ns408p1098 rfl) rfl)) 

noncomputable def Ns408p1100 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz151) (hardyZApproximantRS₀ qz151) Bool.false 20792841286132044222463 9444732965739290427392 174909184304512471423047 Ns408p980 (@Eq.refl Real (hardyZApproximantRS₀ qz151)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz151) (@HSub.hSub Real Real Real qz30 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz152) (Zeta.RiemannSiegel.correction qz153))) Bool.false 20792841286132044222463 9444732965739290427392 174909184304512471423047 Ns408p980 (BSN.hardyZApproximantRS₀_eq qz151 11 (@BSN.floor_sqrt_eq_dec qz151 769208 1000 11 qz154 rfl rfl rfl)) (@Ns408p982 20792841286132044222463 9444732965739290427392 174909184304512471423047 Ns408p980 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 11) (@HAdd.hAdd Real Real Real qz368 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 11)) Bool.false 66004795 33554432 4953 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz151) qz151 11) (Ns408p1064 (Ns408p1063 rfl) rfl rfl)) (Ns408p1099 rfl) rfl rfl)) 

theorem RS409to420.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz151) Bool.false 20792841286132044222463 9444732965739290427392 174909184304512471423047 Ns408p980 := Ns408p1100 

noncomputable def Ns408p1101 := nat_lit 368934881474191032320000000 

noncomputable def Ns408p1102 := nat_lit 939426797719334438691936403456 

noncomputable abbrev qz752 := (Enclosure.sfrac Bool.false 770515 1000)

noncomputable abbrev qz661 := qz752

noncomputable abbrev qz483 := qz661

noncomputable abbrev qz169 := qz483

noncomputable abbrev qz753 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 770515 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz662 := qz753

noncomputable abbrev qz484 := qz662

noncomputable abbrev qz170 := (@HPow.hPow Real Real Real qz351 qz484 qz353)

noncomputable abbrev qz754 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 770515 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz663 := qz754

noncomputable abbrev qz485 := qz663

noncomputable abbrev qz171 := qz485

noncomputable def Ns408p1103 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz169) qz169 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz170) (Zeta.RiemannSiegel.correction qz171)) 214273711 67108864 79379 67108864 1079621810721790350975 4722366482869645213696 1655891970152813509509 Ns408p1101 Ns408p1102 

noncomputable def Ns408p1104 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz169) qz169 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 770515 1000 195 242 268435456 134217728 4503599627370496 Bool.false 393827907700 2587 

noncomputable def Ns408p1105 := Ns408p1104 618095470 44 84886744 8 643680110 44 80936328 8 Bool.true 410473114 136198 Bool.true 200724855 Bool.true 96174616 14148475504056880 1 Bool.false 182535267 Bool.false Bool.false 251390321 Bool.true Bool.true 428547422 

noncomputable def Ns408p1106 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz169) qz169 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 770515 1000 86 143 268435456 134217728 4503599627370496 Bool.false 393827907700 2587 

noncomputable def Ns408p1107 := Ns408p1106 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 400444776 111114 Bool.true 7819585 Bool.true 334823719 14148475504056880 1 Bool.false 268321570 Bool.true Bool.false 254512979 Bool.false Bool.true 410473114 

noncomputable def Ns408p1108 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz169) qz169 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 770515 1000 55 20 268435456 134217728 4503599627370496 Bool.false 393827907700 2587 

noncomputable def Ns408p1109 := Ns408p1108 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 486718610 82406 Bool.false 40795029 Bool.true 218426374 14148475504056880 1 Bool.false 40638177 Bool.false Bool.false 184364868 Bool.false Bool.true 400444776 

noncomputable def Ns408p1110 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz169) qz169 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 770515 1000 253 144 268435456 134217728 4503599627370496 Bool.false 393827907700 2587 

noncomputable def Ns408p1111 := Ns408p1110 372130544 43 134217720 8 432030192 43 120047984 16 Bool.true 433314947 48544 Bool.false 416412238 Bool.false 223494640 14148475504056880 1 Bool.false 268384212 Bool.true Bool.false 180648436 Bool.false Bool.true 486718610 

noncomputable def Ns408p1112 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz169) qz169 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 770515 1000 593 395 268435456 134217728 4503599627370496 Bool.false 393827907700 2587 

noncomputable def Ns408p1113 := Ns408p1112 186065264 43 189812528 16 294906480 43 154981288 8 Bool.true 268435424 2635 Bool.false 418975847 Bool.false 43357097 14148475504056880 1 Bool.false 268422062 Bool.true Bool.false 43168826 Bool.false Bool.true 433314947 

noncomputable def Ns408p1114 := nat_lit 637126970429994734474527865182609449192889887818068937 

noncomputable def Ns408p1115 := nat_lit 434269551479984391206469208975694176438562114764800 

noncomputable def Ns408p1116 := nat_lit 130360851779326052494292114500000000 

noncomputable def Ns408p1117 := nat_lit 602670068683397995865743136633805000000 

noncomputable abbrev qz664 := (@Eq.refl Real qz752)

noncomputable abbrev qz486 := qz664

noncomputable abbrev qz172 := qz486

noncomputable def Ns408p1118 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz169 770515 1000 2374774460900 16000000 1541030 4000 2000 Ns408p1116 Ns408p1117 qz172 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns408p1119 := nat_lit 3185634852149973672372639325913047245964449439090344685000000 

noncomputable abbrev qz665 := (@HSub.hSub Real Real Real qz718 qz719 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz720 (@Nat.cast Real Real.instNatCast 1541030))))

noncomputable abbrev qz487 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 770515 4000) (Real.log (Enclosure.sfrac Bool.false 2374774460900 16000000))) (@HMul.hMul Real Real Real qz579 qz585 qz665))

noncomputable abbrev qz666 := (Enclosure.sfrac Bool.false 770515 2000)

noncomputable abbrev qz173 := (@HSub.hSub Real Real Real qz356 (@HSub.hSub Real Real Real qz356 qz487 qz666) (@HMul.hMul Real Real Real qz350 qz666 (Real.log Real.pi)))

noncomputable def Ns408p1120 := @Enclosure.Real.IsNear.addLit_ft_p qz173 (Enclosure.sfrac Bool.true Ns408p1116 Ns408p1117) 5285869478774392794017 3602879701896396800 7891650464524299 819200000000000000000 Ns408p1116 Ns408p1117 0 1 Ns408p1119 

noncomputable def Ns408p1121 := nat_lit 14189147838912864507850674667520 

noncomputable abbrev qz174 := (@HSub.hSub Real Real Real qz356 qz487 qz666)

noncomputable def Ns408p1122 := @Enclosure.Real.IsNear.subLit_ff_p qz174 (@HMul.hMul Real Real Real qz4 qz666 (Real.log Real.pi)) 1374959250889586097133 720575940379279360 3114062619851 800000000000000000 5919213502383 13421772800 154103 26843545600 Ns408p1121 5285869478774392794017 3602879701896396800 

noncomputable def Ns408p1123 := nat_lit 13749592508895860971330000 

noncomputable abbrev qz175 := qz487

noncomputable def Ns408p1124 := @Enclosure.Real.IsNear.subLit_ff_p qz175 qz666 8262832681201281575841 3602879701896396800 3114062619851 800000000000000000 770515 2000 0 1 Ns408p1123 1374959250889586097133 720575940379279360 3114062619851 800000000000000000 

noncomputable def Ns408p1125 := nat_lit 18606245092041424036966924915014893568 

noncomputable def Ns408p1126 := nat_lit 57582704995467369830678528 

noncomputable def Ns408p1127 := nat_lit 839763932351610604180331068052303826415134009743340851821183003305000000000000 

noncomputable def Ns408p1128 := nat_lit 1081338675617977479340710300415628502003674902109673299436552711000000000000 

noncomputable def Ns408p1129 := nat_lit 6867819246589551157296978387810669938391916213185305457615000000000000 

noncomputable def Ns408p1130 := BSN.log_dyadic_bound 277622460900 4471926460900 4 3 Ns408p1127 134217728 50000000 Ns408p1128 Ns408p1129 16686247 4749548921800 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 277622460900) (BSN.artanhQ 4471926460900) 0 3 Ns408p1128 Ns408p1127 Ns408p1129 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz488 := (Real.log (Enclosure.sfrac Bool.false 2374774460900 16000000))

noncomputable def Ns408p1131 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 770515 4000) qz488 770515 4000 0 1 53628073069702247 4503599627370496 20000017 1000000000000000 8264246944260325369441 3602879701896396800 3082062619751 800000000000000000 (Enclosure.Real.IsNear.const Bool.false 770515 4000) (BSN.isNear_log_sfrac 2374774460900 16000000 53628073069702247 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2374774460900) qz359)) Bool.false Ns408p1126 Ns408p100 1000000850000000 50000000000000000000000 53628073069702247 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2374774460900 16000000 17 4749548921800 4194304000000 16686247 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns408p1130 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns408p1132 := BSN.arctan_dyadic_bound_f 1000 1541030 1 0 16777216 6250000 0 1 1 0 1 1 10887 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1541030) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1541030) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns408p1133 := @Enclosure.Real.IsNear.subLit_ff_p qz12 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz13 (@Nat.cast Real Real.instNatCast 1541030))) 884279719003555 562949953421312 1 2000000000000000 10887 16777216 1 6250000 14829623013999049179136 883914411902371 562949953421312 320000001 2000000000000000 qz14 (Ns408p1132 rfl) rfl rfl 

noncomputable abbrev qz489 := (@HMul.hMul Real Real Real qz579 qz585 qz665)

noncomputable abbrev qz176 := qz489

noncomputable abbrev qz490 := qz665

noncomputable abbrev qz177 := qz490

noncomputable def Ns408p1134 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 770515 4000) qz488) qz176 8264246944260325369441 3602879701896396800 3082062619751 800000000000000000 883914411902371 2251799813685248 320000001 8000000000000000 Ns408p1125 8262832681201281575841 3602879701896396800 3114062619851 800000000000000000 (Ns408p1131 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz16 qz177 1 4 0 1 883914411902371 562949953421312 320000001 2000000000000000 883914411902371 2251799813685248 320000001 8000000000000000 qz367 Ns408p1133 rfl) 

noncomputable def Ns408p1135 := @Ns408p1120 Ns408p1114 Ns408p1115 7891650464524299 819200000000000000000 (@Ns408p1122 7891650464524299 819200000000000000000 (Ns408p1124 (Ns408p1134 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 770515 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz666 (Real.log Real.pi) 770515 2000 0 1 38410761 33554432 1 67108864 5919213502383 13421772800 154103 26843545600 (Enclosure.Real.IsNear.const Bool.false 770515 2000) RS409to420.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns408p1116 Ns408p1117) 

noncomputable def Ns408p1136 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz169) Bool.false Ns408p1114 Ns408p1115 7891650464524299 819200000000000000000 24614244231 16777216 81 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz169) (@HAdd.hAdd Real Real Real qz368 qz173 (Enclosure.sfrac Bool.true Ns408p1116 Ns408p1117)) Bool.false Ns408p1114 Ns408p1115 7891650464524299 819200000000000000000 Ns408p1118 (Ns408p1135 rfl rfl)) 

noncomputable def Ns408p1137 := nat_lit 3796778792911630019592192 

noncomputable def Ns408p1138 := nat_lit 3506488973861100368736440792288785912896552614008323770894369684514152151797419274222703426868591687133067547931723399623563711907681586721 

noncomputable def Ns408p1139 := nat_lit 2493365136797972069185418213312513252839181055109793673574226477925145420799873729475469160586242049396265162432153533058712130866721 

noncomputable def Ns408p1140 := nat_lit 17510685519270875250351985222098948905989125990265704662772703386916192432034579893668221268273981453916092262467597142805707242312262798881 

noncomputable def Ns408p1141 := BSN.sin_dyadic_bound_f 107910943623 68719476736 4 3 33554432 12512208 Ns408p1138 Ns408p114 Ns408p1139 Ns408p1140 Ns408p117 Ns408p1139 33554428 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107910943623) qz591 0 3 Ns408p1138 Ns408p114 Ns408p1139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107910943623) qz592 0 3 Ns408p1140 Ns408p117 Ns408p1139 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1142 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz169) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24614244231) qz369) Bool.false 24614244231 16777216 81 8388608 Bool.true 33554428 33554432 1 6250000 (Ns408p1136 rfl) (Enclosure.sfrac_false_div 24614244231 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24614244231) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns408p1137) qz593) 226375608064910080 72057594037927936 Bool.false 33554428 33554432 233 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q1 24614244231 16777216 226375608064910080 72057594037927936 233 Ns408p1137 Ns408p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554428 33554432 Ns408p1137 Ns408p112 107910943623 68719476736 12512208 12500000 (Ns408p1141 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns408p1143 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz169) Bool.false Ns408p1114 Ns408p1115 7891650464524299 819200000000000000000 393827907700 268435456 2587 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz169) (@HAdd.hAdd Real Real Real qz368 qz173 (Enclosure.sfrac Bool.true Ns408p1116 Ns408p1117)) Bool.false Ns408p1114 Ns408p1115 7891650464524299 819200000000000000000 Ns408p1118 (Ns408p1135 rfl rfl)) 

noncomputable def Ns408p1144 := Ns408p1113 48544 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 593 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268422062 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 395 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 43168826 268435456) qz172 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz169) qz169 1) Bool.true 8388607 8388608 32164913 3276800000000 268435424 268435456 2635 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz169) qz169 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz169)) Bool.true 8388607 8388608 32164913 3276800000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz169) qz169) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz169)) Bool.true 33554428 33554432 514638608 52428800000000 8388607 8388608 32164913 3276800000000 (Ns408p1142 rfl rfl) rfl)) rfl) (Ns408p1143 rfl) RS409to420.d7 

noncomputable def Ns408p1145 := nat_lit 43194238419264392827001972777985753431446136352911951692285233493450055623911297592404744714666909106896500641 

noncomputable def Ns408p1146 := nat_lit 29259564059016238988882347892383997436335056036774119182401203674440756461994193688801201123404899547041 

noncomputable def Ns408p1147 := nat_lit 215709573108742836243009969023718032337819440073323140513922277882601115792605626876615766027111380890258896801 

noncomputable def Ns408p1148 := BSN.sin_dyadic_bound_f 418975847 268435456 4 3 268435456 134217728 Ns408p1145 Ns408p269 Ns408p1146 Ns408p1147 Ns408p272 Ns408p1146 268422062 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 418975847) qz372 0 3 Ns408p1145 Ns408p269 Ns408p1146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 418975847) qz373 0 3 Ns408p1147 Ns408p272 Ns408p1146 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1149 := nat_lit 3533790380894750724680987573281 

noncomputable def Ns408p1150 := BSN.sin_dyadic_bound_f 43357097 268435456 2 1 268435456 134217728 Ns408p1149 Ns408p133 Ns408p1149 Ns408p1149 Ns408p134 Ns408p1149 43168826 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 43357097) qz372 0 1 Ns408p1149 Ns408p133 Ns408p1149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 43357097) qz373 0 1 Ns408p1149 Ns408p134 Ns408p1149 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1151 := nat_lit 42144719262614286180483213684202130623181225725566235270720783028015868196230701811906888433992148477490630656 

noncomputable def Ns408p1152 := nat_lit 27182025455084525796991399752392337785523576935007523724326767878749106028408725130957507984188034912256 

noncomputable def Ns408p1153 := nat_lit 210474515356632605625224078357369515996775416917003431065944388655381369099898706250861813297005816778232303616 

noncomputable def Ns408p1154 := BSN.sin_dyadic_bound_f 416412238 268435456 4 3 268435456 134217728 Ns408p1151 Ns408p269 Ns408p1152 Ns408p1153 Ns408p272 Ns408p1152 268384212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 416412238) qz372 0 3 Ns408p1151 Ns408p269 Ns408p1152 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 416412238) qz373 0 3 Ns408p1153 Ns408p272 Ns408p1152 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1155 := nat_lit 21770151150265295325821678341441592879287649895444923083888839884800000 

noncomputable def Ns408p1156 := nat_lit 6224964748307816752683526026927720809118329663505695349145600000000 

noncomputable def Ns408p1157 := nat_lit 65298003521299270343959667972270923196244713027007757860968228454400000 

noncomputable def Ns408p1158 := BSN.cos_dyadic_bound_f 223494640 268435456 3 2 268435456 134217728 Ns408p1155 Ns408p123 Ns408p1156 Ns408p1157 Ns408p126 Ns408p1156 180648436 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 223494640) qz370 0 2 Ns408p1155 Ns408p123 Ns408p1156 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 223494640) qz371 0 2 Ns408p1157 Ns408p126 Ns408p1156 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1159 := Ns408p1111 82406 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 253 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268384212 268435456) BSN.abs_quadSignPos qz606 (BSN.sfrac_eq_quadSignPos_mul Bool.false 180648436 268435456) qz172 rfl rfl (Ns408p1144 RS409to420.d9 RS409to420.d11 RS409to420.d13 RS409to420.d17 (Ns408p1148 rfl rfl) (Ns408p1150 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns408p1143 rfl) RS409to420.d19 RS409to420.d21 RS409to420.d23 RS409to420.d25 RS409to420.d17 (Ns408p1154 rfl rfl) (Ns408p1158 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns408p1160 := nat_lit 2769676108556071689277947727281 

noncomputable def Ns408p1161 := BSN.sin_dyadic_bound_f 40795029 268435456 2 1 268435456 134217728 Ns408p1160 Ns408p133 Ns408p1160 Ns408p1160 Ns408p134 Ns408p1160 40638177 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 40795029) qz372 0 1 Ns408p1160 Ns408p133 Ns408p1160 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 40795029) qz373 0 1 Ns408p1160 Ns408p134 Ns408p1160 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1162 := nat_lit 19861059576218221965202507764795098406517328351721622961740487240294656 

noncomputable def Ns408p1163 := nat_lit 5181322327804128007834357425802315585601665343425484061322653573376 

noncomputable def Ns408p1164 := nat_lit 59572816083999057639591854579533690588380781724478017917098816413737216 

noncomputable def Ns408p1165 := BSN.cos_dyadic_bound_f 218426374 268435456 3 2 268435456 134217728 Ns408p1162 Ns408p123 Ns408p1163 Ns408p1164 Ns408p126 Ns408p1163 184364868 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 218426374) qz370 0 2 Ns408p1162 Ns408p123 Ns408p1163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 218426374) qz371 0 2 Ns408p1164 Ns408p126 Ns408p1163 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1166 := Ns408p1109 111114 BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 40638177 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 184364868 268435456) qz172 rfl rfl (Ns408p1159 rfl rfl) (Ns408p1143 rfl) RS409to420.d27 RS409to420.d29 RS409to420.d31 RS409to420.d33 RS409to420.d17 (Ns408p1161 rfl rfl) (Ns408p1165 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1167 := nat_lit 3738822257414716882491450625 

noncomputable def Ns408p1168 := BSN.cos_dyadic_bound_f 7819585 268435456 2 1 268435456 134217728 Ns408p1167 Ns408p149 Ns408p1167 Ns408p1167 Ns408p150 Ns408p1167 268321570 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7819585) qz370 0 1 Ns408p1167 Ns408p149 Ns408p1167 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7819585) qz371 0 1 Ns408p1167 Ns408p150 Ns408p1167 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1169 := nat_lit 17596670232934008294313054262778747929725342575684197797689256363721350669309599218870964141881182477377881761 

noncomputable def Ns408p1170 := nat_lit 1985155774380930336940507682072853736731496703819092815139388889174683865482293804569856019627270489761 

noncomputable def Ns408p1171 := nat_lit 87939842873439368220086610214095346496035282361395315215551719522266552856997665359826007645449377147344668321 

noncomputable def Ns408p1172 := BSN.sin_dyadic_bound_f 334823719 268435456 4 3 268435456 134217728 Ns408p1169 Ns408p269 Ns408p1170 Ns408p1171 Ns408p272 Ns408p1170 254512979 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 334823719) qz372 0 3 Ns408p1169 Ns408p269 Ns408p1170 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 334823719) qz373 0 3 Ns408p1171 Ns408p272 Ns408p1170 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1173 := Ns408p1107 136198 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268321570 268435456) BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 254512979 268435456) qz172 rfl rfl (Ns408p1166 rfl) (Ns408p1143 rfl) RS409to420.d35 RS409to420.d37 RS409to420.d39 RS409to420.d41 RS409to420.d17 (Ns408p1168 rfl rfl) (Ns408p1172 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1174 := nat_lit 25491231112133096646933901332454062404352488589742731615927163002530625 

noncomputable def Ns408p1175 := nat_lit 2635173551101749752933785724322068365384277839454334979676937890625 

noncomputable def Ns408p1176 := nat_lit 66758481679361088385226896408111737234045895570919466261270711869090625 

noncomputable def Ns408p1177 := BSN.sin_dyadic_bound_f 200724855 268435456 3 2 268435456 134217728 Ns408p1174 Ns408p142 Ns408p1175 Ns408p1176 Ns408p145 Ns408p1175 182535267 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 200724855) qz372 0 2 Ns408p1174 Ns408p142 Ns408p1175 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 200724855) qz373 0 2 Ns408p1176 Ns408p145 Ns408p1175 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1178 := nat_lit 746302505067350964309858339760348879545249241060764169079794671026176 

noncomputable def Ns408p1179 := nat_lit 7319538301069482349443736620371201333822719411215914253571588096 

noncomputable def Ns408p1180 := nat_lit 2238892876125450753964876131807805896233080077743470075410876869902336 

noncomputable def Ns408p1181 := BSN.cos_dyadic_bound_f 96174616 268435456 3 2 268435456 134217728 Ns408p1178 Ns408p123 Ns408p1179 Ns408p1180 Ns408p126 Ns408p1179 251390321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 96174616) qz370 0 2 Ns408p1178 Ns408p123 Ns408p1179 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 96174616) qz371 0 2 Ns408p1180 Ns408p126 Ns408p1179 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1182 := Ns408p1105 158758 BSN.abs_quadSignPos qz415 (BSN.sfrac_eq_quadSignPos_mul Bool.false 182535267 268435456) BSN.abs_quadSignNeg qz395 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 251390321 268435456) qz172 rfl rfl (Ns408p1173 rfl) (Ns408p1143 rfl) RS409to420.d43 RS409to420.d45 RS409to420.d52 RS409to420.d54 RS409to420.d17 (Ns408p1177 rfl rfl) (Ns408p1181 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1183 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz169) qz169 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz169) qz169 11) 428547422 268435456 158758 268435456 428547422 268435456 158758 268435456 230074645284388864 214273711 67108864 79379 67108864 (Ns408p1182 rfl) 

noncomputable def Ns408p1184 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz4 qz33 qz170) (Zeta.RiemannSiegel.correction qz171) 2520807 8388608 1 16777216 428284200544425 562949953421312 3251263967139591 219902325555200000000 1079621810721790350975 4722366482869645213696 

noncomputable def Ns408p1185 := @Enclosure.Real.IsNear.mulLit_tf qz33 qz170 1 1 0 1 2520807 8388608 1 16777216 2520807 8388608 1 16777216 

noncomputable abbrev qz178 := qz484

noncomputable def Ns408p1186 := @Enclosure.Real.IsNear.sqrt_image qz178 822964418359 6710886400 154103 6710886400 185789189 185789225 16777216 (@Enclosure.Real.IsNear.of_eq qz178 (@HMul.hMul Real Real Real qz4 qz169 qz2) Bool.false 822964418359 6710886400 154103 6710886400 (BSN.t_div_two_pi_mk qz169 770515 1000 qz172) (@Enclosure.Real.IsNear.mulLit_ff qz169 qz2 770515 1000 0 1 5340353 33554432 1 33554432 822964418359 6710886400 154103 6710886400 (Enclosure.Real.IsNear.const Bool.false 770515 1000) RS409to420.d48 rfl)) 

noncomputable abbrev qz755 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 770515 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz667 := qz755

noncomputable abbrev qz491 := qz667

noncomputable abbrev qz179 := qz491

noncomputable def Ns408p1187 := @Enclosure.Real.IsNear.sqrt_image qz179 185789207 16777216 9 8388608 55830326 55830332 16777216 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 371578414 33554432 36 33554432 185789207 16777216 9 8388608 (Ns408p1186 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns408p1188 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz179) 55830329 16777216 3 16777216 5041613 5041615 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz179) Bool.false 111660658 33554432 6 33554432 55830329 16777216 3 16777216 (Ns408p1187 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns408p1189 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 10083228 33554432 2 33554432 2520807 8388608 1 16777216 (Ns408p1188 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz180 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz485))

noncomputable abbrev qz668 := (@HMul.hMul Real Real Real qz714 qz754 qz754)

noncomputable abbrev qz492 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz668 qz663) qz598)

noncomputable abbrev qz181 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz492))

noncomputable def Ns408p1190 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz171) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv qz180) qz181) Bool.false 428284200544425 

noncomputable def Ns408p1191 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz180) qz181 37527723 33554432 293 

noncomputable def Ns408p1192 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz180) Bool.false 37527723 33554432 293 33554432 37527723 33554432 293 

noncomputable def Ns408p1193 := @Enclosure.Real.IsNear.recentre' qz180 Bool.false 15000909 16777216 364638608 52428800000000 15000909 16777216 22789913 3276800000000 

noncomputable abbrev qz182 := (@HMul.hMul Real Real Real qz350 qz347 qz485)

noncomputable def Ns408p1194 := @Enclosure.Real.IsNear.cos_image qz182 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15580175) qz418) Bool.false 15580175 33554432 57 8388608 Bool.false 15000909 16777216 1 

noncomputable def Ns408p1195 := nat_lit 242874678686721442694087679 

noncomputable def Ns408p1196 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz171 884279719003555 140737488355328 1 500000000000000 1239831 16777216 9 8388608 1096357408291896599205 2361183241434822606848 Ns408p1195 

noncomputable def Ns408p1197 := @Enclosure.Real.IsNear.subLit_ff_p qz179 qz31 185789207 16777216 9 8388608 11 1 0 1 1239831 1239831 16777216 9 

noncomputable def Ns408p1198 := @Ns408p1197 8388608 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 371578414 33554432 36 33554432 185789207 16777216 9 8388608 (Ns408p1186 rfl rfl rfl rfl rfl rfl) rfl) qz398 

noncomputable def Ns408p1199 := @Enclosure.Real.IsNear.recentre' qz182 Bool.false 1096357408291896599205 2361183241434822606848 Ns408p1195 Ns408p171 15580175 33554432 57 8388608 (@Ns408p1196 Ns408p171 RS409to420.d47 (Ns408p1198 rfl rfl) rfl) 

noncomputable def Ns408p1200 := nat_lit 125490309356905301343441504289491128123865403683211064962890625 

noncomputable def Ns408p1201 := nat_lit 3471991486961447719851231776191219999654392334136962890625 

noncomputable def Ns408p1202 := nat_lit 376463984087741981134884810404921001931596902264964920962890625 

noncomputable def Ns408p1203 := BSN.cos_dyadic_bound_f 15580175 33554432 3 2 16777216 6250000 Ns408p1200 Ns408p489 Ns408p1201 Ns408p1202 Ns408p492 Ns408p1201 15000909 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 15580175) qz619 0 2 Ns408p1200 Ns408p489 Ns408p1201 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 15580175) (BSN.cosOddQ 33554432) 0 2 Ns408p1202 Ns408p492 Ns408p1201 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1204 := @Enclosure.Real.IsNear.inv_image qz180 15000909 16777216 22789913 3276800000000 18763715 18764008 16777216 (Ns408p1193 (@Ns408p1194 6250000 (Ns408p1199 rfl) (Enclosure.sfrac_false_div 15580175 33554432) (Ns408p1203 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns408p1205 := @Enclosure.Real.IsNear.recentre' qz181 Bool.false 11412475 16777216 

noncomputable abbrev qz183 := (@HMul.hMul Real Real Real qz350 qz347 qz492)

noncomputable def Ns408p1206 := @Enclosure.Real.IsNear.cos_image qz183 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 862675)) (@Nat.cast Real Real.instNatCast 1048576)) Bool.true 862675 1048576 

noncomputable def Ns408p1207 := nat_lit 32590940482247832062530677805 

noncomputable def Ns408p1208 := nat_lit 73078319196240042900225009880231 

noncomputable def Ns408p1209 := @Enclosure.Real.IsNear.recentre' qz183 Bool.true Ns408p1207 Ns408p187 Ns408p1208 

noncomputable def Ns408p1210 := nat_lit 9444732965739290427392000000000000000 

noncomputable abbrev qz184 := qz492

noncomputable def Ns408p1211 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz184 884279719003555 140737488355328 1 500000000000000 36855917626351 

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz584 qz668 qz663)

noncomputable abbrev qz185 := qz493

noncomputable def Ns408p1212 := @Enclosure.Real.IsNear.subLit_tf qz185 qz28 19263731581935 281474976710656 2708001 2199023255552 1 16 

noncomputable abbrev qz494 := qz668

noncomputable abbrev qz186 := qz494

noncomputable def Ns408p1213 := @Enclosure.Real.IsNear.subLit_ff_n qz186 qz171 1537180908561 281474976710656 348705 2199023255552 1239831 16777216 9 8388608 

noncomputable def Ns408p1214 := @Enclosure.Real.IsNear.mulLit_ff qz171 qz171 1239831 16777216 9 8388608 1239831 16777216 9 8388608 1537180908561 281474976710656 

noncomputable def Ns408p1215 := nat_lit 1125164961634893238016542131925915329477741525390625 

noncomputable def Ns408p1216 := nat_lit 58927746017182005661972572455120531352527200132792320 

noncomputable def Ns408p1217 := nat_lit 306745146803978821184781010669957397613525390625 

noncomputable def Ns408p1218 := nat_lit 3374881394611071756407256833756406073637997525390625 

noncomputable def Ns408p1219 := nat_lit 2651748570773190254788765760480423910863724005975654400 

noncomputable def Ns408p1220 := BSN.cos_dyadic_bound_f 862675 1048576 3 2 16777216 6250000 Ns408p1215 Ns408p1216 Ns408p1217 Ns408p1218 Ns408p1219 Ns408p1217 11412475 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 862675) (BSN.cosEvenQ 1048576) 0 2 Ns408p1215 Ns408p1216 Ns408p1217 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 862675) (BSN.cosOddQ 1048576) 0 2 Ns408p1218 Ns408p1219 Ns408p1217 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1221 := @Ns408p1205 414638608 52428800000000 11412475 16777216 25914913 3276800000000 (@Ns408p1206 65 8388608 Bool.false 11412475 16777216 1 6250000 (@Ns408p1209 Ns408p1210 862675 1048576 65 8388608 (@Ns408p1211 281474976710656 2708001 2199023255552 Ns408p1207 Ns408p187 Ns408p1208 Ns408p1210 RS409to420.d47 (@Ns408p1212 0 1 589694682021616 36855917626351 281474976710656 2708001 2199023255552 (@Ns408p1213 323191785716145192960 19263731581935 281474976710656 2708001 2199023255552 (@Ns408p1214 348705 2199023255552 (Ns408p1198 rfl rfl) (Ns408p1198 rfl rfl) rfl) (Ns408p1198 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 862675 1048576) (BSN.cos_neg_of_bound 862675 1048576 Bool.false 11412475 16777216 1 6250000 (Ns408p1220 rfl rfl)) rfl rfl) 

noncomputable def Ns408p1222 := @Ns408p1184 1655891970152813509509 Ns408p1101 (Ns408p1185 qz51 (@Enclosure.Real.IsNear.of_eq qz170 (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 2520807 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz178 (BSN.t_div_two_pi_nonneg qz169 770515 1000 qz172)) Ns408p1189) rfl) (@Ns408p1190 562949953421312 3251263967139591 219902325555200000000 (BSN.correction_mk qz171 (BSN.cos_two_pi_p_ne_zero_mk qz169 770515 1000 11 qz172 rfl rfl (@BSN.floor_sqrt_eq_dec qz169 770515 1000 11 qz172 rfl rfl rfl))) (@Ns408p1191 33554432 11412475 16777216 25914913 3276800000000 428284200544425 562949953421312 3251263967139591 219902325555200000000 (@Ns408p1192 33554432 (Ns408p1204 rfl rfl rfl rfl rfl) rfl) (Ns408p1221 rfl) rfl)) 

noncomputable def Ns408p1223 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz169) (hardyZApproximantRS₀ qz169) Bool.true 13998550142635918240129 4722366482869645213696 438046559476308333509509 Ns408p1101 (@Eq.refl Real (hardyZApproximantRS₀ qz169)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz169) (@HSub.hSub Real Real Real qz30 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz169) qz169 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz170) (Zeta.RiemannSiegel.correction qz171))) Bool.true 13998550142635918240129 4722366482869645213696 438046559476308333509509 Ns408p1101 (BSN.hardyZApproximantRS₀_eq qz169 11 (@BSN.floor_sqrt_eq_dec qz169 770515 1000 11 qz172 rfl rfl rfl)) (@Ns408p1103 13998550142635918240129 4722366482869645213696 438046559476308333509509 Ns408p1101 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz169) qz169 11) (@HAdd.hAdd Real Real Real qz368 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz169) qz169 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz169) qz169 11)) Bool.true 214273711 67108864 79379 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz169) qz169 11) (Ns408p1183 (Ns408p1182 rfl) rfl rfl)) (Ns408p1222 rfl) rfl rfl)) 

theorem RS409to420.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz169) Bool.true 13998550142635918240129 4722366482869645213696 438046559476308333509509 Ns408p1101 := Ns408p1223 

noncomputable def Ns408p1224 := nat_lit 922337203685477580800000000 

noncomputable def Ns408p1225 := nat_lit 94444683467200167504322232320 

noncomputable abbrev qz756 := (Enclosure.sfrac Bool.false 771821 1000)

noncomputable abbrev qz669 := qz756

noncomputable abbrev qz495 := qz669

noncomputable abbrev qz187 := qz495

noncomputable abbrev qz757 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 771821 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz670 := qz757

noncomputable abbrev qz496 := qz670

noncomputable abbrev qz188 := (@HPow.hPow Real Real Real qz351 qz496 qz353)

noncomputable abbrev qz758 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 771821 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz671 := qz758

noncomputable abbrev qz497 := qz671

noncomputable abbrev qz189 := qz497

noncomputable def Ns408p1226 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz187) qz187 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz188) (Zeta.RiemannSiegel.correction qz189)) 76256805 16777216 159029 134217728 263246206135664798875 1180591620717411303424 4259612502977236324429 Ns408p1224 Ns408p1225 

noncomputable def Ns408p1227 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz187) qz187 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 771821 1000 195 242 268435456 134217728 4503599627370496 Bool.false 394671049850 2591 

noncomputable def Ns408p1228 := Ns408p1227 618095470 44 84886744 8 643680110 44 80936328 8 Bool.false 637206335 136431 Bool.true 164815388 Bool.true 93678689 14148475504056880 1 Bool.false 154653540 Bool.false Bool.false 252254669 Bool.true Bool.false 610054440 

noncomputable def Ns408p1229 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz187) qz187 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 771821 1000 85 143 268435456 134217728 4503599627370496 Bool.false 394671049850 2591 

noncomputable def Ns408p1230 := Ns408p1229 558195838 44 94906264 8 589812974 44 89478488 8 Bool.false 650656665 111305 Bool.true 315338628 Bool.true 261977313 14148475504056880 1 Bool.false 247654500 Bool.true Bool.false 222326266 Bool.false Bool.false 637206335 

noncomputable def Ns408p1231 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz187) qz187 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 771821 1000 55 20 268435456 134217728 4503599627370496 Bool.false 394671049850 2591 

noncomputable def Ns408p1232 := Ns408p1231 480971758 44 109588312 8 522351262 44 101459064 8 Bool.false 462189997 82548 Bool.false 255788064 Bool.true 57474972 14148475504056880 1 Bool.false 218799096 Bool.false Bool.false 262305915 Bool.false Bool.false 650656665 

noncomputable def Ns408p1233 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz187) qz187 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 771821 1000 254 145 268435456 134217728 4503599627370496 Bool.false 394671049850 2591 

noncomputable def Ns408p1234 := Ns408p1233 372130544 43 134217720 8 432030192 43 120047984 16 Bool.false 532249571 48629 Bool.false 351894469 Bool.false 80747931 14148475504056880 1 Bool.false 68980292 Bool.true Bool.false 79535664 Bool.true Bool.false 462189997 

noncomputable def Ns408p1235 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz187) qz187 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 771821 1000 595 396 268435456 134217728 4503599627370496 Bool.false 394671049850 2591 

noncomputable def Ns408p1236 := Ns408p1235 186065264 43 189812528 16 294906480 43 154981288 8 Bool.false 268435280 2643 Bool.false 175801905 Bool.false 79693956 14148475504056880 1 Bool.false 163501445 Bool.false Bool.false 256692195 Bool.false Bool.false 532249571 

noncomputable def Ns408p1237 := nat_lit 50391554920940482862244668061180936678919224302710265457131 

noncomputable def Ns408p1238 := nat_lit 34273808603105178516392989590797133716193512968421376000 

noncomputable def Ns408p1239 := nat_lit 131469391652621270994170222288480000 

noncomputable def Ns408p1240 := nat_lit 608825143244210283135817533498317532480 

noncomputable abbrev qz672 := (@Eq.refl Real qz756)

noncomputable abbrev qz498 := qz672

noncomputable abbrev qz190 := qz498

noncomputable def Ns408p1241 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz187 771821 1000 2382831624164 16000000 1543642 4000 2000 Ns408p1239 Ns408p1240 qz190 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns408p1242 := nat_lit 16125297574700954515918293779577899737254151776867284946281920 

noncomputable abbrev qz673 := (@HSub.hSub Real Real Real qz718 qz719 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz720 (@Nat.cast Real Real.instNatCast 1543642))))

noncomputable abbrev qz499 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 771821 4000) (Real.log (Enclosure.sfrac Bool.false 2382831624164 16000000))) (@HMul.hMul Real Real Real qz579 qz585 qz673))

noncomputable abbrev qz674 := (Enclosure.sfrac Bool.false 771821 2000)

noncomputable abbrev qz191 := (@HSub.hSub Real Real Real qz356 (@HSub.hSub Real Real Real qz356 qz499 qz674) (@HMul.hMul Real Real Real qz350 qz674 (Real.log Real.pi)))

noncomputable def Ns408p1243 := @Enclosure.Real.IsNear.addLit_ft_p qz191 (Enclosure.sfrac Bool.true Ns408p1239 Ns408p1240) 26485929699153096826779 18014398509481984000 39524855182387593 4096000000000000000000 Ns408p1239 Ns408p1240 0 1 Ns408p1242 

noncomputable def Ns408p1244 := nat_lit 355488130818805218025428693811200 

noncomputable abbrev qz192 := (@HSub.hSub Real Real Real qz356 qz499 qz674)

noncomputable def Ns408p1245 := @Enclosure.Real.IsNear.subLit_ff_p qz192 (@HMul.hMul Real Real Real qz4 qz674 (Real.log Real.pi)) 6888805899113859191583 3602879701896396800 15596433121457 4000000000000000000 29646231965781 67108864000 771821 134217728000 Ns408p1244 26485929699153096826779 18014398509481984000 

noncomputable def Ns408p1246 := nat_lit 68888058991138591915830000 

noncomputable abbrev qz193 := qz499

noncomputable def Ns408p1247 := @Enclosure.Real.IsNear.subLit_ff_p qz193 qz674 41395975031562743144347 18014398509481984000 15596433121457 4000000000000000000 771821 2000 0 1 Ns408p1246 6888805899113859191583 3602879701896396800 15596433121457 4000000000000000000 

noncomputable def Ns408p1248 := nat_lit 93215448863392163208635913221288493056 

noncomputable def Ns408p1249 := nat_lit 57599083866736175945351168 

noncomputable def Ns408p1250 := nat_lit 848883042568037869774266391410087673922735253082278134307867400506235802849280 

noncomputable def Ns408p1251 := nat_lit 1153436419273539255781379811373856792864520626541784037883175601916137926656 

noncomputable def Ns408p1252 := nat_lit 8153927658059071307216019117140879743768762969797713178458894760407040 

noncomputable def Ns408p1253 := BSN.log_dyadic_bound 285679624164 4479983624164 4 3 Ns408p1250 134217728 50000000 Ns408p1251 Ns408p1252 17140852 4765663248328 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 285679624164) (BSN.artanhQ 4479983624164) 0 3 Ns408p1251 Ns408p1250 Ns408p1252 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz500 := (Real.log (Enclosure.sfrac Bool.false 2382831624164 16000000))

noncomputable def Ns408p1254 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 771821 4000) qz500 771821 4000 0 1 53643327082261607 4503599627370496 20000017 1000000000000000 41403046351958235776347 18014398509481984000 15436433120957 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 771821 4000) (BSN.isNear_log_sfrac 2382831624164 16000000 53643327082261607 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2382831624164) qz359)) Bool.false Ns408p1249 Ns408p100 1000000850000000 50000000000000000000000 53643327082261607 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2382831624164 16000000 17 4765663248328 4194304000000 17140852 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns408p1253 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns408p1255 := BSN.arctan_dyadic_bound_f 1000 1543642 1 0 16777216 6250000 0 1 1 0 1 1 10868 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1543642) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1543642) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns408p1256 := @Enclosure.Real.IsNear.subLit_ff_p qz12 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz13 (@Nat.cast Real Real.instNatCast 1543642))) 884279719003555 562949953421312 1 2000000000000000 10868 16777216 1 6250000 14829633710048164184064 883915049436579 562949953421312 320000001 2000000000000000 qz14 (Ns408p1255 rfl) rfl rfl 

noncomputable abbrev qz501 := (@HMul.hMul Real Real Real qz579 qz585 qz673)

noncomputable abbrev qz194 := qz501

noncomputable abbrev qz502 := qz673

noncomputable abbrev qz195 := qz502

noncomputable def Ns408p1257 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 771821 4000) qz500) qz194 41403046351958235776347 18014398509481984000 15436433120957 4000000000000000000 883915049436579 2251799813685248 320000001 8000000000000000 Ns408p1248 41395975031562743144347 18014398509481984000 15596433121457 4000000000000000000 (Ns408p1254 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz16 qz195 1 4 0 1 883915049436579 562949953421312 320000001 2000000000000000 883915049436579 2251799813685248 320000001 8000000000000000 qz367 Ns408p1256 rfl) 

noncomputable def Ns408p1258 := @Ns408p1243 Ns408p1237 Ns408p1238 39524855182387593 4096000000000000000000 (@Ns408p1245 39524855182387593 4096000000000000000000 (Ns408p1247 (Ns408p1257 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 771821 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz674 (Real.log Real.pi) 771821 2000 0 1 38410761 33554432 1 67108864 29646231965781 67108864000 771821 134217728000 (Enclosure.Real.IsNear.const Bool.false 771821 2000) RS409to420.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns408p1239 Ns408p1240) 

noncomputable def Ns408p1259 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz187) Bool.false Ns408p1237 Ns408p1238 39524855182387593 4096000000000000000000 49333881231 33554432 325 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz187) (@HAdd.hAdd Real Real Real qz368 qz191 (Enclosure.sfrac Bool.true Ns408p1239 Ns408p1240)) Bool.false Ns408p1237 Ns408p1238 39524855182387593 4096000000000000000000 Ns408p1241 (Ns408p1258 rfl rfl)) 

noncomputable def Ns408p1260 := nat_lit 7590446417548138703224832 

noncomputable def Ns408p1261 := nat_lit 3500734394402102961187576172379152669198206260657373637404692264392934310652591059963723839531136990607110282983604176747698513673730759681 

noncomputable def Ns408p1262 := nat_lit 2481133997139137423392945864862782509166166030293671119650858527543980107141146054600300144506001722729950244613106404597755873172481 

noncomputable def Ns408p1263 := nat_lit 17481983856524539805752420163423116323881085533930477743441752244991494116621285158754993042511231291604864717568725090715213749485174103041 

noncomputable def Ns408p1264 := BSN.sin_dyadic_bound_f 107866731263 68719476736 4 3 33554432 12512208 Ns408p1261 Ns408p114 Ns408p1262 Ns408p1263 Ns408p117 Ns408p1262 33554410 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107866731263) qz591 0 3 Ns408p1261 Ns408p114 Ns408p1262 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107866731263) qz592 0 3 Ns408p1263 Ns408p117 Ns408p1262 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1265 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz187) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49333881231) qz418) Bool.false 49333881231 33554432 325 33554432 Bool.false 33554410 33554432 1 6250000 (Ns408p1259 rfl) (Enclosure.sfrac_false_div 49333881231 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49333881231) qz418) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns408p1260) qz430) 226375608064910080 72057594037927936 Bool.false 33554410 33554432 233 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 49333881231 33554432 226375608064910080 72057594037927936 233 Ns408p1260 Ns408p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554410 33554432 Ns408p1260 Ns408p100 107866731263 68719476736 12512208 12500000 (Ns408p1264 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns408p1266 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz187) Bool.false Ns408p1237 Ns408p1238 39524855182387593 4096000000000000000000 394671049850 268435456 2591 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz187) (@HAdd.hAdd Real Real Real qz368 qz191 (Enclosure.sfrac Bool.true Ns408p1239 Ns408p1240)) Bool.false Ns408p1237 Ns408p1238 39524855182387593 4096000000000000000000 Ns408p1241 (Ns408p1258 rfl rfl)) 

noncomputable def Ns408p1267 := Ns408p1236 48629 BSN.abs_quadSignPos (BSN.cos_quad_nat3 595 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 163501445 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 396 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 256692195 268435456) qz190 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz187) qz187 1) Bool.false 16777205 16777216 129050277 13107200000000 268435280 268435456 2643 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz187) qz187 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz187)) Bool.false 16777205 16777216 129050277 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz187) qz187) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz187)) Bool.false 33554410 33554432 2064804432 209715200000000 16777205 16777216 129050277 13107200000000 (Ns408p1265 rfl rfl) rfl)) rfl) (Ns408p1266 rfl) RS409to420.d7 

noncomputable def Ns408p1268 := nat_lit 14998990425032637588388694553487430474546335947652839654191419669130625 

noncomputable def Ns408p1269 := nat_lit 912407012402878271271062460710879311220590778767810813655562890625 

noncomputable def Ns408p1270 := nat_lit 39281592930398731880959761158006881247784141763544194067279228222090625 

noncomputable def Ns408p1271 := BSN.sin_dyadic_bound_f 175801905 268435456 3 2 268435456 134217728 Ns408p1268 Ns408p142 Ns408p1269 Ns408p1270 Ns408p145 Ns408p1269 163501445 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 175801905) qz372 0 2 Ns408p1268 Ns408p142 Ns408p1269 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 175801905) qz373 0 2 Ns408p1270 Ns408p145 Ns408p1269 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1272 := nat_lit 40336809380489413457577164964096 

noncomputable def Ns408p1273 := BSN.cos_dyadic_bound_f 79693956 268435456 2 1 268435456 134217728 Ns408p1272 Ns408p149 Ns408p1272 Ns408p1272 Ns408p150 Ns408p1272 256692195 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 79693956) qz370 0 1 Ns408p1272 Ns408p149 Ns408p1272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 79693956) qz371 0 1 Ns408p1272 Ns408p150 Ns408p1272 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1274 := nat_lit 8265277826260391593092121496018755621960048079950471655097381602255599998074629375610603458524839082095829841 

noncomputable def Ns408p1275 := nat_lit 3605365419477792147642067834514269805393961518675670412888009124061632328842973316395611419770957095761 

noncomputable def Ns408p1276 := nat_lit 50084008252624699708830319037383841587128722298883279580040063699011800520159074054237284156942488578710594385 

noncomputable def Ns408p1277 := BSN.cos_dyadic_bound_f 351894469 268435456 4 3 268435456 134217728 Ns408p1274 Ns408p252 Ns408p1275 Ns408p1276 Ns408p255 Ns408p1275 68980292 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 351894469) qz370 0 3 Ns408p1274 Ns408p252 Ns408p1275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 351894469) qz371 0 3 Ns408p1276 Ns408p255 Ns408p1275 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1278 := nat_lit 42513377876729769629773507739121 

noncomputable def Ns408p1279 := BSN.sin_dyadic_bound_f 80747931 268435456 2 1 268435456 134217728 Ns408p1278 Ns408p133 Ns408p1278 Ns408p1278 Ns408p134 Ns408p1278 79535664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 80747931) qz372 0 1 Ns408p1278 Ns408p133 Ns408p1278 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 80747931) qz373 0 1 Ns408p1278 Ns408p134 Ns408p1278 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1280 := Ns408p1234 82548 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 254 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 68980292 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 145 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 79535664 268435456) qz190 rfl rfl (Ns408p1267 RS409to420.d9 RS409to420.d11 RS409to420.d13 RS409to420.d17 (Ns408p1271 rfl rfl) (Ns408p1273 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns408p1266 rfl) RS409to420.d19 RS409to420.d21 RS409to420.d23 RS409to420.d25 RS409to420.d17 (Ns408p1277 rfl rfl) (Ns408p1279 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns408p1281 := nat_lit 67232736445319388866934351768151492515211723370053302795112051711672320 

noncomputable def Ns408p1282 := nat_lit 18324924705457834404886509268322214785478381750012909319987088326656 

noncomputable def Ns408p1283 := nat_lit 176056069383456229586267771711105196811139929541591962610203965863755776 

noncomputable def Ns408p1284 := BSN.sin_dyadic_bound_f 255788064 268435456 3 2 268435456 134217728 Ns408p1281 Ns408p142 Ns408p1282 Ns408p1283 Ns408p145 Ns408p1282 218799096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 255788064) qz372 0 2 Ns408p1281 Ns408p142 Ns408p1282 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 255788064) qz373 0 2 Ns408p1283 Ns408p145 Ns408p1282 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1285 := nat_lit 10912269255370106448893235814656 

noncomputable def Ns408p1286 := BSN.cos_dyadic_bound_f 57474972 268435456 2 1 268435456 134217728 Ns408p1285 Ns408p149 Ns408p1285 Ns408p1285 Ns408p150 Ns408p1285 262305915 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 57474972) qz370 0 1 Ns408p1285 Ns408p149 Ns408p1285 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 57474972) qz371 0 1 Ns408p1285 Ns408p150 Ns408p1285 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1287 := Ns408p1232 111305 BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 218799096 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 262305915 268435456) qz190 rfl rfl (Ns408p1280 rfl rfl) (Ns408p1266 rfl) RS409to420.d27 RS409to420.d29 RS409to420.d31 RS409to420.d33 RS409to420.d17 (Ns408p1284 rfl rfl) (Ns408p1286 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1288 := nat_lit 155354345800075960365940142448304500031108385485059730645423969506754560 

noncomputable def Ns408p1289 := nat_lit 97772650787265515730385339537632030298570034191735721540429702823936 

noncomputable def Ns408p1290 := nat_lit 406722130898924323456755939672022286318133800976941246236473510141689856 

noncomputable def Ns408p1291 := BSN.sin_dyadic_bound_f 315338628 268435456 3 2 268435456 134217728 Ns408p1288 Ns408p142 Ns408p1289 Ns408p1290 Ns408p145 Ns408p1289 247654500 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 315338628) qz372 0 2 Ns408p1288 Ns408p142 Ns408p1289 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 315338628) qz373 0 2 Ns408p1290 Ns408p145 Ns408p1289 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1292 := nat_lit 73982039813509210182195754749516041369060275241451017605739765749585665 

noncomputable def Ns408p1293 := nat_lit 22187556048840563179697053099505036849519271582546966466608322123521 

noncomputable def Ns408p1294 := nat_lit 193726562516064094327269371972285671621211023002190446259801068251191041 

noncomputable def Ns408p1295 := BSN.sin_dyadic_bound_f 261977313 268435456 3 2 268435456 134217728 Ns408p1292 Ns408p142 Ns408p1293 Ns408p1294 Ns408p145 Ns408p1293 222326266 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 261977313) qz372 0 2 Ns408p1292 Ns408p142 Ns408p1293 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 261977313) qz373 0 2 Ns408p1294 Ns408p145 Ns408p1293 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1296 := Ns408p1230 136431 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 85 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 247654500 268435456) BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 222326266 268435456) qz190 rfl rfl (Ns408p1287 rfl) (Ns408p1266 rfl) RS409to420.d35 RS409to420.d37 RS409to420.d39 RS409to420.d41 RS409to420.d17 (Ns408p1291 rfl rfl) (Ns408p1295 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1297 := nat_lit 11586512621223546759823256180211755556359897464783411373349038513520640 

noncomputable def Ns408p1298 := nat_lit 544480157658816768351617230808480517501227966784154621628708356096 

noncomputable def Ns408p1299 := nat_lit 30344746754377841524769292139323765107723777086296045917955321055215616 

noncomputable def Ns408p1300 := BSN.sin_dyadic_bound_f 164815388 268435456 3 2 268435456 134217728 Ns408p1297 Ns408p142 Ns408p1298 Ns408p1299 Ns408p145 Ns408p1298 154653540 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 164815388) qz372 0 2 Ns408p1297 Ns408p142 Ns408p1298 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 164815388) qz373 0 2 Ns408p1299 Ns408p145 Ns408p1298 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1301 := nat_lit 671793577465469511336518845368278718287405496232015917759298480853761 

noncomputable def Ns408p1302 := nat_lit 5930979657722199134033374405261332062073113869019481004801217281 

noncomputable def Ns408p1303 := nat_lit 2015368870437093089611288469356025632198092342468309714315885840126721 

noncomputable def Ns408p1304 := BSN.cos_dyadic_bound_f 93678689 268435456 3 2 268435456 134217728 Ns408p1301 Ns408p123 Ns408p1302 Ns408p1303 Ns408p126 Ns408p1302 252254669 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 93678689) qz370 0 2 Ns408p1301 Ns408p123 Ns408p1302 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 93678689) qz371 0 2 Ns408p1303 Ns408p126 Ns408p1302 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1305 := Ns408p1228 159029 BSN.abs_quadSignPos qz415 (BSN.sfrac_eq_quadSignPos_mul Bool.false 154653540 268435456) BSN.abs_quadSignNeg qz395 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 252254669 268435456) qz190 rfl rfl (Ns408p1296 rfl) (Ns408p1266 rfl) RS409to420.d43 RS409to420.d45 RS409to420.d52 RS409to420.d54 RS409to420.d17 (Ns408p1300 rfl rfl) (Ns408p1304 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1306 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz187) qz187 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz187) qz187 11) 610054440 268435456 159029 268435456 610054440 268435456 159029 268435456 327520483572449280 76256805 16777216 159029 134217728 (Ns408p1305 rfl) 

noncomputable def Ns408p1307 := @Enclosure.Real.IsNear.mulLit_tf (@HMul.hMul Real Real Real qz4 qz33 qz188) (Zeta.RiemannSiegel.correction qz189) 629935 2097152 1 16777216 417894236922325 562949953421312 3348600793536311 219902325555200000000 263246206135664798875 1180591620717411303424 

noncomputable def Ns408p1308 := @Enclosure.Real.IsNear.mulLit_tf qz33 qz188 1 1 0 1 629935 2097152 1 16777216 629935 2097152 1 16777216 

noncomputable abbrev qz196 := qz496

noncomputable def Ns408p1309 := @Enclosure.Real.IsNear.sqrt_image qz196 4121796592813 33554432000 771821 33554432000 185946576 185946612 16777216 (@Enclosure.Real.IsNear.of_eq qz196 (@HMul.hMul Real Real Real qz4 qz187 qz2) Bool.false 4121796592813 33554432000 771821 33554432000 (BSN.t_div_two_pi_mk qz187 771821 1000 qz190) (@Enclosure.Real.IsNear.mulLit_ff qz187 qz2 771821 1000 0 1 5340353 33554432 1 33554432 4121796592813 33554432000 771821 33554432000 (Enclosure.Real.IsNear.const Bool.false 771821 1000) RS409to420.d48 rfl)) 

noncomputable abbrev qz759 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 771821 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz675 := qz759

noncomputable abbrev qz503 := qz675

noncomputable abbrev qz197 := qz503

noncomputable def Ns408p1310 := @Enclosure.Real.IsNear.sqrt_image qz197 92973297 8388608 9 8388608 55853969 55853975 16777216 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 371893188 33554432 36 33554432 92973297 8388608 9 8388608 (Ns408p1309 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns408p1311 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz197) 13963493 4194304 3 16777216 5039479 5039481 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz197) Bool.false 111707944 33554432 6 33554432 13963493 4194304 3 16777216 (Ns408p1310 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns408p1312 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 10078960 33554432 2 33554432 629935 2097152 1 16777216 (Ns408p1311 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz198 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz497))

noncomputable abbrev qz676 := (@HMul.hMul Real Real Real qz714 qz758 qz758)

noncomputable abbrev qz504 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz676 qz671) qz598)

noncomputable abbrev qz199 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz504))

noncomputable def Ns408p1313 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz189) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv qz198) qz199) Bool.false 417894236922325 

noncomputable def Ns408p1314 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz198) qz199 38737925 33554432 311 

noncomputable def Ns408p1315 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz198) Bool.false 38737925 33554432 311 33554432 38737925 33554432 311 

noncomputable def Ns408p1316 := @Enclosure.Real.IsNear.recentre' qz198 Bool.false 14532269 16777216 1452304432 209715200000000 14532269 16777216 90769027 13107200000000 

noncomputable abbrev qz200 := (@HMul.hMul Real Real Real qz350 qz347 qz497)

noncomputable def Ns408p1317 := @Enclosure.Real.IsNear.cos_image qz200 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17557959) qz418) Bool.false 17557959 33554432 227 33554432 Bool.false 14532269 16777216 1 

noncomputable def Ns408p1318 := nat_lit 242874678687397414711903231 

noncomputable def Ns408p1319 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz189 884279719003555 140737488355328 1 500000000000000 698609 8388608 9 8388608 617765770213354554995 1180591620717411303424 Ns408p1318 

noncomputable def Ns408p1320 := @Enclosure.Real.IsNear.subLit_ff_p qz197 qz31 92973297 8388608 9 8388608 11 1 0 1 698609 698609 8388608 9 

noncomputable def Ns408p1321 := @Ns408p1320 8388608 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 371893188 33554432 36 33554432 92973297 8388608 9 8388608 (Ns408p1309 rfl rfl rfl rfl rfl rfl) rfl) qz398 

noncomputable def Ns408p1322 := @Enclosure.Real.IsNear.recentre' qz200 Bool.false 617765770213354554995 1180591620717411303424 Ns408p1318 Ns408p171 17557959 33554432 227 33554432 (@Ns408p1319 Ns408p171 RS409to420.d47 (Ns408p1321 rfl rfl) rfl) 

noncomputable def Ns408p1323 := nat_lit 202406451331630476652090488620771368214761409641445951592593601 

noncomputable def Ns408p1324 := nat_lit 9032172939828943434400733358069196875721684243094776445121 

noncomputable def Ns408p1325 := nat_lit 607201289649011772069402664395597966250532785555851665224890561 

noncomputable def Ns408p1326 := BSN.cos_dyadic_bound_f 17557959 33554432 3 2 16777216 6250000 Ns408p1323 Ns408p489 Ns408p1324 Ns408p1325 Ns408p492 Ns408p1324 14532269 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 17557959) qz619 0 2 Ns408p1323 Ns408p489 Ns408p1324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 17557959) (BSN.cosOddQ 33554432) 0 2 Ns408p1325 Ns408p492 Ns408p1324 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1327 := @Enclosure.Real.IsNear.inv_image qz198 14532269 16777216 90769027 13107200000000 19368807 19369118 16777216 (Ns408p1316 (@Ns408p1317 6250000 (Ns408p1322 rfl) (Enclosure.sfrac_false_div 17557959 33554432) (Ns408p1326 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns408p1328 := @Enclosure.Real.IsNear.recentre' qz199 Bool.false 10787729 16777216 

noncomputable abbrev qz201 := (@HMul.hMul Real Real Real qz350 qz347 qz504)

noncomputable def Ns408p1329 := @Enclosure.Real.IsNear.cos_image qz201 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 29272515)) qz418) Bool.true 29272515 33554432 

noncomputable def Ns408p1330 := nat_lit 8639721488178536869679969725 

noncomputable def Ns408p1331 := nat_lit 475346306267617897611058772057809 

noncomputable def Ns408p1332 := @Enclosure.Real.IsNear.recentre' qz201 Bool.true Ns408p1330 Ns408p609 Ns408p1331 

noncomputable def Ns408p1333 := nat_lit 60446290980731458735308800000000000000 

noncomputable abbrev qz202 := qz504

noncomputable def Ns408p1334 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz202 884279719003555 140737488355328 1 500000000000000 9770349022495 

noncomputable abbrev qz505 := (@HSub.hSub Real Real Real qz584 qz676 qz671)

noncomputable abbrev qz203 := qz505

noncomputable def Ns408p1335 := @Enclosure.Real.IsNear.subLit_tf qz203 qz28 5372302511391 70368744177664 88072515 70368744177664 1 16 

noncomputable abbrev qz506 := qz676

noncomputable abbrev qz204 := qz506

noncomputable def Ns408p1336 := @Enclosure.Real.IsNear.subLit_ff_n qz204 qz189 488054534881 70368744177664 12575043 70368744177664 698609 8388608 9 8388608 

noncomputable def Ns408p1337 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz189 698609 8388608 9 8388608 698609 8388608 9 8388608 488054534881 70368744177664 

noncomputable def Ns408p1338 := nat_lit 1564223130216530269259320723980252558867994237691766515404190625 

noncomputable def Ns408p1339 := nat_lit 539113612409963013525200601609496966619164992802085375390625 

noncomputable def Ns408p1340 := nat_lit 4691591163424770881750911770737538682670744383089695375461790625 

noncomputable def Ns408p1341 := BSN.cos_dyadic_bound_f 29272515 33554432 3 2 16777216 6250000 Ns408p1338 Ns408p489 Ns408p1339 Ns408p1340 Ns408p492 Ns408p1339 10787729 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 29272515) qz619 0 2 Ns408p1338 Ns408p489 Ns408p1339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 29272515) (BSN.cosOddQ 33554432) 0 2 Ns408p1340 Ns408p492 Ns408p1339 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1342 := @Ns408p1328 210444304 26214400000000 10787729 16777216 13152769 1638400000000 (@Ns408p1329 33 4194304 Bool.false 10787729 16777216 1 6250000 (@Ns408p1332 Ns408p1333 29272515 33554432 33 4194304 (@Ns408p1334 70368744177664 88072515 70368744177664 Ns408p1330 Ns408p609 Ns408p1331 Ns408p1333 RS409to420.d47 (@Ns408p1335 0 1 156325584359920 9770349022495 70368744177664 88072515 70368744177664 (@Ns408p1336 45066139825474633728 5372302511391 70368744177664 88072515 70368744177664 (@Ns408p1337 12575043 70368744177664 (Ns408p1321 rfl rfl) (Ns408p1321 rfl rfl) rfl) (Ns408p1321 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 29272515 33554432) (BSN.cos_neg_of_bound 29272515 33554432 Bool.false 10787729 16777216 1 6250000 (Ns408p1341 rfl rfl)) rfl rfl) 

noncomputable def Ns408p1343 := @Ns408p1307 4259612502977236324429 Ns408p1224 (Ns408p1308 qz51 (@Enclosure.Real.IsNear.of_eq qz188 (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 629935 2097152 1 16777216 (BSN.rpow_neg_quarter_mk qz196 (BSN.t_div_two_pi_nonneg qz187 771821 1000 qz190)) Ns408p1312) rfl) (@Ns408p1313 562949953421312 3348600793536311 219902325555200000000 (BSN.correction_mk qz189 (BSN.cos_two_pi_p_ne_zero_mk qz187 771821 1000 11 qz190 rfl rfl (@BSN.floor_sqrt_eq_dec qz187 771821 1000 11 qz190 rfl rfl rfl))) (@Ns408p1314 33554432 10787729 16777216 13152769 1638400000000 417894236922325 562949953421312 3348600793536311 219902325555200000000 (@Ns408p1315 33554432 (Ns408p1327 rfl rfl rfl rfl rfl) rfl) (Ns408p1342 rfl) rfl)) 

noncomputable def Ns408p1344 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz187) (hardyZApproximantRS₀ qz187) Bool.false 5629341808986673802395 1180591620717411303424 1097098579087911636324429 Ns408p1224 (@Eq.refl Real (hardyZApproximantRS₀ qz187)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz187) (@HSub.hSub Real Real Real qz30 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz187) qz187 11) (@HMul.hMul Real Real Real qz4 (@HMul.hMul Real Real Real qz4 qz33 qz188) (Zeta.RiemannSiegel.correction qz189))) Bool.false 5629341808986673802395 1180591620717411303424 1097098579087911636324429 Ns408p1224 (BSN.hardyZApproximantRS₀_eq qz187 11 (@BSN.floor_sqrt_eq_dec qz187 771821 1000 11 qz190 rfl rfl rfl)) (@Ns408p1226 5629341808986673802395 1180591620717411303424 1097098579087911636324429 Ns408p1224 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz187) qz187 11) (@HAdd.hAdd Real Real Real qz368 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz187) qz187 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz187) qz187 11)) Bool.false 76256805 16777216 159029 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz187) qz187 11) (Ns408p1306 (Ns408p1305 rfl) rfl rfl)) (Ns408p1343 rfl) rfl rfl)) 

theorem RS409to420.d64 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz187) Bool.false 5629341808986673802395 1180591620717411303424 1097098579087911636324429 Ns408p1224 := Ns408p1344 

noncomputable def Ns408p1345 := nat_lit 2198178820541559776355189 

noncomputable def Ns408p1346 := nat_lit 116447803598741985487073837056 

noncomputable abbrev qz760 := (Enclosure.sfrac Bool.false 773127 1000)

noncomputable abbrev qz677 := qz760

noncomputable abbrev qz507 := qz677

noncomputable abbrev qz205 := qz507

noncomputable abbrev qz206 := qz351

noncomputable abbrev qz761 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 773127 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz678 := qz761

noncomputable abbrev qz508 := qz678

noncomputable abbrev qz207 := qz508

noncomputable abbrev qz208 := qz353

noncomputable abbrev qz762 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 773127 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz679 := qz762

noncomputable abbrev qz509 := qz679

noncomputable abbrev qz209 := qz509

noncomputable abbrev qz680 := (@HMul.hMul Real Real Real qz4 qz33 (@HPow.hPow Real Real Real qz206 qz207 qz208))

noncomputable def Ns408p1347 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz205) qz205 11) (@HMul.hMul Real Real Real qz4 qz680 (Zeta.RiemannSiegel.correction qz209)) 63914111 67108864 159297 134217728 513570371056542782073 2361183241434822606848 8817523418641376355189 Ns408p75 Ns408p1346 

noncomputable def Ns408p1348 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz205) qz205 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 773127 1000 195 242 268435456 134217728 4503599627370496 Bool.false 395514488450 2596 

noncomputable def Ns408p1349 := Ns408p1348 618095470 44 84886744 8 643680110 44 80936328 8 Bool.true 90618538 136660 Bool.true 128609472 Bool.true 90886313 14148475504056880 1 Bool.false 123745377 Bool.false Bool.false 253195828 Bool.true Bool.true 127828222 

noncomputable def Ns408p1350 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz205) qz205 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 773127 1000 85 143 268435456 134217728 4503599627370496 Bool.false 395514488450 2596 

noncomputable def Ns408p1351 := Ns408p1350 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 83916491 111491 Bool.true 200903792 Bool.true 188834457 14148475504056880 1 Bool.false 182666426 Bool.true Bool.false 173640856 Bool.false Bool.true 90618538 

noncomputable def Ns408p1352 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz205) qz205 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 773127 1000 56 19 268435456 134217728 4503599627370496 Bool.false 395514488450 2596 

noncomputable def Ns408p1353 := Ns408p1352 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 285624450 82685 Bool.false 49420119 Bool.true 317884549 14148475504056880 1 Bool.false 263899062 Bool.false Bool.false 248625548 Bool.false Bool.true 83916491 

noncomputable def Ns408p1354 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz205) qz205 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 773127 1000 255 145 268435456 134217728 4503599627370496 Bool.false 395514488450 2596 

noncomputable def Ns408p1355 := Ns408p1354 372130544 43 134217720 8 432030192 43 120047984 16 Bool.true 286576954 48708 Bool.false 287673151 Bool.false 359955101 14148475504056880 1 Bool.false 235686108 Bool.false Bool.false 261375203 Bool.true Bool.true 285624450 

noncomputable def Ns408p1356 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz205) qz205 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 773127 1000 596 397 268435456 134217728 4503599627370496 Bool.false 395514488450 2596 

noncomputable def Ns408p1357 := Ns408p1356 186065264 43 189812528 16 294906480 43 154981288 8 Bool.true 268435392 2643 Bool.false 354581842 Bool.false 116327265 14148475504056880 1 Bool.false 66379750 Bool.false Bool.false 112720359 Bool.true Bool.true 286576954 

noncomputable def Ns408p1358 := nat_lit 5668235321642938474907990231372645515748591546716452348753 

noncomputable def Ns408p1359 := nat_lit 3847028055131603436400738153694273276889098119806976000 

noncomputable def Ns408p1360 := nat_lit 132585460020108791012122432515360000 

noncomputable def Ns408p1361 := nat_lit 615032513738790081838321615195192384320 

noncomputable abbrev qz763 := (@Eq.refl Real (Enclosure.sfrac Bool.false 773127 1000))

noncomputable abbrev qz681 := qz763

noncomputable abbrev qz510 := qz681

noncomputable abbrev qz210 := qz510

noncomputable def Ns408p1362 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz205 773127 1000 2390902432516 16000000 1546254 4000 2000 Ns408p1360 Ns408p1361 qz210 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns408p1363 := nat_lit 16324517726331662807735011866353219085355943654543382764408640 

noncomputable abbrev qz682 := (@HSub.hSub Real Real Real qz718 qz719 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz720 (@Nat.cast Real Real.instNatCast 1546254))))

noncomputable abbrev qz511 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 773127 4000) (Real.log (Enclosure.sfrac Bool.false 2390902432516 16000000))) (@HMul.hMul Real Real Real qz579 qz585 qz682))

noncomputable abbrev qz683 := (Enclosure.sfrac Bool.false 773127 2000)

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz356 (@HSub.hSub Real Real Real qz356 qz511 qz683) (@HMul.hMul Real Real Real qz350 qz683 (Real.log Real.pi)))

noncomputable def Ns408p1364 := @Enclosure.Real.IsNear.addLit_ft_p qz211 (Enclosure.sfrac Bool.true Ns408p1360 Ns408p1361) 26542531898910548911377 18014398509481984000 39591458042153691 4096000000000000000000 Ns408p1360 Ns408p1361 0 1 Ns408p1363 

noncomputable def Ns408p1365 := nat_lit 1781239163419649775058947145728000 

noncomputable abbrev qz212 := (@HSub.hSub Real Real Real qz356 qz511 qz683)

noncomputable def Ns408p1366 := @Enclosure.Real.IsNear.subLit_ff_p qz212 (@HMul.hMul Real Real Real qz4 qz683 (Real.log Real.pi)) 34514097613375258715409 18014398509481984000 15622553143659 4000000000000000000 29696396419647 67108864000 773127 134217728000 Ns408p1365 26542531898910548911377 18014398509481984000 

noncomputable def Ns408p1367 := nat_lit 69028195226750517430818000 

noncomputable abbrev qz213 := qz511

noncomputable def Ns408p1368 := @Enclosure.Real.IsNear.subLit_ff_p qz213 qz683 41477806551595397637393 18014398509481984000 15622553143659 4000000000000000000 773127 2000 0 1 Ns408p1367 34514097613375258715409 18014398509481984000 15622553143659 4000000000000000000 

noncomputable def Ns408p1369 := nat_lit 93399717064955275235409842247737278464 

noncomputable def Ns408p1370 := nat_lit 57615435031860074476732416 

noncomputable def Ns408p1371 := nat_lit 858100178473408292331480225654058193393194092006886126971718099937188027207680 

noncomputable def Ns408p1372 := nat_lit 1228501805437415318802524081442289128445623511785504277435070861313004302336 

noncomputable def Ns408p1373 := nat_lit 9637454650032679316887109772310257151431730684185118055800456072458240 

noncomputable def Ns408p1374 := BSN.log_dyadic_bound 293750432516 4488054432516 4 3 Ns408p1371 134217728 50000000 Ns408p1372 Ns408p1373 17594688 4781804865032 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 293750432516) (BSN.artanhQ 4488054432516) 0 3 Ns408p1372 Ns408p1371 Ns408p1373 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz512 := (Real.log (Enclosure.sfrac Bool.false 2390902432516 16000000))

noncomputable def Ns408p1375 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 773127 4000) qz512 773127 4000 0 1 53658555291462759 4503599627370496 20000017 1000000000000000 41484877876822728477393 18014398509481984000 15462553143159 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 773127 4000) (BSN.isNear_log_sfrac 2390902432516 16000000 53658555291462759 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2390902432516) qz359)) Bool.false Ns408p1370 Ns408p100 1000000850000000 50000000000000000000000 53658555291462759 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2390902432516 16000000 17 4781804865032 4194304000000 17594688 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns408p1374 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns408p1376 := BSN.arctan_dyadic_bound_f 1000 1546254 1 0 16777216 6250000 0 1 1 0 1 1 10850 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1546254) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1546254) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns408p1377 := @Enclosure.Real.IsNear.subLit_ff_p qz12 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz13 (@Nat.cast Real Real.instNatCast 1546254))) 884279719003555 562949953421312 1 2000000000000000 10850 16777216 1 6250000 14829643843147325767680 883915653416355 562949953421312 320000001 2000000000000000 qz14 (Ns408p1376 rfl) rfl rfl 

noncomputable abbrev qz513 := (@HMul.hMul Real Real Real qz579 qz585 qz682)

noncomputable abbrev qz214 := qz513

noncomputable abbrev qz514 := qz682

noncomputable abbrev qz215 := qz514

noncomputable def Ns408p1378 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 773127 4000) qz512) qz214 41484877876822728477393 18014398509481984000 15462553143159 4000000000000000000 883915653416355 2251799813685248 320000001 8000000000000000 Ns408p1369 41477806551595397637393 18014398509481984000 15622553143659 4000000000000000000 (Ns408p1375 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz16 qz215 1 4 0 1 883915653416355 562949953421312 320000001 2000000000000000 883915653416355 2251799813685248 320000001 8000000000000000 qz367 Ns408p1377 rfl) 

noncomputable def Ns408p1379 := @Ns408p1364 Ns408p1358 Ns408p1359 39591458042153691 4096000000000000000000 (@Ns408p1366 39591458042153691 4096000000000000000000 (Ns408p1368 (Ns408p1378 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 773127 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz683 (Real.log Real.pi) 773127 2000 0 1 38410761 33554432 1 67108864 29696396419647 67108864000 773127 134217728000 (Enclosure.Real.IsNear.const Bool.false 773127 2000) RS409to420.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns408p1360 Ns408p1361) 

noncomputable def Ns408p1380 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz205) Bool.false Ns408p1358 Ns408p1359 39591458042153691 4096000000000000000000 3089956941 2097152 325 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz205) (@HAdd.hAdd Real Real Real qz368 qz211 (Enclosure.sfrac Bool.true Ns408p1360 Ns408p1361)) Bool.false Ns408p1358 Ns408p1359 39591458042153691 4096000000000000000000 Ns408p1362 (Ns408p1379 rfl rfl)) 

noncomputable def Ns408p1381 := nat_lit 3504856850449439162592186845512703293875465612001540255454578559777593909194070465711559700369917686061914041594396194016758645844134400000 

noncomputable def Ns408p1382 := nat_lit 2489892054703266159939017407069276024106175590598974054677702066716090920672378928172201561441255297567826165500657614081000000000000 

noncomputable def Ns408p1383 := nat_lit 17502545117696840890108377362999431510061317774370954703425040094684470585336540089841152883882803709147728632478638346432300099076672000000 

noncomputable def Ns408p1384 := BSN.sin_dyadic_bound_f 107898409590 68719476736 4 3 33554432 12512208 Ns408p1381 Ns408p114 Ns408p1382 Ns408p1383 Ns408p117 Ns408p1382 33554424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107898409590) qz591 0 3 Ns408p1381 Ns408p114 Ns408p1382 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107898409590) qz592 0 3 Ns408p1383 Ns408p117 Ns408p1382 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1385 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz205) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3089956941) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 3089956941 2097152 325 33554432 Bool.true 33554424 33554432 1 6250000 (Ns408p1380 rfl) (Enclosure.sfrac_false_div 3089956941 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3089956941) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474542223855147267653632) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 33554424 33554432 234 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q1 3089956941 2097152 226375608064910080 72057594037927936 234 474542223855147267653632 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554424 33554432 474542223855147267653632 302231454903657293676544 107898409590 68719476736 12512208 12500000 (Ns408p1384 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns408p1386 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz205) Bool.false Ns408p1358 Ns408p1359 39591458042153691 4096000000000000000000 395514488450 268435456 2596 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz205) (@HAdd.hAdd Real Real Real qz368 qz211 (Enclosure.sfrac Bool.true Ns408p1360 Ns408p1361)) Bool.false Ns408p1358 Ns408p1359 39591458042153691 4096000000000000000000 Ns408p1362 (Ns408p1379 rfl rfl)) 

noncomputable def Ns408p1387 := Ns408p1357 48708 BSN.abs_quadSignPos (BSN.cos_quad_nat0 596 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66379750 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 397 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 112720359 268435456) qz210 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 1) Bool.true 4194303 4194304 129050277 13107200000000 268435392 268435456 2643 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz205)) Bool.true 4194303 4194304 129050277 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz205) qz205) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz205)) Bool.true 33554424 33554432 2064804432 209715200000000 4194303 4194304 129050277 13107200000000 (Ns408p1385 rfl rfl) rfl)) rfl) (Ns408p1386 rfl) RS409to420.d7 

noncomputable def Ns408p1388 := nat_lit 8521130559241091628849350138972368736224461952004899401047262255196712122425612737761129000463083147943612416 

noncomputable def Ns408p1389 := nat_lit 3950007328393864294507890572663162508530119319703758609476275738858994063034392377776341957254813454336 

noncomputable def Ns408p1390 := nat_lit 51632498717640788623525867163936973873307355435986990910743050619895233594763046057349735393919904648001884160 

noncomputable def Ns408p1391 := BSN.cos_dyadic_bound_f 354581842 268435456 4 3 268435456 134217728 Ns408p1388 Ns408p252 Ns408p1389 Ns408p1390 Ns408p255 Ns408p1389 66379750 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 354581842) qz370 0 3 Ns408p1388 Ns408p252 Ns408p1389 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 354581842) qz371 0 3 Ns408p1390 Ns408p255 Ns408p1389 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1392 := nat_lit 183115905810600020901126471050625 

noncomputable def Ns408p1393 := BSN.sin_dyadic_bound_f 116327265 268435456 2 1 268435456 134217728 Ns408p1392 Ns408p133 Ns408p1392 Ns408p1392 Ns408p134 Ns408p1392 112720359 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 116327265) qz372 0 1 Ns408p1392 Ns408p133 Ns408p1392 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 116327265) qz373 0 1 Ns408p1392 Ns408p134 Ns408p1392 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1394 := nat_lit 107579125029487952762194827485992511235323426135959263648469072684475905 

noncomputable def Ns408p1395 := nat_lit 46902354299781772369552296509032006316621625488438285327646633715201 

noncomputable def Ns408p1396 := nat_lit 281678914122649753412388130173727668082286823914816790426888524385707521 

noncomputable def Ns408p1397 := BSN.sin_dyadic_bound_f 287673151 268435456 3 2 268435456 134217728 Ns408p1394 Ns408p142 Ns408p1395 Ns408p1396 Ns408p145 Ns408p1395 235686108 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 287673151) qz372 0 2 Ns408p1394 Ns408p142 Ns408p1395 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 287673151) qz373 0 2 Ns408p1396 Ns408p145 Ns408p1395 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1398 := nat_lit 23511243985891366811290777281371120293362777684976150347418460712261932969586235054675212952922903312745030001 

noncomputable def Ns408p1399 := nat_lit 4731294581388476663807733114173927163169035240631751543756284672630515918291172381914480518712096121201 

noncomputable def Ns408p1400 := nat_lit 117478585284531456159354207003241866455403860288425671929970319647785042417151895700115010412107792215180501361 

noncomputable def Ns408p1401 := BSN.sin_dyadic_bound_f 359955101 268435456 4 3 268435456 134217728 Ns408p1398 Ns408p269 Ns408p1399 Ns408p1400 Ns408p272 Ns408p1399 261375203 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 359955101) qz372 0 3 Ns408p1398 Ns408p269 Ns408p1399 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 359955101) qz373 0 3 Ns408p1400 Ns408p272 Ns408p1399 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1402 := Ns408p1355 82685 BSN.abs_quadSignPos (BSN.cos_quad_nat3 255 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 235686108 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 145 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 261375203 268435456) qz210 rfl rfl (Ns408p1387 RS409to420.d9 RS409to420.d11 RS409to420.d13 RS409to420.d17 (Ns408p1391 rfl rfl) (Ns408p1393 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns408p1386 rfl) RS409to420.d19 RS409to420.d21 RS409to420.d23 RS409to420.d25 RS409to420.d17 (Ns408p1397 rfl rfl) (Ns408p1401 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns408p1403 := nat_lit 5965064544298562575684831653921 

noncomputable def Ns408p1404 := BSN.cos_dyadic_bound_f 49420119 268435456 2 1 268435456 134217728 Ns408p1403 Ns408p149 Ns408p1403 Ns408p1403 Ns408p150 Ns408p1403 263899062 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 49420119) qz370 0 1 Ns408p1403 Ns408p149 Ns408p1403 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 49420119) qz371 0 1 Ns408p1403 Ns408p150 Ns408p1403 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1405 := nat_lit 160435814252461477083451237988756116031993451738731927949205940752411105 

noncomputable def Ns408p1406 := nat_lit 104269034935069570720655508135390333595014238812301476963007401093601 

noncomputable def Ns408p1407 := nat_lit 420020220795123279723110276290713481448448064833839894618551642368829921 

noncomputable def Ns408p1408 := BSN.sin_dyadic_bound_f 317884549 268435456 3 2 268435456 134217728 Ns408p1405 Ns408p142 Ns408p1406 Ns408p1407 Ns408p145 Ns408p1406 248625548 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 317884549) qz372 0 2 Ns408p1405 Ns408p142 Ns408p1406 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 317884549) qz373 0 2 Ns408p1407 Ns408p145 Ns408p1406 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1409 := Ns408p1353 111491 BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 263899062 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 19 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 248625548 268435456) qz210 rfl rfl (Ns408p1402 rfl rfl) (Ns408p1386 rfl) RS409to420.d27 RS409to420.d29 RS409to420.d31 RS409to420.d33 RS409to420.d17 (Ns408p1404 rfl rfl) (Ns408p1408 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1410 := nat_lit 25582259225441842649360340428278995473616241344677760398897490952192000 

noncomputable def Ns408p1411 := nat_lit 2654025382544716354005330482928204612511342161217465571731535036416 

noncomputable def Ns408p1412 := nat_lit 66996858120775944064703930586615485337717518491609306100472530008539136 

noncomputable def Ns408p1413 := BSN.sin_dyadic_bound_f 200903792 268435456 3 2 268435456 134217728 Ns408p1410 Ns408p142 Ns408p1411 Ns408p1412 Ns408p145 Ns408p1411 182666426 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 200903792) qz372 0 2 Ns408p1410 Ns408p142 Ns408p1411 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 200903792) qz373 0 2 Ns408p1412 Ns408p145 Ns408p1411 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1414 := nat_lit 19966477105497734560447404289707431798068004624928309607685306082567105 

noncomputable def Ns408p1415 := nat_lit 1616776359076618258995605462200396812408708501645579946833944945601 

noncomputable def Ns408p1416 := nat_lit 52290536686007942657323875492771139781053255156285765652595213353001921 

noncomputable def Ns408p1417 := BSN.sin_dyadic_bound_f 188834457 268435456 3 2 268435456 134217728 Ns408p1414 Ns408p142 Ns408p1415 Ns408p1416 Ns408p145 Ns408p1415 173640856 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 188834457) qz372 0 2 Ns408p1414 Ns408p142 Ns408p1415 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 188834457) qz373 0 2 Ns408p1416 Ns408p145 Ns408p1415 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1418 := Ns408p1351 136660 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 85 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 182666426 268435456) BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 173640856 268435456) qz210 rfl rfl (Ns408p1409 rfl) (Ns408p1386 rfl) RS409to420.d35 RS409to420.d37 RS409to420.d39 RS409to420.d41 RS409to420.d17 (Ns408p1413 rfl rfl) (Ns408p1417 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1419 := nat_lit 4295766722225176078272968671768342126518979446828241219466576013557760 

noncomputable def Ns408p1420 := nat_lit 74848593199980494623339457833710612713391340606497652217097486336 

noncomputable def Ns408p1421 := nat_lit 11250696422391232617533146828842498609414838774760602197642204734816256 

noncomputable def Ns408p1422 := BSN.sin_dyadic_bound_f 128609472 268435456 3 2 268435456 134217728 Ns408p1419 Ns408p142 Ns408p1420 Ns408p1421 Ns408p145 Ns408p1420 123745377 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 128609472) qz372 0 2 Ns408p1419 Ns408p142 Ns408p1420 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 128609472) qz373 0 2 Ns408p1421 Ns408p145 Ns408p1420 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1423 := nat_lit 595204403960830171439326377510889352514115929701282895047423880897601 

noncomputable def Ns408p1424 := nat_lit 4655731063114204533953228835073090538905908101136390903670547521 

noncomputable def Ns408p1425 := nat_lit 1785603900420364285908911226074997911361269977287646412360464301597761 

noncomputable def Ns408p1426 := BSN.cos_dyadic_bound_f 90886313 268435456 3 2 268435456 134217728 Ns408p1423 Ns408p123 Ns408p1424 Ns408p1425 Ns408p126 Ns408p1424 253195828 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 90886313) qz370 0 2 Ns408p1423 Ns408p123 Ns408p1424 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 90886313) qz371 0 2 Ns408p1425 Ns408p126 Ns408p1424 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1427 := Ns408p1349 159297 BSN.abs_quadSignPos qz415 (BSN.sfrac_eq_quadSignPos_mul Bool.false 123745377 268435456) BSN.abs_quadSignNeg qz395 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 253195828 268435456) qz210 rfl rfl (Ns408p1418 rfl) (Ns408p1386 rfl) RS409to420.d43 RS409to420.d45 RS409to420.d52 RS409to420.d54 RS409to420.d17 (Ns408p1422 rfl rfl) (Ns408p1426 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1428 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 11) 127828222 268435456 159297 268435456 127828222 268435456 159297 268435456 68627254124478464 63914111 67108864 159297 134217728 (Ns408p1427 rfl) 

noncomputable def Ns408p1429 := @Enclosure.Real.IsNear.mulLit_tf qz680 (Zeta.RiemannSiegel.correction qz209) 10074701 33554432 1 33554432 50976239498973 70368744177664 1742522653579789 109951162777600000000 513570371056542782073 2361183241434822606848 

noncomputable abbrev qz684 := (@HPow.hPow Real Real Real qz206 qz207 qz208)

noncomputable def Ns408p1430 := @Enclosure.Real.IsNear.mulLit_tf qz33 qz684 1 1 0 1 10074701 33554432 1 33554432 10074701 33554432 1 33554432 

noncomputable def Ns408p1431 := @Enclosure.Real.IsNear.sqrt_image qz207 4128771093831 33554432000 773127 33554432000 186103830 186103866 16777216 (@Enclosure.Real.IsNear.of_eq qz207 (@HMul.hMul Real Real Real qz4 qz205 qz2) Bool.false 4128771093831 33554432000 773127 33554432000 (BSN.t_div_two_pi_mk qz205 773127 1000 qz210) (@Enclosure.Real.IsNear.mulLit_ff qz205 qz2 773127 1000 0 1 5340353 33554432 1 33554432 4128771093831 33554432000 773127 33554432000 (Enclosure.Real.IsNear.const Bool.false 773127 1000) RS409to420.d48 rfl)) 

noncomputable abbrev qz764 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 773127 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz685 := qz764

noncomputable abbrev qz515 := qz685

noncomputable abbrev qz216 := qz515

noncomputable def Ns408p1432 := @Enclosure.Real.IsNear.sqrt_image qz216 23262981 2097152 9 8388608 55877581 55877588 16777216 (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 372207696 33554432 36 33554432 23262981 2097152 9 8388608 (Ns408p1431 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns408p1433 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz216) 111755169 33554432 7 33554432 5037350 5037351 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz216) Bool.false 111755169 33554432 7 33554432 111755169 33554432 7 33554432 (Ns408p1432 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns408p1434 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz216)) Bool.false 10074701 33554432 1 33554432 10074701 33554432 1 33554432 (Ns408p1433 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz509))

noncomputable abbrev qz686 := (@HMul.hMul Real Real Real qz714 qz762 qz762)

noncomputable abbrev qz516 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz686 qz679) qz598)

noncomputable abbrev qz218 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz516))

noncomputable def Ns408p1435 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz209) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv qz217) qz218) Bool.false 50976239498973 

noncomputable def Ns408p1436 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz217) qz218 10042911 8388608 167 

noncomputable def Ns408p1437 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz217) Bool.false 40171644 33554432 334 33554432 10042911 8388608 167 

noncomputable def Ns408p1438 := @Enclosure.Real.IsNear.recentre' qz217 Bool.false 14013615 16777216 1452304432 209715200000000 14013615 16777216 90769027 13107200000000 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz350 qz347 qz509)

noncomputable def Ns408p1439 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19534071) qz418) Bool.false 19534071 33554432 227 33554432 Bool.false 14013615 16777216 1 

noncomputable def Ns408p1440 := nat_lit 48574935737614563099813683 

noncomputable def Ns408p1441 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz209 884279719003555 140737488355328 1 500000000000000 194309 2097152 9 8388608 171823507919861768495 295147905179352825856 Ns408p1440 

noncomputable def Ns408p1442 := @Enclosure.Real.IsNear.subLit_ff_p qz216 qz31 23262981 2097152 9 8388608 11 1 0 1 194309 194309 2097152 9 

noncomputable def Ns408p1443 := @Ns408p1442 8388608 (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 372207696 33554432 36 33554432 23262981 2097152 9 8388608 (Ns408p1431 rfl rfl rfl rfl rfl rfl) rfl) qz398 

noncomputable def Ns408p1444 := @Enclosure.Real.IsNear.recentre' qz219 Bool.false 171823507919861768495 295147905179352825856 Ns408p1440 Ns408p598 19534071 33554432 227 33554432 (@Ns408p1441 Ns408p598 RS409to420.d47 (Ns408p1443 rfl rfl) rfl) 

noncomputable def Ns408p1445 := nat_lit 310105584473170822260555274983379873998736191282399257269931841 

noncomputable def Ns408p1446 := nat_lit 21200304328840414278424534030378125942669564390412537597761 

noncomputable def Ns408p1447 := nat_lit 930274352810854785953108975882078865744323234718416946734600001 

noncomputable def Ns408p1448 := BSN.cos_dyadic_bound_f 19534071 33554432 3 2 16777216 6250000 Ns408p1445 Ns408p489 Ns408p1446 Ns408p1447 Ns408p492 Ns408p1446 14013615 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 19534071) qz619 0 2 Ns408p1445 Ns408p489 Ns408p1446 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 19534071) (BSN.cosOddQ 33554432) 0 2 Ns408p1447 Ns408p492 Ns408p1446 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1449 := @Enclosure.Real.IsNear.inv_image qz217 14013615 16777216 90769027 13107200000000 20085655 20085989 16777216 (Ns408p1438 (@Ns408p1439 6250000 (Ns408p1444 rfl) (Enclosure.sfrac_false_div 19534071 33554432) (Ns408p1448 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns408p1450 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 10151686 16777216 

noncomputable abbrev qz220 := (@HMul.hMul Real Real Real qz350 qz347 qz516)

noncomputable def Ns408p1451 := @Enclosure.Real.IsNear.cos_image qz220 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 965655)) (@Nat.cast Real Real.instNatCast 1048576)) Bool.true 965655 1048576 

noncomputable def Ns408p1452 := nat_lit 570022117593479186843517205 

noncomputable def Ns408p1453 := nat_lit 618970019642690137449562112 

noncomputable def Ns408p1454 := nat_lit 2414924546064122684543044485761999 

noncomputable def Ns408p1455 := @Enclosure.Real.IsNear.recentre' qz220 Bool.true Ns408p1452 Ns408p1453 Ns408p1454 

noncomputable abbrev qz221 := qz516

noncomputable def Ns408p1456 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz221 884279719003555 140737488355328 1 500000000000000 644617427431 

noncomputable abbrev qz517 := (@HSub.hSub Real Real Real qz584 qz686 qz679)

noncomputable abbrev qz222 := qz517

noncomputable def Ns408p1457 := @Enclosure.Real.IsNear.subLit_tf qz222 qz28 369739520487 4398046511104 89487801 70368744177664 1 16 

noncomputable abbrev qz518 := qz686

noncomputable abbrev qz223 := qz518

noncomputable def Ns408p1458 := @Enclosure.Real.IsNear.subLit_ff_n qz223 qz209 37755987481 4398046511104 13990329 70368744177664 194309 2097152 9 8388608 

noncomputable def Ns408p1459 := @Enclosure.Real.IsNear.mulLit_ff qz209 qz209 194309 2097152 9 8388608 194309 2097152 9 8388608 37755987481 4398046511104 

noncomputable def Ns408p1460 := nat_lit 1766781345607831919867737121938276060779044738690625 

noncomputable def Ns408p1461 := nat_lit 756094272623339076019472454279474005152437890625 

noncomputable def Ns408p1462 := nat_lit 5298831848278249081451172420906269234326829340290625 

noncomputable def Ns408p1463 := BSN.cos_dyadic_bound_f 965655 1048576 3 2 16777216 6250000 Ns408p1460 Ns408p1216 Ns408p1461 Ns408p1462 Ns408p1219 Ns408p1461 10151686 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 965655) (BSN.cosEvenQ 1048576) 0 2 Ns408p1460 Ns408p1216 Ns408p1461 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 965655) (BSN.cosOddQ 1048576) 0 2 Ns408p1462 Ns408p1219 Ns408p1461 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1464 := @Ns408p1450 860527216 104857600000000 5075843 8388608 53782951 6553600000000 (@Ns408p1451 135 16777216 Bool.false 10151686 16777216 1 6250000 (@Ns408p1455 Ns408p612 965655 1048576 135 16777216 (@Ns408p1456 4398046511104 89487801 70368744177664 Ns408p1452 Ns408p1453 Ns408p1454 Ns408p612 RS409to420.d47 (@Ns408p1457 0 1 10313878838896 644617427431 4398046511104 89487801 70368744177664 (@Ns408p1458 775399974868353024 369739520487 4398046511104 89487801 70368744177664 (@Ns408p1459 13990329 70368744177664 (Ns408p1443 rfl rfl) (Ns408p1443 rfl rfl) rfl) (Ns408p1443 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 965655 1048576) (BSN.cos_neg_of_bound 965655 1048576 Bool.false 10151686 16777216 1 6250000 (Ns408p1463 rfl rfl)) rfl rfl) 

noncomputable def Ns408p1465 := @Ns408p1429 8817523418641376355189 Ns408p75 (Ns408p1430 qz51 (@Enclosure.Real.IsNear.of_eq qz684 (@Inv.inv Real Real.instInv (Real.sqrt qz216)) Bool.false 10074701 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz207 (BSN.t_div_two_pi_nonneg qz205 773127 1000 qz210)) Ns408p1434) rfl) (@Ns408p1435 70368744177664 1742522653579789 109951162777600000000 (BSN.correction_mk qz209 (BSN.cos_two_pi_p_ne_zero_mk qz205 773127 1000 11 qz210 rfl rfl (@BSN.floor_sqrt_eq_dec qz205 773127 1000 11 qz210 rfl rfl rfl))) (@Ns408p1436 16777216 5075843 8388608 53782951 6553600000000 50976239498973 70368744177664 1742522653579789 109951162777600000000 (@Ns408p1437 16777216 (Ns408p1449 rfl rfl rfl rfl rfl) rfl) (Ns408p1464 rfl) rfl)) 

noncomputable def Ns408p1466 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz205) (hardyZApproximantRS₀ qz205) Bool.true 1735207492094367526279 2361183241434822606848 Ns408p1345 Ns408p75 (@Eq.refl Real (hardyZApproximantRS₀ qz205)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz205) (@HSub.hSub Real Real Real qz30 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz205) qz205 11) (@HMul.hMul Real Real Real qz4 qz680 (Zeta.RiemannSiegel.correction qz209))) Bool.true 1735207492094367526279 2361183241434822606848 Ns408p1345 Ns408p75 (BSN.hardyZApproximantRS₀_eq qz205 11 (@BSN.floor_sqrt_eq_dec qz205 773127 1000 11 qz210 rfl rfl rfl)) (@Ns408p1347 1735207492094367526279 2361183241434822606848 Ns408p1345 Ns408p75 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz205) qz205 11) (@HAdd.hAdd Real Real Real qz368 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 11)) Bool.true 63914111 67108864 159297 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz205) qz205 11) (Ns408p1428 (Ns408p1427 rfl) rfl rfl)) (Ns408p1465 rfl) rfl rfl)) 

theorem RS409to420.d65 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz205) Bool.true 1735207492094367526279 2361183241434822606848 Ns408p1345 Ns408p75 := Ns408p1466 

noncomputable def Ns408p1467 := nat_lit 4404489912871170606247893 

noncomputable def Ns408p1468 := nat_lit 3689348814741910323200000000 

noncomputable def Ns408p1469 := nat_lit 358955774982091612826420379648 

noncomputable abbrev qz765 := (Enclosure.sfrac Bool.false 774433 1000)

noncomputable abbrev qz687 := qz765

noncomputable abbrev qz519 := qz687

noncomputable abbrev qz224 := qz519

noncomputable abbrev qz766 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 774433 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz688 := qz766

noncomputable abbrev qz520 := qz688

noncomputable abbrev qz225 := qz520

noncomputable abbrev qz767 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 774433 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz689 := qz767

noncomputable abbrev qz521 := qz689

noncomputable abbrev qz226 := qz521

noncomputable abbrev qz690 := (@HMul.hMul Real Real Real qz4 qz33 (@HPow.hPow Real Real Real qz206 qz225 qz208))

noncomputable def Ns408p1470 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz224) qz224 11) (@HMul.hMul Real Real Real qz4 qz690 (Zeta.RiemannSiegel.correction qz226)) 23765385 67108864 159567 134217728 2004177269773268195877 9444732965739290427392 18345615137845806247893 Ns408p1468 Ns408p1469 

noncomputable def Ns408p1471 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz224) qz224 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 774433 1000 195 242 268435456 134217728 4503599627370496 Bool.false 396358223535 2600 

noncomputable def Ns408p1472 := Ns408p1471 618095470 44 84886744 8 643680110 44 80936328 8 Bool.false 95617827 136892 Bool.true 92107071 Bool.true 87797452 14148475504056880 1 Bool.false 90310307 Bool.false Bool.false 254204996 Bool.true Bool.false 47530770 

noncomputable def Ns408p1473 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz224) qz224 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 774433 1000 85 143 268435456 134217728 4503599627370496 Bool.false 396358223535 2600 

noncomputable def Ns408p1474 := Ns408p1473 558195838 44 94906264 8 589812974 44 89478488 8 Bool.false 88272578 111681 Bool.true 86172472 Bool.true 115395116 14148475504056880 1 Bool.false 84700035 Bool.true Bool.false 111873697 Bool.false Bool.false 95617827 

noncomputable def Ns408p1475 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz224) qz224 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 774433 1000 56 19 268435456 134217728 4503599627370496 Bool.false 396358223535 2600 

noncomputable def Ns408p1476 := Ns408p1475 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 27918052 82827 Bool.false 265006088 Bool.true 156340212 14148475504056880 1 Bool.false 147910094 Bool.false Bool.false 147650359 Bool.false Bool.false 88272578 

noncomputable def Ns408p1477 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz224) qz224 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 774433 1000 256 146 268435456 134217728 4503599627370496 Bool.false 396358223535 2600 

noncomputable def Ns408p1478 := Ns408p1477 372130544 43 134217720 8 432030192 43 120047984 16 Bool.true 35494982 48793 Bool.false 223748317 Bool.false 217801326 14148475504056880 1 Bool.false 180460717 Bool.false Bool.false 184818674 Bool.true Bool.true 27918052 

noncomputable def Ns408p1479 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz224) qz224 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 774433 1000 598 398 268435456 134217728 4503599627370496 Bool.false 396358223535 2600 

noncomputable def Ns408p1480 := Ns408p1479 186065264 43 189812528 16 294906480 43 154981288 8 Bool.false 268435344 2651 Bool.false 112000836 Bool.false 153257059 14148475504056880 1 Bool.false 245407090 Bool.true Bool.false 225861688 Bool.true Bool.true 35494982 

noncomputable def Ns408p1481 := nat_lit 51643291895932525181793820088025889632953938459099246805839 

noncomputable def Ns408p1482 := nat_lit 34975660365401564172674760243998687092597479822065664000 

noncomputable def Ns408p1483 := nat_lit 133709095163391750488084102748640000 

noncomputable def Ns408p1484 := nat_lit 621292535026213318130934486376281126720 

noncomputable abbrev qz768 := (@Eq.refl Real (Enclosure.sfrac Bool.false 774433 1000))

noncomputable abbrev qz691 := qz768

noncomputable abbrev qz522 := qz691

noncomputable abbrev qz227 := qz522

noncomputable def Ns408p1485 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz224 774433 1000 2398986885956 16000000 1548866 4000 2000 Ns408p1483 Ns408p1484 qz227 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns408p1486 := nat_lit 16525853406698408058174022428168284682545260306911758977868480 

noncomputable abbrev qz692 := (@HSub.hSub Real Real Real qz718 qz719 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz720 (@Nat.cast Real Real.instNatCast 1548866))))

noncomputable abbrev qz523 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 774433 4000) (Real.log (Enclosure.sfrac Bool.false 2398986885956 16000000))) (@HMul.hMul Real Real Real qz579 qz585 qz692))

noncomputable abbrev qz693 := (Enclosure.sfrac Bool.false 774433 2000)

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz356 (@HSub.hSub Real Real Real qz356 qz523 qz693) (@HMul.hMul Real Real Real qz350 qz693 (Real.log Real.pi)))

noncomputable def Ns408p1487 := @Enclosure.Real.IsNear.addLit_ft_p qz228 (Enclosure.sfrac Bool.true Ns408p1483 Ns408p1484) 26599153995452529601159 18014398509481984000 39658060901919789 4096000000000000000000 Ns408p1483 Ns408p1484 0 1 Ns408p1486 

noncomputable def Ns408p1488 := nat_lit 1785039007995880427460153573376000 

noncomputable abbrev qz229 := (@HSub.hSub Real Real Real qz356 qz523 qz693)

noncomputable def Ns408p1489 := @Enclosure.Real.IsNear.subLit_ff_p qz229 (@HMul.hMul Real Real Real qz4 qz693 (Real.log Real.pi)) 34584185627965750078087 18014398509481984000 15648673165861 4000000000000000000 29746560873513 67108864000 774433 134217728000 Ns408p1488 26599153995452529601159 18014398509481984000 

noncomputable def Ns408p1490 := nat_lit 69168371255931500156174000 

noncomputable abbrev qz230 := qz523

noncomputable def Ns408p1491 := @Enclosure.Real.IsNear.subLit_ff_p qz230 qz693 41559657968412580735623 18014398509481984000 15648673165861 4000000000000000000 774433 2000 0 1 Ns408p1490 34584185627965750078087 18014398509481984000 15648673165861 4000000000000000000 

noncomputable def Ns408p1492 := nat_lit 93584030070094081710862057962423189504 

noncomputable def Ns408p1493 := nat_lit 57631758634954253500678144 

noncomputable def Ns408p1494 := nat_lit 867416358005387289648842577146909516168880508003682807652548730199584640634880 

noncomputable def Ns408p1495 := nat_lit 1306598974778921933768881360039943889733820533939999499312253942201228619776 

noncomputable def Ns408p1496 := nat_lit 11342475832893148734048995253459223520496062341983769483358069302947840 

noncomputable def Ns408p1497 := BSN.log_dyadic_bound 301834885956 4496138885956 4 3 Ns408p1494 134217728 50000000 Ns408p1495 Ns408p1496 18047759 4797973771912 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 301834885956) (BSN.artanhQ 4496138885956) 0 3 Ns408p1495 Ns408p1494 Ns408p1496 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz524 := (Real.log (Enclosure.sfrac Bool.false 2398986885956 16000000))

noncomputable def Ns408p1498 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 774433 4000) qz524 774433 4000 0 1 53673757831523431 4503599627370496 20000017 1000000000000000 41566729298740185239623 18014398509481984000 15488673165361 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 774433 4000) (BSN.isNear_log_sfrac 2398986885956 16000000 53673757831523431 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2398986885956) qz359)) Bool.false Ns408p1493 Ns408p100 1000000850000000 50000000000000000000000 53673757831523431 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2398986885956 16000000 17 4797973771912 4194304000000 18047759 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns408p1497 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns408p1499 := BSN.arctan_dyadic_bound_f 1000 1548866 1 0 16777216 6250000 0 1 1 0 1 1 10831 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1548866) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1548866) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns408p1500 := @Enclosure.Real.IsNear.subLit_ff_p qz12 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz13 (@Nat.cast Real Real.instNatCast 1548866))) 884279719003555 562949953421312 1 2000000000000000 10831 16777216 1 6250000 14829654539196440772608 883916290950563 562949953421312 320000001 2000000000000000 qz14 (Ns408p1499 rfl) rfl rfl 

noncomputable abbrev qz525 := (@HMul.hMul Real Real Real qz579 qz585 qz692)

noncomputable abbrev qz231 := qz525

noncomputable abbrev qz526 := qz692

noncomputable abbrev qz232 := qz526

noncomputable def Ns408p1501 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 774433 4000) qz524) qz231 41566729298740185239623 18014398509481984000 15488673165361 4000000000000000000 883916290950563 2251799813685248 320000001 8000000000000000 Ns408p1492 41559657968412580735623 18014398509481984000 15648673165861 4000000000000000000 (Ns408p1498 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz16 qz232 1 4 0 1 883916290950563 562949953421312 320000001 2000000000000000 883916290950563 2251799813685248 320000001 8000000000000000 qz367 Ns408p1500 rfl) 

noncomputable def Ns408p1502 := @Ns408p1487 Ns408p1481 Ns408p1482 39658060901919789 4096000000000000000000 (@Ns408p1489 39658060901919789 4096000000000000000000 (Ns408p1491 (Ns408p1501 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 774433 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz693 (Real.log Real.pi) 774433 2000 0 1 38410761 33554432 1 67108864 29746560873513 67108864000 774433 134217728000 (Enclosure.Real.IsNear.const Bool.false 774433 2000) RS409to420.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns408p1483 Ns408p1484) 

noncomputable def Ns408p1503 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz224) Bool.false Ns408p1481 Ns408p1482 39658060901919789 4096000000000000000000 49544777941 33554432 163 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz224) (@HAdd.hAdd Real Real Real qz368 qz228 (Enclosure.sfrac Bool.true Ns408p1483 Ns408p1484)) Bool.false Ns408p1481 Ns408p1482 39658060901919789 4096000000000000000000 Ns408p1485 (Ns408p1502 rfl rfl)) 

noncomputable def Ns408p1504 := BSN.cos_dyadic_bound_f 61685162 68719476736 1 0 33554432 12512208 0 1 1 0 1 1 33554418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 61685162) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 61685162) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns408p1505 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz224) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49544777941) qz418) Bool.false 49544777941 33554432 163 16777216 Bool.false 33554418 33554432 1 6250000 (Ns408p1503 rfl) (Enclosure.sfrac_false_div 49544777941 33554432) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49544777941) qz418) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4340707413988214833152) qz430) 226375608064910080 72057594037927936 Bool.false 33554418 33554432 235 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q0 49544777941 33554432 226375608064910080 72057594037927936 235 4340707413988214833152 Ns408p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554418 33554432 4340707413988214833152 Ns408p100 61685162 68719476736 12512208 12500000 (Ns408p1504 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns408p1506 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz224) Bool.false Ns408p1481 Ns408p1482 39658060901919789 4096000000000000000000 396358223535 268435456 2600 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz224) (@HAdd.hAdd Real Real Real qz368 qz228 (Enclosure.sfrac Bool.true Ns408p1483 Ns408p1484)) Bool.false Ns408p1481 Ns408p1482 39658060901919789 4096000000000000000000 Ns408p1485 (Ns408p1502 rfl rfl)) 

noncomputable def Ns408p1507 := Ns408p1480 48793 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 598 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 245407090 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 398 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 225861688 268435456) qz227 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz224) qz224 1) Bool.false 16777209 16777216 64720451 6553600000000 268435344 268435456 2651 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz224) qz224 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz224)) Bool.false 16777209 16777216 64720451 6553600000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz224) qz224) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz224)) Bool.false 33554418 33554432 1035527216 104857600000000 16777209 16777216 64720451 6553600000000 (Ns408p1505 rfl rfl) rfl)) rfl) (Ns408p1506 rfl) RS409to420.d7 

noncomputable def Ns408p1508 := nat_lit 1372655920991829372011771244910389759984179266888509164856473865486336 

noncomputable def Ns408p1509 := nat_lit 24761110305299855644099967589488128851367457673752839305109241856 

noncomputable def Ns408p1510 := nat_lit 4117918240754877516324025534795990303694835065750179988890811377975296 

noncomputable def Ns408p1511 := BSN.cos_dyadic_bound_f 112000836 268435456 3 2 268435456 134217728 Ns408p1508 Ns408p123 Ns408p1509 Ns408p1510 Ns408p126 Ns408p1509 245407090 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 112000836) qz370 0 2 Ns408p1508 Ns408p123 Ns408p1509 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 112000836) qz371 0 2 Ns408p1510 Ns408p126 Ns408p1509 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1512 := nat_lit 4812582750921039515785531602920603487559938939399841932623698350410401 

noncomputable def Ns408p1513 := nat_lit 304343406668042520957151168756348705328589939479760850233133468321 

noncomputable def Ns408p1514 := nat_lit 14437139565949782462314680506424297765269159638320566276170628784294561 

noncomputable def Ns408p1515 := BSN.cos_dyadic_bound_f 153257059 268435456 3 2 268435456 134217728 Ns408p1512 Ns408p123 Ns408p1513 Ns408p1514 Ns408p126 Ns408p1513 225861688 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 153257059) qz370 0 2 Ns408p1512 Ns408p123 Ns408p1513 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 153257059) qz371 0 2 Ns408p1514 Ns408p126 Ns408p1513 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1516 := nat_lit 21869188610158244297925139698769000551451077145506273944735688925199521 

noncomputable def Ns408p1517 := nat_lit 6281714852058629021429712363250037186884622502354267511754427284641 

noncomputable def Ns408p1518 := nat_lit 65595002400770615635732559671580501579979462191514113299183557921029281 

noncomputable def Ns408p1519 := BSN.cos_dyadic_bound_f 223748317 268435456 3 2 268435456 134217728 Ns408p1516 Ns408p123 Ns408p1517 Ns408p1518 Ns408p126 Ns408p1517 180460717 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 223748317) qz370 0 2 Ns408p1516 Ns408p123 Ns408p1517 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 223748317) qz371 0 2 Ns408p1518 Ns408p126 Ns408p1517 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1520 := nat_lit 19634637856200141689644814032878044032056297746712849859853799311360256 

noncomputable def Ns408p1521 := nat_lit 5063888746874400665908686554019101495670689143703114080996707614976 

noncomputable def Ns408p1522 := nat_lit 58893785791106676267602624725526093893177551861851143351399404518850816 

noncomputable def Ns408p1523 := BSN.cos_dyadic_bound_f 217801326 268435456 3 2 268435456 134217728 Ns408p1520 Ns408p123 Ns408p1521 Ns408p1522 Ns408p126 Ns408p1521 184818674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 217801326) qz370 0 2 Ns408p1520 Ns408p123 Ns408p1521 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 217801326) qz371 0 2 Ns408p1522 Ns408p126 Ns408p1521 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1524 := Ns408p1478 82827 BSN.abs_quadSignPos (BSN.cos_quad_nat0 256 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 180460717 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 146 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 184818674 268435456) qz227 rfl rfl (Ns408p1507 RS409to420.d9 RS409to420.d11 RS409to420.d13 RS409to420.d17 (Ns408p1511 rfl rfl) (Ns408p1515 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns408p1506 rfl) RS409to420.d19 RS409to420.d21 RS409to420.d23 RS409to420.d25 RS409to420.d17 (Ns408p1519 rfl rfl) (Ns408p1523 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns408p1525 := nat_lit 43046483621594858638390058322572771118150248518670452196149274267877376 

noncomputable def Ns408p1526 := nat_lit 24324661702245199946627961313890908125193806534765104972597135671296 

noncomputable def Ns408p1527 := nat_lit 129090801541380085515276919045090531538200357942941826378502628532289536 

noncomputable def Ns408p1528 := BSN.cos_dyadic_bound_f 265006088 268435456 3 2 268435456 134217728 Ns408p1525 Ns408p123 Ns408p1526 Ns408p1527 Ns408p126 Ns408p1526 147910094 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 265006088) qz370 0 2 Ns408p1525 Ns408p123 Ns408p1526 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 265006088) qz371 0 2 Ns408p1527 Ns408p126 Ns408p1526 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1529 := nat_lit 9380815866848546355291252073599871727161962451106959901383020253347840 

noncomputable def Ns408p1530 := nat_lit 356915634373620581405454621093345860374328655016782765986372714496 

noncomputable def Ns408p1531 := nat_lit 24568225597385778401964337075755989106412152744600582093429646536278016 

noncomputable def Ns408p1532 := BSN.sin_dyadic_bound_f 156340212 268435456 3 2 268435456 134217728 Ns408p1529 Ns408p142 Ns408p1530 Ns408p1531 Ns408p145 Ns408p1530 147650359 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 156340212) qz372 0 2 Ns408p1529 Ns408p142 Ns408p1530 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 156340212) qz373 0 2 Ns408p1531 Ns408p145 Ns408p1530 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1533 := Ns408p1476 111681 BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 147910094 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 19 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 147650359 268435456) qz227 rfl rfl (Ns408p1524 rfl rfl) (Ns408p1506 rfl) RS409to420.d27 RS409to420.d29 RS409to420.d31 RS409to420.d33 RS409to420.d17 (Ns408p1528 rfl rfl) (Ns408p1532 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1534 := nat_lit 55140945202201668407399265734656 

noncomputable def Ns408p1535 := BSN.sin_dyadic_bound_f 86172472 268435456 2 1 268435456 134217728 Ns408p1534 Ns408p133 Ns408p1534 Ns408p1534 Ns408p134 Ns408p1534 84700035 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 86172472) qz372 0 1 Ns408p1534 Ns408p133 Ns408p1534 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 86172472) qz373 0 1 Ns408p1534 Ns408p134 Ns408p1534 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1536 := nat_lit 177316729441550460669912956743936 

noncomputable def Ns408p1537 := BSN.sin_dyadic_bound_f 115395116 268435456 2 1 268435456 134217728 Ns408p1536 Ns408p133 Ns408p1536 Ns408p1536 Ns408p134 Ns408p1536 111873697 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 115395116) qz372 0 1 Ns408p1536 Ns408p133 Ns408p1536 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 115395116) qz373 0 1 Ns408p1536 Ns408p134 Ns408p1536 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1538 := Ns408p1474 136892 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 85 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 84700035 268435456) BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 111873697 268435456) qz227 rfl rfl (Ns408p1533 rfl) (Ns408p1506 rfl) RS409to420.d35 RS409to420.d37 RS409to420.d39 RS409to420.d41 RS409to420.d17 (Ns408p1535 rfl rfl) (Ns408p1537 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1539 := nat_lit 71973378261121364034610913319681 

noncomputable def Ns408p1540 := BSN.sin_dyadic_bound_f 92107071 268435456 2 1 268435456 134217728 Ns408p1539 Ns408p133 Ns408p1539 Ns408p1539 Ns408p134 Ns408p1539 90310307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 92107071) qz372 0 1 Ns408p1539 Ns408p133 Ns408p1539 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 92107071) qz373 0 1 Ns408p1539 Ns408p134 Ns408p1539 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1541 := nat_lit 518321714514207110845832141557489117648086801316320602405593153601536 

noncomputable def Ns408p1542 := nat_lit 3530655129573378748766500729490342706186055942535337057473069056 

noncomputable def Ns408p1543 := nat_lit 1554958082232362185779998891671008372258848031837076736542664514666496 

noncomputable def Ns408p1544 := BSN.cos_dyadic_bound_f 87797452 268435456 3 2 268435456 134217728 Ns408p1541 Ns408p123 Ns408p1542 Ns408p1543 Ns408p126 Ns408p1542 254204996 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 87797452) qz370 0 2 Ns408p1541 Ns408p123 Ns408p1542 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 87797452) qz371 0 2 Ns408p1543 Ns408p126 Ns408p1542 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1545 := Ns408p1472 159567 BSN.abs_quadSignPos qz415 (BSN.sfrac_eq_quadSignPos_mul Bool.false 90310307 268435456) BSN.abs_quadSignNeg qz395 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 254204996 268435456) qz227 rfl rfl (Ns408p1538 rfl) (Ns408p1506 rfl) RS409to420.d43 RS409to420.d45 RS409to420.d52 RS409to420.d54 RS409to420.d17 (Ns408p1540 rfl rfl) (Ns408p1544 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1546 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz224) qz224 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz224) qz224 11) 47530770 268435456 159567 268435456 47530770 268435456 159567 268435456 25517887837962240 23765385 67108864 159567 134217728 (Ns408p1545 rfl) 

noncomputable def Ns408p1547 := @Enclosure.Real.IsNear.mulLit_tf qz690 (Zeta.RiemannSiegel.correction qz226) 10070451 33554432 1 33554432 199015641878727 281474976710656 3628014840393843 219902325555200000000 2004177269773268195877 9444732965739290427392 

noncomputable abbrev qz694 := (@HPow.hPow Real Real Real qz206 qz225 qz208)

noncomputable def Ns408p1548 := @Enclosure.Real.IsNear.mulLit_tf qz33 qz694 1 1 0 1 10070451 33554432 1 33554432 10070451 33554432 1 33554432 

noncomputable def Ns408p1549 := @Enclosure.Real.IsNear.sqrt_image qz225 4135745594849 33554432000 774433 33554432000 186260951 186260987 16777216 (@Enclosure.Real.IsNear.of_eq qz225 (@HMul.hMul Real Real Real qz4 qz224 qz2) Bool.false 4135745594849 33554432000 774433 33554432000 (BSN.t_div_two_pi_mk qz224 774433 1000 qz227) (@Enclosure.Real.IsNear.mulLit_ff qz224 qz2 774433 1000 0 1 5340353 33554432 1 33554432 4135745594849 33554432000 774433 33554432000 (Enclosure.Real.IsNear.const Bool.false 774433 1000) RS409to420.d48 rfl)) 

noncomputable abbrev qz769 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 774433 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz695 := qz769

noncomputable abbrev qz527 := qz695

noncomputable abbrev qz233 := qz527

noncomputable def Ns408p1550 := @Enclosure.Real.IsNear.sqrt_image qz233 186260969 16777216 9 8388608 55901164 55901171 16777216 (@Enclosure.Real.IsNear.recentre' qz233 Bool.false 372521938 33554432 36 33554432 186260969 16777216 9 8388608 (Ns408p1549 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns408p1551 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz233) 111802335 33554432 7 33554432 5035225 5035226 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz233) Bool.false 111802335 33554432 7 33554432 111802335 33554432 7 33554432 (Ns408p1550 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns408p1552 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz233)) Bool.false 10070451 33554432 1 33554432 10070451 33554432 1 33554432 (Ns408p1551 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz521))

noncomputable abbrev qz696 := (@HMul.hMul Real Real Real qz714 qz767 qz767)

noncomputable abbrev qz528 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz696 qz689) qz598)

noncomputable abbrev qz235 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz528))

noncomputable def Ns408p1553 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz226) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv qz234) qz235) Bool.false 199015641878727 

noncomputable def Ns408p1554 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz234) qz235 20932377 16777216 91 

noncomputable def Ns408p1555 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz234) Bool.false 41864754 33554432 364 33554432 20932377 16777216 91 

noncomputable def Ns408p1556 := @Enclosure.Real.IsNear.recentre' qz234 Bool.false 13446871 16777216 364638608 52428800000000 13446871 16777216 22789913 3276800000000 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz350 qz347 qz521)

noncomputable def Ns408p1557 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21508511) qz418) Bool.false 21508511 33554432 57 8388608 Bool.false 13446871 16777216 1 

noncomputable def Ns408p1558 := nat_lit 242874678688747645055583231 

noncomputable def Ns408p1559 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz226 884279719003555 140737488355328 1 500000000000000 1711593 16777216 9 8388608 1513526977088451713115 2361183241434822606848 Ns408p1558 

noncomputable def Ns408p1560 := @Enclosure.Real.IsNear.subLit_ff_p qz233 qz31 186260969 16777216 9 8388608 11 1 0 1 1711593 1711593 16777216 9 

noncomputable def Ns408p1561 := @Ns408p1560 8388608 (@Enclosure.Real.IsNear.recentre' qz233 Bool.false 372521938 33554432 36 33554432 186260969 16777216 9 8388608 (Ns408p1549 rfl rfl rfl rfl rfl rfl) rfl) qz398 

noncomputable def Ns408p1562 := @Enclosure.Real.IsNear.recentre' qz236 Bool.false 1513526977088451713115 2361183241434822606848 Ns408p1558 Ns408p171 21508511 33554432 57 8388608 (@Ns408p1559 Ns408p171 RS409to420.d47 (Ns408p1561 rfl rfl) rfl) 

noncomputable def Ns408p1563 := nat_lit 455820520602622626332889960460796951838237613094908608312533761 

noncomputable def Ns408p1564 := nat_lit 45801823337346330038121937554612106301916051841576656986881 

noncomputable def Ns408p1565 := nat_lit 1367369958161193186338593637507281631302109007181042671623627521 

noncomputable def Ns408p1566 := BSN.cos_dyadic_bound_f 21508511 33554432 3 2 16777216 6250000 Ns408p1563 Ns408p489 Ns408p1564 Ns408p1565 Ns408p492 Ns408p1564 13446871 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 21508511) qz619 0 2 Ns408p1563 Ns408p489 Ns408p1564 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 21508511) (BSN.cosOddQ 33554432) 0 2 Ns408p1565 Ns408p492 Ns408p1564 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1567 := @Enclosure.Real.IsNear.inv_image qz234 13446871 16777216 22789913 3276800000000 20932195 20932559 16777216 (Ns408p1556 (@Ns408p1557 6250000 (Ns408p1562 rfl) (Enclosure.sfrac_false_div 21508511 33554432) (Ns408p1566 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns408p1568 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 9507551 16777216 

noncomputable abbrev qz237 := (@HMul.hMul Real Real Real qz350 qz347 qz528)

noncomputable def Ns408p1569 := @Enclosure.Real.IsNear.cos_image qz237 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4061379)) (@Nat.cast Real Real.instNatCast 4194304)) Bool.true 4061379 4194304 

noncomputable def Ns408p1570 := nat_lit 38358640169158693383986644525 

noncomputable def Ns408p1571 := nat_lit 245308525845778123175536627149467 

noncomputable def Ns408p1572 := @Enclosure.Real.IsNear.recentre' qz237 Bool.true Ns408p1570 Ns408p187 Ns408p1571 

noncomputable abbrev qz238 := qz528

noncomputable def Ns408p1573 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz238 884279719003555 140737488355328 1 500000000000000 43378400911855 

noncomputable abbrev qz529 := (@HSub.hSub Real Real Real qz584 qz696 qz689)

noncomputable abbrev qz239 := qz529

noncomputable def Ns408p1574 := @Enclosure.Real.IsNear.subLit_tf qz239 qz28 25786214867439 281474976710656 45450945 35184372088832 1 16 

noncomputable abbrev qz530 := qz696

noncomputable abbrev qz240 := qz530

noncomputable def Ns408p1575 := @Enclosure.Real.IsNear.subLit_ff_n qz240 qz226 2929550597649 281474976710656 7702209 35184372088832 1711593 16777216 9 8388608 

noncomputable def Ns408p1576 := @Enclosure.Real.IsNear.mulLit_ff qz226 qz226 1711593 16777216 9 8388608 1711593 16777216 9 8388608 2929550597649 281474976710656 

noncomputable def Ns408p1577 := nat_lit 141537063089606498536364481746192673284036150550881524641 

noncomputable def Ns408p1578 := nat_lit 3861888762982039923063034508418779142719222587902677483520 

noncomputable def Ns408p1579 := nat_lit 74026659360079155604615784073977347529062229260000161 

noncomputable def Ns408p1580 := nat_lit 424463135950099337297884213670430065157050327194124573601 

noncomputable def Ns408p1581 := nat_lit 173784994334191796537836552878845061422365016455620486758400 

noncomputable def Ns408p1582 := BSN.cos_dyadic_bound_f 4061379 4194304 3 2 16777216 6250000 Ns408p1577 Ns408p1578 Ns408p1579 Ns408p1580 Ns408p1581 Ns408p1579 9507551 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 4061379) (BSN.cosEvenQ 4194304) 0 2 Ns408p1577 Ns408p1578 Ns408p1579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 4061379) (BSN.cosOddQ 4194304) 0 2 Ns408p1580 Ns408p1581 Ns408p1579 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1583 := @Ns408p1568 1739804432 209715200000000 9507551 16777216 108737777 13107200000000 (@Ns408p1569 273 33554432 Bool.false 9507551 16777216 1 6250000 (@Ns408p1572 Ns408p190 4061379 4194304 273 33554432 (@Ns408p1573 281474976710656 45450945 35184372088832 Ns408p1570 Ns408p187 Ns408p1571 Ns408p190 RS409to420.d47 (@Ns408p1574 0 1 694054414589680 43378400911855 281474976710656 45450945 35184372088832 (@Ns408p1575 432620896653435469824 25786214867439 281474976710656 45450945 35184372088832 (@Ns408p1576 7702209 35184372088832 (Ns408p1561 rfl rfl) (Ns408p1561 rfl rfl) rfl) (Ns408p1561 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4061379 4194304) (BSN.cos_neg_of_bound 4061379 4194304 Bool.false 9507551 16777216 1 6250000 (Ns408p1582 rfl rfl)) rfl rfl) 

noncomputable def Ns408p1584 := @Ns408p1547 18345615137845806247893 Ns408p1468 (Ns408p1548 qz51 (@Enclosure.Real.IsNear.of_eq qz694 (@Inv.inv Real Real.instInv (Real.sqrt qz233)) Bool.false 10070451 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz225 (BSN.t_div_two_pi_nonneg qz224 774433 1000 qz227)) Ns408p1552) rfl) (@Ns408p1553 281474976710656 3628014840393843 219902325555200000000 (BSN.correction_mk qz226 (BSN.cos_two_pi_p_ne_zero_mk qz224 774433 1000 11 qz227 rfl rfl (@BSN.floor_sqrt_eq_dec qz224 774433 1000 11 qz227 rfl rfl rfl))) (@Ns408p1554 8388608 9507551 16777216 108737777 13107200000000 199015641878727 281474976710656 3628014840393843 219902325555200000000 (@Ns408p1555 8388608 (Ns408p1567 rfl rfl rfl rfl rfl) rfl) (Ns408p1583 rfl) rfl)) 

noncomputable def Ns408p1585 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz224) (hardyZApproximantRS₀ qz224) Bool.false 5348857864470654917157 9444732965739290427392 Ns408p1467 Ns408p1468 (@Eq.refl Real (hardyZApproximantRS₀ qz224)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz224) (@HSub.hSub Real Real Real qz30 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz224) qz224 11) (@HMul.hMul Real Real Real qz4 qz690 (Zeta.RiemannSiegel.correction qz226))) Bool.false 5348857864470654917157 9444732965739290427392 Ns408p1467 Ns408p1468 (BSN.hardyZApproximantRS₀_eq qz224 11 (@BSN.floor_sqrt_eq_dec qz224 774433 1000 11 qz227 rfl rfl rfl)) (@Ns408p1470 5348857864470654917157 9444732965739290427392 Ns408p1467 Ns408p1468 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz224) qz224 11) (@HAdd.hAdd Real Real Real qz368 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz224) qz224 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz224) qz224 11)) Bool.false 23765385 67108864 159567 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz224) qz224 11) (Ns408p1546 (Ns408p1545 rfl) rfl rfl)) (Ns408p1584 rfl) rfl rfl)) 

theorem RS409to420.d66 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz224) Bool.false 5348857864470654917157 9444732965739290427392 Ns408p1467 Ns408p1468 := Ns408p1585 

noncomputable def Ns408p1586 := nat_lit 2206218958183003372802973 

noncomputable def Ns408p1587 := nat_lit 178238017672139000340964966400 

noncomputable abbrev qz770 := (Enclosure.sfrac Bool.false 775738 1000)

noncomputable abbrev qz697 := qz770

noncomputable abbrev qz531 := qz697

noncomputable abbrev qz241 := qz531

noncomputable abbrev qz771 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 775738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz698 := qz771

noncomputable abbrev qz532 := qz698

noncomputable abbrev qz242 := qz532

noncomputable abbrev qz772 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 775738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz699 := qz772

noncomputable abbrev qz533 := qz699

noncomputable abbrev qz243 := qz533

noncomputable abbrev qz700 := (@HMul.hMul Real Real Real qz4 qz33 (@HPow.hPow Real Real Real qz206 qz242 qz208))

noncomputable def Ns408p1588 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz241) qz241 11) (@HMul.hMul Real Real Real qz4 qz700 (Zeta.RiemannSiegel.correction qz243)) 103278745 134217728 159843 134217728 488922180371593518495 2361183241434822606848 9353494200513772802973 Ns408p75 Ns408p1587 

noncomputable def Ns408p1589 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz241) qz241 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 775738 1000 195 242 268435456 134217728 4503599627370496 Bool.false 397201607245 2605 

noncomputable def Ns408p1590 := Ns408p1589 618095470 44 84886744 8 643680110 44 80936328 8 Bool.true 43687339 137129 Bool.true 55337949 Bool.true 84416285 14148475504056880 1 Bool.false 54946824 Bool.false Bool.false 255271072 Bool.true Bool.true 103278745 

noncomputable def Ns408p1591 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz241) qz241 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 775738 1000 84 143 268435456 134217728 4503599627370496 Bool.false 397201607245 2605 

noncomputable def Ns408p1592 := Ns408p1591 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 67687956 111875 Bool.true 392891759 Bool.true 41717337 14148475504056880 1 Bool.false 28710646 Bool.false Bool.false 41549613 Bool.false Bool.true 43687339 

noncomputable def Ns408p1593 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz241) qz241 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 775738 1000 57 18 268435456 134217728 4503599627370496 Bool.false 397201607245 2605 

noncomputable def Ns408p1594 := Ns408p1593 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 41737722 82972 Bool.false 59064226 Bool.true 416282327 14148475504056880 1 Bool.false 58588790 Bool.true Bool.false 5374742 Bool.true Bool.true 67687956 

noncomputable def Ns408p1595 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz241) qz241 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 775738 1000 257 147 268435456 134217728 4503599627370496 Bool.false 397201607245 2605 

noncomputable def Ns408p1596 := Ns408p1595 372130544 43 134217720 8 432030192 43 120047984 16 Bool.false 125046 48880 Bool.false 159844239 Bool.false 75728208 14148475504056880 1 Bool.false 150564043 Bool.true Bool.false 74727715 Bool.false Bool.true 41737722 

noncomputable def Ns408p1597 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz241) qz241 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 775738 1000 599 399 268435456 134217728 4503599627370496 Bool.false 397201607245 2605 

noncomputable def Ns408p1598 := Ns408p1597 186065264 43 189812528 16 294906480 43 154981288 8 Bool.true 268435272 2659 Bool.false 290911948 Bool.false 190130384 14148475504056880 1 Bool.false 237219205 Bool.false Bool.false 174627111 Bool.false Bool.false 125046 

noncomputable def Ns408p1599 := nat_lit 408426922860974156696753275280885714841612954492488823743 

noncomputable def Ns408p1600 := nat_lit 276021711092840180660157146494035567571507523616768000 

noncomputable def Ns408p1601 := nat_lit 134839466387321508525221253360640000 

noncomputable def Ns408p1602 := nat_lit 627600709533090095328946396180152913920 

noncomputable abbrev qz773 := (@Eq.refl Real (Enclosure.sfrac Bool.false 775738 1000))

noncomputable abbrev qz701 := qz773

noncomputable abbrev qz534 := qz701

noncomputable abbrev qz244 := qz534

noncomputable def Ns408p1603 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz241 775738 1000 2407078778576 16000000 1551476 4000 2000 Ns408p1601 Ns408p1602 qz244 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns408p1604 := nat_lit 8364583380192750729149507077752539439956233308006171110256640 

noncomputable abbrev qz702 := (@HSub.hSub Real Real Real qz718 qz719 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz720 (@Nat.cast Real Real.instNatCast 1551476))))

noncomputable abbrev qz535 := (@HSub.hSub Real Real Real qz584 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 775738 4000) (Real.log (Enclosure.sfrac Bool.false 2407078778576 16000000))) (@HMul.hMul Real Real Real qz579 qz585 qz702))

noncomputable abbrev qz703 := (Enclosure.sfrac Bool.false 775738 2000)

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz356 (@HSub.hSub Real Real Real qz356 qz535 qz703) (@HMul.hMul Real Real Real qz350 qz703 (Real.log Real.pi)))

noncomputable def Ns408p1605 := @Enclosure.Real.IsNear.addLit_ft_p qz245 (Enclosure.sfrac Bool.true Ns408p1601 Ns408p1602) 13327876255814958072267 9007199254740992000 19862306382045177 2048000000000000000000 Ns408p1601 Ns408p1602 0 1 Ns408p1604 

noncomputable def Ns408p1606 := nat_lit 447209317530157615218734137344000 

noncomputable abbrev qz246 := (@HSub.hSub Real Real Real qz356 qz535 qz703)

noncomputable def Ns408p1607 := @Enclosure.Real.IsNear.subLit_ff_p qz246 (@HMul.hMul Real Real Real qz4 qz703 (Real.log Real.pi)) 17327119875690751476171 9007199254740992000 7837386594023 2000000000000000000 14898343458309 33554432000 387869 67108864000 Ns408p1606 13327876255814958072267 9007199254740992000 

noncomputable def Ns408p1608 := nat_lit 34654239751381502952342000 

noncomputable abbrev qz247 := qz535

noncomputable def Ns408p1609 := @Enclosure.Real.IsNear.subLit_ff_p qz247 qz703 20820733243427885302219 9007199254740992000 7837386594023 2000000000000000000 775738 2000 0 1 Ns408p1608 17327119875690751476171 9007199254740992000 7837386594023 2000000000000000000 

noncomputable def Ns408p1610 := nat_lit 46884123238341161416114664232621965312 

noncomputable def Ns408p1611 := nat_lit 57648042210054944455655424 

noncomputable def Ns408p1612 := nat_lit 876825360601704119119142878742145588516225982903839399546691782815477378580480 

noncomputable def Ns408p1613 := nat_lit 1387729766705777826557528531728360385056786108874547830532121728711860944896 

noncomputable def Ns408p1614 := nat_lit 13293699947179366220589089664815033055460165535603225107528449408368640 

noncomputable def Ns408p1615 := BSN.log_dyadic_bound 309926778576 4504230778576 4 3 Ns408p1612 134217728 50000000 Ns408p1613 Ns408p1614 18499719 4814157557152 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 309926778576) (BSN.artanhQ 4504230778576) 0 3 Ns408p1613 Ns408p1612 Ns408p1614 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz536 := (Real.log (Enclosure.sfrac Bool.false 2407078778576 16000000))

noncomputable def Ns408p1616 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 775738 4000) qz536 775738 4000 0 1 53688923092610151 4503599627370496 20000017 1000000000000000 20824268911007606658219 9007199254740992000 7757386593773 2000000000000000000 (Enclosure.Real.IsNear.const Bool.false 775738 4000) (BSN.isNear_log_sfrac 2407078778576 16000000 53688923092610151 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2407078778576) qz359)) Bool.false Ns408p1611 Ns408p100 1000000850000000 50000000000000000000000 53688923092610151 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2407078778576 16000000 17 4814157557152 4194304000000 18499719 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns408p1615 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns408p1617 := BSN.arctan_dyadic_bound_f 1000 1551476 1 0 16777216 6250000 0 1 1 0 1 1 10813 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1551476) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1551476) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns408p1618 := @Enclosure.Real.IsNear.subLit_ff_p qz12 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz13 (@Nat.cast Real Real.instNatCast 1551476))) 884279719003555 562949953421312 1 2000000000000000 10813 16777216 1 6250000 14829664672295602356224 883916894930339 562949953421312 320000001 2000000000000000 qz14 (Ns408p1617 rfl) rfl rfl 

noncomputable abbrev qz537 := (@HMul.hMul Real Real Real qz579 qz585 qz702)

noncomputable abbrev qz248 := qz537

noncomputable abbrev qz538 := qz702

noncomputable abbrev qz249 := qz538

noncomputable def Ns408p1619 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 775738 4000) qz536) qz248 20824268911007606658219 9007199254740992000 7757386593773 2000000000000000000 883916894930339 2251799813685248 320000001 8000000000000000 Ns408p1610 20820733243427885302219 9007199254740992000 7837386594023 2000000000000000000 (Ns408p1616 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz16 qz249 1 4 0 1 883916894930339 562949953421312 320000001 2000000000000000 883916894930339 2251799813685248 320000001 8000000000000000 qz367 Ns408p1618 rfl) 

noncomputable def Ns408p1620 := @Ns408p1605 Ns408p1599 Ns408p1600 19862306382045177 2048000000000000000000 (@Ns408p1607 19862306382045177 2048000000000000000000 (Ns408p1609 (Ns408p1619 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 775738 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz703 (Real.log Real.pi) 775738 2000 0 1 38410761 33554432 1 67108864 14898343458309 33554432000 387869 67108864000 (Enclosure.Real.IsNear.const Bool.false 775738 2000) RS409to420.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns408p1601 Ns408p1602) 

noncomputable def Ns408p1621 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz241) Bool.false Ns408p1599 Ns408p1600 19862306382045177 2048000000000000000000 49650200905 33554432 327 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz241) (@HAdd.hAdd Real Real Real qz368 qz245 (Enclosure.sfrac Bool.true Ns408p1601 Ns408p1602)) Bool.false Ns408p1599 Ns408p1600 19862306382045177 2048000000000000000000 Ns408p1603 (Ns408p1620 rfl rfl)) 

noncomputable def Ns408p1622 := BSN.cos_dyadic_bound_f 79312162 68719476736 1 0 33554432 12512208 0 1 1 0 1 1 33554409 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 79312162) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 79312162) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns408p1623 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz241) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49650200905) qz418) Bool.false 49650200905 33554432 327 33554432 Bool.true 33554409 33554432 1 6250000 (Ns408p1621 rfl) (Enclosure.sfrac_false_div 49650200905 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49650200905) qz418) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5581097242817346928640) qz430) 226375608064910080 72057594037927936 Bool.false 33554409 33554432 235 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q2 49650200905 33554432 226375608064910080 72057594037927936 235 5581097242817346928640 Ns408p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554409 33554432 5581097242817346928640 Ns408p100 79312162 68719476736 12512208 12500000 (Ns408p1622 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns408p1624 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz241) Bool.false Ns408p1599 Ns408p1600 19862306382045177 2048000000000000000000 397201607245 268435456 2605 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz241) (@HAdd.hAdd Real Real Real qz368 qz245 (Enclosure.sfrac Bool.true Ns408p1601 Ns408p1602)) Bool.false Ns408p1599 Ns408p1600 19862306382045177 2048000000000000000000 Ns408p1603 (Ns408p1620 rfl rfl)) 

noncomputable def Ns408p1625 := Ns408p1598 48880 BSN.abs_quadSignPos (BSN.cos_quad_nat3 599 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 237219205 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 399 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 174627111 268435456) qz244 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 1) Bool.true 33554409 33554432 129831527 13107200000000 268435272 268435456 2659 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz241)) Bool.true 33554409 33554432 129831527 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz241) qz241) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz241)) Bool.true 33554409 33554432 2077304432 209715200000000 33554409 33554432 129831527 13107200000000 (Ns408p1623 rfl rfl) rfl)) rfl) (Ns408p1624 rfl) RS409to420.d7 

noncomputable def Ns408p1626 := nat_lit 112508566696410213696321727385812038823403207950685193758149466268958720 

noncomputable def Ns408p1627 := nat_lit 51297059130207336992055993936474518056537458344113563581069572243456 

noncomputable def Ns408p1628 := nat_lit 294582241347244509706665004877420095317774007795427895025545918063640576 

noncomputable def Ns408p1629 := BSN.sin_dyadic_bound_f 290911948 268435456 3 2 268435456 134217728 Ns408p1626 Ns408p142 Ns408p1627 Ns408p1628 Ns408p145 Ns408p1627 237219205 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 290911948) qz372 0 2 Ns408p1626 Ns408p142 Ns408p1627 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 290911948) qz373 0 2 Ns408p1628 Ns408p145 Ns408p1627 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1630 := nat_lit 20520292456891402904823881469276633864281382514908342781068725337456640 

noncomputable def Ns408p1631 := nat_lit 1707702454509329240192995194036792926737350181005157720522642948096 

noncomputable def Ns408p1632 := nat_lit 53740858249789230598626043760648457694093665162562127504584863033327616 

noncomputable def Ns408p1633 := BSN.sin_dyadic_bound_f 190130384 268435456 3 2 268435456 134217728 Ns408p1630 Ns408p142 Ns408p1631 Ns408p1632 Ns408p145 Ns408p1631 174627111 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 190130384) qz372 0 2 Ns408p1630 Ns408p142 Ns408p1631 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 190130384) qz373 0 2 Ns408p1632 Ns408p145 Ns408p1631 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1634 := nat_lit 10250553355917339760304392219687782394694939493583922156250155815247745 

noncomputable def Ns408p1635 := nat_lit 426163162558489387538434819415192652196952116292963785419557674881 

noncomputable def Ns408p1636 := nat_lit 26845997382282223722741203109474662626573665513102940848812109756080001 

noncomputable def Ns408p1637 := BSN.sin_dyadic_bound_f 159844239 268435456 3 2 268435456 134217728 Ns408p1634 Ns408p142 Ns408p1635 Ns408p1636 Ns408p145 Ns408p1635 150564043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 159844239) qz372 0 2 Ns408p1634 Ns408p142 Ns408p1635 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 159844239) qz373 0 2 Ns408p1636 Ns408p145 Ns408p1635 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1638 := nat_lit 32887489311531301118910959517696 

noncomputable def Ns408p1639 := BSN.sin_dyadic_bound_f 75728208 268435456 2 1 268435456 134217728 Ns408p1638 Ns408p133 Ns408p1638 Ns408p1638 Ns408p134 Ns408p1638 74727715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 75728208) qz372 0 1 Ns408p1638 Ns408p133 Ns408p1638 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 75728208) qz373 0 1 Ns408p1638 Ns408p134 Ns408p1638 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1640 := Ns408p1596 82972 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 257 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 150564043 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 74727715 268435456) qz244 rfl rfl (Ns408p1625 RS409to420.d9 RS409to420.d11 RS409to420.d13 RS409to420.d17 (Ns408p1629 rfl rfl) (Ns408p1633 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns408p1624 rfl) RS409to420.d19 RS409to420.d21 RS409to420.d23 RS409to420.d25 RS409to420.d17 (Ns408p1637 rfl rfl) (Ns408p1639 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns408p1641 := nat_lit 12170209903469690636278973813776 

noncomputable def Ns408p1642 := BSN.sin_dyadic_bound_f 59064226 268435456 2 1 268435456 134217728 Ns408p1641 Ns408p133 Ns408p1641 Ns408p1641 Ns408p134 Ns408p1641 58588790 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 59064226) qz372 0 1 Ns408p1641 Ns408p133 Ns408p1641 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 59064226) qz373 0 1 Ns408p1641 Ns408p134 Ns408p1641 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1643 := nat_lit 16213989724698149069961087935414691035343321027687851692282389228288014256986873544213729370107424593664111201 

noncomputable def Ns408p1644 := nat_lit 27080437915116374181380725232645203650333652471335259188375766074439814055780029036601232801861426573921 

noncomputable def Ns408p1645 := nat_lit 98139756531699548628713734291909969857552543590172379404951629646168049268302411902677715003568651813198852705 

noncomputable def Ns408p1646 := BSN.cos_dyadic_bound_f 416282327 268435456 4 3 268435456 134217728 Ns408p1643 Ns408p252 Ns408p1644 Ns408p1645 Ns408p255 Ns408p1644 5374742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 416282327) qz370 0 3 Ns408p1643 Ns408p252 Ns408p1644 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 416282327) qz371 0 3 Ns408p1645 Ns408p255 Ns408p1644 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1647 := Ns408p1594 111875 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58588790 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 5374742 268435456) qz244 rfl rfl (Ns408p1640 rfl rfl) (Ns408p1624 rfl) RS409to420.d27 RS409to420.d29 RS409to420.d31 RS409to420.d33 RS409to420.d17 (Ns408p1642 rfl rfl) (Ns408p1646 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1648 := nat_lit 12856465929299612860452176080705678979081924154748507690063325258114273750768006780774970182705814970458144961 

noncomputable def Ns408p1649 := nat_lit 13529290863878244545661099054561793022272423647328743286934262348038431102109029208415934884976439820481 

noncomputable def Ns408p1650 := nat_lit 77854174232140715006869752582262586408949909781444235671007181896589229650952458258298629718477021901501202625 

noncomputable def Ns408p1651 := BSN.cos_dyadic_bound_f 392891759 268435456 4 3 268435456 134217728 Ns408p1648 Ns408p252 Ns408p1649 Ns408p1650 Ns408p255 Ns408p1649 28710646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 392891759) qz370 0 3 Ns408p1648 Ns408p252 Ns408p1649 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 392891759) qz371 0 3 Ns408p1650 Ns408p255 Ns408p1649 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1652 := nat_lit 3028770111207784403592491521761 

noncomputable def Ns408p1653 := BSN.sin_dyadic_bound_f 41717337 268435456 2 1 268435456 134217728 Ns408p1652 Ns408p133 Ns408p1652 Ns408p1652 Ns408p134 Ns408p1652 41549613 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 41717337) qz372 0 1 Ns408p1652 Ns408p133 Ns408p1652 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 41717337) qz373 0 1 Ns408p1652 Ns408p134 Ns408p1652 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1654 := Ns408p1592 137129 BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 28710646 268435456) BSN.abs_quadSignPos qz650 (BSN.sfrac_eq_quadSignPos_mul Bool.false 41549613 268435456) qz244 rfl rfl (Ns408p1647 rfl) (Ns408p1624 rfl) RS409to420.d35 RS409to420.d37 RS409to420.d39 RS409to420.d41 RS409to420.d17 (Ns408p1651 rfl rfl) (Ns408p1653 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1655 := nat_lit 9377611466790591278321306613201 

noncomputable def Ns408p1656 := BSN.sin_dyadic_bound_f 55337949 268435456 2 1 268435456 134217728 Ns408p1655 Ns408p133 Ns408p1655 Ns408p1655 Ns408p134 Ns408p1655 54946824 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 55337949) qz372 0 1 Ns408p1655 Ns408p133 Ns408p1655 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 55337949) qz373 0 1 Ns408p1655 Ns408p134 Ns408p1655 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1657 := nat_lit 442971991644009470786684266642255235152326267826086099818255096190625 

noncomputable def Ns408p1658 := nat_lit 2578753830728217755778063904237494253803412486985765176875390625 

noncomputable def Ns408p1659 := nat_lit 1328910817424366955924541243798957230468471196653284327924411537790625 

noncomputable def Ns408p1660 := BSN.cos_dyadic_bound_f 84416285 268435456 3 2 268435456 134217728 Ns408p1657 Ns408p123 Ns408p1658 Ns408p1659 Ns408p126 Ns408p1658 255271072 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 84416285) qz370 0 2 Ns408p1657 Ns408p123 Ns408p1658 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 84416285) qz371 0 2 Ns408p1659 Ns408p126 Ns408p1658 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1661 := Ns408p1590 159843 BSN.abs_quadSignPos qz415 (BSN.sfrac_eq_quadSignPos_mul Bool.false 54946824 268435456) BSN.abs_quadSignNeg qz395 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 255271072 268435456) qz244 rfl rfl (Ns408p1654 rfl) (Ns408p1624 rfl) RS409to420.d43 RS409to420.d45 RS409to420.d52 RS409to420.d54 RS409to420.d17 (Ns408p1656 rfl rfl) (Ns408p1660 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns408p1662 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 11) 103278745 268435456 159843 268435456 103278745 268435456 159843 268435456 55447354018365440 103278745 134217728 159843 134217728 (Ns408p1661 rfl) 

noncomputable def Ns408p1663 := @Enclosure.Real.IsNear.mulLit_tf qz700 (Zeta.RiemannSiegel.correction qz243) 10066213 33554432 1 33554432 48570617408115 70368744177664 1850854433586189 109951162777600000000 488922180371593518495 2361183241434822606848 

noncomputable abbrev qz704 := (@HPow.hPow Real Real Real qz206 qz242 qz208)

noncomputable def Ns408p1664 := @Enclosure.Real.IsNear.mulLit_tf qz33 qz704 1 1 0 1 10066213 33554432 1 33554432 10066213 33554432 1 33554432 

noncomputable def Ns408p1665 := @Enclosure.Real.IsNear.sqrt_image qz242 2071357377757 16777216000 387869 16777216000 186417820 186417855 16777216 (@Enclosure.Real.IsNear.of_eq qz242 (@HMul.hMul Real Real Real qz4 qz241 qz2) Bool.false 2071357377757 16777216000 387869 16777216000 (BSN.t_div_two_pi_mk qz241 775738 1000 qz244) (@Enclosure.Real.IsNear.mulLit_ff qz241 qz2 775738 1000 0 1 5340353 33554432 1 33554432 2071357377757 16777216000 387869 16777216000 (Enclosure.Real.IsNear.const Bool.false 775738 1000) RS409to420.d48 rfl)) 

noncomputable abbrev qz774 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 775738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz705 := qz774

noncomputable abbrev qz539 := qz705

noncomputable abbrev qz250 := qz539

noncomputable def Ns408p1666 := @Enclosure.Real.IsNear.sqrt_image qz250 372835675 33554432 35 33554432 55924699 55924705 16777216 (@Enclosure.Real.IsNear.recentre' qz250 Bool.false 372835675 33554432 35 33554432 372835675 33554432 35 33554432 (Ns408p1665 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns408p1667 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz250) 27962351 8388608 3 16777216 5033106 5033107 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz250) Bool.false 111849404 33554432 6 33554432 27962351 8388608 3 16777216 (Ns408p1666 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns408p1668 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz250)) Bool.false 10066213 33554432 1 33554432 10066213 33554432 1 33554432 (Ns408p1667 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz533))

noncomputable abbrev qz706 := (@HMul.hMul Real Real Real qz714 qz772 qz772)

noncomputable abbrev qz540 := (@HSub.hSub Real Real Real qz584 (@HSub.hSub Real Real Real qz584 qz706 qz699) qz598)

noncomputable abbrev qz252 := (Real.cos (@HMul.hMul Real Real Real qz350 qz347 qz540))

noncomputable def Ns408p1669 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz243) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv qz251) qz252) Bool.false 48570617408115 

noncomputable def Ns408p1670 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz251) qz252 21930945 16777216 97 

noncomputable def Ns408p1671 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz251) Bool.false 43861890 33554432 388 33554432 21930945 16777216 97 

noncomputable def Ns408p1672 := @Enclosure.Real.IsNear.recentre' qz251 Bool.false 12834603 16777216 1414804432 209715200000000 12834603 16777216 88425277 13107200000000 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz350 qz347 qz533)

noncomputable def Ns408p1673 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23479779) qz418) Bool.false 23479779 33554432 221 33554432 Bool.false 12834603 16777216 1 

noncomputable def Ns408p1674 := nat_lit 944512639348641515076254261 

noncomputable def Ns408p1675 := nat_lit 144115188075855872000000000000000 

noncomputable def Ns408p1676 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz243 884279719003555 140737488355328 1 500000000000000 3736923 33554432 35 33554432 3304485220377921761265 4722366482869645213696 Ns408p1674 

noncomputable def Ns408p1677 := @Enclosure.Real.IsNear.subLit_ff_p qz250 qz31 372835675 33554432 35 33554432 11 1 0 1 3736923 3736923 33554432 35 

noncomputable def Ns408p1678 := @Ns408p1677 33554432 (@Enclosure.Real.IsNear.recentre' qz250 Bool.false 372835675 33554432 35 33554432 372835675 33554432 35 33554432 (Ns408p1665 rfl rfl rfl rfl rfl rfl) rfl) qz398 

noncomputable def Ns408p1679 := @Enclosure.Real.IsNear.recentre' qz253 Bool.false 3304485220377921761265 4722366482869645213696 Ns408p1674 Ns408p1675 23479779 33554432 221 33554432 (@Ns408p1676 Ns408p1675 RS409to420.d47 (Ns408p1678 rfl rfl) rfl) 

noncomputable def Ns408p1680 := nat_lit 647361463836816835013205887578273335239320687570777768057147041 

noncomputable def Ns408p1681 := nat_lit 92374486856818440391660383762019044896047455534068830604961 

noncomputable def Ns408p1682 := nat_lit 1941899642536736868158834341967295967628169967801265166510231201 

noncomputable def Ns408p1683 := BSN.cos_dyadic_bound_f 23479779 33554432 3 2 16777216 6250000 Ns408p1680 Ns408p489 Ns408p1681 Ns408p1682 Ns408p492 Ns408p1681 12834603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 23479779) qz619 0 2 Ns408p1680 Ns408p489 Ns408p1681 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 23479779) (BSN.cosOddQ 33554432) 0 2 Ns408p1682 Ns408p492 Ns408p1681 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1684 := @Enclosure.Real.IsNear.inv_image qz251 12834603 16777216 88425277 13107200000000 21930751 21931139 16777216 (Ns408p1672 (@Ns408p1673 6250000 (Ns408p1679 rfl) (Enclosure.sfrac_false_div 23479779 33554432) (Ns408p1683 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns408p1685 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 8858828 16777216 

noncomputable abbrev qz254 := (@HMul.hMul Real Real Real qz350 qz347 qz540)

noncomputable def Ns408p1686 := @Enclosure.Real.IsNear.cos_image qz254 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 34041655)) qz418) Bool.true 34041655 33554432 

noncomputable def Ns408p1687 := nat_lit 160757171127043434399782584405 

noncomputable def Ns408p1688 := nat_lit 38751760199896777157141814358190317 

noncomputable def Ns408p1689 := @Enclosure.Real.IsNear.recentre' qz254 Bool.true Ns408p1687 Ns408p320 Ns408p1688 

noncomputable abbrev qz255 := qz540

noncomputable def Ns408p1690 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz255 884279719003555 140737488355328 1 500000000000000 181794479362471 

noncomputable abbrev qz541 := (@HSub.hSub Real Real Real qz584 qz706 qz699)

noncomputable abbrev qz256 := qz541

noncomputable def Ns408p1691 := @Enclosure.Real.IsNear.subLit_tf qz256 qz28 111425735184807 1125899906842624 1435990955 1125899906842624 1 16 

noncomputable abbrev qz542 := qz706

noncomputable abbrev qz257 := qz542

noncomputable def Ns408p1692 := @Enclosure.Real.IsNear.subLit_ff_n qz257 qz243 13964593507929 1125899906842624 261585835 1125899906842624 3736923 33554432 35 33554432 

noncomputable def Ns408p1693 := @Enclosure.Real.IsNear.mulLit_ff qz243 qz243 3736923 33554432 35 33554432 3736923 33554432 35 33554432 13964593507929 1125899906842624 

noncomputable def Ns408p1694 := nat_lit 2861707746579355030262856872096609932867720134403654075038690625 

noncomputable def Ns408p1695 := nat_lit 1803372022892858034982487867110875523412024904755049937890625 

noncomputable def Ns408p1696 := nat_lit 8581516495692279374718605640555608047556336353401452125240290625 

noncomputable def Ns408p1697 := BSN.cos_dyadic_bound_f 34041655 33554432 3 2 16777216 6250000 Ns408p1694 Ns408p489 Ns408p1695 Ns408p1696 Ns408p492 Ns408p1695 8858828 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 34041655) qz619 0 2 Ns408p1694 Ns408p489 Ns408p1695 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 34041655) (BSN.cosOddQ 33554432) 0 2 Ns408p1696 Ns408p492 Ns408p1695 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns408p1698 := @Ns408p1685 860527216 104857600000000 2214707 4194304 53782951 6553600000000 (@Ns408p1686 135 16777216 Bool.false 8858828 16777216 1 6250000 (@Ns408p1689 Ns408p323 34041655 33554432 135 16777216 (@Ns408p1690 1125899906842624 1435990955 1125899906842624 Ns408p1687 Ns408p320 Ns408p1688 Ns408p323 RS409to420.d47 (@Ns408p1691 0 1 2908711669799536 181794479362471 1125899906842624 1435990955 1125899906842624 (@Ns408p1692 3738827254308613914624 111425735184807 1125899906842624 1435990955 1125899906842624 (@Ns408p1693 261585835 1125899906842624 (Ns408p1678 rfl rfl) (Ns408p1678 rfl rfl) rfl) (Ns408p1678 rfl rfl) rfl rfl) qz381 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 34041655 33554432) (BSN.cos_neg_of_bound 34041655 33554432 Bool.false 8858828 16777216 1 6250000 (Ns408p1697 rfl rfl)) rfl rfl) 

noncomputable def Ns408p1699 := @Ns408p1663 9353494200513772802973 Ns408p75 (Ns408p1664 qz51 (@Enclosure.Real.IsNear.of_eq qz704 (@Inv.inv Real Real.instInv (Real.sqrt qz250)) Bool.false 10066213 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz242 (BSN.t_div_two_pi_nonneg qz241 775738 1000 qz244)) Ns408p1668) rfl) (@Ns408p1669 70368744177664 1850854433586189 109951162777600000000 (BSN.correction_mk qz243 (BSN.cos_two_pi_p_ne_zero_mk qz241 775738 1000 11 qz244 rfl rfl (@BSN.floor_sqrt_eq_dec qz241 775738 1000 11 qz244 rfl rfl rfl))) (@Ns408p1670 8388608 2214707 4194304 53782951 6553600000000 48570617408115 70368744177664 1850854433586189 109951162777600000000 (@Ns408p1671 8388608 (Ns408p1684 rfl rfl rfl rfl rfl) rfl) (Ns408p1698 rfl) rfl)) 

noncomputable def Ns408p1700 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz241) (hardyZApproximantRS₀ qz241) Bool.true 1327976716102205219425 2361183241434822606848 Ns408p1586 Ns408p75 (@Eq.refl Real (hardyZApproximantRS₀ qz241)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz241) (@HSub.hSub Real Real Real qz30 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz241) qz241 11) (@HMul.hMul Real Real Real qz4 qz700 (Zeta.RiemannSiegel.correction qz243))) Bool.true 1327976716102205219425 2361183241434822606848 Ns408p1586 Ns408p75 (BSN.hardyZApproximantRS₀_eq qz241 11 (@BSN.floor_sqrt_eq_dec qz241 775738 1000 11 qz244 rfl rfl rfl)) (@Ns408p1588 1327976716102205219425 2361183241434822606848 Ns408p1586 Ns408p75 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz241) qz241 11) (@HAdd.hAdd Real Real Real qz368 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 11)) Bool.true 103278745 134217728 159843 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz241) qz241 11) (Ns408p1662 (Ns408p1661 rfl) rfl rfl)) (Ns408p1699 rfl) rfl rfl)) 

theorem RS409to420.d67 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz241) Bool.true 1327976716102205219425 2361183241434822606848 Ns408p1586 Ns408p75 := Ns408p1700 

noncomputable def RS409to420.d68 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz543 := (RS409to420.d3 qz580 qz600 (@Enclosure.dec_le_dec qz580 qz600 760048 1000 762013 1000 (@Eq.refl Real qz580) qz603 rfl rfl rfl))

noncomputable abbrev qz258 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz543)

noncomputable def Ns408p1701 := @Enclosure.Real.IsNear.of_eq qz258 (hardyZApproximantRS₀ qz3) Bool.true 7251450955349397247091 4722366482869645213696 Ns408p74 Ns408p75 

noncomputable abbrev qz544 := (@Enclosure.dec_le_dec qz580 qz600 760048 1000 762013 1000 (@Eq.refl Real qz580) qz603 rfl rfl rfl)

noncomputable abbrev qz259 := qz544

noncomputable def Ns408p1702 := @Enclosure.Real.IsNear.neg_val qz258 7251450955349397247091 4722366482869645213696 Ns408p74 Ns408p75 (Ns408p1701 (RS409to420.d4 qz3 qz32 qz259) RS409to420.d49) rfl 

noncomputable abbrev qz260 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz543)

noncomputable def Ns408p1703 := @Enclosure.Real.IsNear.of_eq qz260 (hardyZApproximantRS₀ qz32) Bool.false 48302364134301611608561 9444732965739290427392 13533049854040222554889 Ns408p205 

noncomputable def Ns408p1704 := @Enclosure.Real.IsNear.pos_val qz260 48302364134301611608561 9444732965739290427392 13533049854040222554889 Ns408p205 (Ns408p1703 (RS409to420.d50 qz3 qz32 qz259) RS409to420.d55) rfl 

noncomputable def Ns408p1705 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz258 qz3 qz3 760048 1000 760048 1000 

noncomputable def Ns408p1706 := @Enclosure.norm_gt_of_isNear qz258 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 7251450955349397247091 4722366482869645213696 Ns408p74 

noncomputable def Ns408p1707 := @Ns408p1706 Ns408p75 274986237 5368709120 1213 5368709120 (Ns408p1701 (RS409to420.d4 qz3 qz32 qz259) RS409to420.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable def Ns408p1708 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz260 qz3 qz32 760048 1000 762013 1000 

noncomputable def Ns408p1709 := @Enclosure.norm_gt_of_isNear qz260 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 48302364134301611608561 9444732965739290427392 13533049854040222554889 

noncomputable def Ns408p1710 := @Ns408p1709 Ns408p205 274986237 5368709120 1213 5368709120 (Ns408p1703 (RS409to420.d50 qz3 qz32 qz259) RS409to420.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable abbrev qz261 := qz543

noncomputable def Ns408p1711 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz261 (@BSN.thirtyTwoPi_le_dec qz3 760048 1000 qz8 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz258 qz260 (Ns408p1702 rfl rfl) (Ns408p1704 rfl rfl)) (Ns408p1705 qz8 qz8 rfl rfl rfl rfl (Ns408p1707 rfl)) (Ns408p1708 qz8 qz36 rfl rfl rfl rfl (Ns408p1710 rfl)) 

noncomputable abbrev qz545 := (RS409to420.d3 qz600 qz611 (@Enclosure.dec_le_dec qz600 qz611 762013 1000 763159 1000 qz603 qz614 rfl rfl rfl))

noncomputable abbrev qz262 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz545)

noncomputable def Ns408p1712 := @Enclosure.Real.IsNear.of_eq qz262 (hardyZApproximantRS₀ qz32) Bool.false 48302364134301611608561 9444732965739290427392 13533049854040222554889 Ns408p205 

noncomputable abbrev qz546 := (@Enclosure.dec_le_dec qz600 qz611 762013 1000 763159 1000 qz603 qz614 rfl rfl rfl)

noncomputable abbrev qz263 := qz546

noncomputable def Ns408p1713 := @Enclosure.Real.IsNear.pos_val qz262 48302364134301611608561 9444732965739290427392 13533049854040222554889 Ns408p205 (Ns408p1712 (RS409to420.d4 qz32 qz61 qz263) RS409to420.d55) rfl 

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz545)

noncomputable def Ns408p1714 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantRS₀ qz61) Bool.true 15041876900279702608685 18889465931478580854784 Ns408p370 Ns408p371 

noncomputable def Ns408p1715 := @Enclosure.Real.IsNear.neg_val qz264 15041876900279702608685 18889465931478580854784 Ns408p370 Ns408p371 (Ns408p1714 (RS409to420.d50 qz32 qz61 qz263) RS409to420.d57) rfl 

noncomputable def Ns408p1716 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz262 qz3 qz32 760048 1000 762013 1000 

noncomputable def Ns408p1717 := @Enclosure.norm_gt_of_isNear qz262 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 48302364134301611608561 9444732965739290427392 13533049854040222554889 

noncomputable def Ns408p1718 := @Ns408p1717 Ns408p205 274986237 5368709120 1213 5368709120 (Ns408p1712 (RS409to420.d4 qz32 qz61 qz263) RS409to420.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable def Ns408p1719 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz264 qz3 qz61 760048 1000 763159 1000 

noncomputable def Ns408p1720 := @Enclosure.norm_gt_of_isNear qz264 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 15041876900279702608685 18889465931478580854784 Ns408p370 

noncomputable def Ns408p1721 := @Ns408p1720 Ns408p371 274986237 5368709120 1213 5368709120 (Ns408p1714 (RS409to420.d50 qz32 qz61 qz263) RS409to420.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable abbrev qz265 := qz545

noncomputable def Ns408p1722 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz265 (@BSN.thirtyTwoPi_le_dec qz32 762013 1000 qz36 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz262 qz264 (Ns408p1713 rfl rfl) (Ns408p1715 rfl rfl)) (Ns408p1716 qz8 qz36 rfl rfl rfl rfl (Ns408p1718 rfl)) (Ns408p1719 qz8 qz64 rfl rfl rfl rfl (Ns408p1721 rfl)) 

noncomputable abbrev qz547 := (RS409to420.d3 qz611 qz620 (@Enclosure.dec_le_dec qz611 qz620 763159 1000 763813 1000 qz614 qz623 rfl rfl rfl))

noncomputable abbrev qz266 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz547)

noncomputable def Ns408p1723 := @Enclosure.Real.IsNear.of_eq qz266 (hardyZApproximantRS₀ qz61) Bool.true 15041876900279702608685 18889465931478580854784 Ns408p370 Ns408p371 

noncomputable abbrev qz548 := (@Enclosure.dec_le_dec qz611 qz620 763159 1000 763813 1000 qz614 qz623 rfl rfl rfl)

noncomputable abbrev qz267 := qz548

noncomputable def Ns408p1724 := @Enclosure.Real.IsNear.neg_val qz266 15041876900279702608685 18889465931478580854784 Ns408p370 Ns408p371 (Ns408p1723 (RS409to420.d4 qz61 qz79 qz267) RS409to420.d57) rfl 

noncomputable abbrev qz268 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz547)

noncomputable def Ns408p1725 := @Enclosure.Real.IsNear.of_eq qz268 (hardyZApproximantRS₀ qz79) Bool.false 13830714192051142581 36893488147419103232 54263195025175100639429 Ns408p497 

noncomputable def Ns408p1726 := @Enclosure.Real.IsNear.pos_val qz268 13830714192051142581 36893488147419103232 54263195025175100639429 Ns408p497 (Ns408p1725 (RS409to420.d50 qz61 qz79 qz267) RS409to420.d58) rfl 

noncomputable def Ns408p1727 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz266 qz3 qz61 760048 1000 763159 1000 

noncomputable def Ns408p1728 := @Enclosure.norm_gt_of_isNear qz266 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 15041876900279702608685 18889465931478580854784 Ns408p370 

noncomputable def Ns408p1729 := @Ns408p1728 Ns408p371 274986237 5368709120 1213 5368709120 (Ns408p1723 (RS409to420.d4 qz61 qz79 qz267) RS409to420.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable def Ns408p1730 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz268 qz3 qz79 760048 1000 763813 1000 

noncomputable def Ns408p1731 := @Enclosure.norm_gt_of_isNear qz268 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 13830714192051142581 36893488147419103232 54263195025175100639429 

noncomputable def Ns408p1732 := @Ns408p1731 Ns408p497 274986237 5368709120 1213 5368709120 (Ns408p1725 (RS409to420.d50 qz61 qz79 qz267) RS409to420.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable abbrev qz269 := qz547

noncomputable def Ns408p1733 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz269 (@BSN.thirtyTwoPi_le_dec qz61 763159 1000 qz64 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz266 qz268 (Ns408p1724 rfl rfl) (Ns408p1726 rfl rfl)) (Ns408p1727 qz8 qz64 rfl rfl rfl rfl (Ns408p1729 rfl)) (Ns408p1730 qz8 qz82 rfl rfl rfl rfl (Ns408p1732 rfl)) 

noncomputable abbrev qz549 := (RS409to420.d3 qz620 qz628 (@Enclosure.dec_le_dec qz620 qz628 763813 1000 765286 1000 qz623 qz631 rfl rfl rfl))

noncomputable abbrev qz270 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz549)

noncomputable def Ns408p1734 := @Enclosure.Real.IsNear.of_eq qz270 (hardyZApproximantRS₀ qz79) Bool.false 13830714192051142581 36893488147419103232 54263195025175100639429 Ns408p497 

noncomputable abbrev qz550 := (@Enclosure.dec_le_dec qz620 qz628 763813 1000 765286 1000 qz623 qz631 rfl rfl rfl)

noncomputable abbrev qz271 := qz550

noncomputable def Ns408p1735 := @Enclosure.Real.IsNear.pos_val qz270 13830714192051142581 36893488147419103232 54263195025175100639429 Ns408p497 (Ns408p1734 (RS409to420.d4 qz79 qz97 qz271) RS409to420.d58) rfl 

noncomputable abbrev qz272 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz549)

noncomputable def Ns408p1736 := @Enclosure.Real.IsNear.of_eq qz272 (hardyZApproximantRS₀ qz97) Bool.true 759500189377543214407 295147905179352825856 3479697829428540488989 Ns408p626 

noncomputable def Ns408p1737 := @Enclosure.Real.IsNear.neg_val qz272 759500189377543214407 295147905179352825856 3479697829428540488989 Ns408p626 (Ns408p1736 (RS409to420.d50 qz79 qz97 qz271) RS409to420.d59) rfl 

noncomputable def Ns408p1738 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz270 qz3 qz79 760048 1000 763813 1000 

noncomputable def Ns408p1739 := @Enclosure.norm_gt_of_isNear qz270 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 13830714192051142581 36893488147419103232 54263195025175100639429 

noncomputable def Ns408p1740 := @Ns408p1739 Ns408p497 274986237 5368709120 1213 5368709120 (Ns408p1734 (RS409to420.d4 qz79 qz97 qz271) RS409to420.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable def Ns408p1741 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz272 qz3 qz97 760048 1000 765286 1000 

noncomputable def Ns408p1742 := @Enclosure.norm_gt_of_isNear qz272 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 759500189377543214407 295147905179352825856 3479697829428540488989 

noncomputable def Ns408p1743 := @Ns408p1742 Ns408p626 274986237 5368709120 1213 5368709120 (Ns408p1736 (RS409to420.d50 qz79 qz97 qz271) RS409to420.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable abbrev qz273 := qz549

noncomputable def Ns408p1744 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz273 (@BSN.thirtyTwoPi_le_dec qz79 763813 1000 qz82 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz270 qz272 (Ns408p1735 rfl rfl) (Ns408p1737 rfl rfl)) (Ns408p1738 qz8 qz82 rfl rfl rfl rfl (Ns408p1740 rfl)) (Ns408p1741 qz8 qz100 rfl rfl rfl rfl (Ns408p1743 rfl)) 

noncomputable abbrev qz551 := (RS409to420.d3 qz628 qz636 (@Enclosure.dec_le_dec qz628 qz636 765286 1000 766594 1000 qz631 qz639 rfl rfl rfl))

noncomputable abbrev qz274 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns408p1745 := @Enclosure.Real.IsNear.of_eq qz274 (hardyZApproximantRS₀ qz97) Bool.true 759500189377543214407 295147905179352825856 3479697829428540488989 Ns408p626 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz628 qz636 765286 1000 766594 1000 qz631 qz639 rfl rfl rfl)

noncomputable abbrev qz275 := qz552

noncomputable def Ns408p1746 := @Enclosure.Real.IsNear.neg_val qz274 759500189377543214407 295147905179352825856 3479697829428540488989 Ns408p626 (Ns408p1745 (RS409to420.d4 qz97 qz115 qz275) RS409to420.d59) rfl 

noncomputable abbrev qz276 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns408p1747 := @Enclosure.Real.IsNear.of_eq qz276 (hardyZApproximantRS₀ qz115) Bool.false 376773199373746121241 295147905179352825856 27233277308953644852473 Ns408p743 

noncomputable def Ns408p1748 := @Enclosure.Real.IsNear.pos_val qz276 376773199373746121241 295147905179352825856 27233277308953644852473 Ns408p743 (Ns408p1747 (RS409to420.d50 qz97 qz115 qz275) RS409to420.d60) rfl 

noncomputable def Ns408p1749 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz274 qz3 qz97 760048 1000 765286 1000 

noncomputable def Ns408p1750 := @Enclosure.norm_gt_of_isNear qz274 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 759500189377543214407 295147905179352825856 3479697829428540488989 

noncomputable def Ns408p1751 := @Ns408p1750 Ns408p626 274986237 5368709120 1213 5368709120 (Ns408p1745 (RS409to420.d4 qz97 qz115 qz275) RS409to420.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable def Ns408p1752 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz276 qz3 qz115 760048 1000 766594 1000 

noncomputable def Ns408p1753 := @Enclosure.norm_gt_of_isNear qz276 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 376773199373746121241 295147905179352825856 27233277308953644852473 

noncomputable def Ns408p1754 := @Ns408p1753 Ns408p743 274986237 5368709120 1213 5368709120 (Ns408p1747 (RS409to420.d50 qz97 qz115 qz275) RS409to420.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable abbrev qz277 := qz551

noncomputable def Ns408p1755 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz277 (@BSN.thirtyTwoPi_le_dec qz97 765286 1000 qz100 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz274 qz276 (Ns408p1746 rfl rfl) (Ns408p1748 rfl rfl)) (Ns408p1749 qz8 qz100 rfl rfl rfl rfl (Ns408p1751 rfl)) (Ns408p1752 qz8 qz118 rfl rfl rfl rfl (Ns408p1754 rfl)) 

noncomputable abbrev qz553 := (RS409to420.d3 qz636 qz644 (@Enclosure.dec_le_dec qz636 qz644 766594 1000 767901 1000 qz639 qz647 rfl rfl rfl))

noncomputable abbrev qz278 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns408p1756 := @Enclosure.Real.IsNear.of_eq qz278 (hardyZApproximantRS₀ qz115) Bool.false 376773199373746121241 295147905179352825856 27233277308953644852473 Ns408p743 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz636 qz644 766594 1000 767901 1000 qz639 qz647 rfl rfl rfl)

noncomputable abbrev qz279 := qz554

noncomputable def Ns408p1757 := @Enclosure.Real.IsNear.pos_val qz278 376773199373746121241 295147905179352825856 27233277308953644852473 Ns408p743 (Ns408p1756 (RS409to420.d4 qz115 qz133 qz279) RS409to420.d60) rfl 

noncomputable abbrev qz280 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns408p1758 := @Enclosure.Real.IsNear.of_eq qz280 (hardyZApproximantRS₀ qz133) Bool.true 1283190787772293089455 1180591620717411303424 21824668333820991239503 Ns408p863 

noncomputable def Ns408p1759 := @Enclosure.Real.IsNear.neg_val qz280 1283190787772293089455 1180591620717411303424 21824668333820991239503 Ns408p863 (Ns408p1758 (RS409to420.d50 qz115 qz133 qz279) RS409to420.d61) rfl 

noncomputable def Ns408p1760 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz278 qz3 qz115 760048 1000 766594 1000 

noncomputable def Ns408p1761 := @Enclosure.norm_gt_of_isNear qz278 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 376773199373746121241 295147905179352825856 27233277308953644852473 

noncomputable def Ns408p1762 := @Ns408p1761 Ns408p743 274986237 5368709120 1213 5368709120 (Ns408p1756 (RS409to420.d4 qz115 qz133 qz279) RS409to420.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable def Ns408p1763 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz280 qz3 qz133 760048 1000 767901 1000 

noncomputable def Ns408p1764 := @Enclosure.norm_gt_of_isNear qz280 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 1283190787772293089455 1180591620717411303424 21824668333820991239503 

noncomputable def Ns408p1765 := @Ns408p1764 Ns408p863 274986237 5368709120 1213 5368709120 (Ns408p1758 (RS409to420.d50 qz115 qz133 qz279) RS409to420.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable abbrev qz281 := qz553

noncomputable def Ns408p1766 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz281 (@BSN.thirtyTwoPi_le_dec qz115 766594 1000 qz118 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz278 qz280 (Ns408p1757 rfl rfl) (Ns408p1759 rfl rfl)) (Ns408p1760 qz8 qz118 rfl rfl rfl rfl (Ns408p1762 rfl)) (Ns408p1763 qz8 qz136 rfl rfl rfl rfl (Ns408p1765 rfl)) 

noncomputable abbrev qz555 := (RS409to420.d3 qz644 qz653 (@Enclosure.dec_le_dec qz644 qz653 767901 1000 769208 1000 qz647 qz656 rfl rfl rfl))

noncomputable abbrev qz282 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns408p1767 := @Enclosure.Real.IsNear.of_eq qz282 (hardyZApproximantRS₀ qz133) Bool.true 1283190787772293089455 1180591620717411303424 21824668333820991239503 Ns408p863 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz644 qz653 767901 1000 769208 1000 qz647 qz656 rfl rfl rfl)

noncomputable abbrev qz283 := qz556

noncomputable def Ns408p1768 := @Enclosure.Real.IsNear.neg_val qz282 1283190787772293089455 1180591620717411303424 21824668333820991239503 Ns408p863 (Ns408p1767 (RS409to420.d4 qz133 qz151 qz283) RS409to420.d61) rfl 

noncomputable abbrev qz284 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns408p1769 := @Enclosure.Real.IsNear.of_eq qz284 (hardyZApproximantRS₀ qz151) Bool.false 20792841286132044222463 9444732965739290427392 174909184304512471423047 Ns408p980 

noncomputable def Ns408p1770 := @Enclosure.Real.IsNear.pos_val qz284 20792841286132044222463 9444732965739290427392 174909184304512471423047 Ns408p980 (Ns408p1769 (RS409to420.d50 qz133 qz151 qz283) RS409to420.d62) rfl 

noncomputable def Ns408p1771 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz282 qz3 qz133 760048 1000 767901 1000 

noncomputable def Ns408p1772 := @Enclosure.norm_gt_of_isNear qz282 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 1283190787772293089455 1180591620717411303424 21824668333820991239503 

noncomputable def Ns408p1773 := @Ns408p1772 Ns408p863 274986237 5368709120 1213 5368709120 (Ns408p1767 (RS409to420.d4 qz133 qz151 qz283) RS409to420.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable def Ns408p1774 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz284 qz3 qz151 760048 1000 769208 1000 

noncomputable def Ns408p1775 := @Enclosure.norm_gt_of_isNear qz284 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 20792841286132044222463 9444732965739290427392 174909184304512471423047 

noncomputable def Ns408p1776 := @Ns408p1775 Ns408p980 274986237 5368709120 1213 5368709120 (Ns408p1769 (RS409to420.d50 qz133 qz151 qz283) RS409to420.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable abbrev qz285 := qz555

noncomputable def Ns408p1777 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz285 (@BSN.thirtyTwoPi_le_dec qz133 767901 1000 qz136 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz282 qz284 (Ns408p1768 rfl rfl) (Ns408p1770 rfl rfl)) (Ns408p1771 qz8 qz136 rfl rfl rfl rfl (Ns408p1773 rfl)) (Ns408p1774 qz8 qz154 rfl rfl rfl rfl (Ns408p1776 rfl)) 

noncomputable abbrev qz557 := (RS409to420.d3 qz653 qz661 (@Enclosure.dec_le_dec qz653 qz661 769208 1000 770515 1000 qz656 qz664 rfl rfl rfl))

noncomputable abbrev qz286 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns408p1778 := @Enclosure.Real.IsNear.of_eq qz286 (hardyZApproximantRS₀ qz151) Bool.false 20792841286132044222463 9444732965739290427392 174909184304512471423047 Ns408p980 

noncomputable abbrev qz558 := (@Enclosure.dec_le_dec qz653 qz661 769208 1000 770515 1000 qz656 qz664 rfl rfl rfl)

noncomputable abbrev qz287 := qz558

noncomputable def Ns408p1779 := @Enclosure.Real.IsNear.pos_val qz286 20792841286132044222463 9444732965739290427392 174909184304512471423047 Ns408p980 (Ns408p1778 (RS409to420.d4 qz151 qz169 qz287) RS409to420.d62) rfl 

noncomputable abbrev qz288 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns408p1780 := @Enclosure.Real.IsNear.of_eq qz288 (hardyZApproximantRS₀ qz169) Bool.true 13998550142635918240129 4722366482869645213696 438046559476308333509509 Ns408p1101 

noncomputable def Ns408p1781 := @Enclosure.Real.IsNear.neg_val qz288 13998550142635918240129 4722366482869645213696 438046559476308333509509 Ns408p1101 (Ns408p1780 (RS409to420.d50 qz151 qz169 qz287) RS409to420.d63) rfl 

noncomputable def Ns408p1782 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz286 qz3 qz151 760048 1000 769208 1000 

noncomputable def Ns408p1783 := @Enclosure.norm_gt_of_isNear qz286 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 20792841286132044222463 9444732965739290427392 174909184304512471423047 

noncomputable def Ns408p1784 := @Ns408p1783 Ns408p980 274986237 5368709120 1213 5368709120 (Ns408p1778 (RS409to420.d4 qz151 qz169 qz287) RS409to420.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable def Ns408p1785 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz288 qz3 qz169 760048 1000 770515 1000 

noncomputable def Ns408p1786 := @Enclosure.norm_gt_of_isNear qz288 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 13998550142635918240129 4722366482869645213696 438046559476308333509509 

noncomputable def Ns408p1787 := @Ns408p1786 Ns408p1101 274986237 5368709120 1213 5368709120 (Ns408p1780 (RS409to420.d50 qz151 qz169 qz287) RS409to420.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable abbrev qz289 := qz557

noncomputable def Ns408p1788 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz289 (@BSN.thirtyTwoPi_le_dec qz151 769208 1000 qz154 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz286 qz288 (Ns408p1779 rfl rfl) (Ns408p1781 rfl rfl)) (Ns408p1782 qz8 qz154 rfl rfl rfl rfl (Ns408p1784 rfl)) (Ns408p1785 qz8 qz172 rfl rfl rfl rfl (Ns408p1787 rfl)) 

noncomputable abbrev qz707 := (@Enclosure.dec_le_dec qz752 qz756 770515 1000 771821 1000 (@Eq.refl Real qz752) (@Eq.refl Real qz756) rfl rfl rfl)

noncomputable abbrev qz559 := (RS409to420.d3 qz661 qz669 qz707)

noncomputable abbrev qz290 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns408p1789 := @Enclosure.Real.IsNear.of_eq qz290 (hardyZApproximantRS₀ qz169) Bool.true 13998550142635918240129 4722366482869645213696 438046559476308333509509 Ns408p1101 

noncomputable abbrev qz560 := qz707

noncomputable abbrev qz291 := qz560

noncomputable def Ns408p1790 := @Enclosure.Real.IsNear.neg_val qz290 13998550142635918240129 4722366482869645213696 438046559476308333509509 Ns408p1101 (Ns408p1789 (RS409to420.d4 qz169 qz187 qz291) RS409to420.d63) rfl 

noncomputable abbrev qz292 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns408p1791 := @Enclosure.Real.IsNear.of_eq qz292 (hardyZApproximantRS₀ qz187) Bool.false 5629341808986673802395 1180591620717411303424 1097098579087911636324429 Ns408p1224 

noncomputable def Ns408p1792 := @Enclosure.Real.IsNear.pos_val qz292 5629341808986673802395 1180591620717411303424 1097098579087911636324429 Ns408p1224 (Ns408p1791 (RS409to420.d50 qz169 qz187 qz291) RS409to420.d64) rfl 

noncomputable def Ns408p1793 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz290 qz3 qz169 760048 1000 770515 1000 

noncomputable def Ns408p1794 := @Enclosure.norm_gt_of_isNear qz290 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 13998550142635918240129 4722366482869645213696 438046559476308333509509 

noncomputable def Ns408p1795 := @Ns408p1794 Ns408p1101 274986237 5368709120 1213 5368709120 (Ns408p1789 (RS409to420.d4 qz169 qz187 qz291) RS409to420.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable def Ns408p1796 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz292 qz3 qz187 760048 1000 771821 1000 

noncomputable def Ns408p1797 := @Enclosure.norm_gt_of_isNear qz292 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 5629341808986673802395 1180591620717411303424 1097098579087911636324429 

noncomputable def Ns408p1798 := @Ns408p1797 Ns408p1224 274986237 5368709120 1213 5368709120 (Ns408p1791 (RS409to420.d50 qz169 qz187 qz291) RS409to420.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable abbrev qz293 := qz559

noncomputable def Ns408p1799 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz293 (@BSN.thirtyTwoPi_le_dec qz169 770515 1000 qz172 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz290 qz292 (Ns408p1790 rfl rfl) (Ns408p1792 rfl rfl)) (Ns408p1793 qz8 qz172 rfl rfl rfl rfl (Ns408p1795 rfl)) (Ns408p1796 qz8 qz190 rfl rfl rfl rfl (Ns408p1798 rfl)) 

noncomputable abbrev qz708 := (@Enclosure.dec_le_dec qz756 qz760 771821 1000 773127 1000 (@Eq.refl Real qz756) qz763 rfl rfl rfl)

noncomputable abbrev qz561 := (RS409to420.d3 qz669 qz677 qz708)

noncomputable abbrev qz294 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns408p1800 := @Enclosure.Real.IsNear.of_eq qz294 (hardyZApproximantRS₀ qz187) Bool.false 5629341808986673802395 1180591620717411303424 1097098579087911636324429 Ns408p1224 

noncomputable abbrev qz562 := qz708

noncomputable abbrev qz295 := qz562

noncomputable def Ns408p1801 := @Enclosure.Real.IsNear.pos_val qz294 5629341808986673802395 1180591620717411303424 1097098579087911636324429 Ns408p1224 (Ns408p1800 (RS409to420.d4 qz187 qz205 qz295) RS409to420.d64) rfl 

noncomputable abbrev qz296 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns408p1802 := @Enclosure.Real.IsNear.of_eq qz296 (hardyZApproximantRS₀ qz205) Bool.true 1735207492094367526279 2361183241434822606848 Ns408p1345 Ns408p75 

noncomputable def Ns408p1803 := @Enclosure.Real.IsNear.neg_val qz296 1735207492094367526279 2361183241434822606848 Ns408p1345 Ns408p75 (Ns408p1802 (RS409to420.d50 qz187 qz205 qz295) RS409to420.d65) rfl 

noncomputable def Ns408p1804 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz294 qz3 qz187 760048 1000 771821 1000 

noncomputable def Ns408p1805 := @Enclosure.norm_gt_of_isNear qz294 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 5629341808986673802395 1180591620717411303424 1097098579087911636324429 

noncomputable def Ns408p1806 := @Ns408p1805 Ns408p1224 274986237 5368709120 1213 5368709120 (Ns408p1800 (RS409to420.d4 qz187 qz205 qz295) RS409to420.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable def Ns408p1807 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz296 qz3 qz205 760048 1000 773127 1000 

noncomputable def Ns408p1808 := @Enclosure.norm_gt_of_isNear qz296 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 1735207492094367526279 2361183241434822606848 Ns408p1345 

noncomputable def Ns408p1809 := @Ns408p1808 Ns408p75 274986237 5368709120 1213 5368709120 (Ns408p1802 (RS409to420.d50 qz187 qz205 qz295) RS409to420.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable abbrev qz297 := qz561

noncomputable def Ns408p1810 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz297 (@BSN.thirtyTwoPi_le_dec qz187 771821 1000 qz190 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz294 qz296 (Ns408p1801 rfl rfl) (Ns408p1803 rfl rfl)) (Ns408p1804 qz8 qz190 rfl rfl rfl rfl (Ns408p1806 rfl)) (Ns408p1807 qz8 qz210 rfl rfl rfl rfl (Ns408p1809 rfl)) 

noncomputable abbrev qz709 := (@Enclosure.dec_le_dec qz760 qz765 773127 1000 774433 1000 qz763 qz768 rfl rfl rfl)

noncomputable abbrev qz563 := (RS409to420.d3 qz677 qz687 qz709)

noncomputable abbrev qz298 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns408p1811 := @Enclosure.Real.IsNear.of_eq qz298 (hardyZApproximantRS₀ qz205) Bool.true 1735207492094367526279 2361183241434822606848 Ns408p1345 Ns408p75 

noncomputable abbrev qz564 := qz709

noncomputable abbrev qz299 := qz564

noncomputable def Ns408p1812 := @Enclosure.Real.IsNear.neg_val qz298 1735207492094367526279 2361183241434822606848 Ns408p1345 Ns408p75 (Ns408p1811 (RS409to420.d4 qz205 qz224 qz299) RS409to420.d65) rfl 

noncomputable abbrev qz300 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns408p1813 := @Enclosure.Real.IsNear.of_eq qz300 (hardyZApproximantRS₀ qz224) Bool.false 5348857864470654917157 9444732965739290427392 Ns408p1467 Ns408p1468 

noncomputable def Ns408p1814 := @Enclosure.Real.IsNear.pos_val qz300 5348857864470654917157 9444732965739290427392 Ns408p1467 Ns408p1468 (Ns408p1813 (RS409to420.d50 qz205 qz224 qz299) RS409to420.d66) rfl 

noncomputable def Ns408p1815 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz298 qz3 qz205 760048 1000 773127 1000 

noncomputable def Ns408p1816 := @Enclosure.norm_gt_of_isNear qz298 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 1735207492094367526279 2361183241434822606848 Ns408p1345 

noncomputable def Ns408p1817 := @Ns408p1816 Ns408p75 274986237 5368709120 1213 5368709120 (Ns408p1811 (RS409to420.d4 qz205 qz224 qz299) RS409to420.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable def Ns408p1818 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz300 qz3 qz224 760048 1000 774433 1000 

noncomputable def Ns408p1819 := @Enclosure.norm_gt_of_isNear qz300 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 5348857864470654917157 9444732965739290427392 Ns408p1467 

noncomputable def Ns408p1820 := @Ns408p1819 Ns408p1468 274986237 5368709120 1213 5368709120 (Ns408p1813 (RS409to420.d50 qz205 qz224 qz299) RS409to420.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable abbrev qz301 := qz563

noncomputable def Ns408p1821 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz301 (@BSN.thirtyTwoPi_le_dec qz205 773127 1000 qz210 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz298 qz300 (Ns408p1812 rfl rfl) (Ns408p1814 rfl rfl)) (Ns408p1815 qz8 qz210 rfl rfl rfl rfl (Ns408p1817 rfl)) (Ns408p1818 qz8 qz227 rfl rfl rfl rfl (Ns408p1820 rfl)) 

noncomputable abbrev qz775 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 774433 1000) (Enclosure.sfrac Bool.false 775738 1000) 774433 1000 775738 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 774433 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 775738 1000)) rfl rfl rfl)

noncomputable abbrev qz710 := qz775

noncomputable abbrev qz565 := (RS409to420.d3 qz687 qz697 qz710)

noncomputable abbrev qz302 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz565)

noncomputable def Ns408p1822 := @Enclosure.Real.IsNear.of_eq qz302 (hardyZApproximantRS₀ qz224) Bool.false 5348857864470654917157 9444732965739290427392 Ns408p1467 Ns408p1468 

noncomputable abbrev qz566 := qz710

noncomputable abbrev qz303 := qz566

noncomputable def Ns408p1823 := @Enclosure.Real.IsNear.pos_val qz302 5348857864470654917157 9444732965739290427392 Ns408p1467 Ns408p1468 (Ns408p1822 (RS409to420.d4 qz224 qz241 qz303) RS409to420.d66) rfl 

noncomputable abbrev qz304 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz565)

noncomputable def Ns408p1824 := @Enclosure.Real.IsNear.of_eq qz304 (hardyZApproximantRS₀ qz241) Bool.true 1327976716102205219425 2361183241434822606848 Ns408p1586 Ns408p75 

noncomputable def Ns408p1825 := @Enclosure.Real.IsNear.neg_val qz304 1327976716102205219425 2361183241434822606848 Ns408p1586 Ns408p75 (Ns408p1824 (RS409to420.d50 qz224 qz241 qz303) RS409to420.d67) rfl 

noncomputable def Ns408p1826 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz302 qz3 qz224 760048 1000 774433 1000 

noncomputable def Ns408p1827 := @Enclosure.norm_gt_of_isNear qz302 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 5348857864470654917157 9444732965739290427392 Ns408p1467 

noncomputable def Ns408p1828 := @Ns408p1827 Ns408p1468 274986237 5368709120 1213 5368709120 (Ns408p1822 (RS409to420.d4 qz224 qz241 qz303) RS409to420.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable def Ns408p1829 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz304 qz3 qz241 760048 1000 775738 1000 

noncomputable def Ns408p1830 := @Enclosure.norm_gt_of_isNear qz304 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 1327976716102205219425 2361183241434822606848 Ns408p1586 

noncomputable def Ns408p1831 := @Ns408p1830 Ns408p75 274986237 5368709120 1213 5368709120 (Ns408p1824 (RS409to420.d50 qz224 qz241 qz303) RS409to420.d67) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 274986237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS409to420.d56) rfl rfl rfl rfl 

noncomputable abbrev qz305 := qz565

noncomputable def Ns408p1832 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz305 (@BSN.thirtyTwoPi_le_dec qz224 774433 1000 qz227 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz302 qz304 (Ns408p1823 rfl rfl) (Ns408p1825 rfl rfl)) (Ns408p1826 qz8 qz227 rfl rfl rfl rfl (Ns408p1828 rfl)) (Ns408p1829 qz8 qz244 rfl rfl rfl rfl (Ns408p1831 rfl)) 

noncomputable def Ns408p1833 := @List.cons RS409to420.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz301 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz301) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz301) Ns408p1821)) (@List.cons RS409to420.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz305 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz305) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz305) Ns408p1832)) (@List.nil RS409to420.d0)) 

noncomputable def Ns408p1834 := @List.cons RS409to420.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz293 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz293) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz293) Ns408p1799)) (@List.cons RS409to420.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz297 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz297) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz297) Ns408p1810)) Ns408p1833) 

noncomputable def Ns408p1835 := @List.cons RS409to420.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz285 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz285) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz285) Ns408p1777)) (@List.cons RS409to420.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz289 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz289) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz289) Ns408p1788)) Ns408p1834) 

noncomputable def Ns408p1836 := @List.cons RS409to420.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz277 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz277) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz277) Ns408p1755)) (@List.cons RS409to420.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz281 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz281) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz281) Ns408p1766)) Ns408p1835) 

noncomputable def Ns408p1837 := @List.cons RS409to420.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz269 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz269) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz269) Ns408p1733)) (@List.cons RS409to420.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz273 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz273) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz273) Ns408p1744)) Ns408p1836) 

noncomputable def Ns408p1838 := @List.cons RS409to420.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz261 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz261) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz261) Ns408p1711)) (@List.cons RS409to420.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz265 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz265) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz265) Ns408p1722)) Ns408p1837) 

noncomputable abbrev qz567 := (RS409to420.d2 qz661 qz669 qz707)

noncomputable abbrev qz711 := (RS409to420.d2 qz760 qz765 (@Enclosure.dec_le_dec qz760 qz765 773127 1000 774433 1000 qz763 qz768 rfl rfl rfl))

noncomputable abbrev qz712 := (@List.cons RS409to420.d1 (RS409to420.d2 qz765 qz770 qz775) (@List.nil RS409to420.d1))

noncomputable abbrev qz568 := (@List.cons RS409to420.d1 (RS409to420.d2 qz669 qz677 qz708) (@List.cons RS409to420.d1 qz711 qz712))

noncomputable abbrev qz306 := (@List.cons RS409to420.d1 (RS409to420.d2 qz471 qz483 qz558) (@List.cons RS409to420.d1 qz567 qz568))

noncomputable def Ns408p1839 := @List.cons RS409to420.d1 (RS409to420.d2 qz115 qz133 qz279) (@List.cons RS409to420.d1 (RS409to420.d2 qz133 qz151 qz283) qz306) 

noncomputable abbrev qz307 := (RS409to420.d2 qz435 qz447 qz552)

noncomputable def Ns408p1840 := @List.IsChain.cons_cons RS409to420.d1 RS409to420.d68 qz307 (RS409to420.d2 qz115 qz133 qz279) (@List.cons RS409to420.d1 (RS409to420.d2 qz133 qz151 qz283) qz306) 

noncomputable def Ns408p1841 := @List.IsChain.cons_cons RS409to420.d1 RS409to420.d68 (RS409to420.d2 qz115 qz133 qz279) (RS409to420.d2 qz133 qz151 qz283) qz306 (@Enclosure.dec_le_dec qz133 qz133 767901 1000 767901 1000 qz136 qz136 rfl rfl rfl) 

noncomputable abbrev qz308 := (RS409to420.d2 qz471 qz483 qz558)

noncomputable abbrev qz309 := qz567

noncomputable abbrev qz310 := qz568

noncomputable abbrev qz569 := (RS409to420.d2 qz669 qz677 qz708)

noncomputable abbrev qz311 := qz569

noncomputable abbrev qz570 := (@List.cons RS409to420.d1 qz711 qz712)

noncomputable abbrev qz312 := qz570

noncomputable abbrev qz571 := qz711

noncomputable abbrev qz313 := qz571

noncomputable abbrev qz572 := qz712

noncomputable abbrev qz314 := qz572

noncomputable abbrev qz713 := (RS409to420.d2 qz765 qz770 qz775)

noncomputable abbrev qz573 := qz713

noncomputable abbrev qz315 := qz573

noncomputable def Ns408p1842 := @List.IsChain.cons_cons RS409to420.d1 RS409to420.d68 qz308 qz309 qz310 (@Enclosure.dec_le_dec qz169 qz169 770515 1000 770515 1000 qz172 qz172 rfl rfl rfl) (@List.IsChain.cons_cons RS409to420.d1 RS409to420.d68 qz309 qz311 qz312 (@Enclosure.dec_le_dec qz187 qz187 771821 1000 771821 1000 qz190 qz190 rfl rfl rfl) (@List.IsChain.cons_cons RS409to420.d1 RS409to420.d68 qz311 qz313 qz314 (@Enclosure.dec_le_dec qz205 qz205 773127 1000 773127 1000 qz210 qz210 rfl rfl rfl) (@List.IsChain.cons_cons RS409to420.d1 RS409to420.d68 qz313 qz315 (@List.nil RS409to420.d1) (@Enclosure.dec_le_dec qz224 qz224 774433 1000 774433 1000 qz227 qz227 rfl rfl rfl) (@List.IsChain.singleton RS409to420.d1 RS409to420.d68 qz315)))) 

noncomputable abbrev qz316 := (@List.cons RS409to420.d1 qz567 qz568)

noncomputable def Ns408p1843 := @List.IsChain.cons_cons RS409to420.d1 RS409to420.d68 (RS409to420.d2 qz133 qz151 qz283) qz308 qz316 (@Enclosure.dec_le_dec qz151 qz151 769208 1000 769208 1000 qz154 qz154 rfl rfl rfl) Ns408p1842 

noncomputable def Ns408p1844 := @List.IsChain.cons_cons RS409to420.d1 RS409to420.d68 (RS409to420.d2 qz3 qz32 qz259) (RS409to420.d2 qz32 qz61 qz263) (@List.cons RS409to420.d1 (RS409to420.d2 qz61 qz79 qz267) (@List.cons RS409to420.d1 (RS409to420.d2 qz79 qz97 qz271) (@List.cons RS409to420.d1 qz307 Ns408p1839))) (@Enclosure.dec_le_dec qz32 qz32 762013 1000 762013 1000 qz36 qz36 rfl rfl rfl) (@List.IsChain.cons_cons RS409to420.d1 RS409to420.d68 (RS409to420.d2 qz32 qz61 qz263) (RS409to420.d2 qz61 qz79 qz267) (@List.cons RS409to420.d1 (RS409to420.d2 qz79 qz97 qz271) (@List.cons RS409to420.d1 qz307 Ns408p1839)) (@Enclosure.dec_le_dec qz61 qz61 763159 1000 763159 1000 qz64 qz64 rfl rfl rfl) (@List.IsChain.cons_cons RS409to420.d1 RS409to420.d68 (RS409to420.d2 qz61 qz79 qz267) (RS409to420.d2 qz79 qz97 qz271) (@List.cons RS409to420.d1 qz307 Ns408p1839) (@Enclosure.dec_le_dec qz79 qz79 763813 1000 763813 1000 qz82 qz82 rfl rfl rfl) (@List.IsChain.cons_cons RS409to420.d1 RS409to420.d68 (RS409to420.d2 qz79 qz97 qz271) qz307 Ns408p1839 (@Enclosure.dec_le_dec qz97 qz97 765286 1000 765286 1000 qz100 qz100 rfl rfl rfl) (Ns408p1840 (@Enclosure.dec_le_dec qz115 qz115 766594 1000 766594 1000 qz118 qz118 rfl rfl rfl) (Ns408p1841 Ns408p1843))))) 

noncomputable abbrev qz574 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz575 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns408p1838 Ns408p1844)

noncomputable abbrev qz576 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns408p1838 Ns408p1844))

theorem RS409to420.d69 : Zeta.Certificates.BatchSpec 12 760048 1000 775738 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz3)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz241)))) qz575 (@And.intro (@Eq Nat (@List.length qz574 qz576) 12) (And (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 qz576)) (@Option.some Real qz3)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 qz576)) (@Option.some Real qz241))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 qz576)) (@Option.some Real qz3)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 qz576)) (@Option.some Real qz241)) (@Eq.refl (Option Real) (@Option.some Real qz3)) (@Eq.refl (Option Real) (@Option.some Real qz241))))

theorem solution : Zeta.Certificates.BatchSpec 12 760048 1000 775738 1000 := RS409to420.d69
#print axioms solution
#check solution
