-- Prove2me | solution 1 for RHHeight1000.rs_main_0397_0408
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:20:59.039047+00:00
-- url     : https://prove2.me/submissions/88177ea6-b5ec-4a5a-89cd-165be561449f

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

noncomputable def RS397to408.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS397to408.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS397to408.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS397to408.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS397to408.d2 a b h 

theorem RS397to408.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS397to408.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS397to408.d3 a b h)) 

noncomputable def Ns396p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns396p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns396p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns396p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns396p0 Ns396p1 Ns396p2 Ns396p1 307286088 268435456 1 100000000 307286088 268435456 1 100000000 153643044 134217728 2 134217728 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns396p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns396p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns396p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns396p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns396p8 := nat_lit 6573389678388862351155759458724141871788046104702795740939545775355827438482086890337971184306503456724674701876007739166027855002689342487126242201873902293161938510715598861337724155978462934346539722102807352693564004597780440630880721700532830491857281958381906437104026277614553345439647264822859384496062743250358046048880947907642984145065307980413206151384068885350206914057384338280179177725692904928360597982006748935836093248417685721122261418062303135764477585928239149568275027355236134745000697766005167655784166499502223346815249842007858448160935771607172549259242715110048115445292136446613946552506617916138661398090061483392335970316672263498462800198746102072055363920390651513279180731193678641632192805423820381724597815072905552156968003637925334143020171520625 

noncomputable def Ns396p9 := nat_lit 702614123509571190207434367497643053726389003684617183996726348470791223755418688598787599501240412886827946200799073391711533512528899996899108221816773619593298708861540359234024488137706935294538610329535191474811214152768697527793266408685885408431698677504366547635987768499962038530066773279961750661013789994039311989768445302208965109624014234440840481147386361324656837522786906307734587964680180646868573806366973424595907336814393861048013934514934272026683624090151873353554279683010347128413433843775162422864773798490322287367830744467164676975854073090397461536167654230134598982106570951920409048997311342333559851528447946435833392322432321465286801524775001800171249769824525762984779161997185015423416919065587459911326773695449510414365759468097615398764501522575 

noncomputable def Ns396p10 := nat_lit 541392566138474909591412279139378993255101875047003589935782329109463644892392322173295519240510467068363239080443023466297029982601757003829684821059136286585994161974307047499333049696728682047261006046816072264069316416942594393775486731411634963656291648112663555457379375292741727868294229136381639619442405391741167595634732196900940186574903289828257139713673376723681752760045249773972946001592268830432998579610986951410273979009689762628244990479410235165324966379611071762421902787196495466840333515349387051622842182127210560393625584510287605139387730811840242457253978115925211125629993337408355023684205061830608267784338105681114876710224147942516826039256450164994945245879666660679160980454641866547806615379410050641833332584350523565507268843323231339375 

noncomputable def Ns396p11 := BSN.log_dyadic_bound Ns396p6 Ns396p7 16 15 Ns396p8 268435456 100000000 Ns396p9 Ns396p10 307286088 Ns396p4 Ns396p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns396p6) (BSN.artanhQ Ns396p7) 0 15 Ns396p9 Ns396p8 Ns396p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns396p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns396p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns396p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns396p15 := nat_lit 6573389678388957581038003304946500209472262679236338533996718496177406624059139082449994147026037314666926693076053053862592074936423388863596813530408382584499373597031431853921413941298322255656576695489433951602693567143885654771592106690789036275646003378131729522606930818530515414843848039000889531334935427389830473690579523667466182538201372727149023132371319359578146651783732835416323469915494090659780509855937937675396353734377829186029766969614606089327824892671842834136516654569045504808111725705550748907924941183733134599012581542910476929082687043869700761244349471219210833189555347464155979117619898077496880661665775336657207488512148128426326823595335945176245554694022845325705851563290369414226074229552025260849280553835909109839168582914725334143020171520625 

noncomputable def Ns396p16 := nat_lit 702614123509582134195699383225799303120857312948289364169564431944606347230839067212220070086773571232938822231607515388838247088164426860334641427891924556959013106220289292017417932077264689683982462259236603120411894481357554273197237433243865910367073588753830073256225145709268648257922640132615276470163987114280905050307903018021985933333474523803420109333064989110261463867307642914581311357336787925252212965840242792007601256472655504246146516404729632839909377990937267835233434162343951883521915890115762575574377037535717851480622294463860980162526686236248764915916362237196611189536095144270945605478817014333998082847306947436470576941659846222535334992451365706225994338058508887942119777908276510373758951874822816373072605980596581754554466975502415398764501522575 

noncomputable def Ns396p17 := nat_lit 541392566138490077533790984620311058177654278555980714203107761719673916425133183846751239616284470803704371181920004286935467360846628369375164068764590875438310007353955324186636582299553928814156491749519256774653872128089233575343481607925575468185460509172779152955629338248076232826253005811067688706928164570779608774451502836676056177667078421728722179008027603013170304530594440809888606240685402729798990208830923560422594844623819537735750113690675240496626214395332044296593456069970973486809806367897564108502902289348063943342100923856630472249952347312756547637419241376870243223562839253667975765230153074010838184467350558565952691487980795548332122966513692688198426849374346091985539852378055886379210372820263137502377721028428076000707268843323231339375 

noncomputable def Ns396p18 := BSN.log_dyadic_bound Ns396p13 Ns396p14 16 15 Ns396p15 268435456 100000000 Ns396p16 Ns396p17 307286088 Ns396p12 Ns396p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns396p13) (BSN.artanhQ Ns396p14) 0 15 Ns396p16 Ns396p15 Ns396p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns396p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 153643044 134217728 2 134217728 38410761 33554432 1 67108864 (Ns396p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns396p0 Ns396p1 307286088 268435456 1 100000000 Bool.false (BSN.logfrac_isNear Ns396p4 Ns396p5 1 Ns396p0 Ns396p1 307286088 268435456 100000000 rfl rfl rfl (Ns396p11 rfl))) (BSN.isNear_log_sfrac Ns396p2 Ns396p1 307286088 268435456 1 100000000 Bool.false (BSN.logfrac_isNear Ns396p12 Ns396p5 1 Ns396p2 Ns396p1 307286088 268435456 100000000 rfl rfl rfl (Ns396p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS397to408.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 67108864 := Ns396p19 

noncomputable def Ns396p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 16777216 6250000 385100712855 135135 11629079 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz316

theorem RS397to408.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 11629079 16777216 1 6250000 := BSN.isNear_log_sfrac 2 1 11629079 16777216 1 6250000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 11629079 16777216 6250000 rfl rfl rfl (Ns396p20 rfl)) 

theorem RS397to408.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 186065264 268435456 43 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 11629079 16777216 1 6250000 186065264 268435456 43 268435456 RS397to408.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz577 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz577

noncomputable def Ns396p21 := @Enclosure.Real.IsNear.inv_image qz317 47453133 33554432 1 33554432 11863282 11863284 16777216 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 47453133 33554432 1 33554432 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 47453133 33554432 1 33554432 47453133 33554432 1 33554432 (BSN.sqrt_enclosure 2 1 23726566 23726567 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS397to408.d8 : Enclosure.Real.IsNear qz320 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 23726566 33554432 2 33554432 11863283 16777216 1 16777216 (Ns396p21 rfl rfl) rfl 

theorem RS397to408.d9 : Enclosure.Real.IsNear qz320 Bool.false 189812528 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 189812528 268435456 16 268435456 RS397to408.d8 rfl 

noncomputable def Ns396p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 16777216 6250000 13079757671720842725 316234143225 18431655 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS397to408.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 6250000 := BSN.isNear_log_sfrac 3 1 18431655 16777216 1 6250000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 18431655 16777216 6250000 rfl rfl rfl (Ns396p22 rfl)) 

theorem RS397to408.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 294906480 268435456 43 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 6250000 294906480 268435456 43 268435456 RS397to408.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns396p23 := @Enclosure.Real.IsNear.inv_image qz321 58117981 33554432 1 33554432 9686330 9686331 16777216 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 58117981 33554432 1 33554432 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 58117981 33554432 1 33554432 58117981 33554432 1 33554432 (BSN.sqrt_enclosure 3 1 29058990 29058991 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS397to408.d12 : Enclosure.Real.IsNear qz323 Bool.false 19372661 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 19372661 33554432 1 33554432 19372661 33554432 1 33554432 (Ns396p23 rfl rfl) rfl 

theorem RS397to408.d13 : Enclosure.Real.IsNear qz323 Bool.false 154981288 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 19372661 33554432 1 33554432 154981288 268435456 8 268435456 RS397to408.d12 rfl 

noncomputable def Ns396p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns396p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns396p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns396p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns396p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns396p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns396p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns396p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns396p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns396p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns396p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns396p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns396p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns396p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns396p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns396p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns396p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns396p25 Ns396p26 Ns396p27 Ns396p28 200200021673987500790625 Ns396p29 Ns396p30 Ns396p31 Ns396p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns396p32 Ns396p33 151412625 Ns396p34 Ns396p35 1322214852783825 Ns396p27 Ns396p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns396p32 Ns396p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns396p34 Ns396p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns396p36 Ns396p37 1267389585 Ns396p38 Ns396p39 1927077560082675 Ns396p29 Ns396p30 Ns396p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns396p36 Ns396p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns396p38 Ns396p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS397to408.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns396p24 Ns396p25 1 Ns396p26 := Ns396p40 rfl rfl rfl 

noncomputable def Ns396p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns396p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns396p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns396p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns396p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns396p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns396p25 Ns396p26 Ns396p42 Ns396p43 9945 Ns396p44 Ns396p45 65835 Ns396p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns396p42 Ns396p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns396p44 Ns396p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS397to408.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns396p41 Ns396p25 1 Ns396p26 := Ns396p46 rfl 

noncomputable def Ns396p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns396p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS397to408.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns396p47 Ns396p25 1 Ns396p48 := BSN.pi_combine Ns396p24 Ns396p41 Ns396p25 Ns396p26 Ns396p48 Ns396p47 rfl rfl rfl rfl RS397to408.d14 RS397to408.d15 

theorem RS397to408.d17 : Enclosure.Real.IsNear Real.pi Bool.false 14148475504056880 4503599627370496 1 4503599627370496 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns396p47 Ns396p25 1 Ns396p48 14148475504056880 4503599627370496 1 4503599627370496 RS397to408.d16 rfl 

noncomputable def Ns396p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns396p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns396p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns396p52 := BSN.log_dyadic_bound 3 5 17 16 Ns396p49 16777216 6250000 Ns396p50 Ns396p51 23258159 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns396p50 Ns396p49 Ns396p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS397to408.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 6250000 := BSN.isNear_log_sfrac 4 1 23258159 16777216 1 6250000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 23258159 16777216 6250000 rfl rfl rfl (Ns396p52 rfl)) 

theorem RS397to408.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 372130544 268435456 43 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 6250000 372130544 268435456 43 268435456 RS397to408.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns396p53 := @Enclosure.Real.IsNear.inv_image qz325 67108865 33554432 1 33554432 8388607 8388608 16777216 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 67108865 33554432 1 33554432 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 67108865 33554432 1 33554432 67108865 33554432 1 33554432 (BSN.sqrt_enclosure 4 1 33554432 33554433 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS397to408.d20 : Enclosure.Real.IsNear qz327 Bool.false 16777215 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 16777215 33554432 1 33554432 16777215 33554432 1 33554432 (Ns396p53 rfl rfl) rfl 

theorem RS397to408.d21 : Enclosure.Real.IsNear qz327 Bool.false 134217720 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 16777215 33554432 1 33554432 134217720 268435456 8 268435456 RS397to408.d20 rfl 

noncomputable def Ns396p54 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns396p55 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns396p56 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns396p57 := nat_lit 885951608314392539099884620 

noncomputable def Ns396p58 := nat_lit 1286943652057122751813246125 

noncomputable def Ns396p59 := BSN.log_dyadic_bound 2 3 22 21 Ns396p54 16777216 6250000 Ns396p55 Ns396p56 27001887 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns396p57 Ns396p58 84004523356416638976000 Ns396p55 Ns396p54 Ns396p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns396p57 Ns396p58 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS397to408.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 6250000 := BSN.isNear_log_sfrac 5 1 27001887 16777216 1 6250000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 27001887 16777216 6250000 rfl rfl rfl (Ns396p59 rfl rfl)) 

theorem RS397to408.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 432030192 268435456 43 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 6250000 432030192 268435456 43 268435456 RS397to408.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns396p60 := @Enclosure.Real.IsNear.inv_image qz328 75029991 33554432 1 33554432 7502998 7503000 16777216 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 75029991 33554432 1 33554432 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 75029991 33554432 1 33554432 75029991 33554432 1 33554432 (BSN.sqrt_enclosure 5 1 37514995 37514996 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS397to408.d24 : Enclosure.Real.IsNear qz329 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 15005998 33554432 2 33554432 7502999 16777216 1 16777216 (Ns396p60 rfl rfl) rfl 

theorem RS397to408.d25 : Enclosure.Real.IsNear qz329 Bool.false 120047984 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 120047984 268435456 16 268435456 RS397to408.d24 rfl 

noncomputable def Ns396p61 := BSN.log_dyadic_bound 2 10 6 5 103950000000000 16777216 6250000 1420244935680 967680 6802575 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 2) (BSN.artanhQ 10) 0 5 1420244935680 103950000000000 967680 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz577)

theorem RS397to408.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 80000001 500000000000000 := BSN.isNear_log_sfrac 6 1 4034683545132279 2251799813685248 80000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 1083052117253279893684224 604462909807314587353088 1000000012500000 6250000000000000000000 4034683545132279 2251799813685248 80000001 500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 6802575 16777216 24973259072661432 36028797018963968 6250000 1000000000000000 rfl rfl rfl rfl (Ns396p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS397to408.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 480971758 268435456 44 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 80000001 500000000000000 480971758 268435456 44 268435456 RS397to408.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns396p62 := @Enclosure.Real.IsNear.inv_image qz331 82191237 33554432 1 33554432 6849269 6849270 16777216 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 82191237 33554432 1 33554432 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 82191237 33554432 1 33554432 82191237 33554432 1 33554432 (BSN.sqrt_enclosure 6 1 41095618 41095619 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS397to408.d28 : Enclosure.Real.IsNear qz332 Bool.false 13698539 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 13698539 33554432 1 33554432 13698539 33554432 1 33554432 (Ns396p62 rfl rfl) rfl 

theorem RS397to408.d29 : Enclosure.Real.IsNear qz332 Bool.false 109588312 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 13698539 33554432 1 33554432 109588312 268435456 8 268435456 RS397to408.d28 rfl 

noncomputable def Ns396p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 16777216 6250000 11010900719820672 5524329195 9388794 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz577)

theorem RS397to408.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 80000001 500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 80000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 1176230476650867868041216 604462909807314587353088 1000000012500000 6250000000000000000000 4381799983422711 2251799813685248 80000001 500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 9388794 16777216 24973259072661432 36028797018963968 6250000 1000000000000000 rfl rfl rfl rfl (Ns396p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS397to408.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 522351262 268435456 44 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 80000001 500000000000000 522351262 268435456 44 268435456 RS397to408.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns396p64 := @Enclosure.Real.IsNear.inv_image qz334 88776683 33554432 1 33554432 6341191 6341192 16777216 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 88776683 33554432 1 33554432 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 88776683 33554432 1 33554432 88776683 33554432 1 33554432 (BSN.sqrt_enclosure 7 1 44388341 44388342 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS397to408.d32 : Enclosure.Real.IsNear qz335 Bool.false 12682383 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 12682383 33554432 1 33554432 12682383 33554432 1 33554432 (Ns396p64 rfl rfl) rfl 

theorem RS397to408.d33 : Enclosure.Real.IsNear qz335 Bool.false 101459064 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 12682383 33554432 1 33554432 101459064 268435456 8 268435456 RS397to408.d32 rfl 

noncomputable def Ns396p65 := nat_lit 1256945285058001618599936 

noncomputable def Ns396p66 := BSN.log_dyadic_bound 0 16 1 0 1 16777216 6250000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz577)

theorem RS397to408.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 160000003 1000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 160000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false Ns396p65 604462909807314587353088 1000000018750000 6250000000000000000000 9364972152248037 4503599627370496 160000003 1000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 16777216 24973259072661432 36028797018963968 6250000 1000000000000000 rfl rfl rfl rfl (Ns396p66 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS397to408.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 558195838 268435456 44 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 160000003 1000000000000000 558195838 268435456 44 268435456 RS397to408.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns396p67 := @Enclosure.Real.IsNear.inv_image qz337 94906265 33554432 1 33554432 5931641 5931642 16777216 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 94906265 33554432 1 33554432 (BSN.sqrt_enclosure 8 1 47453132 47453133 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS397to408.d36 : Enclosure.Real.IsNear qz338 Bool.false 11863283 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 11863283 33554432 1 33554432 (Ns396p67 rfl rfl) rfl 

theorem RS397to408.d37 : Enclosure.Real.IsNear qz338 Bool.false 94906264 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 94906264 268435456 8 268435456 RS397to408.d36 rfl 

noncomputable def Ns396p68 := nat_lit 1328140746012062765809664 

noncomputable def Ns396p69 := BSN.log_dyadic_bound 1 17 3 2 1252815 16777216 6250000 1448 3 1976071 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz577)

theorem RS397to408.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 160000003 1000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 160000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false Ns396p68 604462909807314587353088 1000000018750000 6250000000000000000000 9895419672221413 4503599627370496 160000003 1000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 1976071 16777216 24973259072661432 36028797018963968 6250000 1000000000000000 rfl rfl rfl rfl (Ns396p69 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS397to408.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 589812974 268435456 44 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 160000003 1000000000000000 589812974 268435456 44 268435456 RS397to408.d38 rfl 

noncomputable abbrev qz340 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns396p70 := @Enclosure.Real.IsNear.inv_image qz340 100663297 33554432 1 33554432 5592405 5592406 16777216 (@Enclosure.Real.IsNear.of_eq qz340 (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 100663297 33554432 1 33554432 (BSN.sqrt_enclosure 9 1 50331648 50331649 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS397to408.d40 : Enclosure.Real.IsNear qz341 Bool.false 11184811 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 11184811 33554432 1 33554432 (Ns396p70 rfl rfl) rfl 

theorem RS397to408.d41 : Enclosure.Real.IsNear qz341 Bool.false 89478488 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 89478488 268435456 8 268435456 RS397to408.d40 rfl 

noncomputable def Ns396p71 := nat_lit 1391827265235416537628672 

noncomputable def Ns396p72 := BSN.log_dyadic_bound 2 18 4 3 3571283520 16777216 6250000 14806464 960 3743727 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz706 := (Enclosure.sfrac Bool.false 10 1)

noncomputable abbrev qz578 := qz706

noncomputable abbrev qz342 := qz578

noncomputable abbrev qz1 := qz342

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz577)

theorem RS397to408.d42 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 10369921216632549 4503599627370496 160000003 1000000000000000 := BSN.isNear_log_sfrac 10 1 10369921216632549 4503599627370496 160000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false Ns396p71 604462909807314587353088 1000000018750000 6250000000000000000000 10369921216632549 4503599627370496 160000003 1000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 3743727 16777216 24973259072661432 36028797018963968 6250000 1000000000000000 rfl rfl rfl rfl (Ns396p72 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS397to408.d43 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 618095470 268435456 44 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 10369921216632549 4503599627370496 160000003 1000000000000000 618095470 268435456 44 268435456 RS397to408.d42 rfl 

noncomputable abbrev qz344 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns396p73 := @Enclosure.Real.IsNear.inv_image qz344 106108431 33554432 1 33554432 5305421 5305422 16777216 (@Enclosure.Real.IsNear.of_eq qz344 (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 106108431 33554432 1 33554432 (BSN.sqrt_enclosure 10 1 53054215 53054216 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz345 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS397to408.d44 : Enclosure.Real.IsNear qz345 Bool.false 10610843 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 10610843 33554432 1 33554432 (Ns396p73 rfl rfl) rfl 

theorem RS397to408.d45 : Enclosure.Real.IsNear qz345 Bool.false 84886744 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 84886744 268435456 8 268435456 RS397to408.d44 rfl 

theorem RS397to408.d46 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz707 := (@instHMul Real Real.instMul)

noncomputable abbrev qz579 := qz707

noncomputable abbrev qz346 := (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz2 := qz346

theorem RS397to408.d47 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS397to408.d46 rfl 

noncomputable abbrev qz347 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 2 1) Real.pi))

noncomputable abbrev qz3 := qz347

theorem RS397to408.d48 : Enclosure.Real.IsNear qz3 Bool.false 5340353 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 5340353 33554432 1 33554432 5340353 33554432 1 33554432 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 2670176 2670177 16777216 RS397to408.d47 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns396p74 := nat_lit 3957700054230419495740787 

noncomputable def Ns396p75 := nat_lit 3689348814741910323200000000 

noncomputable def Ns396p76 := nat_lit 1632575776067577594505303425024 

noncomputable abbrev qz708 := (Enclosure.sfrac Bool.false 744291 1000)

noncomputable abbrev qz580 := qz708

noncomputable abbrev qz348 := qz580

noncomputable abbrev qz4 := qz348

noncomputable abbrev qz349 := qz579

noncomputable abbrev qz5 := qz349

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10)

noncomputable abbrev qz350 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz709 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 744291 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz581 := qz709

noncomputable abbrev qz351 := qz581

noncomputable abbrev qz352 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz7 := (@HPow.hPow Real Real Real qz350 qz351 qz352)

noncomputable abbrev qz710 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 744291 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz582 := qz710

noncomputable abbrev qz353 := qz582

noncomputable abbrev qz8 := qz353

noncomputable def Ns396p77 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8)) 158986947 67108864 71363 67108864 1951851198292258553325 9444732965739290427392 34477639581485095740787 Ns396p75 Ns396p76 

noncomputable def Ns396p78 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin BSN.quadSignNeg 9 10 744291 1000 197 268435456 134217728 4503599627370496 Bool.false 376961493763 2499 618095470 44 84886744 8 

noncomputable def Ns396p79 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 744291 1000 91 147 268435456 134217728 4503599627370496 Bool.false 376961493763 2499 

noncomputable def Ns396p80 := Ns396p79 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 372472955 107338 Bool.true 127818725 Bool.true 47352513 14148475504056880 1 Bool.false 123043127 Bool.false Bool.false 47107311 Bool.false Bool.true 313268204 

noncomputable def Ns396p81 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 744291 1000 45 28 268435456 134217728 4503599627370496 Bool.false 376961493763 2499 

noncomputable def Ns396p82 := Ns396p81 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 472188753 79606 Bool.false 3958757 Bool.true 13441390 14148475504056880 1 Bool.false 3958613 Bool.true Bool.false 268099000 Bool.false Bool.true 372472955 

noncomputable def Ns396p83 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 744291 1000 237 131 268435456 134217728 4503599627370496 Bool.false 376961493763 2499 

noncomputable def Ns396p84 := Ns396p83 372130544 43 134217720 8 432030192 43 120047984 16 Bool.true 515139438 46895 Bool.false 55268539 Bool.false 168187026 14148475504056880 1 Bool.false 54878882 Bool.true Bool.false 157397106 Bool.false Bool.true 472188753 

noncomputable def Ns396p85 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 744291 1000 565 373 268435456 134217728 4503599627370496 Bool.false 376961493763 2499 

noncomputable def Ns396p86 := Ns396p85 186065264 43 189812528 16 294906480 43 154981288 8 Bool.true 268435336 2547 Bool.false 238345384 Bool.false 187034113 14148475504056880 1 Bool.false 208239313 Bool.true Bool.false 172264007 Bool.true Bool.true 515139438 

noncomputable def Ns396p87 := nat_lit 4300649705652712946796773560143242830972890704000615460861 

noncomputable def Ns396p88 := nat_lit 3062506075376711644454692222989812001968133341446144000 

noncomputable def Ns396p89 := nat_lit 109636603163366836124180593176480000 

noncomputable def Ns396p90 := nat_lit 489609325143021663963555845223188854080 

noncomputable abbrev qz354 := (@Eq.refl Real qz580)

noncomputable abbrev qz9 := qz354

noncomputable def Ns396p91 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 744291 1000 2215877370724 16000000 1488582 4000 2000 Ns396p89 Ns396p90 qz9 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns396p92 := nat_lit 12385871152279813286774707853212539353201925227521772527279680 

noncomputable abbrev qz711 := (@instHSub Real Real.instSub)

noncomputable abbrev qz583 := qz711

noncomputable abbrev qz355 := qz583

noncomputable abbrev qz584 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz712 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz713 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz585 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1488582))))

noncomputable abbrev qz356 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 744291 4000) (Real.log (Enclosure.sfrac Bool.false 2215877370724 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz585))

noncomputable abbrev qz586 := (Enclosure.sfrac Bool.false 744291 2000)

noncomputable abbrev qz10 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz356 qz586) (@HMul.hMul Real Real Real qz349 qz586 (Real.log Real.pi)))

noncomputable def Ns396p93 := @Enclosure.Real.IsNear.addLit_ft_p qz10 (Enclosure.sfrac Bool.true Ns396p89 Ns396p90) 25297461652102293676821 18014398509481984000 38120891377364103 4096000000000000000000 Ns396p89 Ns396p90 0 1 Ns396p92 

noncomputable def Ns396p94 := nat_lit 1697683913556148140445840441344000 

noncomputable abbrev qz11 := (@HSub.hSub Real Real Real qz355 qz356 qz586)

noncomputable def Ns396p95 := @Enclosure.Real.IsNear.subLit_ff_p qz11 (@HMul.hMul Real Real Real qz5 qz586 (Real.log Real.pi)) 32971704845244757107477 18014398509481984000 15045832653447 4000000000000000000 28588783715451 67108864000 744291 134217728000 Ns396p94 25297461652102293676821 18014398509481984000 

noncomputable def Ns396p96 := nat_lit 65943409690489514214954000 

noncomputable abbrev qz12 := qz356

noncomputable def Ns396p97 := @Enclosure.Real.IsNear.subLit_ff_p qz12 qz586 39675682185755184784149 18014398509481984000 15045832653447 4000000000000000000 744291 2000 0 1 Ns396p96 32971704845244757107477 18014398509481984000 15045832653447 4000000000000000000 

noncomputable def Ns396p98 := nat_lit 89341693753718638227151532427105533952 

noncomputable def Ns396p99 := nat_lit 57247813039749254491406336 

noncomputable def Ns396p100 := nat_lit 4835703278458516698824704 

noncomputable def Ns396p101 := nat_lit 5190640146904922498612884211406562467286671179984640 

noncomputable def Ns396p102 := nat_lit 1311654065448919463459719652573662052679583991808 

noncomputable def Ns396p103 := nat_lit 596067430208732226129243370652544491483996928 

noncomputable def Ns396p104 := BSN.log_dyadic_bound 118725370724 4313029370724 3 2 Ns396p101 134217728 50000000 Ns396p102 Ns396p103 7391128 4431754741448 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 118725370724) (BSN.artanhQ 4313029370724) 0 2 Ns396p102 Ns396p101 Ns396p103 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz357 := (Real.log (Enclosure.sfrac Bool.false 2215877370724 16000000))

noncomputable abbrev qz358 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns396p105 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 744291 4000) qz357 744291 4000 0 1 53316180631284839 4503599627370496 20000017 1000000000000000 39682753398239624104149 18014398509481984000 14885832652947 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 744291 4000) (BSN.isNear_log_sfrac 2215877370724 16000000 53316180631284839 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2215877370724) qz358)) Bool.false Ns396p99 Ns396p100 1000000850000000 50000000000000000000000 53316180631284839 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2215877370724 16000000 17 4431754741448 4194304000000 7391128 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns396p104 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns396p106 := BSN.arctan_dyadic_bound_f 1000 1488582 1 0 16777216 6250000 0 1 1 0 1 1 11270 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1488582) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1488582) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz587 := qz712

noncomputable abbrev qz359 := qz587

noncomputable abbrev qz13 := qz359

noncomputable abbrev qz588 := qz713

noncomputable abbrev qz360 := qz588

noncomputable abbrev qz14 := qz360

noncomputable abbrev qz714 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz589 := qz714

noncomputable abbrev qz361 := qz589

noncomputable abbrev qz15 := (@Enclosure.Real.IsNear.mulLit_ff qz361 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 1488582)

noncomputable def Ns396p107 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz362)) 884279719003555 562949953421312 1 2000000000000000 11270 16777216 1 6250000 14829407404166888816640 883901560554915 562949953421312 320000001 2000000000000000 qz15 (Ns396p106 rfl) rfl rfl 

noncomputable abbrev qz363 := (@HMul.hMul Real Real Real qz579 qz584 qz585)

noncomputable abbrev qz16 := qz363

noncomputable abbrev qz364 := qz584

noncomputable abbrev qz17 := qz364

noncomputable abbrev qz365 := qz585

noncomputable abbrev qz18 := qz365

noncomputable abbrev qz366 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns396p108 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 744291 4000) qz357) qz16 39682753398239624104149 18014398509481984000 14885832652947 4000000000000000000 883901560554915 2251799813685248 320000001 8000000000000000 Ns396p98 39675682185755184784149 18014398509481984000 15045832653447 4000000000000000000 (Ns396p105 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz18 1 4 0 1 883901560554915 562949953421312 320000001 2000000000000000 883901560554915 2251799813685248 320000001 8000000000000000 qz366 Ns396p107 rfl) 

noncomputable def Ns396p109 := @Ns396p93 Ns396p87 Ns396p88 38120891377364103 4096000000000000000000 (@Ns396p95 38120891377364103 4096000000000000000000 (Ns396p97 (Ns396p108 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 744291 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz586 (Real.log Real.pi) 744291 2000 0 1 38410761 33554432 1 67108864 28588783715451 67108864000 744291 134217728000 (Enclosure.Real.IsNear.const Bool.false 744291 2000) RS397to408.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns396p89 Ns396p90) 

noncomputable abbrev qz367 := (@instHAdd Real Real.instAdd)

noncomputable def Ns396p110 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns396p87 Ns396p88 38120891377364103 4096000000000000000000 1472505835 1048576 313 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz367 qz10 (Enclosure.sfrac Bool.true Ns396p89 Ns396p90)) Bool.false Ns396p87 Ns396p88 38120891377364103 4096000000000000000000 Ns396p91 (Ns396p109 rfl rfl)) 

noncomputable def Ns396p111 := nat_lit 3502596197628825488867409526441760231706891777294476631946201894494645895379258365430115582760616415495940542581058177620807242697124745216 

noncomputable def Ns396p112 := nat_lit 69061887427279807374175457422696049589758900585025510522285359577850094671315332446731519433112496475662717985575392155893264493730122956800 

noncomputable def Ns396p113 := nat_lit 2485086810324903552692943795209640929735035923571506680799441125029774764932674859795628499877807969345528853229520872187853096226816 

noncomputable def Ns396p114 := nat_lit 17491269838581202980649012410600558663136661187909478592153325596604636163983677222048926320428327277739089324282968016481884917584666955776 

noncomputable def Ns396p115 := nat_lit 2417166059954793258096141009794361735641561520475892868279987585224753313496036635635603180158937376648195129495138725456264257280554303488000 

noncomputable abbrev qz368 := (BSN.sinEvenQ 68719476736)

noncomputable abbrev qz369 := (BSN.sinOddQ 68719476736)

noncomputable def Ns396p116 := BSN.sin_dyadic_bound_f 107881041454 68719476736 4 3 33554432 12512208 Ns396p111 Ns396p112 Ns396p113 Ns396p114 Ns396p115 Ns396p113 33554417 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107881041454) qz368 0 3 Ns396p111 Ns396p112 Ns396p113 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107881041454) qz369 0 3 Ns396p114 Ns396p115 Ns396p113 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p117 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1472505835) (@Nat.cast Real Real.instNatCast 1048576)) Bool.false 1472505835 1048576 313 33554432 Bool.true 33554417 33554432 1 6250000 (Ns396p110 rfl) (Enclosure.sfrac_false_div 1472505835 1048576) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1472505835) (@Nat.cast Real Real.instNatCast 1048576)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 237232918992055361863680) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 33554417 33554432 223 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q1 1472505835 1048576 226375608064910080 72057594037927936 223 237232918992055361863680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554417 33554432 237232918992055361863680 151115727451828646838272 107881041454 68719476736 12512208 12500000 (Ns396p116 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p118 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns396p87 Ns396p88 38120891377364103 4096000000000000000000 376961493763 268435456 2499 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz367 qz10 (Enclosure.sfrac Bool.true Ns396p89 Ns396p90)) Bool.false Ns396p87 Ns396p88 38120891377364103 4096000000000000000000 Ns396p91 (Ns396p109 rfl rfl)) 

noncomputable def Ns396p119 := Ns396p86 46895 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 565 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 208239313 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 373 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 172264007 268435456) qz9 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 33554417 33554432 124362777 13107200000000 268435336 268435456 2547 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554417 33554432 124362777 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554417 33554432 1989804432 209715200000000 33554417 33554432 124362777 13107200000000 (Ns396p117 rfl rfl) rfl)) rfl) (Ns396p118 rfl) RS397to408.d7 

noncomputable def Ns396p120 := nat_lit 50682442510507504462212378104531129282425467166320527739053364886896640 

noncomputable def Ns396p121 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080 

noncomputable def Ns396p122 := nat_lit 10414872638636075465698077603272172588467276015813482733166810628096 

noncomputable def Ns396p123 := nat_lit 132722868209914243755040336243366707460256800322051969868333685581807616 

noncomputable def Ns396p124 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800 

noncomputable abbrev qz370 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz371 := (BSN.sinOddQ 268435456)

noncomputable def Ns396p125 := BSN.sin_dyadic_bound_f 238345384 268435456 3 2 268435456 134217728 Ns396p120 Ns396p121 Ns396p122 Ns396p123 Ns396p124 Ns396p122 208239313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 238345384) qz370 0 2 Ns396p120 Ns396p121 Ns396p122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 238345384) qz371 0 2 Ns396p123 Ns396p124 Ns396p122 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p126 := nat_lit 19215798892426968849536027337027812274426049481479141420079667080024065 

noncomputable def Ns396p127 := nat_lit 1497499186138798943068040476912018590672563010232618058268463288321 

noncomputable def Ns396p128 := nat_lit 50324667814816884169543675721919746021969040682809755670971455316643841 

noncomputable def Ns396p129 := BSN.sin_dyadic_bound_f 187034113 268435456 3 2 268435456 134217728 Ns396p126 Ns396p121 Ns396p127 Ns396p128 Ns396p124 Ns396p127 172264007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 187034113) qz370 0 2 Ns396p126 Ns396p121 Ns396p127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 187034113) qz371 0 2 Ns396p128 Ns396p124 Ns396p127 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p130 := nat_lit 9330650824526000538483764419441 

noncomputable def Ns396p131 := nat_lit 623075623024179315423659559506411520 

noncomputable def Ns396p132 := nat_lit 4361529361169255207965616916544880640 

noncomputable def Ns396p133 := BSN.sin_dyadic_bound_f 55268539 268435456 2 1 268435456 134217728 Ns396p130 Ns396p131 Ns396p130 Ns396p130 Ns396p132 Ns396p130 54878882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 55268539) qz370 0 1 Ns396p130 Ns396p131 Ns396p130 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 55268539) qz371 0 1 Ns396p130 Ns396p132 Ns396p130 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p134 := nat_lit 12564158219670296199097644779842482368145606888295006867755518123393280 

noncomputable def Ns396p135 := nat_lit 640235762028846963488738640791520942485037974907421458323826360576 

noncomputable def Ns396p136 := nat_lit 32905092098378919531124373608454743739807804169765644066522404128112896 

noncomputable def Ns396p137 := BSN.sin_dyadic_bound_f 168187026 268435456 3 2 268435456 134217728 Ns396p134 Ns396p121 Ns396p135 Ns396p136 Ns396p124 Ns396p135 157397106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 168187026) qz370 0 2 Ns396p134 Ns396p121 Ns396p135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 168187026) qz371 0 2 Ns396p136 Ns396p124 Ns396p135 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p138 := Ns396p84 79606 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 237 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 54878882 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 131 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 157397106 268435456) qz9 rfl rfl (Ns396p119 RS397to408.d9 RS397to408.d11 RS397to408.d13 RS397to408.d17 (Ns396p125 rfl rfl) (Ns396p129 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns396p118 rfl) RS397to408.d19 RS397to408.d21 RS397to408.d23 RS397to408.d25 RS397to408.d17 (Ns396p133 rfl rfl) (Ns396p137 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns396p139 := BSN.sin_dyadic_bound_f 3958757 268435456 1 0 268435456 134217728 0 1 1 0 1 1 3958613 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 3958757) qz370 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 3958757) qz371 0 0 rfl) rfl rfl 

noncomputable def Ns396p140 := nat_lit 32641997641764493970450410000 

noncomputable def Ns396p141 := nat_lit 124615124604835863084731911901282304 

noncomputable def Ns396p142 := nat_lit 1869226869072537946270978678519234560 

noncomputable abbrev qz372 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz373 := (BSN.cosOddQ 268435456)

noncomputable def Ns396p143 := BSN.cos_dyadic_bound_f 13441390 268435456 2 1 268435456 134217728 Ns396p140 Ns396p141 Ns396p140 Ns396p140 Ns396p142 Ns396p140 268099000 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13441390) qz372 0 1 Ns396p140 Ns396p141 Ns396p140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13441390) qz373 0 1 Ns396p140 Ns396p142 Ns396p140 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p144 := Ns396p82 107338 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 3958613 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268099000 268435456) qz9 rfl rfl (Ns396p138 rfl rfl) (Ns396p118 rfl) RS397to408.d27 RS397to408.d29 RS397to408.d31 RS397to408.d33 RS397to408.d17 (Ns396p139 rfl rfl) (Ns396p143 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p145 := nat_lit 4191086346146318706884259560881124924991490830172961626191936300390625 

noncomputable def Ns396p146 := nat_lit 71245239205652364051770453421764643920595419650779419097900390625 

noncomputable def Ns396p147 := nat_lit 10976539366662596985631262650145025279839937876916417282871769900390625 

noncomputable def Ns396p148 := BSN.sin_dyadic_bound_f 127818725 268435456 3 2 268435456 134217728 Ns396p145 Ns396p121 Ns396p146 Ns396p147 Ns396p124 Ns396p146 123043127 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 127818725) qz370 0 2 Ns396p145 Ns396p121 Ns396p146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 127818725) qz371 0 2 Ns396p147 Ns396p124 Ns396p146 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p149 := nat_lit 5027732093423311257426971298561 

noncomputable def Ns396p150 := BSN.sin_dyadic_bound_f 47352513 268435456 2 1 268435456 134217728 Ns396p149 Ns396p131 Ns396p149 Ns396p149 Ns396p132 Ns396p149 47107311 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 47352513) qz370 0 1 Ns396p149 Ns396p131 Ns396p149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 47352513) qz371 0 1 Ns396p149 Ns396p132 Ns396p149 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p151 := Ns396p80 131569 BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 123043127 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47107311 268435456) qz9 rfl rfl (Ns396p144 rfl) (Ns396p118 rfl) RS397to408.d35 RS397to408.d37 RS397to408.d39 RS397to408.d41 RS397to408.d17 (Ns396p148 rfl rfl) (Ns396p150 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p152 := nat_lit 49134206357760943421683210000 

noncomputable def Ns396p153 := BSN.sin_dyadic_bound_f 14888330 268435456 2 1 268435456 134217728 Ns396p152 Ns396p131 Ns396p152 Ns396p152 Ns396p132 Ns396p152 14880697 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 14888330) qz370 0 1 Ns396p152 Ns396p131 Ns396p152 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 14888330) qz371 0 1 Ns396p152 Ns396p132 Ns396p152 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p154 := Ns396p78 Bool.true 313268204 131569 Bool.true 14888330 14148475504056880 1 Bool.false 14880697 Bool.true Bool.true 317973894 142726 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 197 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 14880697 268435456) qz9 rfl (Ns396p151 rfl) (Ns396p118 rfl) RS397to408.d43 RS397to408.d45 RS397to408.d17 (Ns396p153 rfl rfl) rfl 

noncomputable def Ns396p155 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) 317973894 268435456 142726 268435456 317973894 268435456 142726 268435456 170710934463971328 158986947 67108864 71363 67108864 (Ns396p154 rfl rfl rfl rfl) 

noncomputable def Ns396p156 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8) 10170895 33554432 1 33554432 191905549933635 281474976710656 3382462712827097 109951162777600000000 1951851198292258553325 9444732965739290427392 

noncomputable def Ns396p157 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz7 1 1 0 1 10170895 33554432 1 33554432 10170895 33554432 1 33554432 

noncomputable abbrev qz19 := qz351

noncomputable abbrev qz20 := (@Enclosure.Real.IsNear.of_eq qz351 (@HMul.hMul Real Real Real qz349 qz348 qz347) Bool.false 3974776674723 33554432000 744291 33554432000 (BSN.t_div_two_pi_mk qz348 744291 1000 qz354) (@Enclosure.Real.IsNear.mulLit_ff qz348 qz347 744291 1000 0 1 5340353 33554432 1 33554432 3974776674723 33554432000 744291 33554432000 (Enclosure.Real.IsNear.const Bool.false 744291 1000) RS397to408.d48 rfl))

noncomputable def Ns396p158 := @Enclosure.Real.IsNear.sqrt_image qz19 3974776674723 33554432000 744291 33554432000 182600211 182600246 16777216 qz20 

noncomputable abbrev qz715 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 744291 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz590 := qz715

noncomputable abbrev qz374 := qz590

noncomputable abbrev qz21 := qz374

noncomputable def Ns396p159 := @Enclosure.Real.IsNear.sqrt_image qz21 365200457 33554432 35 33554432 55349102 55349109 16777216 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 365200457 33554432 35 33554432 365200457 33554432 35 33554432 (Ns396p158 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz591 := (Real.sqrt qz715)

noncomputable abbrev qz375 := qz591

noncomputable abbrev qz22 := qz375

noncomputable def Ns396p160 := @Enclosure.Real.IsNear.inv_image qz22 110698211 33554432 7 33554432 5085447 5085448 16777216 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 110698211 33554432 7 33554432 110698211 33554432 7 33554432 (Ns396p159 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns396p161 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz22) Bool.false 10170895 33554432 1 33554432 10170895 33554432 1 33554432 (Ns396p160 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz23 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz353))

noncomputable abbrev qz592 := (@HMul.hMul Real Real Real qz707 qz710 qz710)

noncomputable abbrev qz593 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz376 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz592 qz582) qz593)

noncomputable abbrev qz24 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz376))

noncomputable def Ns396p162 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz8) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz23) qz24) Bool.false 191905549933635 

noncomputable def Ns396p163 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz23) qz24 45027735 33554432 409 

noncomputable def Ns396p164 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 45027735 33554432 409 33554432 45027735 33554432 409 

noncomputable def Ns396p165 := @Enclosure.Real.IsNear.recentre' qz23 Bool.false 25004587 33554432 1414804432 209715200000000 25004587 33554432 88425277 13107200000000 

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz349 qz346 qz353)

noncomputable abbrev qz377 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable def Ns396p166 := @Enclosure.Real.IsNear.cos_image qz25 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46583751) qz377) Bool.false 46583751 8388608 221 33554432 Bool.false 25004587 33554432 1 

noncomputable def Ns396p167 := nat_lit 944512639571285868012304949 

noncomputable def Ns396p168 := nat_lit 144115188075855872000000000000000 

noncomputable def Ns396p169 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz8 884279719003555 140737488355328 1 500000000000000 29656137 33554432 35 33554432 26224320493090930567035 4722366482869645213696 Ns396p167 

noncomputable def Ns396p170 := @Enclosure.Real.IsNear.subLit_ff_p qz21 qz1 365200457 33554432 35 33554432 10 1 0 1 29656137 29656137 33554432 35 

noncomputable abbrev qz378 := (Enclosure.Real.IsNear.const Bool.false 10 1)

noncomputable def Ns396p171 := @Ns396p170 33554432 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 365200457 33554432 35 33554432 365200457 33554432 35 33554432 (Ns396p158 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns396p172 := @Enclosure.Real.IsNear.recentre' qz25 Bool.false 26224320493090930567035 4722366482869645213696 Ns396p167 Ns396p168 46583751 8388608 221 33554432 (@Ns396p169 Ns396p168 RS397to408.d47 (Ns396p171 rfl rfl) rfl) 

noncomputable def Ns396p173 := nat_lit 1208925819614629174706176 

noncomputable def Ns396p174 := nat_lit 751828294851825888064074687331101005891638230838267503202721309707266999377878381169577505 

noncomputable def Ns396p175 := nat_lit 180468656028383376705345110207518346455653528001341539704795567934989718275908111313435361280 

noncomputable def Ns396p176 := nat_lit 124248584875757911518914805198373807923150369371999861745599231198240991586571493150241 

noncomputable def Ns396p177 := nat_lit 1968872941188792765453926890468276695931938837311717365754777221906616417717588930169507361 

noncomputable def Ns396p178 := nat_lit 3308592027187028572931327020471169685020314680024594894587918745474811501724982040746314956800 

noncomputable def Ns396p179 := BSN.sin_dyadic_bound_f 57781183283 68719476736 3 2 33554432 12512208 Ns396p174 Ns396p175 Ns396p176 Ns396p177 Ns396p178 Ns396p176 25004587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 57781183283) qz368 0 2 Ns396p174 Ns396p175 Ns396p176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 57781183283) qz369 0 2 Ns396p177 Ns396p178 Ns396p176 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz594 := (@Nat.cast Real Real.instNatCast Ns396p173)

noncomputable def Ns396p180 := @Ns396p166 6250000 (Ns396p172 rfl) (Enclosure.sfrac_false_div 46583751 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46583751) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1016497326189331404029952) qz594) 226375608064910080 72057594037927936 Bool.false 25004587 33554432 0 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 46583751 8388608 226375608064910080 72057594037927936 0 1016497326189331404029952 Ns396p173 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 25004587 33554432 1016497326189331404029952 Ns396p173 57781183283 68719476736 12512208 12500000 (Ns396p179 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p181 := @Enclosure.Real.IsNear.inv_image qz23 25004587 33554432 88425277 13107200000000 22513663 22514072 16777216 (Ns396p165 (Ns396p180 rfl rfl) rfl) rfl 

noncomputable def Ns396p182 := @Enclosure.Real.IsNear.recentre' qz24 Bool.false 8523882 16777216 

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz349 qz346 qz376)

noncomputable def Ns396p183 := @Enclosure.Real.IsNear.cos_image qz26 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8706217)) qz377) Bool.true 8706217 8388608 

noncomputable def Ns396p184 := nat_lit 164455790784671678056787300845 

noncomputable def Ns396p185 := nat_lit 158456325028528675187087900672 

noncomputable def Ns396p186 := nat_lit 87713810648233216192141441058049913 

noncomputable def Ns396p187 := @Enclosure.Real.IsNear.recentre' qz26 Bool.true Ns396p184 Ns396p185 Ns396p186 

noncomputable def Ns396p188 := nat_lit 4835703278458516698824704000000000000000 

noncomputable abbrev qz27 := qz376

noncomputable def Ns396p189 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz27 884279719003555 140737488355328 1 500000000000000 185977114764079 

noncomputable abbrev qz379 := (@HSub.hSub Real Real Real qz583 qz592 qz582)

noncomputable abbrev qz28 := qz379

noncomputable abbrev qz380 := qz593

noncomputable abbrev qz29 := qz380

noncomputable def Ns396p190 := @Enclosure.Real.IsNear.subLit_tf qz28 qz29 115608370586415 1125899906842624 3250335935 1125899906842624 1 16 

noncomputable abbrev qz381 := qz592

noncomputable abbrev qz30 := qz381

noncomputable def Ns396p191 := @Enclosure.Real.IsNear.subLit_ff_n qz30 qz8 879486461762769 1125899906842624 2075930815 1125899906842624 29656137 33554432 35 33554432 

noncomputable def Ns396p192 := @Enclosure.Real.IsNear.mulLit_ff qz8 qz8 29656137 33554432 35 33554432 29656137 33554432 35 33554432 879486461762769 1125899906842624 

noncomputable def Ns396p193 := nat_lit 47828489908307879198093145074948779326762587788280178861121 

noncomputable def Ns396p194 := nat_lit 988643523323402220304136834155207460536120982503085435781120 

noncomputable def Ns396p195 := nat_lit 33009268553945767190833339343293116876871877293216818241 

noncomputable def Ns396p196 := nat_lit 143419451187815746059897768546159751746534019610254102946881 

noncomputable def Ns396p197 := nat_lit 44488958549553099913686157536984335724125444212638844610150400 

noncomputable def Ns396p198 := BSN.cos_dyadic_bound_f 8706217 8388608 3 2 16777216 6250000 Ns396p193 Ns396p194 Ns396p195 Ns396p196 Ns396p197 Ns396p195 8523882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 8706217) (BSN.cosEvenQ 8388608) 0 2 Ns396p193 Ns396p194 Ns396p195 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 8706217) (BSN.cosOddQ 8388608) 0 2 Ns396p196 Ns396p197 Ns396p195 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz382 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns396p199 := @Ns396p182 3839804432 209715200000000 4261941 8388608 239987777 13107200000000 (@Ns396p183 609 33554432 Bool.false 8523882 16777216 1 6250000 (@Ns396p187 Ns396p188 8706217 8388608 609 33554432 (@Ns396p189 1125899906842624 3250335935 1125899906842624 Ns396p184 Ns396p185 Ns396p186 Ns396p188 RS397to408.d47 (@Ns396p190 0 1 2975633836225264 185977114764079 1125899906842624 3250335935 1125899906842624 (@Ns396p191 3879173209472662241280 115608370586415 1125899906842624 3250335935 1125899906842624 (@Ns396p192 2075930815 1125899906842624 (Ns396p171 rfl rfl) (Ns396p171 rfl rfl) rfl) (Ns396p171 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8706217 8388608) (BSN.cos_neg_of_bound 8706217 8388608 Bool.false 8523882 16777216 1 6250000 (Ns396p198 rfl rfl)) rfl rfl) 

noncomputable abbrev qz31 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 10 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns396p200 := @Ns396p156 34477639581485095740787 Ns396p75 (Ns396p157 qz31 (@Enclosure.Real.IsNear.of_eq qz7 (@Inv.inv Real Real.instInv qz22) Bool.false 10170895 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz19 (BSN.t_div_two_pi_nonneg qz4 744291 1000 qz9)) Ns396p161) rfl) (@Ns396p162 281474976710656 3382462712827097 109951162777600000000 (BSN.correction_mk qz8 (BSN.cos_two_pi_p_ne_zero_mk qz4 744291 1000 10 qz9 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 744291 1000 10 qz9 rfl rfl rfl))) (@Ns396p163 33554432 4261941 8388608 239987777 13107200000000 191905549933635 281474976710656 3382462712827097 109951162777600000000 (@Ns396p164 33554432 (Ns396p181 rfl rfl rfl rfl rfl) rfl) (Ns396p199 rfl) rfl)) 

noncomputable abbrev qz32 := qz355

noncomputable def Ns396p201 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 24327274800353908456941 9444732965739290427392 Ns396p74 Ns396p75 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8))) Bool.true 24327274800353908456941 9444732965739290427392 Ns396p74 Ns396p75 (BSN.hardyZApproximantRS₀_eq qz4 10 (@BSN.floor_sqrt_eq_dec qz4 744291 1000 10 qz9 rfl rfl rfl)) (@Ns396p77 24327274800353908456941 9444732965739290427392 Ns396p74 Ns396p75 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10)) Bool.true 158986947 67108864 71363 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (Ns396p155 (Ns396p154 rfl rfl rfl rfl) rfl rfl)) (Ns396p200 rfl) rfl rfl)) 

theorem RS397to408.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 24327274800353908456941 9444732965739290427392 Ns396p74 Ns396p75 := Ns396p201 

theorem RS397to408.d50 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS397to408.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS397to408.d3 a b h)) 

noncomputable def Ns396p202 := nat_lit 922337203685477580800000000 

noncomputable def Ns396p203 := nat_lit 152819403482663491934460313600 

noncomputable abbrev qz716 := (Enclosure.sfrac Bool.false 745607 1000)

noncomputable abbrev qz595 := qz716

noncomputable abbrev qz383 := qz595

noncomputable abbrev qz33 := qz383

noncomputable abbrev qz717 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 745607 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz596 := qz717

noncomputable abbrev qz384 := qz596

noncomputable abbrev qz34 := (@HPow.hPow Real Real Real qz350 qz384 qz352)

noncomputable abbrev qz718 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 745607 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz597 := qz718

noncomputable abbrev qz385 := qz597

noncomputable abbrev qz35 := qz385

noncomputable def Ns396p204 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35)) 78930347 67108864 17873 16777216 499928133105811987929 2361183241434822606848 8305513786276781502087 Ns396p202 Ns396p203 

noncomputable def Ns396p205 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.cos BSN.quadSignPos 9 10 745607 1000 196 268435456 134217728 4503599627370496 Bool.false 377804981885 2504 618095470 44 84886744 8 

noncomputable def Ns396p206 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 745607 1000 91 146 268435456 134217728 4503599627370496 Bool.false 377804981885 2504 

noncomputable def Ns396p207 := Ns396p206 558195838 44 94906264 8 589812974 44 89478488 8 Bool.false 153019708 107533 Bool.true 18916326 Bool.true 401715693 14148475504056880 1 Bool.false 18900673 Bool.false Bool.false 19923397 Bool.true Bool.false 153060972 

noncomputable def Ns396p208 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 745607 1000 45 27 268435456 134217728 4503599627370496 Bool.false 377804981885 2504 

noncomputable def Ns396p209 := Ns396p208 480971758 44 109588312 8 522351262 44 101459064 8 Bool.false 144089061 79751 Bool.false 214488045 Bool.true 279024957 14148475504056880 1 Bool.false 192382352 Bool.true Bool.false 231424958 Bool.false Bool.false 153019708 

noncomputable def Ns396p210 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 745607 1000 237 132 268435456 134217728 4503599627370496 Bool.false 377804981885 2504 

noncomputable def Ns396p211 := Ns396p210 372130544 43 134217720 8 432030192 43 120047984 16 Bool.false 158494024 46982 Bool.false 409032865 Bool.false 21465987 14148475504056880 1 Bool.false 268138643 Bool.true Bool.false 267577627 Bool.false Bool.false 144089061 

noncomputable def Ns396p212 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 745607 1000 566 374 268435456 134217728 4503599627370496 Bool.false 377804981885 2504 

noncomputable def Ns396p213 := Ns396p212 186065264 43 189812528 16 294906480 43 154981288 8 Bool.false 268435440 2555 Bool.false 415314191 Bool.false 220767880 14148475504056880 1 Bool.false 6342646 Bool.true Bool.false 182655988 Bool.true Bool.false 158494024 

noncomputable def Ns396p214 := nat_lit 39205818312923774320600747788763114161248757648328131079769 

noncomputable def Ns396p215 := nat_lit 27856254473265474145231746774211150347374802442911744000 

noncomputable def Ns396p216 := nat_lit 110609292762532431524451029507360000 

noncomputable def Ns396p217 := nat_lit 494826481536589464575679407229301005120 

noncomputable abbrev qz598 := (@Eq.refl Real qz716)

noncomputable abbrev qz386 := qz598

noncomputable abbrev qz36 := qz386

noncomputable def Ns396p218 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz33 745607 1000 2223720193796 16000000 1491214 4000 2000 Ns396p216 Ns396p217 qz36 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns396p219 := nat_lit 12545861860135607782592239292404196531599602447465001945526080 

noncomputable abbrev qz599 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1491214))))

noncomputable abbrev qz387 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 745607 4000) (Real.log (Enclosure.sfrac Bool.false 2223720193796 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz599))

noncomputable abbrev qz600 := (Enclosure.sfrac Bool.false 745607 2000)

noncomputable abbrev qz37 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz387 qz600) (@HMul.hMul Real Real Real qz349 qz600 (Real.log Real.pi)))

noncomputable def Ns396p220 := @Enclosure.Real.IsNear.addLit_ft_p qz37 (Enclosure.sfrac Bool.true Ns396p216 Ns396p217) 25354067174692619429009 18014398509481984000 38188004213085531 4096000000000000000000 Ns396p216 Ns396p217 0 1 Ns396p219 

noncomputable def Ns396p221 := nat_lit 1701482645873311239065122635776000 

noncomputable abbrev qz38 := (@HSub.hSub Real Real Real qz355 qz387 qz600)

noncomputable def Ns396p222 := @Enclosure.Real.IsNear.subLit_ff_p qz38 (@HMul.hMul Real Real Real qz5 qz600 (Real.log Real.pi)) 33041879393985036952721 18014398509481984000 15072152675819 4000000000000000000 28639332276927 67108864000 745607 134217728000 Ns396p221 25354067174692619429009 18014398509481984000 

noncomputable def Ns396p223 := nat_lit 13216751757594014781088400 

noncomputable abbrev qz39 := qz387

noncomputable def Ns396p224 := @Enclosure.Real.IsNear.subLit_ff_p qz39 qz600 7951542041742940754973 3602879701896396800 15072152675819 4000000000000000000 745607 2000 0 1 Ns396p223 33041879393985036952721 18014398509481984000 15072152675819 4000000000000000000 

noncomputable def Ns396p225 := nat_lit 17905280888107170467138546886512738304 

noncomputable def Ns396p226 := nat_lit 57264898183526023356743680 

noncomputable def Ns396p227 := nat_lit 5228497942178863253938171380703073272584245649411840 

noncomputable def Ns396p228 := nat_lit 1496185830897328817763887878246464917499845019648 

noncomputable def Ns396p229 := nat_lit 769873879003882492738992719688389159401882368 

noncomputable def Ns396p230 := BSN.log_dyadic_bound 126568193796 4320872193796 3 2 Ns396p227 134217728 50000000 Ns396p228 Ns396p229 7865336 4447440387592 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 126568193796) (BSN.artanhQ 4320872193796) 0 2 Ns396p228 Ns396p227 Ns396p229 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz388 := (Real.log (Enclosure.sfrac Bool.false 2223720193796 16000000))

noncomputable def Ns396p231 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 745607 4000) qz388 745607 4000 0 1 53332092411374695 4503599627370496 20000017 1000000000000000 7952956285313570442973 3602879701896396800 14912152675319 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 745607 4000) (BSN.isNear_log_sfrac 2223720193796 16000000 53332092411374695 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2223720193796) qz358)) Bool.false Ns396p226 Ns396p100 1000000850000000 50000000000000000000000 53332092411374695 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2223720193796 16000000 17 4447440387592 4194304000000 7865336 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns396p230 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns396p232 := BSN.arctan_dyadic_bound_f 1000 1491214 1 0 16777216 6250000 0 1 1 0 1 1 11250 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1491214) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1491214) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz389 := (@Nat.cast Real Real.instNatCast 1491214)

noncomputable def Ns396p233 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz389)) 884279719003555 562949953421312 1 2000000000000000 11250 16777216 1 6250000 14829418663165957242880 883902231643555 562949953421312 320000001 2000000000000000 qz15 (Ns396p232 rfl) rfl rfl 

noncomputable abbrev qz390 := (@HMul.hMul Real Real Real qz579 qz584 qz599)

noncomputable abbrev qz40 := qz390

noncomputable abbrev qz391 := qz599

noncomputable abbrev qz41 := qz391

noncomputable def Ns396p234 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 745607 4000) qz388) qz40 7952956285313570442973 3602879701896396800 14912152675319 4000000000000000000 883902231643555 2251799813685248 320000001 8000000000000000 Ns396p225 7951542041742940754973 3602879701896396800 15072152675819 4000000000000000000 (Ns396p231 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz41 1 4 0 1 883902231643555 562949953421312 320000001 2000000000000000 883902231643555 2251799813685248 320000001 8000000000000000 qz366 Ns396p233 rfl) 

noncomputable def Ns396p235 := @Ns396p220 Ns396p214 Ns396p215 38188004213085531 4096000000000000000000 (@Ns396p222 38188004213085531 4096000000000000000000 (Ns396p224 (Ns396p234 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 745607 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz600 (Real.log Real.pi) 745607 2000 0 1 38410761 33554432 1 67108864 28639332276927 67108864000 745607 134217728000 (Enclosure.Real.IsNear.const Bool.false 745607 2000) RS397to408.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns396p216 Ns396p217) 

noncomputable def Ns396p236 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz33) Bool.false Ns396p214 Ns396p215 38188004213085531 4096000000000000000000 47225622735 33554432 157 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz33) (@HAdd.hAdd Real Real Real qz367 qz37 (Enclosure.sfrac Bool.true Ns396p216 Ns396p217)) Bool.false Ns396p214 Ns396p215 38188004213085531 4096000000000000000000 Ns396p218 (Ns396p235 rfl rfl)) 

noncomputable def Ns396p237 := nat_lit 7594574644894178706718720 

noncomputable def Ns396p238 := nat_lit 3508371722472234654724457225759839868410660667022812339257194820981896757917422584446577596080152230198549384679154807353188076740953706496 

noncomputable def Ns396p239 := nat_lit 2497375539410416737189444050516436652753311922278464939303540788071069443988894637390019664672549041522647244457353728412189476458496 

noncomputable def Ns396p240 := nat_lit 17520075930969734242472114406958512709900146283882238730328363632969777037218397017483494288520656576156652873860989326200784476208551366656 

noncomputable def Ns396p241 := BSN.sin_dyadic_bound_f 107925396902 68719476736 4 3 33554432 12512208 Ns396p238 Ns396p112 Ns396p239 Ns396p240 Ns396p115 Ns396p239 33554430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107925396902) qz368 0 3 Ns396p238 Ns396p112 Ns396p239 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107925396902) qz369 0 3 Ns396p240 Ns396p115 Ns396p239 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz392 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable abbrev qz393 := (@Nat.cast Real Real.instNatCast Ns396p100)

noncomputable def Ns396p242 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz33) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47225622735) qz392) Bool.false 47225622735 33554432 157 16777216 Bool.false 33554430 33554432 1 6250000 (Ns396p236 rfl) (Enclosure.sfrac_false_div 47225622735 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47225622735) qz392) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p237) qz393) 226375608064910080 72057594037927936 Bool.false 33554430 33554432 223 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 47225622735 33554432 226375608064910080 72057594037927936 223 Ns396p237 Ns396p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554430 33554432 Ns396p237 Ns396p100 107925396902 68719476736 12512208 12500000 (Ns396p241 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p243 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz33) Bool.false Ns396p214 Ns396p215 38188004213085531 4096000000000000000000 377804981885 268435456 2504 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz33) (@HAdd.hAdd Real Real Real qz367 qz37 (Enclosure.sfrac Bool.true Ns396p216 Ns396p217)) Bool.false Ns396p214 Ns396p215 38188004213085531 4096000000000000000000 Ns396p218 (Ns396p235 rfl rfl)) 

noncomputable def Ns396p244 := Ns396p213 46982 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 566 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 6342646 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 374 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 182655988 268435456) qz36 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 1) Bool.false 16777215 16777216 62376701 6553600000000 268435440 268435456 2555 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz33)) Bool.false 16777215 16777216 62376701 6553600000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz33) qz33) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz33)) Bool.false 33554430 33554432 998027216 104857600000000 16777215 16777216 62376701 6553600000000 (Ns396p242 rfl rfl) rfl)) rfl) (Ns396p243 rfl) RS397to408.d7 

noncomputable def Ns396p245 := nat_lit 16063170043933236700948726093147532597129640755690797115260355423027009771907096564755782338163288951477335361 

noncomputable def Ns396p246 := nat_lit 67052582193422231333984484018745857420694574238012043916021913709013615522643186318434558042568065189255577600 

noncomputable def Ns396p247 := nat_lit 26334267992723873236696868452481514200142332231296450614871730028199279461087153777617937940134504002881 

noncomputable def Ns396p248 := nat_lit 97228939454473012723184916996570928112612840205706615534565389899836116359546816739282697620120076763270575425 

noncomputable def Ns396p249 := nat_lit 6101784979601423051392588045705873025283206255659095996357994147520239012560529954977544781873693932222257561600 

noncomputable def Ns396p250 := BSN.cos_dyadic_bound_f 415314191 268435456 4 3 268435456 134217728 Ns396p245 Ns396p246 Ns396p247 Ns396p248 Ns396p249 Ns396p247 6342646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 415314191) qz372 0 3 Ns396p245 Ns396p246 Ns396p247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 415314191) qz373 0 3 Ns396p248 Ns396p249 Ns396p247 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p251 := nat_lit 20726720671524822229564836192481551259734519877917104341712424140800000 

noncomputable def Ns396p252 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120 

noncomputable def Ns396p253 := nat_lit 5642701772917161703736409595985579100372523120143652362649600000000 

noncomputable def Ns396p254 := nat_lit 62168876611028632365287035758252682621002814587511025720411973222400000 

noncomputable def Ns396p255 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400 

noncomputable def Ns396p256 := BSN.cos_dyadic_bound_f 220767880 268435456 3 2 268435456 134217728 Ns396p251 Ns396p252 Ns396p253 Ns396p254 Ns396p255 Ns396p253 182655988 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 220767880) qz372 0 2 Ns396p251 Ns396p252 Ns396p253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 220767880) qz373 0 2 Ns396p254 Ns396p255 Ns396p253 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p257 := nat_lit 39230578240789328428299800243765990366374672885466337805226955958181039256418530630905005943087206731577290625 

noncomputable def Ns396p258 := nat_lit 871683568514489007341798292243696146469029465094156570908284878217177001794361422139649254553384847460322508800 

noncomputable def Ns396p259 := nat_lit 21933020754169614732828421225705583151359622728094155268912641775285233259236238782237600541386962890625 

noncomputable def Ns396p260 := nat_lit 195937014789674488241919099333008403587739161040496915304650974672841798629188553017912662786556898126034890625 

noncomputable def Ns396p261 := nat_lit 30508924898007115256962940228529365126416031278295479981789970737601195062802649774887723909368469661111287808000 

noncomputable def Ns396p262 := BSN.sin_dyadic_bound_f 409032865 268435456 4 3 268435456 134217728 Ns396p257 Ns396p258 Ns396p259 Ns396p260 Ns396p261 Ns396p259 268138643 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 409032865) qz370 0 3 Ns396p257 Ns396p258 Ns396p259 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 409032865) qz371 0 3 Ns396p260 Ns396p261 Ns396p259 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p263 := nat_lit 212326131940058395823540820561 

noncomputable def Ns396p264 := BSN.cos_dyadic_bound_f 21465987 268435456 2 1 268435456 134217728 Ns396p263 Ns396p141 Ns396p263 Ns396p263 Ns396p142 Ns396p263 267577627 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 21465987) qz372 0 1 Ns396p263 Ns396p141 Ns396p263 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 21465987) qz373 0 1 Ns396p263 Ns396p142 Ns396p263 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p265 := Ns396p211 79751 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 237 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268138643 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 132 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267577627 268435456) qz36 rfl rfl (Ns396p244 RS397to408.d9 RS397to408.d11 RS397to408.d13 RS397to408.d17 (Ns396p250 rfl rfl) (Ns396p256 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns396p243 rfl) RS397to408.d19 RS397to408.d21 RS397to408.d23 RS397to408.d25 RS397to408.d17 (Ns396p262 rfl rfl) (Ns396p264 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns396p266 := nat_lit 33236264052643527095172513616158864247399130825262594058419999057230625 

noncomputable def Ns396p267 := nat_lit 4479450338050759682895052735284337217668863242222986234110125390625 

noncomputable def Ns396p268 := nat_lit 87040105789709536400250943671225612673407212097105099603863819232590625 

noncomputable def Ns396p269 := BSN.sin_dyadic_bound_f 214488045 268435456 3 2 268435456 134217728 Ns396p266 Ns396p121 Ns396p267 Ns396p268 Ns396p124 Ns396p267 192382352 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 214488045) qz370 0 2 Ns396p266 Ns396p121 Ns396p267 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 214488045) qz371 0 2 Ns396p268 Ns396p124 Ns396p267 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p270 := nat_lit 95209683805505006994847004492295499521142343355845098541190569910963105 

noncomputable def Ns396p271 := nat_lit 36740443887642152314214283083720367441090383180812170277732654877601 

noncomputable def Ns396p272 := nat_lit 249299211152885502454185807688162189579515800549682514570287544516053921 

noncomputable def Ns396p273 := BSN.sin_dyadic_bound_f 279024957 268435456 3 2 268435456 134217728 Ns396p270 Ns396p121 Ns396p271 Ns396p272 Ns396p124 Ns396p271 231424958 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 279024957) qz370 0 2 Ns396p270 Ns396p121 Ns396p271 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 279024957) qz371 0 2 Ns396p272 Ns396p124 Ns396p271 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p274 := Ns396p209 107533 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 192382352 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 231424958 268435456) qz36 rfl rfl (Ns396p265 rfl rfl) (Ns396p243 rfl) RS397to408.d27 RS397to408.d29 RS397to408.d31 RS397to408.d33 RS397to408.d17 (Ns396p269 rfl rfl) (Ns396p273 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p275 := nat_lit 128040440560646156797158652176 

noncomputable def Ns396p276 := BSN.sin_dyadic_bound_f 18916326 268435456 2 1 268435456 134217728 Ns396p275 Ns396p131 Ns396p275 Ns396p275 Ns396p132 Ns396p275 18900673 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 18916326) qz370 0 1 Ns396p275 Ns396p131 Ns396p275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 18916326) qz371 0 1 Ns396p275 Ns396p132 Ns396p275 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p277 := nat_lit 14054490639780718407491303342708607987629172365467423726420513414842599817566700689044861991935557116883640881 

noncomputable def Ns396p278 := nat_lit 17661418152093181712361764251640503629197088825121714390012255774395864408770963744071870335371042366001 

noncomputable def Ns396p279 := nat_lit 85094626298129653721069772887937749763982931628135980776101652209032133691405798561827381799315082781110575665 

noncomputable def Ns396p280 := BSN.cos_dyadic_bound_f 401715693 268435456 4 3 268435456 134217728 Ns396p277 Ns396p246 Ns396p278 Ns396p279 Ns396p249 Ns396p278 19923397 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 401715693) qz372 0 3 Ns396p277 Ns396p246 Ns396p278 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 401715693) qz373 0 3 Ns396p279 Ns396p249 Ns396p278 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p281 := Ns396p207 131807 BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 18900673 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 146 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 19923397 268435456) qz36 rfl rfl (Ns396p274 rfl) (Ns396p243 rfl) RS397to408.d35 RS397to408.d37 RS397to408.d39 RS397to408.d41 RS397to408.d17 (Ns396p276 rfl rfl) (Ns396p280 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p282 := nat_lit 14734035645744042438057056929194907150785903665984217883210102422569914217515863628345022762528358599619140625 

noncomputable def Ns396p283 := nat_lit 20340345111115884965977292318351526652581209526922297781749841083040347412673271634650290012359619140625 

noncomputable def Ns396p284 := nat_lit 89200482292097680194439357773714478848575795466490015947382469785751454606604320917575064065922646215619140625 

noncomputable def Ns396p285 := BSN.cos_dyadic_bound_f 406471275 268435456 4 3 268435456 134217728 Ns396p282 Ns396p246 Ns396p283 Ns396p284 Ns396p249 Ns396p283 15178054 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 406471275) qz372 0 3 Ns396p282 Ns396p246 Ns396p283 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 406471275) qz373 0 3 Ns396p284 Ns396p249 Ns396p283 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz394 := (BSN.cos_quad_nat0 196 rfl)

noncomputable def Ns396p286 := Ns396p205 Bool.false 153060972 131807 Bool.true 406471275 14148475504056880 1 Bool.false 15178054 Bool.false Bool.false 157860694 142984 BSN.abs_quadSignPos qz394 (BSN.sfrac_eq_quadSignPos_mul Bool.false 15178054 268435456) qz36 rfl (Ns396p281 rfl) (Ns396p243 rfl) RS397to408.d43 RS397to408.d45 RS397to408.d17 (Ns396p285 rfl rfl) rfl 

noncomputable def Ns396p287 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) 157860694 268435456 142984 268435456 157860694 268435456 142984 268435456 84750814756732928 78930347 67108864 17873 16777216 (Ns396p286 rfl rfl rfl rfl) 

noncomputable def Ns396p288 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35) 2541601 8388608 1 16777216 196698117881529 281474976710656 3252711404650983 109951162777600000000 499928133105811987929 2361183241434822606848 

noncomputable def Ns396p289 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz34 1 1 0 1 2541601 8388608 1 16777216 2541601 8388608 1 16777216 

noncomputable abbrev qz42 := qz384

noncomputable def Ns396p290 := @Enclosure.Real.IsNear.sqrt_image qz42 3981804579271 33554432000 745607 33554432000 182761570 182761605 16777216 (@Enclosure.Real.IsNear.of_eq qz42 (@HMul.hMul Real Real Real qz5 qz33 qz3) Bool.false 3981804579271 33554432000 745607 33554432000 (BSN.t_div_two_pi_mk qz33 745607 1000 qz36) (@Enclosure.Real.IsNear.mulLit_ff qz33 qz3 745607 1000 0 1 5340353 33554432 1 33554432 3981804579271 33554432000 745607 33554432000 (Enclosure.Real.IsNear.const Bool.false 745607 1000) RS397to408.d48 rfl)) 

noncomputable abbrev qz719 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 745607 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz601 := qz719

noncomputable abbrev qz395 := qz601

noncomputable abbrev qz43 := qz395

noncomputable def Ns396p291 := @Enclosure.Real.IsNear.sqrt_image qz43 365523175 33554432 35 33554432 55373552 55373558 16777216 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 365523175 33554432 35 33554432 365523175 33554432 35 33554432 (Ns396p290 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns396p292 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz43) 55373555 16777216 3 16777216 5083201 5083203 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz43) Bool.false 110747110 33554432 6 33554432 55373555 16777216 3 16777216 (Ns396p291 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns396p293 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz43)) Bool.false 10166404 33554432 2 33554432 2541601 8388608 1 16777216 (Ns396p292 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz44 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz385))

noncomputable abbrev qz602 := (@HMul.hMul Real Real Real qz707 qz718 qz718)

noncomputable abbrev qz396 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz602 qz597) qz593)

noncomputable abbrev qz45 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz396))

noncomputable def Ns396p294 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz35) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz44) qz45) Bool.false 196698117881529 

noncomputable def Ns396p295 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz44) qz45 21396573 16777216 185 

noncomputable def Ns396p296 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz44) Bool.false 42793146 33554432 370 33554432 21396573 16777216 185 

noncomputable def Ns396p297 := @Enclosure.Real.IsNear.recentre' qz44 Bool.false 26310286 33554432 1414804432 209715200000000 13155143 16777216 88425277 13107200000000 

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz349 qz346 qz385)

noncomputable def Ns396p298 := @Enclosure.Real.IsNear.cos_image qz46 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 188362701) qz392) Bool.false 188362701 33554432 221 33554432 Bool.false 26310286 33554432 1 

noncomputable def Ns396p299 := nat_lit 188902527914811598904793201 

noncomputable def Ns396p300 := nat_lit 28823037615171174400000000000000 

noncomputable def Ns396p301 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz35 884279719003555 140737488355328 1 500000000000000 29978855 33554432 35 33554432 26509693475448319829525 4722366482869645213696 Ns396p299 

noncomputable def Ns396p302 := @Enclosure.Real.IsNear.subLit_ff_p qz43 qz1 365523175 33554432 35 33554432 10 1 0 1 29978855 29978855 33554432 35 

noncomputable def Ns396p303 := @Ns396p302 33554432 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 365523175 33554432 35 33554432 365523175 33554432 35 33554432 (Ns396p290 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns396p304 := @Enclosure.Real.IsNear.recentre' qz46 Bool.false 26509693475448319829525 4722366482869645213696 Ns396p299 Ns396p300 188362701 33554432 221 33554432 (@Ns396p301 Ns396p300 RS397to408.d47 (Ns396p303 rfl rfl) rfl) 

noncomputable def Ns396p305 := nat_lit 4358211239273174340206592 

noncomputable def Ns396p306 := nat_lit 992452680894728630686301951571554710021928087321933011912994435189077935354444097597230625 

noncomputable def Ns396p307 := nat_lit 216484998249584058094956215062589496712361551006405976615570822545694332704420140174881 

noncomputable def Ns396p308 := nat_lit 2598930331393789944274827563101113381348467833808195135809988787020606325580117861099130401 

noncomputable def Ns396p309 := BSN.sin_dyadic_bound_f 61933906739 68719476736 3 2 33554432 12512208 Ns396p306 Ns396p175 Ns396p307 Ns396p308 Ns396p178 Ns396p307 26310286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 61933906739) qz368 0 2 Ns396p306 Ns396p175 Ns396p307 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 61933906739) qz369 0 2 Ns396p308 Ns396p178 Ns396p307 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p310 := @Ns396p298 6250000 (Ns396p304 rfl) (Enclosure.sfrac_false_div 188362701 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 188362701) qz392) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p305) qz393) 226375608064910080 72057594037927936 Bool.false 26310286 33554432 0 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 188362701 33554432 226375608064910080 72057594037927936 0 Ns396p305 Ns396p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 26310286 33554432 Ns396p305 Ns396p100 61933906739 68719476736 12512208 12500000 (Ns396p309 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p311 := @Enclosure.Real.IsNear.inv_image qz44 13155143 16777216 88425277 13107200000000 21396388 21396758 16777216 (Ns396p297 (Ns396p310 rfl rfl) rfl) rfl 

noncomputable def Ns396p312 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 9192973 16777216 

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz349 qz346 qz396)

noncomputable def Ns396p313 := @Enclosure.Real.IsNear.cos_image qz47 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 33248817)) qz392) Bool.true 33248817 33554432 

noncomputable def Ns396p314 := nat_lit 157013103595920845953061106445 

noncomputable def Ns396p315 := nat_lit 88323433108030828918610559495839973 

noncomputable def Ns396p316 := @Enclosure.Real.IsNear.recentre' qz47 Bool.true Ns396p314 Ns396p185 Ns396p315 

noncomputable abbrev qz48 := qz396

noncomputable def Ns396p317 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz48 884279719003555 140737488355328 1 500000000000000 177560448601999 

noncomputable abbrev qz397 := (@HSub.hSub Real Real Real qz583 qz602 qz597)

noncomputable abbrev qz49 := qz397

noncomputable def Ns396p318 := @Enclosure.Real.IsNear.subLit_tf qz49 qz29 107191704424335 1125899906842624 3272926195 1125899906842624 1 16 

noncomputable abbrev qz398 := qz602

noncomputable abbrev qz50 := qz398

noncomputable def Ns396p319 := @Enclosure.Real.IsNear.subLit_ff_n qz50 qz35 898731747111025 1125899906842624 2098521075 1125899906842624 29978855 33554432 35 33554432 

noncomputable def Ns396p320 := @Enclosure.Real.IsNear.mulLit_ff qz35 qz35 29978855 33554432 35 33554432 29978855 33554432 35 33554432 898731747111025 1125899906842624 

noncomputable def Ns396p321 := nat_lit 2604130748945410927972300909568578865137208112430681395581889921 

noncomputable def Ns396p322 := nat_lit 64791741944522487909851911563195676133695224709322207119351480320 

noncomputable def Ns396p323 := nat_lit 1493514973263577923549647356988855442942951086224347748576641 

noncomputable def Ns396p324 := nat_lit 7809405216889705628069803433991758884525738435119595491248516481 

noncomputable def Ns396p325 := nat_lit 2915628387503511955943336020343805426016285111919499320370816614400 

noncomputable def Ns396p326 := BSN.cos_dyadic_bound_f 33248817 33554432 3 2 16777216 6250000 Ns396p321 Ns396p322 Ns396p323 Ns396p324 Ns396p325 Ns396p323 9192973 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 33248817) (BSN.cosEvenQ 33554432) 0 2 Ns396p321 Ns396p322 Ns396p323 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 33248817) (BSN.cosOddQ 33554432) 0 2 Ns396p324 Ns396p325 Ns396p323 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p327 := @Ns396p312 1935527216 104857600000000 9192973 16777216 120970451 6553600000000 (@Ns396p313 307 16777216 Bool.false 9192973 16777216 1 6250000 (@Ns396p316 Ns396p188 33248817 33554432 307 16777216 (@Ns396p317 1125899906842624 3272926195 1125899906842624 Ns396p314 Ns396p185 Ns396p315 Ns396p188 RS397to408.d47 (@Ns396p318 0 1 2840967177631984 177560448601999 1125899906842624 3272926195 1125899906842624 (@Ns396p319 3596756757070447902720 107191704424335 1125899906842624 3272926195 1125899906842624 (@Ns396p320 2098521075 1125899906842624 (Ns396p303 rfl rfl) (Ns396p303 rfl rfl) rfl) (Ns396p303 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 33248817 33554432) (BSN.cos_neg_of_bound 33248817 33554432 Bool.false 9192973 16777216 1 6250000 (Ns396p326 rfl rfl)) rfl rfl) 

noncomputable def Ns396p328 := @Ns396p288 8305513786276781502087 Ns396p202 (Ns396p289 qz31 (@Enclosure.Real.IsNear.of_eq qz34 (@Inv.inv Real Real.instInv (Real.sqrt qz43)) Bool.false 2541601 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz42 (BSN.t_div_two_pi_nonneg qz33 745607 1000 qz36)) Ns396p293) rfl) (@Ns396p294 281474976710656 3252711404650983 109951162777600000000 (BSN.correction_mk qz35 (BSN.cos_two_pi_p_ne_zero_mk qz33 745607 1000 10 qz36 rfl rfl (@BSN.floor_sqrt_eq_dec qz33 745607 1000 10 qz36 rfl rfl rfl))) (@Ns396p295 16777216 9192973 16777216 120970451 6553600000000 196698117881529 281474976710656 3252711404650983 109951162777600000000 (@Ns396p296 16777216 (Ns396p311 rfl rfl rfl rfl rfl) rfl) (Ns396p327 rfl) rfl)) 

noncomputable def Ns396p329 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz33) (hardyZApproximantRS₀ qz33) Bool.false 2277186564842812596775 2361183241434822606848 990884079948299181502087 Ns396p202 (@Eq.refl Real (hardyZApproximantRS₀ qz33)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz33) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35))) Bool.false 2277186564842812596775 2361183241434822606848 990884079948299181502087 Ns396p202 (BSN.hardyZApproximantRS₀_eq qz33 10 (@BSN.floor_sqrt_eq_dec qz33 745607 1000 10 qz36 rfl rfl rfl)) (@Ns396p204 2277186564842812596775 2361183241434822606848 990884079948299181502087 Ns396p202 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10)) Bool.false 78930347 67108864 17873 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (Ns396p287 (Ns396p286 rfl rfl rfl rfl) rfl rfl)) (Ns396p328 rfl) rfl rfl)) 

theorem RS397to408.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz33) Bool.false 2277186564842812596775 2361183241434822606848 990884079948299181502087 Ns396p202 := Ns396p329 

noncomputable abbrev qz603 := (@HMul.hMul Real Real Real qz707 (Real.sqrt qz715) qz709)

noncomputable abbrev qz399 := qz603

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv qz399)

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz579 (@HMul.hMul Real Real Real qz579 qz603 qz603) qz603)

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz400))

noncomputable abbrev qz401 := (@HMul.hMul Real Real Real qz579 qz591 qz591)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz349 qz401 qz375))

noncomputable abbrev qz604 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz51)

noncomputable def Ns396p330 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz367 (@HAdd.hAdd Real Real Real qz367 qz604 qz52) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz53)) Bool.false 

noncomputable def Ns396p331 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz367 qz604 qz52) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz53) 17172201 1073741824 

noncomputable def Ns396p332 := @Enclosure.Real.IsNear.addLit_ff qz604 qz52 2146525 134217728 25 134217728 

noncomputable def Ns396p333 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz51 25 4 0 1 85861 33554432 1 33554432 2146525 

noncomputable def Ns396p334 := @Enclosure.Real.IsNear.recentre' qz51 Bool.false 85861 33554432 1 33554432 85861 33554432 1 33554432 

noncomputable def Ns396p335 := @Enclosure.Real.IsNear.mulLit_ff qz22 qz19 110698211 33554432 7 33554432 3974776674723 33554432000 744291 33554432000 440000667016365020553 1125899906842624000 110215124096499 

noncomputable def Ns396p336 := @Enclosure.Real.IsNear.sqrt_image qz19 3974776674723 33554432000 744291 33554432000 182600211 182600246 16777216 qz20 

noncomputable def Ns396p337 := @Enclosure.Real.IsNear.sqrt_image qz21 365200457 33554432 35 33554432 55349102 55349109 16777216 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 365200457 33554432 35 33554432 365200457 33554432 35 33554432 (Ns396p336 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz402 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 110698211 33554432 7 33554432 110698211 33554432 7 33554432 (Ns396p337 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns396p338 := @Ns396p335 1125899906842624000 qz402 

noncomputable def Ns396p339 := Ns396p338 qz20 

noncomputable abbrev qz54 := qz399

noncomputable def Ns396p340 := @Enclosure.Real.IsNear.inv_image qz54 440000667016365020553 1125899906842624000 110215124096499 1125899906842624000 42930 42931 16777216 (Ns396p339 rfl) rfl rfl 

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv qz400)

noncomputable def Ns396p341 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz55 1 32 0 1 1 

noncomputable def Ns396p342 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 1 33554432 1 33554432 

noncomputable def Ns396p343 := nat_lit 85184387403692086531136111100390551330933085423087774972652377 

noncomputable def Ns396p344 := nat_lit 1427247692705959881058285969449495136382746624000000000 

noncomputable def Ns396p345 := nat_lit 64013154190321913462263649152893073389482331269228592231 

noncomputable abbrev qz56 := qz400

noncomputable def Ns396p346 := @Enclosure.Real.IsNear.inv_image qz56 Ns396p343 Ns396p344 Ns396p345 Ns396p344 0 1 

noncomputable def Ns396p347 := nat_lit 193600586974846128917845231599700112425809 

noncomputable def Ns396p348 := nat_lit 1267650600228229401496703205376000000 

noncomputable def Ns396p349 := nat_lit 19397893676575117975704362888948979 

noncomputable def Ns396p350 := nat_lit 253530120045645880299340641075200000 

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz579 qz603 qz603)

noncomputable abbrev qz57 := qz403

noncomputable def Ns396p351 := @Enclosure.Real.IsNear.mulLit_ff qz57 qz54 Ns396p347 Ns396p348 Ns396p349 Ns396p350 440000667016365020553 1125899906842624000 110215124096499 

noncomputable def Ns396p352 := @Enclosure.Real.IsNear.mulLit_ff qz54 qz54 440000667016365020553 1125899906842624000 110215124096499 1125899906842624000 440000667016365020553 1125899906842624000 110215124096499 1125899906842624000 Ns396p347 

noncomputable def Ns396p353 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz53 13 10 0 1 934497 33554432 1 

noncomputable def Ns396p354 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 934497 33554432 1 33554432 934497 33554432 

noncomputable def Ns396p355 := nat_lit 1356506274215057298367931 

noncomputable abbrev qz58 := qz401

noncomputable def Ns396p356 := @Enclosure.Real.IsNear.mulLit_ff qz58 qz22 12254093918600521 1125899906842624 1549775003 1125899906842624 110698211 33554432 7 33554432 Ns396p355 

noncomputable def Ns396p357 := @Enclosure.Real.IsNear.mulLit_ff qz22 qz22 110698211 33554432 7 33554432 110698211 33554432 7 33554432 12254093918600521 1125899906842624 1549775003 

noncomputable def Ns396p358 := @Ns396p357 1125899906842624 qz402 

noncomputable def Ns396p359 := Ns396p358 qz402 

noncomputable def Ns396p360 := @Ns396p356 37778931862957161709568 257335988563248301 37778931862957161709568 (Ns396p359 rfl) qz402 

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz349 qz401 qz375)

noncomputable def Ns396p361 := @Enclosure.Real.IsNear.inv_image qz59 Ns396p355 37778931862957161709568 257335988563248301 37778931862957161709568 467248 467249 16777216 (Ns396p360 rfl) 

noncomputable def Ns396p362 := @Ns396p331 201 1073741824 12148461 335544320 13 335544320 18806345180381184 280236381 5368709120 1213 5368709120 (@Ns396p332 1 1073741824 1 1073741824 2304813802979328 17172201 1073741824 201 1073741824 (@Ns396p333 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns396p334 (Ns396p340 rfl rfl rfl rfl) rfl) rfl) (@Ns396p341 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns396p342 1 33554432 1 33554432 (@Ns396p346 16777216 (@Ns396p351 1125899906842624000 Ns396p343 Ns396p344 Ns396p345 Ns396p344 (@Ns396p352 Ns396p348 Ns396p349 Ns396p350 (Ns396p339 rfl) (Ns396p339 rfl) rfl) (Ns396p339 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns396p353 33554432 12148461 335544320 13 335544320 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns396p354 1 33554432 (Ns396p361 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS397to408.d52 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 := @Ns396p330 280236381 5368709120 1213 5368709120 (BSN.hardyZErrorBoundRS₀_mk qz4 744291 1000 qz9 rfl rfl) (Ns396p362 rfl rfl) 

noncomputable def Ns396p363 := nat_lit 92233720368547758080000000 

noncomputable def Ns396p364 := nat_lit 16962412100048648402425085952 

noncomputable abbrev qz720 := (Enclosure.sfrac Bool.false 746922 1000)

noncomputable abbrev qz605 := qz720

noncomputable abbrev qz404 := qz605

noncomputable abbrev qz60 := qz404

noncomputable abbrev qz721 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 746922 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz606 := qz721

noncomputable abbrev qz405 := qz606

noncomputable abbrev qz61 := (@HPow.hPow Real Real Real qz350 qz405 qz352)

noncomputable abbrev qz722 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 746922 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz607 := qz722

noncomputable abbrev qz406 := qz607

noncomputable abbrev qz62 := qz406

noncomputable def Ns396p365 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62)) 85823145 134217728 143237 134217728 32016272609842748289 147573952589676412928 800045731658481289553 Ns396p363 Ns396p364 

noncomputable def Ns396p366 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos BSN.quadSignPos 9 10 746922 1000 196 268435456 134217728 4503599627370496 Bool.false 378648140693 2508 618095470 44 84886744 8 

noncomputable def Ns396p367 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 746922 1000 90 146 268435456 134217728 4503599627370496 Bool.false 378648140693 2508 

noncomputable def Ns396p368 := Ns396p367 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 40207562 107724 Bool.true 331442473 Bool.true 334160946 14148475504056880 1 Bool.false 88526258 Bool.true Bool.false 85955372 Bool.true Bool.true 100158112 

noncomputable def Ns396p369 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 746922 1000 46 27 268435456 134217728 4503599627370496 Bool.false 378648140693 2508 

noncomputable def Ns396p370 := Ns396p369 480971758 44 109588312 8 522351262 44 101459064 8 Bool.false 24573586 79894 Bool.false 3511563 Bool.true 122758059 14148475504056880 1 Bool.false 268412487 Bool.true Bool.false 118523807 Bool.false Bool.true 40207562 

noncomputable def Ns396p371 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 746922 1000 238 132 268435456 134217728 4503599627370496 Bool.false 378648140693 2508 

noncomputable def Ns396p372 := Ns396p371 372130544 43 134217720 8 432030192 43 120047984 16 Bool.false 10246922 47068 Bool.false 341182580 Bool.false 296505092 14148475504056880 1 Bool.false 79274802 Bool.true Bool.false 120667314 Bool.false Bool.false 24573586 

noncomputable def Ns396p373 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 746922 1000 568 375 268435456 134217728 4503599627370496 Bool.false 378648140693 2508 

noncomputable def Ns396p374 := Ns396p373 186065264 43 189812528 16 294906480 43 154981288 8 Bool.true 268435352 2563 Bool.false 170482320 Bool.false 254467238 14148475504056880 1 Bool.false 216094479 Bool.false Bool.false 218031251 Bool.false Bool.false 10246922 

noncomputable def Ns396p375 := nat_lit 34471314016298501646725255635846468116870388713325247263 

noncomputable def Ns396p376 := nat_lit 24437787757084308051073035856295298609816547622912000 

noncomputable def Ns396p377 := nat_lit 111588126873653742741272345103360000 

noncomputable def Ns396p378 := nat_lit 500085865982688966277367678018567147520 

noncomputable abbrev qz608 := (@Eq.refl Real qz720)

noncomputable abbrev qz407 := qz608

noncomputable abbrev qz63 := qz407

noncomputable def Ns396p379 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz60 746922 1000 2231570896336 16000000 1493844 4000 2000 Ns396p377 Ns396p378 qz63 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns396p380 := nat_lit 6353752599484139823524399118799221003301550047640109575516160 

noncomputable abbrev qz609 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1493844))))

noncomputable abbrev qz408 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 746922 4000) (Real.log (Enclosure.sfrac Bool.false 2231570896336 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz609))

noncomputable abbrev qz610 := (Enclosure.sfrac Bool.false 746922 2000)

noncomputable abbrev qz64 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz408 qz610) (@HMul.hMul Real Real Real qz349 qz610 (Real.log Real.pi)))

noncomputable def Ns396p381 := @Enclosure.Real.IsNear.addLit_ft_p qz64 (Enclosure.sfrac Bool.true Ns396p377 Ns396p378) 12705325298676958313683 9007199254740992000 19127533025605713 2048000000000000000000 Ns396p377 Ns396p378 0 1 Ns396p380 

noncomputable def Ns396p382 := nat_lit 426319973772335687703310893056000 

noncomputable abbrev qz65 := (@HSub.hSub Real Real Real qz355 qz408 qz610)

noncomputable def Ns396p383 := @Enclosure.Real.IsNear.subLit_ff_p qz65 (@HMul.hMul Real Real Real qz5 qz610 (Real.log Real.pi)) 16556010765993071951059 9007199254740992000 7549226349087 2000000000000000000 14344921213821 33554432000 373461 67108864000 Ns396p382 12705325298676958313683 9007199254740992000 

noncomputable def Ns396p384 := nat_lit 33112021531986143902118000 

noncomputable abbrev qz66 := qz408

noncomputable def Ns396p385 := @Enclosure.Real.IsNear.subLit_ff_p qz66 qz610 19919848406867897564371 9007199254740992000 7549226349087 2000000000000000000 746922 2000 0 1 Ns396p384 16556010765993071951059 9007199254740992000 7549226349087 2000000000000000000 

noncomputable def Ns396p386 := nat_lit 44855510931223515932263186332813099008 

noncomputable def Ns396p387 := nat_lit 57281940272890354560139264 

noncomputable def Ns396p388 := nat_lit 5266600793496831212177360549488840551915020433162240 

noncomputable def Ns396p389 := nat_lit 1693797238396533556572574148230003784500369686528 

noncomputable def Ns396p390 := nat_lit 979405538730738429886180992574086543798632448 

noncomputable def Ns396p391 := BSN.log_dyadic_bound 134418896336 4328722896336 3 2 Ns396p388 134217728 50000000 Ns396p389 Ns396p390 8338349 4463141792672 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 134418896336) (BSN.artanhQ 4328722896336) 0 2 Ns396p389 Ns396p388 Ns396p390 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz409 := (Real.log (Enclosure.sfrac Bool.false 2231570896336 16000000))

noncomputable def Ns396p392 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 746922 4000) qz409 746922 4000 0 1 53347964093918311 4503599627370496 20000017 1000000000000000 19923384018478826344371 9007199254740992000 7469226348837 2000000000000000000 (Enclosure.Real.IsNear.const Bool.false 746922 4000) (BSN.isNear_log_sfrac 2231570896336 16000000 53347964093918311 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2231570896336) qz358)) Bool.false Ns396p387 Ns396p100 1000000850000000 50000000000000000000000 53347964093918311 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2231570896336 16000000 17 4463141792672 4194304000000 8338349 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns396p391 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns396p393 := BSN.arctan_dyadic_bound_f 1000 1493844 1 0 16777216 6250000 0 1 1 0 1 1 11230 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1493844) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1493844) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz410 := (@Nat.cast Real Real.instNatCast 1493844)

noncomputable def Ns396p394 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz410)) 884279719003555 562949953421312 1 2000000000000000 11230 16777216 1 6250000 14829429922165025669120 883902902732195 562949953421312 320000001 2000000000000000 qz15 (Ns396p393 rfl) rfl rfl 

noncomputable abbrev qz411 := (@HMul.hMul Real Real Real qz579 qz584 qz609)

noncomputable abbrev qz67 := qz411

noncomputable abbrev qz412 := qz609

noncomputable abbrev qz68 := qz412

noncomputable def Ns396p395 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 746922 4000) qz409) qz67 19923384018478826344371 9007199254740992000 7469226348837 2000000000000000000 883902902732195 2251799813685248 320000001 8000000000000000 Ns396p386 19919848406867897564371 9007199254740992000 7549226349087 2000000000000000000 (Ns396p392 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz68 1 4 0 1 883902902732195 562949953421312 320000001 2000000000000000 883902902732195 2251799813685248 320000001 8000000000000000 qz366 Ns396p394 rfl) 

noncomputable def Ns396p396 := @Ns396p381 Ns396p375 Ns396p376 19127533025605713 2048000000000000000000 (@Ns396p383 19127533025605713 2048000000000000000000 (Ns396p385 (Ns396p395 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 746922 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz610 (Real.log Real.pi) 746922 2000 0 1 38410761 33554432 1 67108864 14344921213821 33554432000 373461 67108864000 (Enclosure.Real.IsNear.const Bool.false 746922 2000) RS397to408.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns396p377 Ns396p378) 

noncomputable def Ns396p397 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz60) Bool.false Ns396p375 Ns396p376 19127533025605713 2048000000000000000000 23665508793 16777216 315 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz60) (@HAdd.hAdd Real Real Real qz367 qz64 (Enclosure.sfrac Bool.true Ns396p377 Ns396p378)) Bool.false Ns396p375 Ns396p376 19127533025605713 2048000000000000000000 Ns396p379 (Ns396p396 rfl rfl)) 

noncomputable def Ns396p398 := nat_lit 3795881762220315651342336 

noncomputable def Ns396p399 := nat_lit 2417851639229258349412352 

noncomputable def Ns396p400 := nat_lit 3503169715947181070271132964026101706982873420824028750287998363788232289260033318302503437972258913031580530239181512688200490386549438321 

noncomputable def Ns396p401 := nat_lit 2486305296416664793581584615155784326535249096111827855741109364758979618882981372321493157909157917313017541800329946387539913406321 

noncomputable def Ns396p402 := nat_lit 17494130332197076848639917501185866573181843867998244402067431931661010096655551536957917739929454203288799304330609643507283170376546842481 

noncomputable def Ns396p403 := BSN.sin_dyadic_bound_f 107885448477 68719476736 4 3 33554432 12512208 Ns396p400 Ns396p112 Ns396p401 Ns396p402 Ns396p115 Ns396p401 33554419 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107885448477) qz368 0 3 Ns396p400 Ns396p112 Ns396p401 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107885448477) qz369 0 3 Ns396p402 Ns396p115 Ns396p401 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz413 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable abbrev qz414 := (@Nat.cast Real Real.instNatCast Ns396p399)

noncomputable def Ns396p404 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz60) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23665508793) qz413) Bool.false 23665508793 16777216 315 33554432 Bool.true 33554419 33554432 1 6250000 (Ns396p397 rfl) (Enclosure.sfrac_false_div 23665508793 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23665508793) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p398) qz414) 226375608064910080 72057594037927936 Bool.false 33554419 33554432 224 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q1 23665508793 16777216 226375608064910080 72057594037927936 224 Ns396p398 Ns396p399 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554419 33554432 Ns396p398 Ns396p399 107885448477 68719476736 12512208 12500000 (Ns396p403 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p405 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz60) Bool.false Ns396p375 Ns396p376 19127533025605713 2048000000000000000000 378648140693 268435456 2508 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz60) (@HAdd.hAdd Real Real Real qz367 qz64 (Enclosure.sfrac Bool.true Ns396p377 Ns396p378)) Bool.false Ns396p375 Ns396p376 19127533025605713 2048000000000000000000 Ns396p379 (Ns396p396 rfl rfl)) 

noncomputable def Ns396p406 := Ns396p374 47068 BSN.abs_quadSignPos (BSN.cos_quad_nat0 568 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 216094479 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 375 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 218031251 268435456) qz63 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 1) Bool.true 33554419 33554432 125144027 13107200000000 268435352 268435456 2563 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz60)) Bool.true 33554419 33554432 125144027 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz60) qz60) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz60)) Bool.true 33554419 33554432 2002304432 209715200000000 33554419 33554432 125144027 13107200000000 (Ns396p404 rfl rfl) rfl)) rfl) (Ns396p405 rfl) RS397to408.d7 

noncomputable def Ns396p407 := nat_lit 7369333954835956326487743098333670747377004631105122043515686092800000 

noncomputable def Ns396p408 := nat_lit 713567028503513524105585470967209585913967839429984360857600000000 

noncomputable def Ns396p409 := nat_lit 22106574730450861952415018124059077822959185957636506161825343078400000 

noncomputable def Ns396p410 := BSN.cos_dyadic_bound_f 170482320 268435456 3 2 268435456 134217728 Ns396p407 Ns396p252 Ns396p408 Ns396p409 Ns396p255 Ns396p408 216094479 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 170482320) qz372 0 2 Ns396p407 Ns396p252 Ns396p408 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 170482320) qz373 0 2 Ns396p409 Ns396p255 Ns396p408 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p411 := nat_lit 65854395302014116852877207133141940483591738218381210681736005425373440 

noncomputable def Ns396p412 := nat_lit 17581462870232473444259716374355856798770823377947241902510767677696 

noncomputable def Ns396p413 := nat_lit 172447331993961358229101979141241839403161304476957922917656901537833216 

noncomputable def Ns396p414 := BSN.sin_dyadic_bound_f 254467238 268435456 3 2 268435456 134217728 Ns396p411 Ns396p121 Ns396p412 Ns396p413 Ns396p124 Ns396p412 218031251 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 254467238) qz370 0 2 Ns396p411 Ns396p121 Ns396p412 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 254467238) qz371 0 2 Ns396p413 Ns396p124 Ns396p412 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p415 := nat_lit 7302413096800847398124805850074147614241192073087362410060714098773965910303361109060583309690462797824000000 

noncomputable def Ns396p416 := nat_lit 2487953091381535523915489441492911437824277102480056529708543002721533128865415957937524736000000000000 

noncomputable def Ns396p417 := nat_lit 44255486750038095190204813337214364646030799506269404631018972627555654544884443589135125768591955040665600000 

noncomputable def Ns396p418 := BSN.cos_dyadic_bound_f 341182580 268435456 4 3 268435456 134217728 Ns396p415 Ns396p246 Ns396p416 Ns396p417 Ns396p249 Ns396p416 79274802 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 341182580) qz372 0 3 Ns396p415 Ns396p246 Ns396p416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 341182580) qz373 0 3 Ns396p417 Ns396p249 Ns396p416 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p419 := nat_lit 4162536562481993856753910874488133660374451112352478078244327806700696835587248335411954863962486962615484416 

noncomputable def Ns396p420 := nat_lit 461727639781527264744777075322213237228442555934004271143499855716520439472603043704647365485014286336 

noncomputable def Ns396p421 := nat_lit 25237815842364104049509196775127675902253926197152144253097596173367800618659640238770786501229126768299868160 

noncomputable def Ns396p422 := BSN.cos_dyadic_bound_f 296505092 268435456 4 3 268435456 134217728 Ns396p419 Ns396p246 Ns396p420 Ns396p421 Ns396p249 Ns396p420 120667314 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 296505092) qz372 0 3 Ns396p419 Ns396p246 Ns396p420 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 296505092) qz373 0 3 Ns396p421 Ns396p249 Ns396p420 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p423 := Ns396p372 79894 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 79274802 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 132 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 120667314 268435456) qz63 rfl rfl (Ns396p406 RS397to408.d9 RS397to408.d11 RS397to408.d13 RS397to408.d17 (Ns396p410 rfl rfl) (Ns396p414 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns396p405 rfl) RS397to408.d19 RS397to408.d21 RS397to408.d23 RS397to408.d25 RS397to408.d17 (Ns396p418 rfl rfl) (Ns396p422 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns396p424 := BSN.cos_dyadic_bound_f 3511563 268435456 1 0 268435456 134217728 0 1 1 0 1 1 268412487 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 3511563) qz372 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 3511563) qz373 0 0 rfl) rfl rfl 

noncomputable def Ns396p425 := nat_lit 3565723260244119976511815379614340157460921593850415642293263455380065 

noncomputable def Ns396p426 := nat_lit 51570352911484947032042233323964079035856177265157055452396020321 

noncomputable def Ns396p427 := nat_lit 9338715520067981343807178878231223518174450883416468808868767075295841 

noncomputable def Ns396p428 := BSN.sin_dyadic_bound_f 122758059 268435456 3 2 268435456 134217728 Ns396p425 Ns396p121 Ns396p426 Ns396p427 Ns396p124 Ns396p426 118523807 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 122758059) qz370 0 2 Ns396p425 Ns396p121 Ns396p426 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 122758059) qz371 0 2 Ns396p427 Ns396p124 Ns396p426 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p429 := Ns396p370 107724 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268412487 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 118523807 268435456) qz63 rfl rfl (Ns396p423 rfl rfl) (Ns396p405 rfl) RS397to408.d27 RS397to408.d29 RS397to408.d31 RS397to408.d33 RS397to408.d17 (Ns396p424 rfl rfl) (Ns396p428 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p430 := nat_lit 6502463474216944783248038486413719420584442452123437456711018890002852772202569584548450034789407331441570401 

noncomputable def Ns396p431 := nat_lit 1757510500987324702615284770471674727418730785514732780586485879877944746140700315552322661743026369121 

noncomputable def Ns396p432 := nat_lit 39411936601228955105233629860498869925658826390679227423203184489339197401763897015495602178883840724324971105 

noncomputable def Ns396p433 := BSN.cos_dyadic_bound_f 331442473 268435456 4 3 268435456 134217728 Ns396p430 Ns396p246 Ns396p431 Ns396p432 Ns396p249 Ns396p431 88526258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 331442473) qz372 0 3 Ns396p430 Ns396p246 Ns396p431 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 331442473) qz373 0 3 Ns396p432 Ns396p249 Ns396p431 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p434 := nat_lit 6718742254011872670515553943707531688678078107285284585157055114729300908365786590831922523585932751237943296 

noncomputable def Ns396p435 := nat_lit 1938511138689435150852030702020827123560286393509781355222725800237782310360090321583051872658559471616 

noncomputable def Ns396p436 := nat_lit 40721573372964244965358877011506252546856693669563621445556201152937334474525803802961181543068561859138949120 

noncomputable def Ns396p437 := BSN.cos_dyadic_bound_f 334160946 268435456 4 3 268435456 134217728 Ns396p434 Ns396p246 Ns396p435 Ns396p436 Ns396p249 Ns396p435 85955372 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 334160946) qz372 0 3 Ns396p434 Ns396p246 Ns396p435 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 334160946) qz373 0 3 Ns396p436 Ns396p249 Ns396p435 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p438 := Ns396p368 132041 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 88526258 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 146 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 85955372 268435456) qz63 rfl rfl (Ns396p429 rfl) (Ns396p405 rfl) RS397to408.d35 RS397to408.d37 RS397to408.d39 RS397to408.d41 RS397to408.d17 (Ns396p433 rfl rfl) (Ns396p437 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p439 := nat_lit 10791716002334248981329804117696852466705381929800235194201199037874059456532012364477539709434317754944000000 

noncomputable def Ns396p440 := nat_lit 8012185445463416993288905787381048555036951601363079121965198931202314220826792059349569601000000000000 

noncomputable def Ns396p441 := nat_lit 65369810052392515051224373304752973439886736708536456117728196254609117933931598991534648372431989599193600000 

noncomputable def Ns396p442 := BSN.cos_dyadic_bound_f 376108010 268435456 4 3 268435456 134217728 Ns396p439 Ns396p246 Ns396p440 Ns396p441 Ns396p249 Ns396p440 45331149 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 376108010) qz372 0 3 Ns396p439 Ns396p246 Ns396p440 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 376108010) qz373 0 3 Ns396p441 Ns396p249 Ns396p440 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p443 := Ns396p366 Bool.true 100158112 132041 Bool.true 376108010 14148475504056880 1 Bool.false 45331149 Bool.false Bool.true 85823145 143237 BSN.abs_quadSignPos qz394 (BSN.sfrac_eq_quadSignPos_mul Bool.false 45331149 268435456) qz63 rfl (Ns396p438 rfl) (Ns396p405 rfl) RS397to408.d43 RS397to408.d45 RS397to408.d17 (Ns396p442 rfl rfl) rfl 

noncomputable def Ns396p444 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) 85823145 268435456 143237 268435456 85823145 268435456 143237 268435456 46075950126858240 85823145 134217728 143237 134217728 (Ns396p443 rfl rfl rfl rfl) 

noncomputable def Ns396p445 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62) 10161927 33554432 1 33554432 3150610372407 4398046511104 628287545572633 21990232555520000000 32016272609842748289 147573952589676412928 

noncomputable def Ns396p446 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz61 1 1 0 1 10161927 33554432 1 33554432 10161927 33554432 1 33554432 

noncomputable abbrev qz69 := qz405

noncomputable def Ns396p447 := @Enclosure.Real.IsNear.sqrt_image qz69 1994413571733 16777216000 373461 16777216000 182922664 182922699 16777216 (@Enclosure.Real.IsNear.of_eq qz69 (@HMul.hMul Real Real Real qz5 qz60 qz3) Bool.false 1994413571733 16777216000 373461 16777216000 (BSN.t_div_two_pi_mk qz60 746922 1000 qz63) (@Enclosure.Real.IsNear.mulLit_ff qz60 qz3 746922 1000 0 1 5340353 33554432 1 33554432 1994413571733 16777216000 373461 16777216000 (Enclosure.Real.IsNear.const Bool.false 746922 1000) RS397to408.d48 rfl)) 

noncomputable abbrev qz723 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 746922 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz611 := qz723

noncomputable abbrev qz415 := qz611

noncomputable abbrev qz70 := qz415

noncomputable def Ns396p448 := @Enclosure.Real.IsNear.sqrt_image qz70 365845363 33554432 35 33554432 55397951 55397957 16777216 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 365845363 33554432 35 33554432 365845363 33554432 35 33554432 (Ns396p447 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns396p449 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz70) 27698977 8388608 3 16777216 5080963 5080964 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz70) Bool.false 110795908 33554432 6 33554432 27698977 8388608 3 16777216 (Ns396p448 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns396p450 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz70)) Bool.false 10161927 33554432 1 33554432 10161927 33554432 1 33554432 (Ns396p449 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz71 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz406))

noncomputable abbrev qz612 := (@HMul.hMul Real Real Real qz707 qz722 qz722)

noncomputable abbrev qz416 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz612 qz607) qz593)

noncomputable abbrev qz72 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz416))

noncomputable def Ns396p451 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz62) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz71) qz72) Bool.false 3150610372407 

noncomputable def Ns396p452 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz71) qz72 2557187 2097152 169 

noncomputable def Ns396p453 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz71) Bool.false 40914992 33554432 338 33554432 2557187 2097152 169 

noncomputable def Ns396p454 := @Enclosure.Real.IsNear.recentre' qz71 Bool.false 27518028 33554432 1414804432 209715200000000 6879507 8388608 88425277 13107200000000 

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz349 qz346 qz406)

noncomputable def Ns396p455 := @Enclosure.Real.IsNear.cos_image qz73 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47596767) qz377) Bool.false 47596767 8388608 221 33554432 Bool.false 27518028 33554432 1 

noncomputable def Ns396p456 := nat_lit 944512639576825568370293301 

noncomputable def Ns396p457 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz62 884279719003555 140737488355328 1 500000000000000 30301043 33554432 35 33554432 26794597789554637207865 4722366482869645213696 Ns396p456 

noncomputable def Ns396p458 := @Enclosure.Real.IsNear.subLit_ff_p qz70 qz1 365845363 33554432 35 33554432 10 1 0 1 30301043 30301043 33554432 35 

noncomputable def Ns396p459 := @Ns396p458 33554432 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 365845363 33554432 35 33554432 365845363 33554432 35 33554432 (Ns396p447 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns396p460 := @Enclosure.Real.IsNear.recentre' qz73 Bool.false 26794597789554637207865 4722366482869645213696 Ns396p456 Ns396p168 47596767 8388608 221 33554432 (@Ns396p457 Ns396p168 RS397to408.d47 (Ns396p459 rfl rfl) rfl) 

noncomputable def Ns396p461 := nat_lit 1286172102689996707381814925198290446782690713798608409450418140348095637621742374614830625 

noncomputable def Ns396p462 := nat_lit 363538409920319246185005239750495492297899453126254879418797309346984079257961625390625 

noncomputable def Ns396p463 := nat_lit 3367957397238691811982358605131164653633802889405579516851083743363212505261955233740590625 

noncomputable def Ns396p464 := BSN.sin_dyadic_bound_f 66079810355 68719476736 3 2 33554432 12512208 Ns396p461 Ns396p175 Ns396p462 Ns396p463 Ns396p178 Ns396p462 27518028 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 66079810355) qz368 0 2 Ns396p461 Ns396p175 Ns396p462 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 66079810355) qz369 0 2 Ns396p463 Ns396p178 Ns396p462 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p465 := @Ns396p455 6250000 (Ns396p460 rfl) (Enclosure.sfrac_false_div 47596767 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47596767) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1162488317553182616059904) qz594) 226375608064910080 72057594037927936 Bool.false 27518028 33554432 0 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 47596767 8388608 226375608064910080 72057594037927936 0 1162488317553182616059904 Ns396p173 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 27518028 33554432 1162488317553182616059904 Ns396p173 66079810355 68719476736 12512208 12500000 (Ns396p464 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p466 := @Enclosure.Real.IsNear.inv_image qz71 6879507 8388608 88425277 13107200000000 20457327 20457665 16777216 (Ns396p454 (Ns396p465 rfl rfl) rfl) rfl 

noncomputable def Ns396p467 := @Enclosure.Real.IsNear.recentre' qz72 Bool.false 9856488 16777216 

noncomputable abbrev qz74 := (@HMul.hMul Real Real Real qz349 qz346 qz416)

noncomputable def Ns396p468 := @Enclosure.Real.IsNear.cos_image qz74 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 988639)) (@Nat.cast Real Real.instNatCast 1048576)) Bool.true 988639 1048576 

noncomputable def Ns396p469 := nat_lit 149398903036019140473026300005 

noncomputable def Ns396p470 := nat_lit 88932054384429100022075748661505757 

noncomputable def Ns396p471 := @Enclosure.Real.IsNear.recentre' qz74 Bool.true Ns396p469 Ns396p185 Ns396p470 

noncomputable abbrev qz75 := qz416

noncomputable def Ns396p472 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz75 884279719003555 140737488355328 1 500000000000000 168949824162391 

noncomputable abbrev qz417 := (@HSub.hSub Real Real Real qz583 qz612 qz607)

noncomputable abbrev qz76 := qz417

noncomputable def Ns396p473 := @Enclosure.Real.IsNear.subLit_tf qz76 qz29 98581079984727 1125899906842624 3295479355 1125899906842624 1 16 

noncomputable abbrev qz418 := qz612

noncomputable abbrev qz77 := qz418

noncomputable def Ns396p474 := @Enclosure.Real.IsNear.subLit_ff_n qz77 qz62 918153206887849 1125899906842624 2121074235 1125899906842624 30301043 33554432 35 33554432 

noncomputable def Ns396p475 := @Enclosure.Real.IsNear.mulLit_ff qz62 qz62 30301043 33554432 35 33554432 30301043 33554432 35 33554432 918153206887849 1125899906842624 

noncomputable def Ns396p476 := nat_lit 1941172460733822080692760092901603489074136852578561 

noncomputable def Ns396p477 := nat_lit 58927746017182005661972572455120531352527200132792320 

noncomputable def Ns396p478 := nat_lit 912645062749574507825919699102543445701923815681 

noncomputable def Ns396p479 := nat_lit 5821692092075967093062628439306605380331006710104321 

noncomputable def Ns396p480 := nat_lit 2651748570773190254788765760480423910863724005975654400 

noncomputable def Ns396p481 := BSN.cos_dyadic_bound_f 988639 1048576 3 2 16777216 6250000 Ns396p476 Ns396p477 Ns396p478 Ns396p479 Ns396p480 Ns396p478 9856488 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 988639) (BSN.cosEvenQ 1048576) 0 2 Ns396p476 Ns396p477 Ns396p478 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 988639) (BSN.cosOddQ 1048576) 0 2 Ns396p479 Ns396p480 Ns396p478 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p482 := @Ns396p467 1948027216 104857600000000 1232061 2097152 121751701 6553600000000 (@Ns396p468 309 16777216 Bool.false 9856488 16777216 1 6250000 (@Ns396p471 Ns396p188 988639 1048576 309 16777216 (@Ns396p472 1125899906842624 3295479355 1125899906842624 Ns396p469 Ns396p185 Ns396p470 Ns396p188 RS397to408.d47 (@Ns396p473 0 1 2703197186598256 168949824162391 1125899906842624 3295479355 1125899906842624 (@Ns396p474 3307832144834083160064 98581079984727 1125899906842624 3295479355 1125899906842624 (@Ns396p475 2121074235 1125899906842624 (Ns396p459 rfl rfl) (Ns396p459 rfl rfl) rfl) (Ns396p459 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 988639 1048576) (BSN.cos_neg_of_bound 988639 1048576 Bool.false 9856488 16777216 1 6250000 (Ns396p481 rfl rfl)) rfl rfl) 

noncomputable def Ns396p483 := @Ns396p445 800045731658481289553 Ns396p363 (Ns396p446 qz31 (@Enclosure.Real.IsNear.of_eq qz61 (@Inv.inv Real Real.instInv (Real.sqrt qz70)) Bool.false 10161927 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz69 (BSN.t_div_two_pi_nonneg qz60 746922 1000 qz63)) Ns396p450) rfl) (@Ns396p451 4398046511104 628287545572633 21990232555520000000 (BSN.correction_mk qz62 (BSN.cos_two_pi_p_ne_zero_mk qz60 746922 1000 10 qz63 rfl rfl (@BSN.floor_sqrt_eq_dec qz60 746922 1000 10 qz63 rfl rfl rfl))) (@Ns396p452 16777216 1232061 2097152 121751701 6553600000000 3150610372407 4398046511104 628287545572633 21990232555520000000 (@Ns396p453 16777216 (Ns396p466 rfl rfl rfl rfl rfl) rfl) (Ns396p482 rfl) rfl)) 

noncomputable def Ns396p484 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz60) (hardyZApproximantRS₀ qz60) Bool.true 126379818469648423809 147573952589676412928 99231762624002801289553 Ns396p363 (@Eq.refl Real (hardyZApproximantRS₀ qz60)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz60) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62))) Bool.true 126379818469648423809 147573952589676412928 99231762624002801289553 Ns396p363 (BSN.hardyZApproximantRS₀_eq qz60 10 (@BSN.floor_sqrt_eq_dec qz60 746922 1000 10 qz63 rfl rfl rfl)) (@Ns396p365 126379818469648423809 147573952589676412928 99231762624002801289553 Ns396p363 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10)) Bool.true 85823145 134217728 143237 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (Ns396p444 (Ns396p443 rfl rfl rfl rfl) rfl rfl)) (Ns396p483 rfl) rfl rfl)) 

theorem RS397to408.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz60) Bool.true 126379818469648423809 147573952589676412928 99231762624002801289553 Ns396p363 := Ns396p484 

noncomputable def Ns396p485 := nat_lit 461168601842738790400000000 

noncomputable def Ns396p486 := nat_lit 161447803538638717031809024 

noncomputable abbrev qz724 := (Enclosure.sfrac Bool.false 748073 1000)

noncomputable abbrev qz613 := qz724

noncomputable abbrev qz419 := qz613

noncomputable abbrev qz78 := qz419

noncomputable abbrev qz725 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 748073 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz614 := qz725

noncomputable abbrev qz420 := qz614

noncomputable abbrev qz79 := (@HPow.hPow Real Real Real qz350 qz420 qz352)

noncomputable abbrev qz726 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 748073 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz615 := qz726

noncomputable abbrev qz421 := qz615

noncomputable abbrev qz80 := qz421

noncomputable def Ns396p487 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80)) 64758101 134217728 71727 67108864 1022191535107567385 4611686018427387904 4013051692228065166909 Ns396p485 Ns396p486 

noncomputable def Ns396p488 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.cos BSN.quadSignPos 9 10 748073 1000 196 268435456 134217728 4503599627370496 Bool.false 379386400018 2512 618095470 44 84886744 8 

noncomputable def Ns396p489 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 748073 1000 90 146 268435456 134217728 4503599627370496 Bool.false 379386400018 2512 

noncomputable def Ns396p490 := Ns396p489 558195838 44 94906264 8 589812974 44 89478488 8 Bool.false 149320355 107886 Bool.true 235666558 Bool.true 274776354 14148475504056880 1 Bool.false 171462616 Bool.true Bool.false 139660648 Bool.true Bool.false 42145616 

noncomputable def Ns396p491 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 748073 1000 46 26 268435456 134217728 4503599627370496 Bool.false 379386400018 2512 

noncomputable def Ns396p492 := Ns396p491 480971758 44 109588312 8 522351262 44 101459064 8 Bool.false 238460592 80013 Bool.false 188172395 Bool.true 407382465 14148475504056880 1 Bool.false 205138282 Bool.true Bool.false 14268236 Bool.true Bool.false 149320355 

noncomputable def Ns396p493 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 748073 1000 239 133 268435456 134217728 4503599627370496 Bool.false 379386400018 2512 

noncomputable def Ns396p494 := Ns396p493 372130544 43 134217720 8 432030192 43 120047984 16 Bool.false 187412565 47136 Bool.false 229462220 Bool.false 115840238 14148475504056880 1 Bool.false 202520711 Bool.false Bool.false 112278166 Bool.true Bool.false 238460592 

noncomputable def Ns396p495 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 748073 1000 569 376 268435456 134217728 4503599627370496 Bool.false 379386400018 2512 

noncomputable def Ns396p496 := Ns396p495 186065264 43 189812528 16 294906480 43 154981288 8 Bool.false 248051328 2563 Bool.false 272923098 Bool.false 231631776 14148475504056880 1 Bool.false 228273653 Bool.true Bool.false 174547557 Bool.false Bool.false 187412565 

noncomputable def Ns396p497 := nat_lit 40157680324631087788699974853566078188874522258184700326487 

noncomputable def Ns396p498 := nat_lit 28413631140469458251276506717976357456104555894800384000 

noncomputable def Ns396p499 := nat_lit 112450561834925930296408885564640000 

noncomputable def Ns396p500 := nat_lit 504727480085688609024368153618957632320 

noncomputable abbrev qz616 := (@Eq.refl Real qz724)

noncomputable abbrev qz422 := qz616

noncomputable abbrev qz81 := qz422

noncomputable def Ns396p501 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz78 748073 1000 2238453853316 16000000 1496146 4000 2000 Ns396p499 Ns396p500 qz81 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns396p502 := nat_lit 12850457703881948092383991953141145020439847122619104104475840 

noncomputable abbrev qz617 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1496146))))

noncomputable abbrev qz423 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 748073 4000) (Real.log (Enclosure.sfrac Bool.false 2238453853316 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz617))

noncomputable abbrev qz618 := (Enclosure.sfrac Bool.false 748073 2000)

noncomputable abbrev qz82 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz423 qz618) (@HMul.hMul Real Real Real qz349 qz618 (Real.log Real.pi)))

noncomputable def Ns396p503 := @Enclosure.Real.IsNear.addLit_ft_p qz82 (Enclosure.sfrac Bool.true Ns396p499 Ns396p500) 25460194335821645700287 18014398509481984000 38313764283669909 4096000000000000000000 Ns396p499 Ns396p500 0 1 Ns396p502 

noncomputable def Ns396p504 := nat_lit 341720943819245029911349008793600 

noncomputable abbrev qz83 := (@HSub.hSub Real Real Real qz355 qz423 qz618)

noncomputable def Ns396p505 := @Enclosure.Real.IsNear.subLit_ff_p qz83 (@HMul.hMul Real Real Real qz5 qz618 (Real.log Real.pi)) 6634686602586002127091 3602879701896396800 15121472717741 4000000000000000000 28734053213553 67108864000 748073 134217728000 Ns396p504 25460194335821645700287 18014398509481984000 

noncomputable def Ns396p506 := nat_lit 66346866025860021270910000 

noncomputable abbrev qz84 := qz423

noncomputable def Ns396p507 := @Enclosure.Real.IsNear.subLit_ff_p qz84 qz618 39911475581021868743871 18014398509481984000 15121472717741 4000000000000000000 748073 2000 0 1 Ns396p506 6634686602586002127091 3602879701896396800 15121472717741 4000000000000000000 

noncomputable def Ns396p508 := nat_lit 89872653277248369205303336209123115008 

noncomputable def Ns396p509 := nat_lit 57296832343792579088744448 

noncomputable def Ns396p510 := nat_lit 5300177752432225725769299033929866948358220833591040 

noncomputable def Ns396p511 := nat_lit 1877768279180938731958775456519273552235196581888 

noncomputable def Ns396p512 := nat_lit 1195949074596324077351229672463519562758718208 

noncomputable def Ns396p513 := BSN.log_dyadic_bound 141301853316 4335605853316 3 2 Ns396p510 134217728 50000000 Ns396p511 Ns396p512 8751687 4476907706632 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 141301853316) (BSN.artanhQ 4335605853316) 0 2 Ns396p511 Ns396p510 Ns396p512 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz424 := (Real.log (Enclosure.sfrac Bool.false 2238453853316 16000000))

noncomputable def Ns396p514 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 748073 4000) qz424 748073 4000 0 1 53361833415732327 4503599627370496 20000017 1000000000000000 39918546808807129055871 18014398509481984000 14961472717241 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 748073 4000) (BSN.isNear_log_sfrac 2238453853316 16000000 53361833415732327 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2238453853316) qz358)) Bool.false Ns396p509 Ns396p100 1000000850000000 50000000000000000000000 53361833415732327 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2238453853316 16000000 17 4476907706632 4194304000000 8751687 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns396p513 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns396p515 := BSN.arctan_dyadic_bound_f 1000 1496146 1 0 16777216 6250000 0 1 1 0 1 1 11213 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1496146) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1496146) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz425 := (@Nat.cast Real Real.instNatCast 1496146)

noncomputable def Ns396p516 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz425)) 884279719003555 562949953421312 1 2000000000000000 11213 16777216 1 6250000 14829439492314233831424 883903473157539 562949953421312 320000001 2000000000000000 qz15 (Ns396p515 rfl) rfl rfl 

noncomputable abbrev qz426 := (@HMul.hMul Real Real Real qz579 qz584 qz617)

noncomputable abbrev qz85 := qz426

noncomputable abbrev qz427 := qz617

noncomputable abbrev qz86 := qz427

noncomputable def Ns396p517 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 748073 4000) qz424) qz85 39918546808807129055871 18014398509481984000 14961472717241 4000000000000000000 883903473157539 2251799813685248 320000001 8000000000000000 Ns396p508 39911475581021868743871 18014398509481984000 15121472717741 4000000000000000000 (Ns396p514 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz86 1 4 0 1 883903473157539 562949953421312 320000001 2000000000000000 883903473157539 2251799813685248 320000001 8000000000000000 qz366 Ns396p516 rfl) 

noncomputable def Ns396p518 := @Ns396p503 Ns396p497 Ns396p498 38313764283669909 4096000000000000000000 (@Ns396p505 38313764283669909 4096000000000000000000 (Ns396p507 (Ns396p517 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 748073 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz618 (Real.log Real.pi) 748073 2000 0 1 38410761 33554432 1 67108864 28734053213553 67108864000 748073 134217728000 (Enclosure.Real.IsNear.const Bool.false 748073 2000) RS397to408.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns396p499 Ns396p500) 

noncomputable def Ns396p519 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz78) Bool.false Ns396p497 Ns396p498 38313764283669909 4096000000000000000000 23711650001 16777216 315 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz78) (@HAdd.hAdd Real Real Real qz367 qz82 (Enclosure.sfrac Bool.true Ns396p499 Ns396p500)) Bool.false Ns396p497 Ns396p498 38313764283669909 4096000000000000000000 Ns396p501 (Ns396p518 rfl rfl)) 

noncomputable def Ns396p520 := nat_lit 2849625683914824353841152 

noncomputable def Ns396p521 := nat_lit 2903556087059064543224938256233467210245449497127603521579647859318415075622656658770173025 

noncomputable def Ns396p522 := nat_lit 1851416341455407852200578619399880874857045371875265698721429511342271577571919484099681 

noncomputable def Ns396p523 := nat_lit 7601554125363765048114132591418147648274027752351163554910671602815580567886127189042863201 

noncomputable def Ns396p524 := BSN.sin_dyadic_bound_f 80991233173 68719476736 3 2 33554432 12512208 Ns396p521 Ns396p175 Ns396p522 Ns396p523 Ns396p178 Ns396p522 31006416 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 80991233173) qz368 0 2 Ns396p521 Ns396p175 Ns396p522 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 80991233173) qz369 0 2 Ns396p523 Ns396p178 Ns396p522 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p525 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz78) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23711650001) qz413) Bool.false 23711650001 16777216 315 33554432 Bool.false 31006416 33554432 1 6250000 (Ns396p519 rfl) (Enclosure.sfrac_false_div 23711650001 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23711650001) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p520) qz414) 226375608064910080 72057594037927936 Bool.false 31006416 33554432 224 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 23711650001 16777216 226375608064910080 72057594037927936 224 Ns396p520 Ns396p399 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 31006416 33554432 Ns396p520 Ns396p399 80991233173 68719476736 12512208 12500000 (Ns396p524 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p526 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz78) Bool.false Ns396p497 Ns396p498 38313764283669909 4096000000000000000000 379386400018 268435456 2512 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz78) (@HAdd.hAdd Real Real Real qz367 qz82 (Enclosure.sfrac Bool.true Ns396p499 Ns396p500)) Bool.false Ns396p497 Ns396p498 38313764283669909 4096000000000000000000 Ns396p501 (Ns396p518 rfl rfl)) 

noncomputable def Ns396p527 := Ns396p496 47136 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 569 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 228273653 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 376 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 174547557 268435456) qz81 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 1) Bool.false 1937901 2097152 125144027 13107200000000 248051328 268435456 2563 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz78)) Bool.false 1937901 2097152 125144027 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz78) qz78) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz78)) Bool.false 31006416 33554432 2002304432 209715200000000 1937901 2097152 125144027 13107200000000 (Ns396p525 rfl rfl) rfl)) rfl) (Ns396p526 rfl) RS397to408.d7 

noncomputable def Ns396p528 := nat_lit 87147695409314467279443155842268930533555504210541128069260353275633920 

noncomputable def Ns396p529 := nat_lit 30783807821634441269121815532084492393121241945943702026932243865856 

noncomputable def Ns396p530 := nat_lit 228194123716493339493629687123652395552580314731123807520971606374686976 

noncomputable def Ns396p531 := BSN.sin_dyadic_bound_f 272923098 268435456 3 2 268435456 134217728 Ns396p528 Ns396p121 Ns396p529 Ns396p530 Ns396p124 Ns396p529 228273653 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 272923098) qz370 0 2 Ns396p528 Ns396p121 Ns396p529 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 272923098) qz371 0 2 Ns396p530 Ns396p124 Ns396p529 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p532 := nat_lit 25119132752868657351887549835802616619547671619525681226754348973817856 

noncomputable def Ns396p533 := nat_lit 8286766402048498178438132423848086712056172789052028368851436568576 

noncomputable def Ns396p534 := nat_lit 75340824725801875059305773242560153685218902512998939623525344048316416 

noncomputable def Ns396p535 := BSN.cos_dyadic_bound_f 231631776 268435456 3 2 268435456 134217728 Ns396p532 Ns396p252 Ns396p533 Ns396p534 Ns396p255 Ns396p533 174547557 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 231631776) qz372 0 2 Ns396p532 Ns396p252 Ns396p533 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 231631776) qz373 0 2 Ns396p534 Ns396p255 Ns396p533 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p536 := nat_lit 43537425001744861415176565123044902406997769203523816621025868554240000 

noncomputable def Ns396p537 := nat_lit 7685807942087897966340499244081306725498841864641255415833600000000 

noncomputable def Ns396p538 := nat_lit 114014145601235066157326452609198612759819540265257719593918306099200000 

noncomputable def Ns396p539 := BSN.sin_dyadic_bound_f 229462220 268435456 3 2 268435456 134217728 Ns396p536 Ns396p121 Ns396p537 Ns396p538 Ns396p124 Ns396p537 202520711 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 229462220) qz370 0 2 Ns396p536 Ns396p121 Ns396p537 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 229462220) qz371 0 2 Ns396p538 Ns396p124 Ns396p537 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p540 := nat_lit 180068507338887487387523802462736 

noncomputable def Ns396p541 := BSN.sin_dyadic_bound_f 115840238 268435456 2 1 268435456 134217728 Ns396p540 Ns396p131 Ns396p540 Ns396p540 Ns396p132 Ns396p540 112278166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 115840238) qz370 0 1 Ns396p540 Ns396p131 Ns396p540 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 115840238) qz371 0 1 Ns396p540 Ns396p132 Ns396p540 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p542 := Ns396p494 80013 BSN.abs_quadSignPos (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 202520711 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 133 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 112278166 268435456) qz81 rfl rfl (Ns396p527 RS397to408.d9 RS397to408.d11 RS397to408.d13 RS397to408.d17 (Ns396p531 rfl rfl) (Ns396p535 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns396p526 rfl) RS397to408.d19 RS397to408.d21 RS397to408.d23 RS397to408.d25 RS397to408.d17 (Ns396p539 rfl rfl) (Ns396p541 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns396p543 := nat_lit 10938426775140474794248726638173424497385385219236403441718092535190625 

noncomputable def Ns396p544 := nat_lit 1571981027213237100043271717929943879681776415663374226462250390625 

noncomputable def Ns396p545 := nat_lit 32812136363366997908546093371084413604396792104877883576701353104790625 

noncomputable def Ns396p546 := BSN.cos_dyadic_bound_f 188172395 268435456 3 2 268435456 134217728 Ns396p543 Ns396p252 Ns396p544 Ns396p545 Ns396p255 Ns396p544 205138282 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 188172395) qz372 0 2 Ns396p543 Ns396p252 Ns396p544 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 188172395) qz373 0 2 Ns396p545 Ns396p255 Ns396p544 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p547 := nat_lit 14867015827532404777836760245381693955138482375013592660453615485956869879492304776601018006836516208696890625 

noncomputable def Ns396p548 := nat_lit 20894307422261240019221747532061593640655288201848134434784425860689830759796240336573853836230712890625 

noncomputable def Ns396p549 := nat_lit 90003865821966384520780504287184323204462203614290552780430277694267418930379637967797996409146443913682490625 

noncomputable def Ns396p550 := BSN.cos_dyadic_bound_f 407382465 268435456 4 3 268435456 134217728 Ns396p547 Ns396p246 Ns396p548 Ns396p549 Ns396p249 Ns396p548 14268236 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 407382465) qz372 0 3 Ns396p547 Ns396p246 Ns396p548 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 407382465) qz373 0 3 Ns396p549 Ns396p249 Ns396p548 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p551 := Ns396p492 107886 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 205138282 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 14268236 268435456) qz81 rfl rfl (Ns396p542 rfl rfl) (Ns396p526 rfl) RS397to408.d27 RS397to408.d29 RS397to408.d31 RS397to408.d33 RS397to408.d17 (Ns396p546 rfl rfl) (Ns396p550 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p552 := nat_lit 26916226521381353135540294097648358080821545769332539327856871144816896 

noncomputable def Ns396p553 := nat_lit 9514449614653236145522389574714314592817464223378430776423540982016 

noncomputable def Ns396p554 := nat_lit 80729650664914752934329837513795645613279002379550861122017766352486656 

noncomputable def Ns396p555 := BSN.cos_dyadic_bound_f 235666558 268435456 3 2 268435456 134217728 Ns396p552 Ns396p252 Ns396p553 Ns396p554 Ns396p255 Ns396p553 171462616 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 235666558) qz372 0 2 Ns396p552 Ns396p252 Ns396p553 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 235666558) qz373 0 2 Ns396p554 Ns396p255 Ns396p553 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p556 := nat_lit 3069346538919537123945159571803932206089188363455704064625152585454410895900275426190596082682166573078941696 

noncomputable def Ns396p557 := nat_lit 185247467337769118475990993966752821353609913024169914906036047269325996517488516045853376891467862016 

noncomputable def Ns396p558 := nat_lit 18612594220018700461679608944852932114700462897120433572314932168642160413765184734136466735181106740453969920 

noncomputable def Ns396p559 := BSN.cos_dyadic_bound_f 274776354 268435456 4 3 268435456 134217728 Ns396p556 Ns396p246 Ns396p557 Ns396p558 Ns396p249 Ns396p557 139660648 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 274776354) qz372 0 3 Ns396p556 Ns396p246 Ns396p557 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 274776354) qz373 0 3 Ns396p558 Ns396p249 Ns396p557 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p560 := Ns396p490 132240 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 171462616 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 146 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 139660648 268435456) qz81 rfl rfl (Ns396p551 rfl) (Ns396p526 rfl) RS397to408.d35 RS397to408.d37 RS397to408.d39 RS397to408.d41 RS397to408.d17 (Ns396p555 rfl rfl) (Ns396p559 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p561 := nat_lit 8021638284583646459849941329063770545751992203028572518758394042662339114572988576531788706386003660519283921 

noncomputable def Ns396p562 := nat_lit 3296351052945744959245648304158453148541372485745975052661405805547509871425244798624532026065376812241 

noncomputable def Ns396p563 := nat_lit 48609331489003231723481716575236796818467170904798674282751079853024869431812977705230427416459050955479489745 

noncomputable def Ns396p564 := BSN.cos_dyadic_bound_f 349276571 268435456 4 3 268435456 134217728 Ns396p561 Ns396p246 Ns396p562 Ns396p563 Ns396p249 Ns396p562 71506958 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 349276571) qz372 0 3 Ns396p561 Ns396p246 Ns396p562 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 349276571) qz373 0 3 Ns396p563 Ns396p249 Ns396p562 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p565 := Ns396p488 Bool.false 42145616 132240 Bool.true 349276571 14148475504056880 1 Bool.false 71506958 Bool.false Bool.false 64758101 143454 BSN.abs_quadSignPos qz394 (BSN.sfrac_eq_quadSignPos_mul Bool.false 71506958 268435456) qz81 rfl (Ns396p560 rfl) (Ns396p526 rfl) RS397to408.d43 RS397to408.d45 RS397to408.d17 (Ns396p564 rfl rfl) rfl 

noncomputable def Ns396p566 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) 64758101 268435456 143454 268435456 64758101 268435456 143454 268435456 34766740743258112 64758101 134217728 71727 67108864 (Ns396p565 rfl rfl rfl rfl) 

noncomputable def Ns396p567 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80) 158719 524288 1 16777216 6440259421415 8796093022208 786162395368101 27487790694400000000 1022191535107567385 4611686018427387904 

noncomputable def Ns396p568 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz79 1 1 0 1 158719 524288 1 16777216 158719 524288 1 16777216 

noncomputable abbrev qz87 := qz420

noncomputable def Ns396p569 := @Enclosure.Real.IsNear.sqrt_image qz87 3994973889769 33554432000 748073 33554432000 183063550 183063586 16777216 (@Enclosure.Real.IsNear.of_eq qz87 (@HMul.hMul Real Real Real qz5 qz78 qz3) Bool.false 3994973889769 33554432000 748073 33554432000 (BSN.t_div_two_pi_mk qz78 748073 1000 qz81) (@Enclosure.Real.IsNear.mulLit_ff qz78 qz3 748073 1000 0 1 5340353 33554432 1 33554432 3994973889769 33554432000 748073 33554432000 (Enclosure.Real.IsNear.const Bool.false 748073 1000) RS397to408.d48 rfl)) 

noncomputable abbrev qz727 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 748073 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz619 := qz727

noncomputable abbrev qz428 := qz619

noncomputable abbrev qz88 := qz428

noncomputable def Ns396p570 := @Enclosure.Real.IsNear.sqrt_image qz88 11441473 1048576 9 8388608 55419281 55419287 16777216 (@Enclosure.Real.IsNear.recentre' qz88 Bool.false 366127136 33554432 36 33554432 11441473 1048576 9 8388608 (Ns396p569 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns396p571 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz88) 13854821 4194304 3 16777216 5079007 5079009 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz88) Bool.false 110838568 33554432 6 33554432 13854821 4194304 3 16777216 (Ns396p570 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns396p572 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz88)) Bool.false 10158016 33554432 2 33554432 158719 524288 1 16777216 (Ns396p571 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz89 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz421))

noncomputable abbrev qz620 := (@HMul.hMul Real Real Real qz707 qz726 qz726)

noncomputable abbrev qz429 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz620 qz615) qz593)

noncomputable abbrev qz90 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz429))

noncomputable def Ns396p573 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz80) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz89) qz90) Bool.false 6440259421415 

noncomputable def Ns396p574 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz89) qz90 39515885 33554432 323 

noncomputable def Ns396p575 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz89) Bool.false 39515885 33554432 323 33554432 39515885 33554432 323 

noncomputable def Ns396p576 := @Enclosure.Real.IsNear.recentre' qz89 Bool.false 28492337 33554432 1452304432 209715200000000 28492337 33554432 90769027 13107200000000 

noncomputable abbrev qz91 := (@HMul.hMul Real Real Real qz349 qz346 qz421)

noncomputable def Ns396p577 := @Enclosure.Real.IsNear.cos_image qz91 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48039375) qz377) Bool.false 48039375 8388608 227 33554432 Bool.false 28492337 33554432 1 

noncomputable def Ns396p578 := nat_lit 242874678747072506366313471 

noncomputable def Ns396p579 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns396p580 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz80 884279719003555 140737488355328 1 500000000000000 955713 1048576 9 8388608 845117623088044559715 147573952589676412928 Ns396p578 

noncomputable def Ns396p581 := @Enclosure.Real.IsNear.subLit_ff_p qz88 qz1 11441473 1048576 9 8388608 10 1 0 1 955713 955713 1048576 9 

noncomputable def Ns396p582 := @Ns396p581 8388608 (@Enclosure.Real.IsNear.recentre' qz88 Bool.false 366127136 33554432 36 33554432 11441473 1048576 9 8388608 (Ns396p569 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns396p583 := @Enclosure.Real.IsNear.recentre' qz91 Bool.false 845117623088044559715 147573952589676412928 Ns396p578 Ns396p579 48039375 8388608 227 33554432 (@Ns396p580 Ns396p579 RS397to408.d47 (Ns396p582 rfl rfl) rfl) 

noncomputable def Ns396p584 := nat_lit 1226274852717061031854080 

noncomputable def Ns396p585 := nat_lit 1592667900164339815111004118985428430464966925221718584537478870614329346239123000936730145 

noncomputable def Ns396p586 := nat_lit 557370660742319787597002336744821829353267488733563774514965253236404691403024046591521 

noncomputable def Ns396p587 := nat_lit 4170370662217783378967948974511868558732150942503694332439420431675146489697336296854097441 

noncomputable def Ns396p588 := BSN.sin_dyadic_bound_f 69705655091 68719476736 3 2 33554432 12512208 Ns396p585 Ns396p175 Ns396p586 Ns396p587 Ns396p178 Ns396p586 28492337 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 69705655091) qz368 0 2 Ns396p585 Ns396p175 Ns396p586 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 69705655091) qz369 0 2 Ns396p587 Ns396p178 Ns396p586 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p589 := @Ns396p577 6250000 (Ns396p583 rfl) (Enclosure.sfrac_false_div 48039375 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48039375) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p584) qz594) 226375608064910080 72057594037927936 Bool.false 28492337 33554432 0 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 48039375 8388608 226375608064910080 72057594037927936 0 Ns396p584 Ns396p173 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 28492337 33554432 Ns396p584 Ns396p173 69705655091 68719476736 12512208 12500000 (Ns396p588 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p590 := @Enclosure.Real.IsNear.inv_image qz89 28492337 33554432 90769027 13107200000000 19757781 19758104 16777216 (Ns396p576 (Ns396p589 rfl rfl) rfl) rfl 

noncomputable def Ns396p591 := @Enclosure.Real.IsNear.recentre' qz90 Bool.false 10430656 16777216 

noncomputable abbrev qz92 := (@HMul.hMul Real Real Real qz349 qz346 qz429)

noncomputable def Ns396p592 := @Enclosure.Real.IsNear.cos_image qz92 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15097233)) qz413) Bool.true 15097233 16777216 

noncomputable def Ns396p593 := nat_lit 139247397411006496872610525 

noncomputable def Ns396p594 := nat_lit 154742504910672534362390528 

noncomputable def Ns396p595 := nat_lit 1150255692625800793908982589657083 

noncomputable def Ns396p596 := @Enclosure.Real.IsNear.recentre' qz92 Bool.true Ns396p593 Ns396p594 Ns396p595 

noncomputable def Ns396p597 := nat_lit 60446290980731458735308800000000000000 

noncomputable abbrev qz93 := qz429

noncomputable def Ns396p598 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz93 884279719003555 140737488355328 1 500000000000000 157469853055 

noncomputable abbrev qz430 := (@HSub.hSub Real Real Real qz583 qz620 qz615)

noncomputable abbrev qz94 := qz430

noncomputable def Ns396p599 := @Enclosure.Real.IsNear.subLit_tf qz94 qz29 88750376319 1099511627776 213120225 70368744177664 1 16 

noncomputable abbrev qz431 := qz620

noncomputable abbrev qz95 := qz431

noncomputable def Ns396p600 := @Enclosure.Real.IsNear.subLit_ff_n qz95 qz80 913387338369 1099511627776 137622753 70368744177664 955713 1048576 9 8388608 

noncomputable def Ns396p601 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz80 955713 1048576 9 8388608 955713 1048576 9 8388608 913387338369 1099511627776 

noncomputable def Ns396p602 := nat_lit 6917477721085116979734097874047876674439706240802069244987521 

noncomputable def Ns396p603 := nat_lit 253092741970790968397859029543733109897246971520789871559966720 

noncomputable def Ns396p604 := nat_lit 2698850708912938974253726288198397877053573431439926413441 

noncomputable def Ns396p605 := nat_lit 20747035461837525061253786169567233227565011575543327882135681 

noncomputable def Ns396p606 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400 

noncomputable def Ns396p607 := BSN.cos_dyadic_bound_f 15097233 16777216 3 2 16777216 6250000 Ns396p602 Ns396p603 Ns396p604 Ns396p605 Ns396p606 Ns396p604 10430656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 15097233) (BSN.cosEvenQ 16777216) 0 2 Ns396p602 Ns396p603 Ns396p604 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 15097233) (BSN.cosOddQ 16777216) 0 2 Ns396p605 Ns396p606 Ns396p604 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p608 := @Ns396p591 4027304432 209715200000000 162979 262144 251706527 13107200000000 (@Ns396p592 639 33554432 Bool.false 10430656 16777216 1 6250000 (@Ns396p596 Ns396p597 15097233 16777216 639 33554432 (@Ns396p598 1099511627776 213120225 70368744177664 Ns396p593 Ns396p594 Ns396p595 Ns396p597 RS397to408.d47 (@Ns396p599 0 1 2519517648880 157469853055 1099511627776 213120225 70368744177664 (@Ns396p600 93061514599071744 88750376319 1099511627776 213120225 70368744177664 (@Ns396p601 137622753 70368744177664 (Ns396p582 rfl rfl) (Ns396p582 rfl rfl) rfl) (Ns396p582 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15097233 16777216) (BSN.cos_neg_of_bound 15097233 16777216 Bool.false 10430656 16777216 1 6250000 (Ns396p607 rfl rfl)) rfl rfl) 

noncomputable def Ns396p609 := @Ns396p567 4013051692228065166909 Ns396p485 (Ns396p568 qz31 (@Enclosure.Real.IsNear.of_eq qz79 (@Inv.inv Real Real.instInv (Real.sqrt qz88)) Bool.false 158719 524288 1 16777216 (BSN.rpow_neg_quarter_mk qz87 (BSN.t_div_two_pi_nonneg qz78 748073 1000 qz81)) Ns396p572) rfl) (@Ns396p573 8796093022208 786162395368101 27487790694400000000 (BSN.correction_mk qz80 (BSN.cos_two_pi_p_ne_zero_mk qz78 748073 1000 10 qz81 rfl rfl (@BSN.floor_sqrt_eq_dec qz78 748073 1000 10 qz81 rfl rfl rfl))) (@Ns396p574 33554432 162979 262144 251706527 13107200000000 6440259421415 8796093022208 786162395368101 27487790694400000000 (@Ns396p575 33554432 (Ns396p590 rfl rfl rfl rfl rfl) rfl) (Ns396p608 rfl) rfl)) 

noncomputable def Ns396p610 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz78) (hardyZApproximantRS₀ qz78) Bool.false 1202879872460951783 4611686018427387904 496917242476535265166909 Ns396p485 (@Eq.refl Real (hardyZApproximantRS₀ qz78)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz78) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80))) Bool.false 1202879872460951783 4611686018427387904 496917242476535265166909 Ns396p485 (BSN.hardyZApproximantRS₀_eq qz78 10 (@BSN.floor_sqrt_eq_dec qz78 748073 1000 10 qz81 rfl rfl rfl)) (@Ns396p487 1202879872460951783 4611686018427387904 496917242476535265166909 Ns396p485 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10)) Bool.false 64758101 134217728 71727 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (Ns396p566 (Ns396p565 rfl rfl rfl rfl) rfl rfl)) (Ns396p609 rfl) rfl rfl)) 

theorem RS397to408.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz78) Bool.false 1202879872460951783 4611686018427387904 496917242476535265166909 Ns396p485 := Ns396p610 

noncomputable def Ns396p611 := nat_lit 3982205923217072891636037 

noncomputable def Ns396p612 := nat_lit 1370435118092842331650570321920 

noncomputable abbrev qz728 := (Enclosure.sfrac Bool.false 749551 1000)

noncomputable abbrev qz621 := qz728

noncomputable abbrev qz432 := qz621

noncomputable abbrev qz96 := qz432

noncomputable abbrev qz729 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 749551 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz622 := qz729

noncomputable abbrev qz433 := qz622

noncomputable abbrev qz97 := (@HPow.hPow Real Real Real qz350 qz433 qz352)

noncomputable abbrev qz730 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 749551 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz623 := qz730

noncomputable abbrev qz434 := qz623

noncomputable abbrev qz98 := qz434

noncomputable def Ns396p613 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98)) 549818027 134217728 35933 33554432 538036278647806621033 2361183241434822606848 31330791129572091636037 Ns396p75 Ns396p612 

noncomputable def Ns396p614 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos BSN.quadSignPos 9 10 749551 1000 196 268435456 134217728 4503599627370496 Bool.false 380334747929 2517 618095470 44 84886744 8 

noncomputable def Ns396p615 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 749551 1000 90 146 268435456 134217728 4503599627370496 Bool.false 380334747929 2517 

noncomputable def Ns396p616 := Ns396p615 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 429919364 108094 Bool.true 112332095 Bool.true 198172018 14148475504056880 1 Bool.false 245272665 Bool.true Bool.false 198547903 Bool.true Bool.true 582818982 

noncomputable def Ns396p617 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 749551 1000 47 26 268435456 134217728 4503599627370496 Bool.false 380334747929 2517 

noncomputable def Ns396p618 := Ns396p617 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 365412810 80166 Bool.false 3986619 Bool.true 231069719 14148475504056880 1 Bool.false 3986472 Bool.false Bool.false 174974184 Bool.true Bool.true 429919364 

noncomputable def Ns396p619 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 749551 1000 240 134 268435456 134217728 4503599627370496 Bool.false 380334747929 2517 

noncomputable def Ns396p620 := Ns396p619 372130544 43 134217720 8 432030192 43 120047984 16 Bool.true 341926191 47224 Bool.false 206143759 Bool.false 3990097 14148475504056880 1 Bool.false 193096218 Bool.false Bool.false 268405801 Bool.true Bool.true 365412810 

noncomputable def Ns396p621 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 749551 1000 571 377 268435456 134217728 4503599627370496 Bool.false 380334747929 2517 

noncomputable def Ns396p622 := Ns396p621 186065264 43 189812528 16 294906480 43 154981288 8 Bool.true 268435336 2563 Bool.false 102951692 Bool.false 322450482 14148475504056880 1 Bool.false 100446304 Bool.false Bool.false 250310979 Bool.true Bool.true 341926191 

noncomputable def Ns396p623 := nat_lit 40737662783943793149838311525372089235188039727510687165889 

noncomputable def Ns396p624 := nat_lit 28752127291336144371245711516751511454901077494726656000 

noncomputable def Ns396p625 := nat_lit 113565826642484631922660274920480000 

noncomputable def Ns396p626 := nat_lit 510740379612715578105865281997060226880 

noncomputable abbrev qz624 := (@Eq.refl Real qz728)

noncomputable abbrev qz435 := qz624

noncomputable abbrev qz99 := qz435

noncomputable def Ns396p627 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz96 749551 1000 2247307806404 16000000 1499102 4000 2000 Ns396p625 Ns396p626 qz99 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns396p628 := nat_lit 13036052090862013807948259688119068555260172712803419893084480 

noncomputable abbrev qz625 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1499102))))

noncomputable abbrev qz436 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 749551 4000) (Real.log (Enclosure.sfrac Bool.false 2247307806404 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz625))

noncomputable abbrev qz626 := (Enclosure.sfrac Bool.false 749551 2000)

noncomputable abbrev qz100 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz436 qz626) (@HMul.hMul Real Real Real qz349 qz626 (Real.log Real.pi)))

noncomputable def Ns396p629 := @Enclosure.Real.IsNear.addLit_ft_p qz100 (Enclosure.sfrac Bool.true Ns396p625 Ns396p626) 25523836878860168476521 18014398509481984000 38389138729867683 4096000000000000000000 Ns396p625 Ns396p626 0 1 Ns396p628 

noncomputable def Ns396p630 := nat_lit 1712875697861611521307934982144000 

noncomputable abbrev qz101 := (@HSub.hSub Real Real Real qz355 qz436 qz626)

noncomputable def Ns396p631 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (@HMul.hMul Real Real Real qz5 qz626 (Real.log Real.pi)) 33252314933361870911337 18014398509481984000 15151032742867 4000000000000000000 28790824318311 67108864000 749551 134217728000 Ns396p630 25523836878860168476521 18014398509481984000 

noncomputable def Ns396p632 := nat_lit 66504629866723741822674000 

noncomputable abbrev qz102 := qz436

noncomputable def Ns396p633 := @Enclosure.Real.IsNear.subLit_ff_p qz102 qz626 40003670141952236205929 18014398509481984000 15151032742867 4000000000000000000 749551 2000 0 1 Ns396p632 33252314933361870911337 18014398509481984000 15151032742867 4000000000000000000 

noncomputable def Ns396p634 := nat_lit 90080256972374163900875237646917435392 

noncomputable def Ns396p635 := nat_lit 57315921697489918881693696 

noncomputable def Ns396p636 := nat_lit 5343605565819882848044071950147629383937916798979840 

noncomputable def Ns396p637 := nat_lit 2129300711957677423928186205536431705528660789248 

noncomputable def Ns396p638 := nat_lit 1525069997804295578396312118490695932287795968 

noncomputable def Ns396p639 := BSN.log_dyadic_bound 150155806404 4344459806404 3 2 Ns396p636 134217728 50000000 Ns396p637 Ns396p638 9281523 4494615612808 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 150155806404) (BSN.artanhQ 4344459806404) 0 2 Ns396p637 Ns396p636 Ns396p638 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz437 := (Real.log (Enclosure.sfrac Bool.false 2247307806404 16000000))

noncomputable def Ns396p640 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 749551 4000) qz437 749551 4000 0 1 53379611761765479 4503599627370496 20000017 1000000000000000 40010741375643076549929 18014398509481984000 14991032742367 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 749551 4000) (BSN.isNear_log_sfrac 2247307806404 16000000 53379611761765479 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2247307806404) qz358)) Bool.false Ns396p635 Ns396p100 1000000850000000 50000000000000000000000 53379611761765479 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2247307806404 16000000 17 4494615612808 4194304000000 9281523 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns396p639 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns396p641 := BSN.arctan_dyadic_bound_f 1000 1499102 1 0 16777216 6250000 0 1 1 0 1 1 11191 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1499102) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1499102) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz438 := (@Nat.cast Real Real.instNatCast 1499102)

noncomputable def Ns396p642 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz438)) 884279719003555 562949953421312 1 2000000000000000 11191 16777216 1 6250000 14829451877213209100288 883904211355043 562949953421312 320000001 2000000000000000 qz15 (Ns396p641 rfl) rfl rfl 

noncomputable abbrev qz439 := (@HMul.hMul Real Real Real qz579 qz584 qz625)

noncomputable abbrev qz103 := qz439

noncomputable abbrev qz440 := qz625

noncomputable abbrev qz104 := qz440

noncomputable def Ns396p643 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 749551 4000) qz437) qz103 40010741375643076549929 18014398509481984000 14991032742367 4000000000000000000 883904211355043 2251799813685248 320000001 8000000000000000 Ns396p634 40003670141952236205929 18014398509481984000 15151032742867 4000000000000000000 (Ns396p640 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz104 1 4 0 1 883904211355043 562949953421312 320000001 2000000000000000 883904211355043 2251799813685248 320000001 8000000000000000 qz366 Ns396p642 rfl) 

noncomputable def Ns396p644 := @Ns396p629 Ns396p623 Ns396p624 38389138729867683 4096000000000000000000 (@Ns396p631 38389138729867683 4096000000000000000000 (Ns396p633 (Ns396p643 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 749551 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz626 (Real.log Real.pi) 749551 2000 0 1 38410761 33554432 1 67108864 28790824318311 67108864000 749551 134217728000 (Enclosure.Real.IsNear.const Bool.false 749551 2000) RS397to408.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns396p625 Ns396p626) 

noncomputable def Ns396p645 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz96) Bool.false Ns396p623 Ns396p624 38389138729867683 4096000000000000000000 47541843491 33554432 315 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz96) (@HAdd.hAdd Real Real Real qz367 qz100 (Enclosure.sfrac Bool.true Ns396p625 Ns396p626)) Bool.false Ns396p623 Ns396p624 38389138729867683 4096000000000000000000 Ns396p627 (Ns396p644 rfl rfl)) 

noncomputable def Ns396p646 := nat_lit 7591358685687446704750592 

noncomputable def Ns396p647 := nat_lit 3502421036294273141706453085167203306343301754467712110441507207885223882361362706983299241587538568686881326713842422971352592516333068721 

noncomputable def Ns396p648 := nat_lit 2484714745108580606130165896223923345611593460476565019100146883102805167682937275347487693447286876370871420582818866849786052108721 

noncomputable def Ns396p649 := nat_lit 17490396199509252630588643318528268326010142921600334851675984961021764120991457322238640873658111673062637061291566034591825502011510120881 

noncomputable def Ns396p650 := BSN.sin_dyadic_bound_f 107879695373 68719476736 4 3 33554432 12512208 Ns396p647 Ns396p112 Ns396p648 Ns396p649 Ns396p115 Ns396p648 33554417 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107879695373) qz368 0 3 Ns396p647 Ns396p112 Ns396p648 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107879695373) qz369 0 3 Ns396p649 Ns396p115 Ns396p648 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p651 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz96) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47541843491) qz392) Bool.false 47541843491 33554432 315 33554432 Bool.true 33554417 33554432 1 6250000 (Ns396p645 rfl) (Enclosure.sfrac_false_div 47541843491 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47541843491) qz392) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p646) qz393) 226375608064910080 72057594037927936 Bool.false 33554417 33554432 225 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q1 47541843491 33554432 226375608064910080 72057594037927936 225 Ns396p646 Ns396p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554417 33554432 Ns396p646 Ns396p100 107879695373 68719476736 12512208 12500000 (Ns396p650 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p652 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz96) Bool.false Ns396p623 Ns396p624 38389138729867683 4096000000000000000000 380334747929 268435456 2517 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz96) (@HAdd.hAdd Real Real Real qz367 qz100 (Enclosure.sfrac Bool.true Ns396p625 Ns396p626)) Bool.false Ns396p623 Ns396p624 38389138729867683 4096000000000000000000 Ns396p627 (Ns396p644 rfl rfl)) 

noncomputable def Ns396p653 := Ns396p622 47224 BSN.abs_quadSignPos (BSN.cos_quad_nat3 571 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 100446304 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 377 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 250310979 268435456) qz99 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 1) Bool.true 33554417 33554432 125144027 13107200000000 268435336 268435456 2563 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz96)) Bool.true 33554417 33554432 125144027 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz96) qz96) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz96)) Bool.true 33554417 33554432 2002304432 209715200000000 33554417 33554432 125144027 13107200000000 (Ns396p651 rfl rfl) rfl)) rfl) (Ns396p652 rfl) RS397to408.d7 

noncomputable def Ns396p654 := nat_lit 112339879676870741757108668682496 

noncomputable def Ns396p655 := BSN.sin_dyadic_bound_f 102951692 268435456 2 1 268435456 134217728 Ns396p654 Ns396p131 Ns396p654 Ns396p654 Ns396p132 Ns396p654 100446304 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 102951692) qz370 0 1 Ns396p654 Ns396p131 Ns396p654 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 102951692) qz371 0 1 Ns396p654 Ns396p132 Ns396p654 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p656 := nat_lit 169860475941259055586617381734387151112926605146470719131415991348609280 

noncomputable def Ns396p657 := nat_lit 116870322824303572384473264021274172498419621020531453797963560632576 

noncomputable def Ns396p658 := nat_lit 444683456466343892181089709734027142349810334092437689657083274433904896 

noncomputable def Ns396p659 := BSN.sin_dyadic_bound_f 322450482 268435456 3 2 268435456 134217728 Ns396p656 Ns396p121 Ns396p657 Ns396p658 Ns396p124 Ns396p657 250310979 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 322450482) qz370 0 2 Ns396p656 Ns396p121 Ns396p657 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 322450482) qz371 0 2 Ns396p658 Ns396p124 Ns396p657 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p660 := nat_lit 15755763696026853441139060789840044436604897019767982702445625873404801 

noncomputable def Ns396p661 := nat_lit 3261080568170746261614416346225097201432893426195000988988525646721 

noncomputable def Ns396p662 := nat_lit 47260768926944218830893953536827683115411825272451558105358900568920961 

noncomputable def Ns396p663 := BSN.cos_dyadic_bound_f 206143759 268435456 3 2 268435456 134217728 Ns396p660 Ns396p252 Ns396p661 Ns396p662 Ns396p255 Ns396p661 193096218 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 206143759) qz372 0 2 Ns396p660 Ns396p252 Ns396p661 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 206143759) qz373 0 2 Ns396p662 Ns396p255 Ns396p661 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p664 := nat_lit 253474231133979891749609281 

noncomputable def Ns396p665 := BSN.cos_dyadic_bound_f 3990097 268435456 2 1 268435456 134217728 Ns396p664 Ns396p141 Ns396p664 Ns396p664 Ns396p142 Ns396p664 268405801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 3990097) qz372 0 1 Ns396p664 Ns396p141 Ns396p664 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 3990097) qz373 0 1 Ns396p664 Ns396p142 Ns396p664 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p666 := Ns396p620 80166 BSN.abs_quadSignPos (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 193096218 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 134 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268405801 268435456) qz99 rfl rfl (Ns396p653 RS397to408.d9 RS397to408.d11 RS397to408.d13 RS397to408.d17 (Ns396p655 rfl rfl) (Ns396p659 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns396p652 rfl) RS397to408.d19 RS397to408.d21 RS397to408.d23 RS397to408.d25 RS397to408.d17 (Ns396p663 rfl rfl) (Ns396p665 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns396p667 := BSN.sin_dyadic_bound_f 3986619 268435456 1 0 268435456 134217728 0 1 1 0 1 1 3986472 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 3986619) qz370 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 3986619) qz371 0 0 rfl) rfl rfl 

noncomputable def Ns396p668 := nat_lit 24876131970654667320881941868262053897078037002787314679604659198496321 

noncomputable def Ns396p669 := nat_lit 8127262547299714817600506648683013728093818324254531772668413349441 

noncomputable def Ns396p670 := nat_lit 74612141386869402533010624591488795663777923371713434975268640768790081 

noncomputable def Ns396p671 := BSN.cos_dyadic_bound_f 231069719 268435456 3 2 268435456 134217728 Ns396p668 Ns396p252 Ns396p669 Ns396p670 Ns396p255 Ns396p669 174974184 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 231069719) qz372 0 2 Ns396p668 Ns396p252 Ns396p669 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 231069719) qz373 0 2 Ns396p670 Ns396p255 Ns396p669 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p672 := Ns396p618 108094 BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 3986472 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 174974184 268435456) qz99 rfl rfl (Ns396p666 rfl rfl) (Ns396p652 rfl) RS397to408.d27 RS397to408.d29 RS397to408.d31 RS397to408.d33 RS397to408.d17 (Ns396p667 rfl rfl) (Ns396p671 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p673 := nat_lit 1388967735987261780697213217189924557540552614768418145900832489690625 

noncomputable def Ns396p674 := nat_lit 25353088277672076575162210053959790867744033638067813046812890625 

noncomputable def Ns396p675 := nat_lit 4166852501785229997938489327149665753039922356237978302076403843290625 

noncomputable def Ns396p676 := BSN.cos_dyadic_bound_f 112332095 268435456 3 2 268435456 134217728 Ns396p673 Ns396p252 Ns396p674 Ns396p675 Ns396p255 Ns396p674 245272665 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 112332095) qz372 0 2 Ns396p673 Ns396p252 Ns396p674 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 112332095) qz373 0 2 Ns396p675 Ns396p255 Ns396p674 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p677 := nat_lit 13455966685291040691265885983544569221804024065239558118883833352601856 

noncomputable def Ns396p678 := nat_lit 2378694425688463777604307873403878105509840641657131485179319992576 

noncomputable def Ns396p679 := nat_lit 40363142667021745146242449334886899909201052514435360093681141417820416 

noncomputable def Ns396p680 := BSN.cos_dyadic_bound_f 198172018 268435456 3 2 268435456 134217728 Ns396p677 Ns396p252 Ns396p678 Ns396p679 Ns396p255 Ns396p678 198547903 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 198172018) qz372 0 2 Ns396p677 Ns396p252 Ns396p678 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 198172018) qz373 0 2 Ns396p679 Ns396p255 Ns396p678 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p681 := Ns396p616 132496 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 245272665 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 146 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 198547903 268435456) qz99 rfl rfl (Ns396p672 rfl) (Ns396p652 rfl) RS397to408.d35 RS397to408.d37 RS397to408.d39 RS397to408.d41 RS397to408.d17 (Ns396p676 rfl rfl) (Ns396p680 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p682 := nat_lit 5268283603198280750813365747221319456670282645882102726701972324143121542622786784857128454966748909011992576 

noncomputable def Ns396p683 := nat_lit 935433731276261357358926902662828033929690329430628511516352146789377885783144767793327415127804215296 

noncomputable def Ns396p684 := nat_lit 31937053603094551904876781222007614151818147189411911531179357910587245389386266530883868073894886265407406080 

noncomputable def Ns396p685 := BSN.cos_dyadic_bound_f 314473764 268435456 4 3 268435456 134217728 Ns396p682 Ns396p246 Ns396p683 Ns396p684 Ns396p249 Ns396p683 104358185 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 314473764) qz372 0 3 Ns396p682 Ns396p246 Ns396p683 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 314473764) qz373 0 3 Ns396p684 Ns396p249 Ns396p683 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p686 := Ns396p614 Bool.true 582818982 132496 Bool.true 314473764 14148475504056880 1 Bool.false 104358185 Bool.false Bool.true 549818027 143732 BSN.abs_quadSignPos qz394 (BSN.sfrac_eq_quadSignPos_mul Bool.false 104358185 268435456) qz99 rfl (Ns396p681 rfl) (Ns396p652 rfl) RS397to408.d43 RS397to408.d45 RS397to408.d17 (Ns396p685 rfl rfl) rfl 

noncomputable def Ns396p687 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) 549818027 268435456 143732 268435456 549818027 268435456 143732 268435456 295181305589530624 549818027 134217728 35933 33554432 (Ns396p686 rfl rfl rfl rfl) 

noncomputable def Ns396p688 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98) 2538251 8388608 1 16777216 211971266296283 281474976710656 6139105714657929 219902325555200000000 538036278647806621033 2361183241434822606848 

noncomputable def Ns396p689 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz97 1 1 0 1 2538251 8388608 1 16777216 2538251 8388608 1 16777216 

noncomputable abbrev qz105 := qz433

noncomputable def Ns396p690 := @Enclosure.Real.IsNear.sqrt_image qz105 4002866931503 33554432000 749551 33554432000 183244304 183244340 16777216 (@Enclosure.Real.IsNear.of_eq qz105 (@HMul.hMul Real Real Real qz5 qz96 qz3) Bool.false 4002866931503 33554432000 749551 33554432000 (BSN.t_div_two_pi_mk qz96 749551 1000 qz99) (@Enclosure.Real.IsNear.mulLit_ff qz96 qz3 749551 1000 0 1 5340353 33554432 1 33554432 4002866931503 33554432000 749551 33554432000 (Enclosure.Real.IsNear.const Bool.false 749551 1000) RS397to408.d48 rfl)) 

noncomputable abbrev qz731 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 749551 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz627 := qz731

noncomputable abbrev qz441 := qz627

noncomputable abbrev qz106 := qz441

noncomputable def Ns396p691 := @Enclosure.Real.IsNear.sqrt_image qz106 91622161 8388608 9 8388608 55446634 55446640 16777216 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 366488644 33554432 36 33554432 91622161 8388608 9 8388608 (Ns396p690 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns396p692 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz106) 55446637 16777216 3 16777216 5076501 5076503 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz106) Bool.false 110893274 33554432 6 33554432 55446637 16777216 3 16777216 (Ns396p691 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns396p693 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz106)) Bool.false 10153004 33554432 2 33554432 2538251 8388608 1 16777216 (Ns396p692 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz107 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz434))

noncomputable abbrev qz628 := (@HMul.hMul Real Real Real qz707 qz730 qz730)

noncomputable abbrev qz442 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz628 qz623) qz593)

noncomputable abbrev qz108 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz442))

noncomputable def Ns396p694 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz98) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz107) qz108) Bool.false 211971266296283 

noncomputable def Ns396p695 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz107) qz108 38003953 33554432 301 

noncomputable def Ns396p696 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz107) Bool.false 38003953 33554432 301 33554432 38003953 33554432 301 

noncomputable def Ns396p697 := @Enclosure.Real.IsNear.recentre' qz107 Bool.false 29625863 33554432 364638608 52428800000000 29625863 33554432 22789913 3276800000000 

noncomputable abbrev qz109 := (@HMul.hMul Real Real Real qz349 qz346 qz434)

noncomputable def Ns396p698 := @Enclosure.Real.IsNear.cos_image qz109 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 194428921) qz392) Bool.false 194428921 33554432 57 8388608 Bool.false 29625863 33554432 1 

noncomputable def Ns396p699 := nat_lit 48574935749569767776986931 

noncomputable def Ns396p700 := nat_lit 7205759403792793600000000000000 

noncomputable def Ns396p701 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz98 884279719003555 140737488355328 1 500000000000000 7736081 8388608 9 8388608 6840859532868740767955 1180591620717411303424 Ns396p699 

noncomputable def Ns396p702 := @Enclosure.Real.IsNear.subLit_ff_p qz106 qz1 91622161 8388608 9 8388608 10 1 0 1 7736081 7736081 8388608 9 

noncomputable def Ns396p703 := @Ns396p702 8388608 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 366488644 33554432 36 33554432 91622161 8388608 9 8388608 (Ns396p690 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns396p704 := @Enclosure.Real.IsNear.recentre' qz109 Bool.false 6840859532868740767955 1180591620717411303424 Ns396p699 Ns396p700 194428921 33554432 57 8388608 (@Ns396p701 Ns396p700 RS397to408.d47 (Ns396p703 rfl rfl) rfl) 

noncomputable def Ns396p705 := nat_lit 5232445675482692748050432 

noncomputable def Ns396p706 := nat_lit 2062517772408502453786480547619170445446979429508581510593865219204171651807471096782474785 

noncomputable def Ns396p707 := nat_lit 934543282883737920554552576467129274883229357320753484894262271468345153072336550317601 

noncomputable def Ns396p708 := nat_lit 5400319190992837517569408349116880576392278039277289403056008673285691291152688137158348321 

noncomputable def Ns396p709 := BSN.sin_dyadic_bound_f 74357525299 68719476736 3 2 33554432 12512208 Ns396p706 Ns396p175 Ns396p707 Ns396p708 Ns396p178 Ns396p707 29625863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 74357525299) qz368 0 2 Ns396p706 Ns396p175 Ns396p707 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 74357525299) qz369 0 2 Ns396p708 Ns396p178 Ns396p707 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p710 := @Ns396p698 6250000 (Ns396p704 rfl) (Enclosure.sfrac_false_div 194428921 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 194428921) qz392) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p705) qz393) 226375608064910080 72057594037927936 Bool.false 29625863 33554432 0 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 194428921 33554432 226375608064910080 72057594037927936 0 Ns396p705 Ns396p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 29625863 33554432 Ns396p705 Ns396p100 74357525299 68719476736 12512208 12500000 (Ns396p709 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p711 := @Enclosure.Real.IsNear.inv_image qz107 29625863 33554432 22789913 3276800000000 19001826 19002127 16777216 (Ns396p697 (Ns396p710 rfl rfl) rfl) rfl 

noncomputable def Ns396p712 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 11155222 16777216 

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz349 qz346 qz442)

noncomputable def Ns396p713 := @Enclosure.Real.IsNear.cos_image qz110 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 28300891)) qz392) Bool.true 28300891 33554432 

noncomputable def Ns396p714 := nat_lit 8352948881407851362214347005 

noncomputable def Ns396p715 := nat_lit 9903520314283042199192993792 

noncomputable def Ns396p716 := nat_lit 5795179032793952065361171715773909 

noncomputable def Ns396p717 := @Enclosure.Real.IsNear.recentre' qz110 Bool.true Ns396p714 Ns396p715 Ns396p716 

noncomputable def Ns396p718 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz111 := qz442

noncomputable def Ns396p719 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz111 884279719003555 140737488355328 1 500000000000000 9446048237791 

noncomputable abbrev qz443 := (@HSub.hSub Real Real Real qz583 qz628 qz623)

noncomputable abbrev qz112 := qz443

noncomputable def Ns396p720 := @Enclosure.Real.IsNear.subLit_tf qz112 qz29 5048001726687 70368744177664 214747011 70368744177664 1 16 

noncomputable abbrev qz444 := qz628

noncomputable abbrev qz113 := qz444

noncomputable def Ns396p721 := @Enclosure.Real.IsNear.subLit_ff_n qz113 qz98 59846949238561 70368744177664 139249539 70368744177664 7736081 8388608 9 8388608 

noncomputable def Ns396p722 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz98 7736081 8388608 9 8388608 7736081 8388608 9 8388608 59846949238561 70368744177664 

noncomputable def Ns396p723 := nat_lit 1366595806332126066884716938545352856907489318499764464426610401 

noncomputable def Ns396p724 := nat_lit 411529402296013607619582376786087952191746542430336249949921 

noncomputable def Ns396p725 := nat_lit 4098964360191786173438911650882486394818084462414432720779931361 

noncomputable def Ns396p726 := BSN.cos_dyadic_bound_f 28300891 33554432 3 2 16777216 6250000 Ns396p723 Ns396p322 Ns396p724 Ns396p725 Ns396p325 Ns396p724 11155222 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 28300891) (BSN.cosEvenQ 33554432) 0 2 Ns396p723 Ns396p322 Ns396p724 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 28300891) (BSN.cosOddQ 33554432) 0 2 Ns396p725 Ns396p325 Ns396p724 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p727 := @Ns396p712 4064804432 209715200000000 5577611 8388608 254050277 13107200000000 (@Ns396p713 645 33554432 Bool.false 11155222 16777216 1 6250000 (@Ns396p717 Ns396p718 28300891 33554432 645 33554432 (@Ns396p719 70368744177664 214747011 70368744177664 Ns396p714 Ns396p715 Ns396p716 Ns396p718 RS397to408.d47 (@Ns396p720 0 1 151136771804656 9446048237791 70368744177664 214747011 70368744177664 (@Ns396p721 42345707668500381696 5048001726687 70368744177664 214747011 70368744177664 (@Ns396p722 139249539 70368744177664 (Ns396p703 rfl rfl) (Ns396p703 rfl rfl) rfl) (Ns396p703 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 28300891 33554432) (BSN.cos_neg_of_bound 28300891 33554432 Bool.false 11155222 16777216 1 6250000 (Ns396p726 rfl rfl)) rfl rfl) 

noncomputable def Ns396p728 := @Ns396p688 31330791129572091636037 Ns396p75 (Ns396p689 qz31 (@Enclosure.Real.IsNear.of_eq qz97 (@Inv.inv Real Real.instInv (Real.sqrt qz106)) Bool.false 2538251 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz105 (BSN.t_div_two_pi_nonneg qz96 749551 1000 qz99)) Ns396p693) rfl) (@Ns396p694 281474976710656 6139105714657929 219902325555200000000 (BSN.correction_mk qz98 (BSN.cos_two_pi_p_ne_zero_mk qz96 749551 1000 10 qz99 rfl rfl (@BSN.floor_sqrt_eq_dec qz96 749551 1000 10 qz99 rfl rfl rfl))) (@Ns396p695 33554432 5577611 8388608 254050277 13107200000000 211971266296283 281474976710656 6139105714657929 219902325555200000000 (@Ns396p696 33554432 (Ns396p711 rfl rfl rfl rfl rfl) rfl) (Ns396p727 rfl) rfl)) 

noncomputable def Ns396p729 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz96) (hardyZApproximantRS₀ qz96) Bool.true 10210537300205546108265 2361183241434822606848 Ns396p611 Ns396p75 (@Eq.refl Real (hardyZApproximantRS₀ qz96)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz96) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98))) Bool.true 10210537300205546108265 2361183241434822606848 Ns396p611 Ns396p75 (BSN.hardyZApproximantRS₀_eq qz96 10 (@BSN.floor_sqrt_eq_dec qz96 749551 1000 10 qz99 rfl rfl rfl)) (@Ns396p613 10210537300205546108265 2361183241434822606848 Ns396p611 Ns396p75 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10)) Bool.true 549818027 134217728 35933 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (Ns396p687 (Ns396p686 rfl rfl rfl rfl) rfl rfl)) (Ns396p728 rfl) rfl rfl)) 

theorem RS397to408.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz96) Bool.true 10210537300205546108265 2361183241434822606848 Ns396p611 Ns396p75 := Ns396p729 

noncomputable def Ns396p730 := nat_lit 2560129580337063424545521664 

noncomputable abbrev qz732 := (Enclosure.sfrac Bool.false 750865 1000)

noncomputable abbrev qz629 := qz732

noncomputable abbrev qz445 := qz629

noncomputable abbrev qz114 := qz445

noncomputable abbrev qz733 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 750865 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz630 := qz733

noncomputable abbrev qz446 := qz630

noncomputable abbrev qz115 := (@HPow.hPow Real Real Real qz350 qz446 qz352)

noncomputable abbrev qz734 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 750865 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz631 := qz734

noncomputable abbrev qz447 := qz631

noncomputable abbrev qz116 := qz447

noncomputable def Ns396p731 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116)) 24347889 67108864 71995 67108864 68934244715457324255 295147905179352825856 766133125995460853853 Ns396p363 Ns396p730 

noncomputable def Ns396p732 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos BSN.quadSignPos 9 10 750865 1000 196 268435456 134217728 4503599627370496 Bool.false 381178194760 2522 618095470 44 84886744 8 

noncomputable def Ns396p733 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 750865 1000 90 146 268435456 134217728 4503599627370496 Bool.false 381178194760 2522 

noncomputable def Ns396p734 := Ns396p733 558195838 44 94906264 8 589812974 44 89478488 8 Bool.false 180960734 108289 Bool.true 2354595 Bool.true 129739435 14148475504056880 1 Bool.false 268425129 Bool.true Bool.false 237688401 Bool.true Bool.false 6828651 

noncomputable def Ns396p735 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 750865 1000 47 26 268435456 134217728 4503599627370496 Bool.false 381178194760 2522 

noncomputable def Ns396p736 := Ns396p735 480971758 44 109588312 8 522351262 44 101459064 8 Bool.false 199780422 80311 Bool.false 215436560 Bool.true 73992446 14148475504056880 1 Bool.false 193042646 Bool.false Bool.false 258302098 Bool.true Bool.false 180960734 

noncomputable def Ns396p737 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 750865 1000 241 134 268435456 134217728 4503599627370496 Bool.false 381178194760 2522 

noncomputable def Ns396p738 := Ns396p737 372130544 43 134217720 8 432030192 43 120047984 16 Bool.false 326744057 47311 Bool.false 138953627 Bool.false 279749256 14148475504056880 1 Bool.false 132830711 Bool.true Bool.false 135390078 Bool.true Bool.false 199780422 

noncomputable def Ns396p739 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 750865 1000 572 378 268435456 134217728 4503599627370496 Bool.false 381178194760 2522 

noncomputable def Ns396p740 := Ns396p739 186065264 43 189812528 16 294906480 43 154981288 8 Bool.false 268435424 2571 Bool.false 280251338 Bool.false 356732770 14148475504056880 1 Bool.false 134956299 Bool.false Bool.false 64293515 Bool.true Bool.false 326744057 

noncomputable def Ns396p741 := nat_lit 528119446488193968191880532787524363051919472477999131 

noncomputable def Ns396p742 := nat_lit 371915252207524879118147421306489497523508268236800 

noncomputable def Ns396p743 := nat_lit 114564754973355900200209139500000000 

noncomputable def Ns396p744 := nat_lit 516136095262582749063278471794005000000 

noncomputable abbrev qz632 := (@Eq.refl Real qz732)

noncomputable abbrev qz448 := qz632

noncomputable abbrev qz117 := qz448

noncomputable def Ns396p745 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz114 750865 1000 2255193992900 16000000 1501730 4000 2000 Ns396p743 Ns396p744 qz117 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns396p746 := nat_lit 2640597232440969840959402663937621815259597362389995655000000 

noncomputable abbrev qz633 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1501730))))

noncomputable abbrev qz449 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 750865 4000) (Real.log (Enclosure.sfrac Bool.false 2255193992900 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz633))

noncomputable abbrev qz634 := (Enclosure.sfrac Bool.false 750865 2000)

noncomputable abbrev qz118 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz449 qz634) (@HMul.hMul Real Real Real qz349 qz634 (Real.log Real.pi)))

noncomputable def Ns396p747 := @Enclosure.Real.IsNear.addLit_ft_p qz118 (Enclosure.sfrac Bool.true Ns396p743 Ns396p744) 5116087926112983156331 3602879701896396800 7691229914079609 819200000000000000000 Ns396p743 Ns396p744 0 1 Ns396p746 

noncomputable def Ns396p748 := nat_lit 68666969769111647054501563596800 

noncomputable abbrev qz119 := (@HSub.hSub Real Real Real qz355 qz449 qz634)

noncomputable def Ns396p749 := @Enclosure.Real.IsNear.subLit_ff_p qz119 (@HMul.hMul Real Real Real qz5 qz634 (Real.log Real.pi)) 6664493217919256725099 3602879701896396800 3035462553041 800000000000000000 5768259211653 13421772800 150173 26843545600 Ns396p748 5116087926112983156331 3602879701896396800 

noncomputable def Ns396p750 := nat_lit 2665797287167702690039600 

noncomputable abbrev qz120 := qz449

noncomputable def Ns396p751 := @Enclosure.Real.IsNear.subLit_ff_p qz120 qz634 1603426270320295143343 720575940379279360 3035462553041 800000000000000000 750865 2000 0 1 Ns396p750 6664493217919256725099 3602879701896396800 3035462553041 800000000000000000 

noncomputable def Ns396p752 := nat_lit 3610594976765272698769017201244504064 

noncomputable def Ns396p753 := nat_lit 57332861284926731132600320 

noncomputable def Ns396p754 := nat_lit 5382510795249305113646493447187969885757521500000000 

noncomputable def Ns396p755 := nat_lit 2367583329101666173047716743820302505344800000000 

noncomputable def Ns396p756 := nat_lit 1871592277721983669066491598684479504300000000 

noncomputable def Ns396p757 := BSN.log_dyadic_bound 158041992900 4352345992900 3 2 Ns396p754 134217728 50000000 Ns396p755 Ns396p756 9751691 4510387985800 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 158041992900) (BSN.artanhQ 4352345992900) 0 2 Ns396p755 Ns396p754 Ns396p756 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz450 := (Real.log (Enclosure.sfrac Bool.false 2255193992900 16000000))

noncomputable def Ns396p758 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 750865 4000) qz450 750865 4000 0 1 53395387981950055 4503599627370496 20000017 1000000000000000 1603709119882677121903 720575940379279360 3003462552941 800000000000000000 (Enclosure.Real.IsNear.const Bool.false 750865 4000) (BSN.isNear_log_sfrac 2255193992900 16000000 53395387981950055 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2255193992900) qz358)) Bool.false Ns396p753 Ns396p100 1000000850000000 50000000000000000000000 53395387981950055 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2255193992900 16000000 17 4510387985800 4194304000000 9751691 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns396p757 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns396p759 := BSN.arctan_dyadic_bound_f 1000 1501730 1 0 16777216 6250000 0 1 1 0 1 1 11171 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1501730) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1501730) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz451 := (@Nat.cast Real Real.instNatCast 1501730)

noncomputable def Ns396p760 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz451)) 884279719003555 562949953421312 1 2000000000000000 11171 16777216 1 6250000 14829463136212277526528 883904882443683 562949953421312 320000001 2000000000000000 qz15 (Ns396p759 rfl) rfl rfl 

noncomputable abbrev qz452 := (@HMul.hMul Real Real Real qz579 qz584 qz633)

noncomputable abbrev qz121 := qz452

noncomputable abbrev qz453 := qz633

noncomputable abbrev qz122 := qz453

noncomputable def Ns396p761 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 750865 4000) qz450) qz121 1603709119882677121903 720575940379279360 3003462552941 800000000000000000 883904882443683 2251799813685248 320000001 8000000000000000 Ns396p752 1603426270320295143343 720575940379279360 3035462553041 800000000000000000 (Ns396p758 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz122 1 4 0 1 883904882443683 562949953421312 320000001 2000000000000000 883904882443683 2251799813685248 320000001 8000000000000000 qz366 Ns396p760 rfl) 

noncomputable def Ns396p762 := @Ns396p747 Ns396p741 Ns396p742 7691229914079609 819200000000000000000 (@Ns396p749 7691229914079609 819200000000000000000 (Ns396p751 (Ns396p761 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 750865 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz634 (Real.log Real.pi) 750865 2000 0 1 38410761 33554432 1 67108864 5768259211653 13421772800 150173 26843545600 (Enclosure.Real.IsNear.const Bool.false 750865 2000) RS397to408.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns396p743 Ns396p744) 

noncomputable def Ns396p763 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns396p741 Ns396p742 7691229914079609 819200000000000000000 47647274345 33554432 79 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz367 qz118 (Enclosure.sfrac Bool.true Ns396p743 Ns396p744)) Bool.false Ns396p741 Ns396p742 7691229914079609 819200000000000000000 Ns396p745 (Ns396p762 rfl rfl)) 

noncomputable def Ns396p764 := nat_lit 7593736144350194339676160 

noncomputable def Ns396p765 := nat_lit 3506819460858438546921397078251534065729994323967159578692188984965884421481485502768537170169580778492445939008116002541897027246029275136 

noncomputable def Ns396p766 := nat_lit 2494068789811016039789899971792195366944104929150004025203471667333633018127470454023719495322751232743252692613706262072158989582336 

noncomputable def Ns396p767 := nat_lit 17512333859705139509473540872316063124523555367904063818201723548870487269484320931179638783113819973101674492320961758918862472368510468096 

noncomputable def Ns396p768 := BSN.sin_dyadic_bound_f 107913481092 68719476736 4 3 33554432 12512208 Ns396p765 Ns396p112 Ns396p766 Ns396p767 Ns396p115 Ns396p766 33554428 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107913481092) qz368 0 3 Ns396p765 Ns396p112 Ns396p766 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107913481092) qz369 0 3 Ns396p767 Ns396p115 Ns396p766 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p769 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz114) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47647274345) qz392) Bool.false 47647274345 33554432 79 8388608 Bool.false 33554428 33554432 1 6250000 (Ns396p763 rfl) (Enclosure.sfrac_false_div 47647274345 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47647274345) qz392) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p764) qz393) 226375608064910080 72057594037927936 Bool.false 33554428 33554432 225 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 47647274345 33554432 226375608064910080 72057594037927936 225 Ns396p764 Ns396p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554428 33554432 Ns396p764 Ns396p100 107913481092 68719476736 12512208 12500000 (Ns396p768 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p770 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns396p741 Ns396p742 7691229914079609 819200000000000000000 381178194760 268435456 2522 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz367 qz118 (Enclosure.sfrac Bool.true Ns396p743 Ns396p744)) Bool.false Ns396p741 Ns396p742 7691229914079609 819200000000000000000 Ns396p745 (Ns396p762 rfl rfl)) 

noncomputable def Ns396p771 := Ns396p740 47311 BSN.abs_quadSignPos (BSN.cos_quad_nat0 572 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134956299 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 378 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64293515 268435456) qz117 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) Bool.false 8388607 8388608 31383663 3276800000000 268435424 268435456 2571 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 8388607 8388608 31383663 3276800000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz114) qz114) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 33554428 33554432 502138608 52428800000000 8388607 8388608 31383663 3276800000000 (Ns396p769 rfl rfl) rfl)) rfl) (Ns396p770 rfl) RS397to408.d7 

noncomputable def Ns396p772 := nat_lit 3321563586925601904813379592744416998406590417800782349576904037889984674769152852244154575595514535265243136 

noncomputable def Ns396p773 := nat_lit 234732020262735520763039426845972742581708580336734933066250510009170038657383389597184980606195142656 

noncomputable def Ns396p774 := nat_lit 20141324622595202616943792975807064033888851573347555592372458843185178561560720666239267044524776001463193600 

noncomputable def Ns396p775 := BSN.cos_dyadic_bound_f 280251338 268435456 4 3 268435456 134217728 Ns396p772 Ns396p246 Ns396p773 Ns396p774 Ns396p249 Ns396p773 134956299 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 280251338) qz372 0 3 Ns396p772 Ns396p246 Ns396p773 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 280251338) qz373 0 3 Ns396p774 Ns396p249 Ns396p773 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p776 := nat_lit 8730166415452974717024590695897858803925337557313059040966844791921332991146059079999975628421771517504000000 

noncomputable def Ns396p777 := nat_lit 4247330665658826071192345567936832604068691873939306788432291404767100293462331449037691121000000000000 

noncomputable def Ns396p778 := nat_lit 52897557772319795800329278375308151700970472140043349726425677217964498392323630310258989314998509828057600000 

noncomputable def Ns396p779 := BSN.cos_dyadic_bound_f 356732770 268435456 4 3 268435456 134217728 Ns396p776 Ns396p246 Ns396p777 Ns396p778 Ns396p249 Ns396p777 64293515 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 356732770) qz372 0 3 Ns396p776 Ns396p246 Ns396p777 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 356732770) qz373 0 3 Ns396p778 Ns396p249 Ns396p777 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p780 := nat_lit 5853709443482408379825724268857331788810996369888694639500918806891745 

noncomputable def Ns396p781 := nat_lit 138982173289442897189623011012703465398290527882907687906136902881 

noncomputable def Ns396p782 := nat_lit 15330918761792410468186208933560896022227678974568104110055320272588001 

noncomputable def Ns396p783 := BSN.sin_dyadic_bound_f 138953627 268435456 3 2 268435456 134217728 Ns396p780 Ns396p121 Ns396p781 Ns396p782 Ns396p124 Ns396p781 132830711 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 138953627) qz370 0 2 Ns396p780 Ns396p121 Ns396p781 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 138953627) qz371 0 2 Ns396p782 Ns396p124 Ns396p781 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p784 := nat_lit 3297807936686724561040368263815317733648174181875577257461119205247285467945242218649864599934247946646716416 

noncomputable def Ns396p785 := nat_lit 229735062135542283751193623761244777589934428867548504830099486834782634206960755499186175236779278336 

noncomputable def Ns396p786 := nat_lit 19997342247255677423924452541544321916521758439752522965689360665799226276919964110604185697284836032679772160 

noncomputable def Ns396p787 := BSN.cos_dyadic_bound_f 279749256 268435456 4 3 268435456 134217728 Ns396p784 Ns396p246 Ns396p785 Ns396p786 Ns396p249 Ns396p785 135390078 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 279749256) qz372 0 3 Ns396p784 Ns396p246 Ns396p785 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 279749256) qz373 0 3 Ns396p786 Ns396p249 Ns396p785 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p788 := Ns396p738 80311 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132830711 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 134 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 135390078 268435456) qz117 rfl rfl (Ns396p771 RS397to408.d9 RS397to408.d11 RS397to408.d13 RS397to408.d17 (Ns396p775 rfl rfl) (Ns396p779 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns396p770 rfl) RS397to408.d19 RS397to408.d21 RS397to408.d23 RS397to408.d25 RS397to408.d17 (Ns396p783 rfl rfl) (Ns396p787 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns396p789 := nat_lit 33828169903042092062056173887334144684335466389945550827480248483840000 

noncomputable def Ns396p790 := nat_lit 4640398167568911433727494908456172740028277795073673501081600000000 

noncomputable def Ns396p791 := nat_lit 88590074815696081924968706141737640369775699523903466219636994867200000 

noncomputable def Ns396p792 := BSN.sin_dyadic_bound_f 215436560 268435456 3 2 268435456 134217728 Ns396p789 Ns396p121 Ns396p790 Ns396p791 Ns396p124 Ns396p790 193042646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 215436560) qz370 0 2 Ns396p789 Ns396p121 Ns396p790 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 215436560) qz371 0 2 Ns396p791 Ns396p124 Ns396p790 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p793 := nat_lit 29974333626347579585007038423056 

noncomputable def Ns396p794 := BSN.cos_dyadic_bound_f 73992446 268435456 2 1 268435456 134217728 Ns396p793 Ns396p141 Ns396p793 Ns396p793 Ns396p142 Ns396p793 258302098 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 73992446) qz372 0 1 Ns396p793 Ns396p141 Ns396p793 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 73992446) qz373 0 1 Ns396p793 Ns396p142 Ns396p793 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p795 := Ns396p736 108289 BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 193042646 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 258302098 268435456) qz117 rfl rfl (Ns396p788 rfl rfl) (Ns396p770 rfl) RS397to408.d27 RS397to408.d29 RS397to408.d31 RS397to408.d33 RS397to408.d17 (Ns396p792 rfl rfl) (Ns396p794 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p796 := BSN.cos_dyadic_bound_f 2354595 268435456 1 0 268435456 134217728 0 1 1 0 1 1 268425129 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 2354595) qz372 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 2354595) qz373 0 0 rfl) rfl rfl 

noncomputable def Ns396p797 := nat_lit 2471558594949733943942563635734567052332790999689208531524129039190625 

noncomputable def Ns396p798 := nat_lit 80274205956424809920412400136503875207444790970349705053250390625 

noncomputable def Ns396p799 := nat_lit 7414515236437288982207850082403428149247958109485684895162280616790625 

noncomputable def Ns396p800 := BSN.cos_dyadic_bound_f 129739435 268435456 3 2 268435456 134217728 Ns396p797 Ns396p252 Ns396p798 Ns396p799 Ns396p255 Ns396p798 237688401 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 129739435) qz372 0 2 Ns396p797 Ns396p252 Ns396p798 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 129739435) qz373 0 2 Ns396p799 Ns396p255 Ns396p798 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p801 := Ns396p734 132734 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268425129 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 146 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 237688401 268435456) qz117 rfl rfl (Ns396p795 rfl) (Ns396p770 rfl) RS397to408.d35 RS397to408.d37 RS397to408.d39 RS397to408.d41 RS397to408.d17 (Ns396p796 rfl rfl) (Ns396p800 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p802 := nat_lit 3463895687996540124948010066256303502954127913398379295020940258524554774397657053477264210015418618588381041 

noncomputable def Ns396p803 := nat_lit 266194824907190475854659441030318732217710502126369850794866530066989014053232315460572050834089262961 

noncomputable def Ns396p804 := nat_lit 21003975477660544280117503078285453717306139223168282427835412765732422872743683409071320326666822133532540785 

noncomputable def Ns396p805 := BSN.cos_dyadic_bound_f 283204381 268435456 4 3 268435456 134217728 Ns396p802 Ns396p246 Ns396p803 Ns396p804 Ns396p249 Ns396p803 132395482 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 283204381) qz372 0 3 Ns396p802 Ns396p246 Ns396p803 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 283204381) qz373 0 3 Ns396p804 Ns396p249 Ns396p803 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p806 := Ns396p732 Bool.false 6828651 132734 Bool.true 283204381 14148475504056880 1 Bool.false 132395482 Bool.false Bool.false 48695778 143990 BSN.abs_quadSignPos qz394 (BSN.sfrac_eq_quadSignPos_mul Bool.false 132395482 268435456) qz117 rfl (Ns396p801 rfl) (Ns396p770 rfl) RS397to408.d43 RS397to408.d45 RS397to408.d17 (Ns396p805 rfl rfl) rfl 

noncomputable def Ns396p807 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) 48695778 268435456 143990 268435456 48695778 268435456 143990 268435456 26143346745409536 24347889 67108864 71995 67108864 (Ns396p806 rfl rfl rfl rfl) 

noncomputable def Ns396p808 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116) 634285 2097152 1 16777216 108680237930043 140737488355328 300293895510051 10995116277760000000 68934244715457324255 295147905179352825856 

noncomputable def Ns396p809 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz115 1 1 0 1 634285 2097152 1 16777216 634285 2097152 1 16777216 

noncomputable abbrev qz123 := qz446

noncomputable def Ns396p810 := @Enclosure.Real.IsNear.sqrt_image qz123 801976831069 6710886400 150173 6710886400 183404852 183404888 16777216 (@Enclosure.Real.IsNear.of_eq qz123 (@HMul.hMul Real Real Real qz5 qz114 qz3) Bool.false 801976831069 6710886400 150173 6710886400 (BSN.t_div_two_pi_mk qz114 750865 1000 qz117) (@Enclosure.Real.IsNear.mulLit_ff qz114 qz3 750865 1000 0 1 5340353 33554432 1 33554432 801976831069 6710886400 150173 6710886400 (Enclosure.Real.IsNear.const Bool.false 750865 1000) RS397to408.d48 rfl)) 

noncomputable abbrev qz735 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 750865 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz635 := qz735

noncomputable abbrev qz454 := qz635

noncomputable abbrev qz124 := qz454

noncomputable def Ns396p811 := @Enclosure.Real.IsNear.sqrt_image qz124 91702435 8388608 9 8388608 55470918 55470925 16777216 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 366809740 33554432 36 33554432 91702435 8388608 9 8388608 (Ns396p810 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns396p812 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz124) 110941843 33554432 7 33554432 5074279 5074281 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz124) Bool.false 110941843 33554432 7 33554432 110941843 33554432 7 33554432 (Ns396p811 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns396p813 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz124)) Bool.false 10148560 33554432 2 33554432 634285 2097152 1 16777216 (Ns396p812 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz125 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz447))

noncomputable abbrev qz636 := (@HMul.hMul Real Real Real qz707 qz734 qz734)

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz636 qz631) qz593)

noncomputable abbrev qz126 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz455))

noncomputable def Ns396p814 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz116) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz125) qz126) Bool.false 108680237930043 

noncomputable def Ns396p815 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz125) qz126 18445869 16777216 141 

noncomputable def Ns396p816 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz125) Bool.false 36891738 33554432 282 33554432 18445869 16777216 141 

noncomputable def Ns396p817 := @Enclosure.Real.IsNear.recentre' qz125 Bool.false 30519026 33554432 1452304432 209715200000000 15259513 16777216 90769027 13107200000000 

noncomputable abbrev qz127 := (@HMul.hMul Real Real Real qz349 qz346 qz447)

noncomputable def Ns396p818 := @Enclosure.Real.IsNear.cos_image qz127 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 196446427) qz392) Bool.false 196446427 33554432 227 33554432 Bool.false 30519026 33554432 1 

noncomputable def Ns396p819 := nat_lit 242874678748538387294372863 

noncomputable def Ns396p820 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz116 884279719003555 140737488355328 1 500000000000000 7816355 8388608 9 8388608 6911844203032032142025 1180591620717411303424 Ns396p819 

noncomputable def Ns396p821 := @Enclosure.Real.IsNear.subLit_ff_p qz124 qz1 91702435 8388608 9 8388608 10 1 0 1 7816355 7816355 8388608 9 

noncomputable def Ns396p822 := @Ns396p821 8388608 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 366809740 33554432 36 33554432 91702435 8388608 9 8388608 (Ns396p810 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns396p823 := @Enclosure.Real.IsNear.recentre' qz127 Bool.false 6911844203032032142025 1180591620717411303424 Ns396p819 Ns396p579 196446427 33554432 227 33554432 (@Ns396p820 Ns396p579 RS397to408.d47 (Ns396p822 rfl rfl) rfl) 

noncomputable def Ns396p824 := nat_lit 5523198932116860424945664 

noncomputable def Ns396p825 := nat_lit 2560878940889723025663760799945663968947879700328180147341223814726660398271050006552038945 

noncomputable def Ns396p826 := nat_lit 1440413163082678001472810981090926318515090532242465477677650616834609516002445491097121 

noncomputable def Ns396p827 := nat_lit 6704731795304283588545560401126401276062089068569222108453631889952092627683984153031659041 

noncomputable def Ns396p828 := BSN.sin_dyadic_bound_f 78489377587 68719476736 3 2 33554432 12512208 Ns396p825 Ns396p175 Ns396p826 Ns396p827 Ns396p178 Ns396p826 30519026 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 78489377587) qz368 0 2 Ns396p825 Ns396p175 Ns396p826 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 78489377587) qz369 0 2 Ns396p827 Ns396p178 Ns396p826 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p829 := @Ns396p818 6250000 (Ns396p823 rfl) (Enclosure.sfrac_false_div 196446427 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 196446427) qz392) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p824) qz393) 226375608064910080 72057594037927936 Bool.false 30519026 33554432 0 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 196446427 33554432 226375608064910080 72057594037927936 0 Ns396p824 Ns396p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 30519026 33554432 Ns396p824 Ns396p100 78489377587 68719476736 12512208 12500000 (Ns396p828 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p830 := @Enclosure.Real.IsNear.inv_image qz125 15259513 16777216 90769027 13107200000000 18445728 18446010 16777216 (Ns396p817 (Ns396p829 rfl rfl) rfl) rfl 

noncomputable def Ns396p831 := @Enclosure.Real.IsNear.recentre' qz126 Bool.false 11783694 16777216 

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz349 qz346 qz455)

noncomputable def Ns396p832 := @Enclosure.Real.IsNear.cos_image qz128 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 830561)) (@Nat.cast Real Real.instNatCast 1048576)) Bool.true 830561 1048576 

noncomputable def Ns396p833 := nat_lit 7844426913721300044493207045 

noncomputable def Ns396p834 := nat_lit 5834172076701953089845911022858929 

noncomputable def Ns396p835 := @Enclosure.Real.IsNear.recentre' qz128 Bool.true Ns396p833 Ns396p715 Ns396p834 

noncomputable abbrev qz129 := qz455

noncomputable def Ns396p836 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz129 884279719003555 140737488355328 1 500000000000000 8870979108919 

noncomputable abbrev qz456 := (@HSub.hSub Real Real Real qz583 qz636 qz631)

noncomputable abbrev qz130 := qz456

noncomputable def Ns396p837 := @Enclosure.Real.IsNear.subLit_tf qz130 qz29 4472932597815 70368744177664 216191943 70368744177664 1 16 

noncomputable abbrev qz457 := qz636

noncomputable abbrev qz131 := qz457

noncomputable def Ns396p838 := @Enclosure.Real.IsNear.subLit_ff_n qz131 qz116 61095405486025 70368744177664 140694471 70368744177664 7816355 8388608 9 8388608 

noncomputable def Ns396p839 := @Enclosure.Real.IsNear.mulLit_ff qz116 qz116 7816355 8388608 9 8388608 7816355 8388608 9 8388608 61095405486025 70368744177664 

noncomputable def Ns396p840 := nat_lit 966711348625704474411729265012612747087711424828161 

noncomputable def Ns396p841 := nat_lit 226449974140283539265661355544360843023203521281 

noncomputable def Ns396p842 := nat_lit 2899681145928832856156656472326749519577087867441921 

noncomputable def Ns396p843 := BSN.cos_dyadic_bound_f 830561 1048576 3 2 16777216 6250000 Ns396p840 Ns396p477 Ns396p841 Ns396p842 Ns396p480 Ns396p841 11783694 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 830561) (BSN.cosEvenQ 1048576) 0 2 Ns396p840 Ns396p477 Ns396p841 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 830561) (BSN.cosOddQ 1048576) 0 2 Ns396p842 Ns396p480 Ns396p841 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p844 := @Ns396p831 510444304 26214400000000 5891847 8388608 31902769 1638400000000 (@Ns396p832 81 4194304 Bool.false 11783694 16777216 1 6250000 (@Ns396p835 Ns396p718 830561 1048576 81 4194304 (@Ns396p836 70368744177664 216191943 70368744177664 Ns396p833 Ns396p715 Ns396p834 Ns396p718 RS397to408.d47 (@Ns396p837 0 1 141935665742704 8870979108919 70368744177664 216191943 70368744177664 (@Ns396p838 37521678173491691520 4472932597815 70368744177664 216191943 70368744177664 (@Ns396p839 140694471 70368744177664 (Ns396p822 rfl rfl) (Ns396p822 rfl rfl) rfl) (Ns396p822 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 830561 1048576) (BSN.cos_neg_of_bound 830561 1048576 Bool.false 11783694 16777216 1 6250000 (Ns396p843 rfl rfl)) rfl rfl) 

noncomputable def Ns396p845 := @Ns396p808 766133125995460853853 Ns396p363 (Ns396p809 qz31 (@Enclosure.Real.IsNear.of_eq qz115 (@Inv.inv Real Real.instInv (Real.sqrt qz124)) Bool.false 634285 2097152 1 16777216 (BSN.rpow_neg_quarter_mk qz123 (BSN.t_div_two_pi_nonneg qz114 750865 1000 qz117)) Ns396p813) rfl) (@Ns396p814 140737488355328 300293895510051 10995116277760000000 (BSN.correction_mk qz116 (BSN.cos_two_pi_p_ne_zero_mk qz114 750865 1000 10 qz117 rfl rfl (@BSN.floor_sqrt_eq_dec qz114 750865 1000 10 qz117 rfl rfl rfl))) (@Ns396p815 16777216 5891847 8388608 31902769 1638400000000 108680237930043 140737488355328 300293895510051 10995116277760000000 (@Ns396p816 16777216 (Ns396p830 rfl rfl rfl rfl rfl) rfl) (Ns396p844 rfl) rfl)) 

noncomputable def Ns396p846 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (hardyZApproximantRS₀ qz114) Bool.false 38148903553740135201 295147905179352825856 99715307678161860853853 Ns396p363 (@Eq.refl Real (hardyZApproximantRS₀ qz114)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116))) Bool.false 38148903553740135201 295147905179352825856 99715307678161860853853 Ns396p363 (BSN.hardyZApproximantRS₀_eq qz114 10 (@BSN.floor_sqrt_eq_dec qz114 750865 1000 10 qz117 rfl rfl rfl)) (@Ns396p731 38148903553740135201 295147905179352825856 99715307678161860853853 Ns396p363 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10)) Bool.false 24347889 67108864 71995 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (Ns396p807 (Ns396p806 rfl rfl rfl rfl) rfl rfl)) (Ns396p845 rfl) rfl rfl)) 

theorem RS397to408.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz114) Bool.false 38148903553740135201 295147905179352825856 99715307678161860853853 Ns396p363 := Ns396p846 

noncomputable def Ns396p847 := nat_lit 1997161430596431061853841 

noncomputable def Ns396p848 := nat_lit 1844674407370955161600000000 

noncomputable def Ns396p849 := nat_lit 611369234488192091928997658624 

noncomputable abbrev qz736 := (Enclosure.sfrac Bool.false 752179 1000)

noncomputable abbrev qz637 := qz736

noncomputable abbrev qz458 := qz637

noncomputable abbrev qz132 := qz458

noncomputable abbrev qz737 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 752179 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz638 := qz737

noncomputable abbrev qz459 := qz638

noncomputable abbrev qz133 := (@HPow.hPow Real Real Real qz350 qz459 qz352)

noncomputable abbrev qz738 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 752179 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz639 := qz738

noncomputable abbrev qz460 := qz639

noncomputable abbrev qz134 := qz460

noncomputable def Ns396p850 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz133) (Zeta.RiemannSiegel.correction qz134)) 121429425 33554432 144243 134217728 1130550737203917612907 4722366482869645213696 14700734030261461853841 Ns396p848 Ns396p849 

noncomputable def Ns396p851 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos BSN.quadSignPos 9 10 752179 1000 196 268435456 134217728 4503599627370496 Bool.false 382021950251 2526 618095470 44 84886744 8 

noncomputable def Ns396p852 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 752179 1000 89 146 268435456 134217728 4503599627370496 Bool.false 382021950251 2526 

noncomputable def Ns396p853 := Ns396p852 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 361446460 108480 Bool.true 313725864 Bool.true 60998192 14148475504056880 1 Bool.false 247027840 Bool.true Bool.false 261534734 Bool.true Bool.true 535962237 

noncomputable def Ns396p854 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 752179 1000 48 25 268435456 134217728 4503599627370496 Bool.false 382021950251 2526 

noncomputable def Ns396p855 := Ns396p854 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 374409182 80454 Bool.false 5537733 Bool.true 338263942 14148475504056880 1 Bool.false 268378337 Bool.false Bool.false 255585588 Bool.true Bool.true 361446460 

noncomputable def Ns396p856 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 752179 1000 242 135 268435456 134217728 4503599627370496 Bool.false 382021950251 2526 

noncomputable def Ns396p857 := Ns396p856 372130544 43 134217720 8 432030192 43 120047984 16 Bool.true 302531401 47397 Bool.false 72072155 Bool.false 134159646 14148475504056880 1 Bool.false 258818122 Bool.true Bool.false 128643838 Bool.false Bool.true 374409182 

noncomputable def Ns396p858 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 752179 1000 574 379 268435456 134217728 4503599627370496 Bool.false 382021950251 2526 

noncomputable def Ns396p859 := Ns396p858 186065264 43 189812528 16 294906480 43 154981288 8 Bool.true 268435264 2579 Bool.false 36202215 Bool.false 391323718 14148475504056880 1 Bool.false 265997970 Bool.true Bool.false 266723395 Bool.false Bool.true 302531401 

noncomputable def Ns396p860 := nat_lit 41786742337357752475594834533964714597837297550056177982389 

noncomputable def Ns396p861 := nat_lit 29362300325156511172755797554677519131824995094757376000 

noncomputable def Ns396p862 := nat_lit 115570700253841468417072603311520000 

noncomputable def Ns396p863 := nat_lit 521579230031159667162579963578350812480 

noncomputable abbrev qz640 := (@Eq.refl Real qz736)

noncomputable abbrev qz461 := qz640

noncomputable abbrev qz135 := qz461

noncomputable def Ns396p864 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz132 752179 1000 2263093992164 16000000 1504358 4000 2000 Ns396p862 Ns396p863 qz135 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns396p865 := nat_lit 13371757547954480792190347050868708671307935216017976954364480 

noncomputable abbrev qz641 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1504358))))

noncomputable abbrev qz462 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 752179 4000) (Real.log (Enclosure.sfrac Bool.false 2263093992164 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz641))

noncomputable abbrev qz642 := (Enclosure.sfrac Bool.false 752179 2000)

noncomputable abbrev qz136 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz462 qz642) (@HMul.hMul Real Real Real qz349 qz642 (Real.log Real.pi)))

noncomputable def Ns396p866 := @Enclosure.Real.IsNear.addLit_ft_p qz136 (Enclosure.sfrac Bool.true Ns396p862 Ns396p863) 25637063096036797384901 18014398509481984000 38523160410928407 4096000000000000000000 Ns396p862 Ns396p863 0 1 Ns396p865 

noncomputable def Ns396p867 := nat_lit 344094836134270474939775372492800 

noncomputable abbrev qz137 := (@HSub.hSub Real Real Real qz355 qz462 qz642)

noncomputable def Ns396p868 := @Enclosure.Real.IsNear.subLit_ff_p qz137 (@HMul.hMul Real Real Real qz5 qz642 (Real.log Real.pi)) 6678527591919566127553 3602879701896396800 15203592787543 4000000000000000000 28891767798219 67108864000 752179 134217728000 Ns396p867 25637063096036797384901 18014398509481984000 

noncomputable def Ns396p869 := nat_lit 66785275919195661275530000 

noncomputable abbrev qz138 := qz462

noncomputable def Ns396p870 := @Enclosure.Real.IsNear.subLit_ff_p qz138 qz642 40167664087829655259333 18014398509481984000 15203592787543 4000000000000000000 752179 2000 0 1 Ns396p869 6678527591919566127553 3602879701896396800 15203592787543 4000000000000000000 

noncomputable def Ns396p871 := nat_lit 90449538509146444769677611511876419584 

noncomputable def Ns396p872 := nat_lit 57349771256692393795125248 

noncomputable def Ns396p873 := nat_lit 5421696783158770702822876076288754783691627997802240 

noncomputable def Ns396p874 := nat_lit 2619882680237299958511430969224602250234793494528 

noncomputable def Ns396p875 := nat_lit 2274816936486813665513731721323088161887560448 

noncomputable def Ns396p876 := BSN.log_dyadic_bound 165941992164 4360245992164 3 2 Ns396p873 134217728 50000000 Ns396p874 Ns396p875 10221037 4526187984328 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 165941992164) (BSN.artanhQ 4360245992164) 0 2 Ns396p874 Ns396p873 Ns396p875 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz463 := (Real.log (Enclosure.sfrac Bool.false 2263093992164 16000000))

noncomputable def Ns396p877 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 752179 4000) qz463 752179 4000 0 1 53411136620391527 4503599627370496 20000017 1000000000000000 40174735331989478387333 18014398509481984000 15043592787043 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 752179 4000) (BSN.isNear_log_sfrac 2263093992164 16000000 53411136620391527 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2263093992164) qz358)) Bool.false Ns396p872 Ns396p100 1000000850000000 50000000000000000000000 53411136620391527 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2263093992164 16000000 17 4526187984328 4194304000000 10221037 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns396p876 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns396p878 := BSN.arctan_dyadic_bound_f 1000 1504358 1 0 16777216 6250000 0 1 1 0 1 1 11152 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1504358) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1504358) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz464 := (@Nat.cast Real Real.instNatCast 1504358)

noncomputable def Ns396p879 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz464)) 884279719003555 562949953421312 1 2000000000000000 11152 16777216 1 6250000 14829473832261392531456 883905519977891 562949953421312 320000001 2000000000000000 qz15 (Ns396p878 rfl) rfl rfl 

noncomputable abbrev qz465 := (@HMul.hMul Real Real Real qz579 qz584 qz641)

noncomputable abbrev qz139 := qz465

noncomputable abbrev qz466 := qz641

noncomputable abbrev qz140 := qz466

noncomputable def Ns396p880 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 752179 4000) qz463) qz139 40174735331989478387333 18014398509481984000 15043592787043 4000000000000000000 883905519977891 2251799813685248 320000001 8000000000000000 Ns396p871 40167664087829655259333 18014398509481984000 15203592787543 4000000000000000000 (Ns396p877 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz140 1 4 0 1 883905519977891 562949953421312 320000001 2000000000000000 883905519977891 2251799813685248 320000001 8000000000000000 qz366 Ns396p879 rfl) 

noncomputable def Ns396p881 := @Ns396p866 Ns396p860 Ns396p861 38523160410928407 4096000000000000000000 (@Ns396p868 38523160410928407 4096000000000000000000 (Ns396p870 (Ns396p880 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 752179 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz642 (Real.log Real.pi) 752179 2000 0 1 38410761 33554432 1 67108864 28891767798219 67108864000 752179 134217728000 (Enclosure.Real.IsNear.const Bool.false 752179 2000) RS397to408.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns396p862 Ns396p863) 

noncomputable def Ns396p882 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz132) Bool.false Ns396p860 Ns396p861 38523160410928407 4096000000000000000000 47752743781 33554432 317 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz132) (@HAdd.hAdd Real Real Real qz367 qz136 (Enclosure.sfrac Bool.true Ns396p862 Ns396p863)) Bool.false Ns396p860 Ns396p861 38523160410928407 4096000000000000000000 Ns396p864 (Ns396p881 rfl rfl)) 

noncomputable def Ns396p883 := BSN.cos_dyadic_bound_f 81981112 68719476736 1 0 33554432 12512208 0 1 1 0 1 1 33554408 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 81981112) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 81981112) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns396p884 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz132) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47752743781) qz392) Bool.false 47752743781 33554432 317 33554432 Bool.true 33554408 33554432 1 6250000 (Ns396p882 rfl) (Enclosure.sfrac_false_div 47752743781 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47752743781) qz392) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5768907926607780380672) qz393) 226375608064910080 72057594037927936 Bool.false 33554408 33554432 226 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q2 47752743781 33554432 226375608064910080 72057594037927936 226 5768907926607780380672 Ns396p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554408 33554432 5768907926607780380672 Ns396p100 81981112 68719476736 12512208 12500000 (Ns396p883 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p885 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz132) Bool.false Ns396p860 Ns396p861 38523160410928407 4096000000000000000000 382021950251 268435456 2526 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz132) (@HAdd.hAdd Real Real Real qz367 qz136 (Enclosure.sfrac Bool.true Ns396p862 Ns396p863)) Bool.false Ns396p860 Ns396p861 38523160410928407 4096000000000000000000 Ns396p864 (Ns396p881 rfl rfl)) 

noncomputable def Ns396p886 := Ns396p859 47397 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 574 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 265997970 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 379 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266723395 268435456) qz135 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 1) Bool.true 4194301 4194304 125925277 13107200000000 268435264 268435456 2579 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz132)) Bool.true 4194301 4194304 125925277 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz132) qz132) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz132)) Bool.true 33554408 33554432 2014804432 209715200000000 4194301 4194304 125925277 13107200000000 (Ns396p884 rfl rfl) rfl)) rfl) (Ns396p885 rfl) RS397to408.d7 

noncomputable def Ns396p887 := nat_lit 1717673332219534541427743750625 

noncomputable def Ns396p888 := BSN.cos_dyadic_bound_f 36202215 268435456 2 1 268435456 134217728 Ns396p887 Ns396p141 Ns396p887 Ns396p887 Ns396p142 Ns396p887 265997970 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 36202215) qz372 0 1 Ns396p887 Ns396p141 Ns396p887 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 36202215) qz373 0 1 Ns396p887 Ns396p142 Ns396p887 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p889 := nat_lit 32855727378014377329817778854403780434610037698612247742726117754164081910525311039985643090029266967806283776 

noncomputable def Ns396p890 := nat_lit 12895377306521305606076528173478763048166787149073940230820816997872049885773721576593348499125335166976 

noncomputable def Ns396p891 := nat_lit 164127141194522760301656476087090829741514857720637825664212889573210382922639973386364460898490907736867803136 

noncomputable def Ns396p892 := BSN.sin_dyadic_bound_f 391323718 268435456 4 3 268435456 134217728 Ns396p889 Ns396p258 Ns396p890 Ns396p891 Ns396p261 Ns396p890 266723395 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 391323718) qz370 0 3 Ns396p889 Ns396p258 Ns396p890 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 391323718) qz371 0 3 Ns396p891 Ns396p261 Ns396p890 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p893 := nat_lit 26981744884102820517782653200625 

noncomputable def Ns396p894 := BSN.cos_dyadic_bound_f 72072155 268435456 2 1 268435456 134217728 Ns396p893 Ns396p141 Ns396p893 Ns396p893 Ns396p142 Ns396p893 258818122 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 72072155) qz372 0 1 Ns396p893 Ns396p141 Ns396p893 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 72072155) qz373 0 1 Ns396p893 Ns396p142 Ns396p893 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p895 := nat_lit 5086720512376227417684511803343730452355872768683400537243974248136960 

noncomputable def Ns396p896 := nat_lit 104948256773044807950589269822427459262922269405878966388743700736 

noncomputable def Ns396p897 := nat_lit 13322193330474391640437039483272914873617050615258439507788636493414656 

noncomputable def Ns396p898 := BSN.sin_dyadic_bound_f 134159646 268435456 3 2 268435456 134217728 Ns396p895 Ns396p121 Ns396p896 Ns396p897 Ns396p124 Ns396p896 128643838 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 134159646) qz370 0 2 Ns396p895 Ns396p121 Ns396p896 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 134159646) qz371 0 2 Ns396p897 Ns396p124 Ns396p896 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p899 := Ns396p857 80454 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 242 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 258818122 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 135 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 128643838 268435456) qz135 rfl rfl (Ns396p886 RS397to408.d9 RS397to408.d11 RS397to408.d13 RS397to408.d17 (Ns396p888 rfl rfl) (Ns396p892 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns396p885 rfl) RS397to408.d19 RS397to408.d21 RS397to408.d23 RS397to408.d25 RS397to408.d17 (Ns396p894 rfl rfl) (Ns396p898 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns396p900 := nat_lit 940433411384307024199345521 

noncomputable def Ns396p901 := BSN.cos_dyadic_bound_f 5537733 268435456 2 1 268435456 134217728 Ns396p900 Ns396p141 Ns396p900 Ns396p900 Ns396p142 Ns396p900 268378337 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 5537733) qz372 0 1 Ns396p900 Ns396p141 Ns396p900 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 5537733) qz373 0 1 Ns396p900 Ns396p142 Ns396p900 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p902 := nat_lit 18331709022655382626008266245335761383345537530223275127015860404994554155646521224712312469960847558496423936 

noncomputable def Ns396p903 := nat_lit 2244235707201498479192667457234694673308132605664117451542763002672638862745145928458618661864788135936 

noncomputable def Ns396p904 := nat_lit 91611328889246499112976354525500111566461791862891675850448067219332418642536301417556589050644570836682346496 

noncomputable def Ns396p905 := BSN.sin_dyadic_bound_f 338263942 268435456 4 3 268435456 134217728 Ns396p902 Ns396p258 Ns396p903 Ns396p904 Ns396p261 Ns396p903 255585588 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 338263942) qz370 0 3 Ns396p902 Ns396p258 Ns396p903 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 338263942) qz371 0 3 Ns396p904 Ns396p261 Ns396p903 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p906 := Ns396p855 108480 BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268378337 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 255585588 268435456) qz135 rfl rfl (Ns396p899 rfl rfl) (Ns396p885 rfl) RS397to408.d27 RS397to408.d29 RS397to408.d31 RS397to408.d33 RS397to408.d17 (Ns396p901 rfl rfl) (Ns396p905 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p907 := nat_lit 152198530339596095679554828829535124354586673775067546638988742880133120 

noncomputable def Ns396p908 := nat_lit 93843153239978748278130032995536264262209937446218862858653984096256 

noncomputable def Ns396p909 := nat_lit 398463261974648856425431388785837314596064377131216363038437458235621376 

noncomputable def Ns396p910 := BSN.sin_dyadic_bound_f 313725864 268435456 3 2 268435456 134217728 Ns396p907 Ns396p121 Ns396p908 Ns396p909 Ns396p124 Ns396p908 247027840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 313725864) qz370 0 2 Ns396p907 Ns396p121 Ns396p908 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 313725864) qz371 0 2 Ns396p909 Ns396p124 Ns396p908 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p911 := nat_lit 13844199546387215608794143850496 

noncomputable def Ns396p912 := BSN.cos_dyadic_bound_f 60998192 268435456 2 1 268435456 134217728 Ns396p911 Ns396p141 Ns396p911 Ns396p911 Ns396p142 Ns396p911 261534734 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 60998192) qz372 0 1 Ns396p911 Ns396p141 Ns396p911 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 60998192) qz373 0 1 Ns396p911 Ns396p142 Ns396p911 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p913 := Ns396p853 132968 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 89 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 247027840 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 146 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 261534734 268435456) qz135 rfl rfl (Ns396p906 rfl) (Ns396p885 rfl) RS397to408.d35 RS397to408.d37 RS397to408.d39 RS397to408.d41 RS397to408.d17 (Ns396p910 rfl rfl) (Ns396p912 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p914 := nat_lit 34985873599848098932766548638782393507851736829185671890402572285971201 

noncomputable def Ns396p915 := nat_lit 16071216956861258656197623925133063195147643643201683235863228517121 

noncomputable def Ns396p916 := nat_lit 104925478365630574280987250668496914397164915200270612304735990400879361 

noncomputable def Ns396p917 := BSN.cos_dyadic_bound_f 251626337 268435456 3 2 268435456 134217728 Ns396p914 Ns396p252 Ns396p915 Ns396p916 Ns396p255 Ns396p915 158887180 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 251626337) qz372 0 2 Ns396p914 Ns396p252 Ns396p915 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 251626337) qz373 0 2 Ns396p916 Ns396p255 Ns396p915 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p918 := Ns396p851 Bool.true 535962237 132968 Bool.true 251626337 14148475504056880 1 Bool.false 158887180 Bool.false Bool.true 485717700 144243 BSN.abs_quadSignPos qz394 (BSN.sfrac_eq_quadSignPos_mul Bool.false 158887180 268435456) qz135 rfl (Ns396p913 rfl) (Ns396p885 rfl) RS397to408.d43 RS397to408.d45 RS397to408.d17 (Ns396p917 rfl rfl) rfl 

noncomputable def Ns396p919 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) 485717700 268435456 144243 268435456 485717700 268435456 144243 268435456 260767704573542400 121429425 33554432 144243 134217728 (Ns396p918 rfl rfl rfl rfl) 

noncomputable def Ns396p920 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz133) (Zeta.RiemannSiegel.correction qz134) 2536031 8388608 1 16777216 445795314490997 562949953421312 5762414478250739 219902325555200000000 1130550737203917612907 4722366482869645213696 

noncomputable def Ns396p921 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz133 1 1 0 1 2536031 8388608 1 16777216 2536031 8388608 1 16777216 

noncomputable abbrev qz141 := qz459

noncomputable def Ns396p922 := @Enclosure.Real.IsNear.sqrt_image qz141 4016901379187 33554432000 752179 33554432000 183565260 183565295 16777216 (@Enclosure.Real.IsNear.of_eq qz141 (@HMul.hMul Real Real Real qz5 qz132 qz3) Bool.false 4016901379187 33554432000 752179 33554432000 (BSN.t_div_two_pi_mk qz132 752179 1000 qz135) (@Enclosure.Real.IsNear.mulLit_ff qz132 qz3 752179 1000 0 1 5340353 33554432 1 33554432 4016901379187 33554432000 752179 33554432000 (Enclosure.Real.IsNear.const Bool.false 752179 1000) RS397to408.d48 rfl)) 

noncomputable abbrev qz739 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 752179 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz643 := qz739

noncomputable abbrev qz467 := qz643

noncomputable abbrev qz142 := qz467

noncomputable def Ns396p923 := @Enclosure.Real.IsNear.sqrt_image qz142 367130555 33554432 35 33554432 55495171 55495177 16777216 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 367130555 33554432 35 33554432 367130555 33554432 35 33554432 (Ns396p922 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns396p924 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz142) 27747587 8388608 3 16777216 5072061 5072063 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz142) Bool.false 110990348 33554432 6 33554432 27747587 8388608 3 16777216 (Ns396p923 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns396p925 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz142)) Bool.false 10144124 33554432 2 33554432 2536031 8388608 1 16777216 (Ns396p924 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz143 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz460))

noncomputable abbrev qz644 := (@HMul.hMul Real Real Real qz707 qz738 qz738)

noncomputable abbrev qz468 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz644 qz639) qz593)

noncomputable abbrev qz144 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz468))

noncomputable def Ns396p926 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz134) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz143) qz144) Bool.false 445795314490997 

noncomputable def Ns396p927 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz143) qz144 35969803 33554432 261 

noncomputable def Ns396p928 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz143) Bool.false 35969803 33554432 261 33554432 35969803 33554432 261 

noncomputable def Ns396p929 := @Enclosure.Real.IsNear.recentre' qz143 Bool.false 31301253 33554432 1414804432 209715200000000 31301253 33554432 88425277 13107200000000 

noncomputable abbrev qz145 := (@HMul.hMul Real Real Real qz349 qz346 qz460)

noncomputable def Ns396p930 := @Enclosure.Real.IsNear.cos_image qz145 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 198462167) qz392) Bool.false 198462167 33554432 221 33554432 Bool.false 31301253 33554432 1 

noncomputable def Ns396p931 := nat_lit 188902527917573056717690993 

noncomputable def Ns396p932 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz134 884279719003555 140737488355328 1 500000000000000 31586235 33554432 35 33554432 27931067010180254065425 4722366482869645213696 Ns396p931 

noncomputable def Ns396p933 := @Enclosure.Real.IsNear.subLit_ff_p qz142 qz1 367130555 33554432 35 33554432 10 1 0 1 31586235 31586235 33554432 35 

noncomputable def Ns396p934 := @Ns396p933 33554432 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 367130555 33554432 35 33554432 367130555 33554432 35 33554432 (Ns396p922 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns396p935 := @Enclosure.Real.IsNear.recentre' qz145 Bool.false 27931067010180254065425 4722366482869645213696 Ns396p931 Ns396p300 198462167 33554432 221 33554432 (@Ns396p932 Ns396p300 RS397to408.d47 (Ns396p934 rfl rfl) rfl) 

noncomputable def Ns396p936 := nat_lit 5813697681328886140370944 

noncomputable def Ns396p937 := nat_lit 3144066113633607202514288514125951971150389526926820020628206038352142410146899282213719585 

noncomputable def Ns396p938 := nat_lit 2170606751344228507636481881694113957054929686865579337129245504388820790189648536391201 

noncomputable def Ns396p939 := nat_lit 8230944553347747255667915613949988501844359827220079592242330369629457745295857736738917921 

noncomputable def Ns396p940 := BSN.sin_dyadic_bound_f 82617613107 68719476736 3 2 33554432 12512208 Ns396p937 Ns396p175 Ns396p938 Ns396p939 Ns396p178 Ns396p938 31301253 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 82617613107) qz368 0 2 Ns396p937 Ns396p175 Ns396p938 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 82617613107) qz369 0 2 Ns396p939 Ns396p178 Ns396p938 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p941 := @Ns396p930 6250000 (Ns396p935 rfl) (Enclosure.sfrac_false_div 198462167 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 198462167) qz392) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p936) qz393) 226375608064910080 72057594037927936 Bool.false 31301253 33554432 0 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 198462167 33554432 226375608064910080 72057594037927936 0 Ns396p936 Ns396p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 31301253 33554432 Ns396p936 Ns396p100 82617613107 68719476736 12512208 12500000 (Ns396p940 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p942 := @Enclosure.Real.IsNear.inv_image qz143 31301253 33554432 88425277 13107200000000 17984771 17985032 16777216 (Ns396p929 (Ns396p941 rfl rfl) rfl) rfl 

noncomputable def Ns396p943 := @Enclosure.Real.IsNear.recentre' qz144 Bool.false 12393599 16777216 

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz349 qz346 qz468)

noncomputable def Ns396p944 := @Enclosure.Real.IsNear.cos_image qz146 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 12408979)) qz413) Bool.true 12408979 16777216 

noncomputable def Ns396p945 := nat_lit 117199495624293514392774884245 

noncomputable def Ns396p946 := nat_lit 91359814560013322911579083884856493 

noncomputable def Ns396p947 := @Enclosure.Real.IsNear.recentre' qz146 Bool.true Ns396p945 Ns396p185 Ns396p946 

noncomputable abbrev qz147 := qz468

noncomputable def Ns396p948 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz147 884279719003555 140737488355328 1 500000000000000 132536677145959 

noncomputable abbrev qz469 := (@HSub.hSub Real Real Real qz583 qz644 qz639)

noncomputable abbrev qz148 := qz469

noncomputable def Ns396p949 := @Enclosure.Real.IsNear.subLit_tf qz148 qz29 62167932968295 1125899906842624 3385442795 1125899906842624 1 16 

noncomputable abbrev qz470 := qz644

noncomputable abbrev qz149 := qz470

noncomputable def Ns396p950 := @Enclosure.Real.IsNear.subLit_ff_n qz149 qz134 997690241475225 1125899906842624 2211037675 1125899906842624 31586235 33554432 35 33554432 

noncomputable def Ns396p951 := @Enclosure.Real.IsNear.mulLit_ff qz134 qz134 31586235 33554432 35 33554432 31586235 33554432 35 33554432 997690241475225 1125899906842624 

noncomputable def Ns396p952 := nat_lit 3156533632850296531104513830738448158625258024248145923262241 

noncomputable def Ns396p953 := nat_lit 562196835571180996695022206395768606731732040196208707361 

noncomputable def Ns396p954 := nat_lit 9468476504879747231320151447802552938662310608664045352372001 

noncomputable def Ns396p955 := BSN.cos_dyadic_bound_f 12408979 16777216 3 2 16777216 6250000 Ns396p952 Ns396p603 Ns396p953 Ns396p954 Ns396p606 Ns396p953 12393599 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 12408979) (BSN.cosEvenQ 16777216) 0 2 Ns396p952 Ns396p603 Ns396p953 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 12408979) (BSN.cosOddQ 16777216) 0 2 Ns396p954 Ns396p606 Ns396p953 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p956 := @Ns396p943 4002304432 209715200000000 12393599 16777216 250144027 13107200000000 (@Ns396p944 635 33554432 Bool.false 12393599 16777216 1 6250000 (@Ns396p947 Ns396p188 12408979 16777216 635 33554432 (@Ns396p948 1125899906842624 3385442795 1125899906842624 Ns396p945 Ns396p185 Ns396p946 Ns396p188 RS397to408.d47 (@Ns396p949 0 1 2120586834335344 132536677145959 1125899906842624 3385442795 1125899906842624 (@Ns396p950 2086009679365212733440 62167932968295 1125899906842624 3385442795 1125899906842624 (@Ns396p951 2211037675 1125899906842624 (Ns396p934 rfl rfl) (Ns396p934 rfl rfl) rfl) (Ns396p934 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 12408979 16777216) (BSN.cos_neg_of_bound 12408979 16777216 Bool.false 12393599 16777216 1 6250000 (Ns396p955 rfl rfl)) rfl rfl) 

noncomputable def Ns396p957 := @Ns396p920 14700734030261461853841 Ns396p848 (Ns396p921 qz31 (@Enclosure.Real.IsNear.of_eq qz133 (@Inv.inv Real Real.instInv (Real.sqrt qz142)) Bool.false 2536031 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz141 (BSN.t_div_two_pi_nonneg qz132 752179 1000 qz135)) Ns396p925) rfl) (@Ns396p926 562949953421312 5762414478250739 219902325555200000000 (BSN.correction_mk qz134 (BSN.cos_two_pi_p_ne_zero_mk qz132 752179 1000 10 qz135 rfl rfl (@BSN.floor_sqrt_eq_dec qz132 752179 1000 10 qz135 rfl rfl rfl))) (@Ns396p927 33554432 12393599 16777216 250144027 13107200000000 445795314490997 562949953421312 5762414478250739 219902325555200000000 (@Ns396p928 33554432 (Ns396p942 rfl rfl rfl rfl rfl) rfl) (Ns396p956 rfl) rfl)) 

noncomputable def Ns396p958 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz132) (hardyZApproximantRS₀ qz132) Bool.true 18220223024135592339307 4722366482869645213696 Ns396p847 Ns396p848 (@Eq.refl Real (hardyZApproximantRS₀ qz132)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz132) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz133) (Zeta.RiemannSiegel.correction qz134))) Bool.true 18220223024135592339307 4722366482869645213696 Ns396p847 Ns396p848 (BSN.hardyZApproximantRS₀_eq qz132 10 (@BSN.floor_sqrt_eq_dec qz132 752179 1000 10 qz135 rfl rfl rfl)) (@Ns396p850 18220223024135592339307 4722366482869645213696 Ns396p847 Ns396p848 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10)) Bool.true 121429425 33554432 144243 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (Ns396p919 (Ns396p918 rfl rfl rfl rfl) rfl rfl)) (Ns396p957 rfl) rfl rfl)) 

theorem RS397to408.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz132) Bool.true 18220223024135592339307 4722366482869645213696 Ns396p847 Ns396p848 := Ns396p958 

noncomputable def Ns396p959 := nat_lit 18446744073709551616000000 

noncomputable def Ns396p960 := nat_lit 1920809869517308912286992171008 

noncomputable abbrev qz740 := (Enclosure.sfrac Bool.false 753491 1000)

noncomputable abbrev qz645 := qz740

noncomputable abbrev qz471 := qz645

noncomputable abbrev qz150 := qz471

noncomputable abbrev qz741 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 753491 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz646 := qz741

noncomputable abbrev qz472 := qz646

noncomputable abbrev qz151 := (@HPow.hPow Real Real Real qz350 qz472 qz352)

noncomputable abbrev qz742 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 753491 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz647 := qz742

noncomputable abbrev qz473 := qz647

noncomputable abbrev qz152 := qz473

noncomputable def Ns396p961 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz151) (Zeta.RiemannSiegel.correction qz152)) 439683117 134217728 72245 67108864 1158825645500002801083 4722366482869645213696 149421669591792652923 Ns396p959 Ns396p960 

noncomputable def Ns396p962 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.cos BSN.quadSignPos 9 10 753491 1000 196 268435456 134217728 4503599627370496 Bool.false 382864729136 2530 618095470 44 84886744 8 

noncomputable def Ns396p963 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 753491 1000 89 145 268435456 134217728 4503599627370496 Bool.false 382864729136 2530 

noncomputable def Ns396p964 := Ns396p963 558195838 44 94906264 8 589812974 44 89478488 8 Bool.false 536335509 108665 Bool.true 203299918 Bool.true 413711357 14148475504056880 1 Bool.false 184414915 Bool.true Bool.false 268317857 Bool.true Bool.false 381695703 

noncomputable def Ns396p965 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 753491 1000 48 25 268435456 134217728 4503599627370496 Bool.false 382864729136 2530 

noncomputable def Ns396p966 := Ns396p965 480971758 44 109588312 8 522351262 44 101459064 8 Bool.false 524018004 80590 Bool.false 217281672 Bool.true 180809912 14148475504056880 1 Bool.false 185195198 Bool.false Bool.false 167444616 Bool.true Bool.false 536335509 

noncomputable def Ns396p967 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 753491 1000 243 135 268435456 134217728 4503599627370496 Bool.false 382864729136 2530 

noncomputable def Ns396p968 := Ns396p967 372130544 43 134217720 8 432030192 43 120047984 16 Bool.false 401601956 47475 Bool.false 4958338 Bool.false 410114919 14148475504056880 1 Bool.false 4958056 Bool.false Bool.false 268187334 Bool.false Bool.false 524018004 

noncomputable def Ns396p969 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 753491 1000 575 381 268435456 134217728 4503599627370496 Bool.false 382864729136 2530 

noncomputable def Ns396p970 := Ns396p969 186065264 43 189812528 16 294906480 43 154981288 8 Bool.false 268435368 2579 Bool.false 213206046 Bool.false 3870444 14148475504056880 1 Bool.false 191486093 Bool.false Bool.false 3870309 Bool.true Bool.false 401601956 

noncomputable def Ns396p971 := nat_lit 42319131436866170275324167345815544308472476658844272017621 

noncomputable def Ns396p972 := nat_lit 29670937227330799934415953752681829678960453401706496000 

noncomputable def Ns396p973 := nat_lit 116582152152606494194330068056480000 

noncomputable def Ns396p974 := nat_lit 527061722751845705915058348848167030080 

noncomputable abbrev qz648 := (@Eq.refl Real qz740)

noncomputable abbrev qz474 := qz648

noncomputable abbrev qz153 := qz474

noncomputable def Ns396p975 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz150 753491 1000 2270995748324 16000000 1506982 4000 2000 Ns396p973 Ns396p974 qz153 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns396p976 := nat_lit 13542122059797174488103733550660974178711192530830167045638720 

noncomputable abbrev qz649 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1506982))))

noncomputable abbrev qz475 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 753491 4000) (Real.log (Enclosure.sfrac Bool.false 2270995748324 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz649))

noncomputable abbrev qz650 := (Enclosure.sfrac Bool.false 753491 2000)

noncomputable abbrev qz154 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz475 qz650) (@HMul.hMul Real Real Real qz349 qz650 (Real.log Real.pi)))

noncomputable def Ns396p977 := @Enclosure.Real.IsNear.addLit_ft_p qz154 (Enclosure.sfrac Bool.true Ns396p973 Ns396p974) 25693621022694726867109 18014398509481984000 38590069256267703 4096000000000000000000 Ns396p973 Ns396p974 0 1 Ns396p976 

noncomputable def Ns396p978 := nat_lit 344853943775912267768392790835200 

noncomputable abbrev qz155 := (@HSub.hSub Real Real Real qz355 qz475 qz650)

noncomputable def Ns396p979 := @Enclosure.Real.IsNear.subLit_ff_p qz155 (@HMul.hMul Real Real Real qz5 qz650 (Real.log Real.pi)) 6692544733833027368993 3602879701896396800 15229832809847 4000000000000000000 28942162716651 67108864000 753491 134217728000 Ns396p978 25693621022694726867109 18014398509481984000 

noncomputable def Ns396p980 := nat_lit 66925447338330273689930000 

noncomputable abbrev qz156 := qz475

noncomputable def Ns396p981 := @Enclosure.Real.IsNear.subLit_ff_p qz156 qz650 40249567242819181648037 18014398509481984000 15229832809847 4000000000000000000 753491 2000 0 1 Ns396p980 6692544733833027368993 3602879701896396800 15229832809847 4000000000000000000 

noncomputable def Ns396p982 := nat_lit 90633968018292094281870107003035058176 

noncomputable def Ns396p983 := nat_lit 57366626068369820423815168 

noncomputable def Ns396p984 := nat_lit 5461105131243067996409795952447515475959200952528640 

noncomputable def Ns396p985 := nat_lit 2885993347480955814808996249477205406715729348608 

noncomputable def Ns396p986 := nat_lit 2740044174254186345337175225130676463038505728 

noncomputable def Ns396p987 := BSN.log_dyadic_bound 173843748324 4368147748324 3 2 Ns396p984 134217728 50000000 Ns396p985 Ns396p986 10688852 4541991496648 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 173843748324) (BSN.artanhQ 4368147748324) 0 2 Ns396p985 Ns396p984 Ns396p986 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz476 := (Real.log (Enclosure.sfrac Bool.false 2270995748324 16000000))

noncomputable def Ns396p988 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 753491 4000) qz476 753491 4000 0 1 53426833886997607 4503599627370496 20000017 1000000000000000 40256638492347713896037 18014398509481984000 15069832809347 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 753491 4000) (BSN.isNear_log_sfrac 2270995748324 16000000 53426833886997607 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2270995748324) qz358)) Bool.false Ns396p983 Ns396p100 1000000850000000 50000000000000000000000 53426833886997607 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2270995748324 16000000 17 4541991496648 4194304000000 10688852 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns396p987 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns396p989 := BSN.arctan_dyadic_bound_f 1000 1506982 1 0 16777216 6250000 0 1 1 0 1 1 11132 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1506982) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1506982) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns396p990 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1506982))) 884279719003555 562949953421312 1 2000000000000000 11132 16777216 1 6250000 14829485091260460957696 883906191066531 562949953421312 320000001 2000000000000000 qz15 (Ns396p989 rfl) rfl rfl 

noncomputable abbrev qz477 := (@HMul.hMul Real Real Real qz579 qz584 qz649)

noncomputable abbrev qz157 := qz477

noncomputable abbrev qz478 := qz649

noncomputable abbrev qz158 := qz478

noncomputable def Ns396p991 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 753491 4000) qz476) qz157 40256638492347713896037 18014398509481984000 15069832809347 4000000000000000000 883906191066531 2251799813685248 320000001 8000000000000000 Ns396p982 40249567242819181648037 18014398509481984000 15229832809847 4000000000000000000 (Ns396p988 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz158 1 4 0 1 883906191066531 562949953421312 320000001 2000000000000000 883906191066531 2251799813685248 320000001 8000000000000000 qz366 Ns396p990 rfl) 

noncomputable def Ns396p992 := @Ns396p977 Ns396p971 Ns396p972 38590069256267703 4096000000000000000000 (@Ns396p979 38590069256267703 4096000000000000000000 (Ns396p981 (Ns396p991 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 753491 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz650 (Real.log Real.pi) 753491 2000 0 1 38410761 33554432 1 67108864 28942162716651 67108864000 753491 134217728000 (Enclosure.Real.IsNear.const Bool.false 753491 2000) RS397to408.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns396p973 Ns396p974) 

noncomputable def Ns396p993 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz150) Bool.false Ns396p971 Ns396p972 38590069256267703 4096000000000000000000 23929045571 16777216 317 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz150) (@HAdd.hAdd Real Real Real qz367 qz154 (Enclosure.sfrac Bool.true Ns396p973 Ns396p974)) Bool.false Ns396p971 Ns396p972 38590069256267703 4096000000000000000000 Ns396p975 (Ns396p992 rfl rfl)) 

noncomputable def Ns396p994 := nat_lit 3796009352232007423229952 

noncomputable def Ns396p995 := nat_lit 3503641689547394505899072080985550977858144224511231940154920297143943538861427284176975766723009885707094204326818537668381621716061782016 

noncomputable def Ns396p996 := nat_lit 2487308340644643499022190971193974897192192849848993158130770622972310979171608100192167692046681010790904182682411781228572616687616 

noncomputable def Ns396p997 := nat_lit 17496484358092641011374850799290322888216725085264637532878163074469589241752598946641213273702396210366149254877650389319048745754952728576 

noncomputable def Ns396p998 := BSN.sin_dyadic_bound_f 107889074804 68719476736 4 3 33554432 12512208 Ns396p995 Ns396p112 Ns396p996 Ns396p997 Ns396p115 Ns396p996 33554421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107889074804) qz368 0 3 Ns396p995 Ns396p112 Ns396p996 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107889074804) qz369 0 3 Ns396p997 Ns396p115 Ns396p996 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p999 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz150) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23929045571) qz413) Bool.false 23929045571 16777216 317 33554432 Bool.false 33554421 33554432 1 6250000 (Ns396p993 rfl) (Enclosure.sfrac_false_div 23929045571 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23929045571) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p994) qz414) 226375608064910080 72057594037927936 Bool.false 33554421 33554432 226 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 23929045571 16777216 226375608064910080 72057594037927936 226 Ns396p994 Ns396p399 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554421 33554432 Ns396p994 Ns396p399 107889074804 68719476736 12512208 12500000 (Ns396p998 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p1000 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz150) Bool.false Ns396p971 Ns396p972 38590069256267703 4096000000000000000000 382864729136 268435456 2530 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz150) (@HAdd.hAdd Real Real Real qz367 qz154 (Enclosure.sfrac Bool.true Ns396p973 Ns396p974)) Bool.false Ns396p971 Ns396p972 38590069256267703 4096000000000000000000 Ns396p975 (Ns396p992 rfl rfl)) 

noncomputable def Ns396p1001 := Ns396p970 47475 BSN.abs_quadSignPos (BSN.cos_quad_nat3 575 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 191486093 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 381 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 3870309 268435456) qz153 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 1) Bool.false 33554421 33554432 125925277 13107200000000 268435368 268435456 2579 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz150)) Bool.false 33554421 33554432 125925277 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz150) qz150) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz150)) Bool.false 33554421 33554432 2014804432 209715200000000 33554421 33554432 125925277 13107200000000 (Ns396p999 rfl rfl) rfl)) rfl) (Ns396p1000 rfl) RS397to408.d7 

noncomputable def Ns396p1002 := nat_lit 32448641174693869076750362912029279122285490666909773015395027533922560 

noncomputable def Ns396p1003 := nat_lit 4269687877718115104614706609134114550335117809650404515469136199936 

noncomputable def Ns396p1004 := nat_lit 84977623581920018252748240958899990087190028222595685813961931606425856 

noncomputable def Ns396p1005 := BSN.sin_dyadic_bound_f 213206046 268435456 3 2 268435456 134217728 Ns396p1002 Ns396p121 Ns396p1003 Ns396p1004 Ns396p124 Ns396p1003 191486093 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 213206046) qz370 0 2 Ns396p1002 Ns396p121 Ns396p1003 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 213206046) qz371 0 2 Ns396p1004 Ns396p124 Ns396p1003 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1006 := BSN.sin_dyadic_bound_f 3870444 268435456 1 0 268435456 134217728 0 1 1 0 1 1 3870309 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 3870444) qz370 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 3870444) qz371 0 0 rfl) rfl rfl 

noncomputable def Ns396p1007 := BSN.sin_dyadic_bound_f 4958338 268435456 1 0 268435456 134217728 0 1 1 0 1 1 4958056 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 4958338) qz370 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 4958338) qz371 0 0 rfl) rfl rfl 

noncomputable def Ns396p1008 := nat_lit 39648100117327010185735180581049557422431879941546914559250212452835630837845516800915771729317262176187667361 

noncomputable def Ns396p1009 := nat_lit 22639499318835931036115960765944635945255383103982734319441045282739718666833244946234480177849464083361 

noncomputable def Ns396p1010 := nat_lit 198020012066230648400530714826372541168346661660781484227908567749227796070286652360965215086117539832883925921 

noncomputable def Ns396p1011 := BSN.sin_dyadic_bound_f 410114919 268435456 4 3 268435456 134217728 Ns396p1008 Ns396p258 Ns396p1009 Ns396p1010 Ns396p261 Ns396p1009 268187334 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 410114919) qz370 0 3 Ns396p1008 Ns396p258 Ns396p1009 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 410114919) qz371 0 3 Ns396p1010 Ns396p261 Ns396p1009 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1012 := Ns396p968 80590 BSN.abs_quadSignPos (BSN.cos_quad_nat3 243 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 4958056 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 135 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268187334 268435456) qz153 rfl rfl (Ns396p1001 RS397to408.d9 RS397to408.d11 RS397to408.d13 RS397to408.d17 (Ns396p1005 rfl rfl) (Ns396p1006 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns396p1000 rfl) RS397to408.d19 RS397to408.d21 RS397to408.d23 RS397to408.d25 RS397to408.d17 (Ns396p1007 rfl rfl) (Ns396p1011 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns396p1013 := nat_lit 19447873936015771559962934366996733662728994498713895097290351827746816 

noncomputable def Ns396p1014 := nat_lit 4968036253223421238444679633449093585962414002505227916902595035136 

noncomputable def Ns396p1015 := nat_lit 58333685735540867837411913741723302801015058668136674836037250293170176 

noncomputable def Ns396p1016 := BSN.cos_dyadic_bound_f 217281672 268435456 3 2 268435456 134217728 Ns396p1013 Ns396p252 Ns396p1014 Ns396p1015 Ns396p255 Ns396p1014 185195198 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 217281672) qz372 0 2 Ns396p1013 Ns396p252 Ns396p1014 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 217281672) qz373 0 2 Ns396p1015 Ns396p255 Ns396p1014 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1017 := nat_lit 16782621551374789153116423832441095371416452747511815298678968801034240 

noncomputable def Ns396p1018 := nat_lit 1142293955036369921856436255419463323952820462274139299336259895296 

noncomputable def Ns396p1019 := nat_lit 43952635587197246040193342473884570651185262153211072413865040534306816 

noncomputable def Ns396p1020 := BSN.sin_dyadic_bound_f 180809912 268435456 3 2 268435456 134217728 Ns396p1017 Ns396p121 Ns396p1018 Ns396p1019 Ns396p124 Ns396p1018 167444616 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 180809912) qz370 0 2 Ns396p1017 Ns396p121 Ns396p1018 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 180809912) qz371 0 2 Ns396p1019 Ns396p124 Ns396p1018 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1021 := Ns396p966 108665 BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 185195198 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 167444616 268435456) qz153 rfl rfl (Ns396p1012 rfl rfl) (Ns396p1000 rfl) RS397to408.d27 RS397to408.d29 RS397to408.d31 RS397to408.d33 RS397to408.d17 (Ns396p1016 rfl rfl) (Ns396p1020 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p1022 := nat_lit 26824853660574322681535675729187240464138928866360727925646113693876480 

noncomputable def Ns396p1023 := nat_lit 2918082914169144102238025478990661772198151455969270757093383454976 

noncomputable def Ns396p1024 := nat_lit 70250844595833618884999336773286311572732683357158908604990241815511296 

noncomputable def Ns396p1025 := BSN.sin_dyadic_bound_f 203299918 268435456 3 2 268435456 134217728 Ns396p1022 Ns396p121 Ns396p1023 Ns396p1024 Ns396p124 Ns396p1023 184414915 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 203299918) qz370 0 2 Ns396p1022 Ns396p121 Ns396p1023 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 203299918) qz371 0 2 Ns396p1024 Ns396p124 Ns396p1023 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1026 := nat_lit 41059878325578838408105777833403898625498122051388396350985501695215436370909563884932867164876354519808879601 

noncomputable def Ns396p1027 := nat_lit 25140234085269802702340243218097157438002888229366019918962277205518639511272626818029287079659368098801 

noncomputable def Ns396p1028 := nat_lit 205062948159129034354182356291276216571196718288775823717601482935086011704726094270245311985719547997289982961 

noncomputable def Ns396p1029 := BSN.sin_dyadic_bound_f 413711357 268435456 4 3 268435456 134217728 Ns396p1026 Ns396p258 Ns396p1027 Ns396p1028 Ns396p261 Ns396p1027 268317857 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 413711357) qz370 0 3 Ns396p1026 Ns396p258 Ns396p1027 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 413711357) qz371 0 3 Ns396p1028 Ns396p261 Ns396p1027 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1030 := Ns396p964 133195 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 89 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 184414915 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 145 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268317857 268435456) qz153 rfl rfl (Ns396p1021 rfl) (Ns396p1000 rfl) RS397to408.d35 RS397to408.d37 RS397to408.d39 RS397to408.d41 RS397to408.d17 (Ns396p1025 rfl rfl) (Ns396p1029 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p1031 := nat_lit 20361345547952021355882141107984704588433519128783561317210513258303201 

noncomputable def Ns396p1032 := nat_lit 5445565980038616904596315210981451361608377361811198864962580369121 

noncomputable def Ns396p1033 := nat_lit 61073145511895986833837230693532150862577340631627061553901614614171361 

noncomputable def Ns396p1034 := BSN.cos_dyadic_bound_f 219788709 268435456 3 2 268435456 134217728 Ns396p1031 Ns396p252 Ns396p1032 Ns396p1033 Ns396p255 Ns396p1032 183372306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 219788709) qz372 0 2 Ns396p1031 Ns396p252 Ns396p1032 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 219788709) qz373 0 2 Ns396p1033 Ns396p255 Ns396p1032 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1035 := Ns396p962 Bool.false 381695703 133195 Bool.true 219788709 14148475504056880 1 Bool.false 183372306 Bool.false Bool.false 439683117 144490 BSN.abs_quadSignPos qz394 (BSN.sfrac_eq_quadSignPos_mul Bool.false 183372306 268435456) qz153 rfl (Ns396p1030 rfl) (Ns396p1000 rfl) RS397to408.d43 RS397to408.d45 RS397to408.d17 (Ns396p1034 rfl rfl) rfl 

noncomputable def Ns396p1036 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) 439683117 268435456 144490 268435456 439683117 268435456 144490 268435456 236053076014792704 439683117 134217728 72245 67108864 (Ns396p1035 rfl rfl rfl rfl) 

noncomputable def Ns396p1037 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz151) (Zeta.RiemannSiegel.correction qz152) 5069853 16777216 1 16777216 228571843305911 281474976710656 234371736667571 8796093022208000000 1158825645500002801083 4722366482869645213696 

noncomputable def Ns396p1038 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz151 1 1 0 1 5069853 16777216 1 16777216 5069853 16777216 1 16777216 

noncomputable abbrev qz159 := qz472

noncomputable def Ns396p1039 := @Enclosure.Real.IsNear.sqrt_image qz159 4023907922323 33554432000 753491 33554432000 183725283 183725319 16777216 (@Enclosure.Real.IsNear.of_eq qz159 (@HMul.hMul Real Real Real qz5 qz150 qz3) Bool.false 4023907922323 33554432000 753491 33554432000 (BSN.t_div_two_pi_mk qz150 753491 1000 qz153) (@Enclosure.Real.IsNear.mulLit_ff qz150 qz3 753491 1000 0 1 5340353 33554432 1 33554432 4023907922323 33554432000 753491 33554432000 (Enclosure.Real.IsNear.const Bool.false 753491 1000) RS397to408.d48 rfl)) 

noncomputable abbrev qz743 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 753491 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz651 := qz743

noncomputable abbrev qz479 := qz651

noncomputable abbrev qz160 := qz479

noncomputable def Ns396p1040 := @Enclosure.Real.IsNear.sqrt_image qz160 183725301 16777216 9 8388608 55519354 55519361 16777216 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 367450602 33554432 36 33554432 183725301 16777216 9 8388608 (Ns396p1039 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns396p1041 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz160) 111038715 33554432 7 33554432 5069852 5069854 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz160) Bool.false 111038715 33554432 7 33554432 111038715 33554432 7 33554432 (Ns396p1040 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns396p1042 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz160)) Bool.false 10139706 33554432 2 33554432 5069853 16777216 1 16777216 (Ns396p1041 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz161 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz473))

noncomputable abbrev qz652 := (@HMul.hMul Real Real Real qz707 qz742 qz742)

noncomputable abbrev qz480 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz652 qz647) qz593)

noncomputable abbrev qz162 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz480))

noncomputable def Ns396p1043 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz152) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz161) qz162) Bool.false 228571843305911 

noncomputable def Ns396p1044 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz161) qz162 35218393 33554432 257 

noncomputable def Ns396p1045 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz161) Bool.false 35218393 33554432 257 33554432 35218393 33554432 257 

noncomputable def Ns396p1046 := @Enclosure.Real.IsNear.recentre' qz161 Bool.false 31969088 33554432 1452304432 209715200000000 499517 524288 90769027 13107200000000 

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz349 qz346 qz473)

noncomputable def Ns396p1047 := @Enclosure.Real.IsNear.cos_image qz163 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 100236541) qz413) Bool.false 100236541 16777216 227 33554432 Bool.false 31969088 33554432 1 

noncomputable def Ns396p1048 := nat_lit 242874678749914627959997439 

noncomputable def Ns396p1049 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz152 884279719003555 140737488355328 1 500000000000000 15953141 16777216 9 8388608 14107039040704092416255 2361183241434822606848 Ns396p1048 

noncomputable def Ns396p1050 := @Enclosure.Real.IsNear.subLit_ff_p qz160 qz1 183725301 16777216 9 8388608 10 1 0 1 15953141 15953141 16777216 9 

noncomputable def Ns396p1051 := @Ns396p1050 8388608 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 367450602 33554432 36 33554432 183725301 16777216 9 8388608 (Ns396p1039 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns396p1052 := @Enclosure.Real.IsNear.recentre' qz163 Bool.false 14107039040704092416255 2361183241434822606848 Ns396p1048 Ns396p579 100236541 16777216 227 33554432 (@Ns396p1049 Ns396p579 RS397to408.d47 (Ns396p1051 rfl rfl) rfl) 

noncomputable def Ns396p1053 := nat_lit 3051750537379222925606912 

noncomputable def Ns396p1054 := nat_lit 3819991479840020547447268551174279996016999786681334771001168984995379374719318999127035425 

noncomputable def Ns396p1055 := nat_lit 3203271860963307441267479857235871649694767707607863680495158136181963838210927035944481 

noncomputable def Ns396p1056 := nat_lit 9999553340377541793171270285687589530706922198353083097139402799910270420907779687274516001 

noncomputable def Ns396p1057 := BSN.sin_dyadic_bound_f 86735967027 68719476736 3 2 33554432 12512208 Ns396p1054 Ns396p175 Ns396p1055 Ns396p1056 Ns396p178 Ns396p1055 31969088 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 86735967027) qz368 0 2 Ns396p1054 Ns396p175 Ns396p1055 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 86735967027) qz369 0 2 Ns396p1056 Ns396p178 Ns396p1055 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1058 := @Ns396p1047 6250000 (Ns396p1052 rfl) (Enclosure.sfrac_false_div 100236541 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 100236541) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p1053) qz414) 226375608064910080 72057594037927936 Bool.false 31969088 33554432 0 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 100236541 16777216 226375608064910080 72057594037927936 0 Ns396p1053 Ns396p399 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 31969088 33554432 Ns396p1053 Ns396p399 86735967027 68719476736 12512208 12500000 (Ns396p1057 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p1059 := @Enclosure.Real.IsNear.inv_image qz161 499517 524288 90769027 13107200000000 17609068 17609325 16777216 (Ns396p1046 (Ns396p1058 rfl rfl) rfl) rfl 

noncomputable def Ns396p1060 := @Enclosure.Real.IsNear.recentre' qz162 Bool.false 12980254 16777216 

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz349 qz346 qz480)

noncomputable def Ns396p1061 := @Enclosure.Real.IsNear.cos_image qz164 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 23023771)) qz392) Bool.true 23023771 33554432 

noncomputable def Ns396p1062 := nat_lit 27181671529482667178417238005 

noncomputable def Ns396p1063 := nat_lit 39614081257132168796771975168 

noncomputable def Ns396p1064 := nat_lit 2955998326428160749882211275867521 

noncomputable def Ns396p1065 := @Enclosure.Real.IsNear.recentre' qz164 Bool.true Ns396p1062 Ns396p1063 Ns396p1064 

noncomputable def Ns396p1066 := nat_lit 151115727451828646838272000000000000000 

noncomputable abbrev qz165 := qz480

noncomputable def Ns396p1067 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz165 884279719003555 140737488355328 1 500000000000000 30738770713991 

noncomputable abbrev qz481 := (@HSub.hSub Real Real Real qz583 qz652 qz647)

noncomputable abbrev qz166 := qz481

noncomputable def Ns396p1068 := @Enclosure.Real.IsNear.subLit_tf qz166 qz29 13146584669575 281474976710656 109537911 35184372088832 1 16 

noncomputable abbrev qz482 := qz652

noncomputable abbrev qz167 := qz482

noncomputable def Ns396p1069 := @Enclosure.Real.IsNear.subLit_ff_n qz167 qz152 254502707765881 281474976710656 71789175 35184372088832 15953141 16777216 9 8388608 

noncomputable def Ns396p1070 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz152 15953141 16777216 9 8388608 15953141 16777216 9 8388608 254502707765881 281474976710656 

noncomputable def Ns396p1071 := nat_lit 598510778448703227127737320004430919711737206819169607707657441 

noncomputable def Ns396p1072 := nat_lit 78960821152541449601801467096135310108183288003826295899361 

noncomputable def Ns396p1073 := nat_lit 1795374413703804598484008357079100488514995253881501170531173601 

noncomputable def Ns396p1074 := BSN.cos_dyadic_bound_f 23023771 33554432 3 2 16777216 6250000 Ns396p1071 Ns396p322 Ns396p1072 Ns396p1073 Ns396p325 Ns396p1072 12980254 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 23023771) (BSN.cosEvenQ 33554432) 0 2 Ns396p1071 Ns396p322 Ns396p1072 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 23023771) (BSN.cosOddQ 33554432) 0 2 Ns396p1073 Ns396p325 Ns396p1072 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1075 := @Ns396p1060 4139804432 209715200000000 6490127 8388608 258737777 13107200000000 (@Ns396p1061 657 33554432 Bool.false 12980254 16777216 1 6250000 (@Ns396p1065 Ns396p1066 23023771 33554432 657 33554432 (@Ns396p1067 281474976710656 109537911 35184372088832 Ns396p1062 Ns396p1063 Ns396p1064 Ns396p1066 RS397to408.d47 (@Ns396p1068 0 1 491820331423856 30738770713991 281474976710656 109537911 35184372088832 (@Ns396p1069 220563090663748403200 13146584669575 281474976710656 109537911 35184372088832 (@Ns396p1070 71789175 35184372088832 (Ns396p1051 rfl rfl) (Ns396p1051 rfl rfl) rfl) (Ns396p1051 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 23023771 33554432) (BSN.cos_neg_of_bound 23023771 33554432 Bool.false 12980254 16777216 1 6250000 (Ns396p1074 rfl rfl)) rfl rfl) 

noncomputable def Ns396p1076 := @Ns396p1037 149421669591792652923 Ns396p959 (Ns396p1038 qz31 (@Enclosure.Real.IsNear.of_eq qz151 (@Inv.inv Real Real.instInv (Real.sqrt qz160)) Bool.false 5069853 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz159 (BSN.t_div_two_pi_nonneg qz150 753491 1000 qz153)) Ns396p1042) rfl) (@Ns396p1043 281474976710656 234371736667571 8796093022208000000 (BSN.correction_mk qz152 (BSN.cos_two_pi_p_ne_zero_mk qz150 753491 1000 10 qz153 rfl rfl (@BSN.floor_sqrt_eq_dec qz150 753491 1000 10 qz153 rfl rfl rfl))) (@Ns396p1044 33554432 6490127 8388608 258737777 13107200000000 228571843305911 281474976710656 234371736667571 8796093022208000000 (@Ns396p1045 33554432 (Ns396p1059 rfl rfl rfl rfl rfl) rfl) (Ns396p1075 rfl) rfl)) 

noncomputable def Ns396p1077 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz150) (hardyZApproximantRS₀ qz150) Bool.false 14311148744205451848261 4722366482869645213696 20007976056761072652923 Ns396p959 (@Eq.refl Real (hardyZApproximantRS₀ qz150)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz150) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz151) (Zeta.RiemannSiegel.correction qz152))) Bool.false 14311148744205451848261 4722366482869645213696 20007976056761072652923 Ns396p959 (BSN.hardyZApproximantRS₀_eq qz150 10 (@BSN.floor_sqrt_eq_dec qz150 753491 1000 10 qz153 rfl rfl rfl)) (@Ns396p961 14311148744205451848261 4722366482869645213696 20007976056761072652923 Ns396p959 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 10)) Bool.false 439683117 134217728 72245 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (Ns396p1036 (Ns396p1035 rfl rfl rfl rfl) rfl rfl)) (Ns396p1076 rfl) rfl rfl)) 

theorem RS397to408.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz150) Bool.false 14311148744205451848261 4722366482869645213696 20007976056761072652923 Ns396p959 := Ns396p1077 

noncomputable def Ns396p1078 := nat_lit 2004204274218900281945347 

noncomputable def Ns396p1079 := nat_lit 89065001360003873382093291520 

noncomputable abbrev qz744 := (Enclosure.sfrac Bool.false 754804 1000)

noncomputable abbrev qz653 := qz744

noncomputable abbrev qz483 := qz653

noncomputable abbrev qz168 := qz483

noncomputable abbrev qz745 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 754804 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz654 := qz745

noncomputable abbrev qz484 := qz654

noncomputable abbrev qz169 := (@HPow.hPow Real Real Real qz350 qz484 qz352)

noncomputable abbrev qz746 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 754804 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz655 := qz746

noncomputable abbrev qz485 := qz655

noncomputable abbrev qz170 := qz485

noncomputable def Ns396p1080 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz169) (Zeta.RiemannSiegel.correction qz170)) 268004059 134217728 72373 67108864 74238812674508937147 295147905179352825856 14830398293089081945347 Ns396p848 Ns396p1079 

noncomputable def Ns396p1081 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos BSN.quadSignPos 9 10 754804 1000 196 268435456 134217728 4503599627370496 Bool.false 383708457066 2535 618095470 44 84886744 8 

noncomputable def Ns396p1082 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 754804 1000 89 145 268435456 134217728 4503599627370496 Bool.false 383708457066 2535 

noncomputable def Ns396p1083 := Ns396p1082 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 215133414 108859 Bool.true 92483124 Bool.true 344407862 14148475504056880 1 Bool.false 90664350 Bool.true Bool.false 257396628 Bool.true Bool.true 332986981 

noncomputable def Ns396p1084 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 754804 1000 49 25 268435456 134217728 4503599627370496 Bool.false 383708457066 2535 

noncomputable def Ns396p1085 := Ns396p1084 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 203278847 80735 Bool.false 7836255 Bool.true 22929189 14148475504056880 1 Bool.false 7835142 Bool.true Bool.false 22901316 Bool.true Bool.true 215133414 

noncomputable def Ns396p1086 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 754804 1000 243 136 268435456 134217728 4503599627370496 Bool.false 383708457066 2535 

noncomputable def Ns396p1087 := Ns396p1086 372130544 43 134217720 8 432030192 43 120047984 16 Bool.true 400156406 47562 Bool.false 360078863 Bool.false 264929779 14148475504056880 1 Bool.false 261403374 Bool.false Bool.false 147973768 Bool.false Bool.true 203278847 

noncomputable def Ns396p1088 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 754804 1000 576 382 268435456 134217728 4503599627370496 Bool.false 383708457066 2535 

noncomputable def Ns396p1089 := Ns396p1088 186065264 43 189812528 16 294906480 43 154981288 8 Bool.true 268435376 2587 Bool.false 390972856 Bool.false 38728738 14148475504056880 1 Bool.false 30617792 Bool.false Bool.false 265646489 Bool.true Bool.true 400156406 

noncomputable def Ns396p1090 := nat_lit 326978781738174901423839248132101379083371504807638843 

noncomputable def Ns396p1091 := nat_lit 228748407186976434948945213216376529602014609408000 

noncomputable def Ns396p1092 := nat_lit 117601452328108083710588293611520000 

noncomputable def Ns396p1093 := nat_lit 532596388801411806952546381429714452480 

noncomputable abbrev qz656 := (@Eq.refl Real qz744)

noncomputable abbrev qz486 := qz656

noncomputable abbrev qz171 := qz486

noncomputable def Ns396p1094 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz168 754804 1000 2278917313664 16000000 1509608 4000 2000 Ns396p1092 Ns396p1093 qz171 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns396p1095 := nat_lit 3428621030398884854354036634493663356737253590251747074375680 

noncomputable abbrev qz657 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1509608))))

noncomputable abbrev qz487 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 754804 4000) (Real.log (Enclosure.sfrac Bool.false 2278917313664 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz657))

noncomputable abbrev qz658 := (Enclosure.sfrac Bool.false 754804 2000)

noncomputable abbrev qz172 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz487 qz658) (@HMul.hMul Real Real Real qz349 qz658 (Real.log Real.pi)))

noncomputable def Ns396p1096 := @Enclosure.Real.IsNear.addLit_ft_p qz172 (Enclosure.sfrac Bool.true Ns396p1092 Ns396p1093) 6437560659667118540091 4503599627370496000 9664257274800633 1024000000000000000000 Ns396p1092 Ns396p1093 0 1 Ns396p1095 

noncomputable def Ns396p1097 := nat_lit 108004345700337735844711366656000 

noncomputable abbrev qz173 := (@HSub.hSub Real Real Real qz355 qz487 qz658)

noncomputable def Ns396p1098 := @Enclosure.Real.IsNear.subLit_ff_p qz173 (@HMul.hMul Real Real Real qz5 qz658 (Real.log Real.pi)) 8383220844714601301307 4503599627370496000 1907011604021 500000000000000000 7248149011461 16777216000 188701 33554432000 Ns396p1097 6437560659667118540091 4503599627370496000 

noncomputable def Ns396p1099 := nat_lit 16766441689429202602614000 

noncomputable abbrev qz174 := qz487

noncomputable def Ns396p1100 := @Enclosure.Real.IsNear.subLit_ff_p qz174 qz658 10082888351283481232699 4503599627370496000 1907011604021 500000000000000000 754804 2000 0 1 Ns396p1099 8383220844714601301307 4503599627370496000 1907011604021 500000000000000000 

noncomputable def Ns396p1101 := nat_lit 22704646110829300426720920633031524352 

noncomputable def Ns396p1102 := nat_lit 57383464342829415348043776 

noncomputable def Ns396p1103 := nat_lit 5500827525530760143803642553103776483047222007562240 

noncomputable def Ns396p1104 := nat_lit 3166720535802552685358397459777849561122265366528 

noncomputable def Ns396p1105 := nat_lit 3274653068428901164976897486750770864689512448 

noncomputable def Ns396p1106 := BSN.log_dyadic_bound 181765313664 4376069313664 3 2 Ns396p1103 134217728 50000000 Ns396p1104 Ns396p1105 11156208 4557834627328 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 181765313664) (BSN.artanhQ 4376069313664) 0 2 Ns396p1104 Ns396p1103 Ns396p1105 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz488 := (Real.log (Enclosure.sfrac Bool.false 2278917313664 16000000))

noncomputable def Ns396p1107 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 754804 4000) qz488 754804 4000 0 1 53442515752119399 4503599627370496 20000017 1000000000000000 10084656164940682710699 4503599627370496000 3774023207917 1000000000000000000 (Enclosure.Real.IsNear.const Bool.false 754804 4000) (BSN.isNear_log_sfrac 2278917313664 16000000 53442515752119399 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2278917313664) qz358)) Bool.false Ns396p1102 Ns396p100 1000000850000000 50000000000000000000000 53442515752119399 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2278917313664 16000000 17 4557834627328 4194304000000 11156208 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns396p1106 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns396p1108 := BSN.arctan_dyadic_bound_f 1000 1509608 1 0 16777216 6250000 0 1 1 0 1 1 11113 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1509608) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1509608) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns396p1109 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1509608))) 884279719003555 562949953421312 1 2000000000000000 11113 16777216 1 6250000 14829495787309575962624 883906828600739 562949953421312 320000001 2000000000000000 qz15 (Ns396p1108 rfl) rfl rfl 

noncomputable abbrev qz489 := (@HMul.hMul Real Real Real qz579 qz584 qz657)

noncomputable abbrev qz175 := qz489

noncomputable abbrev qz490 := qz657

noncomputable abbrev qz176 := qz490

noncomputable def Ns396p1110 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 754804 4000) qz488) qz175 10084656164940682710699 4503599627370496000 3774023207917 1000000000000000000 883906828600739 2251799813685248 320000001 8000000000000000 Ns396p1101 10082888351283481232699 4503599627370496000 1907011604021 500000000000000000 (Ns396p1107 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz176 1 4 0 1 883906828600739 562949953421312 320000001 2000000000000000 883906828600739 2251799813685248 320000001 8000000000000000 qz366 Ns396p1109 rfl) 

noncomputable def Ns396p1111 := @Ns396p1096 Ns396p1090 Ns396p1091 9664257274800633 1024000000000000000000 (@Ns396p1098 9664257274800633 1024000000000000000000 (Ns396p1100 (Ns396p1110 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 754804 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz658 (Real.log Real.pi) 754804 2000 0 1 38410761 33554432 1 67108864 7248149011461 16777216000 188701 33554432000 (Enclosure.Real.IsNear.const Bool.false 754804 2000) RS397to408.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns396p1092 Ns396p1093) 

noncomputable def Ns396p1112 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns396p1090 Ns396p1091 9664257274800633 1024000000000000000000 47963557133 33554432 159 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz367 qz172 (Enclosure.sfrac Bool.true Ns396p1092 Ns396p1093)) Bool.false Ns396p1090 Ns396p1091 9664257274800633 1024000000000000000000 Ns396p1094 (Ns396p1111 rfl rfl)) 

noncomputable def Ns396p1113 := BSN.cos_dyadic_bound_f 50519463 68719476736 1 0 33554432 12512208 0 1 1 0 1 1 33554422 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 50519463) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 50519463) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns396p1114 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz168) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47963557133) qz392) Bool.false 47963557133 33554432 159 16777216 Bool.true 33554422 33554432 1 6250000 (Ns396p1112 rfl) (Enclosure.sfrac_false_div 47963557133 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47963557133) qz392) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3554991217506963685376) qz393) 226375608064910080 72057594037927936 Bool.false 33554422 33554432 227 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q2 47963557133 33554432 226375608064910080 72057594037927936 227 3554991217506963685376 Ns396p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554422 33554432 3554991217506963685376 Ns396p100 50519463 68719476736 12512208 12500000 (Ns396p1113 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p1115 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns396p1090 Ns396p1091 9664257274800633 1024000000000000000000 383708457066 268435456 2535 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz367 qz172 (Enclosure.sfrac Bool.true Ns396p1092 Ns396p1093)) Bool.false Ns396p1090 Ns396p1091 9664257274800633 1024000000000000000000 Ns396p1094 (Ns396p1111 rfl rfl)) 

noncomputable def Ns396p1116 := Ns396p1089 47562 BSN.abs_quadSignPos (BSN.cos_quad_nat0 576 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 30617792 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 382 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 265646489 268435456) qz171 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) Bool.true 16777211 16777216 63157951 6553600000000 268435376 268435456 2587 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.true 16777211 16777216 63157951 6553600000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz168) qz168) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.true 33554422 33554432 1010527216 104857600000000 16777211 16777216 63157951 6553600000000 (Ns396p1114 rfl rfl) rfl)) rfl) (Ns396p1115 rfl) RS397to408.d7 

noncomputable def Ns396p1117 := nat_lit 12606466953302572448892153077938197577798064989337320964095455654969124906778143227890772373723653029144559616 

noncomputable def Ns396p1118 := nat_lit 12757315058294509614097032682653085609539301692570101112225164667297966222001723147558087473366392897536 

noncomputable def Ns396p1119 := nat_lit 76342958623718396846985085522353058282896803130157047546547351120506601753861002531161957934492239381722562560 

noncomputable def Ns396p1120 := BSN.cos_dyadic_bound_f 390972856 268435456 4 3 268435456 134217728 Ns396p1117 Ns396p246 Ns396p1118 Ns396p1119 Ns396p249 Ns396p1118 30617792 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 390972856) qz372 0 3 Ns396p1117 Ns396p246 Ns396p1118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 390972856) qz373 0 3 Ns396p1119 Ns396p249 Ns396p1118 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1121 := nat_lit 2249745448417951280882613150736 

noncomputable def Ns396p1122 := BSN.cos_dyadic_bound_f 38728738 268435456 2 1 268435456 134217728 Ns396p1121 Ns396p141 Ns396p1121 Ns396p1121 Ns396p142 Ns396p1121 265646489 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 38728738) qz372 0 1 Ns396p1121 Ns396p141 Ns396p1121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 38728738) qz373 0 1 Ns396p1121 Ns396p142 Ns396p1121 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1123 := nat_lit 23543630407988529586102677227520769903098555810992085887311779581727353972508902719958824338554870811765545281 

noncomputable def Ns396p1124 := nat_lit 4750852455950087030559723745532418463430510583520206233620473765894547216075323286512112306874238146881 

noncomputable def Ns396p1125 := nat_lit 117640303569143005159042560741454841081229180045122031972429852375335911477254733115498540756807504896591698241 

noncomputable def Ns396p1126 := BSN.sin_dyadic_bound_f 360078863 268435456 4 3 268435456 134217728 Ns396p1123 Ns396p258 Ns396p1124 Ns396p1125 Ns396p261 Ns396p1124 261403374 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 360078863) qz370 0 3 Ns396p1123 Ns396p258 Ns396p1124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 360078863) qz371 0 3 Ns396p1125 Ns396p261 Ns396p1124 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1127 := nat_lit 42996895797292414845896292931696124875274707055946415694221895047364641 

noncomputable def Ns396p1128 := nat_lit 24268683487606644618670448784083674367055552300827416388811995004961 

noncomputable def Ns396p1129 := nat_lit 128942150024902031248451537897520207277090010063237592249888061152084001 

noncomputable def Ns396p1130 := BSN.cos_dyadic_bound_f 264929779 268435456 3 2 268435456 134217728 Ns396p1127 Ns396p252 Ns396p1128 Ns396p1129 Ns396p255 Ns396p1128 147973768 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 264929779) qz372 0 2 Ns396p1127 Ns396p252 Ns396p1128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 264929779) qz373 0 2 Ns396p1129 Ns396p255 Ns396p1128 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1131 := Ns396p1087 80735 BSN.abs_quadSignPos (BSN.cos_quad_nat3 243 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 261403374 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 136 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 147973768 268435456) qz171 rfl rfl (Ns396p1116 RS397to408.d9 RS397to408.d11 RS397to408.d13 RS397to408.d17 (Ns396p1120 rfl rfl) (Ns396p1122 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns396p1115 rfl) RS397to408.d19 RS397to408.d21 RS397to408.d23 RS397to408.d25 RS397to408.d17 (Ns396p1126 rfl rfl) (Ns396p1130 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns396p1132 := BSN.sin_dyadic_bound_f 7836255 268435456 1 0 268435456 134217728 0 1 1 0 1 1 7835142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 7836255) qz370 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 7836255) qz371 0 0 rfl) rfl rfl 

noncomputable def Ns396p1133 := nat_lit 276410652675155989186029593841 

noncomputable def Ns396p1134 := BSN.sin_dyadic_bound_f 22929189 268435456 2 1 268435456 134217728 Ns396p1133 Ns396p131 Ns396p1133 Ns396p1133 Ns396p132 Ns396p1133 22901316 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 22929189) qz370 0 1 Ns396p1133 Ns396p131 Ns396p1133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 22929189) qz371 0 1 Ns396p1133 Ns396p132 Ns396p1133 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1135 := Ns396p1085 108859 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 7835142 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 22901316 268435456) qz171 rfl rfl (Ns396p1131 rfl rfl) (Ns396p1115 rfl) RS397to408.d27 RS397to408.d29 RS397to408.d31 RS397to408.d33 RS397to408.d17 (Ns396p1132 rfl rfl) (Ns396p1134 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p1136 := nat_lit 73156002429859725031015449989376 

noncomputable def Ns396p1137 := BSN.sin_dyadic_bound_f 92483124 268435456 2 1 268435456 134217728 Ns396p1136 Ns396p131 Ns396p1136 Ns396p1136 Ns396p132 Ns396p1136 90664350 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 92483124) qz370 0 1 Ns396p1136 Ns396p131 Ns396p1136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 92483124) qz371 0 1 Ns396p1136 Ns396p132 Ns396p1136 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1138 := nat_lit 19701503931751593895451212173749387409876621691555756931603025449907148579978371330190748320633330082295648256 

noncomputable def Ns396p1139 := nat_lit 2785330157918303911407091851290391127528351337928930355872480766815894768792359772263916511415912697856 

noncomputable def Ns396p1140 := nat_lit 98452989567303404651523781969969238212929711855908506805737096647693101347710992255491518371105113323604873216 

noncomputable def Ns396p1141 := BSN.sin_dyadic_bound_f 344407862 268435456 4 3 268435456 134217728 Ns396p1138 Ns396p258 Ns396p1139 Ns396p1140 Ns396p261 Ns396p1139 257396628 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 344407862) qz370 0 3 Ns396p1138 Ns396p258 Ns396p1139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 344407862) qz371 0 3 Ns396p1140 Ns396p261 Ns396p1139 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1142 := Ns396p1083 133432 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 89 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 90664350 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 145 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 257396628 268435456) qz171 rfl rfl (Ns396p1135 rfl) (Ns396p1115 rfl) RS397to408.d35 RS397to408.d37 RS397to408.d39 RS397to408.d41 RS397to408.d17 (Ns396p1137 rfl rfl) (Ns396p1141 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p1143 := nat_lit 10810560803070474781336877634516933380838453961121455057130442726825121 

noncomputable def Ns396p1144 := nat_lit 1535449293325753503066252087664104321492598932803130875543947566241 

noncomputable def Ns396p1145 := nat_lit 32428611510624772837004500399375471933872376685498758909640240285342881 

noncomputable def Ns396p1146 := BSN.cos_dyadic_bound_f 187620131 268435456 3 2 268435456 134217728 Ns396p1143 Ns396p252 Ns396p1144 Ns396p1145 Ns396p255 Ns396p1144 205494046 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 187620131) qz372 0 2 Ns396p1143 Ns396p252 Ns396p1144 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 187620131) qz373 0 2 Ns396p1145 Ns396p255 Ns396p1144 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1147 := Ns396p1081 Bool.true 332986981 133432 Bool.true 187620131 14148475504056880 1 Bool.false 205494046 Bool.false Bool.true 268004059 144746 BSN.abs_quadSignPos qz394 (BSN.sfrac_eq_quadSignPos_mul Bool.false 205494046 268435456) qz171 rfl (Ns396p1142 rfl) (Ns396p1115 rfl) RS397to408.d43 RS397to408.d45 RS397to408.d17 (Ns396p1146 rfl rfl) rfl 

noncomputable def Ns396p1148 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) 268004059 268435456 144746 268435456 268004059 268435456 144746 268435456 143883583575031808 268004059 134217728 72373 67108864 (Ns396p1147 rfl rfl rfl rfl) 

noncomputable def Ns396p1149 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz169) (Zeta.RiemannSiegel.correction qz170) 10135293 33554432 1 33554432 7324782093079 8796093022208 2917452301829101 109951162777600000000 74238812674508937147 295147905179352825856 

noncomputable def Ns396p1150 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz169 1 1 0 1 10135293 33554432 1 33554432 10135293 33554432 1 33554432 

noncomputable abbrev qz177 := qz484

noncomputable def Ns396p1151 := @Enclosure.Real.IsNear.sqrt_image qz177 1007729951453 8388608000 188701 8388608000 183885289 183885325 16777216 (@Enclosure.Real.IsNear.of_eq qz177 (@HMul.hMul Real Real Real qz5 qz168 qz3) Bool.false 1007729951453 8388608000 188701 8388608000 (BSN.t_div_two_pi_mk qz168 754804 1000 qz171) (@Enclosure.Real.IsNear.mulLit_ff qz168 qz3 754804 1000 0 1 5340353 33554432 1 33554432 1007729951453 8388608000 188701 8388608000 (Enclosure.Real.IsNear.const Bool.false 754804 1000) RS397to408.d48 rfl)) 

noncomputable abbrev qz747 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 754804 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz659 := qz747

noncomputable abbrev qz491 := qz659

noncomputable abbrev qz178 := qz491

noncomputable def Ns396p1152 := @Enclosure.Real.IsNear.sqrt_image qz178 183885307 16777216 9 8388608 55543525 55543531 16777216 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 367770614 33554432 36 33554432 183885307 16777216 9 8388608 (Ns396p1151 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns396p1153 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz178) 6942941 2097152 3 16777216 5067646 5067647 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz178) Bool.false 111087056 33554432 6 33554432 6942941 2097152 3 16777216 (Ns396p1152 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns396p1154 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz178)) Bool.false 10135293 33554432 1 33554432 10135293 33554432 1 33554432 (Ns396p1153 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz179 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz485))

noncomputable abbrev qz660 := (@HMul.hMul Real Real Real qz707 qz746 qz746)

noncomputable abbrev qz492 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz660 qz655) qz593)

noncomputable abbrev qz180 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz492))

noncomputable def Ns396p1155 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz170) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz179) qz180) Bool.false 7324782093079 

noncomputable def Ns396p1156 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz179) qz180 1081861 1048576 125 

noncomputable def Ns396p1157 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz179) Bool.false 34619552 33554432 250 33554432 1081861 1048576 125 

noncomputable def Ns396p1158 := @Enclosure.Real.IsNear.recentre' qz179 Bool.false 32522082 33554432 364638608 52428800000000 16261041 16777216 22789913 3276800000000 

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz349 qz346 qz485)

noncomputable def Ns396p1159 := @Enclosure.Real.IsNear.cos_image qz181 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3163809) (@Nat.cast Real Real.instNatCast 524288)) Bool.false 3163809 524288 57 8388608 Bool.false 32522082 33554432 1 

noncomputable def Ns396p1160 := nat_lit 48574935750120369699432243 

noncomputable def Ns396p1161 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz170 884279719003555 140737488355328 1 500000000000000 16113147 16777216 9 8388608 14248529101422975237585 2361183241434822606848 Ns396p1160 

noncomputable def Ns396p1162 := @Enclosure.Real.IsNear.subLit_ff_p qz178 qz1 183885307 16777216 9 8388608 10 1 0 1 16113147 16113147 16777216 9 

noncomputable def Ns396p1163 := @Ns396p1162 8388608 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 367770614 33554432 36 33554432 183885307 16777216 9 8388608 (Ns396p1151 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns396p1164 := @Enclosure.Real.IsNear.recentre' qz181 Bool.false 14248529101422975237585 2361183241434822606848 Ns396p1160 Ns396p700 3163809 524288 57 8388608 (@Ns396p1161 Ns396p700 RS397to408.d47 (Ns396p1163 rfl rfl) rfl) 

noncomputable def Ns396p1165 := nat_lit 4599529663258567900679913673167498298188424926791625073243370060845182584669157300924616225 

noncomputable def Ns396p1166 := nat_lit 4642451614144664333895909811416992421000421303567684003249402948278943392711264104386081 

noncomputable def Ns396p1167 := nat_lit 12038870863063824569049656718601153745621397935677051322489279697440169432450069931966893601 

noncomputable def Ns396p1168 := BSN.sin_dyadic_bound_f 90853868339 68719476736 3 2 33554432 12512208 Ns396p1165 Ns396p175 Ns396p1166 Ns396p1167 Ns396p178 Ns396p1166 32522082 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 90853868339) qz368 0 2 Ns396p1165 Ns396p175 Ns396p1166 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 90853868339) qz369 0 2 Ns396p1167 Ns396p178 Ns396p1166 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1169 := @Ns396p1159 6250000 (Ns396p1164 rfl) (Enclosure.sfrac_false_div 3163809 524288) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3163809) (@Nat.cast Real Real.instNatCast 524288)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 99894884667678762467328) (@Nat.cast Real Real.instNatCast 75557863725914323419136)) 226375608064910080 72057594037927936 Bool.false 32522082 33554432 0 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 3163809 524288 226375608064910080 72057594037927936 0 99894884667678762467328 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 32522082 33554432 99894884667678762467328 75557863725914323419136 90853868339 68719476736 12512208 12500000 (Ns396p1168 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p1170 := @Enclosure.Real.IsNear.inv_image qz179 16261041 16777216 22789913 3276800000000 17309651 17309901 16777216 (Ns396p1158 (Ns396p1169 rfl rfl) rfl) rfl 

noncomputable def Ns396p1171 := @Enclosure.Real.IsNear.recentre' qz180 Bool.false 13541078 16777216 

noncomputable abbrev qz182 := (@HMul.hMul Real Real Real qz349 qz346 qz492)

noncomputable def Ns396p1172 := @Enclosure.Real.IsNear.cos_image qz182 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 21191425)) qz392) Bool.true 21191425 33554432 

noncomputable def Ns396p1173 := nat_lit 25018419803867295963539732245 

noncomputable def Ns396p1174 := nat_lit 1487714514672040882865508154952831 

noncomputable def Ns396p1175 := @Enclosure.Real.IsNear.recentre' qz182 Bool.true Ns396p1173 Ns396p1063 Ns396p1174 

noncomputable def Ns396p1176 := nat_lit 75557863725914323419136000000000000000 

noncomputable abbrev qz183 := qz492

noncomputable def Ns396p1177 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz183 884279719003555 140737488355328 1 500000000000000 28292427459559 

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz583 qz660 qz655)

noncomputable abbrev qz184 := qz493

noncomputable def Ns396p1178 := @Enclosure.Real.IsNear.subLit_tf qz184 qz29 10700241415143 281474976710656 55128969 17592186044416 1 16 

noncomputable abbrev qz494 := qz660

noncomputable abbrev qz185 := qz494

noncomputable def Ns396p1179 := @Enclosure.Real.IsNear.subLit_ff_n qz185 qz170 259633506243609 281474976710656 36254601 17592186044416 16113147 16777216 9 8388608 

noncomputable def Ns396p1180 := @Enclosure.Real.IsNear.mulLit_ff qz170 qz170 16113147 16777216 9 8388608 16113147 16777216 9 8388608 259633506243609 281474976710656 

noncomputable def Ns396p1181 := nat_lit 429527147671466231137017966116433898045897045402985546212890625 

noncomputable def Ns396p1182 := nat_lit 40670666704915858020189720751205654562584064697418212890625 

noncomputable def Ns396p1183 := nat_lit 1288500101680988861695013518907799282828565968079561802212890625 

noncomputable def Ns396p1184 := BSN.cos_dyadic_bound_f 21191425 33554432 3 2 16777216 6250000 Ns396p1181 Ns396p322 Ns396p1182 Ns396p1183 Ns396p325 Ns396p1182 13541078 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 21191425) (BSN.cosEvenQ 33554432) 0 2 Ns396p1181 Ns396p322 Ns396p1182 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 21191425) (BSN.cosOddQ 33554432) 0 2 Ns396p1183 Ns396p325 Ns396p1182 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1185 := @Ns396p1171 2085527216 104857600000000 6770539 8388608 130345451 6553600000000 (@Ns396p1172 331 16777216 Bool.false 13541078 16777216 1 6250000 (@Ns396p1175 Ns396p1176 21191425 33554432 331 16777216 (@Ns396p1177 281474976710656 55128969 17592186044416 Ns396p1173 Ns396p1063 Ns396p1174 Ns396p1176 RS397to408.d47 (@Ns396p1178 0 1 452678839352944 28292427459559 281474976710656 55128969 17592186044416 (@Ns396p1179 179520261473999781888 10700241415143 281474976710656 55128969 17592186044416 (@Ns396p1180 36254601 17592186044416 (Ns396p1163 rfl rfl) (Ns396p1163 rfl rfl) rfl) (Ns396p1163 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 21191425 33554432) (BSN.cos_neg_of_bound 21191425 33554432 Bool.false 13541078 16777216 1 6250000 (Ns396p1184 rfl rfl)) rfl rfl) 

noncomputable def Ns396p1186 := @Ns396p1149 14830398293089081945347 Ns396p848 (Ns396p1150 qz31 (@Enclosure.Real.IsNear.of_eq qz169 (@Inv.inv Real Real.instInv (Real.sqrt qz178)) Bool.false 10135293 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz177 (BSN.t_div_two_pi_nonneg qz168 754804 1000 qz171)) Ns396p1154) rfl) (@Ns396p1155 8796093022208 2917452301829101 109951162777600000000 (BSN.correction_mk qz170 (BSN.cos_two_pi_p_ne_zero_mk qz168 754804 1000 10 qz171 rfl rfl (@BSN.floor_sqrt_eq_dec qz168 754804 1000 10 qz171 rfl rfl rfl))) (@Ns396p1156 16777216 6770539 8388608 130345451 6553600000000 7324782093079 8796093022208 2917452301829101 109951162777600000000 (@Ns396p1157 16777216 (Ns396p1170 rfl rfl rfl rfl rfl) rfl) (Ns396p1185 rfl) rfl)) 

noncomputable def Ns396p1187 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (hardyZApproximantRS₀ qz168) Bool.true 663585970997839222715 295147905179352825856 Ns396p1078 Ns396p848 (@Eq.refl Real (hardyZApproximantRS₀ qz168)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz169) (Zeta.RiemannSiegel.correction qz170))) Bool.true 663585970997839222715 295147905179352825856 Ns396p1078 Ns396p848 (BSN.hardyZApproximantRS₀_eq qz168 10 (@BSN.floor_sqrt_eq_dec qz168 754804 1000 10 qz171 rfl rfl rfl)) (@Ns396p1080 663585970997839222715 295147905179352825856 Ns396p1078 Ns396p848 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10)) Bool.true 268004059 134217728 72373 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (Ns396p1148 (Ns396p1147 rfl rfl rfl rfl) rfl rfl)) (Ns396p1186 rfl) rfl rfl)) 

theorem RS397to408.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz168) Bool.true 663585970997839222715 295147905179352825856 Ns396p1078 Ns396p848 := Ns396p1187 

noncomputable def Ns396p1188 := nat_lit 28823037615171174400000000 

noncomputable def Ns396p1189 := nat_lit 27600459051323876908032065536 

noncomputable abbrev qz748 := (Enclosure.sfrac Bool.false 756116 1000)

noncomputable abbrev qz661 := qz748

noncomputable abbrev qz495 := qz661

noncomputable abbrev qz186 := qz495

noncomputable abbrev qz749 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 756116 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz662 := qz749

noncomputable abbrev qz496 := qz662

noncomputable abbrev qz187 := (@HPow.hPow Real Real Real qz350 qz496 qz352)

noncomputable abbrev qz750 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 756116 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz663 := qz750

noncomputable abbrev qz497 := qz663

noncomputable abbrev qz188 := qz497

noncomputable def Ns396p1190 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz187) (Zeta.RiemannSiegel.correction qz188)) 128116701 134217728 4531 4194304 76092160249617848215 295147905179352825856 225322466549809123133 Ns396p1188 Ns396p1189 

noncomputable def Ns396p1191 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.cos BSN.quadSignPos 9 10 756116 1000 196 268435456 134217728 4503599627370496 Bool.false 384551849090 2539 618095470 44 84886744 8 

noncomputable def Ns396p1192 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 756116 1000 88 145 268435456 134217728 4503599627370496 Bool.false 384551849090 2539 

noncomputable def Ns396p1193 := Ns396p1192 558195838 44 94906264 8 589812974 44 89478488 8 Bool.false 126893566 109042 Bool.true 403101467 Bool.true 274850460 14148475504056880 1 Bool.false 18541186 Bool.false Bool.false 229281861 Bool.true Bool.false 57021575 

noncomputable def Ns396p1194 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 756116 1000 49 24 268435456 134217728 4503599627370496 Bool.false 384551849090 2539 

noncomputable def Ns396p1195 := Ns396p1194 480971758 44 109588312 8 522351262 44 101459064 8 Bool.false 158092817 80869 Bool.false 220193333 Bool.true 286519450 14148475504056880 1 Bool.false 196317481 Bool.true Bool.false 129501650 Bool.false Bool.false 126893566 

noncomputable def Ns396p1196 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 756116 1000 244 137 268435456 134217728 4503599627370496 Bool.false 384551849090 2539 

noncomputable def Ns396p1197 := Ns396p1196 372130544 43 134217720 8 432030192 43 120047984 16 Bool.false 148287275 47639 Bool.false 293578185 Bool.false 119840763 14148475504056880 1 Bool.false 123274607 Bool.false Bool.false 115899334 Bool.true Bool.false 158092817 

noncomputable def Ns396p1198 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 756116 1000 578 383 268435456 134217728 4503599627370496 Bool.false 384551849090 2539 

noncomputable def Ns396p1199 := Ns396p1198 186065264 43 189812528 16 294906480 43 154981288 8 Bool.false 268435312 2587 Bool.false 146932397 Bool.false 73546032 14148475504056880 1 Bool.false 229216608 Bool.true Bool.false 72629354 Bool.false Bool.false 148287275 

noncomputable def Ns396p1200 := nat_lit 331129987799295061547044306520012034027962881791154747 

noncomputable def Ns396p1201 := nat_lit 231144459402167256752372603845467625935882682368000 

noncomputable def Ns396p1202 := nat_lit 118627085167935446977060302356480000 

noncomputable def Ns396p1203 := nat_lit 538175132596323398762318780285929390080 

noncomputable abbrev qz664 := (@Eq.refl Real qz748)

noncomputable abbrev qz498 := qz664

noncomputable abbrev qz189 := qz498

noncomputable def Ns396p1204 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz186 756116 1000 2286846621824 16000000 1512232 4000 2000 Ns396p1202 Ns396p1203 qz189 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns396p1205 := nat_lit 3472149580866336184567535307535281385929052067370418799902720 

noncomputable abbrev qz665 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1512232))))

noncomputable abbrev qz499 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 756116 4000) (Real.log (Enclosure.sfrac Bool.false 2286846621824 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz665))

noncomputable abbrev qz666 := (Enclosure.sfrac Bool.false 756116 2000)

noncomputable abbrev qz190 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz499 qz666) (@HMul.hMul Real Real Real qz349 qz666 (Real.log Real.pi)))

noncomputable def Ns396p1206 := @Enclosure.Real.IsNear.addLit_ft_p qz190 (Enclosure.sfrac Bool.true Ns396p1202 Ns396p1203) 6451710428098946148659 4503599627370496000 9680984486135457 1024000000000000000000 Ns396p1202 Ns396p1203 0 1 Ns396p1205 

noncomputable def Ns396p1207 := nat_lit 108241739421668488908420153344000 

noncomputable abbrev qz191 := (@HSub.hSub Real Real Real qz355 qz499 qz666)

noncomputable def Ns396p1208 := @Enclosure.Real.IsNear.subLit_ff_p qz191 (@HMul.hMul Real Real Real qz5 qz666 (Real.log Real.pi)) 8400752558873773091123 4503599627370496000 1910291606809 500000000000000000 7260747741069 16777216000 189029 33554432000 Ns396p1207 6451710428098946148659 4503599627370496000 

noncomputable def Ns396p1209 := nat_lit 16801505117747546182246000 

noncomputable abbrev qz192 := qz499

noncomputable def Ns396p1210 := @Enclosure.Real.IsNear.subLit_ff_p qz192 qz666 10103374426798208067891 4503599627370496000 1910291606809 500000000000000000 756116 2000 0 1 Ns396p1209 8400752558873773091123 4503599627370496000 1910291606809 500000000000000000 

noncomputable def Ns396p1211 := nat_lit 22750776651856504235226663586489171968 

noncomputable def Ns396p1212 := nat_lit 57400260607711686160285696 

noncomputable def Ns396p1213 := nat_lit 5540805366693256751946750067689833429881617792368640 

noncomputable def Ns396p1214 := nat_lit 3461851666376747599220983674843341117700710596608 

noncomputable def Ns396p1215 := nat_lit 3884555465823947510036879386743434962406473728 

noncomputable def Ns396p1216 := BSN.log_dyadic_bound 189694621824 4383998621824 3 2 Ns396p1213 134217728 50000000 Ns396p1214 Ns396p1215 11622398 4573693243648 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 189694621824) (BSN.artanhQ 4383998621824) 0 2 Ns396p1214 Ns396p1213 Ns396p1215 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz500 := (Real.log (Enclosure.sfrac Bool.false 2286846621824 16000000))

noncomputable def Ns396p1217 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 756116 4000) qz500 756116 4000 0 1 53458158492773479 4503599627370496 20000017 1000000000000000 10105142241730477961891 4503599627370496000 3780583213493 1000000000000000000 (Enclosure.Real.IsNear.const Bool.false 756116 4000) (BSN.isNear_log_sfrac 2286846621824 16000000 53458158492773479 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2286846621824) qz358)) Bool.false Ns396p1212 Ns396p100 1000000850000000 50000000000000000000000 53458158492773479 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2286846621824 16000000 17 4573693243648 4194304000000 11622398 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns396p1216 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns396p1218 := BSN.arctan_dyadic_bound_f 1000 1512232 1 0 16777216 6250000 0 1 1 0 1 1 11094 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1512232) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1512232) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns396p1219 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1512232))) 884279719003555 562949953421312 1 2000000000000000 11094 16777216 1 6250000 14829506483358690967552 883907466134947 562949953421312 320000001 2000000000000000 qz15 (Ns396p1218 rfl) rfl rfl 

noncomputable abbrev qz501 := (@HMul.hMul Real Real Real qz579 qz584 qz665)

noncomputable abbrev qz193 := qz501

noncomputable abbrev qz502 := qz665

noncomputable abbrev qz194 := qz502

noncomputable def Ns396p1220 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 756116 4000) qz500) qz193 10105142241730477961891 4503599627370496000 3780583213493 1000000000000000000 883907466134947 2251799813685248 320000001 8000000000000000 Ns396p1211 10103374426798208067891 4503599627370496000 1910291606809 500000000000000000 (Ns396p1217 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz194 1 4 0 1 883907466134947 562949953421312 320000001 2000000000000000 883907466134947 2251799813685248 320000001 8000000000000000 qz366 Ns396p1219 rfl) 

noncomputable def Ns396p1221 := @Ns396p1206 Ns396p1200 Ns396p1201 9680984486135457 1024000000000000000000 (@Ns396p1208 9680984486135457 1024000000000000000000 (Ns396p1210 (Ns396p1220 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 756116 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz666 (Real.log Real.pi) 756116 2000 0 1 38410761 33554432 1 67108864 7260747741069 16777216000 189029 33554432000 (Enclosure.Real.IsNear.const Bool.false 756116 2000) RS397to408.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns396p1202 Ns396p1203) 

noncomputable def Ns396p1222 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz186) Bool.false Ns396p1200 Ns396p1201 9680984486135457 1024000000000000000000 3004311321 2097152 159 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz186) (@HAdd.hAdd Real Real Real qz367 qz190 (Enclosure.sfrac Bool.true Ns396p1202 Ns396p1203)) Bool.false Ns396p1200 Ns396p1201 9680984486135457 1024000000000000000000 Ns396p1204 (Ns396p1221 rfl rfl)) 

noncomputable def Ns396p1223 := BSN.cos_dyadic_bound_f 70274335 68719476736 1 0 33554432 12512208 0 1 1 0 1 1 33554414 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 70274335) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 70274335) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns396p1224 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz186) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3004311321) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 3004311321 2097152 159 16777216 Bool.false 33554414 33554432 1 6250000 (Ns396p1222 rfl) (Enclosure.sfrac_false_div 3004311321 2097152) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3004311321) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 309069795421681876992) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 33554414 33554432 228 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q0 3004311321 2097152 226375608064910080 72057594037927936 228 309069795421681876992 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554414 33554432 309069795421681876992 302231454903657293676544 70274335 68719476736 12512208 12500000 (Ns396p1223 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p1225 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz186) Bool.false Ns396p1200 Ns396p1201 9680984486135457 1024000000000000000000 384551849090 268435456 2539 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz186) (@HAdd.hAdd Real Real Real qz367 qz190 (Enclosure.sfrac Bool.true Ns396p1202 Ns396p1203)) Bool.false Ns396p1200 Ns396p1201 9680984486135457 1024000000000000000000 Ns396p1204 (Ns396p1221 rfl rfl)) 

noncomputable def Ns396p1226 := Ns396p1199 47639 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 578 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 229216608 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 383 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 72629354 268435456) qz189 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 1) Bool.false 16777207 16777216 63157951 6553600000000 268435312 268435456 2587 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz186)) Bool.false 16777207 16777216 63157951 6553600000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz186) qz186) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz186)) Bool.false 33554414 33554432 1010527216 104857600000000 16777207 16777216 63157951 6553600000000 (Ns396p1224 rfl rfl) rfl)) rfl) (Ns396p1225 rfl) RS397to408.d7 

noncomputable def Ns396p1227 := nat_lit 4065952071624215568416258092283707791447259458453158973649305934743841 

noncomputable def Ns396p1228 := nat_lit 217240357379362484948436109883677788119042198329138410766219856161 

noncomputable def Ns396p1229 := nat_lit 12197421734157887980278877404631356018765540290962818644126385364519201 

noncomputable def Ns396p1230 := BSN.cos_dyadic_bound_f 146932397 268435456 3 2 268435456 134217728 Ns396p1227 Ns396p252 Ns396p1228 Ns396p1229 Ns396p255 Ns396p1228 229216608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 146932397) qz372 0 2 Ns396p1227 Ns396p252 Ns396p1228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 146932397) qz373 0 2 Ns396p1229 Ns396p255 Ns396p1228 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1231 := nat_lit 29257484626973572891376526360576 

noncomputable def Ns396p1232 := BSN.sin_dyadic_bound_f 73546032 268435456 2 1 268435456 134217728 Ns396p1231 Ns396p131 Ns396p1231 Ns396p1231 Ns396p132 Ns396p1231 72629354 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 73546032) qz370 0 1 Ns396p1231 Ns396p131 Ns396p1231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 73546032) qz371 0 1 Ns396p1231 Ns396p132 Ns396p1231 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1233 := nat_lit 4000456941092387623630642193615448220056130391013531516901052566686810344536713592452665949766090961024390625 

noncomputable def Ns396p1234 := nat_lit 409907037287239193780794339233699136594819649954771987914835370694075730514856620770044137910400390625 

noncomputable def Ns396p1235 := nat_lit 24255670150292279688638099328481881602125375382170121368524138938555535680618372027561238808528897231385990625 

noncomputable def Ns396p1236 := BSN.cos_dyadic_bound_f 293578185 268435456 4 3 268435456 134217728 Ns396p1233 Ns396p246 Ns396p1234 Ns396p1235 Ns396p249 Ns396p1234 123274607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 293578185) qz372 0 3 Ns396p1233 Ns396p246 Ns396p1234 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 293578185) qz373 0 3 Ns396p1235 Ns396p249 Ns396p1234 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1237 := nat_lit 3238659332472917659443196484380577715016979205636144709739174928119265 

noncomputable def Ns396p1238 := nat_lit 42543824002524794444238220769035680373666622483519655775549322721 

noncomputable def Ns396p1239 := nat_lit 8482134133142589782207842978163125100609578649753500922255154874742241 

noncomputable def Ns396p1240 := BSN.sin_dyadic_bound_f 119840763 268435456 3 2 268435456 134217728 Ns396p1237 Ns396p121 Ns396p1238 Ns396p1239 Ns396p124 Ns396p1238 115899334 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 119840763) qz370 0 2 Ns396p1237 Ns396p121 Ns396p1238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 119840763) qz371 0 2 Ns396p1239 Ns396p124 Ns396p1238 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1241 := Ns396p1197 80869 BSN.abs_quadSignPos (BSN.cos_quad_nat0 244 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 123274607 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 137 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 115899334 268435456) qz189 rfl rfl (Ns396p1226 RS397to408.d9 RS397to408.d11 RS397to408.d13 RS397to408.d17 (Ns396p1230 rfl rfl) (Ns396p1232 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns396p1225 rfl) RS397to408.d19 RS397to408.d21 RS397to408.d23 RS397to408.d25 RS397to408.d17 (Ns396p1236 rfl rfl) (Ns396p1240 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns396p1242 := nat_lit 36916709103053751028288887329349381569163369280969883398022153095734625 

noncomputable def Ns396p1243 := nat_lit 5526285558347330122081890036176666611261627556966953888122879731041 

noncomputable def Ns396p1244 := nat_lit 96677671759951071301511334231094570459009638815066986212334392493073761 

noncomputable def Ns396p1245 := BSN.sin_dyadic_bound_f 220193333 268435456 3 2 268435456 134217728 Ns396p1242 Ns396p121 Ns396p1243 Ns396p1244 Ns396p124 Ns396p1243 196317481 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 220193333) qz370 0 2 Ns396p1242 Ns396p121 Ns396p1243 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 220193333) qz371 0 2 Ns396p1244 Ns396p124 Ns396p1243 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1246 := nat_lit 3629080684909228419979536438703531805990904791673913232160540753487708809552009246524939511181982440000000000 

noncomputable def Ns396p1247 := nat_lit 306090115915434422095432353598824585041929712360381479395862250317139483898350566650390625000000000000 

noncomputable def Ns396p1248 := nat_lit 22005090285008913276926316935617667907818094392152550397884386014469994289921524262483554002444860136000000000 

noncomputable def Ns396p1249 := BSN.cos_dyadic_bound_f 286519450 268435456 4 3 268435456 134217728 Ns396p1246 Ns396p246 Ns396p1247 Ns396p1248 Ns396p249 Ns396p1247 129501650 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 286519450) qz372 0 3 Ns396p1246 Ns396p246 Ns396p1247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 286519450) qz373 0 3 Ns396p1248 Ns396p249 Ns396p1247 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1250 := Ns396p1195 109042 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 196317481 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 129501650 268435456) qz189 rfl rfl (Ns396p1241 rfl rfl) (Ns396p1225 rfl) RS397to408.d27 RS397to408.d29 RS397to408.d31 RS397to408.d33 RS397to408.d17 (Ns396p1245 rfl rfl) (Ns396p1249 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p1251 := nat_lit 14250016886569644202404338262001926167628788618965511157464484993957475455768151995293056930515677423673017041 

noncomputable def Ns396p1252 := nat_lit 18406556324336044378829861272558342754824520198171059333336146770433858611117596797397304027350554378961 

noncomputable def Ns396p1253 := nat_lit 86276089052394231694703796976835726487617017138896604654234511589815154757078840035851955293600239460825432785 

noncomputable def Ns396p1254 := BSN.cos_dyadic_bound_f 403101467 268435456 4 3 268435456 134217728 Ns396p1251 Ns396p246 Ns396p1252 Ns396p1253 Ns396p249 Ns396p1252 18541186 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 403101467) qz372 0 3 Ns396p1251 Ns396p246 Ns396p1252 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 403101467) qz373 0 3 Ns396p1253 Ns396p249 Ns396p1252 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1255 := nat_lit 89636520423195954162361028236818236914372994247844521493090777866240000 

noncomputable def Ns396p1256 := nat_lit 32566549403756746965625514698376422790739527971536106631193600000000 

noncomputable def Ns396p1257 := nat_lit 234709588599811892834905965977393249138839501889543640690215819059200000 

noncomputable def Ns396p1258 := BSN.sin_dyadic_bound_f 274850460 268435456 3 2 268435456 134217728 Ns396p1255 Ns396p121 Ns396p1256 Ns396p1257 Ns396p124 Ns396p1256 229281861 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 274850460) qz370 0 2 Ns396p1255 Ns396p121 Ns396p1256 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 274850460) qz371 0 2 Ns396p1257 Ns396p124 Ns396p1256 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1259 := Ns396p1193 133658 BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 18541186 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 145 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 229281861 268435456) qz189 rfl rfl (Ns396p1250 rfl) (Ns396p1225 rfl) RS397to408.d35 RS397to408.d37 RS397to408.d39 RS397to408.d41 RS397to408.d17 (Ns396p1254 rfl rfl) (Ns396p1258 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p1260 := nat_lit 5057333321402262550971072177885961929827461287495465989162063049588736 

noncomputable def Ns396p1261 := nat_lit 336084002427685342012875387700540022274170839262835604028097888256 

noncomputable def Ns396p1262 := nat_lit 15171327796201932282229190782882484709437835520807872296278132952989696 

noncomputable def Ns396p1263 := BSN.cos_dyadic_bound_f 155169364 268435456 3 2 268435456 134217728 Ns396p1260 Ns396p252 Ns396p1261 Ns396p1262 Ns396p255 Ns396p1261 224822532 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 155169364) qz372 0 2 Ns396p1260 Ns396p252 Ns396p1261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 155169364) qz373 0 2 Ns396p1262 Ns396p255 Ns396p1261 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1264 := Ns396p1191 Bool.false 57021575 133658 Bool.true 155169364 14148475504056880 1 Bool.false 224822532 Bool.false Bool.false 128116701 144992 BSN.abs_quadSignPos qz394 (BSN.sfrac_eq_quadSignPos_mul Bool.false 224822532 268435456) qz189 rfl (Ns396p1259 rfl) (Ns396p1225 rfl) RS397to408.d43 RS397to408.d45 RS397to408.d17 (Ns396p1263 rfl rfl) rfl 

noncomputable def Ns396p1265 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) 128116701 268435456 144992 268435456 128116701 268435456 144992 268435456 68782130108301312 128116701 134217728 4531 4194304 (Ns396p1264 rfl rfl rfl rfl) 

noncomputable def Ns396p1266 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz187) (Zeta.RiemannSiegel.correction qz188) 5065447 16777216 1 16777216 15021805627345 17592186044416 1414164312220447 54975581388800000000 76092160249617848215 295147905179352825856 

noncomputable def Ns396p1267 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz187 1 1 0 1 5065447 16777216 1 16777216 5065447 16777216 1 16777216 

noncomputable abbrev qz195 := qz496

noncomputable def Ns396p1268 := @Enclosure.Real.IsNear.sqrt_image qz195 1009481587237 8388608000 189029 8388608000 184045035 184045070 16777216 (@Enclosure.Real.IsNear.of_eq qz195 (@HMul.hMul Real Real Real qz5 qz186 qz3) Bool.false 1009481587237 8388608000 189029 8388608000 (BSN.t_div_two_pi_mk qz186 756116 1000 qz189) (@Enclosure.Real.IsNear.mulLit_ff qz186 qz3 756116 1000 0 1 5340353 33554432 1 33554432 1009481587237 8388608000 189029 8388608000 (Enclosure.Real.IsNear.const Bool.false 756116 1000) RS397to408.d48 rfl)) 

noncomputable abbrev qz751 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 756116 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz667 := qz751

noncomputable abbrev qz503 := qz667

noncomputable abbrev qz196 := qz503

noncomputable def Ns396p1269 := @Enclosure.Real.IsNear.sqrt_image qz196 368090105 33554432 35 33554432 55567646 55567652 16777216 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 368090105 33554432 35 33554432 368090105 33554432 35 33554432 (Ns396p1268 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns396p1270 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz196) 55567649 16777216 3 16777216 5065446 5065448 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz196) Bool.false 111135298 33554432 6 33554432 55567649 16777216 3 16777216 (Ns396p1269 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns396p1271 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz196)) Bool.false 10130894 33554432 2 33554432 5065447 16777216 1 16777216 (Ns396p1270 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz197 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz497))

noncomputable abbrev qz668 := (@HMul.hMul Real Real Real qz707 qz750 qz750)

noncomputable abbrev qz504 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz668 qz663) qz593)

noncomputable abbrev qz198 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz504))

noncomputable def Ns396p1272 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz188) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz197) qz198) Bool.false 15021805627345 

noncomputable def Ns396p1273 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz197) qz198 1067561 1048576 59 

noncomputable def Ns396p1274 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz197) Bool.false 34161952 33554432 236 33554432 1067561 1048576 59 

noncomputable def Ns396p1275 := @Enclosure.Real.IsNear.recentre' qz197 Bool.false 32957716 33554432 1414804432 209715200000000 8239429 8388608 88425277 13107200000000 

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz349 qz346 qz497)

noncomputable def Ns396p1276 := @Enclosure.Real.IsNear.cos_image qz199 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 102245599) qz413) Bool.false 102245599 16777216 221 33554432 Bool.false 32957716 33554432 1 

noncomputable def Ns396p1277 := nat_lit 188902527919221551065241713 

noncomputable def Ns396p1278 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz188 884279719003555 140737488355328 1 500000000000000 32545785 33554432 35 33554432 28779577614550115265675 4722366482869645213696 Ns396p1277 

noncomputable def Ns396p1279 := @Enclosure.Real.IsNear.subLit_ff_p qz196 qz1 368090105 33554432 35 33554432 10 1 0 1 32545785 32545785 33554432 35 

noncomputable def Ns396p1280 := @Ns396p1279 33554432 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 368090105 33554432 35 33554432 368090105 33554432 35 33554432 (Ns396p1268 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns396p1281 := @Enclosure.Real.IsNear.recentre' qz199 Bool.false 28779577614550115265675 4722366482869645213696 Ns396p1277 Ns396p300 102245599 16777216 221 33554432 (@Ns396p1278 Ns396p300 RS397to408.d47 (Ns396p1280 rfl rfl) rfl) 

noncomputable def Ns396p1282 := nat_lit 3341286308904525772095488 

noncomputable def Ns396p1283 := nat_lit 5491363081733862277482531983091863631699404352871662081160703460788745796580201393776430625 

noncomputable def Ns396p1284 := nat_lit 6614714287014869935175443484721012839797324730329625928291903634371394597230889625390625 

noncomputable def Ns396p1285 := nat_lit 14371431867123996175416347332931999300329244303195724151536988839038685304552629829068590625 

noncomputable def Ns396p1286 := BSN.sin_dyadic_bound_f 94965068595 68719476736 3 2 33554432 12512208 Ns396p1283 Ns396p175 Ns396p1284 Ns396p1285 Ns396p178 Ns396p1284 32957716 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 94965068595) qz368 0 2 Ns396p1283 Ns396p175 Ns396p1284 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 94965068595) qz369 0 2 Ns396p1285 Ns396p178 Ns396p1284 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1287 := @Ns396p1276 6250000 (Ns396p1281 rfl) (Enclosure.sfrac_false_div 102245599 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 102245599) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p1282) qz414) 226375608064910080 72057594037927936 Bool.false 32957716 33554432 0 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 102245599 16777216 226375608064910080 72057594037927936 0 Ns396p1282 Ns396p399 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 32957716 33554432 Ns396p1282 Ns396p399 94965068595 68719476736 12512208 12500000 (Ns396p1286 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p1288 := @Enclosure.Real.IsNear.inv_image qz197 8239429 8388608 88425277 13107200000000 17080858 17081094 16777216 (Ns396p1275 (Ns396p1287 rfl rfl) rfl) rfl 

noncomputable def Ns396p1289 := @Enclosure.Real.IsNear.recentre' qz198 Bool.false 14071145 16777216 

noncomputable abbrev qz200 := (@HMul.hMul Real Real Real qz349 qz346 qz504)

noncomputable def Ns396p1290 := @Enclosure.Real.IsNear.cos_image qz200 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4830951)) qz377) Bool.true 4830951 8388608 

noncomputable def Ns396p1291 := nat_lit 91254087950240898994344887245 

noncomputable def Ns396p1292 := nat_lit 93172428765873662973835927018479193 

noncomputable def Ns396p1293 := @Enclosure.Real.IsNear.recentre' qz200 Bool.true Ns396p1291 Ns396p185 Ns396p1292 

noncomputable abbrev qz201 := qz504

noncomputable def Ns396p1294 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz201 884279719003555 140737488355328 1 500000000000000 103195952580559 

noncomputable abbrev qz505 := (@HSub.hSub Real Real Real qz583 qz668 qz663)

noncomputable abbrev qz202 := qz505

noncomputable def Ns396p1295 := @Enclosure.Real.IsNear.subLit_tf qz202 qz29 32827208402895 1125899906842624 3452611295 1125899906842624 1 16 

noncomputable abbrev qz506 := qz668

noncomputable abbrev qz203 := qz506

noncomputable def Ns396p1296 := @Enclosure.Real.IsNear.subLit_ff_n qz203 qz188 1059228121266225 1125899906842624 2278206175 1125899906842624 32545785 33554432 35 33554432 

noncomputable def Ns396p1297 := @Enclosure.Real.IsNear.mulLit_ff qz188 qz188 32545785 33554432 35 33554432 32545785 33554432 35 33554432 1059228121266225 1125899906842624 

noncomputable def Ns396p1298 := nat_lit 4531352484567878600720762258143510690172202722116090066881 

noncomputable def Ns396p1299 := nat_lit 296661412303269326448651648446027943702656226770417601 

noncomputable def Ns396p1300 := nat_lit 13593464130879029263509389471133640014629202853894729365441 

noncomputable def Ns396p1301 := BSN.cos_dyadic_bound_f 4830951 8388608 3 2 16777216 6250000 Ns396p1298 Ns396p194 Ns396p1299 Ns396p1300 Ns396p197 Ns396p1299 14071145 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 4830951) (BSN.cosEvenQ 8388608) 0 2 Ns396p1298 Ns396p194 Ns396p1299 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 4830951) (BSN.cosOddQ 8388608) 0 2 Ns396p1300 Ns396p197 Ns396p1299 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1302 := @Ns396p1289 510444304 26214400000000 14071145 16777216 31902769 1638400000000 (@Ns396p1290 81 4194304 Bool.false 14071145 16777216 1 6250000 (@Ns396p1293 Ns396p188 4830951 8388608 81 4194304 (@Ns396p1294 1125899906842624 3452611295 1125899906842624 Ns396p1291 Ns396p185 Ns396p1292 Ns396p188 RS397to408.d47 (@Ns396p1295 0 1 1651135241288944 103195952580559 1125899906842624 3452611295 1125899906842624 (@Ns396p1296 1101498332104768880640 32827208402895 1125899906842624 3452611295 1125899906842624 (@Ns396p1297 2278206175 1125899906842624 (Ns396p1280 rfl rfl) (Ns396p1280 rfl rfl) rfl) (Ns396p1280 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4830951 8388608) (BSN.cos_neg_of_bound 4830951 8388608 Bool.false 14071145 16777216 1 6250000 (Ns396p1301 rfl rfl)) rfl rfl) 

noncomputable def Ns396p1303 := @Ns396p1266 225322466549809123133 Ns396p1188 (Ns396p1267 qz31 (@Enclosure.Real.IsNear.of_eq qz187 (@Inv.inv Real Real.instInv (Real.sqrt qz196)) Bool.false 5065447 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz195 (BSN.t_div_two_pi_nonneg qz186 756116 1000 qz189)) Ns396p1271) rfl) (@Ns396p1272 17592186044416 1414164312220447 54975581388800000000 (BSN.correction_mk qz188 (BSN.cos_two_pi_p_ne_zero_mk qz186 756116 1000 10 qz189 rfl rfl (@BSN.floor_sqrt_eq_dec qz186 756116 1000 10 qz189 rfl rfl rfl))) (@Ns396p1273 8388608 14071145 16777216 31902769 1638400000000 15021805627345 17592186044416 1414164312220447 54975581388800000000 (@Ns396p1274 8388608 (Ns396p1288 rfl rfl rfl rfl rfl) rfl) (Ns396p1302 rfl) rfl)) 

noncomputable def Ns396p1304 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz186) (hardyZApproximantRS₀ qz186) Bool.false 205639444673984325737 295147905179352825856 31362117375631409123133 Ns396p1188 (@Eq.refl Real (hardyZApproximantRS₀ qz186)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz186) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz187) (Zeta.RiemannSiegel.correction qz188))) Bool.false 205639444673984325737 295147905179352825856 31362117375631409123133 Ns396p1188 (BSN.hardyZApproximantRS₀_eq qz186 10 (@BSN.floor_sqrt_eq_dec qz186 756116 1000 10 qz189 rfl rfl rfl)) (@Ns396p1190 205639444673984325737 295147905179352825856 31362117375631409123133 Ns396p1188 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 10)) Bool.false 128116701 134217728 4531 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (Ns396p1265 (Ns396p1264 rfl rfl rfl rfl) rfl rfl)) (Ns396p1303 rfl) rfl rfl)) 

theorem RS397to408.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz186) Bool.false 205639444673984325737 295147905179352825856 31362117375631409123133 Ns396p1188 := Ns396p1304 

noncomputable def Ns396p1305 := nat_lit 8042576939601514701664679 

noncomputable def Ns396p1306 := nat_lit 7378697629483820646400000000 

noncomputable def Ns396p1307 := nat_lit 389213705802542021534795431936 

noncomputable abbrev qz752 := (Enclosure.sfrac Bool.false 757427 1000)

noncomputable abbrev qz669 := qz752

noncomputable abbrev qz507 := qz669

noncomputable abbrev qz204 := qz507

noncomputable abbrev qz205 := qz350

noncomputable abbrev qz753 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 757427 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz670 := qz753

noncomputable abbrev qz508 := qz670

noncomputable abbrev qz206 := qz508

noncomputable abbrev qz207 := qz352

noncomputable abbrev qz754 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 757427 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz671 := qz754

noncomputable abbrev qz509 := qz671

noncomputable abbrev qz208 := qz509

noncomputable abbrev qz672 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz205 qz206 qz207))

noncomputable def Ns396p1308 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (@HMul.hMul Real Real Real qz5 qz672 (Zeta.RiemannSiegel.correction qz208)) 16171859 16777216 145249 134217728 4991050134501859571405 18889465931478580854784 57428718459703501664679 Ns396p1306 Ns396p1307 

noncomputable def Ns396p1309 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos BSN.quadSignPos 9 10 757427 1000 196 268435456 134217728 4503599627370496 Bool.false 385394902971 2544 618095470 44 84886744 8 

noncomputable def Ns396p1310 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 757427 1000 88 145 268435456 134217728 4503599627370496 Bool.false 385394902971 2544 

noncomputable def Ns396p1311 := Ns396p1310 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 187819768 109236 Bool.true 291842330 Bool.true 205041388 14148475504056880 1 Bool.false 124814006 Bool.false Bool.false 185676478 Bool.true Bool.true 205583515 

noncomputable def Ns396p1312 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 757427 1000 50 24 268435456 134217728 4503599627370496 Bool.false 385394902971 2544 

noncomputable def Ns396p1313 := Ns396p1312 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 168418913 81014 Bool.false 11035811 Bool.true 128268073 14148475504056880 1 Bool.false 268208638 Bool.true Bool.false 238368597 Bool.false Bool.true 187819768 

noncomputable def Ns396p1314 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 757427 1000 245 137 268435456 134217728 4503599627370496 Bool.false 385394902971 2544 

noncomputable def Ns396p1315 := Ns396p1314 372130544 43 134217720 8 432030192 43 120047984 16 Bool.false 51587399 47726 Bool.false 227111495 Bool.false 396503062 14148475504056880 1 Bool.false 200970045 Bool.true Bool.false 267257744 Bool.true Bool.true 168418913 

noncomputable def Ns396p1316 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 757427 1000 579 384 268435456 134217728 4503599627370496 Bool.false 385394902971 2544 

noncomputable def Ns396p1317 := Ns396p1316 186065264 43 189812528 16 294906480 43 154981288 8 Bool.true 268435448 2595 Bool.false 324397289 Bool.false 108320089 14148475504056880 1 Bool.false 251007614 Bool.false Bool.false 246875540 Bool.false Bool.false 51587399 

noncomputable def Ns396p1318 := nat_lit 43951492279603935128138662784425924523185678370424410185781 

noncomputable def Ns396p1319 := nat_lit 30613116003804383598676007843093472221231467550736384000 

noncomputable def Ns396p1320 := nat_lit 119659071501316356531515895635360000 

noncomputable def Ns396p1321 := nat_lit 543798179887111807294459848149398912320 

noncomputable abbrev qz755 := (@Eq.refl Real (Enclosure.sfrac Bool.false 757427 1000))

noncomputable abbrev qz673 := qz755

noncomputable abbrev qz510 := qz673

noncomputable abbrev qz209 := qz510

noncomputable def Ns396p1322 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz204 757427 1000 2294783641316 16000000 1514854 4000 2000 Ns396p1320 Ns396p1321 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns396p1323 := nat_lit 14064477529473259241004372091016295847419417078535811259449920 

noncomputable abbrev qz674 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1514854))))

noncomputable abbrev qz511 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 757427 4000) (Real.log (Enclosure.sfrac Bool.false 2294783641316 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz674))

noncomputable abbrev qz675 := (Enclosure.sfrac Bool.false 757427 2000)

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz511 qz675) (@HMul.hMul Real Real Real qz349 qz675 (Real.log Real.pi)))

noncomputable def Ns396p1324 := @Enclosure.Real.IsNear.addLit_ft_p qz210 (Enclosure.sfrac Bool.true Ns396p1320 Ns396p1321) 25863418093784596826181 18014398509481984000 38790795792285591 4096000000000000000000 Ns396p1320 Ns396p1321 0 1 Ns396p1323 

noncomputable def Ns396p1325 := nat_lit 1735664607430929753703012368384000 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz355 qz511 qz675)

noncomputable def Ns396p1326 := @Enclosure.Real.IsNear.subLit_ff_p qz211 (@HMul.hMul Real Real Real qz5 qz675 (Real.log Real.pi)) 33673104088983136979013 18014398509481984000 15308552876759 4000000000000000000 29093347471947 67108864000 757427 134217728000 Ns396p1325 25863418093784596826181 18014398509481984000 

noncomputable def Ns396p1327 := nat_lit 67346208177966273958026000 

noncomputable abbrev qz212 := qz511

noncomputable def Ns396p1328 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz675 40495399998903842326597 18014398509481984000 15308552876759 4000000000000000000 757427 2000 0 1 Ns396p1327 33673104088983136979013 18014398509481984000 15308552876759 4000000000000000000 

noncomputable def Ns396p1329 := nat_lit 91187534172641264214461469672976941056 

noncomputable def Ns396p1330 := nat_lit 57417014935074226898468864 

noncomputable def Ns396p1331 := nat_lit 5581039916832869288571216872336036069183063324471040 

noncomputable def Ns396p1332 := nat_lit 3771570345741665844345424831072342118359191717888 

noncomputable def Ns396p1333 := nat_lit 4576644346583571998556752024159026099256894208 

noncomputable def Ns396p1334 := BSN.log_dyadic_bound 197631641316 4391935641316 3 2 Ns396p1331 134217728 50000000 Ns396p1332 Ns396p1333 12087424 4589567282632 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 197631641316) (BSN.artanhQ 4391935641316) 0 2 Ns396p1332 Ns396p1331 Ns396p1333 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz512 := (Real.log (Enclosure.sfrac Bool.false 2294783641316 16000000))

noncomputable def Ns396p1335 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 757427 4000) qz512 757427 4000 0 1 53473762176068711 4503599627370496 20000017 1000000000000000 40502471263733195566597 18014398509481984000 15148552876259 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 757427 4000) (BSN.isNear_log_sfrac 2294783641316 16000000 53473762176068711 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2294783641316) qz358)) Bool.false Ns396p1330 Ns396p100 1000000850000000 50000000000000000000000 53473762176068711 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2294783641316 16000000 17 4589567282632 4194304000000 12087424 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns396p1334 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns396p1336 := BSN.arctan_dyadic_bound_f 1000 1514854 1 0 16777216 6250000 0 1 1 0 1 1 11075 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1514854) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1514854) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns396p1337 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1514854))) 884279719003555 562949953421312 1 2000000000000000 11075 16777216 1 6250000 14829517179407805972480 883908103669155 562949953421312 320000001 2000000000000000 qz15 (Ns396p1336 rfl) rfl rfl 

noncomputable abbrev qz513 := (@HMul.hMul Real Real Real qz579 qz584 qz674)

noncomputable abbrev qz213 := qz513

noncomputable abbrev qz514 := qz674

noncomputable abbrev qz214 := qz514

noncomputable def Ns396p1338 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 757427 4000) qz512) qz213 40502471263733195566597 18014398509481984000 15148552876259 4000000000000000000 883908103669155 2251799813685248 320000001 8000000000000000 Ns396p1329 40495399998903842326597 18014398509481984000 15308552876759 4000000000000000000 (Ns396p1335 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz214 1 4 0 1 883908103669155 562949953421312 320000001 2000000000000000 883908103669155 2251799813685248 320000001 8000000000000000 qz366 Ns396p1337 rfl) 

noncomputable def Ns396p1339 := @Ns396p1324 Ns396p1318 Ns396p1319 38790795792285591 4096000000000000000000 (@Ns396p1326 38790795792285591 4096000000000000000000 (Ns396p1328 (Ns396p1338 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 757427 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz675 (Real.log Real.pi) 757427 2000 0 1 38410761 33554432 1 67108864 29093347471947 67108864000 757427 134217728000 (Enclosure.Real.IsNear.const Bool.false 757427 2000) RS397to408.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns396p1320 Ns396p1321) 

noncomputable def Ns396p1340 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz204) Bool.false Ns396p1318 Ns396p1319 38790795792285591 4096000000000000000000 48174362871 33554432 319 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz204) (@HAdd.hAdd Real Real Real qz367 qz210 (Enclosure.sfrac Bool.true Ns396p1320 Ns396p1321)) Bool.false Ns396p1318 Ns396p1319 38790795792285591 4096000000000000000000 Ns396p1322 (Ns396p1339 rfl rfl)) 

noncomputable def Ns396p1341 := BSN.cos_dyadic_bound_f 3464343 68719476736 1 0 33554432 12512208 0 1 1 0 1 1 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 3464343) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 3464343) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns396p1342 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz204) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48174362871) qz392) Bool.false 48174362871 33554432 319 33554432 Bool.true 33554431 33554432 1 6250000 (Ns396p1340 rfl) (Enclosure.sfrac_false_div 48174362871 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48174362871) qz392) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 243781466396580380672) qz393) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 228 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q2 48174362871 33554432 226375608064910080 72057594037927936 228 243781466396580380672 Ns396p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554431 33554432 243781466396580380672 Ns396p100 3464343 68719476736 12512208 12500000 (Ns396p1341 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p1343 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz204) Bool.false Ns396p1318 Ns396p1319 38790795792285591 4096000000000000000000 385394902971 268435456 2544 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz204) (@HAdd.hAdd Real Real Real qz367 qz210 (Enclosure.sfrac Bool.true Ns396p1320 Ns396p1321)) Bool.false Ns396p1318 Ns396p1319 38790795792285591 4096000000000000000000 Ns396p1322 (Ns396p1339 rfl rfl)) 

noncomputable def Ns396p1344 := Ns396p1317 47726 BSN.abs_quadSignPos (BSN.cos_quad_nat3 579 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 251007614 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 384 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 246875540 268435456) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 1) Bool.true 33554431 33554432 126706527 13107200000000 268435448 268435456 2595 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz204)) Bool.true 33554431 33554432 126706527 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz204) qz204) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz204)) Bool.true 33554431 33554432 2027304432 209715200000000 33554431 33554432 126706527 13107200000000 (Ns396p1342 rfl rfl) rfl)) rfl) (Ns396p1343 rfl) RS397to408.d7 

noncomputable def Ns396p1345 := nat_lit 15503622928899845779226436394930294508568865891633428095760051810352975120356690031618999457644176298567444321 

noncomputable def Ns396p1346 := nat_lit 1358083877990513629591451637611525439215688665204131601839727566757649919641186962699554366361580513121 

noncomputable def Ns396p1347 := nat_lit 77484335347491807087695205808471855677362924466571863737692429148508836228047612356980678791472756461768714081 

noncomputable def Ns396p1348 := BSN.sin_dyadic_bound_f 324397289 268435456 4 3 268435456 134217728 Ns396p1345 Ns396p258 Ns396p1346 Ns396p1347 Ns396p261 Ns396p1346 251007614 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 324397289) qz370 0 3 Ns396p1345 Ns396p258 Ns396p1346 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 324397289) qz371 0 3 Ns396p1347 Ns396p261 Ns396p1346 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1349 := nat_lit 1200913378066671406117267681336957579151854999185511767160129127770561 

noncomputable def Ns396p1350 := nat_lit 18952742642198649807903836491420408565635835742601131997615942081 

noncomputable def Ns396p1351 := nat_lit 3602702228714729821052187236337889896638433725885050099216392151427521 

noncomputable def Ns396p1352 := BSN.cos_dyadic_bound_f 108320089 268435456 3 2 268435456 134217728 Ns396p1349 Ns396p252 Ns396p1350 Ns396p1351 Ns396p255 Ns396p1350 246875540 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 108320089) qz372 0 2 Ns396p1349 Ns396p252 Ns396p1350 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 108320089) qz373 0 2 Ns396p1351 Ns396p255 Ns396p1350 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1353 := nat_lit 41780279997615551249248894690251686462978042502391715531273557821330625 

noncomputable def Ns396p1354 := nat_lit 7078038635909031810009023501906786868705767890817145440914687890625 

noncomputable def Ns396p1355 := nat_lit 109413083169296876744149947674513234510012206739202693870240694323090625 

noncomputable def Ns396p1356 := BSN.sin_dyadic_bound_f 227111495 268435456 3 2 268435456 134217728 Ns396p1353 Ns396p121 Ns396p1354 Ns396p1355 Ns396p124 Ns396p1354 200970045 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 227111495) qz370 0 2 Ns396p1353 Ns396p121 Ns396p1354 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 227111495) qz371 0 2 Ns396p1355 Ns396p124 Ns396p1354 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1357 := nat_lit 34632797668906836017360393699210138100369426287675072838561437953534419588560950488076257326741928470995603456 

noncomputable def Ns396p1358 := nat_lit 15099360223063773758919182382394149908299972131686199360031262546235585090646289468817726441361439789056 

noncomputable def Ns396p1359 := nat_lit 172995685570777470420264804339308872400149106517854654058874329702952923174025442639102589403937309384031932416 

noncomputable def Ns396p1360 := BSN.sin_dyadic_bound_f 396503062 268435456 4 3 268435456 134217728 Ns396p1357 Ns396p258 Ns396p1358 Ns396p1359 Ns396p261 Ns396p1358 267257744 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 396503062) qz370 0 3 Ns396p1357 Ns396p258 Ns396p1358 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 396503062) qz371 0 3 Ns396p1359 Ns396p261 Ns396p1358 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1361 := Ns396p1315 81014 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 245 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 200970045 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 137 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267257744 268435456) qz209 rfl rfl (Ns396p1344 RS397to408.d9 RS397to408.d11 RS397to408.d13 RS397to408.d17 (Ns396p1348 rfl rfl) (Ns396p1352 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns396p1343 rfl) RS397to408.d19 RS397to408.d21 RS397to408.d23 RS397to408.d25 RS397to408.d17 (Ns396p1356 rfl rfl) (Ns396p1360 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns396p1362 := nat_lit 14832590828870907995753253841 

noncomputable def Ns396p1363 := BSN.cos_dyadic_bound_f 11035811 268435456 2 1 268435456 134217728 Ns396p1362 Ns396p141 Ns396p1362 Ns396p1362 Ns396p142 Ns396p1362 268208638 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11035811) qz372 0 1 Ns396p1362 Ns396p141 Ns396p1362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11035811) qz373 0 1 Ns396p1362 Ns396p142 Ns396p1362 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1364 := nat_lit 2361329288706789659392602975407687017531901222552951649555177840490561 

noncomputable def Ns396p1365 := nat_lit 73273774273142028190681404097549083237031744102308464904171862081 

noncomputable def Ns396p1366 := nat_lit 7083841318571822694121427563414865954429229604170650331735725177747521 

noncomputable def Ns396p1367 := BSN.cos_dyadic_bound_f 128268073 268435456 3 2 268435456 134217728 Ns396p1364 Ns396p252 Ns396p1365 Ns396p1366 Ns396p255 Ns396p1365 238368597 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 128268073) qz372 0 2 Ns396p1364 Ns396p252 Ns396p1365 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 128268073) qz373 0 2 Ns396p1366 Ns396p255 Ns396p1365 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1368 := Ns396p1313 109236 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268208638 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 238368597 268435456) qz209 rfl rfl (Ns396p1361 rfl rfl) (Ns396p1343 rfl) RS397to408.d27 RS397to408.d29 RS397to408.d31 RS397to408.d33 RS397to408.d17 (Ns396p1363 rfl rfl) (Ns396p1367 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p1369 := nat_lit 3906600009654004058544438784665297134696987989337887273275169878181419445613305641124048936191158377024000000 

noncomputable def Ns396p1370 := nat_lit 381750318086536041072585757224148015098318200594543641269937016956398338393355167817041761000000000000 

noncomputable def Ns396p1371 := nat_lit 23686909443216038894253784744334918544340675092847929756457885683368706046999743840542402534452155741145600000 

noncomputable def Ns396p1372 := BSN.cos_dyadic_bound_f 291842330 268435456 4 3 268435456 134217728 Ns396p1369 Ns396p246 Ns396p1370 Ns396p1371 Ns396p249 Ns396p1370 124814006 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 291842330) qz372 0 3 Ns396p1369 Ns396p246 Ns396p1370 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 291842330) qz373 0 3 Ns396p1371 Ns396p249 Ns396p1370 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1373 := nat_lit 27755964257082382978269446684110492861467793373212108726483754737008640 

noncomputable def Ns396p1374 := nat_lit 3124152785079500015251728833151913297012225135079511839728793092096 

noncomputable def Ns396p1375 := nat_lit 72689133949754207657347667087892854396601439041527298883526463408111616 

noncomputable def Ns396p1376 := BSN.sin_dyadic_bound_f 205041388 268435456 3 2 268435456 134217728 Ns396p1373 Ns396p121 Ns396p1374 Ns396p1375 Ns396p124 Ns396p1374 185676478 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 205041388) qz370 0 2 Ns396p1373 Ns396p121 Ns396p1374 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 205041388) qz371 0 2 Ns396p1375 Ns396p124 Ns396p1374 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1377 := Ns396p1311 133895 BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 124814006 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 145 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 185676478 268435456) qz209 rfl rfl (Ns396p1368 rfl) (Ns396p1343 rfl) RS397to408.d35 RS397to408.d37 RS397to408.d39 RS397to408.d41 RS397to408.d17 (Ns396p1372 rfl rfl) (Ns396p1376 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p1378 := nat_lit 1960442141861911279949039698554514664501528849336895891939428149559296 

noncomputable def Ns396p1379 := nat_lit 50506594843688044959550115476352904528162974265430789946741948416 

noncomputable def Ns396p1380 := nat_lit 5881225412396046463757199995432591287695530222062156814238390964781056 

noncomputable def Ns396p1381 := BSN.cos_dyadic_bound_f 122438644 268435456 3 2 268435456 134217728 Ns396p1378 Ns396p252 Ns396p1379 Ns396p1380 Ns396p255 Ns396p1379 240992894 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 122438644) qz372 0 2 Ns396p1378 Ns396p252 Ns396p1379 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 122438644) qz373 0 2 Ns396p1380 Ns396p255 Ns396p1379 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1382 := Ns396p1309 Bool.true 205583515 133895 Bool.true 122438644 14148475504056880 1 Bool.false 240992894 Bool.false Bool.true 129374872 145249 BSN.abs_quadSignPos qz394 (BSN.sfrac_eq_quadSignPos_mul Bool.false 240992894 268435456) qz209 rfl (Ns396p1377 rfl) (Ns396p1343 rfl) RS397to408.d43 RS397to408.d45 RS397to408.d17 (Ns396p1381 rfl rfl) rfl 

noncomputable def Ns396p1383 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) 129374872 268435456 145249 268435456 129374872 268435456 145249 268435456 69457605520523264 16171859 16777216 145249 134217728 (Ns396p1382 rfl rfl rfl rfl) 

noncomputable def Ns396p1384 := @Enclosure.Real.IsNear.mulLit_ff qz672 (Zeta.RiemannSiegel.correction qz208) 10126507 33554432 1 33554432 492869864653415 562949953421312 706514417023411 27487790694400000000 4991050134501859571405 18889465931478580854784 

noncomputable abbrev qz676 := (@HPow.hPow Real Real Real qz205 qz206 qz207)

noncomputable def Ns396p1385 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz676 1 1 0 1 10126507 33554432 1 33554432 10126507 33554432 1 33554432 

noncomputable def Ns396p1386 := @Enclosure.Real.IsNear.sqrt_image qz206 4044927551731 33554432000 757427 33554432000 184204520 184204555 16777216 (@Enclosure.Real.IsNear.of_eq qz206 (@HMul.hMul Real Real Real qz5 qz204 qz3) Bool.false 4044927551731 33554432000 757427 33554432000 (BSN.t_div_two_pi_mk qz204 757427 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz204 qz3 757427 1000 0 1 5340353 33554432 1 33554432 4044927551731 33554432000 757427 33554432000 (Enclosure.Real.IsNear.const Bool.false 757427 1000) RS397to408.d48 rfl)) 

noncomputable abbrev qz756 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 757427 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz677 := qz756

noncomputable abbrev qz515 := qz677

noncomputable abbrev qz215 := qz515

noncomputable def Ns396p1387 := @Enclosure.Real.IsNear.sqrt_image qz215 368409075 33554432 35 33554432 55591717 55591723 16777216 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 368409075 33554432 35 33554432 368409075 33554432 35 33554432 (Ns396p1386 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns396p1388 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz215) 6948965 2097152 3 16777216 5063253 5063254 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz215) Bool.false 111183440 33554432 6 33554432 6948965 2097152 3 16777216 (Ns396p1387 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns396p1389 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 10126507 33554432 1 33554432 10126507 33554432 1 33554432 (Ns396p1388 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz216 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz509))

noncomputable abbrev qz678 := (@HMul.hMul Real Real Real qz707 qz754 qz754)

noncomputable abbrev qz516 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz678 qz671) qz593)

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz516))

noncomputable def Ns396p1390 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz216) qz217) Bool.false 492869864653415 

noncomputable def Ns396p1391 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz216) qz217 33836207 33554432 231 

noncomputable def Ns396p1392 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz216) Bool.false 33836207 33554432 231 33554432 33836207 33554432 231 

noncomputable def Ns396p1393 := @Enclosure.Real.IsNear.recentre' qz216 Bool.false 33275004 33554432 1414804432 209715200000000 8318751 8388608 88425277 13107200000000 

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz349 qz346 qz509)

noncomputable def Ns396p1394 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 206495345) qz392) Bool.false 206495345 33554432 221 33554432 Bool.false 33275004 33554432 1 

noncomputable def Ns396p1395 := nat_lit 188902527919769537352603761 

noncomputable def Ns396p1396 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 32864755 33554432 35 33554432 29061636316520679204025 4722366482869645213696 Ns396p1395 

noncomputable def Ns396p1397 := @Enclosure.Real.IsNear.subLit_ff_p qz215 qz1 368409075 33554432 35 33554432 10 1 0 1 32864755 32864755 33554432 35 

noncomputable def Ns396p1398 := @Ns396p1397 33554432 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 368409075 33554432 35 33554432 368409075 33554432 35 33554432 (Ns396p1386 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns396p1399 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 29061636316520679204025 4722366482869645213696 Ns396p1395 Ns396p300 206495345 33554432 221 33554432 (@Ns396p1396 Ns396p300 RS397to408.d47 (Ns396p1398 rfl rfl) rfl) 

noncomputable def Ns396p1400 := nat_lit 6971400639645713862492160 

noncomputable def Ns396p1401 := nat_lit 6505520441356231933718249339151853344174771473580628715592081129794823862516472499825495585 

noncomputable def Ns396p1402 := nat_lit 9279443485615014359831689545665910897249189265311019592334243531921654288993133073223201 

noncomputable def Ns396p1403 := nat_lit 17023243961718183136489020771847585379005045648186381175782147517077617913932391474567269921 

noncomputable def Ns396p1404 := BSN.sin_dyadic_bound_f 99069561651 68719476736 3 2 33554432 12512208 Ns396p1401 Ns396p175 Ns396p1402 Ns396p1403 Ns396p178 Ns396p1402 33275004 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 99069561651) qz368 0 2 Ns396p1401 Ns396p175 Ns396p1402 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 99069561651) qz369 0 2 Ns396p1403 Ns396p178 Ns396p1402 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1405 := @Ns396p1394 6250000 (Ns396p1399 rfl) (Enclosure.sfrac_false_div 206495345 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 206495345) qz392) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p1400) qz393) 226375608064910080 72057594037927936 Bool.false 33275004 33554432 0 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 206495345 33554432 226375608064910080 72057594037927936 0 Ns396p1400 Ns396p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33275004 33554432 Ns396p1400 Ns396p100 99069561651 68719476736 12512208 12500000 (Ns396p1404 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p1406 := @Enclosure.Real.IsNear.inv_image qz216 8318751 8388608 88425277 13107200000000 16917988 16918219 16777216 (Ns396p1393 (Ns396p1405 rfl rfl) rfl) rfl 

noncomputable def Ns396p1407 := @Enclosure.Real.IsNear.recentre' qz217 Bool.false 14566345 16777216 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz349 qz346 qz516)

noncomputable def Ns396p1408 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 17421095)) qz392) Bool.true 17421095 33554432 

noncomputable def Ns396p1409 := nat_lit 82268795477926801353361945445 

noncomputable def Ns396p1410 := nat_lit 93774971158911973964590772015812573 

noncomputable def Ns396p1411 := @Enclosure.Real.IsNear.recentre' qz219 Bool.true Ns396p1409 Ns396p185 Ns396p1410 

noncomputable abbrev qz220 := qz516

noncomputable def Ns396p1412 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz220 884279719003555 140737488355328 1 500000000000000 93034809811799 

noncomputable abbrev qz517 := (@HSub.hSub Real Real Real qz583 qz678 qz671)

noncomputable abbrev qz221 := qz517

noncomputable def Ns396p1413 := @Enclosure.Real.IsNear.subLit_tf qz221 qz29 22666065634135 1125899906842624 3474939195 1125899906842624 1 16 

noncomputable abbrev qz518 := qz678

noncomputable abbrev qz222 := qz518

noncomputable def Ns396p1414 := @Enclosure.Real.IsNear.subLit_ff_n qz222 qz208 1080092121210025 1125899906842624 2300534075 1125899906842624 32864755 33554432 35 33554432 

noncomputable def Ns396p1415 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 32864755 33554432 35 33554432 32864755 33554432 35 33554432 1080092121210025 1125899906842624 

noncomputable def Ns396p1416 := nat_lit 196168570521824224024646699490226516624363363061229410928690625 

noncomputable def Ns396p1417 := nat_lit 8484057285907638341303499015732140353132124327841187890625 

noncomputable def Ns396p1418 := nat_lit 588488743450900856797257491472648085592383824935032550410290625 

noncomputable def Ns396p1419 := BSN.cos_dyadic_bound_f 17421095 33554432 3 2 16777216 6250000 Ns396p1416 Ns396p322 Ns396p1417 Ns396p1418 Ns396p325 Ns396p1417 14566345 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 17421095) (BSN.cosEvenQ 33554432) 0 2 Ns396p1416 Ns396p322 Ns396p1417 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 17421095) (BSN.cosOddQ 33554432) 0 2 Ns396p1418 Ns396p325 Ns396p1417 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1420 := @Ns396p1407 4102304432 209715200000000 14566345 16777216 256394027 13107200000000 (@Ns396p1408 651 33554432 Bool.false 14566345 16777216 1 6250000 (@Ns396p1411 Ns396p188 17421095 33554432 651 33554432 (@Ns396p1412 1125899906842624 3474939195 1125899906842624 Ns396p1409 Ns396p185 Ns396p1410 Ns396p188 RS397to408.d47 (@Ns396p1413 0 1 1488556956988784 93034809811799 1125899906842624 3474939195 1125899906842624 (@Ns396p1414 760546958028119736320 22666065634135 1125899906842624 3474939195 1125899906842624 (@Ns396p1415 2300534075 1125899906842624 (Ns396p1398 rfl rfl) (Ns396p1398 rfl rfl) rfl) (Ns396p1398 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 17421095 33554432) (BSN.cos_neg_of_bound 17421095 33554432 Bool.false 14566345 16777216 1 6250000 (Ns396p1419 rfl rfl)) rfl rfl) 

noncomputable def Ns396p1421 := @Ns396p1384 57428718459703501664679 Ns396p1306 (Ns396p1385 qz31 (@Enclosure.Real.IsNear.of_eq qz676 (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 10126507 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz206 (BSN.t_div_two_pi_nonneg qz204 757427 1000 qz209)) Ns396p1389) rfl) (@Ns396p1390 562949953421312 706514417023411 27487790694400000000 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz204 757427 1000 10 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz204 757427 1000 10 qz209 rfl rfl rfl))) (@Ns396p1391 33554432 14566345 16777216 256394027 13107200000000 492869864653415 562949953421312 706514417023411 27487790694400000000 (@Ns396p1392 33554432 (Ns396p1406 rfl rfl rfl rfl rfl) rfl) (Ns396p1420 rfl) rfl)) 

noncomputable def Ns396p1422 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz204) (hardyZApproximantRS₀ qz204) Bool.true 23198944676073910089421 18889465931478580854784 Ns396p1305 Ns396p1306 (@Eq.refl Real (hardyZApproximantRS₀ qz204)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz204) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (@HMul.hMul Real Real Real qz5 qz672 (Zeta.RiemannSiegel.correction qz208))) Bool.true 23198944676073910089421 18889465931478580854784 Ns396p1305 Ns396p1306 (BSN.hardyZApproximantRS₀_eq qz204 10 (@BSN.floor_sqrt_eq_dec qz204 757427 1000 10 qz209 rfl rfl rfl)) (@Ns396p1308 23198944676073910089421 18889465931478580854784 Ns396p1305 Ns396p1306 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 10)) Bool.true 16171859 16777216 145249 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (Ns396p1383 (Ns396p1382 rfl rfl rfl rfl) rfl rfl)) (Ns396p1421 rfl) rfl rfl)) 

theorem RS397to408.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz204) Bool.true 23198944676073910089421 18889465931478580854784 Ns396p1305 Ns396p1306 := Ns396p1422 

noncomputable def Ns396p1423 := nat_lit 230584300921369395200000000 

noncomputable def Ns396p1424 := nat_lit 31811091472633130477397475328 

noncomputable abbrev qz757 := (Enclosure.sfrac Bool.false 758738 1000)

noncomputable abbrev qz679 := qz757

noncomputable abbrev qz519 := qz679

noncomputable abbrev qz223 := qz519

noncomputable abbrev qz758 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 758738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz680 := qz758

noncomputable abbrev qz520 := qz680

noncomputable abbrev qz224 := qz520

noncomputable abbrev qz759 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 758738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz681 := qz759

noncomputable abbrev qz521 := qz681

noncomputable abbrev qz225 := qz521

noncomputable abbrev qz682 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz205 qz224 qz207))

noncomputable def Ns396p1425 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HMul.hMul Real Real Real qz5 qz682 (Zeta.RiemannSiegel.correction qz225)) 90232399 134217728 145489 134217728 159835186717524610545 590295810358705651712 1811765036086459526163 Ns396p1423 Ns396p1424 

noncomputable def Ns396p1426 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos BSN.quadSignPos 9 10 758738 1000 196 268435456 134217728 4503599627370496 Bool.false 386238261485 2547 618095470 44 84886744 8 

noncomputable def Ns396p1427 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 758738 1000 88 145 268435456 134217728 4503599627370496 Bool.false 386238261485 2547 

noncomputable def Ns396p1428 := Ns396p1427 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 21179678 109416 Bool.true 180278560 Bool.true 134927683 14148475504056880 1 Bool.false 210140220 Bool.false Bool.false 129317406 Bool.true Bool.false 10010304 

noncomputable def Ns396p1429 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 758738 1000 50 23 268435456 134217728 4503599627370496 Bool.false 386238261485 2547 

noncomputable def Ns396p1430 := Ns396p1429 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 48348636 81146 Bool.false 223840350 Bool.true 391369492 14148475504056880 1 Bool.false 180392574 Bool.true Bool.false 266728553 Bool.false Bool.true 21179678 

noncomputable def Ns396p1431 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 758738 1000 246 138 268435456 134217728 4503599627370496 Bool.false 386238261485 2547 

noncomputable def Ns396p1432 := Ns396p1431 372130544 43 134217720 8 432030192 43 120047984 16 Bool.false 133446954 47802 Bool.false 160949438 Bool.false 251812566 14148475504056880 1 Bool.false 221612470 Bool.true Bool.false 158737039 Bool.true Bool.true 48348636 

noncomputable def Ns396p1433 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 758738 1000 581 385 268435456 134217728 4503599627370496 Bool.false 386238261485 2547 

noncomputable def Ns396p1434 := Ns396p1433 186065264 43 189812528 16 294906480 43 154981288 8 Bool.false 268435448 2595 Bool.false 80509385 Bool.false 143398780 14148475504056880 1 Bool.false 79307798 Bool.true Bool.false 136675108 Bool.true Bool.false 133446954 

noncomputable def Ns396p1435 := nat_lit 347711695869544926393333387839990172979636448906156998507 

noncomputable def Ns396p1436 := nat_lit 241659506436109464850151891884134025018274394144768000 

noncomputable def Ns396p1437 := nat_lit 120698227514455718543064824560640000 

noncomputable def Ns396p1438 := nat_lit 549470101841756024555597586832241233920 

noncomputable abbrev qz760 := (@Eq.refl Real (Enclosure.sfrac Bool.false 758738 1000))

noncomputable abbrev qz683 := qz760

noncomputable abbrev qz522 := qz683

noncomputable abbrev qz226 := qz522

noncomputable def Ns396p1439 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz223 758738 1000 2302734410576 16000000 1517476 4000 2000 Ns396p1437 Ns396p1438 qz226 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns396p1440 := nat_lit 7121135531408280092535467782962998742622954473598095329423360 

noncomputable abbrev qz684 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1517476))))

noncomputable abbrev qz523 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 758738 4000) (Real.log (Enclosure.sfrac Bool.false 2302734410576 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz684))

noncomputable abbrev qz685 := (Enclosure.sfrac Bool.false 758738 2000)

noncomputable abbrev qz227 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz523 qz685) (@HMul.hMul Real Real Real qz349 qz685 (Real.log Real.pi)))

noncomputable def Ns396p1441 := @Enclosure.Real.IsNear.addLit_ft_p qz227 (Enclosure.sfrac Bool.true Ns396p1437 Ns396p1438) 12960007459354190869983 9007199254740992000 19428826820014677 2048000000000000000000 Ns396p1437 Ns396p1438 0 1 Ns396p1440 

noncomputable def Ns396p1442 := nat_lit 434865689014392961461865414656000 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz355 qz523 qz685)

noncomputable def Ns396p1443 := @Enclosure.Real.IsNear.subLit_ff_p qz228 (@HMul.hMul Real Real Real qz5 qz685 (Real.log Real.pi)) 16871609193003077137887 9007199254740992000 7667386449523 2000000000000000000 14571851989809 33554432000 379369 67108864000 Ns396p1442 12960007459354190869983 9007199254740992000 

noncomputable def Ns396p1444 := nat_lit 6748643677201230855154800 

noncomputable abbrev qz229 := qz523

noncomputable def Ns396p1445 := @Enclosure.Real.IsNear.subLit_ff_p qz229 qz685 4057732273414982506387 1801439850948198400 7667386449523 2000000000000000000 758738 2000 0 1 Ns396p1444 16871609193003077137887 9007199254740992000 7667386449523 2000000000000000000 

noncomputable def Ns396p1446 := nat_lit 9137200777260475404173587838167678976 

noncomputable def Ns396p1447 := nat_lit 57433740295283964389621760 

noncomputable def Ns396p1448 := nat_lit 5621563462391387868750369840281206353218332499312640 

noncomputable def Ns396p1449 := nat_lit 4096315084510092009709940076817044651932511633408 

noncomputable def Ns396p1450 := nat_lit 5358769429705605877553675564807604842051862528 

noncomputable def Ns396p1451 := BSN.log_dyadic_bound 205582410576 4399886410576 3 2 Ns396p1448 134217728 50000000 Ns396p1449 Ns396p1450 12551646 4605468821152 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 205582410576) (BSN.artanhQ 4399886410576) 0 2 Ns396p1449 Ns396p1448 Ns396p1450 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz524 := (Real.log (Enclosure.sfrac Bool.false 2302734410576 16000000))

noncomputable def Ns396p1452 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 758738 4000) qz524 758738 4000 0 1 53489338881600615 4503599627370496 20000017 1000000000000000 4058439400434788742387 1801439850948198400 7587386449273 2000000000000000000 (Enclosure.Real.IsNear.const Bool.false 758738 4000) (BSN.isNear_log_sfrac 2302734410576 16000000 53489338881600615 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2302734410576) qz358)) Bool.false Ns396p1447 Ns396p100 1000000850000000 50000000000000000000000 53489338881600615 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2302734410576 16000000 17 4605468821152 4194304000000 12551646 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns396p1451 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns396p1453 := BSN.arctan_dyadic_bound_f 1000 1517476 1 0 16777216 6250000 0 1 1 0 1 1 11055 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1517476) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1517476) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns396p1454 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1517476))) 884279719003555 562949953421312 1 2000000000000000 11055 16777216 1 6250000 14829528438406874398720 883908774757795 562949953421312 320000001 2000000000000000 qz15 (Ns396p1453 rfl) rfl rfl 

noncomputable abbrev qz525 := (@HMul.hMul Real Real Real qz579 qz584 qz684)

noncomputable abbrev qz230 := qz525

noncomputable abbrev qz526 := qz684

noncomputable abbrev qz231 := qz526

noncomputable def Ns396p1455 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 758738 4000) qz524) qz230 4058439400434788742387 1801439850948198400 7587386449273 2000000000000000000 883908774757795 2251799813685248 320000001 8000000000000000 Ns396p1446 4057732273414982506387 1801439850948198400 7667386449523 2000000000000000000 (Ns396p1452 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz231 1 4 0 1 883908774757795 562949953421312 320000001 2000000000000000 883908774757795 2251799813685248 320000001 8000000000000000 qz366 Ns396p1454 rfl) 

noncomputable def Ns396p1456 := @Ns396p1441 Ns396p1435 Ns396p1436 19428826820014677 2048000000000000000000 (@Ns396p1443 19428826820014677 2048000000000000000000 (Ns396p1445 (Ns396p1455 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 758738 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz685 (Real.log Real.pi) 758738 2000 0 1 38410761 33554432 1 67108864 14571851989809 33554432000 379369 67108864000 (Enclosure.Real.IsNear.const Bool.false 758738 2000) RS397to408.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns396p1437 Ns396p1438) 

noncomputable def Ns396p1457 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns396p1435 Ns396p1436 19428826820014677 2048000000000000000000 48279782685 33554432 319 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz367 qz227 (Enclosure.sfrac Bool.true Ns396p1437 Ns396p1438)) Bool.false Ns396p1435 Ns396p1436 19428826820014677 2048000000000000000000 Ns396p1439 (Ns396p1456 rfl rfl)) 

noncomputable def Ns396p1458 := BSN.cos_dyadic_bound_f 14640142 68719476736 1 0 33554432 12512208 0 1 1 0 1 1 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 14640142) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 14640142) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns396p1459 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz223) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48279782685) qz392) Bool.false 48279782685 33554432 319 33554432 Bool.false 33554431 33554432 1 6250000 (Ns396p1457 rfl) (Enclosure.sfrac_false_div 48279782685 33554432) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48279782685) qz392) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1030208452786766479360) qz393) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 229 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q0 48279782685 33554432 226375608064910080 72057594037927936 229 1030208452786766479360 Ns396p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554431 33554432 1030208452786766479360 Ns396p100 14640142 68719476736 12512208 12500000 (Ns396p1458 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p1460 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns396p1435 Ns396p1436 19428826820014677 2048000000000000000000 386238261485 268435456 2547 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz367 qz227 (Enclosure.sfrac Bool.true Ns396p1437 Ns396p1438)) Bool.false Ns396p1435 Ns396p1436 19428826820014677 2048000000000000000000 Ns396p1439 (Ns396p1456 rfl rfl)) 

noncomputable def Ns396p1461 := Ns396p1434 47802 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 581 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 79307798 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 385 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 136675108 268435456) qz226 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) Bool.false 33554431 33554432 126706527 13107200000000 268435448 268435456 2595 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 33554431 33554432 126706527 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz223) qz223) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 33554431 33554432 2027304432 209715200000000 33554431 33554432 126706527 13107200000000 (Ns396p1459 rfl rfl) rfl)) rfl) (Ns396p1460 rfl) RS397to408.d7 

noncomputable def Ns396p1462 := nat_lit 42013226608472182848876969150625 

noncomputable def Ns396p1463 := BSN.sin_dyadic_bound_f 80509385 268435456 2 1 268435456 134217728 Ns396p1462 Ns396p131 Ns396p1462 Ns396p1462 Ns396p132 Ns396p1462 79307798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 80509385) qz370 0 1 Ns396p1462 Ns396p131 Ns396p1462 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 80509385) qz371 0 1 Ns396p1462 Ns396p132 Ns396p1462 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1464 := nat_lit 6639491551659638346557578525972824262058926053402433534131223306240000 

noncomputable def Ns396p1465 := nat_lit 178798409763042120586195096894253150188599720815319994393600000000 

noncomputable def Ns396p1466 := nat_lit 17388855056921341220407947061676710943149262883172672547495614259200000 

noncomputable def Ns396p1467 := BSN.sin_dyadic_bound_f 143398780 268435456 3 2 268435456 134217728 Ns396p1464 Ns396p121 Ns396p1465 Ns396p1466 Ns396p124 Ns396p1465 136675108 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 143398780) qz370 0 2 Ns396p1464 Ns396p121 Ns396p1465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 143398780) qz371 0 2 Ns396p1466 Ns396p124 Ns396p1465 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1468 := nat_lit 5854099002826816908709427820001571316390397571727745801572234798366976 

noncomputable def Ns396p1469 := nat_lit 450314277235731168979672181682926338623869072004654955343797616896 

noncomputable def Ns396p1470 := nat_lit 17561396379925979263790324115641348096493944977039228094806016799867136 

noncomputable def Ns396p1471 := BSN.cos_dyadic_bound_f 160949438 268435456 3 2 268435456 134217728 Ns396p1468 Ns396p252 Ns396p1469 Ns396p1470 Ns396p255 Ns396p1469 221612470 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 160949438) qz372 0 2 Ns396p1468 Ns396p252 Ns396p1469 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 160949438) qz373 0 2 Ns396p1470 Ns396p255 Ns396p1469 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1472 := nat_lit 35089608782740505638390585985978894371688776760259304496891405389291776 

noncomputable def Ns396p1473 := nat_lit 16166618445489362323179232716926452802933958893938292345317918269696 

noncomputable def Ns396p1474 := nat_lit 105236493111330538190525399492502830209460462362990036905983580331335936 

noncomputable def Ns396p1475 := BSN.cos_dyadic_bound_f 251812566 268435456 3 2 268435456 134217728 Ns396p1472 Ns396p252 Ns396p1473 Ns396p1474 Ns396p255 Ns396p1473 158737039 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 251812566) qz372 0 2 Ns396p1472 Ns396p252 Ns396p1473 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 251812566) qz373 0 2 Ns396p1474 Ns396p255 Ns396p1473 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1476 := Ns396p1432 81146 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 246 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 221612470 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 138 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 158737039 268435456) qz226 rfl rfl (Ns396p1461 RS397to408.d9 RS397to408.d11 RS397to408.d13 RS397to408.d17 (Ns396p1463 rfl rfl) (Ns396p1467 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns396p1460 rfl) RS397to408.d19 RS397to408.d21 RS397to408.d23 RS397to408.d25 RS397to408.d17 (Ns396p1471 rfl rfl) (Ns396p1475 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns396p1477 := nat_lit 21905202442774337201795142586334441219444451433506391942206070500000000 

noncomputable def Ns396p1478 := nat_lit 6302415183352072325092623363514833939723631405682187539062500000000 

noncomputable def Ns396p1479 := nat_lit 65703002497956307460735242512276293990453907037707811451540086500000000 

noncomputable def Ns396p1480 := BSN.cos_dyadic_bound_f 223840350 268435456 3 2 268435456 134217728 Ns396p1477 Ns396p252 Ns396p1478 Ns396p1479 Ns396p255 Ns396p1478 180392574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 223840350) qz372 0 2 Ns396p1477 Ns396p252 Ns396p1478 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 223840350) qz373 0 2 Ns396p1479 Ns396p255 Ns396p1478 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1481 := nat_lit 32871125855449859816689178612655261915584268573133338977922839887399158925858999750476101032746120476398452736 

noncomputable def Ns396p1482 := nat_lit 12913489765507702471665041286451299110489992629827179033141289592189723648229174985061697726696690548736 

noncomputable def Ns396p1483 := nat_lit 164203991733195701266563605809866123613267545030770585360081747216684322721818590114777470277270295090923831296 

noncomputable def Ns396p1484 := BSN.sin_dyadic_bound_f 391369492 268435456 4 3 268435456 134217728 Ns396p1481 Ns396p258 Ns396p1482 Ns396p1483 Ns396p261 Ns396p1482 266728553 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 391369492) qz370 0 3 Ns396p1481 Ns396p258 Ns396p1482 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 391369492) qz371 0 3 Ns396p1483 Ns396p261 Ns396p1482 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1485 := Ns396p1430 109416 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 180392574 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 23 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266728553 268435456) qz226 rfl rfl (Ns396p1476 rfl rfl) (Ns396p1460 rfl) RS397to408.d27 RS397to408.d29 RS397to408.d31 RS397to408.d33 RS397to408.d17 (Ns396p1480 rfl rfl) (Ns396p1484 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p1486 := nat_lit 9215050153502873115388032648123930429740305112944123252885474508800000 

noncomputable def Ns396p1487 := nat_lit 1115713385373611183358655516832695031278272390473524550041600000000 

noncomputable def Ns396p1488 := nat_lit 27642919033737872123797380633338125899158358794051422709556340326400000 

noncomputable def Ns396p1489 := BSN.cos_dyadic_bound_f 180278560 268435456 3 2 268435456 134217728 Ns396p1486 Ns396p252 Ns396p1487 Ns396p1488 Ns396p255 Ns396p1487 210140220 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 180278560) qz372 0 2 Ns396p1486 Ns396p252 Ns396p1487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 180278560) qz373 0 2 Ns396p1488 Ns396p255 Ns396p1487 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1490 := nat_lit 5204208876581403690689720454820698986291131404491383548509024418539425 

noncomputable def Ns396p1491 := nat_lit 109852134811107374385529106888015730839470931826313695860112500641 

noncomputable def Ns396p1492 := nat_lit 13629893011399696444628834144071631033864937392159238119158909485459361 

noncomputable def Ns396p1493 := BSN.sin_dyadic_bound_f 134927683 268435456 3 2 268435456 134217728 Ns396p1490 Ns396p121 Ns396p1491 Ns396p1492 Ns396p124 Ns396p1491 129317406 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 134927683) qz370 0 2 Ns396p1490 Ns396p121 Ns396p1491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 134927683) qz371 0 2 Ns396p1492 Ns396p124 Ns396p1491 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1494 := Ns396p1428 134116 BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 210140220 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 145 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 129317406 268435456) qz226 rfl rfl (Ns396p1485 rfl) (Ns396p1460 rfl) RS397to408.d35 RS397to408.d37 RS397to408.d39 RS397to408.d41 RS397to408.d17 (Ns396p1489 rfl rfl) (Ns396p1493 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p1495 := nat_lit 557296095032842196301636445883258830941962023109176383941589583359201 

noncomputable def Ns396p1496 := nat_lit 4081577491440353292542324796448320157503066961356116631125585121 

noncomputable def Ns396p1497 := nat_lit 1671880121943543708198324253000183596185571063193606439591506498907361 

noncomputable def Ns396p1498 := BSN.cos_dyadic_bound_f 89403291 268435456 3 2 268435456 134217728 Ns396p1495 Ns396p252 Ns396p1496 Ns396p1497 Ns396p255 Ns396p1496 253684542 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 89403291) qz372 0 2 Ns396p1495 Ns396p252 Ns396p1496 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 89403291) qz373 0 2 Ns396p1497 Ns396p255 Ns396p1496 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1499 := Ns396p1426 Bool.false 10010304 134116 Bool.true 89403291 14148475504056880 1 Bool.false 253684542 Bool.false Bool.false 90232399 145489 BSN.abs_quadSignPos qz394 (BSN.sfrac_eq_quadSignPos_mul Bool.false 253684542 268435456) qz226 rfl (Ns396p1494 rfl) (Ns396p1460 rfl) RS397to408.d43 RS397to408.d45 RS397to408.d17 (Ns396p1498 rfl rfl) rfl 

noncomputable def Ns396p1500 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) 90232399 268435456 145489 268435456 90232399 268435456 145489 268435456 48443150343077888 90232399 134217728 145489 134217728 (Ns396p1499 rfl rfl rfl rfl) 

noncomputable def Ns396p1501 := @Enclosure.Real.IsNear.mulLit_ff qz682 (Zeta.RiemannSiegel.correction qz225) 5061065 16777216 1 16777216 31581334505193 35184372088832 355543392892993 13743895347200000000 159835186717524610545 590295810358705651712 

noncomputable abbrev qz686 := (@HPow.hPow Real Real Real qz205 qz224 qz207)

noncomputable def Ns396p1502 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz686 1 1 0 1 5061065 16777216 1 16777216 5061065 16777216 1 16777216 

noncomputable def Ns396p1503 := @Enclosure.Real.IsNear.sqrt_image qz224 2025964377257 16777216000 379369 16777216000 184363867 184363902 16777216 (@Enclosure.Real.IsNear.of_eq qz224 (@HMul.hMul Real Real Real qz5 qz223 qz3) Bool.false 2025964377257 16777216000 379369 16777216000 (BSN.t_div_two_pi_mk qz223 758738 1000 qz226) (@Enclosure.Real.IsNear.mulLit_ff qz223 qz3 758738 1000 0 1 5340353 33554432 1 33554432 2025964377257 16777216000 379369 16777216000 (Enclosure.Real.IsNear.const Bool.false 758738 1000) RS397to408.d48 rfl)) 

noncomputable abbrev qz761 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 758738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz687 := qz761

noncomputable abbrev qz527 := qz687

noncomputable abbrev qz232 := qz527

noncomputable def Ns396p1504 := @Enclosure.Real.IsNear.sqrt_image qz232 368727769 33554432 35 33554432 55615756 55615763 16777216 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 368727769 33554432 35 33554432 368727769 33554432 35 33554432 (Ns396p1503 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns396p1505 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz232) 111231519 33554432 7 33554432 5061064 5061066 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz232) Bool.false 111231519 33554432 7 33554432 111231519 33554432 7 33554432 (Ns396p1504 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns396p1506 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 10122130 33554432 2 33554432 5061065 16777216 1 16777216 (Ns396p1505 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz233 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz521))

noncomputable abbrev qz688 := (@HMul.hMul Real Real Real qz707 qz759 qz759)

noncomputable abbrev qz528 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz688 qz681) qz593)

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz528))

noncomputable def Ns396p1507 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz225) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz233) qz234) Bool.false 31581334505193 

noncomputable def Ns396p1508 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz233) qz234 33635559 33554432 229 

noncomputable def Ns396p1509 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz233) Bool.false 33635559 33554432 229 33554432 33635559 33554432 229 

noncomputable def Ns396p1510 := @Enclosure.Real.IsNear.recentre' qz233 Bool.false 33473501 33554432 1414804432 209715200000000 33473501 33554432 88425277 13107200000000 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz349 qz346 qz521)

noncomputable def Ns396p1511 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 208497759) qz392) Bool.false 208497759 33554432 221 33554432 Bool.false 33473501 33554432 1 

noncomputable def Ns396p1512 := nat_lit 944512639601585247377881653 

noncomputable def Ns396p1513 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz225 884279719003555 140737488355328 1 500000000000000 33183449 33554432 35 33554432 29343450957288798161195 4722366482869645213696 Ns396p1512 

noncomputable def Ns396p1514 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz1 368727769 33554432 35 33554432 10 1 0 1 33183449 33183449 33554432 35 

noncomputable def Ns396p1515 := @Ns396p1514 33554432 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 368727769 33554432 35 33554432 368727769 33554432 35 33554432 (Ns396p1503 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns396p1516 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 29343450957288798161195 4722366482869645213696 Ns396p1512 Ns396p168 208497759 33554432 221 33554432 (@Ns396p1513 Ns396p168 RS397to408.d47 (Ns396p1515 rfl rfl) rfl) 

noncomputable def Ns396p1517 := nat_lit 7259978909861440722567168 

noncomputable def Ns396p1518 := nat_lit 2928797152854777518398175513903383082835653265415349984287050222304806065223215812769666322698926128565947958043673898236763243829798854321 

noncomputable def Ns396p1519 := nat_lit 1454342522872612033962552577709543435984159499951710709696644668439864781470107675895083289605987552122175791857620065729925621702321 

noncomputable def Ns396p1520 := nat_lit 14628796605434381018715542889640201237795476942542190576936130077865694777757382867612792806036112650599425159054575182555715027257702178481 

noncomputable def Ns396p1521 := BSN.sin_dyadic_bound_f 103170505523 68719476736 4 3 33554432 12512208 Ns396p1518 Ns396p112 Ns396p1519 Ns396p1520 Ns396p115 Ns396p1519 33473501 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 103170505523) qz368 0 3 Ns396p1518 Ns396p112 Ns396p1519 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 103170505523) qz369 0 3 Ns396p1520 Ns396p115 Ns396p1519 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1522 := @Ns396p1511 6250000 (Ns396p1516 rfl) (Enclosure.sfrac_false_div 208497759 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 208497759) qz392) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p1517) qz393) 226375608064910080 72057594037927936 Bool.false 33473501 33554432 0 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 208497759 33554432 226375608064910080 72057594037927936 0 Ns396p1517 Ns396p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33473501 33554432 Ns396p1517 Ns396p100 103170505523 68719476736 12512208 12500000 (Ns396p1521 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p1523 := @Enclosure.Real.IsNear.inv_image qz233 33473501 33554432 88425277 13107200000000 16817665 16817894 16777216 (Ns396p1510 (Ns396p1522 rfl rfl) rfl) rfl 

noncomputable def Ns396p1524 := @Enclosure.Real.IsNear.recentre' qz234 Bool.false 15022832 16777216 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz349 qz346 qz528)

noncomputable def Ns396p1525 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7740989)) qz413) Bool.true 7740989 16777216 

noncomputable def Ns396p1526 := nat_lit 73111574794545639090202200205 

noncomputable def Ns396p1527 := nat_lit 94376992180971712105695512135466777 

noncomputable def Ns396p1528 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true Ns396p1526 Ns396p185 Ns396p1527 

noncomputable abbrev qz237 := qz528

noncomputable def Ns396p1529 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz237 884279719003555 140737488355328 1 500000000000000 82679239638031 

noncomputable abbrev qz529 := (@HSub.hSub Real Real Real qz583 qz688 qz681)

noncomputable abbrev qz238 := qz529

noncomputable def Ns396p1530 := @Enclosure.Real.IsNear.subLit_tf qz238 qz29 12310495460367 1125899906842624 3497247775 1125899906842624 1 16 

noncomputable abbrev qz530 := qz688

noncomputable abbrev qz239 := qz530

noncomputable def Ns396p1531 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz225 1101141287535601 1125899906842624 2322842655 1125899906842624 33183449 33554432 35 33554432 

noncomputable def Ns396p1532 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 33183449 33554432 35 33554432 33183449 33554432 35 33554432 1101141287535601 1125899906842624 

noncomputable def Ns396p1533 := nat_lit 477954310433017965817975711031215462549797584745073400902561 

noncomputable def Ns396p1534 := nat_lit 12893523096888305639865610012906901251940559607036670881 

noncomputable def Ns396p1535 := nat_lit 1433837144252860120842647401873620573846888873116006129365921 

noncomputable def Ns396p1536 := BSN.cos_dyadic_bound_f 7740989 16777216 3 2 16777216 6250000 Ns396p1533 Ns396p603 Ns396p1534 Ns396p1535 Ns396p606 Ns396p1534 15022832 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 7740989) (BSN.cosEvenQ 16777216) 0 2 Ns396p1533 Ns396p603 Ns396p1534 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 7740989) (BSN.cosOddQ 16777216) 0 2 Ns396p1535 Ns396p606 Ns396p1534 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1537 := @Ns396p1524 258347152 13107200000000 938927 1048576 16146697 819200000000 (@Ns396p1525 41 2097152 Bool.false 15022832 16777216 1 6250000 (@Ns396p1528 Ns396p188 7740989 16777216 41 2097152 (@Ns396p1529 1125899906842624 3497247775 1125899906842624 Ns396p1526 Ns396p185 Ns396p1527 Ns396p188 RS397to408.d47 (@Ns396p1530 0 1 1322867834208496 82679239638031 1125899906842624 3497247775 1125899906842624 (@Ns396p1531 413071682811193196544 12310495460367 1125899906842624 3497247775 1125899906842624 (@Ns396p1532 2322842655 1125899906842624 (Ns396p1515 rfl rfl) (Ns396p1515 rfl rfl) rfl) (Ns396p1515 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7740989 16777216) (BSN.cos_neg_of_bound 7740989 16777216 Bool.false 15022832 16777216 1 6250000 (Ns396p1536 rfl rfl)) rfl rfl) 

noncomputable def Ns396p1538 := @Ns396p1501 1811765036086459526163 Ns396p1423 (Ns396p1502 qz31 (@Enclosure.Real.IsNear.of_eq qz686 (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 5061065 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz224 (BSN.t_div_two_pi_nonneg qz223 758738 1000 qz226)) Ns396p1506) rfl) (@Ns396p1507 35184372088832 355543392892993 13743895347200000000 (BSN.correction_mk qz225 (BSN.cos_two_pi_p_ne_zero_mk qz223 758738 1000 10 qz226 rfl rfl (@BSN.floor_sqrt_eq_dec qz223 758738 1000 10 qz226 rfl rfl rfl))) (@Ns396p1508 33554432 938927 1048576 16146697 819200000000 31581334505193 35184372088832 355543392892993 13743895347200000000 (@Ns396p1509 33554432 (Ns396p1523 rfl rfl rfl rfl rfl) rfl) (Ns396p1537 rfl) rfl)) 

noncomputable def Ns396p1539 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (hardyZApproximantRS₀ qz223) Bool.false 237011100892969447951 590295810358705651712 251759963807184059526163 Ns396p1423 (@Eq.refl Real (hardyZApproximantRS₀ qz223)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HMul.hMul Real Real Real qz5 qz682 (Zeta.RiemannSiegel.correction qz225))) Bool.false 237011100892969447951 590295810358705651712 251759963807184059526163 Ns396p1423 (BSN.hardyZApproximantRS₀_eq qz223 10 (@BSN.floor_sqrt_eq_dec qz223 758738 1000 10 qz226 rfl rfl rfl)) (@Ns396p1425 237011100892969447951 590295810358705651712 251759963807184059526163 Ns396p1423 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10)) Bool.false 90232399 134217728 145489 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (Ns396p1500 (Ns396p1499 rfl rfl rfl rfl) rfl rfl)) (Ns396p1538 rfl) rfl rfl)) 

theorem RS397to408.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz223) Bool.false 237011100892969447951 590295810358705651712 251759963807184059526163 Ns396p1423 := Ns396p1539 

noncomputable def Ns396p1540 := nat_lit 2018021763766754379499027 

noncomputable def Ns396p1541 := nat_lit 973273271930425544674008629248 

noncomputable abbrev qz762 := (Enclosure.sfrac Bool.false 760048 1000)

noncomputable abbrev qz689 := qz762

noncomputable abbrev qz531 := qz689

noncomputable abbrev qz240 := qz531

noncomputable abbrev qz763 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 760048 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz690 := qz763

noncomputable abbrev qz532 := qz690

noncomputable abbrev qz241 := qz532

noncomputable abbrev qz764 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 760048 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz691 := qz764

noncomputable abbrev qz533 := qz691

noncomputable abbrev qz242 := qz533

noncomputable abbrev qz692 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz205 qz241 qz207))

noncomputable def Ns396p1542 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HMul.hMul Real Real Real qz5 qz692 (Zeta.RiemannSiegel.correction qz242)) 168861147 134217728 145739 134217728 1310177527954439836787 4722366482869645213696 15000199761173579499027 Ns396p848 Ns396p1541 

noncomputable def Ns396p1543 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos BSN.quadSignPos 9 10 760048 1000 196 268435456 134217728 4503599627370496 Bool.false 387081280624 2552 618095470 44 84886744 8 

noncomputable def Ns396p1544 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 760048 1000 88 145 268435456 134217728 4503599627370496 Bool.false 387081280624 2552 

noncomputable def Ns396p1545 := Ns396p1544 558195838 44 94906264 8 589812974 44 89478488 8 Bool.true 322420580 109603 Bool.true 68495968 Bool.true 64563540 14148475504056880 1 Bool.false 259743801 Bool.false Bool.false 63942850 Bool.true Bool.true 251901565 

noncomputable def Ns396p1546 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 760048 1000 51 23 268435456 134217728 4503599627370496 Bool.false 387081280624 2552 

noncomputable def Ns396p1547 := Ns396p1546 480971758 44 109588312 8 522351262 44 101459064 8 Bool.true 405919994 81284 Bool.false 15129058 Bool.true 232630506 14148475504056880 1 Bool.false 15121049 Bool.false Bool.false 204586090 Bool.false Bool.true 322420580 

noncomputable def Ns396p1548 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 760048 1000 247 139 268435456 134217728 4503599627370496 Bool.false 387081280624 2552 

noncomputable def Ns396p1549 := Ns396p1548 372130544 43 134217720 8 432030192 43 120047984 16 Bool.true 499033469 47881 Bool.false 94820136 Bool.false 107214725 14148475504056880 1 Bool.false 92860565 Bool.false Bool.false 104386801 Bool.false Bool.true 405919994 

noncomputable def Ns396p1550 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 760048 1000 582 386 268435456 134217728 4503599627370496 Bool.false 387081280624 2552 

noncomputable def Ns396p1551 := Ns396p1550 186065264 43 189812528 16 294906480 43 154981288 8 Bool.true 268435344 2595 Bool.false 258125600 Bool.false 178433002 14148475504056880 1 Bool.false 153602648 Bool.true Bool.false 211283609 Bool.true Bool.true 499033469 

noncomputable def Ns396p1552 := nat_lit 687687804135936995264024597230249648057269251598417469 

noncomputable def Ns396p1553 := nat_lit 476901877018821755377393261502489772984467718144000 

noncomputable def Ns396p1554 := nat_lit 121743789603758936708933057904640000 

noncomputable def Ns396p1555 := nat_lit 555186854930154228789491184873610936320 

noncomputable abbrev qz765 := (@Eq.refl Real (Enclosure.sfrac Bool.false 760048 1000))

noncomputable abbrev qz693 := qz765

noncomputable abbrev qz534 := qz693

noncomputable abbrev qz243 := qz534

noncomputable def Ns396p1556 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz240 760048 1000 2310692849216 16000000 1520096 4000 2000 Ns396p1554 Ns396p1555 qz243 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns396p1557 := nat_lit 901366158637055338432462320081632818701623953455077744967680 

noncomputable abbrev qz694 := (@HSub.hSub Real Real Real qz711 qz712 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz713 (@Nat.cast Real Real.instNatCast 1520096))))

noncomputable abbrev qz535 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 760048 4000) (Real.log (Enclosure.sfrac Bool.false 2310692849216 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz694))

noncomputable abbrev qz695 := (Enclosure.sfrac Bool.false 760048 2000)

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz535 qz695) (@HMul.hMul Real Real Real qz349 qz695 (Real.log Real.pi)))

noncomputable def Ns396p1558 := @Enclosure.Real.IsNear.addLit_ft_p qz244 (Enclosure.sfrac Bool.true Ns396p1554 Ns396p1555) 1623536810542414395949 1125899906842624000 2432778780636099 256000000000000000000 Ns396p1554 Ns396p1555 0 1 Ns396p1557 

noncomputable def Ns396p1559 := nat_lit 6809606938605290870586474496000 

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz355 qz535 qz695)

noncomputable def Ns396p1560 := @Enclosure.Real.IsNear.subLit_ff_p qz245 (@HMul.hMul Real Real Real qz5 qz695 (Real.log Real.pi)) 2113331224829093181997 1125899906842624000 3840243230329 1000000000000000000 1824626379783 4194304000 47503 8388608000 Ns396p1559 1623536810542414395949 1125899906842624000 

noncomputable def Ns396p1561 := nat_lit 4226662449658186363994000 

noncomputable abbrev qz246 := qz535

noncomputable def Ns396p1562 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz695 2541200211027054524973 1125899906842624000 3840243230329 1000000000000000000 760048 2000 0 1 Ns396p1561 2113331224829093181997 1125899906842624000 3840243230329 1000000000000000000 

noncomputable def Ns396p1563 := nat_lit 5722274161727634279480872289177698304 

noncomputable def Ns396p1564 := nat_lit 57450424078261941996355584 

noncomputable def Ns396p1565 := nat_lit 5662346695836033093159807186155058468358986965975040 

noncomputable def Ns396p1566 := nat_lit 4436042234383103320804735552535605668884867186688 

noncomputable def Ns396p1567 := nat_lit 6237996356352813541009052972801764938385195008 

noncomputable def Ns396p1568 := BSN.log_dyadic_bound 213540849216 4407844849216 3 2 Ns396p1565 134217728 50000000 Ns396p1566 Ns396p1567 13014714 4621385698432 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 213540849216) (BSN.artanhQ 4407844849216) 0 2 Ns396p1566 Ns396p1565 Ns396p1567 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz536 := (Real.log (Enclosure.sfrac Bool.false 2310692849216 16000000))

noncomputable def Ns396p1569 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 760048 4000) qz536 760048 4000 0 1 53504876865317991 4503599627370496 20000017 1000000000000000 2541642165733200526473 1125899906842624000 950060807551 250000000000000000 (Enclosure.Real.IsNear.const Bool.false 760048 4000) (BSN.isNear_log_sfrac 2310692849216 16000000 53504876865317991 4503599627370496 20000017 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2310692849216) qz358)) Bool.false Ns396p1564 Ns396p100 1000000850000000 50000000000000000000000 53504876865317991 4503599627370496 20000017 1000000000000000 (BSN.log_rat_reduce_isNear 2310692849216 16000000 17 4621385698432 4194304000000 13014714 134217728 24973259072661432 36028797018963968 50000000 1000000000000000 rfl rfl rfl rfl (Ns396p1568 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns396p1570 := BSN.arctan_dyadic_bound_f 1000 1520096 1 0 16777216 6250000 0 1 1 0 1 1 11036 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1520096) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1520096) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns396p1571 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1520096))) 884279719003555 562949953421312 1 2000000000000000 11036 16777216 1 6250000 14829539134455989403648 883909412292003 562949953421312 320000001 2000000000000000 qz15 (Ns396p1570 rfl) rfl rfl 

noncomputable abbrev qz537 := (@HMul.hMul Real Real Real qz579 qz584 qz694)

noncomputable abbrev qz247 := qz537

noncomputable abbrev qz538 := qz694

noncomputable abbrev qz248 := qz538

noncomputable def Ns396p1572 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 760048 4000) qz536) qz247 2541642165733200526473 1125899906842624000 950060807551 250000000000000000 883909412292003 2251799813685248 320000001 8000000000000000 Ns396p1563 2541200211027054524973 1125899906842624000 3840243230329 1000000000000000000 (Ns396p1569 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz248 1 4 0 1 883909412292003 562949953421312 320000001 2000000000000000 883909412292003 2251799813685248 320000001 8000000000000000 qz366 Ns396p1571 rfl) 

noncomputable def Ns396p1573 := @Ns396p1558 Ns396p1552 Ns396p1553 2432778780636099 256000000000000000000 (@Ns396p1560 2432778780636099 256000000000000000000 (Ns396p1562 (Ns396p1572 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 760048 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz695 (Real.log Real.pi) 760048 2000 0 1 38410761 33554432 1 67108864 1824626379783 4194304000 47503 8388608000 (Enclosure.Real.IsNear.const Bool.false 760048 2000) RS397to408.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns396p1554 Ns396p1555) 

noncomputable def Ns396p1574 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns396p1552 Ns396p1553 2432778780636099 256000000000000000000 24192580039 16777216 319 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz367 qz244 (Enclosure.sfrac Bool.true Ns396p1554 Ns396p1555)) Bool.false Ns396p1552 Ns396p1553 2432778780636099 256000000000000000000 Ns396p1556 (Ns396p1573 rfl rfl)) 

noncomputable def Ns396p1575 := nat_lit 3795804036159243968053248 

noncomputable def Ns396p1576 := nat_lit 3502882219771998260432420787899100877791064676476141426850663237707452463653171478919085695744842405442290614950973922137171423643814400000 

noncomputable def Ns396p1577 := nat_lit 2485694437845571402852175967864543685789780664636421666066628015935841517820280417084302752582675070192099788409222423681000000000000 

noncomputable def Ns396p1578 := nat_lit 17492696409575064157388210813435115448300659279234674859191783210173521098771465666326746004675878520192243819467335868069859514475072000000 

noncomputable def Ns396p1579 := BSN.sin_dyadic_bound_f 107883239370 68719476736 4 3 33554432 12512208 Ns396p1576 Ns396p112 Ns396p1577 Ns396p1578 Ns396p115 Ns396p1577 33554418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107883239370) qz368 0 3 Ns396p1576 Ns396p112 Ns396p1577 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107883239370) qz369 0 3 Ns396p1578 Ns396p115 Ns396p1577 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1580 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz240) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24192580039) qz413) Bool.false 24192580039 16777216 319 33554432 Bool.true 33554418 33554432 1 6250000 (Ns396p1574 rfl) (Enclosure.sfrac_false_div 24192580039 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24192580039) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p1575) qz414) 226375608064910080 72057594037927936 Bool.false 33554418 33554432 229 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q1 24192580039 16777216 226375608064910080 72057594037927936 229 Ns396p1575 Ns396p399 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554418 33554432 Ns396p1575 Ns396p399 107883239370 68719476736 12512208 12500000 (Ns396p1579 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p1581 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns396p1552 Ns396p1553 2432778780636099 256000000000000000000 387081280624 268435456 2552 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz367 qz244 (Enclosure.sfrac Bool.true Ns396p1554 Ns396p1555)) Bool.false Ns396p1552 Ns396p1553 2432778780636099 256000000000000000000 Ns396p1556 (Ns396p1573 rfl rfl)) 

noncomputable def Ns396p1582 := Ns396p1551 47881 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 582 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 153602648 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 386 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 211283609 268435456) qz243 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) Bool.true 16777209 16777216 126706527 13107200000000 268435344 268435456 2595 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 16777209 16777216 126706527 13107200000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz240) qz240) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 33554418 33554432 2027304432 209715200000000 16777209 16777216 126706527 13107200000000 (Ns396p1580 rfl rfl) rfl)) rfl) (Ns396p1581 rfl) RS397to408.d7 

noncomputable def Ns396p1583 := nat_lit 38744858402987102043094408700589867966721069000563645258661888000000000 

noncomputable def Ns396p1584 := nat_lit 19708275653148981113665583922622147865715381800796160000000000000000 

noncomputable def Ns396p1585 := nat_lit 116195158657655008167055894933924359604431776238089343455985664000000000 

noncomputable def Ns396p1586 := BSN.cos_dyadic_bound_f 258125600 268435456 3 2 268435456 134217728 Ns396p1583 Ns396p252 Ns396p1584 Ns396p1585 Ns396p255 Ns396p1584 153602648 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 258125600) qz372 0 2 Ns396p1583 Ns396p252 Ns396p1584 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 258125600) qz373 0 2 Ns396p1585 Ns396p255 Ns396p1584 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1587 := nat_lit 8843414677852812871818387980243784785101371571608338636183857695252736 

noncomputable def Ns396p1588 := nat_lit 1027546437199559946494091208266695128364905395882159074083003392256 

noncomputable def Ns396p1589 := nat_lit 26528188940684039495562175758314820965047384904033251590403407078973696 

noncomputable def Ns396p1590 := BSN.cos_dyadic_bound_f 178433002 268435456 3 2 268435456 134217728 Ns396p1587 Ns396p252 Ns396p1588 Ns396p1589 Ns396p255 Ns396p1588 211283609 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 178433002) qz372 0 2 Ns396p1587 Ns396p252 Ns396p1588 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 178433002) qz373 0 2 Ns396p1589 Ns396p255 Ns396p1588 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1591 := nat_lit 80835531011723650962484893782016 

noncomputable def Ns396p1592 := BSN.sin_dyadic_bound_f 94820136 268435456 2 1 268435456 134217728 Ns396p1591 Ns396p131 Ns396p1591 Ns396p1591 Ns396p132 Ns396p1591 92860565 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 94820136) qz370 0 1 Ns396p1591 Ns396p131 Ns396p1591 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 94820136) qz371 0 1 Ns396p1591 Ns396p132 Ns396p1591 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1593 := nat_lit 132134961934428643755651656640625 

noncomputable def Ns396p1594 := BSN.sin_dyadic_bound_f 107214725 268435456 2 1 268435456 134217728 Ns396p1593 Ns396p131 Ns396p1593 Ns396p1593 Ns396p132 Ns396p1593 104386801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 107214725) qz370 0 1 Ns396p1593 Ns396p131 Ns396p1593 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 107214725) qz371 0 1 Ns396p1593 Ns396p132 Ns396p1593 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1595 := Ns396p1549 81284 BSN.abs_quadSignPos (BSN.cos_quad_nat3 247 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 92860565 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 139 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 104386801 268435456) qz243 rfl rfl (Ns396p1582 RS397to408.d9 RS397to408.d11 RS397to408.d13 RS397to408.d17 (Ns396p1586 rfl rfl) (Ns396p1590 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns396p1581 rfl) RS397to408.d19 RS397to408.d21 RS397to408.d23 RS397to408.d25 RS397to408.d17 (Ns396p1592 rfl rfl) (Ns396p1594 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns396p1596 := nat_lit 52389897808512812617353108496 

noncomputable def Ns396p1597 := BSN.sin_dyadic_bound_f 15129058 268435456 2 1 268435456 134217728 Ns396p1596 Ns396p131 Ns396p1596 Ns396p1596 Ns396p132 Ns396p1596 15121049 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15129058) qz370 0 1 Ns396p1596 Ns396p131 Ns396p1596 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15129058) qz371 0 1 Ns396p1596 Ns396p132 Ns396p1596 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1598 := nat_lit 45992705718501492314845840690830729440731391044370758357546779414585600 

noncomputable def Ns396p1599 := nat_lit 8576958774908732473062831786302599729156956639952911707898846863616 

noncomputable def Ns396p1600 := nat_lit 120443199900915960972020814367378849088068341472125395746047824143278336 

noncomputable def Ns396p1601 := BSN.sin_dyadic_bound_f 232630506 268435456 3 2 268435456 134217728 Ns396p1598 Ns396p121 Ns396p1599 Ns396p1600 Ns396p124 Ns396p1599 204586090 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 232630506) qz370 0 2 Ns396p1598 Ns396p121 Ns396p1599 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 232630506) qz371 0 2 Ns396p1600 Ns396p124 Ns396p1599 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1602 := Ns396p1547 109603 BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 15121049 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 23 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 204586090 268435456) qz243 rfl rfl (Ns396p1595 rfl rfl) (Ns396p1581 rfl) RS397to408.d27 RS397to408.d29 RS397to408.d31 RS397to408.d33 RS397to408.d17 (Ns396p1597 rfl rfl) (Ns396p1601 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p1603 := nat_lit 22012026672526165208400397336576 

noncomputable def Ns396p1604 := BSN.cos_dyadic_bound_f 68495968 268435456 2 1 268435456 134217728 Ns396p1603 Ns396p141 Ns396p1603 Ns396p1603 Ns396p142 Ns396p1603 259743801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 68495968) qz372 0 1 Ns396p1603 Ns396p141 Ns396p1603 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 68495968) qz373 0 1 Ns396p1603 Ns396p142 Ns396p1603 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1605 := nat_lit 17375981216084302311360358560000 

noncomputable def Ns396p1606 := BSN.sin_dyadic_bound_f 64563540 268435456 2 1 268435456 134217728 Ns396p1605 Ns396p131 Ns396p1605 Ns396p1605 Ns396p132 Ns396p1605 63942850 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 64563540) qz370 0 1 Ns396p1605 Ns396p131 Ns396p1605 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 64563540) qz371 0 1 Ns396p1605 Ns396p132 Ns396p1605 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1607 := Ns396p1545 134346 BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 259743801 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 145 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63942850 268435456) qz243 rfl rfl (Ns396p1602 rfl) (Ns396p1581 rfl) RS397to408.d35 RS397to408.d37 RS397to408.d39 RS397to408.d41 RS397to408.d17 (Ns396p1604 rfl rfl) (Ns396p1606 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns396p1608 := nat_lit 9897318364857930272368093122576 

noncomputable def Ns396p1609 := BSN.cos_dyadic_bound_f 56089218 268435456 2 1 268435456 134217728 Ns396p1608 Ns396p141 Ns396p1608 Ns396p1608 Ns396p142 Ns396p1608 262596862 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 56089218) qz372 0 1 Ns396p1608 Ns396p141 Ns396p1608 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 56089218) qz373 0 1 Ns396p1608 Ns396p142 Ns396p1608 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1610 := Ns396p1543 Bool.true 251901565 134346 Bool.true 56089218 14148475504056880 1 Bool.false 262596862 Bool.false Bool.true 168861147 145739 BSN.abs_quadSignPos qz394 (BSN.sfrac_eq_quadSignPos_mul Bool.false 262596862 268435456) qz243 rfl (Ns396p1607 rfl) (Ns396p1581 rfl) RS397to408.d43 RS397to408.d45 RS397to408.d17 (Ns396p1609 rfl rfl) rfl 

noncomputable def Ns396p1611 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) 168861147 268435456 145739 268435456 168861147 268435456 145739 268435456 90656637991256064 168861147 134217728 145739 134217728 (Ns396p1610 rfl rfl rfl rfl) 

noncomputable def Ns396p1612 := @Enclosure.Real.IsNear.mulLit_ff qz692 (Zeta.RiemannSiegel.correction qz242) 5058883 16777216 1 16777216 258985536521489 281474976710656 5890245175010881 219902325555200000000 1310177527954439836787 4722366482869645213696 

noncomputable abbrev qz696 := (@HPow.hPow Real Real Real qz205 qz241 qz207)

noncomputable def Ns396p1613 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz696 1 1 0 1 5058883 16777216 1 16777216 5058883 16777216 1 16777216 

noncomputable def Ns396p1614 := @Enclosure.Real.IsNear.sqrt_image qz241 253682788559 2097152000 47503 2097152000 184522955 184522991 16777216 (@Enclosure.Real.IsNear.of_eq qz241 (@HMul.hMul Real Real Real qz5 qz240 qz3) Bool.false 253682788559 2097152000 47503 2097152000 (BSN.t_div_two_pi_mk qz240 760048 1000 qz243) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz3 760048 1000 0 1 5340353 33554432 1 33554432 253682788559 2097152000 47503 2097152000 (Enclosure.Real.IsNear.const Bool.false 760048 1000) RS397to408.d48 rfl)) 

noncomputable abbrev qz766 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 760048 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz697 := qz766

noncomputable abbrev qz539 := qz697

noncomputable abbrev qz249 := qz539

noncomputable def Ns396p1615 := @Enclosure.Real.IsNear.sqrt_image qz249 184522973 16777216 9 8388608 55639747 55639753 16777216 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 369045946 33554432 36 33554432 184522973 16777216 9 8388608 (Ns396p1614 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns396p1616 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 27819875 8388608 3 16777216 5058882 5058884 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 111279500 33554432 6 33554432 27819875 8388608 3 16777216 (Ns396p1615 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns396p1617 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 10117766 33554432 2 33554432 5058883 16777216 1 16777216 (Ns396p1616 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz533))

noncomputable abbrev qz698 := (@HMul.hMul Real Real Real qz707 qz764 qz764)

noncomputable abbrev qz540 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz698 qz691) qz593)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz540))

noncomputable def Ns396p1618 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz242) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 258985536521489 

noncomputable def Ns396p1619 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz250) qz251 33556073 33554432 233 

noncomputable def Ns396p1620 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz250) Bool.false 33556073 33554432 233 33554432 33556073 33554432 233 

noncomputable def Ns396p1621 := @Enclosure.Real.IsNear.recentre' qz250 Bool.false 33552791 33554432 1452304432 209715200000000 33552791 33554432 90769027 13107200000000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz349 qz346 qz533)

noncomputable def Ns396p1622 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 52624231) qz377) Bool.false 52624231 8388608 227 33554432 Bool.false 33552791 33554432 1 

noncomputable def Ns396p1623 := nat_lit 242874678753340603112932351 

noncomputable def Ns396p1624 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz242 884279719003555 140737488355328 1 500000000000000 16750813 16777216 9 8388608 14812404212721096140215 2361183241434822606848 Ns396p1623 

noncomputable def Ns396p1625 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 184522973 16777216 9 8388608 10 1 0 1 16750813 16750813 16777216 9 

noncomputable def Ns396p1626 := @Ns396p1625 8388608 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 369045946 33554432 36 33554432 184522973 16777216 9 8388608 (Ns396p1614 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns396p1627 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 14812404212721096140215 2361183241434822606848 Ns396p1623 Ns396p579 52624231 8388608 227 33554432 (@Ns396p1624 Ns396p579 RS397to408.d47 (Ns396p1626 rfl rfl) rfl) 

noncomputable def Ns396p1628 := nat_lit 1887022237457777281728512 

noncomputable def Ns396p1629 := nat_lit 3423092621049639393174249157110888408699925345332399860635407010479963179465813016250018363669297702920814286553243100231709415491905191601 

noncomputable def Ns396p1630 := nat_lit 2319992103124567253811676115515760620746540262658963604774524825898071706723251558977004902667150293848917935106721009942782315790001 

noncomputable def Ns396p1631 := nat_lit 17094724719769205423660788932140562617551931330401598894287613614267009159482729632870901837372333769088347086944901025226187760361951133361 

noncomputable def Ns396p1632 := BSN.sin_dyadic_bound_f 107264795443 68719476736 4 3 33554432 12512208 Ns396p1629 Ns396p112 Ns396p1630 Ns396p1631 Ns396p115 Ns396p1630 33552791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107264795443) qz368 0 3 Ns396p1629 Ns396p112 Ns396p1630 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107264795443) qz369 0 3 Ns396p1631 Ns396p115 Ns396p1630 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1633 := @Ns396p1622 6250000 (Ns396p1627 rfl) (Enclosure.sfrac_false_div 52624231 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 52624231) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns396p1628) qz594) 226375608064910080 72057594037927936 Bool.false 33552791 33554432 0 1000000000000000 12500000 6250000 (BSN.sin_reduce_arg_pos_rat_q3 52624231 8388608 226375608064910080 72057594037927936 0 Ns396p1628 Ns396p173 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33552791 33554432 Ns396p1628 Ns396p173 107264795443 68719476736 12512208 12500000 (Ns396p1632 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns396p1634 := @Enclosure.Real.IsNear.inv_image qz250 33552791 33554432 90769027 13107200000000 16777920 16778153 16777216 (Ns396p1621 (Ns396p1633 rfl rfl) rfl) rfl 

noncomputable def Ns396p1635 := @Enclosure.Real.IsNear.recentre' qz251 Bool.false 15435986 16777216 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz349 qz346 qz540)

noncomputable def Ns396p1636 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6754031)) qz413) Bool.true 6754031 16777216 

noncomputable def Ns396p1637 := nat_lit 15947505240442917321881995525 

noncomputable def Ns396p1638 := nat_lit 610573098352218603187361027669993 

noncomputable def Ns396p1639 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns396p1637 Ns396p1063 Ns396p1638 

noncomputable def Ns396p1640 := nat_lit 30223145490365729367654400000000000000 

noncomputable abbrev qz254 := qz540

noncomputable def Ns396p1641 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 18034457760055 

noncomputable abbrev qz541 := (@HSub.hSub Real Real Real qz583 qz698 qz691)

noncomputable abbrev qz255 := qz541

noncomputable def Ns396p1642 := @Enclosure.Real.IsNear.subLit_tf qz255 qz29 442271715639 281474976710656 113127435 35184372088832 1 16 

noncomputable abbrev qz542 := qz698

noncomputable abbrev qz256 := qz542

noncomputable def Ns396p1643 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz242 280589736160969 281474976710656 75378699 35184372088832 16750813 16777216 9 8388608 

noncomputable def Ns396p1644 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 16750813 16777216 9 8388608 16750813 16777216 9 8388608 280589736160969 281474976710656 

noncomputable def Ns396p1645 := nat_lit 2080904735890965572090579521 

noncomputable def Ns396p1646 := nat_lit 1901475900342344102245054808064 

noncomputable def Ns396p1647 := nat_lit 28522138505135161533675822120960 

noncomputable def Ns396p1648 := BSN.cos_dyadic_bound_f 6754031 16777216 2 1 16777216 6250000 Ns396p1645 Ns396p1646 Ns396p1645 Ns396p1645 Ns396p1647 Ns396p1645 15435986 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 6754031) (BSN.cosEvenQ 16777216) 0 1 Ns396p1645 Ns396p1646 Ns396p1645 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 6754031) (BSN.cosOddQ 16777216) 0 1 Ns396p1645 Ns396p1647 Ns396p1645 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns396p1649 := @Ns396p1635 4277304432 209715200000000 7717993 8388608 267331527 13107200000000 (@Ns396p1636 679 33554432 Bool.false 15435986 16777216 1 6250000 (@Ns396p1639 Ns396p1640 6754031 16777216 679 33554432 (@Ns396p1641 281474976710656 113127435 35184372088832 Ns396p1637 Ns396p1063 Ns396p1638 Ns396p1640 RS397to408.d47 (@Ns396p1642 0 1 288551324160880 18034457760055 281474976710656 113127435 35184372088832 (@Ns396p1643 7420088103966081024 442271715639 281474976710656 113127435 35184372088832 (@Ns396p1644 75378699 35184372088832 (Ns396p1626 rfl rfl) (Ns396p1626 rfl rfl) rfl) (Ns396p1626 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6754031 16777216) (BSN.cos_neg_of_bound 6754031 16777216 Bool.false 15435986 16777216 1 6250000 (Ns396p1648 rfl rfl)) rfl rfl) 

noncomputable def Ns396p1650 := @Ns396p1612 15000199761173579499027 Ns396p848 (Ns396p1613 qz31 (@Enclosure.Real.IsNear.of_eq qz696 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 5058883 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz241 (BSN.t_div_two_pi_nonneg qz240 760048 1000 qz243)) Ns396p1617) rfl) (@Ns396p1618 281474976710656 5890245175010881 219902325555200000000 (BSN.correction_mk qz242 (BSN.cos_two_pi_p_ne_zero_mk qz240 760048 1000 10 qz243 rfl rfl (@BSN.floor_sqrt_eq_dec qz240 760048 1000 10 qz243 rfl rfl rfl))) (@Ns396p1619 33554432 7717993 8388608 267331527 13107200000000 258985536521489 281474976710656 5890245175010881 219902325555200000000 (@Ns396p1620 33554432 (Ns396p1634 rfl rfl rfl rfl rfl) rfl) (Ns396p1649 rfl) rfl)) 

noncomputable def Ns396p1651 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (hardyZApproximantRS₀ qz240) Bool.true 7251450955349397247091 4722366482869645213696 Ns396p1540 Ns396p848 (@Eq.refl Real (hardyZApproximantRS₀ qz240)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HMul.hMul Real Real Real qz5 qz692 (Zeta.RiemannSiegel.correction qz242))) Bool.true 7251450955349397247091 4722366482869645213696 Ns396p1540 Ns396p848 (BSN.hardyZApproximantRS₀_eq qz240 10 (@BSN.floor_sqrt_eq_dec qz240 760048 1000 10 qz243 rfl rfl rfl)) (@Ns396p1542 7251450955349397247091 4722366482869645213696 Ns396p1540 Ns396p848 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10)) Bool.true 168861147 134217728 145739 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (Ns396p1611 (Ns396p1610 rfl rfl rfl rfl) rfl rfl)) (Ns396p1650 rfl) rfl rfl)) 

theorem RS397to408.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz240) Bool.true 7251450955349397247091 4722366482869645213696 Ns396p1540 Ns396p848 := Ns396p1651 

noncomputable def RS397to408.d64 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz543 := (RS397to408.d3 qz580 qz595 (@Enclosure.dec_le_dec qz580 qz595 744291 1000 745607 1000 (@Eq.refl Real qz580) qz598 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz543)

noncomputable def Ns396p1652 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 24327274800353908456941 9444732965739290427392 Ns396p74 Ns396p75 

noncomputable abbrev qz544 := (@Enclosure.dec_le_dec qz580 qz595 744291 1000 745607 1000 (@Eq.refl Real qz580) qz598 rfl rfl rfl)

noncomputable abbrev qz258 := qz544

noncomputable def Ns396p1653 := @Enclosure.Real.IsNear.neg_val qz257 24327274800353908456941 9444732965739290427392 Ns396p74 Ns396p75 (Ns396p1652 (RS397to408.d4 qz4 qz33 qz258) RS397to408.d49) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz543)

noncomputable def Ns396p1654 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz33) Bool.false 2277186564842812596775 2361183241434822606848 990884079948299181502087 Ns396p202 

noncomputable def Ns396p1655 := @Enclosure.Real.IsNear.pos_val qz259 2277186564842812596775 2361183241434822606848 990884079948299181502087 Ns396p202 (Ns396p1654 (RS397to408.d50 qz4 qz33 qz258) RS397to408.d51) rfl 

noncomputable def Ns396p1656 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 744291 1000 744291 1000 

noncomputable def Ns396p1657 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 24327274800353908456941 9444732965739290427392 Ns396p74 

noncomputable def Ns396p1658 := @Ns396p1657 Ns396p75 280236381 5368709120 1213 5368709120 (Ns396p1652 (RS397to408.d4 qz4 qz33 qz258) RS397to408.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable def Ns396p1659 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz33 744291 1000 745607 1000 

noncomputable def Ns396p1660 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2277186564842812596775 2361183241434822606848 990884079948299181502087 

noncomputable def Ns396p1661 := @Ns396p1660 Ns396p202 280236381 5368709120 1213 5368709120 (Ns396p1654 (RS397to408.d50 qz4 qz33 qz258) RS397to408.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz543

noncomputable def Ns396p1662 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 744291 1000 qz9 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns396p1653 rfl rfl) (Ns396p1655 rfl rfl)) (Ns396p1656 qz9 qz9 rfl rfl rfl rfl (Ns396p1658 rfl)) (Ns396p1659 qz9 qz36 rfl rfl rfl rfl (Ns396p1661 rfl)) 

noncomputable abbrev qz545 := (RS397to408.d3 qz595 qz605 (@Enclosure.dec_le_dec qz595 qz605 745607 1000 746922 1000 qz598 qz608 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz545)

noncomputable def Ns396p1663 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz33) Bool.false 2277186564842812596775 2361183241434822606848 990884079948299181502087 Ns396p202 

noncomputable abbrev qz546 := (@Enclosure.dec_le_dec qz595 qz605 745607 1000 746922 1000 qz598 qz608 rfl rfl rfl)

noncomputable abbrev qz262 := qz546

noncomputable def Ns396p1664 := @Enclosure.Real.IsNear.pos_val qz261 2277186564842812596775 2361183241434822606848 990884079948299181502087 Ns396p202 (Ns396p1663 (RS397to408.d4 qz33 qz60 qz262) RS397to408.d51) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz545)

noncomputable def Ns396p1665 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz60) Bool.true 126379818469648423809 147573952589676412928 99231762624002801289553 Ns396p363 

noncomputable def Ns396p1666 := @Enclosure.Real.IsNear.neg_val qz263 126379818469648423809 147573952589676412928 99231762624002801289553 Ns396p363 (Ns396p1665 (RS397to408.d50 qz33 qz60 qz262) RS397to408.d53) rfl 

noncomputable def Ns396p1667 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz33 744291 1000 745607 1000 

noncomputable def Ns396p1668 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2277186564842812596775 2361183241434822606848 990884079948299181502087 

noncomputable def Ns396p1669 := @Ns396p1668 Ns396p202 280236381 5368709120 1213 5368709120 (Ns396p1663 (RS397to408.d4 qz33 qz60 qz262) RS397to408.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable def Ns396p1670 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz60 744291 1000 746922 1000 

noncomputable def Ns396p1671 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 126379818469648423809 147573952589676412928 99231762624002801289553 

noncomputable def Ns396p1672 := @Ns396p1671 Ns396p363 280236381 5368709120 1213 5368709120 (Ns396p1665 (RS397to408.d50 qz33 qz60 qz262) RS397to408.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz545

noncomputable def Ns396p1673 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz33 745607 1000 qz36 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns396p1664 rfl rfl) (Ns396p1666 rfl rfl)) (Ns396p1667 qz9 qz36 rfl rfl rfl rfl (Ns396p1669 rfl)) (Ns396p1670 qz9 qz63 rfl rfl rfl rfl (Ns396p1672 rfl)) 

noncomputable abbrev qz547 := (RS397to408.d3 qz605 qz613 (@Enclosure.dec_le_dec qz605 qz613 746922 1000 748073 1000 qz608 qz616 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz547)

noncomputable def Ns396p1674 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz60) Bool.true 126379818469648423809 147573952589676412928 99231762624002801289553 Ns396p363 

noncomputable abbrev qz548 := (@Enclosure.dec_le_dec qz605 qz613 746922 1000 748073 1000 qz608 qz616 rfl rfl rfl)

noncomputable abbrev qz266 := qz548

noncomputable def Ns396p1675 := @Enclosure.Real.IsNear.neg_val qz265 126379818469648423809 147573952589676412928 99231762624002801289553 Ns396p363 (Ns396p1674 (RS397to408.d4 qz60 qz78 qz266) RS397to408.d53) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz547)

noncomputable def Ns396p1676 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz78) Bool.false 1202879872460951783 4611686018427387904 496917242476535265166909 Ns396p485 

noncomputable def Ns396p1677 := @Enclosure.Real.IsNear.pos_val qz267 1202879872460951783 4611686018427387904 496917242476535265166909 Ns396p485 (Ns396p1676 (RS397to408.d50 qz60 qz78 qz266) RS397to408.d54) rfl 

noncomputable def Ns396p1678 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz60 744291 1000 746922 1000 

noncomputable def Ns396p1679 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 126379818469648423809 147573952589676412928 99231762624002801289553 

noncomputable def Ns396p1680 := @Ns396p1679 Ns396p363 280236381 5368709120 1213 5368709120 (Ns396p1674 (RS397to408.d4 qz60 qz78 qz266) RS397to408.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable def Ns396p1681 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz78 744291 1000 748073 1000 

noncomputable def Ns396p1682 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1202879872460951783 4611686018427387904 496917242476535265166909 

noncomputable def Ns396p1683 := @Ns396p1682 Ns396p485 280236381 5368709120 1213 5368709120 (Ns396p1676 (RS397to408.d50 qz60 qz78 qz266) RS397to408.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz547

noncomputable def Ns396p1684 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz60 746922 1000 qz63 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns396p1675 rfl rfl) (Ns396p1677 rfl rfl)) (Ns396p1678 qz9 qz63 rfl rfl rfl rfl (Ns396p1680 rfl)) (Ns396p1681 qz9 qz81 rfl rfl rfl rfl (Ns396p1683 rfl)) 

noncomputable abbrev qz549 := (RS397to408.d3 qz613 qz621 (@Enclosure.dec_le_dec qz613 qz621 748073 1000 749551 1000 qz616 qz624 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz549)

noncomputable def Ns396p1685 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz78) Bool.false 1202879872460951783 4611686018427387904 496917242476535265166909 Ns396p485 

noncomputable abbrev qz550 := (@Enclosure.dec_le_dec qz613 qz621 748073 1000 749551 1000 qz616 qz624 rfl rfl rfl)

noncomputable abbrev qz270 := qz550

noncomputable def Ns396p1686 := @Enclosure.Real.IsNear.pos_val qz269 1202879872460951783 4611686018427387904 496917242476535265166909 Ns396p485 (Ns396p1685 (RS397to408.d4 qz78 qz96 qz270) RS397to408.d54) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz549)

noncomputable def Ns396p1687 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz96) Bool.true 10210537300205546108265 2361183241434822606848 Ns396p611 Ns396p75 

noncomputable def Ns396p1688 := @Enclosure.Real.IsNear.neg_val qz271 10210537300205546108265 2361183241434822606848 Ns396p611 Ns396p75 (Ns396p1687 (RS397to408.d50 qz78 qz96 qz270) RS397to408.d55) rfl 

noncomputable def Ns396p1689 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz78 744291 1000 748073 1000 

noncomputable def Ns396p1690 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1202879872460951783 4611686018427387904 496917242476535265166909 

noncomputable def Ns396p1691 := @Ns396p1690 Ns396p485 280236381 5368709120 1213 5368709120 (Ns396p1685 (RS397to408.d4 qz78 qz96 qz270) RS397to408.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable def Ns396p1692 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz96 744291 1000 749551 1000 

noncomputable def Ns396p1693 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 10210537300205546108265 2361183241434822606848 Ns396p611 

noncomputable def Ns396p1694 := @Ns396p1693 Ns396p75 280236381 5368709120 1213 5368709120 (Ns396p1687 (RS397to408.d50 qz78 qz96 qz270) RS397to408.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz549

noncomputable def Ns396p1695 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz78 748073 1000 qz81 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns396p1686 rfl rfl) (Ns396p1688 rfl rfl)) (Ns396p1689 qz9 qz81 rfl rfl rfl rfl (Ns396p1691 rfl)) (Ns396p1692 qz9 qz99 rfl rfl rfl rfl (Ns396p1694 rfl)) 

noncomputable abbrev qz551 := (RS397to408.d3 qz621 qz629 (@Enclosure.dec_le_dec qz621 qz629 749551 1000 750865 1000 qz624 qz632 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns396p1696 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz96) Bool.true 10210537300205546108265 2361183241434822606848 Ns396p611 Ns396p75 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz621 qz629 749551 1000 750865 1000 qz624 qz632 rfl rfl rfl)

noncomputable abbrev qz274 := qz552

noncomputable def Ns396p1697 := @Enclosure.Real.IsNear.neg_val qz273 10210537300205546108265 2361183241434822606848 Ns396p611 Ns396p75 (Ns396p1696 (RS397to408.d4 qz96 qz114 qz274) RS397to408.d55) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns396p1698 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz114) Bool.false 38148903553740135201 295147905179352825856 99715307678161860853853 Ns396p363 

noncomputable def Ns396p1699 := @Enclosure.Real.IsNear.pos_val qz275 38148903553740135201 295147905179352825856 99715307678161860853853 Ns396p363 (Ns396p1698 (RS397to408.d50 qz96 qz114 qz274) RS397to408.d56) rfl 

noncomputable def Ns396p1700 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz96 744291 1000 749551 1000 

noncomputable def Ns396p1701 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 10210537300205546108265 2361183241434822606848 Ns396p611 

noncomputable def Ns396p1702 := @Ns396p1701 Ns396p75 280236381 5368709120 1213 5368709120 (Ns396p1696 (RS397to408.d4 qz96 qz114 qz274) RS397to408.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable def Ns396p1703 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz114 744291 1000 750865 1000 

noncomputable def Ns396p1704 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 38148903553740135201 295147905179352825856 99715307678161860853853 

noncomputable def Ns396p1705 := @Ns396p1704 Ns396p363 280236381 5368709120 1213 5368709120 (Ns396p1698 (RS397to408.d50 qz96 qz114 qz274) RS397to408.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz551

noncomputable def Ns396p1706 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz96 749551 1000 qz99 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns396p1697 rfl rfl) (Ns396p1699 rfl rfl)) (Ns396p1700 qz9 qz99 rfl rfl rfl rfl (Ns396p1702 rfl)) (Ns396p1703 qz9 qz117 rfl rfl rfl rfl (Ns396p1705 rfl)) 

noncomputable abbrev qz553 := (RS397to408.d3 qz629 qz637 (@Enclosure.dec_le_dec qz629 qz637 750865 1000 752179 1000 qz632 qz640 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns396p1707 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz114) Bool.false 38148903553740135201 295147905179352825856 99715307678161860853853 Ns396p363 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz629 qz637 750865 1000 752179 1000 qz632 qz640 rfl rfl rfl)

noncomputable abbrev qz278 := qz554

noncomputable def Ns396p1708 := @Enclosure.Real.IsNear.pos_val qz277 38148903553740135201 295147905179352825856 99715307678161860853853 Ns396p363 (Ns396p1707 (RS397to408.d4 qz114 qz132 qz278) RS397to408.d56) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns396p1709 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz132) Bool.true 18220223024135592339307 4722366482869645213696 Ns396p847 Ns396p848 

noncomputable def Ns396p1710 := @Enclosure.Real.IsNear.neg_val qz279 18220223024135592339307 4722366482869645213696 Ns396p847 Ns396p848 (Ns396p1709 (RS397to408.d50 qz114 qz132 qz278) RS397to408.d57) rfl 

noncomputable def Ns396p1711 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz114 744291 1000 750865 1000 

noncomputable def Ns396p1712 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 38148903553740135201 295147905179352825856 99715307678161860853853 

noncomputable def Ns396p1713 := @Ns396p1712 Ns396p363 280236381 5368709120 1213 5368709120 (Ns396p1707 (RS397to408.d4 qz114 qz132 qz278) RS397to408.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable def Ns396p1714 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz132 744291 1000 752179 1000 

noncomputable def Ns396p1715 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 18220223024135592339307 4722366482869645213696 Ns396p847 

noncomputable def Ns396p1716 := @Ns396p1715 Ns396p848 280236381 5368709120 1213 5368709120 (Ns396p1709 (RS397to408.d50 qz114 qz132 qz278) RS397to408.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz553

noncomputable def Ns396p1717 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz114 750865 1000 qz117 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns396p1708 rfl rfl) (Ns396p1710 rfl rfl)) (Ns396p1711 qz9 qz117 rfl rfl rfl rfl (Ns396p1713 rfl)) (Ns396p1714 qz9 qz135 rfl rfl rfl rfl (Ns396p1716 rfl)) 

noncomputable abbrev qz555 := (RS397to408.d3 qz637 qz645 (@Enclosure.dec_le_dec qz637 qz645 752179 1000 753491 1000 qz640 qz648 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns396p1718 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz132) Bool.true 18220223024135592339307 4722366482869645213696 Ns396p847 Ns396p848 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz637 qz645 752179 1000 753491 1000 qz640 qz648 rfl rfl rfl)

noncomputable abbrev qz282 := qz556

noncomputable def Ns396p1719 := @Enclosure.Real.IsNear.neg_val qz281 18220223024135592339307 4722366482869645213696 Ns396p847 Ns396p848 (Ns396p1718 (RS397to408.d4 qz132 qz150 qz282) RS397to408.d57) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns396p1720 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz150) Bool.false 14311148744205451848261 4722366482869645213696 20007976056761072652923 Ns396p959 

noncomputable def Ns396p1721 := @Enclosure.Real.IsNear.pos_val qz283 14311148744205451848261 4722366482869645213696 20007976056761072652923 Ns396p959 (Ns396p1720 (RS397to408.d50 qz132 qz150 qz282) RS397to408.d58) rfl 

noncomputable def Ns396p1722 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz132 744291 1000 752179 1000 

noncomputable def Ns396p1723 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 18220223024135592339307 4722366482869645213696 Ns396p847 

noncomputable def Ns396p1724 := @Ns396p1723 Ns396p848 280236381 5368709120 1213 5368709120 (Ns396p1718 (RS397to408.d4 qz132 qz150 qz282) RS397to408.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable def Ns396p1725 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz150 744291 1000 753491 1000 

noncomputable def Ns396p1726 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 14311148744205451848261 4722366482869645213696 20007976056761072652923 

noncomputable def Ns396p1727 := @Ns396p1726 Ns396p959 280236381 5368709120 1213 5368709120 (Ns396p1720 (RS397to408.d50 qz132 qz150 qz282) RS397to408.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz555

noncomputable def Ns396p1728 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz132 752179 1000 qz135 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns396p1719 rfl rfl) (Ns396p1721 rfl rfl)) (Ns396p1722 qz9 qz135 rfl rfl rfl rfl (Ns396p1724 rfl)) (Ns396p1725 qz9 qz153 rfl rfl rfl rfl (Ns396p1727 rfl)) 

noncomputable abbrev qz557 := (RS397to408.d3 qz645 qz653 (@Enclosure.dec_le_dec qz645 qz653 753491 1000 754804 1000 qz648 qz656 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns396p1729 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz150) Bool.false 14311148744205451848261 4722366482869645213696 20007976056761072652923 Ns396p959 

noncomputable abbrev qz558 := (@Enclosure.dec_le_dec qz645 qz653 753491 1000 754804 1000 qz648 qz656 rfl rfl rfl)

noncomputable abbrev qz286 := qz558

noncomputable def Ns396p1730 := @Enclosure.Real.IsNear.pos_val qz285 14311148744205451848261 4722366482869645213696 20007976056761072652923 Ns396p959 (Ns396p1729 (RS397to408.d4 qz150 qz168 qz286) RS397to408.d58) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns396p1731 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz168) Bool.true 663585970997839222715 295147905179352825856 Ns396p1078 Ns396p848 

noncomputable def Ns396p1732 := @Enclosure.Real.IsNear.neg_val qz287 663585970997839222715 295147905179352825856 Ns396p1078 Ns396p848 (Ns396p1731 (RS397to408.d50 qz150 qz168 qz286) RS397to408.d59) rfl 

noncomputable def Ns396p1733 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz150 744291 1000 753491 1000 

noncomputable def Ns396p1734 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 14311148744205451848261 4722366482869645213696 20007976056761072652923 

noncomputable def Ns396p1735 := @Ns396p1734 Ns396p959 280236381 5368709120 1213 5368709120 (Ns396p1729 (RS397to408.d4 qz150 qz168 qz286) RS397to408.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable def Ns396p1736 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz168 744291 1000 754804 1000 

noncomputable def Ns396p1737 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 663585970997839222715 295147905179352825856 Ns396p1078 

noncomputable def Ns396p1738 := @Ns396p1737 Ns396p848 280236381 5368709120 1213 5368709120 (Ns396p1731 (RS397to408.d50 qz150 qz168 qz286) RS397to408.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz557

noncomputable def Ns396p1739 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz150 753491 1000 qz153 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns396p1730 rfl rfl) (Ns396p1732 rfl rfl)) (Ns396p1733 qz9 qz153 rfl rfl rfl rfl (Ns396p1735 rfl)) (Ns396p1736 qz9 qz171 rfl rfl rfl rfl (Ns396p1738 rfl)) 

noncomputable abbrev qz699 := (@Enclosure.dec_le_dec qz744 qz748 754804 1000 756116 1000 (@Eq.refl Real qz744) (@Eq.refl Real qz748) rfl rfl rfl)

noncomputable abbrev qz559 := (RS397to408.d3 qz653 qz661 qz699)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns396p1740 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz168) Bool.true 663585970997839222715 295147905179352825856 Ns396p1078 Ns396p848 

noncomputable abbrev qz560 := qz699

noncomputable abbrev qz290 := qz560

noncomputable def Ns396p1741 := @Enclosure.Real.IsNear.neg_val qz289 663585970997839222715 295147905179352825856 Ns396p1078 Ns396p848 (Ns396p1740 (RS397to408.d4 qz168 qz186 qz290) RS397to408.d59) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns396p1742 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz186) Bool.false 205639444673984325737 295147905179352825856 31362117375631409123133 Ns396p1188 

noncomputable def Ns396p1743 := @Enclosure.Real.IsNear.pos_val qz291 205639444673984325737 295147905179352825856 31362117375631409123133 Ns396p1188 (Ns396p1742 (RS397to408.d50 qz168 qz186 qz290) RS397to408.d60) rfl 

noncomputable def Ns396p1744 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz168 744291 1000 754804 1000 

noncomputable def Ns396p1745 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 663585970997839222715 295147905179352825856 Ns396p1078 

noncomputable def Ns396p1746 := @Ns396p1745 Ns396p848 280236381 5368709120 1213 5368709120 (Ns396p1740 (RS397to408.d4 qz168 qz186 qz290) RS397to408.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable def Ns396p1747 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz186 744291 1000 756116 1000 

noncomputable def Ns396p1748 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 205639444673984325737 295147905179352825856 31362117375631409123133 

noncomputable def Ns396p1749 := @Ns396p1748 Ns396p1188 280236381 5368709120 1213 5368709120 (Ns396p1742 (RS397to408.d50 qz168 qz186 qz290) RS397to408.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz559

noncomputable def Ns396p1750 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz168 754804 1000 qz171 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns396p1741 rfl rfl) (Ns396p1743 rfl rfl)) (Ns396p1744 qz9 qz171 rfl rfl rfl rfl (Ns396p1746 rfl)) (Ns396p1747 qz9 qz189 rfl rfl rfl rfl (Ns396p1749 rfl)) 

noncomputable abbrev qz700 := (@Enclosure.dec_le_dec qz748 qz752 756116 1000 757427 1000 (@Eq.refl Real qz748) qz755 rfl rfl rfl)

noncomputable abbrev qz561 := (RS397to408.d3 qz661 qz669 qz700)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns396p1751 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz186) Bool.false 205639444673984325737 295147905179352825856 31362117375631409123133 Ns396p1188 

noncomputable abbrev qz562 := qz700

noncomputable abbrev qz294 := qz562

noncomputable def Ns396p1752 := @Enclosure.Real.IsNear.pos_val qz293 205639444673984325737 295147905179352825856 31362117375631409123133 Ns396p1188 (Ns396p1751 (RS397to408.d4 qz186 qz204 qz294) RS397to408.d60) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns396p1753 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz204) Bool.true 23198944676073910089421 18889465931478580854784 Ns396p1305 Ns396p1306 

noncomputable def Ns396p1754 := @Enclosure.Real.IsNear.neg_val qz295 23198944676073910089421 18889465931478580854784 Ns396p1305 Ns396p1306 (Ns396p1753 (RS397to408.d50 qz186 qz204 qz294) RS397to408.d61) rfl 

noncomputable def Ns396p1755 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz186 744291 1000 756116 1000 

noncomputable def Ns396p1756 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 205639444673984325737 295147905179352825856 31362117375631409123133 

noncomputable def Ns396p1757 := @Ns396p1756 Ns396p1188 280236381 5368709120 1213 5368709120 (Ns396p1751 (RS397to408.d4 qz186 qz204 qz294) RS397to408.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable def Ns396p1758 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz204 744291 1000 757427 1000 

noncomputable def Ns396p1759 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 23198944676073910089421 18889465931478580854784 Ns396p1305 

noncomputable def Ns396p1760 := @Ns396p1759 Ns396p1306 280236381 5368709120 1213 5368709120 (Ns396p1753 (RS397to408.d50 qz186 qz204 qz294) RS397to408.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz561

noncomputable def Ns396p1761 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz186 756116 1000 qz189 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns396p1752 rfl rfl) (Ns396p1754 rfl rfl)) (Ns396p1755 qz9 qz189 rfl rfl rfl rfl (Ns396p1757 rfl)) (Ns396p1758 qz9 qz209 rfl rfl rfl rfl (Ns396p1760 rfl)) 

noncomputable abbrev qz701 := (@Enclosure.dec_le_dec qz752 qz757 757427 1000 758738 1000 qz755 qz760 rfl rfl rfl)

noncomputable abbrev qz563 := (RS397to408.d3 qz669 qz679 qz701)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns396p1762 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz204) Bool.true 23198944676073910089421 18889465931478580854784 Ns396p1305 Ns396p1306 

noncomputable abbrev qz564 := qz701

noncomputable abbrev qz298 := qz564

noncomputable def Ns396p1763 := @Enclosure.Real.IsNear.neg_val qz297 23198944676073910089421 18889465931478580854784 Ns396p1305 Ns396p1306 (Ns396p1762 (RS397to408.d4 qz204 qz223 qz298) RS397to408.d61) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns396p1764 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz223) Bool.false 237011100892969447951 590295810358705651712 251759963807184059526163 Ns396p1423 

noncomputable def Ns396p1765 := @Enclosure.Real.IsNear.pos_val qz299 237011100892969447951 590295810358705651712 251759963807184059526163 Ns396p1423 (Ns396p1764 (RS397to408.d50 qz204 qz223 qz298) RS397to408.d62) rfl 

noncomputable def Ns396p1766 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz204 744291 1000 757427 1000 

noncomputable def Ns396p1767 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 23198944676073910089421 18889465931478580854784 Ns396p1305 

noncomputable def Ns396p1768 := @Ns396p1767 Ns396p1306 280236381 5368709120 1213 5368709120 (Ns396p1762 (RS397to408.d4 qz204 qz223 qz298) RS397to408.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable def Ns396p1769 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz223 744291 1000 758738 1000 

noncomputable def Ns396p1770 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 237011100892969447951 590295810358705651712 251759963807184059526163 

noncomputable def Ns396p1771 := @Ns396p1770 Ns396p1423 280236381 5368709120 1213 5368709120 (Ns396p1764 (RS397to408.d50 qz204 qz223 qz298) RS397to408.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz563

noncomputable def Ns396p1772 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz204 757427 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns396p1763 rfl rfl) (Ns396p1765 rfl rfl)) (Ns396p1766 qz9 qz209 rfl rfl rfl rfl (Ns396p1768 rfl)) (Ns396p1769 qz9 qz226 rfl rfl rfl rfl (Ns396p1771 rfl)) 

noncomputable abbrev qz767 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 758738 1000) (Enclosure.sfrac Bool.false 760048 1000) 758738 1000 760048 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 758738 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 760048 1000)) rfl rfl rfl)

noncomputable abbrev qz702 := qz767

noncomputable abbrev qz565 := (RS397to408.d3 qz679 qz689 qz702)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz565)

noncomputable def Ns396p1773 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz223) Bool.false 237011100892969447951 590295810358705651712 251759963807184059526163 Ns396p1423 

noncomputable abbrev qz566 := qz702

noncomputable abbrev qz302 := qz566

noncomputable def Ns396p1774 := @Enclosure.Real.IsNear.pos_val qz301 237011100892969447951 590295810358705651712 251759963807184059526163 Ns396p1423 (Ns396p1773 (RS397to408.d4 qz223 qz240 qz302) RS397to408.d62) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz565)

noncomputable def Ns396p1775 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz240) Bool.true 7251450955349397247091 4722366482869645213696 Ns396p1540 Ns396p848 

noncomputable def Ns396p1776 := @Enclosure.Real.IsNear.neg_val qz303 7251450955349397247091 4722366482869645213696 Ns396p1540 Ns396p848 (Ns396p1775 (RS397to408.d50 qz223 qz240 qz302) RS397to408.d63) rfl 

noncomputable def Ns396p1777 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz223 744291 1000 758738 1000 

noncomputable def Ns396p1778 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 237011100892969447951 590295810358705651712 251759963807184059526163 

noncomputable def Ns396p1779 := @Ns396p1778 Ns396p1423 280236381 5368709120 1213 5368709120 (Ns396p1773 (RS397to408.d4 qz223 qz240 qz302) RS397to408.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable def Ns396p1780 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz240 744291 1000 760048 1000 

noncomputable def Ns396p1781 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 7251450955349397247091 4722366482869645213696 Ns396p1540 

noncomputable def Ns396p1782 := @Ns396p1781 Ns396p848 280236381 5368709120 1213 5368709120 (Ns396p1775 (RS397to408.d50 qz223 qz240 qz302) RS397to408.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 280236381 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS397to408.d52) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz565

noncomputable def Ns396p1783 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz223 758738 1000 qz226 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns396p1774 rfl rfl) (Ns396p1776 rfl rfl)) (Ns396p1777 qz9 qz226 rfl rfl rfl rfl (Ns396p1779 rfl)) (Ns396p1780 qz9 qz243 rfl rfl rfl rfl (Ns396p1782 rfl)) 

noncomputable def Ns396p1784 := @List.cons RS397to408.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns396p1772)) (@List.cons RS397to408.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns396p1783)) (@List.nil RS397to408.d0)) 

noncomputable def Ns396p1785 := @List.cons RS397to408.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns396p1750)) (@List.cons RS397to408.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns396p1761)) Ns396p1784) 

noncomputable def Ns396p1786 := @List.cons RS397to408.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns396p1728)) (@List.cons RS397to408.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns396p1739)) Ns396p1785) 

noncomputable def Ns396p1787 := @List.cons RS397to408.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns396p1706)) (@List.cons RS397to408.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns396p1717)) Ns396p1786) 

noncomputable def Ns396p1788 := @List.cons RS397to408.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns396p1684)) (@List.cons RS397to408.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns396p1695)) Ns396p1787) 

noncomputable def Ns396p1789 := @List.cons RS397to408.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns396p1662)) (@List.cons RS397to408.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns396p1673)) Ns396p1788) 

noncomputable abbrev qz567 := (RS397to408.d2 qz653 qz661 qz699)

noncomputable abbrev qz703 := (RS397to408.d2 qz752 qz757 (@Enclosure.dec_le_dec qz752 qz757 757427 1000 758738 1000 qz755 qz760 rfl rfl rfl))

noncomputable abbrev qz704 := (@List.cons RS397to408.d1 (RS397to408.d2 qz757 qz762 qz767) (@List.nil RS397to408.d1))

noncomputable abbrev qz568 := (@List.cons RS397to408.d1 (RS397to408.d2 qz661 qz669 qz700) (@List.cons RS397to408.d1 qz703 qz704))

noncomputable abbrev qz305 := (@List.cons RS397to408.d1 (RS397to408.d2 qz471 qz483 qz558) (@List.cons RS397to408.d1 qz567 qz568))

noncomputable def Ns396p1790 := @List.cons RS397to408.d1 (RS397to408.d2 qz114 qz132 qz278) (@List.cons RS397to408.d1 (RS397to408.d2 qz132 qz150 qz282) qz305) 

noncomputable abbrev qz306 := (RS397to408.d2 qz432 qz445 qz552)

noncomputable def Ns396p1791 := @List.IsChain.cons_cons RS397to408.d1 RS397to408.d64 qz306 (RS397to408.d2 qz114 qz132 qz278) (@List.cons RS397to408.d1 (RS397to408.d2 qz132 qz150 qz282) qz305) 

noncomputable def Ns396p1792 := @List.IsChain.cons_cons RS397to408.d1 RS397to408.d64 (RS397to408.d2 qz114 qz132 qz278) (RS397to408.d2 qz132 qz150 qz282) qz305 (@Enclosure.dec_le_dec qz132 qz132 752179 1000 752179 1000 qz135 qz135 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS397to408.d2 qz471 qz483 qz558)

noncomputable abbrev qz308 := qz567

noncomputable abbrev qz309 := qz568

noncomputable abbrev qz569 := (RS397to408.d2 qz661 qz669 qz700)

noncomputable abbrev qz310 := qz569

noncomputable abbrev qz570 := (@List.cons RS397to408.d1 qz703 qz704)

noncomputable abbrev qz311 := qz570

noncomputable abbrev qz571 := qz703

noncomputable abbrev qz312 := qz571

noncomputable abbrev qz572 := qz704

noncomputable abbrev qz313 := qz572

noncomputable abbrev qz705 := (RS397to408.d2 qz757 qz762 qz767)

noncomputable abbrev qz573 := qz705

noncomputable abbrev qz314 := qz573

noncomputable def Ns396p1793 := @List.IsChain.cons_cons RS397to408.d1 RS397to408.d64 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz168 qz168 754804 1000 754804 1000 qz171 qz171 rfl rfl rfl) (@List.IsChain.cons_cons RS397to408.d1 RS397to408.d64 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz186 qz186 756116 1000 756116 1000 qz189 qz189 rfl rfl rfl) (@List.IsChain.cons_cons RS397to408.d1 RS397to408.d64 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz204 qz204 757427 1000 757427 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS397to408.d1 RS397to408.d64 qz312 qz314 (@List.nil RS397to408.d1) (@Enclosure.dec_le_dec qz223 qz223 758738 1000 758738 1000 qz226 qz226 rfl rfl rfl) (@List.IsChain.singleton RS397to408.d1 RS397to408.d64 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS397to408.d1 qz567 qz568)

noncomputable def Ns396p1794 := @List.IsChain.cons_cons RS397to408.d1 RS397to408.d64 (RS397to408.d2 qz132 qz150 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz150 qz150 753491 1000 753491 1000 qz153 qz153 rfl rfl rfl) Ns396p1793 

noncomputable def Ns396p1795 := @List.IsChain.cons_cons RS397to408.d1 RS397to408.d64 (RS397to408.d2 qz4 qz33 qz258) (RS397to408.d2 qz33 qz60 qz262) (@List.cons RS397to408.d1 (RS397to408.d2 qz60 qz78 qz266) (@List.cons RS397to408.d1 (RS397to408.d2 qz78 qz96 qz270) (@List.cons RS397to408.d1 qz306 Ns396p1790))) (@Enclosure.dec_le_dec qz33 qz33 745607 1000 745607 1000 qz36 qz36 rfl rfl rfl) (@List.IsChain.cons_cons RS397to408.d1 RS397to408.d64 (RS397to408.d2 qz33 qz60 qz262) (RS397to408.d2 qz60 qz78 qz266) (@List.cons RS397to408.d1 (RS397to408.d2 qz78 qz96 qz270) (@List.cons RS397to408.d1 qz306 Ns396p1790)) (@Enclosure.dec_le_dec qz60 qz60 746922 1000 746922 1000 qz63 qz63 rfl rfl rfl) (@List.IsChain.cons_cons RS397to408.d1 RS397to408.d64 (RS397to408.d2 qz60 qz78 qz266) (RS397to408.d2 qz78 qz96 qz270) (@List.cons RS397to408.d1 qz306 Ns396p1790) (@Enclosure.dec_le_dec qz78 qz78 748073 1000 748073 1000 qz81 qz81 rfl rfl rfl) (@List.IsChain.cons_cons RS397to408.d1 RS397to408.d64 (RS397to408.d2 qz78 qz96 qz270) qz306 Ns396p1790 (@Enclosure.dec_le_dec qz96 qz96 749551 1000 749551 1000 qz99 qz99 rfl rfl rfl) (Ns396p1791 (@Enclosure.dec_le_dec qz114 qz114 750865 1000 750865 1000 qz117 qz117 rfl rfl rfl) (Ns396p1792 Ns396p1794))))) 

noncomputable abbrev qz574 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz575 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns396p1789 Ns396p1795)

noncomputable abbrev qz576 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns396p1789 Ns396p1795))

theorem RS397to408.d65 : Zeta.Certificates.BatchSpec 12 744291 1000 760048 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz240)))) qz575 (@And.intro (@Eq Nat (@List.length qz574 qz576) 12) (And (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 qz576)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 qz576)) (@Option.some Real qz240))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 qz576)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 qz576)) (@Option.some Real qz240)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz240))))

theorem solution : Zeta.Certificates.BatchSpec 12 744291 1000 760048 1000 := RS397to408.d65
#print axioms solution
#check solution
