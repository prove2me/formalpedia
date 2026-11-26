-- Prove2me | solution 1 for RHHeight1000.rs_main_0433_0438
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:42:33.801773+00:00
-- url     : https://prove2.me/submissions/08c82cdc-8f79-4366-b290-dcfb54ba055f

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

noncomputable def RS433to438.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS433to438.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS433to438.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS433to438.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS433to438.d2 a b h 

theorem RS433to438.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS433to438.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS433to438.d3 a b h)) 

noncomputable def Ns432p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns432p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns432p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns432p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns432p0 Ns432p1 Ns432p2 Ns432p1 307286088 268435456 1 108160000 307286088 268435456 1 108160000 153643044 134217728 2 134217728 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns432p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns432p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns432p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns432p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns432p8 := nat_lit 6573389678388862351155759458724141871788046104702795740939545775355827438482086890337971184306503456724674701876007739166027855002689342487126242201873902293161938510715598861337724155978462934346539722102807352693564004597780440630880721700532830491857281958381906437104026277614553345439647264822859384496062743250358046048880947907642984145065307980413206151384068885350206914057384338280179177725692904928360597982006748935836093248417685721122261418062303135764477585928239149568275027355236134745000697766005167655784166499502223346815249842007858448160935771607172549259242715110048115445292136446613946552506617916138661398090061483392335970316672263498462800198746102072055363920390651513279180731193678641632192805423820381724597815072905552156968003637925334143020171520625 

noncomputable def Ns432p9 := nat_lit 702614123509571190207434367497643053726389003684617183996726348470791223755418688598787599501240412886827946200799073391711533512528899996899108221816773619593298708861540359234024488137706935294538610329535191474811214152768697527793266408685885408431698677504366547635987768499962038530066773279961750661013789994039311989768445302208965109624014234440840481147386361324656837522786906307734587964680180646868573806366973424595907336814393861048013934514934272026683624090151873353554279683010347128413433843775162422864773798490322287367830744467164676975854073090397461536167654230134598982106570951920409048997311342333559851528447946435833392322432321465286801524775001800171249769824525762984779161997185015423416919065587459911326773695449510414365759468097615398764501522575 

noncomputable def Ns432p10 := nat_lit 541392566138474909591412279139378993255101875047003589935782329109463644892392322173295519240510467068363239080443023466297029982601757003829684821059136286585994161974307047499333049696728682047261006046816072264069316416942594393775486731411634963656291648112663555457379375292741727868294229136381639619442405391741167595634732196900940186574903289828257139713673376723681752760045249773972946001592268830432998579610986951410273979009689762628244990479410235165324966379611071762421902787196495466840333515349387051622842182127210560393625584510287605139387730811840242457253978115925211125629993337408355023684205061830608267784338105681114876710224147942516826039256450164994945245879666660679160980454641866547806615379410050641833332584350523565507268843323231339375 

noncomputable def Ns432p11 := BSN.log_dyadic_bound Ns432p6 Ns432p7 16 15 Ns432p8 268435456 108160000 Ns432p9 Ns432p10 307286088 Ns432p4 Ns432p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns432p6) (BSN.artanhQ Ns432p7) 0 15 Ns432p9 Ns432p8 Ns432p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns432p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns432p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns432p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns432p15 := nat_lit 6573389678388957581038003304946500209472262679236338533996718496177406624059139082449994147026037314666926693076053053862592074936423388863596813530408382584499373597031431853921413941298322255656576695489433951602693567143885654771592106690789036275646003378131729522606930818530515414843848039000889531334935427389830473690579523667466182538201372727149023132371319359578146651783732835416323469915494090659780509855937937675396353734377829186029766969614606089327824892671842834136516654569045504808111725705550748907924941183733134599012581542910476929082687043869700761244349471219210833189555347464155979117619898077496880661665775336657207488512148128426326823595335945176245554694022845325705851563290369414226074229552025260849280553835909109839168582914725334143020171520625 

noncomputable def Ns432p16 := nat_lit 702614123509582134195699383225799303120857312948289364169564431944606347230839067212220070086773571232938822231607515388838247088164426860334641427891924556959013106220289292017417932077264689683982462259236603120411894481357554273197237433243865910367073588753830073256225145709268648257922640132615276470163987114280905050307903018021985933333474523803420109333064989110261463867307642914581311357336787925252212965840242792007601256472655504246146516404729632839909377990937267835233434162343951883521915890115762575574377037535717851480622294463860980162526686236248764915916362237196611189536095144270945605478817014333998082847306947436470576941659846222535334992451365706225994338058508887942119777908276510373758951874822816373072605980596581754554466975502415398764501522575 

noncomputable def Ns432p17 := nat_lit 541392566138490077533790984620311058177654278555980714203107761719673916425133183846751239616284470803704371181920004286935467360846628369375164068764590875438310007353955324186636582299553928814156491749519256774653872128089233575343481607925575468185460509172779152955629338248076232826253005811067688706928164570779608774451502836676056177667078421728722179008027603013170304530594440809888606240685402729798990208830923560422594844623819537735750113690675240496626214395332044296593456069970973486809806367897564108502902289348063943342100923856630472249952347312756547637419241376870243223562839253667975765230153074010838184467350558565952691487980795548332122966513692688198426849374346091985539852378055886379210372820263137502377721028428076000707268843323231339375 

noncomputable def Ns432p18 := BSN.log_dyadic_bound Ns432p13 Ns432p14 16 15 Ns432p15 268435456 108160000 Ns432p16 Ns432p17 307286088 Ns432p12 Ns432p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns432p13) (BSN.artanhQ Ns432p14) 0 15 Ns432p16 Ns432p15 Ns432p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns432p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 153643044 134217728 2 134217728 38410761 33554432 1 67108864 (Ns432p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns432p0 Ns432p1 307286088 268435456 1 108160000 Bool.false (BSN.logfrac_isNear Ns432p4 Ns432p5 1 Ns432p0 Ns432p1 307286088 268435456 108160000 rfl rfl rfl (Ns432p11 rfl))) (BSN.isNear_log_sfrac Ns432p2 Ns432p1 307286088 268435456 1 108160000 Bool.false (BSN.logfrac_isNear Ns432p12 Ns432p5 1 Ns432p2 Ns432p1 307286088 268435456 108160000 rfl rfl rfl (Ns432p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS433to438.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 67108864 := Ns432p19 

noncomputable def Ns432p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 16777216 6760000 385100712855 135135 11629079 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz449 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz287 := qz449

noncomputable abbrev qz0 := qz287

theorem RS433to438.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 11629079 16777216 1 6760000 := BSN.isNear_log_sfrac 2 1 11629079 16777216 1 6760000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 11629079 16777216 6760000 rfl rfl rfl (Ns432p20 rfl)) 

theorem RS433to438.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 186065264 268435456 40 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 11629079 16777216 1 6760000 186065264 268435456 40 268435456 RS433to438.d6 rfl 

noncomputable abbrev qz288 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz1 := qz288

noncomputable abbrev qz289 := (@Nat.cast Real Real.instNatCast 2)

noncomputable def Ns432p21 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz289) 47453133 33554432 1 33554432 11863282 11863284 16777216 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz289) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz289 qz1)) Bool.false 47453133 33554432 1 33554432 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz289 qz1)) Bool.false 47453133 33554432 1 33554432 47453133 33554432 1 33554432 (BSN.sqrt_enclosure 2 1 23726566 23726567 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz2 := (@Inv.inv Real Real.instInv (Real.sqrt qz289))

theorem RS433to438.d8 : Enclosure.Real.IsNear qz2 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz2 Bool.false 23726566 33554432 2 33554432 11863283 16777216 1 16777216 (Ns432p21 rfl rfl) rfl 

theorem RS433to438.d9 : Enclosure.Real.IsNear qz2 Bool.false 189812528 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz2 Bool.false 11863283 16777216 1 16777216 189812528 268435456 16 268435456 RS433to438.d8 rfl 

noncomputable def Ns432p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 16777216 6760000 13079757671720842725 316234143225 18431655 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS433to438.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 6760000 := BSN.isNear_log_sfrac 3 1 18431655 16777216 1 6760000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 18431655 16777216 6760000 rfl rfl rfl (Ns432p22 rfl)) 

theorem RS433to438.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 294906480 268435456 40 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 6760000 294906480 268435456 40 268435456 RS433to438.d10 rfl 

noncomputable abbrev qz290 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns432p23 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz290) 58117981 33554432 1 33554432 9686330 9686331 16777216 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz290) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz290 qz1)) Bool.false 58117981 33554432 1 33554432 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz290 qz1)) Bool.false 58117981 33554432 1 33554432 58117981 33554432 1 33554432 (BSN.sqrt_enclosure 3 1 29058990 29058991 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz3 := (@Inv.inv Real Real.instInv (Real.sqrt qz290))

theorem RS433to438.d12 : Enclosure.Real.IsNear qz3 Bool.false 19372661 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 19372661 33554432 1 33554432 19372661 33554432 1 33554432 (Ns432p23 rfl rfl) rfl 

theorem RS433to438.d13 : Enclosure.Real.IsNear qz3 Bool.false 154981288 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 19372661 33554432 1 33554432 154981288 268435456 8 268435456 RS433to438.d12 rfl 

noncomputable def Ns432p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns432p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns432p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns432p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns432p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns432p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns432p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns432p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns432p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns432p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns432p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns432p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns432p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns432p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns432p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns432p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns432p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns432p25 Ns432p26 Ns432p27 Ns432p28 200200021673987500790625 Ns432p29 Ns432p30 Ns432p31 Ns432p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns432p32 Ns432p33 151412625 Ns432p34 Ns432p35 1322214852783825 Ns432p27 Ns432p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns432p32 Ns432p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns432p34 Ns432p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns432p36 Ns432p37 1267389585 Ns432p38 Ns432p39 1927077560082675 Ns432p29 Ns432p30 Ns432p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns432p36 Ns432p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns432p38 Ns432p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz4 := (@Nat.cast Real Real.instNatCast 5)

theorem RS433to438.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz1 qz4)) Bool.false Ns432p24 Ns432p25 1 Ns432p26 := Ns432p40 rfl rfl rfl 

noncomputable def Ns432p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns432p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns432p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns432p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns432p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns432p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns432p25 Ns432p26 Ns432p42 Ns432p43 9945 Ns432p44 Ns432p45 65835 Ns432p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns432p42 Ns432p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns432p44 Ns432p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS433to438.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz1 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns432p41 Ns432p25 1 Ns432p26 := Ns432p46 rfl 

noncomputable def Ns432p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns432p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS433to438.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns432p47 Ns432p25 1 Ns432p48 := BSN.pi_combine Ns432p24 Ns432p41 Ns432p25 Ns432p26 Ns432p48 Ns432p47 rfl rfl rfl rfl RS433to438.d14 RS433to438.d15 

theorem RS433to438.d17 : Enclosure.Real.IsNear Real.pi Bool.false 14148475504056880 4503599627370496 1 4503599627370496 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns432p47 Ns432p25 1 Ns432p48 14148475504056880 4503599627370496 1 4503599627370496 RS433to438.d16 rfl 

noncomputable def Ns432p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns432p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns432p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns432p52 := BSN.log_dyadic_bound 3 5 17 16 Ns432p49 16777216 6760000 Ns432p50 Ns432p51 23258159 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns432p50 Ns432p49 Ns432p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS433to438.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 6760000 := BSN.isNear_log_sfrac 4 1 23258159 16777216 1 6760000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 23258159 16777216 6760000 rfl rfl rfl (Ns432p52 rfl)) 

theorem RS433to438.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 372130544 268435456 40 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 6760000 372130544 268435456 40 268435456 RS433to438.d18 rfl 

noncomputable abbrev qz291 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns432p53 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz291) 67108865 33554432 1 33554432 8388607 8388608 16777216 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz291) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz291 qz1)) Bool.false 67108865 33554432 1 33554432 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz291 qz1)) Bool.false 67108865 33554432 1 33554432 67108865 33554432 1 33554432 (BSN.sqrt_enclosure 4 1 33554432 33554433 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz5 := (@Inv.inv Real Real.instInv (Real.sqrt qz291))

theorem RS433to438.d20 : Enclosure.Real.IsNear qz5 Bool.false 16777215 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz5 Bool.false 16777215 33554432 1 33554432 16777215 33554432 1 33554432 (Ns432p53 rfl rfl) rfl 

theorem RS433to438.d21 : Enclosure.Real.IsNear qz5 Bool.false 134217720 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz5 Bool.false 16777215 33554432 1 33554432 134217720 268435456 8 268435456 RS433to438.d20 rfl 

noncomputable def Ns432p54 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns432p55 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns432p56 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns432p57 := nat_lit 885951608314392539099884620 

noncomputable def Ns432p58 := nat_lit 1286943652057122751813246125 

noncomputable def Ns432p59 := BSN.log_dyadic_bound 2 3 22 21 Ns432p54 16777216 6760000 Ns432p55 Ns432p56 27001887 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns432p57 Ns432p58 84004523356416638976000 Ns432p55 Ns432p54 Ns432p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns432p57 Ns432p58 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS433to438.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 6760000 := BSN.isNear_log_sfrac 5 1 27001887 16777216 1 6760000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 27001887 16777216 6760000 rfl rfl rfl (Ns432p59 rfl rfl)) 

theorem RS433to438.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 432030192 268435456 40 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 6760000 432030192 268435456 40 268435456 RS433to438.d22 rfl 

noncomputable def Ns432p60 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz4) 75029991 33554432 1 33554432 7502998 7503000 16777216 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz4) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz4 qz1)) Bool.false 75029991 33554432 1 33554432 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz4 qz1)) Bool.false 75029991 33554432 1 33554432 75029991 33554432 1 33554432 (BSN.sqrt_enclosure 5 1 37514995 37514996 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz6 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS433to438.d24 : Enclosure.Real.IsNear qz6 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz6 Bool.false 15005998 33554432 2 33554432 7502999 16777216 1 16777216 (Ns432p60 rfl rfl) rfl 

theorem RS433to438.d25 : Enclosure.Real.IsNear qz6 Bool.false 120047984 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz6 Bool.false 7502999 16777216 1 16777216 120047984 268435456 16 268435456 RS433to438.d24 rfl 

noncomputable def Ns432p61 := BSN.log_dyadic_bound 2 10 6 5 103950000000000 16777216 6760000 1420244935680 967680 6802575 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 2) (BSN.artanhQ 10) 0 5 1420244935680 103950000000000 967680 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz7 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz288)

theorem RS433to438.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 12500000169 84500000000000000 := BSN.isNear_log_sfrac 6 1 4034683545132279 2251799813685248 12500000169 84500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz7) Bool.false 1083052117253279893684224 604462909807314587353088 1000000013520000 6760000000000000000000 4034683545132279 2251799813685248 12500000169 84500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 6802575 16777216 24973259072661432 36028797018963968 6760000 1000000000000000 rfl rfl rfl rfl (Ns432p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS433to438.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 480971758 268435456 41 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 12500000169 84500000000000000 480971758 268435456 41 268435456 RS433to438.d26 rfl 

noncomputable abbrev qz8 := (@Nat.cast Real Real.instNatCast 6)

noncomputable def Ns432p62 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz8) 82191237 33554432 1 33554432 6849269 6849270 16777216 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz8) (Real.sqrt qz7) Bool.false 82191237 33554432 1 33554432 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz7) Bool.false 82191237 33554432 1 33554432 82191237 33554432 1 33554432 (BSN.sqrt_enclosure 6 1 41095618 41095619 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz9 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS433to438.d28 : Enclosure.Real.IsNear qz9 Bool.false 13698539 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz9 Bool.false 13698539 33554432 1 33554432 13698539 33554432 1 33554432 (Ns432p62 rfl rfl) rfl 

theorem RS433to438.d29 : Enclosure.Real.IsNear qz9 Bool.false 109588312 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz9 Bool.false 13698539 33554432 1 33554432 109588312 268435456 8 268435456 RS433to438.d28 rfl 

noncomputable def Ns432p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 16777216 6760000 11010900719820672 5524329195 9388794 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz10 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz288)

theorem RS433to438.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 12500000169 84500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 12500000169 84500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz10) Bool.false 1176230476650867868041216 604462909807314587353088 1000000013520000 6760000000000000000000 4381799983422711 2251799813685248 12500000169 84500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 9388794 16777216 24973259072661432 36028797018963968 6760000 1000000000000000 rfl rfl rfl rfl (Ns432p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS433to438.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 522351262 268435456 41 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 12500000169 84500000000000000 522351262 268435456 41 268435456 RS433to438.d30 rfl 

noncomputable abbrev qz11 := (@Nat.cast Real Real.instNatCast 7)

noncomputable def Ns432p64 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz11) 88776683 33554432 1 33554432 6341191 6341192 16777216 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz11) (Real.sqrt qz10) Bool.false 88776683 33554432 1 33554432 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz10) Bool.false 88776683 33554432 1 33554432 88776683 33554432 1 33554432 (BSN.sqrt_enclosure 7 1 44388341 44388342 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz12 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS433to438.d32 : Enclosure.Real.IsNear qz12 Bool.false 12682383 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz12 Bool.false 12682383 33554432 1 33554432 12682383 33554432 1 33554432 (Ns432p64 rfl rfl) rfl 

theorem RS433to438.d33 : Enclosure.Real.IsNear qz12 Bool.false 101459064 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz12 Bool.false 12682383 33554432 1 33554432 101459064 268435456 8 268435456 RS433to438.d32 rfl 

noncomputable def Ns432p65 := nat_lit 1256945285058001618599936 

noncomputable def Ns432p66 := BSN.log_dyadic_bound 0 16 1 0 1 16777216 6760000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz13 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz288)

theorem RS433to438.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 25000000507 169000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 25000000507 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz13) Bool.false Ns432p65 604462909807314587353088 1000000020280000 6760000000000000000000 9364972152248037 4503599627370496 25000000507 169000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 16777216 24973259072661432 36028797018963968 6760000 1000000000000000 rfl rfl rfl rfl (Ns432p66 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS433to438.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 558195838 268435456 41 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 25000000507 169000000000000000 558195838 268435456 41 268435456 RS433to438.d34 rfl 

noncomputable abbrev qz14 := (@Nat.cast Real Real.instNatCast 8)

noncomputable def Ns432p67 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz14) 94906265 33554432 1 33554432 5931641 5931642 16777216 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz14) (Real.sqrt qz13) Bool.false 94906265 33554432 1 33554432 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz13) Bool.false 94906265 33554432 1 33554432 94906265 33554432 1 33554432 (BSN.sqrt_enclosure 8 1 47453132 47453133 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz15 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS433to438.d36 : Enclosure.Real.IsNear qz15 Bool.false 11863283 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz15 Bool.false 11863283 33554432 1 33554432 11863283 33554432 1 33554432 (Ns432p67 rfl rfl) rfl 

theorem RS433to438.d37 : Enclosure.Real.IsNear qz15 Bool.false 94906264 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz15 Bool.false 11863283 33554432 1 33554432 94906264 268435456 8 268435456 RS433to438.d36 rfl 

noncomputable def Ns432p68 := nat_lit 1328140746012062765809664 

noncomputable def Ns432p69 := BSN.log_dyadic_bound 1 17 3 2 1252815 16777216 6760000 1448 3 1976071 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz16 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz288)

theorem RS433to438.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 25000000507 169000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 25000000507 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz16) Bool.false Ns432p68 604462909807314587353088 1000000020280000 6760000000000000000000 9895419672221413 4503599627370496 25000000507 169000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 1976071 16777216 24973259072661432 36028797018963968 6760000 1000000000000000 rfl rfl rfl rfl (Ns432p69 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS433to438.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 589812974 268435456 41 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 25000000507 169000000000000000 589812974 268435456 41 268435456 RS433to438.d38 rfl 

noncomputable abbrev qz17 := (@Nat.cast Real Real.instNatCast 9)

noncomputable def Ns432p70 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz17) 100663297 33554432 1 33554432 5592405 5592406 16777216 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz17) (Real.sqrt qz16) Bool.false 100663297 33554432 1 33554432 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz16) Bool.false 100663297 33554432 1 33554432 100663297 33554432 1 33554432 (BSN.sqrt_enclosure 9 1 50331648 50331649 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz18 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS433to438.d40 : Enclosure.Real.IsNear qz18 Bool.false 11184811 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz18 Bool.false 11184811 33554432 1 33554432 11184811 33554432 1 33554432 (Ns432p70 rfl rfl) rfl 

theorem RS433to438.d41 : Enclosure.Real.IsNear qz18 Bool.false 89478488 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz18 Bool.false 11184811 33554432 1 33554432 89478488 268435456 8 268435456 RS433to438.d40 rfl 

noncomputable def Ns432p71 := nat_lit 1391827265235416537628672 

noncomputable def Ns432p72 := BSN.log_dyadic_bound 2 18 4 3 3571283520 16777216 6760000 14806464 960 3743727 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz19 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz288)

theorem RS433to438.d42 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921216632549 4503599627370496 25000000507 169000000000000000 := BSN.isNear_log_sfrac 10 1 10369921216632549 4503599627370496 25000000507 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz19) Bool.false Ns432p71 604462909807314587353088 1000000020280000 6760000000000000000000 10369921216632549 4503599627370496 25000000507 169000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 3743727 16777216 24973259072661432 36028797018963968 6760000 1000000000000000 rfl rfl rfl rfl (Ns432p72 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS433to438.d43 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 618095470 268435456 41 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921216632549 4503599627370496 25000000507 169000000000000000 618095470 268435456 41 268435456 RS433to438.d42 rfl 

noncomputable abbrev qz20 := (@Nat.cast Real Real.instNatCast 10)

noncomputable def Ns432p73 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz20) 106108431 33554432 1 33554432 5305421 5305422 16777216 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz20) (Real.sqrt qz19) Bool.false 106108431 33554432 1 33554432 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz19) Bool.false 106108431 33554432 1 33554432 106108431 33554432 1 33554432 (BSN.sqrt_enclosure 10 1 53054215 53054216 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz21 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS433to438.d44 : Enclosure.Real.IsNear qz21 Bool.false 10610843 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz21 Bool.false 10610843 33554432 1 33554432 10610843 33554432 1 33554432 (Ns432p73 rfl rfl) rfl 

theorem RS433to438.d45 : Enclosure.Real.IsNear qz21 Bool.false 84886744 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz21 Bool.false 10610843 33554432 1 33554432 84886744 268435456 8 268435456 RS433to438.d44 rfl 

noncomputable def Ns432p74 := nat_lit 1449438752820620681019392 

noncomputable def Ns432p75 := BSN.log_dyadic_bound 3 19 5 4 16049467073745 16777216 6760000 135406373544 688905 5342767 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 19) 0 4 135406373544 16049467073745 688905 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz523 := (Enclosure.sfrac Bool.false 11 1)

noncomputable abbrev qz450 := qz523

noncomputable abbrev qz292 := qz450

noncomputable abbrev qz22 := qz292

noncomputable abbrev qz23 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11) qz288)

theorem RS433to438.d46 : Enclosure.Real.IsNear (Real.log qz22) Bool.false 10799160248194789 4503599627370496 25000000507 169000000000000000 := BSN.isNear_log_sfrac 11 1 10799160248194789 4503599627370496 25000000507 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz23) Bool.false Ns432p74 604462909807314587353088 1000000020280000 6760000000000000000000 10799160248194789 4503599627370496 25000000507 169000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 5342767 16777216 24973259072661432 36028797018963968 6760000 1000000000000000 rfl rfl rfl rfl (Ns432p75 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS433to438.d47 : Enclosure.Real.IsNear (Real.log qz22) Bool.false 643680110 268435456 41 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz22) Bool.false 10799160248194789 4503599627370496 25000000507 169000000000000000 643680110 268435456 41 268435456 RS433to438.d46 rfl 

noncomputable abbrev qz24 := (@Nat.cast Real Real.instNatCast 11)

noncomputable def Ns432p76 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz24) 111287461 33554432 1 33554432 5058520 5058521 16777216 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz24) (Real.sqrt qz23) Bool.false 111287461 33554432 1 33554432 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz23) Bool.false 111287461 33554432 1 33554432 111287461 33554432 1 33554432 (BSN.sqrt_enclosure 11 1 55643730 55643731 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz25 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

theorem RS433to438.d48 : Enclosure.Real.IsNear qz25 Bool.false 10117041 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz25 Bool.false 10117041 33554432 1 33554432 10117041 33554432 1 33554432 (Ns432p76 rfl rfl) rfl 

theorem RS433to438.d49 : Enclosure.Real.IsNear qz25 Bool.false 80936328 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz25 Bool.false 10117041 33554432 1 33554432 80936328 268435456 8 268435456 RS433to438.d48 rfl 

theorem RS433to438.d50 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz524 := (@instHMul Real Real.instMul)

noncomputable abbrev qz451 := (@HMul.hMul Real Real Real qz524 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz293 := qz451

noncomputable abbrev qz26 := qz293

theorem RS433to438.d51 : Enclosure.Real.IsNear qz26 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS433to438.d50 rfl 

noncomputable abbrev qz294 := (@Inv.inv Real Real.instInv qz451)

noncomputable abbrev qz27 := qz294

theorem RS433to438.d52 : Enclosure.Real.IsNear qz27 Bool.false 5340353 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz27 Bool.false 5340353 33554432 1 33554432 5340353 33554432 1 33554432 (@Enclosure.Real.IsNear.inv_image qz26 884279719003555 140737488355328 1 500000000000000 2670176 2670177 16777216 RS433to438.d51 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns432p77 := nat_lit 399039967802485020557312000 

noncomputable def Ns432p78 := nat_lit 4040499389416809441905461952512 

noncomputable abbrev qz525 := (Enclosure.sfrac Bool.false 791361 1000)

noncomputable abbrev qz452 := qz525

noncomputable abbrev qz295 := qz452

noncomputable abbrev qz28 := qz295

noncomputable abbrev qz453 := qz524

noncomputable abbrev qz296 := qz453

noncomputable abbrev qz29 := qz296

noncomputable abbrev qz297 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 11)

noncomputable abbrev qz298 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz526 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 791361 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz454 := qz526

noncomputable abbrev qz299 := qz454

noncomputable abbrev qz300 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz30 := (@HMul.hMul Real Real Real qz296 qz297 (@HPow.hPow Real Real Real qz298 qz299 qz300))

noncomputable abbrev qz527 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 791361 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz455 := qz527

noncomputable abbrev qz301 := qz455

noncomputable abbrev qz31 := (Zeta.RiemannSiegel.correction qz301)

noncomputable def Ns432p79 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz28) qz28 11) (@HMul.hMul Real Real Real qz29 qz30 qz31) 235103353 134217728 152357 134217728 2983789052464613055705 18889465931478580854784 9484644387844780175427 Ns432p77 Ns432p78 

noncomputable def Ns432p80 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz28) qz28 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 791361 1000 194 242 268435456 134217728 4503599627370496 Bool.false 407321042875 2576 

noncomputable def Ns432p81 := Ns432p80 618095470 41 84886744 8 643680110 41 80936328 8 Bool.true 69648941 130703 Bool.true 14065276 Bool.true 21195014 14148475504056880 1 Bool.false 268067049 Bool.true Bool.false 267599137 Bool.true Bool.true 235103353 

noncomputable def Ns432p82 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz28) qz28 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 791361 1000 81 140 268435456 134217728 4503599627370496 Bool.false 407321042875 2576 

noncomputable def Ns432p83 := Ns432p82 558195838 41 94906264 8 589812974 41 89478488 8 Bool.false 1805938 106627 Bool.true 259121990 Bool.true 401902085 14148475504056880 1 Bool.false 220713629 Bool.true Bool.false 19737515 Bool.false Bool.true 69648941 

noncomputable def Ns432p84 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz28) qz28 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 791361 1000 63 14 268435456 134217728 4503599627370496 Bool.false 407321042875 2576 

noncomputable def Ns432p85 := Ns432p84 480971758 41 109588312 8 522351262 41 101459064 8 Bool.false 36399513 79073 Bool.false 134333511 Bool.true 144170176 14148475504056880 1 Bool.false 128796410 Bool.false Bool.false 230642017 Bool.true Bool.false 1805938 

noncomputable def Ns432p86 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz28) qz28 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 791361 1000 267 155 268435456 134217728 4503599627370496 Bool.false 407321042875 2576 

noncomputable def Ns432p87 := Ns432p86 372130544 40 134217720 8 432030192 40 120047984 16 Bool.true 102914632 46621 Bool.false 248910097 Bool.false 72296722 14148475504056880 1 Bool.false 214743074 Bool.false Bool.false 71425859 Bool.false Bool.false 36399513 

noncomputable def Ns432p88 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz28) qz28 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 791361 1000 616 412 268435456 134217728 4503599627370496 Bool.false 407321042875 2576 

noncomputable def Ns432p89 := Ns432p88 186065264 40 189812528 16 294906480 40 154981288 8 Bool.true 268435448 2624 Bool.false 335273678 Bool.false 220695509 14148475504056880 1 Bool.false 84900494 Bool.false Bool.false 182709015 Bool.false Bool.true 102914632 

noncomputable def Ns432p90 := nat_lit 6713749225204632687381518166648639126581352476989492134071 

noncomputable def Ns432p91 := nat_lit 4424540215288088771920910990729829324261211896807424000 

noncomputable def Ns432p92 := nat_lit 148975514495426343114381462144480000 

noncomputable def Ns432p93 := nat_lit 707360604536560781015598545390483023680 

noncomputable abbrev qz302 := (@Eq.refl Real qz452)

noncomputable abbrev qz32 := qz302

noncomputable def Ns432p94 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz28 791361 1000 2505009929284 16000000 1582722 4000 2000 Ns432p92 Ns432p93 qz32 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns432p95 := nat_lit 19335597768589342139658772319948080684554295133729737346124480 

noncomputable abbrev qz528 := (@instHSub Real Real.instSub)

noncomputable abbrev qz456 := qz528

noncomputable abbrev qz303 := qz456

noncomputable abbrev qz457 := (Real.log (Enclosure.sfrac Bool.false 2505009929284 16000000))

noncomputable abbrev qz458 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz529 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz530 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz459 := (@HSub.hSub Real Real Real qz528 qz529 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz530 (@Nat.cast Real Real.instNatCast 1582722))))

noncomputable abbrev qz304 := (@HSub.hSub Real Real Real qz456 (@HMul.hMul Real Real Real qz453 (Enclosure.sfrac Bool.false 791361 4000) qz457) (@HMul.hMul Real Real Real qz453 qz458 qz459))

noncomputable abbrev qz305 := (Enclosure.sfrac Bool.false 791361 2000)

noncomputable abbrev qz33 := (@HSub.hSub Real Real Real qz303 (@HSub.hSub Real Real Real qz303 qz304 qz305) (@HMul.hMul Real Real Real qz296 qz305 (Real.log Real.pi)))

noncomputable def Ns432p96 := @Enclosure.Real.IsNear.addLit_ft_p qz33 (Enclosure.sfrac Bool.true Ns432p92 Ns432p93) 27334856264665280382311 18014398509481984000 6639378701328307797 692224000000000000000000 Ns432p92 Ns432p93 0 1 Ns432p95 

noncomputable def Ns432p97 := nat_lit 1834411151524970306698376904704000 

noncomputable abbrev qz34 := (@HSub.hSub Real Real Real qz303 qz304 qz305)

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz296 qz305 (Real.log Real.pi))

noncomputable def Ns432p98 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz35 35494429291301922506087 18014398509481984000 2498005398664653 676000000000000000000 30396778235721 67108864000 791361 134217728000 Ns432p97 27334856264665280382311 18014398509481984000 

noncomputable def Ns432p99 := nat_lit 70988858582603845012174000 

noncomputable abbrev qz36 := qz304

noncomputable abbrev qz37 := qz305

noncomputable def Ns432p100 := @Enclosure.Real.IsNear.subLit_ff_p qz36 qz37 42622375500733008676199 18014398509481984000 2498005398664653 676000000000000000000 791361 2000 0 1 Ns432p99 35494429291301922506087 18014398509481984000 2498005398664653 676000000000000000000 

noncomputable def Ns432p101 := nat_lit 95977057211373267867118578480135012352 

noncomputable def Ns432p102 := nat_lit 57840884328486316032393216 

noncomputable def Ns432p103 := nat_lit 4835703278458516698824704 

noncomputable def Ns432p104 := nat_lit 997609719756426562478509895246618957367925446741727208949074745106767633223680 

noncomputable def Ns432p105 := nat_lit 2624137880642144792824731794798889631264240820631165475819076180794918465536 

noncomputable def Ns432p106 := nat_lit 69046984906814458328895939099551538184695264697629121602654326164746240 

noncomputable def Ns432p107 := BSN.log_dyadic_bound 407857929284 4602161929284 4 3 Ns432p104 134217728 54080000 Ns432p105 Ns432p106 23852163 5010019858568 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 407857929284) (BSN.artanhQ 4602161929284) 0 3 Ns432p105 Ns432p104 Ns432p106 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz306 := qz457

noncomputable abbrev qz38 := qz306

noncomputable abbrev qz307 := (Enclosure.sfrac Bool.false 791361 4000)

noncomputable abbrev qz308 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns432p108 := @Enclosure.Real.IsNear.mulLit_ff qz307 qz38 791361 4000 0 1 53868521310841959 4503599627370496 3125002873 169000000000000000 42629446893069203516199 18014398509481984000 2473005398580153 676000000000000000000 (Enclosure.Real.IsNear.const Bool.false 791361 4000) (BSN.isNear_log_sfrac 2505009929284 16000000 53868521310841959 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2505009929284) qz308)) Bool.false Ns432p102 Ns432p103 1000000919360000 54080000000000000000000 53868521310841959 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2505009929284 16000000 17 5010019858568 4194304000000 23852163 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns432p107 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns432p109 := BSN.arctan_dyadic_bound_f 1000 1582722 1 0 16777216 6760000 0 1 1 0 1 1 10600 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1582722) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1582722) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz460 := qz529

noncomputable abbrev qz309 := qz460

noncomputable abbrev qz39 := qz309

noncomputable abbrev qz461 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz530 (@Nat.cast Real Real.instNatCast 1582722)))

noncomputable abbrev qz310 := qz461

noncomputable abbrev qz40 := qz310

noncomputable abbrev qz531 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz462 := qz531

noncomputable abbrev qz311 := qz462

noncomputable abbrev qz41 := (@Enclosure.Real.IsNear.mulLit_ff qz311 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def Ns432p110 := @Enclosure.Real.IsNear.subLit_ff_p qz39 qz40 884279719003555 562949953421312 1 2000000000000000 10600 16777216 1 6760000 14829784580635681095680 883924042024355 562949953421312 50000000169 338000000000000000 qz41 (Ns432p109 rfl) rfl rfl 

noncomputable abbrev qz312 := (@HMul.hMul Real Real Real qz453 (Enclosure.sfrac Bool.false 791361 4000) qz457)

noncomputable abbrev qz42 := qz312

noncomputable abbrev qz313 := (@HMul.hMul Real Real Real qz453 qz458 qz459)

noncomputable abbrev qz43 := qz313

noncomputable abbrev qz314 := qz458

noncomputable abbrev qz44 := qz314

noncomputable abbrev qz315 := qz459

noncomputable abbrev qz45 := qz315

noncomputable abbrev qz46 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns432p111 := @Enclosure.Real.IsNear.subLit_ff_p qz42 qz43 42629446893069203516199 18014398509481984000 2473005398580153 676000000000000000000 883924042024355 2251799813685248 50000000169 1352000000000000000 Ns432p101 42622375500733008676199 18014398509481984000 2498005398664653 676000000000000000000 (Ns432p108 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 qz45 1 4 0 1 883924042024355 562949953421312 50000000169 338000000000000000 883924042024355 2251799813685248 50000000169 1352000000000000000 qz46 Ns432p110 rfl) 

noncomputable def Ns432p112 := @Ns432p96 Ns432p90 Ns432p91 6639378701328307797 692224000000000000000000 (@Ns432p98 6639378701328307797 692224000000000000000000 (Ns432p100 (Ns432p111 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 791361 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz37 (Real.log Real.pi) 791361 2000 0 1 38410761 33554432 1 67108864 30396778235721 67108864000 791361 134217728000 (Enclosure.Real.IsNear.const Bool.false 791361 2000) RS433to438.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns432p92 Ns432p93) 

noncomputable abbrev qz47 := (@instHAdd Real Real.instAdd)

noncomputable def Ns432p113 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz28) Bool.false Ns432p90 Ns432p91 6639378701328307797 692224000000000000000000 50915130359 33554432 323 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz28) (@HAdd.hAdd Real Real Real qz47 qz33 (Enclosure.sfrac Bool.true Ns432p92 Ns432p93)) Bool.false Ns432p90 Ns432p91 6639378701328307797 692224000000000000000000 Ns432p94 (Ns432p112 rfl rfl)) 

noncomputable def Ns432p114 := nat_lit 7595313475870928192667648 

noncomputable def Ns432p115 := nat_lit 3509739900715503805730314778548090758159480398853636880201065485367618064451676861362959417874787280689502967253483878729334501903244988416 

noncomputable def Ns432p116 := nat_lit 69061887427279807374175457422696049589758900585025510522285359577850094671315332446731519433112496475662717985575392155893264493730122956800 

noncomputable def Ns432p117 := nat_lit 2500292557630980455765410079377196739232046913746971275588215383969409008517528082895944811684330609094540884054124738430641551446016 

noncomputable def Ns432p118 := nat_lit 17526899859661539651274301364496721347363911476117762298771474493592609254411837065105049249271170092444509312936525884720691405121524862976 

noncomputable def Ns432p119 := nat_lit 2417166059954793258096141009794361735641561520475892868279987585224753313496036635635603180158937376648195129495138725456264257280554303488000 

noncomputable def Ns432p120 := BSN.sin_dyadic_bound_f 107935896322 68719476736 4 3 33554432 13533204 Ns432p115 Ns432p116 Ns432p117 Ns432p118 Ns432p119 Ns432p117 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107935896322) (BSN.sinEvenQ 68719476736) 0 3 Ns432p115 Ns432p116 Ns432p117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107935896322) (BSN.sinOddQ 68719476736) 0 3 Ns432p118 Ns432p119 Ns432p117 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz48 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable abbrev qz316 := (@Nat.cast Real Real.instNatCast Ns432p103)

noncomputable def Ns432p121 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz28) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50915130359) qz48) Bool.false 50915130359 33554432 323 33554432 Bool.true 33554431 33554432 1 6760000 (Ns432p113 rfl) (Enclosure.sfrac_false_div 50915130359 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50915130359) qz48) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns432p114) qz316) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 241 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q1 50915130359 33554432 226375608064910080 72057594037927936 241 Ns432p114 Ns432p103 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns432p114 Ns432p103 107935896322 68719476736 13533204 13520000 (Ns432p120 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns432p122 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz28) Bool.false Ns432p90 Ns432p91 6639378701328307797 692224000000000000000000 407321042875 268435456 2576 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz28) (@HAdd.hAdd Real Real Real qz47 qz33 (Enclosure.sfrac Bool.true Ns432p92 Ns432p93)) Bool.false Ns432p90 Ns432p91 6639378701328307797 692224000000000000000000 Ns432p94 (Ns432p112 rfl rfl)) 

noncomputable def Ns432p123 := Ns432p89 46621 BSN.abs_quadSignPos (BSN.cos_quad_nat0 616 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 84900494 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 412 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 182709015 268435456) qz32 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz28) qz28 1) Bool.true 33554431 33554432 34641163 3544186880000 268435448 268435456 2624 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz28) qz28 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz28)) Bool.true 33554431 33554432 34641163 3544186880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz28) qz28) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz28)) Bool.true 33554431 33554432 2217034432 226827960320000 33554431 33554432 34641163 3544186880000 (Ns432p121 rfl rfl) rfl)) rfl) (Ns432p122 rfl) RS433to438.d7 

noncomputable def Ns432p124 := nat_lit 6808812117098246525992185249352873447810239020668443534628905027000217677340656228956611613227534715574685696 

noncomputable def Ns432p125 := nat_lit 67052582193422231333984484018745857420694574238012043916021913709013615522643186318434558042568065189255577600 

noncomputable def Ns432p126 := nat_lit 2017406914103063786074736323431481854218482650689930347579303365974176764860798124414814701838858326016 

noncomputable def Ns432p127 := nat_lit 41266951436907174502148979877657738622323377422447977056236301931005076175084725817583444531924307837231697920 

noncomputable def Ns432p128 := nat_lit 6101784979601423051392588045705873025283206255659095996357994147520239012560529954977544781873693932222257561600 

noncomputable abbrev qz49 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz50 := (BSN.cosOddQ 268435456)

noncomputable def Ns432p129 := BSN.cos_dyadic_bound_f 335273678 268435456 4 3 268435456 134217728 Ns432p124 Ns432p125 Ns432p126 Ns432p127 Ns432p128 Ns432p126 84900494 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 335273678) qz49 0 3 Ns432p124 Ns432p125 Ns432p126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 335273678) qz50 0 3 Ns432p127 Ns432p128 Ns432p126 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p130 := nat_lit 20699548535705022541296479938570366305649454252360017147825598433160801 

noncomputable def Ns432p131 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120 

noncomputable def Ns432p132 := nat_lit 5627920646778455518520087848289812952272083135483628281180569562721 

noncomputable def Ns432p133 := nat_lit 62087389765821510712852399640014519291043818590809084186914434160356961 

noncomputable def Ns432p134 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400 

noncomputable def Ns432p135 := BSN.cos_dyadic_bound_f 220695509 268435456 3 2 268435456 134217728 Ns432p130 Ns432p131 Ns432p132 Ns432p133 Ns432p134 Ns432p132 182709015 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 220695509) qz49 0 2 Ns432p130 Ns432p131 Ns432p132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 220695509) qz50 0 2 Ns432p133 Ns432p134 Ns432p132 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p136 := nat_lit 60286145474010979867640204983704681181693712132119841466864190591968385 

noncomputable def Ns432p137 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080 

noncomputable def Ns432p138 := nat_lit 14734659776668556218305586163316707829055731720477525417067649016961 

noncomputable def Ns432p139 := nat_lit 157868429649437960086132804008295461758426965351814049753016675356746881 

noncomputable def Ns432p140 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800 

noncomputable abbrev qz51 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz52 := (BSN.sinOddQ 268435456)

noncomputable def Ns432p141 := BSN.sin_dyadic_bound_f 248910097 268435456 3 2 268435456 134217728 Ns432p136 Ns432p137 Ns432p138 Ns432p139 Ns432p140 Ns432p138 214743074 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 248910097) qz51 0 2 Ns432p136 Ns432p137 Ns432p138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 248910097) qz52 0 2 Ns432p139 Ns432p140 Ns432p138 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p142 := nat_lit 27319605622727603214177809840656 

noncomputable def Ns432p143 := nat_lit 623075623024179315423659559506411520 

noncomputable def Ns432p144 := nat_lit 4361529361169255207965616916544880640 

noncomputable def Ns432p145 := BSN.sin_dyadic_bound_f 72296722 268435456 2 1 268435456 134217728 Ns432p142 Ns432p143 Ns432p142 Ns432p142 Ns432p144 Ns432p142 71425859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 72296722) qz51 0 1 Ns432p142 Ns432p143 Ns432p142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 72296722) qz52 0 1 Ns432p142 Ns432p144 Ns432p142 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p146 := Ns432p87 79073 BSN.abs_quadSignPos (BSN.cos_quad_nat3 267 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 214743074 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 71425859 268435456) qz32 rfl rfl (Ns432p123 RS433to438.d9 RS433to438.d11 RS433to438.d13 RS433to438.d17 (Ns432p129 rfl rfl) (Ns432p135 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns432p122 rfl) RS433to438.d19 RS433to438.d21 RS433to438.d23 RS433to438.d25 RS433to438.d17 (Ns432p141 rfl rfl) (Ns432p145 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns432p147 := nat_lit 5113141027690654932646899812865462006758384958164292044355358828823745 

noncomputable def Ns432p148 := nat_lit 106041271483979794516110330022706074833829267540550711041401586881 

noncomputable def Ns432p149 := nat_lit 13391388148559788856312663902684744684055562976378080176922348949112001 

noncomputable def Ns432p150 := BSN.sin_dyadic_bound_f 134333511 268435456 3 2 268435456 134217728 Ns432p147 Ns432p137 Ns432p148 Ns432p149 Ns432p140 Ns432p148 128796410 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 134333511) qz51 0 2 Ns432p147 Ns432p137 Ns432p148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 134333511) qz52 0 2 Ns432p149 Ns432p140 Ns432p148 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p151 := nat_lit 3768703916148330614031763734129194948847803050703682450018971529773056 

noncomputable def Ns432p152 := nat_lit 186639442732773096001601298559641094839563333770217648382621515776 

noncomputable def Ns432p153 := nat_lit 11305738469559526295903287999790465564353730025443506914760149346287616 

noncomputable def Ns432p154 := BSN.cos_dyadic_bound_f 144170176 268435456 3 2 268435456 134217728 Ns432p151 Ns432p131 Ns432p152 Ns432p153 Ns432p134 Ns432p152 230642017 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 144170176) qz49 0 2 Ns432p151 Ns432p131 Ns432p152 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 144170176) qz50 0 2 Ns432p153 Ns432p134 Ns432p152 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p155 := Ns432p85 106627 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 128796410 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 230642017 268435456) qz32 rfl rfl (Ns432p146 rfl rfl) (Ns432p122 rfl) RS433to438.d27 RS433to438.d29 RS433to438.d31 RS433to438.d33 RS433to438.d17 (Ns432p150 rfl rfl) (Ns432p154 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p156 := nat_lit 70808119824814070554153895227762232617011185726759826864762165051040000 

noncomputable def Ns432p157 := nat_lit 20325168861972760180955224587662877556682849491835535222240100000000 

noncomputable def Ns432p158 := nat_lit 185416930220165086030110083804330583623747047528050860445922043543200000 

noncomputable def Ns432p159 := BSN.sin_dyadic_bound_f 259121990 268435456 3 2 268435456 134217728 Ns432p156 Ns432p137 Ns432p157 Ns432p158 Ns432p140 Ns432p157 220713629 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 259121990) qz51 0 2 Ns432p156 Ns432p137 Ns432p157 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 259121990) qz52 0 2 Ns432p158 Ns432p140 Ns432p157 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p160 := nat_lit 14080671269090211512778007037280678930127605740062133258101781279995108628462216800098139316850731367508140625 

noncomputable def Ns432p161 := nat_lit 17760006113119155140076858480352981355817251585940014539612010916327092139172672895757772897500244140625 

noncomputable def Ns432p162 := nat_lit 85252825894166660068437892106532474758995380499892537696377617914996324991320759741499637283889469412845740625 

noncomputable def Ns432p163 := BSN.cos_dyadic_bound_f 401902085 268435456 4 3 268435456 134217728 Ns432p160 Ns432p125 Ns432p161 Ns432p162 Ns432p128 Ns432p161 19737515 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 401902085) qz49 0 3 Ns432p160 Ns432p125 Ns432p161 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 401902085) qz50 0 3 Ns432p162 Ns432p128 Ns432p161 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p164 := Ns432p83 130703 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 220713629 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 19737515 268435456) qz32 rfl rfl (Ns432p155 rfl) (Ns432p122 rfl) RS433to438.d35 RS433to438.d37 RS433to438.d39 RS433to438.d41 RS433to438.d17 (Ns432p159 rfl rfl) (Ns432p163 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p165 := nat_lit 39137495854356542830048542976 

noncomputable def Ns432p166 := nat_lit 124615124604835863084731911901282304 

noncomputable def Ns432p167 := nat_lit 1869226869072537946270978678519234560 

noncomputable def Ns432p168 := BSN.cos_dyadic_bound_f 14065276 268435456 2 1 268435456 134217728 Ns432p165 Ns432p166 Ns432p165 Ns432p165 Ns432p167 Ns432p165 268067049 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14065276) qz49 0 1 Ns432p165 Ns432p166 Ns432p165 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14065276) qz50 0 1 Ns432p165 Ns432p167 Ns432p165 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p169 := nat_lit 201806351643656350390036358416 

noncomputable def Ns432p170 := BSN.cos_dyadic_bound_f 21195014 268435456 2 1 268435456 134217728 Ns432p169 Ns432p166 Ns432p169 Ns432p169 Ns432p167 Ns432p169 267599137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 21195014) qz49 0 1 Ns432p169 Ns432p166 Ns432p169 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 21195014) qz50 0 1 Ns432p169 Ns432p167 Ns432p169 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p171 := Ns432p81 152357 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 194 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268067049 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 242 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267599137 268435456) qz32 rfl rfl (Ns432p164 rfl) (Ns432p122 rfl) RS433to438.d43 RS433to438.d45 RS433to438.d47 RS433to438.d49 RS433to438.d17 (Ns432p168 rfl rfl) (Ns432p170 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p172 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz28) qz28 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz28) qz28 11) 235103353 268435456 152357 268435456 235103353 268435456 152357 268435456 126220151539367936 235103353 134217728 152357 134217728 (Ns432p171 rfl) 

noncomputable def Ns432p173 := @Enclosure.Real.IsNear.mulLit_tf qz30 qz31 10016159 33554432 1 33554432 297897532623495 562949953421312 4731529499562761 59461588830126080000 2983789052464613055705 18889465931478580854784 

noncomputable abbrev qz53 := qz297

noncomputable abbrev qz54 := (@HPow.hPow Real Real Real qz298 qz299 qz300)

noncomputable def Ns432p174 := @Enclosure.Real.IsNear.mulLit_tf qz53 qz54 1 1 0 1 10016159 33554432 1 33554432 10016159 33554432 1 33554432 

noncomputable abbrev qz55 := qz299

noncomputable abbrev qz56 := (@Enclosure.Real.IsNear.of_eq qz299 (@HMul.hMul Real Real Real qz296 qz295 qz294) Bool.false 4226147090433 33554432000 791361 33554432000 (BSN.t_div_two_pi_mk qz295 791361 1000 qz302) (@Enclosure.Real.IsNear.mulLit_ff qz295 qz294 791361 1000 0 1 5340353 33554432 1 33554432 4226147090433 33554432000 791361 33554432000 (Enclosure.Real.IsNear.const Bool.false 791361 1000) RS433to438.d52 rfl))

noncomputable def Ns432p175 := @Enclosure.Real.IsNear.sqrt_image qz55 4226147090433 33554432000 791361 33554432000 188285646 188285682 16777216 qz56 

noncomputable abbrev qz532 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 791361 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz463 := qz532

noncomputable abbrev qz317 := qz463

noncomputable abbrev qz57 := qz317

noncomputable def Ns432p176 := @Enclosure.Real.IsNear.sqrt_image qz57 5883927 524288 9 8388608 56204172 56204178 16777216 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 376571328 33554432 36 33554432 5883927 524288 9 8388608 (Ns432p175 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz464 := (Real.sqrt qz532)

noncomputable abbrev qz318 := qz464

noncomputable abbrev qz58 := qz318

noncomputable def Ns432p177 := @Enclosure.Real.IsNear.inv_image qz58 56204175 16777216 3 16777216 5008079 5008080 16777216 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 112408350 33554432 6 33554432 56204175 16777216 3 16777216 (Ns432p176 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns432p178 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz58) Bool.false 10016159 33554432 1 33554432 10016159 33554432 1 33554432 (Ns432p177 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz319 := (@HMul.hMul Real Real Real qz453 qz451 qz455)

noncomputable abbrev qz59 := (@Inv.inv Real Real.instInv (Real.cos qz319))

noncomputable abbrev qz465 := (@HMul.hMul Real Real Real qz524 qz527 qz527)

noncomputable abbrev qz466 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz320 := (@HSub.hSub Real Real Real qz456 (@HSub.hSub Real Real Real qz456 qz465 qz455) qz466)

noncomputable abbrev qz60 := (Real.cos (@HMul.hMul Real Real Real qz296 qz293 qz320))

noncomputable def Ns432p179 := @Enclosure.Real.IsNear.of_eq qz31 (@HMul.hMul Real Real Real qz29 qz59 qz60) Bool.false 297897532623495 

noncomputable def Ns432p180 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz60 196580781 33554432 7963 

noncomputable def Ns432p181 := @Enclosure.Real.IsNear.recentre' qz59 Bool.false 196580781 33554432 7963 33554432 196580781 33554432 7963 

noncomputable abbrev qz61 := (Real.cos qz319)

noncomputable def Ns432p182 := @Enclosure.Real.IsNear.recentre' qz61 Bool.false 2863708 16777216 1568074432 226827960320000 715927 4194304 24501163 3544186880000 

noncomputable abbrev qz62 := qz319

noncomputable def Ns432p183 := @Enclosure.Real.IsNear.cos_image qz62 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46951579) qz48) Bool.false 46951579 33554432 227 33554432 Bool.false 2863708 16777216 1 

noncomputable def Ns432p184 := nat_lit 242874678697443643864957951 

noncomputable def Ns432p185 := nat_lit 36028797018963968000000000000000 

noncomputable abbrev qz63 := qz301

noncomputable def Ns432p186 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz63 884279719003555 140737488355328 1 500000000000000 116759 524288 9 8388608 103247615711136078245 73786976294838206464 Ns432p184 

noncomputable def Ns432p187 := @Enclosure.Real.IsNear.subLit_ff_p qz57 qz22 5883927 524288 9 8388608 11 1 0 1 116759 116759 524288 9 

noncomputable abbrev qz64 := (Enclosure.Real.IsNear.const Bool.false 11 1)

noncomputable def Ns432p188 := @Ns432p187 8388608 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 376571328 33554432 36 33554432 5883927 524288 9 8388608 (Ns432p175 rfl rfl rfl rfl rfl rfl) rfl) qz64 

noncomputable def Ns432p189 := @Enclosure.Real.IsNear.recentre' qz62 Bool.false 103247615711136078245 73786976294838206464 Ns432p184 Ns432p185 46951579 33554432 227 33554432 (@Ns432p186 Ns432p185 RS433to438.d51 (Ns432p188 rfl rfl) rfl) 

noncomputable def Ns432p190 := nat_lit 156212527975407180168647609912477276720661051070260527890949423961584169721226778812772843256973521 

noncomputable def Ns432p191 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600 

noncomputable def Ns432p192 := nat_lit 114763141521535256519126967530818247283651569277795933667327632338783982994809929416750303441 

noncomputable def Ns432p193 := nat_lit 946250365431267453935867268671464663175029713021431679026593539491098868717044434107008766541203665 

noncomputable def Ns432p194 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600 

noncomputable def Ns432p195 := BSN.cos_dyadic_bound_f 46951579 33554432 4 3 16777216 6760000 Ns432p190 Ns432p191 Ns432p192 Ns432p193 Ns432p194 Ns432p192 2863708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 46951579) (BSN.cosEvenQ 33554432) 0 3 Ns432p190 Ns432p191 Ns432p192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 46951579) (BSN.cosOddQ 33554432) 0 3 Ns432p193 Ns432p194 Ns432p192 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p196 := @Enclosure.Real.IsNear.inv_image qz61 715927 4194304 24501163 3544186880000 98286409 98294372 16777216 (Ns432p182 (@Ns432p183 6760000 (Ns432p189 rfl) (Enclosure.sfrac_false_div 46951579 33554432) (Ns432p195 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns432p197 := @Enclosure.Real.IsNear.recentre' qz60 Bool.false 1515395 16777216 

noncomputable abbrev qz65 := (@HMul.hMul Real Real Real qz296 qz293 qz320)

noncomputable def Ns432p198 := @Enclosure.Real.IsNear.cos_image qz65 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 49672251)) qz48) Bool.true 49672251 33554432 

noncomputable def Ns432p199 := nat_lit 57268207477688928562055725 

noncomputable def Ns432p200 := nat_lit 38685626227668133590597632 

noncomputable def Ns432p201 := nat_lit 588966481211974215221309985592171 

noncomputable def Ns432p202 := @Enclosure.Real.IsNear.recentre' qz65 Bool.true Ns432p199 Ns432p200 Ns432p201 

noncomputable def Ns432p203 := nat_lit 60446290980731458735308800000000000000 

noncomputable abbrev qz66 := qz320

noncomputable def Ns432p204 := @Enclosure.Real.IsNear.mulLit_ft qz26 qz66 884279719003555 140737488355328 1 500000000000000 64762547695 

noncomputable abbrev qz321 := (@HSub.hSub Real Real Real qz456 qz465 qz455)

noncomputable abbrev qz67 := qz321

noncomputable abbrev qz322 := qz466

noncomputable abbrev qz68 := qz322

noncomputable def Ns432p205 := @Enclosure.Real.IsNear.subLit_tf qz67 qz68 47582678511 274877906944 109124145 70368744177664 1 16 

noncomputable abbrev qz323 := qz465

noncomputable abbrev qz69 := qz323

noncomputable def Ns432p206 := @Enclosure.Real.IsNear.subLit_ff_n qz69 qz63 13632664081 274877906944 33626673 70368744177664 116759 524288 9 8388608 

noncomputable def Ns432p207 := @Enclosure.Real.IsNear.mulLit_ff qz63 qz63 116759 524288 9 8388608 116759 524288 9 8388608 13632664081 274877906944 

noncomputable def Ns432p208 := nat_lit 195803479308198196807356338945404028484430549986270582487711387473683701116752084958581605932307281 

noncomputable def Ns432p209 := nat_lit 225614026634384430844042068748064369104308360437055522111431711829926949421513536329851442001 

noncomputable def Ns432p210 := nat_lit 1185616017096540418833934951592955845055220717342265034876745240537941110583982444209162524857307985 

noncomputable def Ns432p211 := BSN.cos_dyadic_bound_f 49672251 33554432 4 3 16777216 6760000 Ns432p208 Ns432p191 Ns432p209 Ns432p210 Ns432p194 Ns432p209 1515395 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 49672251) (BSN.cosEvenQ 33554432) 0 3 Ns432p208 Ns432p191 Ns432p209 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 49672251) (BSN.cosOddQ 33554432) 0 3 Ns432p210 Ns432p194 Ns432p209 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz70 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns432p212 := @Ns432p197 281354304 28353495040000 1515395 16777216 4396161 443023360000 (@Ns432p198 41 4194304 Bool.false 1515395 16777216 1 6760000 (@Ns432p202 Ns432p203 49672251 33554432 41 4194304 (@Ns432p204 274877906944 109124145 70368744177664 Ns432p199 Ns432p200 Ns432p201 Ns432p203 RS433to438.d51 (@Ns432p205 0 1 1036200763120 64762547695 274877906944 109124145 70368744177664 (@Ns432p206 24947027351175168 47582678511 274877906944 109124145 70368744177664 (@Ns432p207 33626673 70368744177664 (Ns432p188 rfl rfl) (Ns432p188 rfl rfl) rfl) (Ns432p188 rfl rfl) rfl rfl) qz70 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 49672251 33554432) (BSN.cos_neg_of_bound 49672251 33554432 Bool.false 1515395 16777216 1 6760000 (Ns432p211 rfl rfl)) rfl rfl) 

noncomputable abbrev qz71 := (@Enclosure.Real.IsNear.of_eq qz297 (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1))

noncomputable def Ns432p213 := @Ns432p173 9484644387844780175427 Ns432p77 (Ns432p174 qz71 (@Enclosure.Real.IsNear.of_eq qz54 (@Inv.inv Real Real.instInv qz58) Bool.false 10016159 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz55 (BSN.t_div_two_pi_nonneg qz28 791361 1000 qz32)) Ns432p178) rfl) (@Ns432p179 562949953421312 4731529499562761 59461588830126080000 (BSN.correction_mk qz63 (BSN.cos_two_pi_p_ne_zero_mk qz28 791361 1000 11 qz32 rfl rfl (@BSN.floor_sqrt_eq_dec qz28 791361 1000 11 qz32 rfl rfl rfl))) (@Ns432p180 33554432 1515395 16777216 4396161 443023360000 297897532623495 562949953421312 4731529499562761 59461588830126080000 (@Ns432p181 33554432 (Ns432p196 rfl rfl rfl rfl rfl) rfl) (Ns432p212 rfl) rfl)) 

noncomputable abbrev qz72 := qz303

noncomputable def Ns432p214 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz28) (hardyZApproximantRS₀ qz28) Bool.true 30104066352671455159079 18889465931478580854784 462454108857420738703427 Ns432p77 (@Eq.refl Real (hardyZApproximantRS₀ qz28)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz28) (@HSub.hSub Real Real Real qz72 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz28) qz28 11) (@HMul.hMul Real Real Real qz29 qz30 qz31)) Bool.true 30104066352671455159079 18889465931478580854784 462454108857420738703427 Ns432p77 (BSN.hardyZApproximantRS₀_eq qz28 11 (@BSN.floor_sqrt_eq_dec qz28 791361 1000 11 qz32 rfl rfl rfl)) (@Ns432p79 30104066352671455159079 18889465931478580854784 462454108857420738703427 Ns432p77 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz28) qz28 11) (@HAdd.hAdd Real Real Real qz47 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz28) qz28 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz28) qz28 11)) Bool.true 235103353 134217728 152357 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz28) qz28 11) (Ns432p172 (Ns432p171 rfl) rfl rfl)) (Ns432p213 rfl) rfl rfl)) 

theorem RS433to438.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz28) Bool.true 30104066352671455159079 18889465931478580854784 462454108857420738703427 Ns432p77 := Ns432p214 

theorem RS433to438.d54 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS433to438.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS433to438.d3 a b h)) 

noncomputable def Ns432p215 := nat_lit 15347691069326346944512000 

noncomputable def Ns432p216 := nat_lit 246542644384666799740578430976 

noncomputable abbrev qz533 := (Enclosure.sfrac Bool.false 792660 1000)

noncomputable abbrev qz467 := qz533

noncomputable abbrev qz324 := qz467

noncomputable abbrev qz73 := qz324

noncomputable abbrev qz534 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 792660 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz468 := qz534

noncomputable abbrev qz325 := qz468

noncomputable abbrev qz74 := (@HMul.hMul Real Real Real qz296 qz297 (@HPow.hPow Real Real Real qz298 qz325 qz300))

noncomputable abbrev qz535 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 792660 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz469 := qz535

noncomputable abbrev qz326 := qz469

noncomputable abbrev qz75 := (Zeta.RiemannSiegel.correction qz326)

noncomputable def Ns432p217 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz73) qz73 11) (@HMul.hMul Real Real Real qz29 qz74 qz75) 5322283 134217728 38151 33554432 1462363471698559760055 9444732965739290427392 551125637230187242177 Ns432p215 Ns432p216 

noncomputable def Ns432p218 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz73) qz73 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 792660 1000 193 242 268435456 134217728 4503599627370496 Bool.false 408164315438 2579 

noncomputable def Ns432p219 := Ns432p218 618095470 41 84886744 8 643680110 41 80936328 8 Bool.false 170627181 130916 Bool.true 395356156 Bool.true 14062914 14148475504056880 1 Bool.false 267147988 Bool.true Bool.false 268067173 Bool.true Bool.false 5322283 

noncomputable def Ns432p220 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz73) qz73 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 792660 1000 81 140 268435456 134217728 4503599627370496 Bool.false 408164315438 2579 

noncomputable def Ns432p221 := Ns432p220 558195838 41 94906264 8 589812974 41 89478488 8 Bool.false 186609837 106802 Bool.true 140945821 Bool.true 324796575 14148475504056880 1 Bool.false 134558230 Bool.true Bool.false 94772585 Bool.false Bool.false 170627181 

noncomputable def Ns432p222 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz73) qz73 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 792660 1000 63 13 268435456 134217728 4503599627370496 Bool.false 408164315438 2579 

noncomputable def Ns432p223 := Ns432p222 480971758 41 109588312 8 522351262 41 101459064 8 Bool.false 181766139 79203 Bool.false 352823760 Bool.true 401089331 14148475504056880 1 Bool.false 259658358 Bool.false Bool.false 267647855 Bool.true Bool.false 186609837 

noncomputable def Ns432p224 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz73) qz73 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 792660 1000 268 155 268435456 134217728 4503599627370496 Bool.false 408164315438 2579 

noncomputable def Ns432p225 := Ns432p224 372130544 40 134217720 8 432030192 40 120047984 16 Bool.true 37434456 46699 Bool.false 187127655 Bool.false 354362066 14148475504056880 1 Bool.false 205810563 Bool.false Bool.false 260044244 Bool.false Bool.false 181766139 

noncomputable def Ns432p226 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz73) qz73 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 792660 1000 618 413 268435456 134217728 4503599627370496 Bool.false 408164315438 2579 

noncomputable def Ns432p227 := Ns432p226 186065264 40 189812528 16 294906480 40 154981288 8 Bool.false 268435440 2632 Bool.false 93532607 Bool.false 259227127 14148475504056880 1 Bool.false 252304583 Bool.true Bool.false 220773453 Bool.true Bool.true 37434456 

noncomputable def Ns432p228 := nat_lit 663494213609579140537082078464971467320318437071 

noncomputable def Ns432p229 := nat_lit 436357038200381679466259470772321769855385600 

noncomputable def Ns432p230 := nat_lit 150202233227360623886235648000000000 

noncomputable def Ns432p231 := nat_lit 714355945784233902522161813422080000000 

noncomputable abbrev qz470 := (@Eq.refl Real qz533)

noncomputable abbrev qz327 := qz470

noncomputable abbrev qz76 := qz327

noncomputable def Ns432p232 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz73 792660 1000 2513240502400 16000000 1585320 4000 2000 Ns432p230 Ns432p231 qz76 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns432p233 := nat_lit 978362027620141017470359749621308326851848754567413760000000 

noncomputable abbrev qz471 := (Real.log (Enclosure.sfrac Bool.false 2513240502400 16000000))

noncomputable abbrev qz472 := (@HSub.hSub Real Real Real qz528 qz529 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz530 (@Nat.cast Real Real.instNatCast 1585320))))

noncomputable abbrev qz328 := (@HSub.hSub Real Real Real qz456 (@HMul.hMul Real Real Real qz453 (Enclosure.sfrac Bool.false 792660 4000) qz471) (@HMul.hMul Real Real Real qz453 qz458 qz472))

noncomputable abbrev qz329 := (Enclosure.sfrac Bool.false 792660 2000)

noncomputable abbrev qz77 := (@HSub.hSub Real Real Real qz303 (@HSub.hSub Real Real Real qz303 qz328 qz329) (@HMul.hMul Real Real Real qz296 qz329 (Real.log Real.pi)))

noncomputable def Ns432p234 := @Enclosure.Real.IsNear.addLit_ft_p qz77 (Enclosure.sfrac Bool.true Ns432p230 Ns432p231) 1369572366106955622247 900719925474099200 332511752979663141 34611200000000000000000 Ns432p230 Ns432p231 0 1 Ns432p233 

noncomputable def Ns432p235 := nat_lit 183820891310459788614818594816 

noncomputable abbrev qz78 := (@HSub.hSub Real Real Real qz303 qz328 qz329)

noncomputable abbrev qz79 := (@HMul.hMul Real Real Real qz296 qz329 (Real.log Real.pi))

noncomputable def Ns432p236 := @Enclosure.Real.IsNear.subLit_ff_p qz78 qz79 71128828182306509695 36028797018963968 62551619434917 16900000000000000000 1522333690713 3355443200 39633 6710886400 Ns432p235 1369572366106955622247 900719925474099200 

noncomputable def Ns432p237 := nat_lit 3556441409115325484750000 

noncomputable abbrev qz80 := qz328

noncomputable abbrev qz81 := qz329

noncomputable def Ns432p238 := @Enclosure.Real.IsNear.subLit_ff_p qz80 qz81 2135203032620812478311 900719925474099200 62551619434917 16900000000000000000 792660 2000 0 1 Ns432p237 71128828182306509695 36028797018963968 62551619434917 16900000000000000000 

noncomputable def Ns432p239 := nat_lit 4808049791035722046266122864980656128 

noncomputable def Ns432p240 := nat_lit 57856746690921058279620608 

noncomputable def Ns432p241 := nat_lit 1008362533873951209745880943195446735988425769701716386430561812480000000000000 

noncomputable def Ns432p242 := nat_lit 2751190188173018227318229572578567244379570627932436570409271296000000000000 

noncomputable def Ns432p243 := nat_lit 77840488139354924310175693546269437788919531193611468144640000000000000 

noncomputable def Ns432p244 := BSN.log_dyadic_bound 416088502400 4610392502400 4 3 Ns432p241 134217728 54080000 Ns432p242 Ns432p243 24292432 5026481004800 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 416088502400) (BSN.artanhQ 4610392502400) 0 3 Ns432p242 Ns432p241 Ns432p243 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := qz471

noncomputable abbrev qz82 := qz330

noncomputable abbrev qz331 := (Enclosure.sfrac Bool.false 792660 4000)

noncomputable def Ns432p245 := @Enclosure.Real.IsNear.mulLit_ff qz331 qz82 792660 4000 0 1 53883294287064167 4503599627370496 3125002873 169000000000000000 2135556602479214130711 900719925474099200 123853238865609 33800000000000000000 (Enclosure.Real.IsNear.const Bool.false 792660 4000) (BSN.isNear_log_sfrac 2513240502400 16000000 53883294287064167 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2513240502400) qz308)) Bool.false Ns432p240 Ns432p103 1000000919360000 54080000000000000000000 53883294287064167 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2513240502400 16000000 17 5026481004800 4194304000000 24292432 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns432p244 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns432p246 := BSN.arctan_dyadic_bound_f 1000 1585320 1 0 16777216 6760000 0 1 1 0 1 1 10582 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1585320) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1585320) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz473 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz530 (@Nat.cast Real Real.instNatCast 1585320)))

noncomputable abbrev qz332 := qz473

noncomputable abbrev qz83 := qz332

noncomputable def Ns432p247 := @Enclosure.Real.IsNear.subLit_ff_p qz39 qz83 884279719003555 562949953421312 1 2000000000000000 10582 16777216 1 6760000 14829794713734842679296 883924646004131 562949953421312 50000000169 338000000000000000 qz41 (Ns432p246 rfl) rfl rfl 

noncomputable abbrev qz333 := (@HMul.hMul Real Real Real qz453 (Enclosure.sfrac Bool.false 792660 4000) qz471)

noncomputable abbrev qz84 := qz333

noncomputable abbrev qz334 := (@HMul.hMul Real Real Real qz453 qz458 qz472)

noncomputable abbrev qz85 := qz334

noncomputable abbrev qz335 := qz472

noncomputable abbrev qz86 := qz335

noncomputable def Ns432p248 := @Enclosure.Real.IsNear.subLit_ff_p qz84 qz85 2135556602479214130711 900719925474099200 123853238865609 33800000000000000000 883924646004131 2251799813685248 50000000169 1352000000000000000 Ns432p239 2135203032620812478311 900719925474099200 62551619434917 16900000000000000000 (Ns432p245 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 qz86 1 4 0 1 883924646004131 562949953421312 50000000169 338000000000000000 883924646004131 2251799813685248 50000000169 1352000000000000000 qz46 Ns432p247 rfl) 

noncomputable def Ns432p249 := @Ns432p234 Ns432p228 Ns432p229 332511752979663141 34611200000000000000000 (@Ns432p236 332511752979663141 34611200000000000000000 (Ns432p238 (Ns432p248 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 792660 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz81 (Real.log Real.pi) 792660 2000 0 1 38410761 33554432 1 67108864 1522333690713 3355443200 39633 6710886400 (Enclosure.Real.IsNear.const Bool.false 792660 2000) RS433to438.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns432p230 Ns432p231) 

noncomputable def Ns432p250 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz73) Bool.false Ns432p228 Ns432p229 332511752979663141 34611200000000000000000 51020539429 33554432 81 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz73) (@HAdd.hAdd Real Real Real qz47 qz77 (Enclosure.sfrac Bool.true Ns432p230 Ns432p231)) Bool.false Ns432p228 Ns432p229 332511752979663141 34611200000000000000000 Ns432p232 (Ns432p249 rfl rfl)) 

noncomputable def Ns432p251 := nat_lit 7594551529276631383277568 

noncomputable def Ns432p252 := nat_lit 3508328923062077573064372049320477701807734631864927038039853269225726455862702572994707693838293352654851315622946527502281992639804814881 

noncomputable def Ns432p253 := nat_lit 2497284325663871631855278127443406009534583189726769680701146315953268422902859150631837158372309797951570668467918039085855785563681 

noncomputable def Ns432p254 := nat_lit 17519862464435252184434995138219633936108701587766875993967138713336340580296010484389976619407534314506389379707228116419089675859310622241 

noncomputable def Ns432p255 := BSN.sin_dyadic_bound_f 107925068409 68719476736 4 3 33554432 13533204 Ns432p252 Ns432p116 Ns432p253 Ns432p254 Ns432p119 Ns432p253 33554430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107925068409) (BSN.sinEvenQ 68719476736) 0 3 Ns432p252 Ns432p116 Ns432p253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107925068409) (BSN.sinOddQ 68719476736) 0 3 Ns432p254 Ns432p119 Ns432p253 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p256 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz73) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51020539429) qz48) Bool.false 51020539429 33554432 81 8388608 Bool.false 33554430 33554432 1 6760000 (Ns432p250 rfl) (Enclosure.sfrac_false_div 51020539429 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51020539429) qz48) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns432p251) qz316) 226375608064910080 72057594037927936 Bool.false 33554430 33554432 241 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q3 51020539429 33554432 226375608064910080 72057594037927936 241 Ns432p251 Ns432p103 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554430 33554432 Ns432p251 Ns432p103 107925068409 68719476736 13533204 13520000 (Ns432p255 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns432p257 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz73) Bool.false Ns432p228 Ns432p229 332511752979663141 34611200000000000000000 408164315438 268435456 2579 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz73) (@HAdd.hAdd Real Real Real qz47 qz77 (Enclosure.sfrac Bool.true Ns432p230 Ns432p231)) Bool.false Ns432p228 Ns432p229 332511752979663141 34611200000000000000000 Ns432p232 (Ns432p249 rfl rfl)) 

noncomputable def Ns432p258 := Ns432p227 46699 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 618 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 252304583 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 413 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 220773453 268435456) qz76 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz73) qz73 1) Bool.false 16777215 16777216 8686697 886046720000 268435440 268435456 2632 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz73) qz73 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz73)) Bool.false 16777215 16777216 8686697 886046720000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz73) qz73) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz73)) Bool.false 33554430 33554432 555948608 56706990080000 16777215 16777216 8686697 886046720000 (Ns432p256 rfl rfl) rfl)) rfl) (Ns432p257 rfl) RS433to438.d7 

noncomputable def Ns432p259 := nat_lit 667612968334232894139592035815446976514466411511934961721705259348481 

noncomputable def Ns432p260 := nat_lit 5857392348517444832363348910877342164689436346625561600976499201 

noncomputable def Ns432p261 := nat_lit 2002827190218001647529111380748519174859069855663111634041913825047041 

noncomputable def Ns432p262 := BSN.cos_dyadic_bound_f 93532607 268435456 3 2 268435456 134217728 Ns432p259 Ns432p131 Ns432p260 Ns432p261 Ns432p134 Ns432p260 252304583 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 93532607) qz49 0 2 Ns432p259 Ns432p131 Ns432p260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 93532607) qz50 0 2 Ns432p261 Ns432p134 Ns432p260 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p263 := nat_lit 70923142514880057855265631277575782863204779024272106121616754481063745 

noncomputable def Ns432p264 := nat_lit 20391237029969916076190475114593073954439314947212849155330478466881 

noncomputable def Ns432p265 := nat_lit 185718073155208771661572344957751042521991043315560028562744774294792001 

noncomputable def Ns432p266 := BSN.sin_dyadic_bound_f 259227127 268435456 3 2 268435456 134217728 Ns432p263 Ns432p137 Ns432p264 Ns432p265 Ns432p140 Ns432p264 220773453 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 259227127) qz51 0 2 Ns432p263 Ns432p137 Ns432p264 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 259227127) qz52 0 2 Ns432p265 Ns432p140 Ns432p264 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p267 := nat_lit 10697486330394993932132500012462356882961790016441162593538633704690625 

noncomputable def Ns432p268 := nat_lit 1503501279160100590161136137513009646287021482201153651516187890625 

noncomputable def Ns432p269 := nat_lit 32089451988626661595217177765112044629592796006359085473312868738290625 

noncomputable def Ns432p270 := BSN.cos_dyadic_bound_f 187127655 268435456 3 2 268435456 134217728 Ns432p267 Ns432p131 Ns432p268 Ns432p269 Ns432p134 Ns432p268 205810563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 187127655) qz49 0 2 Ns432p267 Ns432p131 Ns432p268 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 187127655) qz50 0 2 Ns432p269 Ns432p134 Ns432p268 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p271 := nat_lit 22082233787975909394643726623156694522285453940868003916640162712699004363588052016967440493312796177118662656 

noncomputable def Ns432p272 := nat_lit 871683568514489007341798292243696146469029465094156570908284878217177001794361422139649254553384847460322508800 

noncomputable def Ns432p273 := nat_lit 3920727876124929793613324034485680943356347371309875712022236488521269799450771206667491608090660704256 

noncomputable def Ns432p274 := nat_lit 110342676871169861953576072364702175136352815454140056028222782682231284803656340218831513648156925335572975616 

noncomputable def Ns432p275 := nat_lit 30508924898007115256962940228529365126416031278295479981789970737601195062802649774887723909368469661111287808000 

noncomputable def Ns432p276 := BSN.sin_dyadic_bound_f 354362066 268435456 4 3 268435456 134217728 Ns432p271 Ns432p272 Ns432p273 Ns432p274 Ns432p275 Ns432p273 260044244 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 354362066) qz51 0 3 Ns432p271 Ns432p272 Ns432p273 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 354362066) qz52 0 3 Ns432p274 Ns432p275 Ns432p273 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p277 := Ns432p225 79203 BSN.abs_quadSignPos (BSN.cos_quad_nat0 268 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 205810563 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 260044244 268435456) qz76 rfl rfl (Ns432p258 RS433to438.d9 RS433to438.d11 RS433to438.d13 RS433to438.d17 (Ns432p262 rfl rfl) (Ns432p266 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns432p257 rfl) RS433to438.d19 RS433to438.d21 RS433to438.d23 RS433to438.d25 RS433to438.d17 (Ns432p270 rfl rfl) (Ns432p276 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns432p278 := nat_lit 21700906688250559941786241616384827362662401944624426185108319461776914289279110454590546574718580188774400000 

noncomputable def Ns432p279 := nat_lit 3721293175961617274917357023716432392772680191874140647089925200084226568346557151891685376000000000000 

noncomputable def Ns432p280 := nat_lit 108438384429726625273174756214396133342345598326901853152723959060125075565238768954630211882773351759872000000 

noncomputable def Ns432p281 := BSN.sin_dyadic_bound_f 352823760 268435456 4 3 268435456 134217728 Ns432p278 Ns432p272 Ns432p279 Ns432p280 Ns432p275 Ns432p279 259658358 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 352823760) qz51 0 3 Ns432p278 Ns432p272 Ns432p279 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 352823760) qz52 0 3 Ns432p280 Ns432p275 Ns432p279 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p282 := nat_lit 36265860180859061998508051374306686726769671901596357620882963721060986066958240898723096015364861004705693361 

noncomputable def Ns432p283 := nat_lit 17333781529047992042753365590203369418265788861643884440557072667503148183868520853480803657540005789361 

noncomputable def Ns432p284 := nat_lit 181144775941987162179947958662928416395587957175848761706645954557546146980570409681731417895322883763103071921 

noncomputable def Ns432p285 := BSN.sin_dyadic_bound_f 401089331 268435456 4 3 268435456 134217728 Ns432p282 Ns432p272 Ns432p283 Ns432p284 Ns432p275 Ns432p283 267647855 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 401089331) qz51 0 3 Ns432p282 Ns432p272 Ns432p283 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 401089331) qz52 0 3 Ns432p284 Ns432p275 Ns432p283 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p286 := Ns432p223 106802 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 259658358 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267647855 268435456) qz76 rfl rfl (Ns432p277 rfl rfl) (Ns432p257 rfl) RS433to438.d27 RS433to438.d29 RS433to438.d31 RS433to438.d33 RS433to438.d17 (Ns432p281 rfl rfl) (Ns432p285 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p287 := nat_lit 6196707995333787079849126230270766895589135882738502802538670909274785 

noncomputable def Ns432p288 := nat_lit 155746261093769972537564191121668345541375480641076616730595801761 

noncomputable def Ns432p289 := nat_lit 16229221160499100057744555499161621073031146037346469406412288559659681 

noncomputable def Ns432p290 := BSN.sin_dyadic_bound_f 140945821 268435456 3 2 268435456 134217728 Ns432p287 Ns432p137 Ns432p288 Ns432p289 Ns432p140 Ns432p288 134558230 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 140945821) qz51 0 2 Ns432p287 Ns432p137 Ns432p288 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 140945821) qz52 0 2 Ns432p289 Ns432p140 Ns432p288 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p291 := nat_lit 5995761198120349169469090661984823503597995383510055127544806226821020195307191875494287839749606089462890625 

noncomputable def Ns432p292 := nat_lit 1378279482550943179785371022151564098190116766382355018623450749550608508950437004499495029449462890625 

noncomputable def Ns432p293 := nat_lit 36343379904093058772775335733898874206584183867522648418735218179456406427598133271962729686159461065462890625 

noncomputable def Ns432p294 := BSN.cos_dyadic_bound_f 324796575 268435456 4 3 268435456 134217728 Ns432p291 Ns432p125 Ns432p292 Ns432p293 Ns432p128 Ns432p292 94772585 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 324796575) qz49 0 3 Ns432p291 Ns432p125 Ns432p292 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 324796575) qz50 0 3 Ns432p293 Ns432p128 Ns432p292 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p295 := Ns432p221 130916 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134558230 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 94772585 268435456) qz76 rfl rfl (Ns432p286 rfl) (Ns432p257 rfl) RS433to438.d35 RS433to438.d37 RS433to438.d39 RS433to438.d41 RS433to438.d17 (Ns432p290 rfl rfl) (Ns432p294 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p296 := nat_lit 34233203983580863045342371720051959081884976925723951485686910127291696536535238625373271049677874288064987136 

noncomputable def Ns432p297 := nat_lit 14583510069061742700178101604581033443538451482060873438251086034496086502491205775582799201759590875136 

noncomputable def Ns432p298 := nat_lit 171001573219756438633383006710710425903826952752444237611829418124628173268605640232186582120744374449467293696 

noncomputable def Ns432p299 := BSN.sin_dyadic_bound_f 395356156 268435456 4 3 268435456 134217728 Ns432p296 Ns432p272 Ns432p297 Ns432p298 Ns432p275 Ns432p297 267147988 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 395356156) qz51 0 3 Ns432p296 Ns432p272 Ns432p297 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 395356156) qz52 0 3 Ns432p298 Ns432p275 Ns432p297 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p300 := nat_lit 39111212834594948444976588816 

noncomputable def Ns432p301 := BSN.cos_dyadic_bound_f 14062914 268435456 2 1 268435456 134217728 Ns432p300 Ns432p166 Ns432p300 Ns432p300 Ns432p167 Ns432p300 268067173 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14062914) qz49 0 1 Ns432p300 Ns432p166 Ns432p300 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14062914) qz50 0 1 Ns432p300 Ns432p167 Ns432p300 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p302 := Ns432p219 152604 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267147988 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 242 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268067173 268435456) qz76 rfl rfl (Ns432p295 rfl) (Ns432p257 rfl) RS433to438.d43 RS433to438.d45 RS433to438.d47 RS433to438.d49 RS433to438.d17 (Ns432p299 rfl rfl) (Ns432p301 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p303 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz73) qz73 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz73) qz73 11) 5322283 268435456 152604 268435456 5322283 268435456 152604 268435456 2857378928132096 5322283 134217728 38151 33554432 (Ns432p302 rfl) 

noncomputable def Ns432p304 := @Enclosure.Real.IsNear.mulLit_tf qz74 qz75 10012053 33554432 1 33554432 146060300689435 281474976710656 715292562359369 5946158883012608000 1462363471698559760055 9444732965739290427392 

noncomputable abbrev qz87 := (@HPow.hPow Real Real Real qz298 qz325 qz300)

noncomputable def Ns432p305 := @Enclosure.Real.IsNear.mulLit_tf qz53 qz87 1 1 0 1 10012053 33554432 1 33554432 10012053 33554432 1 33554432 

noncomputable abbrev qz88 := qz325

noncomputable def Ns432p306 := @Enclosure.Real.IsNear.sqrt_image qz88 211654210449 1677721600 39633 1677721600 188440116 188440152 16777216 (@Enclosure.Real.IsNear.of_eq qz88 (@HMul.hMul Real Real Real qz29 qz73 qz27) Bool.false 211654210449 1677721600 39633 1677721600 (BSN.t_div_two_pi_mk qz73 792660 1000 qz76) (@Enclosure.Real.IsNear.mulLit_ff qz73 qz27 792660 1000 0 1 5340353 33554432 1 33554432 211654210449 1677721600 39633 1677721600 (Enclosure.Real.IsNear.const Bool.false 792660 1000) RS433to438.d52 rfl)) 

noncomputable abbrev qz536 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 792660 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz474 := qz536

noncomputable abbrev qz336 := qz474

noncomputable abbrev qz89 := qz336

noncomputable def Ns432p307 := @Enclosure.Real.IsNear.sqrt_image qz89 94220067 8388608 9 8388608 56227222 56227228 16777216 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 376880268 33554432 36 33554432 94220067 8388608 9 8388608 (Ns432p306 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz90 := (Real.sqrt qz336)

noncomputable def Ns432p308 := @Enclosure.Real.IsNear.inv_image qz90 56227225 16777216 3 16777216 5006026 5006027 16777216 (@Enclosure.Real.IsNear.recentre' qz90 Bool.false 112454450 33554432 6 33554432 56227225 16777216 3 16777216 (Ns432p307 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns432p309 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz90) Bool.false 10012053 33554432 1 33554432 10012053 33554432 1 33554432 (Ns432p308 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz337 := (@HMul.hMul Real Real Real qz453 qz451 qz469)

noncomputable abbrev qz91 := (@Inv.inv Real Real.instInv (Real.cos qz337))

noncomputable abbrev qz475 := (@HMul.hMul Real Real Real qz524 qz535 qz535)

noncomputable abbrev qz338 := (@HSub.hSub Real Real Real qz456 (@HSub.hSub Real Real Real qz456 qz475 qz469) qz466)

noncomputable abbrev qz92 := (Real.cos (@HMul.hMul Real Real Real qz296 qz293 qz338))

noncomputable def Ns432p310 := @Enclosure.Real.IsNear.of_eq qz75 (@HMul.hMul Real Real Real qz29 qz91 qz92) Bool.false 146060300689435 

noncomputable def Ns432p311 := @Enclosure.Real.IsNear.mulLit_ff qz91 qz92 295802155 33554432 18105 

noncomputable def Ns432p312 := @Enclosure.Real.IsNear.recentre' qz91 Bool.false 295802155 33554432 18105 33554432 295802155 33554432 18105 

noncomputable abbrev qz93 := (Real.cos qz337)

noncomputable def Ns432p313 := @Enclosure.Real.IsNear.recentre' qz93 Bool.false 1903130 16777216 393708608 56706990080000 951565 8388608 6151697 886046720000 

noncomputable abbrev qz94 := qz337

noncomputable abbrev qz339 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns432p314 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24446353) qz339) Bool.false 24446353 16777216 57 8388608 Bool.false 1903130 16777216 1 

noncomputable def Ns432p315 := nat_lit 242874678698107087463171071 

noncomputable abbrev qz95 := qz326

noncomputable def Ns432p316 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz95 884279719003555 140737488355328 1 500000000000000 1945379 8388608 9 8388608 1720259195475416822345 1180591620717411303424 Ns432p315 

noncomputable def Ns432p317 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz22 94220067 8388608 9 8388608 11 1 0 1 1945379 1945379 8388608 9 

noncomputable def Ns432p318 := @Ns432p317 8388608 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 376880268 33554432 36 33554432 94220067 8388608 9 8388608 (Ns432p306 rfl rfl rfl rfl rfl rfl) rfl) qz64 

noncomputable def Ns432p319 := @Enclosure.Real.IsNear.recentre' qz94 Bool.false 1720259195475416822345 1180591620717411303424 Ns432p315 Ns432p185 24446353 16777216 57 8388608 (@Ns432p316 Ns432p185 RS433to438.d51 (Ns432p318 rfl rfl) rfl) 

noncomputable def Ns432p320 := nat_lit 44864767568892284260128530981912296293374301584264587195945679828574660011535303172613158806721 

noncomputable def Ns432p321 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns432p322 := nat_lit 45558450321285110943546474721158676127199421965879983894000130346490605322089296372507841 

noncomputable def Ns432p323 := nat_lit 271693771556371030478980540825296193629930743848429268207974285271980109425293590857584512935105 

noncomputable def Ns432p324 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns432p325 := BSN.cos_dyadic_bound_f 24446353 16777216 4 3 16777216 6760000 Ns432p320 Ns432p321 Ns432p322 Ns432p323 Ns432p324 Ns432p322 1903130 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 24446353) (BSN.cosEvenQ 16777216) 0 3 Ns432p320 Ns432p321 Ns432p322 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 24446353) (BSN.cosOddQ 16777216) 0 3 Ns432p323 Ns432p324 Ns432p322 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p326 := @Enclosure.Real.IsNear.inv_image qz93 951565 8388608 6151697 886046720000 147892025 147910130 16777216 (Ns432p313 (@Ns432p314 6760000 (Ns432p319 rfl) (Enclosure.sfrac_false_div 24446353 16777216) (Ns432p325 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns432p327 := @Enclosure.Real.IsNear.recentre' qz92 Bool.false 987554 16777216 

noncomputable abbrev qz96 := (@HMul.hMul Real Real Real qz296 qz293 qz338)

noncomputable def Ns432p328 := @Enclosure.Real.IsNear.cos_image qz96 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3170683)) (@Nat.cast Real Real.instNatCast 2097152)) Bool.true 3170683 2097152 

noncomputable def Ns432p329 := nat_lit 14973127268807485011944126725 

noncomputable def Ns432p330 := nat_lit 9903520314283042199192993792 

noncomputable def Ns432p331 := nat_lit 596469851535764338054844070613693 

noncomputable def Ns432p332 := @Enclosure.Real.IsNear.recentre' qz96 Bool.true Ns432p329 Ns432p330 Ns432p331 

noncomputable abbrev qz97 := qz338

noncomputable def Ns432p333 := @Enclosure.Real.IsNear.mulLit_ft qz26 qz97 884279719003555 140737488355328 1 500000000000000 16932568899895 

noncomputable abbrev qz340 := (@HSub.hSub Real Real Real qz456 qz475 qz469)

noncomputable abbrev qz98 := qz340

noncomputable def Ns432p334 := @Enclosure.Real.IsNear.subLit_tf qz98 qz68 12534522388791 70368744177664 110514375 70368744177664 1 16 

noncomputable abbrev qz341 := qz475

noncomputable abbrev qz99 := qz341

noncomputable def Ns432p335 := @Enclosure.Real.IsNear.subLit_ff_n qz99 qz95 3784499453641 70368744177664 35016903 70368744177664 1945379 8388608 9 8388608 

noncomputable def Ns432p336 := @Enclosure.Real.IsNear.mulLit_ff qz95 qz95 1945379 8388608 9 8388608 1945379 8388608 9 8388608 3784499453641 70368744177664 

noncomputable def Ns432p337 := nat_lit 757051650565195814312672798780813951621891224105476098707988977967244851589539676241 

noncomputable def Ns432p338 := nat_lit 3466537250751077332112698720796095110148055492926080949987665366995300109908547993600 

noncomputable def Ns432p339 := nat_lit 1032366466449187171766952096633404185497287205393598069244415896765989586452561 

noncomputable def Ns432p340 := nat_lit 4583281475380794383392838241322214803647973325843926949730600622623776469400360566865 

noncomputable def Ns432p341 := nat_lit 315454889818348037222255583592444655023473049856273366448877548396572310001677867417600 

noncomputable def Ns432p342 := BSN.cos_dyadic_bound_f 3170683 2097152 4 3 16777216 6760000 Ns432p337 Ns432p338 Ns432p339 Ns432p340 Ns432p341 Ns432p339 987554 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3170683) (BSN.cosEvenQ 2097152) 0 3 Ns432p337 Ns432p338 Ns432p339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3170683) (BSN.cosOddQ 2097152) 0 3 Ns432p340 Ns432p341 Ns432p339 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p343 := @Ns432p327 569468608 56706990080000 493777 8388608 8897947 886046720000 (@Ns432p328 83 8388608 Bool.false 987554 16777216 1 6760000 (@Ns432p332 Ns432p203 3170683 2097152 83 8388608 (@Ns432p333 70368744177664 110514375 70368744177664 Ns432p329 Ns432p330 Ns432p331 Ns432p203 RS433to438.d51 (@Ns432p334 0 1 270921102398320 16932568899895 70368744177664 110514375 70368744177664 (@Ns432p335 105147194786791292928 12534522388791 70368744177664 110514375 70368744177664 (@Ns432p336 35016903 70368744177664 (Ns432p318 rfl rfl) (Ns432p318 rfl rfl) rfl) (Ns432p318 rfl rfl) rfl rfl) qz70 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3170683 2097152) (BSN.cos_neg_of_bound 3170683 2097152 Bool.false 987554 16777216 1 6760000 (Ns432p342 rfl rfl)) rfl rfl) 

noncomputable def Ns432p344 := @Ns432p304 551125637230187242177 Ns432p215 (Ns432p305 qz71 (@Enclosure.Real.IsNear.of_eq qz87 (@Inv.inv Real Real.instInv qz90) Bool.false 10012053 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz88 (BSN.t_div_two_pi_nonneg qz73 792660 1000 qz76)) Ns432p309) rfl) (@Ns432p310 281474976710656 715292562359369 5946158883012608000 (BSN.correction_mk qz95 (BSN.cos_two_pi_p_ne_zero_mk qz73 792660 1000 11 qz76 rfl rfl (@BSN.floor_sqrt_eq_dec qz73 792660 1000 11 qz76 rfl rfl rfl))) (@Ns432p311 33554432 493777 8388608 8897947 886046720000 146060300689435 281474976710656 715292562359369 5946158883012608000 (@Ns432p312 33554432 (Ns432p326 rfl rfl rfl rfl rfl) rfl) (Ns432p343 rfl) rfl)) 

noncomputable def Ns432p345 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz73) (hardyZApproximantRS₀ qz73) Bool.false 1836885842566689846967 9444732965739290427392 18001272371523572458177 Ns432p215 (@Eq.refl Real (hardyZApproximantRS₀ qz73)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz73) (@HSub.hSub Real Real Real qz72 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz73) qz73 11) (@HMul.hMul Real Real Real qz29 qz74 qz75)) Bool.false 1836885842566689846967 9444732965739290427392 18001272371523572458177 Ns432p215 (BSN.hardyZApproximantRS₀_eq qz73 11 (@BSN.floor_sqrt_eq_dec qz73 792660 1000 11 qz76 rfl rfl rfl)) (@Ns432p217 1836885842566689846967 9444732965739290427392 18001272371523572458177 Ns432p215 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz73) qz73 11) (@HAdd.hAdd Real Real Real qz47 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz73) qz73 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz73) qz73 11)) Bool.false 5322283 134217728 38151 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz73) qz73 11) (Ns432p303 (Ns432p302 rfl) rfl rfl)) (Ns432p344 rfl) rfl rfl)) 

theorem RS433to438.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz73) Bool.false 1836885842566689846967 9444732965739290427392 18001272371523572458177 Ns432p215 := Ns432p345 

noncomputable abbrev qz476 := (@HMul.hMul Real Real Real qz524 (Real.sqrt qz532) qz526)

noncomputable abbrev qz342 := qz476

noncomputable abbrev qz100 := (@HMul.hMul Real Real Real qz296 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz342))

noncomputable abbrev qz343 := (@HMul.hMul Real Real Real qz453 (@HMul.hMul Real Real Real qz453 qz476 qz476) qz476)

noncomputable abbrev qz101 := (@HMul.hMul Real Real Real qz296 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz343))

noncomputable abbrev qz344 := (@HMul.hMul Real Real Real qz453 qz464 qz464)

noncomputable abbrev qz102 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz296 qz344 qz318))

noncomputable def Ns432p346 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz28) (@HAdd.hAdd Real Real Real qz47 (@HAdd.hAdd Real Real Real qz47 qz100 qz101) (@HMul.hMul Real Real Real qz29 (Enclosure.sfrac Bool.false 13 10) qz102)) Bool.false 

noncomputable def Ns432p347 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz47 qz100 qz101) (@HMul.hMul Real Real Real qz29 (Enclosure.sfrac Bool.false 13 10) qz102) 15905001 1073741824 

noncomputable def Ns432p348 := @Enclosure.Real.IsNear.addLit_ff qz100 qz101 1988125 134217728 25 134217728 

noncomputable abbrev qz103 := (@Inv.inv Real Real.instInv qz342)

noncomputable def Ns432p349 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz103 25 4 0 1 79525 33554432 1 33554432 1988125 

noncomputable def Ns432p350 := @Enclosure.Real.IsNear.recentre' qz103 Bool.false 79525 33554432 1 33554432 79525 33554432 1 33554432 

noncomputable def Ns432p351 := @Enclosure.Real.IsNear.mulLit_ff qz58 qz55 56204175 16777216 3 16777216 4226147090433 33554432000 791361 33554432000 9501084425857486311 22517998136852480 57156235777557 

noncomputable def Ns432p352 := @Enclosure.Real.IsNear.sqrt_image qz55 4226147090433 33554432000 791361 33554432000 188285646 188285682 16777216 qz56 

noncomputable def Ns432p353 := @Enclosure.Real.IsNear.sqrt_image qz57 5883927 524288 9 8388608 56204172 56204178 16777216 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 376571328 33554432 36 33554432 5883927 524288 9 8388608 (Ns432p352 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz104 := (@Enclosure.Real.IsNear.recentre' qz318 Bool.false 112408350 33554432 6 33554432 56204175 16777216 3 16777216 (Ns432p353 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns432p354 := @Ns432p351 562949953421312000 qz104 

noncomputable def Ns432p355 := Ns432p354 qz56 

noncomputable abbrev qz105 := qz342

noncomputable def Ns432p356 := @Enclosure.Real.IsNear.inv_image qz105 9501084425857486311 22517998136852480 57156235777557 562949953421312000 39762 39763 16777216 (Ns432p355 rfl) rfl rfl 

noncomputable abbrev qz106 := (@Inv.inv Real Real.instInv qz343)

noncomputable def Ns432p357 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz106 1 32 0 1 1 

noncomputable def Ns432p358 := @Enclosure.Real.IsNear.recentre' qz106 Bool.false 1 33554432 1 33554432 

noncomputable def Ns432p359 := nat_lit 857668641817603732186521201010447675233951597444608298231 

noncomputable def Ns432p360 := nat_lit 11417981541647679048466287755595961091061972992000 

noncomputable def Ns432p361 := nat_lit 9674117324959075756055505430364732938705762003239054993 

noncomputable def Ns432p362 := nat_lit 178405961588244985132285746181186892047843328000000000 

noncomputable abbrev qz107 := qz343

noncomputable def Ns432p363 := @Enclosure.Real.IsNear.inv_image qz107 Ns432p359 Ns432p360 Ns432p361 Ns432p362 0 1 

noncomputable def Ns432p364 := nat_lit 90270605267271680293920895123552388721 

noncomputable def Ns432p365 := nat_lit 507060240091291760598681282150400 

noncomputable def Ns432p366 := nat_lit 27152314346174551610550268810999599 

noncomputable def Ns432p367 := nat_lit 316912650057057350374175801344000000 

noncomputable abbrev qz345 := (@HMul.hMul Real Real Real qz453 qz476 qz476)

noncomputable abbrev qz108 := qz345

noncomputable def Ns432p368 := @Enclosure.Real.IsNear.mulLit_ff qz108 qz105 Ns432p364 Ns432p365 Ns432p366 Ns432p367 9501084425857486311 22517998136852480 57156235777557 

noncomputable def Ns432p369 := @Enclosure.Real.IsNear.mulLit_ff qz105 qz105 9501084425857486311 22517998136852480 57156235777557 562949953421312000 9501084425857486311 22517998136852480 57156235777557 562949953421312000 Ns432p364 

noncomputable def Ns432p370 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz102 13 10 0 1 892491 33554432 1 

noncomputable def Ns432p371 := @Enclosure.Real.IsNear.recentre' qz102 Bool.false 892491 33554432 1 33554432 892491 33554432 

noncomputable abbrev qz109 := qz344

noncomputable def Ns432p372 := @Enclosure.Real.IsNear.mulLit_ff qz109 qz58 3158909287430625 281474976710656 337225059 281474976710656 56204175 16777216 3 16777216 177543890399876147859375 

noncomputable def Ns432p373 := @Enclosure.Real.IsNear.mulLit_ff qz58 qz58 56204175 16777216 3 16777216 56204175 16777216 3 16777216 3158909287430625 281474976710656 337225059 

noncomputable def Ns432p374 := @Ns432p373 281474976710656 qz104 

noncomputable def Ns432p375 := Ns432p374 qz104 

noncomputable def Ns432p376 := @Ns432p372 4722366482869645213696 28430185104388377 4722366482869645213696 (Ns432p375 rfl) qz104 

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz296 qz344 qz318)

noncomputable def Ns432p377 := @Enclosure.Real.IsNear.inv_image qz110 177543890399876147859375 4722366482869645213696 28430185104388377 4722366482869645213696 446245 446246 16777216 (Ns432p376 rfl) 

noncomputable def Ns432p378 := @Ns432p347 201 1073741824 11602383 335544320 13 335544320 17794796630310912 265163133 5368709120 1213 5368709120 (@Ns432p348 1 1073741824 1 1073741824 2134733098057728 15905001 1073741824 201 1073741824 (@Ns432p349 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns432p350 (Ns432p356 rfl rfl rfl rfl) rfl) rfl) (@Ns432p357 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns432p358 1 33554432 1 33554432 (@Ns432p363 16777216 (@Ns432p368 562949953421312000 Ns432p359 Ns432p360 Ns432p361 Ns432p362 (@Ns432p369 Ns432p365 Ns432p366 Ns432p367 (Ns432p355 rfl) (Ns432p355 rfl) rfl) (Ns432p355 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns432p370 33554432 11602383 335544320 13 335544320 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns432p371 1 33554432 (Ns432p377 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS433to438.d56 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz28) Bool.false 265163133 5368709120 1213 5368709120 := @Ns432p346 265163133 5368709120 1213 5368709120 (BSN.hardyZErrorBoundRS₀_mk qz28 791361 1000 qz32 rfl rfl) (Ns432p378 rfl rfl) 

noncomputable def Ns432p379 := nat_lit 79807993560497004111462400 

noncomputable def Ns432p380 := nat_lit 4429027040939245015479569350656 

noncomputable abbrev qz537 := (Enclosure.sfrac Bool.false 793959 1000)

noncomputable abbrev qz477 := qz537

noncomputable abbrev qz346 := qz477

noncomputable abbrev qz111 := qz346

noncomputable abbrev qz538 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 793959 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz478 := qz538

noncomputable abbrev qz347 := qz478

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz296 qz297 (@HPow.hPow Real Real Real qz298 qz347 qz300))

noncomputable abbrev qz539 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 793959 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz479 := qz539

noncomputable abbrev qz348 := qz479

noncomputable abbrev qz113 := (Zeta.RiemannSiegel.correction qz348)

noncomputable def Ns432p381 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz111) qz111 11) (@HMul.hMul Real Real Real qz29 qz112 qz113) 254850489 134217728 152853 134217728 2868194793514250281365 18889465931478580854784 5832784564450549907003 Ns432p379 Ns432p380 

noncomputable def Ns432p382 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz111) qz111 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 793959 1000 193 242 268435456 134217728 4503599627370496 Bool.false 409007873691 2584 

noncomputable def Ns432p383 := Ns432p382 618095470 41 84886744 8 643680110 41 80936328 8 Bool.true 91678998 131129 Bool.true 354703919 Bool.true 6645124 14148475504056880 1 Bool.false 260128839 Bool.true Bool.false 268353210 Bool.true Bool.true 254850489 

noncomputable def Ns432p384 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz111) qz111 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 793959 1000 81 140 268435456 134217728 4503599627370496 Bool.false 409007873691 2584 

noncomputable def Ns432p385 := Ns432p384 558195838 41 94906264 8 589812974 41 89478488 8 Bool.true 137828856 106975 Bool.true 22483962 Bool.true 247405375 14148475504056880 1 Bool.false 22457681 Bool.true Bool.false 162269538 Bool.false Bool.true 91678998 

noncomputable def Ns432p386 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz111) qz111 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 793959 1000 64 13 268435456 134217728 4503599627370496 Bool.false 409007873691 2584 

noncomputable def Ns432p387 := Ns432p386 480971758 41 109588312 8 522351262 41 101459064 8 Bool.true 152600346 79331 Bool.false 149942272 Bool.true 236065367 14148475504056880 1 Bool.false 227635774 Bool.false Bool.false 206793042 Bool.true Bool.true 137828856 

noncomputable def Ns432p388 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz111) qz111 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 793959 1000 269 156 268435456 134217728 4503599627370496 Bool.false 409007873691 2584 

noncomputable def Ns432p389 := Ns432p388 372130544 40 134217720 8 432030192 40 120047984 16 Bool.true 175592637 46773 Bool.false 125630903 Bool.false 215055671 14148475504056880 1 Bool.false 121094611 Bool.true Bool.false 186800212 Bool.false Bool.true 152600346 

noncomputable def Ns432p390 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz111) qz111 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 793959 1000 619 414 268435456 134217728 4503599627370496 Bool.false 409007873691 2584 

noncomputable def Ns432p391 := Ns432p390 186065264 40 189812528 16 294906480 40 154981288 8 Bool.true 268435400 2632 Bool.false 273734653 Bool.false 298044434 14148475504056880 1 Bool.false 228699617 Bool.false Bool.false 119290290 Bool.true Bool.true 175592637 

noncomputable def Ns432p392 := nat_lit 1375088102763170335846301810390912109005608945505934803901 

noncomputable def Ns432p393 := nat_lit 902482386400471730533881190771784389200777491303628800 

noncomputable def Ns432p394 := nat_lit 151437019684151542166261766623520000 

noncomputable def Ns432p395 := nat_lit 721408841784331895646158968999555894080 

noncomputable abbrev qz480 := (@Eq.refl Real qz537)

noncomputable abbrev qz349 := qz480

noncomputable abbrev qz114 := qz349

noncomputable def Ns432p396 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz111 793959 1000 2521484574724 16000000 1587918 4000 2000 Ns432p394 Ns432p395 qz114 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns432p397 := nat_lit 3960253735957930567237349213925826873936153763057092235234880 

noncomputable abbrev qz481 := (Real.log (Enclosure.sfrac Bool.false 2521484574724 16000000))

noncomputable abbrev qz482 := (@HSub.hSub Real Real Real qz528 qz529 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz530 (@Nat.cast Real Real.instNatCast 1587918))))

noncomputable abbrev qz350 := (@HSub.hSub Real Real Real qz456 (@HMul.hMul Real Real Real qz453 (Enclosure.sfrac Bool.false 793959 4000) qz481) (@HMul.hMul Real Real Real qz453 qz458 qz482))

noncomputable abbrev qz351 := (Enclosure.sfrac Bool.false 793959 2000)

noncomputable abbrev qz115 := (@HSub.hSub Real Real Real qz303 (@HSub.hSub Real Real Real qz303 qz350 qz351) (@HMul.hMul Real Real Real qz296 qz351 (Real.log Real.pi)))

noncomputable def Ns432p398 := @Enclosure.Real.IsNear.addLit_ft_p qz115 (Enclosure.sfrac Bool.true Ns432p394 Ns432p395) 5489611510405120611261 3602879701896396800 6661091417858217843 692224000000000000000000 Ns432p394 Ns432p395 0 1 Ns432p397 

noncomputable def Ns432p399 := nat_lit 1842007961323059120023556587520000 

noncomputable abbrev qz116 := (@HSub.hSub Real Real Real qz303 qz350 qz351)

noncomputable abbrev qz117 := (@HMul.hMul Real Real Real qz296 qz351 (Real.log Real.pi))

noncomputable def Ns432p400 := @Enclosure.Real.IsNear.subLit_ff_p qz116 qz117 35634418063417245737649 18014398509481984000 2506124156128707 676000000000000000000 30496569392799 67108864000 793959 134217728000 Ns432p399 5489611510405120611261 3602879701896396800 

noncomputable def Ns432p401 := nat_lit 71268836126834491475298000 

noncomputable abbrev qz118 := qz350

noncomputable abbrev qz119 := qz351

noncomputable def Ns432p402 := @Enclosure.Real.IsNear.subLit_ff_p qz118 qz119 42785764976512149004977 18014398509481984000 2506124156128707 676000000000000000000 793959 2000 0 1 Ns432p401 35634418063417245737649 18014398509481984000 2506124156128707 676000000000000000000 

noncomputable def Ns432p403 := nat_lit 96344977602490866400260341750663479296 

noncomputable def Ns432p404 := nat_lit 57872583076593149853827072 

noncomputable def Ns432p405 := nat_lit 1019229632055371974008951155324109976471257306213992930956994539805544441876480 

noncomputable def Ns432p406 := nat_lit 2882325856287319961696589288026644818947412319778345849355967230322703364096 

noncomputable def Ns432p407 := nat_lit 87564786708401192173795125976722964882645267021945451628107970851696640 

noncomputable def Ns432p408 := BSN.log_dyadic_bound 424332574724 4618636574724 4 3 Ns432p405 134217728 54080000 Ns432p406 Ns432p407 24731980 5042969149448 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 424332574724) (BSN.artanhQ 4618636574724) 0 3 Ns432p406 Ns432p405 Ns432p407 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz352 := qz481

noncomputable abbrev qz120 := qz352

noncomputable abbrev qz353 := (Enclosure.sfrac Bool.false 793959 4000)

noncomputable def Ns432p409 := @Enclosure.Real.IsNear.mulLit_ff qz353 qz120 793959 4000 0 1 53898043070540903 4503599627370496 3125002873 169000000000000000 42792836378243584804977 18014398509481984000 2481124156044207 676000000000000000000 (Enclosure.Real.IsNear.const Bool.false 793959 4000) (BSN.isNear_log_sfrac 2521484574724 16000000 53898043070540903 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2521484574724) qz308)) Bool.false Ns432p404 Ns432p103 1000000919360000 54080000000000000000000 53898043070540903 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2521484574724 16000000 17 5042969149448 4194304000000 24731980 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns432p408 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns432p410 := BSN.arctan_dyadic_bound_f 1000 1587918 1 0 16777216 6760000 0 1 1 0 1 1 10565 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1587918) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1587918) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz483 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz530 (@Nat.cast Real Real.instNatCast 1587918)))

noncomputable abbrev qz354 := qz483

noncomputable abbrev qz121 := qz354

noncomputable def Ns432p411 := @Enclosure.Real.IsNear.subLit_ff_p qz39 qz121 884279719003555 562949953421312 1 2000000000000000 10565 16777216 1 6760000 14829804283884050841600 883925216429475 562949953421312 50000000169 338000000000000000 qz41 (Ns432p410 rfl) rfl rfl 

noncomputable abbrev qz355 := (@HMul.hMul Real Real Real qz453 (Enclosure.sfrac Bool.false 793959 4000) qz481)

noncomputable abbrev qz122 := qz355

noncomputable abbrev qz356 := (@HMul.hMul Real Real Real qz453 qz458 qz482)

noncomputable abbrev qz123 := qz356

noncomputable abbrev qz357 := qz482

noncomputable abbrev qz124 := qz357

noncomputable def Ns432p412 := @Enclosure.Real.IsNear.subLit_ff_p qz122 qz123 42792836378243584804977 18014398509481984000 2481124156044207 676000000000000000000 883925216429475 2251799813685248 50000000169 1352000000000000000 Ns432p403 42785764976512149004977 18014398509481984000 2506124156128707 676000000000000000000 (Ns432p409 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 qz124 1 4 0 1 883925216429475 562949953421312 50000000169 338000000000000000 883925216429475 2251799813685248 50000000169 1352000000000000000 qz46 Ns432p411 rfl) 

noncomputable def Ns432p413 := @Ns432p398 Ns432p392 Ns432p393 6661091417858217843 692224000000000000000000 (@Ns432p400 6661091417858217843 692224000000000000000000 (Ns432p402 (Ns432p412 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 793959 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz119 (Real.log Real.pi) 793959 2000 0 1 38410761 33554432 1 67108864 30496569392799 67108864000 793959 134217728000 (Enclosure.Real.IsNear.const Bool.false 793959 2000) RS433to438.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns432p394 Ns432p395) 

noncomputable def Ns432p414 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz111) Bool.false Ns432p392 Ns432p393 6661091417858217843 692224000000000000000000 51125984211 33554432 81 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz111) (@HAdd.hAdd Real Real Real qz47 qz115 (Enclosure.sfrac Bool.true Ns432p394 Ns432p395)) Bool.false Ns432p392 Ns432p393 6661091417858217843 692224000000000000000000 Ns432p396 (Ns432p413 rfl rfl)) 

noncomputable def Ns432p415 := BSN.cos_dyadic_bound_f 43077037 68719476736 1 0 33554432 13533204 0 1 1 0 1 1 33554425 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 43077037) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 43077037) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns432p416 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz111) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51125984211) qz48) Bool.false 51125984211 33554432 81 8388608 Bool.true 33554425 33554432 1 6760000 (Ns432p414 rfl) (Enclosure.sfrac_false_div 51125984211 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51125984211) qz48) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3031277006222673313792) qz316) 226375608064910080 72057594037927936 Bool.false 33554425 33554432 242 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q2 51125984211 33554432 226375608064910080 72057594037927936 242 3031277006222673313792 Ns432p103 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554425 33554432 3031277006222673313792 Ns432p103 43077037 68719476736 13533204 13520000 (Ns432p415 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns432p417 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz111) Bool.false Ns432p392 Ns432p393 6661091417858217843 692224000000000000000000 409007873691 268435456 2584 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz111) (@HAdd.hAdd Real Real Real qz47 qz115 (Enclosure.sfrac Bool.true Ns432p394 Ns432p395)) Bool.false Ns432p392 Ns432p393 6661091417858217843 692224000000000000000000 Ns432p396 (Ns432p413 rfl rfl)) 

noncomputable def Ns432p418 := Ns432p391 46773 BSN.abs_quadSignPos (BSN.cos_quad_nat3 619 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 228699617 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 414 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 119290290 268435456) qz114 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz111) qz111 1) Bool.true 33554425 33554432 8686697 886046720000 268435400 268435456 2632 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz111) qz111 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz111)) Bool.true 33554425 33554432 8686697 886046720000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz111) qz111) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz111)) Bool.true 33554425 33554432 555948608 56706990080000 33554425 33554432 8686697 886046720000 (Ns432p416 rfl rfl) rfl)) rfl) (Ns432p417 rfl) RS433to438.d7 

noncomputable def Ns432p419 := nat_lit 88189258068027727041791488036429134924910166330901845365071241600596385 

noncomputable def Ns432p420 := nat_lit 31523776347013476405518762372150243737509851697035437862539682412961 

noncomputable def Ns432p421 := nat_lit 230920827873606025195273533527759491075380181582947728104361520896702881 

noncomputable def Ns432p422 := BSN.sin_dyadic_bound_f 273734653 268435456 3 2 268435456 134217728 Ns432p419 Ns432p137 Ns432p420 Ns432p421 Ns432p140 Ns432p420 228699617 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 273734653) qz51 0 2 Ns432p419 Ns432p137 Ns432p420 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 273734653) qz52 0 2 Ns432p421 Ns432p140 Ns432p420 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p423 := nat_lit 4249732051753424743330071599705154806563667029655065678286429209534027258559129384739775754863564927466868736 

noncomputable def Ns432p424 := nat_lit 491328763144007172192796351720374324001584656640382870028445793909770298747210896652832677622665056256 

noncomputable def Ns432p425 := nat_lit 25766171303596300262958386086196124146012109508181552825211115436241629386413162559025255670168662039541452800 

noncomputable def Ns432p426 := BSN.cos_dyadic_bound_f 298044434 268435456 4 3 268435456 134217728 Ns432p423 Ns432p125 Ns432p424 Ns432p425 Ns432p128 Ns432p424 119290290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 298044434) qz49 0 3 Ns432p423 Ns432p125 Ns432p424 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 298044434) qz50 0 3 Ns432p425 Ns432p128 Ns432p424 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p427 := nat_lit 3911416980212713281166558393456197352951302539695258569212283849816385 

noncomputable def Ns432p428 := nat_lit 62054295718267498925295716485026972257978821531329475599011952961 

noncomputable def Ns432p429 := nat_lit 10244086860268800446152250075510969690250708019205102671643106920642881 

noncomputable def Ns432p430 := BSN.sin_dyadic_bound_f 125630903 268435456 3 2 268435456 134217728 Ns432p427 Ns432p137 Ns432p428 Ns432p429 Ns432p140 Ns432p428 121094611 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 125630903) qz51 0 2 Ns432p427 Ns432p137 Ns432p428 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 125630903) qz52 0 2 Ns432p429 Ns432p140 Ns432p428 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p431 := nat_lit 18662888996305764552449298218582717051806043846012942952080107105746241 

noncomputable def Ns432p432 := nat_lit 4575169567867742747055446819652012545423720604972940201901231242561 

noncomputable def Ns432p433 := nat_lit 55979516649781558171853783762108847130327284096828882975836518854753601 

noncomputable def Ns432p434 := BSN.cos_dyadic_bound_f 215055671 268435456 3 2 268435456 134217728 Ns432p431 Ns432p131 Ns432p432 Ns432p433 Ns432p134 Ns432p432 186800212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 215055671) qz49 0 2 Ns432p431 Ns432p131 Ns432p432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 215055671) qz50 0 2 Ns432p433 Ns432p134 Ns432p432 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p435 := Ns432p389 79331 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 269 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 121094611 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 156 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 186800212 268435456) qz114 rfl rfl (Ns432p418 RS433to438.d9 RS433to438.d11 RS433to438.d13 RS433to438.d17 (Ns432p422 rfl rfl) (Ns432p426 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns432p417 rfl) RS433to438.d19 RS433to438.d21 RS433to438.d23 RS433to438.d25 RS433to438.d17 (Ns432p430 rfl rfl) (Ns432p434 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns432p436 := nat_lit 4409509778745038936568679739426133067072921254171900343699120341385216 

noncomputable def Ns432p437 := nat_lit 255501054948528485980343088590298966752767051851086783416983617536 

noncomputable def Ns432p438 := nat_lit 13228018334125219752734078532101218603285258228411998857530527056920576 

noncomputable def Ns432p439 := BSN.cos_dyadic_bound_f 149942272 268435456 3 2 268435456 134217728 Ns432p436 Ns432p131 Ns432p437 Ns432p438 Ns432p134 Ns432p437 227635774 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 149942272) qz49 0 2 Ns432p436 Ns432p131 Ns432p437 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 149942272) qz50 0 2 Ns432p438 Ns432p134 Ns432p437 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p440 := nat_lit 48770397497974451324730423456741680771793239203516397155230292534185025 

noncomputable def Ns432p441 := nat_lit 9644022467548892589478026249091247610093649403535009018304020171841 

noncomputable def Ns432p442 := nat_lit 127716379315461817167244335106110635239518332005413412058621131080682561 

noncomputable def Ns432p443 := BSN.sin_dyadic_bound_f 236065367 268435456 3 2 268435456 134217728 Ns432p440 Ns432p137 Ns432p441 Ns432p442 Ns432p140 Ns432p441 206793042 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 236065367) qz51 0 2 Ns432p440 Ns432p137 Ns432p441 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 236065367) qz52 0 2 Ns432p442 Ns432p140 Ns432p441 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p444 := Ns432p387 106975 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 227635774 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 206793042 268435456) qz114 rfl rfl (Ns432p435 rfl rfl) (Ns432p417 rfl) RS433to438.d27 RS433to438.d29 RS433to438.d31 RS433to438.d33 RS433to438.d17 (Ns432p439 rfl rfl) (Ns432p443 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p445 := nat_lit 255559112051779507795017893136 

noncomputable def Ns432p446 := BSN.sin_dyadic_bound_f 22483962 268435456 2 1 268435456 134217728 Ns432p445 Ns432p143 Ns432p445 Ns432p445 Ns432p144 Ns432p445 22457681 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 22483962) qz51 0 1 Ns432p445 Ns432p143 Ns432p445 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 22483962) qz52 0 1 Ns432p445 Ns432p144 Ns432p445 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p447 := nat_lit 32695788101297241024558628739513119738738828389832747323924293212890625 

noncomputable def Ns432p448 := nat_lit 14036959446226205964418718042519517993820444950628340244293212890625 

noncomputable def Ns432p449 := nat_lit 98059290384999270661747048782454320180228844279596985291284293212890625 

noncomputable def Ns432p450 := BSN.cos_dyadic_bound_f 247405375 268435456 3 2 268435456 134217728 Ns432p447 Ns432p131 Ns432p448 Ns432p449 Ns432p134 Ns432p448 162269538 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 247405375) qz49 0 2 Ns432p447 Ns432p131 Ns432p448 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 247405375) qz50 0 2 Ns432p449 Ns432p134 Ns432p448 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p451 := Ns432p385 131129 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 22457681 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 162269538 268435456) qz114 rfl rfl (Ns432p444 rfl) (Ns432p417 rfl) RS433to438.d35 RS433to438.d37 RS433to438.d39 RS433to438.d41 RS433to438.d17 (Ns432p446 rfl rfl) (Ns432p450 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p452 := nat_lit 22167654047655832853071583141631329769152186711211028448693368195020159909266684167678269273278821379424999361 

noncomputable def Ns432p453 := nat_lit 3966357376444404750399702187123136158165396258739769018173159248305719603323832771813927560334099175361 

noncomputable def Ns432p454 := nat_lit 110769247726018077293564146781466262003415608755197964813803929685352909993211170326438718356723877171837097921 

noncomputable def Ns432p455 := BSN.sin_dyadic_bound_f 354703919 268435456 4 3 268435456 134217728 Ns432p452 Ns432p272 Ns432p453 Ns432p454 Ns432p275 Ns432p453 260128839 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 354703919) qz51 0 3 Ns432p452 Ns432p272 Ns432p453 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 354703919) qz52 0 3 Ns432p454 Ns432p275 Ns432p453 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p456 := nat_lit 1949900082600251920702341376 

noncomputable def Ns432p457 := BSN.cos_dyadic_bound_f 6645124 268435456 2 1 268435456 134217728 Ns432p456 Ns432p166 Ns432p456 Ns432p456 Ns432p167 Ns432p456 268353210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 6645124) qz49 0 1 Ns432p456 Ns432p166 Ns432p456 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 6645124) qz50 0 1 Ns432p456 Ns432p167 Ns432p456 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p458 := Ns432p383 152853 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 260128839 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 242 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268353210 268435456) qz114 rfl rfl (Ns432p451 rfl) (Ns432p417 rfl) RS433to438.d43 RS433to438.d45 RS433to438.d47 RS433to438.d49 RS433to438.d17 (Ns432p455 rfl rfl) (Ns432p457 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p459 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz111) qz111 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz111) qz111 11) 254850489 268435456 152853 268435456 254850489 268435456 152853 268435456 136821814453075968 254850489 134217728 152853 134217728 (Ns432p458 rfl) 

noncomputable def Ns432p460 := @Enclosure.Real.IsNear.mulLit_tf qz112 qz113 10007955 33554432 1 33554432 286591495816503 562949953421312 582693780366413 2378463553205043200 2868194793514250281365 18889465931478580854784 

noncomputable abbrev qz125 := (@HPow.hPow Real Real Real qz298 qz347 qz300)

noncomputable def Ns432p461 := @Enclosure.Real.IsNear.mulLit_tf qz53 qz125 1 1 0 1 10007955 33554432 1 33554432 10007955 33554432 1 33554432 

noncomputable abbrev qz126 := qz347

noncomputable def Ns432p462 := @Enclosure.Real.IsNear.sqrt_image qz126 4240021327527 33554432000 793959 33554432000 188594459 188594495 16777216 (@Enclosure.Real.IsNear.of_eq qz126 (@HMul.hMul Real Real Real qz29 qz111 qz27) Bool.false 4240021327527 33554432000 793959 33554432000 (BSN.t_div_two_pi_mk qz111 793959 1000 qz114) (@Enclosure.Real.IsNear.mulLit_ff qz111 qz27 793959 1000 0 1 5340353 33554432 1 33554432 4240021327527 33554432000 793959 33554432000 (Enclosure.Real.IsNear.const Bool.false 793959 1000) RS433to438.d52 rfl)) 

noncomputable abbrev qz540 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 793959 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz484 := qz540

noncomputable abbrev qz358 := qz484

noncomputable abbrev qz127 := qz358

noncomputable def Ns432p463 := @Enclosure.Real.IsNear.sqrt_image qz127 188594477 16777216 9 8388608 56250244 56250250 16777216 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 377188954 33554432 36 33554432 188594477 16777216 9 8388608 (Ns432p462 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz128 := (Real.sqrt qz358)

noncomputable def Ns432p464 := @Enclosure.Real.IsNear.inv_image qz128 56250247 16777216 3 16777216 5003977 5003978 16777216 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 112500494 33554432 6 33554432 56250247 16777216 3 16777216 (Ns432p463 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns432p465 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz128) Bool.false 10007955 33554432 1 33554432 10007955 33554432 1 33554432 (Ns432p464 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz359 := (@HMul.hMul Real Real Real qz453 qz451 qz479)

noncomputable abbrev qz129 := (@Inv.inv Real Real.instInv (Real.cos qz359))

noncomputable abbrev qz485 := (@HMul.hMul Real Real Real qz524 qz539 qz539)

noncomputable abbrev qz360 := (@HSub.hSub Real Real Real qz456 (@HSub.hSub Real Real Real qz456 qz485 qz479) qz466)

noncomputable abbrev qz130 := (Real.cos (@HMul.hMul Real Real Real qz296 qz293 qz360))

noncomputable def Ns432p466 := @Enclosure.Real.IsNear.of_eq qz113 (@HMul.hMul Real Real Real qz29 qz129 qz130) Bool.false 286591495816503 

noncomputable def Ns432p467 := @Enclosure.Real.IsNear.mulLit_ff qz129 qz130 600811929 33554432 74371 

noncomputable def Ns432p468 := @Enclosure.Real.IsNear.recentre' qz129 Bool.false 600811929 33554432 74371 33554432 600811929 33554432 74371 

noncomputable abbrev qz131 := (Real.cos qz359)

noncomputable def Ns432p469 := @Enclosure.Real.IsNear.recentre' qz131 Bool.false 936982 16777216 1568074432 226827960320000 468491 8388608 24501163 3544186880000 

noncomputable abbrev qz132 := qz359

noncomputable def Ns432p470 := @Enclosure.Real.IsNear.cos_image qz132 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 25416119) qz339) Bool.false 25416119 16777216 227 33554432 Bool.false 936982 16777216 1 

noncomputable def Ns432p471 := nat_lit 242874678698769985600537599 

noncomputable abbrev qz133 := qz348

noncomputable def Ns432p472 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz133 884279719003555 140737488355328 1 500000000000000 4045101 16777216 9 8388608 3577000775620999334055 2361183241434822606848 Ns432p471 

noncomputable def Ns432p473 := @Enclosure.Real.IsNear.subLit_ff_p qz127 qz22 188594477 16777216 9 8388608 11 1 0 1 4045101 4045101 16777216 9 

noncomputable def Ns432p474 := @Ns432p473 8388608 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 377188954 33554432 36 33554432 188594477 16777216 9 8388608 (Ns432p462 rfl rfl rfl rfl rfl rfl) rfl) qz64 

noncomputable def Ns432p475 := @Enclosure.Real.IsNear.recentre' qz132 Bool.false 3577000775620999334055 2361183241434822606848 Ns432p471 Ns432p185 25416119 16777216 227 33554432 (@Ns432p472 Ns432p185 RS433to438.d51 (Ns432p474 rfl rfl) rfl) 

noncomputable def Ns432p476 := nat_lit 52442314281093379112116813027275861002861201804481321076013444517944812967414225146096227126241 

noncomputable def Ns432p477 := nat_lit 72662581426889948111364006162883085031750429063798301619533525957119574064853545982036961 

noncomputable def Ns432p478 := nat_lit 317486801179811403361168728330886739766818836395015975295109864569847029391190254893167335115745 

noncomputable def Ns432p479 := BSN.cos_dyadic_bound_f 25416119 16777216 4 3 16777216 6760000 Ns432p476 Ns432p321 Ns432p477 Ns432p478 Ns432p324 Ns432p477 936982 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 25416119) (BSN.cosEvenQ 16777216) 0 3 Ns432p476 Ns432p321 Ns432p477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 25416119) (BSN.cosOddQ 16777216) 0 3 Ns432p478 Ns432p324 Ns432p477 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p480 := @Enclosure.Real.IsNear.inv_image qz131 468491 8388608 24501163 3544186880000 300368779 300443150 16777216 (Ns432p469 (@Ns432p470 6760000 (Ns432p475 rfl) (Enclosure.sfrac_false_div 25416119 16777216) (Ns432p479 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns432p481 := @Enclosure.Real.IsNear.recentre' qz130 Bool.false 477007 16777216 

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz296 qz293 qz360)

noncomputable def Ns432p482 := @Enclosure.Real.IsNear.cos_image qz134 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 25876517)) qz339) Bool.true 25876517 16777216 

noncomputable def Ns432p483 := nat_lit 61099198562310202156603575205 

noncomputable def Ns432p484 := nat_lit 39614081257132168796771975168 

noncomputable def Ns432p485 := nat_lit 1509917632106737457893475452440421 

noncomputable def Ns432p486 := @Enclosure.Real.IsNear.recentre' qz134 Bool.true Ns432p483 Ns432p484 Ns432p485 

noncomputable def Ns432p487 := nat_lit 151115727451828646838272000000000000000 

noncomputable abbrev qz135 := qz360

noncomputable def Ns432p488 := @Enclosure.Real.IsNear.mulLit_ft qz26 qz135 884279719003555 140737488355328 1 500000000000000 69094877163031 

noncomputable abbrev qz361 := (@HSub.hSub Real Real Real qz456 qz485 qz479)

noncomputable abbrev qz136 := qz361

noncomputable def Ns432p489 := @Enclosure.Real.IsNear.subLit_tf qz136 qz68 51502691118615 281474976710656 55951731 35184372088832 1 16 

noncomputable abbrev qz362 := qz485

noncomputable abbrev qz137 := qz362

noncomputable def Ns432p490 := @Enclosure.Real.IsNear.subLit_ff_n qz137 qz133 16362842100201 281474976710656 18202995 35184372088832 4045101 16777216 9 8388608 

noncomputable def Ns432p491 := @Enclosure.Real.IsNear.mulLit_ff qz133 qz133 4045101 16777216 9 8388608 4045101 16777216 9 8388608 16362842100201 281474976710656 

noncomputable def Ns432p492 := nat_lit 56359783731287880343613653746207679296040935320168042060709842336257893260130447466093681049041 

noncomputable def Ns432p493 := nat_lit 90130096182877145675770749564521980906661651477774349879615723307325588812076447997623761 

noncomputable def Ns432p494 := nat_lit 341150317962497394334385523697983778224117303341696882520664963698540047785522266837134682619345 

noncomputable def Ns432p495 := BSN.cos_dyadic_bound_f 25876517 16777216 4 3 16777216 6760000 Ns432p492 Ns432p321 Ns432p493 Ns432p494 Ns432p324 Ns432p493 477007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 25876517) (BSN.cosEvenQ 16777216) 0 3 Ns432p492 Ns432p321 Ns432p493 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 25876517) (BSN.cosOddQ 16777216) 0 3 Ns432p494 Ns432p324 Ns432p493 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p496 := @Ns432p481 144057152 14176747520000 477007 16777216 2250893 221511680000 (@Ns432p482 21 2097152 Bool.false 477007 16777216 1 6760000 (@Ns432p486 Ns432p487 25876517 16777216 21 2097152 (@Ns432p488 281474976710656 55951731 35184372088832 Ns432p483 Ns432p484 Ns432p485 Ns432p487 RS433to438.d51 (@Ns432p489 0 1 1105518034608496 69094877163031 281474976710656 55951731 35184372088832 (@Ns432p490 864071773478285475840 51502691118615 281474976710656 55951731 35184372088832 (@Ns432p491 18202995 35184372088832 (Ns432p474 rfl rfl) (Ns432p474 rfl rfl) rfl) (Ns432p474 rfl rfl) rfl rfl) qz70 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 25876517 16777216) (BSN.cos_neg_of_bound 25876517 16777216 Bool.false 477007 16777216 1 6760000 (Ns432p495 rfl rfl)) rfl rfl) 

noncomputable def Ns432p497 := @Ns432p460 5832784564450549907003 Ns432p379 (Ns432p461 qz71 (@Enclosure.Real.IsNear.of_eq qz125 (@Inv.inv Real Real.instInv qz128) Bool.false 10007955 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz126 (BSN.t_div_two_pi_nonneg qz111 793959 1000 qz114)) Ns432p465) rfl) (@Ns432p466 562949953421312 582693780366413 2378463553205043200 (BSN.correction_mk qz133 (BSN.cos_two_pi_p_ne_zero_mk qz111 793959 1000 11 qz114 rfl rfl (@BSN.floor_sqrt_eq_dec qz111 793959 1000 11 qz114 rfl rfl rfl))) (@Ns432p467 33554432 477007 16777216 2250893 221511680000 286591495816503 562949953421312 582693780366413 2378463553205043200 (@Ns432p468 33554432 (Ns432p480 rfl rfl rfl rfl rfl) rfl) (Ns432p496 rfl) rfl)) 

noncomputable def Ns432p498 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz111) (hardyZApproximantRS₀ qz111) Bool.true 32998822934472896274027 18889465931478580854784 96721606938963166969403 Ns432p379 (@Eq.refl Real (hardyZApproximantRS₀ qz111)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz111) (@HSub.hSub Real Real Real qz72 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz111) qz111 11) (@HMul.hMul Real Real Real qz29 qz112 qz113)) Bool.true 32998822934472896274027 18889465931478580854784 96721606938963166969403 Ns432p379 (BSN.hardyZApproximantRS₀_eq qz111 11 (@BSN.floor_sqrt_eq_dec qz111 793959 1000 11 qz114 rfl rfl rfl)) (@Ns432p381 32998822934472896274027 18889465931478580854784 96721606938963166969403 Ns432p379 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz111) qz111 11) (@HAdd.hAdd Real Real Real qz47 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz111) qz111 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz111) qz111 11)) Bool.true 254850489 134217728 152853 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz111) qz111 11) (Ns432p459 (Ns432p458 rfl) rfl rfl)) (Ns432p497 rfl) rfl rfl)) 

theorem RS433to438.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz111) Bool.true 32998822934472896274027 18889465931478580854784 96721606938963166969403 Ns432p379 := Ns432p498 

noncomputable def Ns432p499 := nat_lit 1374242652027056027355727 

noncomputable def Ns432p500 := nat_lit 449938732045861319351845519360 

noncomputable abbrev qz541 := (Enclosure.sfrac Bool.false 795257 1000)

noncomputable abbrev qz486 := qz541

noncomputable abbrev qz363 := qz486

noncomputable abbrev qz138 := qz363

noncomputable abbrev qz542 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 795257 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz487 := qz542

noncomputable abbrev qz364 := qz487

noncomputable abbrev qz139 := (@HMul.hMul Real Real Real qz296 qz297 (@HPow.hPow Real Real Real qz298 qz364 qz300))

noncomputable abbrev qz543 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 795257 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz488 := qz543

noncomputable abbrev qz365 := qz488

noncomputable abbrev qz140 := (Zeta.RiemannSiegel.correction qz365)

noncomputable def Ns432p501 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (@HMul.hMul Real Real Real qz29 qz139 qz140) 21320017 16777216 76549 67108864 2814233140100070261477 18889465931478580854784 919070135691323897563727 Ns432p77 Ns432p500 

noncomputable def Ns432p502 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 795257 1000 193 241 268435456 134217728 4503599627370496 Bool.false 409851067121 2588 

noncomputable def Ns432p503 := Ns432p502 618095470 41 84886744 8 643680110 41 80936328 8 Bool.false 329621879 131338 Bool.true 313798409 Bool.true 420605905 14148475504056880 1 Bool.false 247056220 Bool.true Bool.false 268433396 Bool.true Bool.false 170560136 

noncomputable def Ns432p504 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 795257 1000 80 140 268435456 134217728 4503599627370496 Bool.false 409851067121 2588 

noncomputable def Ns432p505 := Ns432p504 558195838 41 94906264 8 589812974 41 89478488 8 Bool.false 224174602 107144 Bool.true 325486158 Bool.true 169789186 14148475504056880 1 Bool.false 94127098 Bool.false Bool.false 216504964 Bool.false Bool.false 329621879 

noncomputable def Ns432p506 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 795257 1000 64 13 268435456 134217728 4503599627370496 Bool.false 409851067121 2588 

noncomputable def Ns432p507 := Ns432p506 480971758 41 109588312 8 522351262 41 101459064 8 Bool.false 229229893 79455 Bool.false 368834360 Bool.true 70883875 14148475504056880 1 Bool.false 52482817 Bool.false Bool.false 70062962 Bool.true Bool.false 224174602 

noncomputable def Ns432p508 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 795257 1000 270 157 268435456 134217728 4503599627370496 Bool.false 409851067121 2588 

noncomputable def Ns432p509 := Ns432p508 372130544 40 134217720 8 432030192 40 120047984 16 Bool.false 393091396 46844 Bool.false 64141459 Bool.false 75816483 14148475504056880 1 Bool.false 260808689 Bool.true Bool.false 74812497 Bool.true Bool.false 229229893 

noncomputable def Ns432p510 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz138) qz138 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 795257 1000 621 415 268435456 134217728 4503599627370496 Bool.false 409851067121 2588 

noncomputable def Ns432p511 := Ns432p510 186065264 40 189812528 16 294906480 40 154981288 8 Bool.false 268435448 2632 Bool.false 32100514 Bool.false 336791825 14148475504056880 1 Bool.false 32024061 Bool.true Bool.false 255131732 Bool.false Bool.false 393091396 

noncomputable def Ns432p512 := nat_lit 62617249223826326615178692642079968498174576176429503345959 

noncomputable def Ns432p513 := nat_lit 41011702048101086511060854978586505952957650691948544000 

noncomputable def Ns432p514 := nat_lit 152678953657909075308875728667360000 

noncomputable def Ns432p515 := nat_lit 728514174285896247892339782811648269120 

noncomputable abbrev qz489 := (@Eq.refl Real qz541)

noncomputable abbrev qz366 := qz489

noncomputable abbrev qz141 := qz366

noncomputable def Ns432p516 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz138 795257 1000 2529735784196 16000000 1590514 4000 2000 Ns432p514 Ns432p515 qz141 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns432p517 := nat_lit 20037519751624424516857181645465589919415864376457441070706880 

noncomputable abbrev qz490 := (Real.log (Enclosure.sfrac Bool.false 2529735784196 16000000))

noncomputable abbrev qz491 := (@HSub.hSub Real Real Real qz528 qz529 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz530 (@Nat.cast Real Real.instNatCast 1590514))))

noncomputable abbrev qz367 := (@HSub.hSub Real Real Real qz456 (@HMul.hMul Real Real Real qz453 (Enclosure.sfrac Bool.false 795257 4000) qz490) (@HMul.hMul Real Real Real qz453 qz458 qz491))

noncomputable abbrev qz368 := (Enclosure.sfrac Bool.false 795257 2000)

noncomputable abbrev qz142 := (@HSub.hSub Real Real Real qz303 (@HSub.hSub Real Real Real qz303 qz367 qz368) (@HMul.hMul Real Real Real qz296 qz368 (Real.log Real.pi)))

noncomputable def Ns432p518 := @Enclosure.Real.IsNear.addLit_ft_p qz142 (Enclosure.sfrac Bool.true Ns432p514 Ns432p515) 27504643299061557314799 18014398509481984000 39478931471298981 4096000000000000000000 Ns432p514 Ns432p515 0 1 Ns432p517 

noncomputable def Ns432p519 := nat_lit 1845805366525233377467051278336000 

noncomputable abbrev qz143 := (@HSub.hSub Real Real Real qz303 qz367 qz368)

noncomputable abbrev qz144 := (@HMul.hMul Real Real Real qz296 qz368 (Real.log Real.pi))

noncomputable def Ns432p520 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz144 35704387242020555932911 18014398509481984000 14853138519869 4000000000000000000 30546426560577 67108864000 795257 134217728000 Ns432p519 27504643299061557314799 18014398509481984000 

noncomputable def Ns432p521 := nat_lit 14281754896808222373164400 

noncomputable abbrev qz145 := qz367

noncomputable abbrev qz146 := qz368

noncomputable def Ns432p522 := @Enclosure.Real.IsNear.subLit_ff_p qz145 qz146 8573485099949622601571 3602879701896396800 14853138519869 4000000000000000000 795257 2000 0 1 Ns432p521 35704387242020555932911 18014398509481984000 14853138519869 4000000000000000000 

noncomputable def Ns432p523 := nat_lit 19305772150699810001408430294704324608 

noncomputable def Ns432p524 := nat_lit 57888381379826792383119360 

noncomputable def Ns432p525 := nat_lit 1030203685541310264714156685443544335014683521104302594025897446925124305326080 

noncomputable def Ns432p526 := nat_lit 3017520887198919942081209376813964085215831064018525255063820229080659030016 

noncomputable def Ns432p527 := nat_lit 98290755202555014569660771707521697519219055145822876998721000112189440 

noncomputable def Ns432p528 := BSN.log_dyadic_bound 432583784196 4626887784196 4 3 Ns432p525 134217728 54080000 Ns432p526 Ns432p527 25170471 5059471568392 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 432583784196) (BSN.artanhQ 4626887784196) 0 3 Ns432p526 Ns432p525 Ns432p527 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz369 := qz490

noncomputable abbrev qz147 := qz369

noncomputable abbrev qz370 := (Enclosure.sfrac Bool.false 795257 4000)

noncomputable def Ns432p529 := @Enclosure.Real.IsNear.mulLit_ff qz370 qz147 795257 4000 0 1 53912756386983015 4503599627370496 3125002873 169000000000000000 8574899381208590311971 3602879701896396800 2485180409773361 676000000000000000000 (Enclosure.Real.IsNear.const Bool.false 795257 4000) (BSN.isNear_log_sfrac 2529735784196 16000000 53912756386983015 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2529735784196) qz308)) Bool.false Ns432p524 Ns432p103 1000000919360000 54080000000000000000000 53912756386983015 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2529735784196 16000000 17 5059471568392 4194304000000 25170471 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns432p528 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns432p530 := BSN.arctan_dyadic_bound_f 1000 1590514 1 0 16777216 6760000 0 1 1 0 1 1 10548 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1590514) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1590514) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz492 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz530 (@Nat.cast Real Real.instNatCast 1590514)))

noncomputable abbrev qz371 := qz492

noncomputable abbrev qz148 := qz371

noncomputable def Ns432p531 := @Enclosure.Real.IsNear.subLit_ff_p qz39 qz148 884279719003555 562949953421312 1 2000000000000000 10548 16777216 1 6760000 14829813854033259003904 883925786854819 562949953421312 50000000169 338000000000000000 qz41 (Ns432p530 rfl) rfl rfl 

noncomputable abbrev qz372 := (@HMul.hMul Real Real Real qz453 (Enclosure.sfrac Bool.false 795257 4000) qz490)

noncomputable abbrev qz149 := qz372

noncomputable abbrev qz373 := (@HMul.hMul Real Real Real qz453 qz458 qz491)

noncomputable abbrev qz150 := qz373

noncomputable abbrev qz374 := qz491

noncomputable abbrev qz151 := qz374

noncomputable def Ns432p532 := @Enclosure.Real.IsNear.subLit_ff_p qz149 qz150 8574899381208590311971 3602879701896396800 2485180409773361 676000000000000000000 883925786854819 2251799813685248 50000000169 1352000000000000000 Ns432p523 8573485099949622601571 3602879701896396800 14853138519869 4000000000000000000 (Ns432p529 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 qz151 1 4 0 1 883925786854819 562949953421312 50000000169 338000000000000000 883925786854819 2251799813685248 50000000169 1352000000000000000 qz46 Ns432p531 rfl) 

noncomputable def Ns432p533 := @Ns432p518 Ns432p512 Ns432p513 39478931471298981 4096000000000000000000 (@Ns432p520 39478931471298981 4096000000000000000000 (Ns432p522 (Ns432p532 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 795257 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz146 (Real.log Real.pi) 795257 2000 0 1 38410761 33554432 1 67108864 30546426560577 67108864000 795257 134217728000 (Enclosure.Real.IsNear.const Bool.false 795257 2000) RS433to438.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns432p514 Ns432p515) 

noncomputable def Ns432p534 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz138) Bool.false Ns432p512 Ns432p513 39478931471298981 4096000000000000000000 25615691695 16777216 81 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz138) (@HAdd.hAdd Real Real Real qz47 qz142 (Enclosure.sfrac Bool.true Ns432p514 Ns432p515)) Bool.false Ns432p512 Ns432p513 39478931471298981 4096000000000000000000 Ns432p516 (Ns432p533 rfl rfl)) 

noncomputable def Ns432p535 := nat_lit 2417851639229258349412352 

noncomputable def Ns432p536 := BSN.cos_dyadic_bound_f 11992356 68719476736 1 0 33554432 13533204 0 1 1 0 1 1 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 11992356) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 11992356) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns432p537 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz138) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 25615691695) qz339) Bool.false 25615691695 16777216 81 8388608 Bool.false 33554431 33554432 1 6760000 (Ns432p534 rfl) (Enclosure.sfrac_false_div 25615691695 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 25615691695) qz339) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 421943543333786746880) (@Nat.cast Real Real.instNatCast Ns432p535)) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 243 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q0 25615691695 16777216 226375608064910080 72057594037927936 243 421943543333786746880 Ns432p535 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554431 33554432 421943543333786746880 Ns432p535 11992356 68719476736 13533204 13520000 (Ns432p536 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns432p538 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz138) Bool.false Ns432p512 Ns432p513 39478931471298981 4096000000000000000000 409851067121 268435456 2588 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz138) (@HAdd.hAdd Real Real Real qz47 qz142 (Enclosure.sfrac Bool.true Ns432p514 Ns432p515)) Bool.false Ns432p512 Ns432p513 39478931471298981 4096000000000000000000 Ns432p516 (Ns432p533 rfl rfl)) 

noncomputable def Ns432p539 := Ns432p511 46844 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 621 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 32024061 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 415 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 255131732 268435456) qz141 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 1) Bool.false 33554431 33554432 8686697 886046720000 268435448 268435456 2632 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz138)) Bool.false 33554431 33554432 8686697 886046720000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz138) qz138) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz138)) Bool.false 33554431 33554432 555948608 56706990080000 33554431 33554432 8686697 886046720000 (Ns432p537 rfl rfl) rfl)) rfl) (Ns432p538 rfl) RS433to438.d7 

noncomputable def Ns432p540 := nat_lit 1061812774320414638531729126416 

noncomputable def Ns432p541 := BSN.sin_dyadic_bound_f 32100514 268435456 2 1 268435456 134217728 Ns432p540 Ns432p143 Ns432p540 Ns432p540 Ns432p144 Ns432p540 32024061 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32100514) qz51 0 1 Ns432p540 Ns432p143 Ns432p540 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32100514) qz52 0 1 Ns432p540 Ns432p144 Ns432p540 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p542 := nat_lit 18014409794874555815995238317644594898183211652053995234247392695232660238793857075184133189517324674087890625 

noncomputable def Ns432p543 := nat_lit 2129798393447086995921102963908184542322358924321742841296295360445679850476085476274549961090087890625 

noncomputable def Ns432p544 := nat_lit 90026451949195838800223277064365187712293071136806749505394853827297262973382448960274636842986779010087890625 

noncomputable def Ns432p545 := BSN.sin_dyadic_bound_f 336791825 268435456 4 3 268435456 134217728 Ns432p542 Ns432p272 Ns432p543 Ns432p544 Ns432p275 Ns432p543 255131732 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 336791825) qz51 0 3 Ns432p542 Ns432p272 Ns432p543 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 336791825) qz52 0 3 Ns432p544 Ns432p275 Ns432p543 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p546 := nat_lit 16926039019142116368622631039761 

noncomputable def Ns432p547 := BSN.cos_dyadic_bound_f 64141459 268435456 2 1 268435456 134217728 Ns432p546 Ns432p166 Ns432p546 Ns432p546 Ns432p167 Ns432p546 260808689 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 64141459) qz49 0 1 Ns432p546 Ns432p166 Ns432p546 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 64141459) qz50 0 1 Ns432p546 Ns432p167 Ns432p546 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p548 := nat_lit 33041103049596143294567735725521 

noncomputable def Ns432p549 := BSN.sin_dyadic_bound_f 75816483 268435456 2 1 268435456 134217728 Ns432p548 Ns432p143 Ns432p548 Ns432p548 Ns432p144 Ns432p548 74812497 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 75816483) qz51 0 1 Ns432p548 Ns432p143 Ns432p548 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 75816483) qz52 0 1 Ns432p548 Ns432p144 Ns432p548 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p550 := Ns432p509 79455 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 270 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 260808689 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 157 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 74812497 268435456) qz141 rfl rfl (Ns432p539 RS433to438.d9 RS433to438.d11 RS433to438.d13 RS433to438.d17 (Ns432p541 rfl rfl) (Ns432p545 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns432p538 rfl) RS433to438.d19 RS433to438.d21 RS433to438.d23 RS433to438.d25 RS433to438.d17 (Ns432p547 rfl rfl) (Ns432p549 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns432p551 := nat_lit 9979089675281682075600996927514265929432899729248265128849539884854874375632470798162070947844381999104000000 

noncomputable def Ns432p552 := nat_lit 6338353678888890296943604340899216641954035573259810842570750849889886414182492817321885696000000000000 

noncomputable def Ns432p553 := nat_lit 60454333748732480347788632015506856266301025889248923528528305891532675964664275529451980992220944243097600000 

noncomputable def Ns432p554 := BSN.cos_dyadic_bound_f 368834360 268435456 4 3 268435456 134217728 Ns432p551 Ns432p125 Ns432p552 Ns432p553 Ns432p128 Ns432p552 52482817 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 368834360) qz49 0 3 Ns432p551 Ns432p125 Ns432p552 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 368834360) qz50 0 3 Ns432p553 Ns432p128 Ns432p552 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p555 := nat_lit 25245838763735366591718994140625 

noncomputable def Ns432p556 := BSN.sin_dyadic_bound_f 70883875 268435456 2 1 268435456 134217728 Ns432p555 Ns432p143 Ns432p555 Ns432p555 Ns432p144 Ns432p555 70062962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 70883875) qz51 0 1 Ns432p555 Ns432p143 Ns432p555 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 70883875) qz52 0 1 Ns432p555 Ns432p144 Ns432p555 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p557 := Ns432p507 107144 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 52482817 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 70062962 268435456) qz141 rfl rfl (Ns432p550 rfl rfl) (Ns432p538 rfl) RS433to438.d27 RS433to438.d29 RS433to438.d31 RS433to438.d33 RS433to438.d17 (Ns432p554 rfl rfl) (Ns432p556 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p558 := nat_lit 6046908200695748035824657366494818326920264556162318828677219217056757447444045949773631651405291220328124416 

noncomputable def Ns432p559 := nat_lit 1413807521731771111616796028274308940757325730040844547816906012037578932766266678786955955603642126336 

noncomputable def Ns432p560 := nat_lit 36653142826247197401573264945950116561047368924789320195061560089561729069644111517234978843426796098713948160 

noncomputable def Ns432p561 := BSN.cos_dyadic_bound_f 325486158 268435456 4 3 268435456 134217728 Ns432p558 Ns432p125 Ns432p559 Ns432p560 Ns432p128 Ns432p559 94127098 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 325486158) qz49 0 3 Ns432p558 Ns432p125 Ns432p559 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 325486158) qz50 0 3 Ns432p560 Ns432p128 Ns432p559 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p562 := nat_lit 7250204822151440393108748040002154926908126835326458432873639154811136 

noncomputable def Ns432p563 := nat_lit 690685295337190867040536676073502942986467676734597186068670054656 

noncomputable def Ns432p564 := nat_lit 21749233095863646797592163046654317774838407570625906104248780124324096 

noncomputable def Ns432p565 := BSN.cos_dyadic_bound_f 169789186 268435456 3 2 268435456 134217728 Ns432p562 Ns432p131 Ns432p563 Ns432p564 Ns432p134 Ns432p563 216504964 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 169789186) qz49 0 2 Ns432p562 Ns432p131 Ns432p563 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 169789186) qz50 0 2 Ns432p564 Ns432p134 Ns432p563 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p566 := Ns432p505 131338 BSN.abs_quadSignPos (BSN.cos_quad_nat0 80 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 94127098 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 216504964 268435456) qz141 rfl rfl (Ns432p557 rfl) (Ns432p538 rfl) RS433to438.d35 RS433to438.d37 RS433to438.d39 RS433to438.d41 RS433to438.d17 (Ns432p561 rfl rfl) (Ns432p565 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p567 := nat_lit 152339441759033575101816134181592329440940267145528630978727662401785665 

noncomputable def Ns432p568 := nat_lit 94016893812255216526114537465703439994863080746225535877374785523521 

noncomputable def Ns432p569 := nat_lit 398832034397963331106571404081606866775804254678985858838580509018591041 

noncomputable def Ns432p570 := BSN.sin_dyadic_bound_f 313798409 268435456 3 2 268435456 134217728 Ns432p567 Ns432p137 Ns432p568 Ns432p569 Ns432p140 Ns432p568 247056220 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 313798409) qz51 0 2 Ns432p567 Ns432p137 Ns432p568 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 313798409) qz52 0 2 Ns432p569 Ns432p140 Ns432p568 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p571 := nat_lit 43871719611299407798044292094840691327613517260559729467486019217343927148278221774533935402336227998194290625 

noncomputable def Ns432p572 := nat_lit 30655216443876231320375656077742381306004351144801048536451015618363843453797015689966497166152587890625 

noncomputable def Ns432p573 := nat_lit 219088722639961612164554848677433767667513639426668782744864855937376211534962340376252720835864301556619890625 

noncomputable def Ns432p574 := BSN.sin_dyadic_bound_f 420605905 268435456 4 3 268435456 134217728 Ns432p571 Ns432p272 Ns432p572 Ns432p573 Ns432p275 Ns432p572 268433396 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 420605905) qz51 0 3 Ns432p571 Ns432p272 Ns432p572 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 420605905) qz52 0 3 Ns432p573 Ns432p275 Ns432p572 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p575 := Ns432p503 153098 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 247056220 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268433396 268435456) qz141 rfl rfl (Ns432p566 rfl) (Ns432p538 rfl) RS433to438.d43 RS433to438.d45 RS433to438.d47 RS433to438.d49 RS433to438.d17 (Ns432p570 rfl rfl) (Ns432p574 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p576 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) 170560136 268435456 153098 268435456 170560136 268435456 153098 268435456 91568775765164032 21320017 16777216 76549 67108864 (Ns432p575 rfl) 

noncomputable def Ns432p577 := @Enclosure.Real.IsNear.mulLit_tf qz139 qz140 10003869 33554432 1 33554432 281314473440233 562949953421312 459354326337243723 59461588830126080000 2814233140100070261477 18889465931478580854784 

noncomputable abbrev qz152 := (@HPow.hPow Real Real Real qz298 qz364 qz300)

noncomputable def Ns432p578 := @Enclosure.Real.IsNear.mulLit_tf qz53 qz152 1 1 0 1 10003869 33554432 1 33554432 10003869 33554432 1 33554432 

noncomputable abbrev qz153 := qz364

noncomputable def Ns432p579 := @Enclosure.Real.IsNear.sqrt_image qz153 4246953105721 33554432000 795257 33554432000 188748557 188748594 16777216 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz29 qz138 qz27) Bool.false 4246953105721 33554432000 795257 33554432000 (BSN.t_div_two_pi_mk qz138 795257 1000 qz141) (@Enclosure.Real.IsNear.mulLit_ff qz138 qz27 795257 1000 0 1 5340353 33554432 1 33554432 4246953105721 33554432000 795257 33554432000 (Enclosure.Real.IsNear.const Bool.false 795257 1000) RS433to438.d52 rfl)) 

noncomputable abbrev qz544 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 795257 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz493 := qz544

noncomputable abbrev qz375 := qz493

noncomputable abbrev qz154 := qz375

noncomputable def Ns432p580 := @Enclosure.Real.IsNear.sqrt_image qz154 377497151 33554432 37 33554432 56273220 56273226 16777216 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 377497151 33554432 37 33554432 377497151 33554432 37 33554432 (Ns432p579 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz155 := (Real.sqrt qz375)

noncomputable def Ns432p581 := @Enclosure.Real.IsNear.inv_image qz155 56273223 16777216 3 16777216 5001934 5001935 16777216 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 112546446 33554432 6 33554432 56273223 16777216 3 16777216 (Ns432p580 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns432p582 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz155) Bool.false 10003869 33554432 1 33554432 10003869 33554432 1 33554432 (Ns432p581 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz376 := (Real.cos (@HMul.hMul Real Real Real qz453 qz451 qz488))

noncomputable abbrev qz156 := (@Inv.inv Real Real.instInv qz376)

noncomputable abbrev qz494 := (@HMul.hMul Real Real Real qz524 qz543 qz543)

noncomputable abbrev qz377 := (@HSub.hSub Real Real Real qz456 (@HSub.hSub Real Real Real qz456 qz494 qz488) qz466)

noncomputable abbrev qz157 := (Real.cos (@HMul.hMul Real Real Real qz296 qz293 qz377))

noncomputable def Ns432p583 := @Enclosure.Real.IsNear.of_eq qz140 (@HMul.hMul Real Real Real qz29 qz156 qz157) Bool.false 281314473440233 

noncomputable def Ns432p584 := @Enclosure.Real.IsNear.mulLit_tt qz156 qz157 18301637723 33554432 70792019 

noncomputable abbrev qz158 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz376))

noncomputable abbrev qz159 := qz376

noncomputable def Ns432p585 := @Enclosure.Real.IsNear.of_eq qz156 (@Neg.neg Real Real.instNeg qz158) Bool.true 18301637723 33554432 70792019 33554432 (BSN.inv_eq_neg_inv_neg qz159) 

noncomputable def Ns432p586 := @Enclosure.Real.IsNear.recentre' qz158 Bool.false 18301637723 33554432 70792019 33554432 18301637723 33554432 

noncomputable def Ns432p587 := @Enclosure.Real.IsNear.recentre' qz159 Bool.true 30760 16777216 1608634432 226827960320000 3845 2097152 25134913 3544186880000 

noncomputable abbrev qz378 := (@HMul.hMul Real Real Real qz453 qz451 qz488)

noncomputable abbrev qz160 := qz378

noncomputable def Ns432p588 := @Enclosure.Real.IsNear.cos_image qz160 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 52768697) qz48) Bool.false 52768697 33554432 233 33554432 Bool.true 30760 16777216 1 

noncomputable def Ns432p589 := nat_lit 998484790206771379928769987 

noncomputable def Ns432p590 := nat_lit 144115188075855872000000000000000 

noncomputable abbrev qz161 := qz365

noncomputable def Ns432p591 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz161 884279719003555 140737488355328 1 500000000000000 8398399 33554432 37 33554432 7426533907799737308445 4722366482869645213696 Ns432p589 

noncomputable def Ns432p592 := @Enclosure.Real.IsNear.subLit_ff_p qz154 qz22 377497151 33554432 37 33554432 11 1 0 1 8398399 8398399 33554432 37 

noncomputable def Ns432p593 := @Ns432p592 33554432 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 377497151 33554432 37 33554432 377497151 33554432 37 33554432 (Ns432p579 rfl rfl rfl rfl rfl rfl) rfl) qz64 

noncomputable def Ns432p594 := @Enclosure.Real.IsNear.recentre' qz160 Bool.false 7426533907799737308445 4722366482869645213696 Ns432p589 Ns432p590 52768697 33554432 233 33554432 (@Ns432p591 Ns432p590 RS433to438.d51 (Ns432p593 rfl rfl) rfl) 

noncomputable def Ns432p595 := nat_lit 249579813143765112721616677801831726014513148033775834925616046957528298103353348862330252713618721 

noncomputable def Ns432p596 := nat_lit 466140078568310997740032924726083431030554731292430641663169182715053126363114198848575204641 

noncomputable def Ns432p597 := nat_lit 1510453445288546642012566322975362140993193066259224709837544533001765137135868971757560406676172065 

noncomputable def Ns432p598 := BSN.cos_dyadic_bound_t 52768697 33554432 4 3 16777216 6760000 Ns432p595 Ns432p191 Ns432p596 Ns432p597 Ns432p194 Ns432p596 30760 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 52768697) (BSN.cosEvenQ 33554432) 0 3 Ns432p595 Ns432p191 Ns432p596 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 52768697) (BSN.cosOddQ 33554432) 0 3 Ns432p597 Ns432p194 Ns432p596 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz162 := (@Neg.neg Real Real.instNeg qz376)

noncomputable def Ns432p599 := @Enclosure.Real.IsNear.inv_image qz162 3845 2097152 25134913 3544186880000 9115422852 9186214871 16777216 (@Enclosure.Real.IsNear.neg qz159 Bool.true 3845 2097152 25134913 3544186880000 (Ns432p587 (@Ns432p588 6760000 (Ns432p594 rfl) (Enclosure.sfrac_false_div 52768697 33554432) (Ns432p598 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns432p600 := Ns432p585 (@Enclosure.Real.IsNear.neg qz158 Bool.false 18301637723 33554432 70792019 33554432 (@Ns432p586 70792019 33554432 (Ns432p599 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns432p601 := @Enclosure.Real.IsNear.recentre' qz157 Bool.true 15371 16777216 

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz296 qz293 qz377)

noncomputable def Ns432p602 := @Enclosure.Real.IsNear.cos_image qz163 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 52737919)) qz48) Bool.true 52737919 33554432 

noncomputable def Ns432p603 := nat_lit 249047785388286918004541194205 

noncomputable def Ns432p604 := nat_lit 158456325028528675187087900672 

noncomputable def Ns432p605 := nat_lit 10054994853185393380817375890911189 

noncomputable def Ns432p606 := @Enclosure.Real.IsNear.recentre' qz163 Bool.true Ns432p603 Ns432p604 Ns432p605 

noncomputable def Ns432p607 := nat_lit 967140655691703339764940800000000000000 

noncomputable abbrev qz164 := qz377

noncomputable def Ns432p608 := @Enclosure.Real.IsNear.mulLit_ft qz26 qz164 884279719003555 140737488355328 1 500000000000000 281639146568831 

noncomputable abbrev qz379 := (@HSub.hSub Real Real Real qz456 qz494 qz488)

noncomputable abbrev qz165 := qz379

noncomputable def Ns432p609 := @Enclosure.Real.IsNear.subLit_tf qz165 qz68 211270402391167 1125899906842624 1862996879 1125899906842624 1 16 

noncomputable abbrev qz380 := qz494

noncomputable abbrev qz166 := qz380

noncomputable def Ns432p610 := @Enclosure.Real.IsNear.subLit_ff_n qz166 qz161 70533105763201 1125899906842624 621482895 1125899906842624 8398399 33554432 37 33554432 

noncomputable def Ns432p611 := @Enclosure.Real.IsNear.mulLit_ff qz161 qz161 8398399 33554432 37 33554432 8398399 33554432 37 33554432 70533105763201 1125899906842624 

noncomputable def Ns432p612 := nat_lit 248995932561598386490977897522942675401177836154602474599207589020616884205992601008880125066339841 

noncomputable def Ns432p613 := nat_lit 462887940327404955427879188473565447351192824703332951265960224978705569585355609930075727361 

noncomputable def Ns432p614 := nat_lit 1506928304040463735868817409250938501219310472095433869674238915272678677599533726663792267805320705 

noncomputable def Ns432p615 := BSN.cos_dyadic_bound_t 52737919 33554432 4 3 16777216 6760000 Ns432p612 Ns432p191 Ns432p613 Ns432p614 Ns432p194 Ns432p613 15371 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 52737919) (BSN.cosEvenQ 33554432) 0 3 Ns432p612 Ns432p191 Ns432p613 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 52737919) (BSN.cosOddQ 33554432) 0 3 Ns432p614 Ns432p194 Ns432p613 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p616 := @Ns432p601 1199777216 113413980160000 15371 16777216 18746519 1772093440000 (@Ns432p602 175 16777216 Bool.true 15371 16777216 1 6760000 (@Ns432p606 Ns432p607 52737919 33554432 175 16777216 (@Ns432p608 1125899906842624 1862996879 1125899906842624 Ns432p603 Ns432p604 Ns432p605 Ns432p607 RS433to438.d51 (@Ns432p609 0 1 4506226345101296 281639146568831 1125899906842624 1862996879 1125899906842624 (@Ns432p610 7089058350647050502144 211270402391167 1125899906842624 1862996879 1125899906842624 (@Ns432p611 621482895 1125899906842624 (Ns432p593 rfl rfl) (Ns432p593 rfl rfl) rfl) (Ns432p593 rfl rfl) rfl rfl) qz70 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 52737919 33554432) (BSN.cos_neg_of_bound 52737919 33554432 Bool.true 15371 16777216 1 6760000 (Ns432p615 rfl rfl)) rfl rfl) 

noncomputable def Ns432p617 := @Ns432p577 919070135691323897563727 Ns432p77 (Ns432p578 qz71 (@Enclosure.Real.IsNear.of_eq qz152 (@Inv.inv Real Real.instInv qz155) Bool.false 10003869 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz138 795257 1000 qz141)) Ns432p582) rfl) (@Ns432p583 562949953421312 459354326337243723 59461588830126080000 (BSN.correction_mk qz161 (BSN.cos_two_pi_p_ne_zero_mk qz138 795257 1000 11 qz141 rfl rfl (@BSN.floor_sqrt_eq_dec qz138 795257 1000 11 qz141 rfl rfl rfl))) (@Ns432p584 33554432 15371 16777216 18746519 1772093440000 281314473440233 562949953421312 459354326337243723 59461588830126080000 Ns432p600 (Ns432p616 rfl) rfl)) 

noncomputable def Ns432p618 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz138) (hardyZApproximantRS₀ qz138) Bool.false 26818438294283230266085 18889465931478580854784 Ns432p499 Ns432p77 (@Eq.refl Real (hardyZApproximantRS₀ qz138)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz138) (@HSub.hSub Real Real Real qz72 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (@HMul.hMul Real Real Real qz29 qz139 qz140)) Bool.false 26818438294283230266085 18889465931478580854784 Ns432p499 Ns432p77 (BSN.hardyZApproximantRS₀_eq qz138 11 (@BSN.floor_sqrt_eq_dec qz138 795257 1000 11 qz141 rfl rfl rfl)) (@Ns432p501 26818438294283230266085 18889465931478580854784 Ns432p499 Ns432p77 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (@HAdd.hAdd Real Real Real qz47 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz138) qz138 11)) Bool.false 21320017 16777216 76549 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz138) qz138 11) (Ns432p576 (Ns432p575 rfl) rfl rfl)) (Ns432p617 rfl) rfl rfl)) 

theorem RS433to438.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz138) Bool.false 26818438294283230266085 18889465931478580854784 Ns432p499 Ns432p77 := Ns432p618 

noncomputable def Ns432p619 := nat_lit 1210832572460334432638369 

noncomputable def Ns432p620 := nat_lit 997599919506212551393280000 

noncomputable def Ns432p621 := nat_lit 4725899103593257159915066097664 

noncomputable abbrev qz545 := (Enclosure.sfrac Bool.false 796555 1000)

noncomputable abbrev qz495 := qz545

noncomputable abbrev qz381 := qz495

noncomputable abbrev qz167 := qz381

noncomputable abbrev qz546 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 796555 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz496 := qz546

noncomputable abbrev qz382 := qz496

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz296 qz297 (@HPow.hPow Real Real Real qz298 qz382 qz300))

noncomputable abbrev qz547 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 796555 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz497 := qz547

noncomputable abbrev qz383 := qz497

noncomputable abbrev qz169 := (Zeta.RiemannSiegel.correction qz383)

noncomputable def Ns432p622 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz167) qz167 11) (@HMul.hMul Real Real Real qz29 qz168 qz169) 520003677 134217728 38339 33554432 1381313554005987090615 9444732965739290427392 70983645381232542078369 Ns432p620 Ns432p621 

noncomputable def Ns432p623 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz167) qz167 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 796555 1000 193 241 268435456 134217728 4503599627370496 Bool.false 410694545341 2593 

noncomputable def Ns432p624 := Ns432p623 618095470 41 84886744 8 643680110 41 80936328 8 Bool.true 366979161 131560 Bool.true 272608109 Bool.true 412624467 14148475504056880 1 Bool.false 228107761 Bool.true Bool.false 268283488 Bool.true Bool.true 520003677 

noncomputable def Ns432p625 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz167) qz167 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 796555 1000 80 140 268435456 134217728 4503599627370496 Bool.false 410694545341 2593 

noncomputable def Ns432p626 := Ns432p625 558195838 41 94906264 8 589812974 41 89478488 8 Bool.true 519437182 107326 Bool.true 206546135 Bool.true 91888206 14148475504056880 1 Bool.false 192816487 Bool.false Bool.false 252861291 Bool.false Bool.true 366979161 

noncomputable def Ns432p627 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz167) qz167 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 796555 1000 65 12 268435456 134217728 4503599627370496 Bool.false 410694545341 2593 

noncomputable def Ns432p628 := Ns432p627 480971758 41 109588312 8 522351262 41 101459064 8 Bool.true 490801506 79591 Bool.false 166353809 Bool.true 327075022 14148475504056880 1 Bool.false 155908435 Bool.true Bool.false 92637476 Bool.false Bool.true 519437182 

noncomputable def Ns432p629 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz167) qz167 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 796555 1000 271 157 268435456 134217728 4503599627370496 Bool.false 410694545341 2593 

noncomputable def Ns432p630 := Ns432p629 372130544 40 134217720 8 432030192 40 120047984 16 Bool.true 375527282 46926 Bool.false 2936804 Bool.false 358519514 14148475504056880 1 Bool.false 2936745 Bool.false Bool.false 261044383 Bool.true Bool.true 490801506 

noncomputable def Ns432p631 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz167) qz167 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 796555 1000 622 416 268435456 134217728 4503599627370496 Bool.false 410694545341 2593 

noncomputable def Ns432p632 := Ns432p631 186065264 40 189812528 16 294906480 40 154981288 8 Bool.true 268435368 2640 Bool.false 212408593 Bool.false 375824005 14148475504056880 1 Bool.false 188692107 Bool.true Bool.false 45611049 Bool.false Bool.true 375527282 

noncomputable def Ns432p633 := nat_lit 811047748072343159357451184686582241177647347451902369 

noncomputable def Ns432p634 := nat_lit 530111671949324708107886988466430217271024759603200 

noncomputable def Ns432p635 := nat_lit 153929022374510371725204326500000000 

noncomputable def Ns432p636 := nat_lit 735677729775847538834353240381245000000 

noncomputable abbrev qz498 := (@Eq.refl Real qz545)

noncomputable abbrev qz384 := qz498

noncomputable abbrev qz170 := qz384

noncomputable def Ns432p637 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz167 796555 1000 2538000472100 16000000 1593110 4000 2000 Ns432p635 Ns432p636 qz170 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns432p638 := nat_lit 4055238740361715796787255923432911205888236737259511845000000 

noncomputable abbrev qz499 := (Real.log (Enclosure.sfrac Bool.false 2538000472100 16000000))

noncomputable abbrev qz500 := (@HSub.hSub Real Real Real qz528 qz529 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz530 (@Nat.cast Real Real.instNatCast 1593110))))

noncomputable abbrev qz385 := (@HSub.hSub Real Real Real qz456 (@HMul.hMul Real Real Real qz453 (Enclosure.sfrac Bool.false 796555 4000) qz499) (@HMul.hMul Real Real Real qz453 qz458 qz500))

noncomputable abbrev qz386 := (Enclosure.sfrac Bool.false 796555 2000)

noncomputable abbrev qz171 := (@HSub.hSub Real Real Real qz303 (@HSub.hSub Real Real Real qz303 qz385 qz386) (@HMul.hMul Real Real Real qz296 qz386 (Real.log Real.pi)))

noncomputable def Ns432p639 := @Enclosure.Real.IsNear.addLit_ft_p qz171 (Enclosure.sfrac Bool.true Ns432p635 Ns432p636) 5512249631622055983881 3602879701896396800 1336557483888167547 138444800000000000000000 Ns432p635 Ns432p636 0 1 Ns432p638 

noncomputable def Ns432p640 := nat_lit 73984162172514930884531244236800 

noncomputable abbrev qz172 := (@HSub.hSub Real Real Real qz303 qz385 qz386)

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz296 qz386 (Real.log Real.pi))

noncomputable def Ns432p641 := @Enclosure.Real.IsNear.subLit_ff_p qz172 qz173 7154875106527326894857 3602879701896396800 502847332717403 135200000000000000000 6119256745671 13421772800 159311 26843545600 Ns432p640 5512249631622055983881 3602879701896396800 

noncomputable def Ns432p642 := nat_lit 14309750213054653789714000 

noncomputable abbrev qz174 := qz385

noncomputable abbrev qz175 := qz386

noncomputable def Ns432p643 := @Enclosure.Real.IsNear.subLit_ff_p qz174 qz175 8589821026999369071369 3602879701896396800 502847332717403 135200000000000000000 796555 2000 0 1 Ns432p642 7154875106527326894857 3602879701896396800 502847332717403 135200000000000000000 

noncomputable def Ns432p644 := nat_lit 19342557388186804905135961511414464512 

noncomputable def Ns432p645 := nat_lit 57904153958499363372138496 

noncomputable def Ns432p646 := nat_lit 1041294195171502239261642860798432937242519283606992944767377853705000000000000 

noncomputable def Ns432p647 := nat_lit 3156957546246723388188476009478536717211931362218273298692026791000000000000 

noncomputable def Ns432p648 := nat_lit 110110135919871524676962476968610607233873842375144534664815000000000000 

noncomputable def Ns432p649 := BSN.log_dyadic_bound 440848472100 4635152472100 4 3 Ns432p646 134217728 54080000 Ns432p647 Ns432p648 25608248 5076000944200 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 440848472100) (BSN.artanhQ 4635152472100) 0 3 Ns432p647 Ns432p646 Ns432p648 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz387 := qz499

noncomputable abbrev qz176 := qz387

noncomputable abbrev qz388 := (Enclosure.sfrac Bool.false 796555 4000)

noncomputable def Ns432p650 := @Enclosure.Real.IsNear.mulLit_ff qz388 qz176 796555 4000 0 1 53927445745560679 4503599627370496 3125002873 169000000000000000 8591235309171017332169 3602879701896396800 497847332700503 135200000000000000000 (Enclosure.Real.IsNear.const Bool.false 796555 4000) (BSN.isNear_log_sfrac 2538000472100 16000000 53927445745560679 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2538000472100) qz308)) Bool.false Ns432p645 Ns432p103 1000000919360000 54080000000000000000000 53927445745560679 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2538000472100 16000000 17 5076000944200 4194304000000 25608248 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns432p649 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns432p651 := BSN.arctan_dyadic_bound_f 1000 1593110 1 0 16777216 6760000 0 1 1 0 1 1 10531 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1593110) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1593110) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz501 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz530 (@Nat.cast Real Real.instNatCast 1593110)))

noncomputable abbrev qz389 := qz501

noncomputable abbrev qz177 := qz389

noncomputable def Ns432p652 := @Enclosure.Real.IsNear.subLit_ff_p qz39 qz177 884279719003555 562949953421312 1 2000000000000000 10531 16777216 1 6760000 14829823424182467166208 883926357280163 562949953421312 50000000169 338000000000000000 qz41 (Ns432p651 rfl) rfl rfl 

noncomputable abbrev qz390 := (@HMul.hMul Real Real Real qz453 (Enclosure.sfrac Bool.false 796555 4000) qz499)

noncomputable abbrev qz178 := qz390

noncomputable abbrev qz391 := (@HMul.hMul Real Real Real qz453 qz458 qz500)

noncomputable abbrev qz179 := qz391

noncomputable abbrev qz392 := qz500

noncomputable abbrev qz180 := qz392

noncomputable def Ns432p653 := @Enclosure.Real.IsNear.subLit_ff_p qz178 qz179 8591235309171017332169 3602879701896396800 497847332700503 135200000000000000000 883926357280163 2251799813685248 50000000169 1352000000000000000 Ns432p644 8589821026999369071369 3602879701896396800 502847332717403 135200000000000000000 (Ns432p650 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 qz180 1 4 0 1 883926357280163 562949953421312 50000000169 338000000000000000 883926357280163 2251799813685248 50000000169 1352000000000000000 qz46 Ns432p652 rfl) 

noncomputable def Ns432p654 := @Ns432p639 Ns432p633 Ns432p634 1336557483888167547 138444800000000000000000 (@Ns432p641 1336557483888167547 138444800000000000000000 (Ns432p643 (Ns432p653 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 796555 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz175 (Real.log Real.pi) 796555 2000 0 1 38410761 33554432 1 67108864 6119256745671 13421772800 159311 26843545600 (Enclosure.Real.IsNear.const Bool.false 796555 2000) RS433to438.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns432p635 Ns432p636) 

noncomputable def Ns432p655 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz167) Bool.false Ns432p633 Ns432p634 1336557483888167547 138444800000000000000000 51336818167 33554432 325 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz167) (@HAdd.hAdd Real Real Real qz47 qz171 (Enclosure.sfrac Bool.true Ns432p635 Ns432p636)) Bool.false Ns432p633 Ns432p634 1336557483888167547 138444800000000000000000 Ns432p637 (Ns432p654 rfl rfl)) 

noncomputable def Ns432p656 := BSN.cos_dyadic_bound_f 53812380 68719476736 1 0 33554432 13533204 0 1 1 0 1 1 33554421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 53812380) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 53812380) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns432p657 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz167) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51336818167) qz48) Bool.false 51336818167 33554432 325 33554432 Bool.true 33554421 33554432 1 6760000 (Ns432p655 rfl) (Enclosure.sfrac_false_div 51336818167 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51336818167) qz48) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3786709632236791005184) qz316) 226375608064910080 72057594037927936 Bool.false 33554421 33554432 243 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q2 51336818167 33554432 226375608064910080 72057594037927936 243 3786709632236791005184 Ns432p103 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554421 33554432 3786709632236791005184 Ns432p103 53812380 68719476736 13533204 13520000 (Ns432p656 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns432p658 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz167) Bool.false Ns432p633 Ns432p634 1336557483888167547 138444800000000000000000 410694545341 268435456 2593 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz167) (@HAdd.hAdd Real Real Real qz47 qz171 (Enclosure.sfrac Bool.true Ns432p635 Ns432p636)) Bool.false Ns432p633 Ns432p634 1336557483888167547 138444800000000000000000 Ns432p637 (Ns432p654 rfl rfl)) 

noncomputable def Ns432p659 := Ns432p632 46926 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 622 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 188692107 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 416 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 45611049 268435456) qz170 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz167) qz167 1) Bool.true 33554421 33554432 34852413 3544186880000 268435368 268435456 2640 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz167) qz167 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz167)) Bool.true 33554421 33554432 34852413 3544186880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz167) qz167) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz167)) Bool.true 33554421 33554432 2230554432 226827960320000 33554421 33554432 34852413 3544186880000 (Ns432p657 rfl rfl) rfl)) rfl) (Ns432p658 rfl) RS433to438.d7 

noncomputable def Ns432p660 := nat_lit 17760633738416898121991807087170591494903315816011053885373915874583681 

noncomputable def Ns432p661 := nat_lit 4143588865270196218961171997947186123300542589844468993329449526401 

noncomputable def Ns432p662 := nat_lit 53273614037520153973537498917515880112463346362853472718135088724698241 

noncomputable def Ns432p663 := BSN.cos_dyadic_bound_f 212408593 268435456 3 2 268435456 134217728 Ns432p660 Ns432p131 Ns432p661 Ns432p662 Ns432p134 Ns432p661 188692107 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 212408593) qz49 0 2 Ns432p660 Ns432p131 Ns432p661 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 212408593) qz50 0 2 Ns432p662 Ns432p134 Ns432p661 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p664 := nat_lit 10759082594092249687427851920470736631497383198923910806601585578981603007919494874265111964013369596428140625 

noncomputable def Ns432p665 := nat_lit 7939884703609109629610730387466451303816630056721876548262297751495878059791408485405185209375244140625 

noncomputable def Ns432p666 := nat_lit 65172436262920192076379217362948190735749770062954001889731008196267009560462295783913120066804555920293740625 

noncomputable def Ns432p667 := BSN.cos_dyadic_bound_f 375824005 268435456 4 3 268435456 134217728 Ns432p664 Ns432p125 Ns432p665 Ns432p666 Ns432p128 Ns432p665 45611049 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 375824005) qz49 0 3 Ns432p664 Ns432p125 Ns432p665 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 375824005) qz50 0 3 Ns432p666 Ns432p128 Ns432p665 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p668 := BSN.sin_dyadic_bound_f 2936804 268435456 1 0 268435456 134217728 0 1 1 0 1 1 2936745 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2936804) qz51 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2936804) qz52 0 0 rfl) rfl rfl 

noncomputable def Ns432p669 := nat_lit 23138015968129375559021633882679813230723526115586113022476044835543677487444429094087475438027559837517418496 

noncomputable def Ns432p670 := nat_lit 4509761642191502222698137637001683735352616027527165827570516761129881209035493081637195250387325751296 

noncomputable def Ns432p671 := nat_lit 115614888188914989177962534712223721767928284341605750085062326344718369400926095654174544834898308185616224256 

noncomputable def Ns432p672 := BSN.sin_dyadic_bound_f 358519514 268435456 4 3 268435456 134217728 Ns432p669 Ns432p272 Ns432p670 Ns432p671 Ns432p275 Ns432p670 261044383 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 358519514) qz51 0 3 Ns432p669 Ns432p272 Ns432p670 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 358519514) qz52 0 3 Ns432p671 Ns432p275 Ns432p670 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p673 := Ns432p630 79591 BSN.abs_quadSignPos (BSN.cos_quad_nat3 271 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 2936745 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 157 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 261044383 268435456) qz170 rfl rfl (Ns432p659 RS433to438.d9 RS433to438.d11 RS433to438.d13 RS433to438.d17 (Ns432p663 rfl rfl) (Ns432p667 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns432p658 rfl) RS433to438.d19 RS433to438.d21 RS433to438.d23 RS433to438.d25 RS433to438.d17 (Ns432p668 rfl rfl) (Ns432p672 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns432p674 := nat_lit 12025232458470658498091933967907746247585012742433639781993152268712065 

noncomputable def Ns432p675 := nat_lit 586491868032471954710664611108256923616556944867996220042063624321 

noncomputable def Ns432p676 := nat_lit 31493706880589195873742676458959445851512987518939270292292473553139841 

noncomputable def Ns432p677 := BSN.sin_dyadic_bound_f 166353809 268435456 3 2 268435456 134217728 Ns432p674 Ns432p137 Ns432p675 Ns432p676 Ns432p140 Ns432p675 155908435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 166353809) qz51 0 2 Ns432p674 Ns432p137 Ns432p675 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 166353809) qz52 0 2 Ns432p676 Ns432p140 Ns432p675 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p678 := nat_lit 6166003650402742925107517135178283503740639039507547632805089752691472655418296864135409149929915704741072896 

noncomputable def Ns432p679 := nat_lit 1498885820985373086656988973242588682076719368320710927588385671006285844894965252628522431683898249216 

noncomputable def Ns432p680 := nat_lit 37374406348460017321884123483693618295906786173646458610421460453526975642319682355979873419756278105180344320 

noncomputable def Ns432p681 := BSN.cos_dyadic_bound_f 327075022 268435456 4 3 268435456 134217728 Ns432p678 Ns432p125 Ns432p679 Ns432p680 Ns432p128 Ns432p679 92637476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 327075022) qz49 0 3 Ns432p678 Ns432p125 Ns432p679 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 327075022) qz50 0 3 Ns432p680 Ns432p128 Ns432p679 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p682 := Ns432p628 107326 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 155908435 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 92637476 268435456) qz170 rfl rfl (Ns432p673 rfl rfl) (Ns432p658 rfl) RS433to438.d27 RS433to438.d29 RS433to438.d31 RS433to438.d33 RS433to438.d17 (Ns432p677 rfl rfl) (Ns432p681 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p683 := nat_lit 15879165999316749328356296337813740567660195399540772804802527210690625 

noncomputable def Ns432p684 := nat_lit 3312352751804711216888229259693697734723650947048649032561437890625 

noncomputable def Ns432p685 := nat_lit 47630873292446638562635112554921834307511138896728221116342458756290625 

noncomputable def Ns432p686 := BSN.cos_dyadic_bound_f 206546135 268435456 3 2 268435456 134217728 Ns432p683 Ns432p131 Ns432p684 Ns432p685 Ns432p134 Ns432p684 192816487 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 206546135) qz49 0 2 Ns432p683 Ns432p131 Ns432p684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 206546135) qz50 0 2 Ns432p685 Ns432p134 Ns432p684 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p687 := nat_lit 621886938945774692762209773469900915033517956373217320011122903204096 

noncomputable def Ns432p688 := nat_lit 5082509282694679526113157602210888766243609092074964845491241216 

noncomputable def Ns432p689 := nat_lit 1865650651818758688927577094094498323323021381901467810103677727129856 

noncomputable def Ns432p690 := BSN.cos_dyadic_bound_f 91888206 268435456 3 2 268435456 134217728 Ns432p687 Ns432p131 Ns432p688 Ns432p689 Ns432p134 Ns432p688 252861291 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 91888206) qz49 0 2 Ns432p687 Ns432p131 Ns432p688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 91888206) qz50 0 2 Ns432p689 Ns432p134 Ns432p688 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p691 := Ns432p626 131560 BSN.abs_quadSignPos (BSN.cos_quad_nat0 80 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 192816487 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 252861291 268435456) qz170 rfl rfl (Ns432p682 rfl) (Ns432p658 rfl) RS433to438.d35 RS433to438.d37 RS433to438.d39 RS433to438.d41 RS433to438.d17 (Ns432p686 rfl rfl) (Ns432p690 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p692 := nat_lit 86745930735820370522729179376560793692351937222151461267365536440280865 

noncomputable def Ns432p693 := nat_lit 30500724935935301017536755903671621005248027059177795247495270917921 

noncomputable def Ns432p694 := nat_lit 227142341229633265643595648381434229426913243538015158317461412619249441 

noncomputable def Ns432p695 := BSN.sin_dyadic_bound_f 272608109 268435456 3 2 268435456 134217728 Ns432p692 Ns432p137 Ns432p693 Ns432p694 Ns432p140 Ns432p693 228107761 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 272608109) qz51 0 2 Ns432p692 Ns432p137 Ns432p693 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 272608109) qz52 0 2 Ns432p694 Ns432p140 Ns432p693 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p696 := nat_lit 40629298116593709841023205922856229483115174765059989707999350232291038689384080807794554792468722007577862961 

noncomputable def Ns432p697 := nat_lit 24359014625040611355170400073596541274865999334996439816523230890765297821299038626458608553448346886961 

noncomputable def Ns432p698 := nat_lit 202914972107136085334257759697646810383570323546592883777156008984567512759515855241779847571591463305185993521 

noncomputable def Ns432p699 := BSN.sin_dyadic_bound_f 412624467 268435456 4 3 268435456 134217728 Ns432p696 Ns432p272 Ns432p697 Ns432p698 Ns432p275 Ns432p697 268283488 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 412624467) qz51 0 3 Ns432p696 Ns432p272 Ns432p697 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 412624467) qz52 0 3 Ns432p698 Ns432p275 Ns432p697 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p700 := Ns432p624 153356 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 228107761 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268283488 268435456) qz170 rfl rfl (Ns432p691 rfl) (Ns432p658 rfl) RS433to438.d43 RS433to438.d45 RS433to438.d47 RS433to438.d49 RS433to438.d17 (Ns432p695 rfl rfl) (Ns432p699 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p701 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz167) qz167 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz167) qz167 11) 520003677 268435456 153356 268435456 520003677 268435456 153356 268435456 279174848314343424 520003677 134217728 38339 33554432 (Ns432p700 rfl) 

noncomputable def Ns432p702 := @Enclosure.Real.IsNear.mulLit_tf qz168 qz169 9999791 33554432 1 33554432 138134242406265 281474976710656 7097053113892607 29730794415063040000 1381313554005987090615 9444732965739290427392 

noncomputable abbrev qz181 := (@HPow.hPow Real Real Real qz298 qz382 qz300)

noncomputable def Ns432p703 := @Enclosure.Real.IsNear.mulLit_tf qz53 qz181 1 1 0 1 9999791 33554432 1 33554432 9999791 33554432 1 33554432 

noncomputable abbrev qz182 := qz382

noncomputable def Ns432p704 := @Enclosure.Real.IsNear.sqrt_image qz182 850776976783 6710886400 159311 6710886400 188902530 188902567 16777216 (@Enclosure.Real.IsNear.of_eq qz182 (@HMul.hMul Real Real Real qz29 qz167 qz27) Bool.false 850776976783 6710886400 159311 6710886400 (BSN.t_div_two_pi_mk qz167 796555 1000 qz170) (@Enclosure.Real.IsNear.mulLit_ff qz167 qz27 796555 1000 0 1 5340353 33554432 1 33554432 850776976783 6710886400 159311 6710886400 (Enclosure.Real.IsNear.const Bool.false 796555 1000) RS433to438.d52 rfl)) 

noncomputable abbrev qz548 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 796555 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz502 := qz548

noncomputable abbrev qz393 := qz502

noncomputable abbrev qz183 := qz393

noncomputable def Ns432p705 := @Enclosure.Real.IsNear.sqrt_image qz183 377805097 33554432 37 33554432 56296168 56296174 16777216 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 377805097 33554432 37 33554432 377805097 33554432 37 33554432 (Ns432p704 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz184 := (Real.sqrt qz393)

noncomputable def Ns432p706 := @Enclosure.Real.IsNear.inv_image qz184 56296171 16777216 3 16777216 4999895 4999896 16777216 (@Enclosure.Real.IsNear.recentre' qz184 Bool.false 112592342 33554432 6 33554432 56296171 16777216 3 16777216 (Ns432p705 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns432p707 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz184) Bool.false 9999791 33554432 1 33554432 9999791 33554432 1 33554432 (Ns432p706 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz394 := (Real.cos (@HMul.hMul Real Real Real qz453 qz451 qz497))

noncomputable abbrev qz185 := (@Inv.inv Real Real.instInv qz394)

noncomputable abbrev qz503 := (@HMul.hMul Real Real Real qz524 qz547 qz547)

noncomputable abbrev qz395 := (@HSub.hSub Real Real Real qz456 (@HSub.hSub Real Real Real qz456 qz503 qz497) qz466)

noncomputable abbrev qz186 := (Real.cos (@HMul.hMul Real Real Real qz296 qz293 qz395))

noncomputable def Ns432p708 := @Enclosure.Real.IsNear.of_eq qz169 (@HMul.hMul Real Real Real qz29 qz185 qz186) Bool.false 138134242406265 

noncomputable def Ns432p709 := @Enclosure.Real.IsNear.mulLit_tt qz185 qz186 282149035 16777216 33793 

noncomputable abbrev qz187 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz394))

noncomputable abbrev qz188 := qz394

noncomputable def Ns432p710 := @Enclosure.Real.IsNear.of_eq qz185 (@Neg.neg Real Real.instNeg qz187) Bool.true 282149035 16777216 33793 16777216 (BSN.inv_eq_neg_inv_neg qz188) 

noncomputable def Ns432p711 := @Enclosure.Real.IsNear.recentre' qz187 Bool.false 564298070 33554432 67586 33554432 282149035 16777216 

noncomputable def Ns432p712 := @Enclosure.Real.IsNear.recentre' qz188 Bool.true 997611 16777216 807697216 113413980160000 997611 16777216 12620269 1772093440000 

noncomputable abbrev qz396 := (@HMul.hMul Real Real Real qz453 qz451 qz497)

noncomputable abbrev qz189 := qz396

noncomputable def Ns432p713 := @Enclosure.Real.IsNear.cos_image qz189 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 27351789) qz339) Bool.false 27351789 16777216 117 16777216 Bool.true 997611 16777216 1 

noncomputable def Ns432p714 := nat_lit 998484790209416615926638019 

noncomputable abbrev qz190 := qz383

noncomputable def Ns432p715 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz190 884279719003555 140737488355328 1 500000000000000 8706345 33554432 37 33554432 7698844310148006056475 4722366482869645213696 Ns432p714 

noncomputable def Ns432p716 := @Enclosure.Real.IsNear.subLit_ff_p qz183 qz22 377805097 33554432 37 33554432 11 1 0 1 8706345 8706345 33554432 37 

noncomputable def Ns432p717 := @Ns432p716 33554432 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 377805097 33554432 37 33554432 377805097 33554432 37 33554432 (Ns432p704 rfl rfl rfl rfl rfl rfl) rfl) qz64 

noncomputable def Ns432p718 := @Enclosure.Real.IsNear.recentre' qz189 Bool.false 7698844310148006056475 4722366482869645213696 Ns432p714 Ns432p590 27351789 16777216 117 16777216 (@Ns432p715 Ns432p590 RS433to438.d51 (Ns432p717 rfl rfl) rfl) 

noncomputable def Ns432p719 := nat_lit 70412741019110571380114898917523542584515725093784046784890134169150063902760674179296209239601 

noncomputable def Ns432p720 := nat_lit 175318945681019239894188026569665349289159861583123605306590014408720765609028439210819121 

noncomputable def Ns432p721 := nat_lit 425977288861918132717393524813001083622441090506099218154012340265925731802741551555342511996465 

noncomputable def Ns432p722 := BSN.cos_dyadic_bound_t 27351789 16777216 4 3 16777216 6760000 Ns432p719 Ns432p321 Ns432p720 Ns432p721 Ns432p324 Ns432p720 997611 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 27351789) (BSN.cosEvenQ 16777216) 0 3 Ns432p719 Ns432p321 Ns432p720 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 27351789) (BSN.cosOddQ 16777216) 0 3 Ns432p721 Ns432p324 Ns432p720 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz191 := (@Neg.neg Real Real.instNeg qz394)

noncomputable def Ns432p723 := @Enclosure.Real.IsNear.inv_image qz191 997611 16777216 12620269 1772093440000 282115242 282182828 16777216 (@Enclosure.Real.IsNear.neg qz188 Bool.true 997611 16777216 12620269 1772093440000 (Ns432p712 (@Ns432p713 6760000 (Ns432p718 rfl) (Enclosure.sfrac_false_div 27351789 16777216) (Ns432p722 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns432p724 := Ns432p710 (@Enclosure.Real.IsNear.neg qz187 Bool.false 282149035 16777216 33793 16777216 (@Ns432p711 33793 16777216 (Ns432p723 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns432p725 := @Enclosure.Real.IsNear.recentre' qz186 Bool.true 489579 16777216 

noncomputable abbrev qz192 := (@HMul.hMul Real Real Real qz296 qz293 qz395)

noncomputable def Ns432p726 := @Enclosure.Real.IsNear.cos_image qz192 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 26843237)) qz339) Bool.true 26843237 16777216 

noncomputable def Ns432p727 := nat_lit 253527206546070406249785308845 

noncomputable def Ns432p728 := nat_lit 50889933060336077554946749486801829 

noncomputable def Ns432p729 := @Enclosure.Real.IsNear.recentre' qz192 Bool.true Ns432p727 Ns432p604 Ns432p728 

noncomputable def Ns432p730 := nat_lit 4835703278458516698824704000000000000000 

noncomputable abbrev qz193 := qz395

noncomputable def Ns432p731 := @Enclosure.Real.IsNear.mulLit_ft qz26 qz193 884279719003555 140737488355328 1 500000000000000 286704762189679 

noncomputable abbrev qz397 := (@HSub.hSub Real Real Real qz456 qz503 qz497)

noncomputable abbrev qz194 := qz397

noncomputable def Ns432p732 := @Enclosure.Real.IsNear.subLit_tf qz194 qz68 216336018012015 1125899906842624 1885784883 1125899906842624 1 16 

noncomputable abbrev qz398 := qz503

noncomputable abbrev qz195 := qz398

noncomputable def Ns432p733 := @Enclosure.Real.IsNear.subLit_ff_n qz195 qz190 75800443259025 1125899906842624 644270899 1125899906842624 8706345 33554432 37 33554432 

noncomputable def Ns432p734 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz190 8706345 33554432 37 33554432 8706345 33554432 37 33554432 75800443259025 1125899906842624 

noncomputable def Ns432p735 := nat_lit 65300446764159709151704297275743701348700842317059105555734455717949466355446082037237694846161 

noncomputable def Ns432p736 := nat_lit 139964736114952554626900101160677044314081006759024285538671546485867321178757578711094481 

noncomputable def Ns432p737 := nat_lit 395129129881778563531125590519326184828537331832264081644385755174796674056931189263297350194385 

noncomputable def Ns432p738 := BSN.cos_dyadic_bound_t 26843237 16777216 4 3 16777216 6760000 Ns432p735 Ns432p321 Ns432p736 Ns432p737 Ns432p324 Ns432p736 489579 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 26843237) (BSN.cosEvenQ 16777216) 0 3 Ns432p735 Ns432p321 Ns432p736 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 26843237) (BSN.cosOddQ 16777216) 0 3 Ns432p737 Ns432p324 Ns432p736 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p739 := @Ns432p725 1213297216 113413980160000 489579 16777216 18957769 1772093440000 (@Ns432p726 177 16777216 Bool.true 489579 16777216 1 6760000 (@Ns432p729 Ns432p730 26843237 16777216 177 16777216 (@Ns432p731 1125899906842624 1885784883 1125899906842624 Ns432p727 Ns432p604 Ns432p728 Ns432p730 RS433to438.d51 (@Ns432p732 0 1 4587276195034864 286704762189679 1125899906842624 1885784883 1125899906842624 (@Ns432p733 7259032205534932500480 216336018012015 1125899906842624 1885784883 1125899906842624 (@Ns432p734 644270899 1125899906842624 (Ns432p717 rfl rfl) (Ns432p717 rfl rfl) rfl) (Ns432p717 rfl rfl) rfl rfl) qz70 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 26843237 16777216) (BSN.cos_neg_of_bound 26843237 16777216 Bool.true 489579 16777216 1 6760000 (Ns432p738 rfl rfl)) rfl rfl) 

noncomputable def Ns432p740 := @Ns432p702 70983645381232542078369 Ns432p620 (Ns432p703 qz71 (@Enclosure.Real.IsNear.of_eq qz181 (@Inv.inv Real Real.instInv qz184) Bool.false 9999791 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz182 (BSN.t_div_two_pi_nonneg qz167 796555 1000 qz170)) Ns432p707) rfl) (@Ns432p708 281474976710656 7097053113892607 29730794415063040000 (BSN.correction_mk qz190 (BSN.cos_two_pi_p_ne_zero_mk qz167 796555 1000 11 qz170 rfl rfl (@BSN.floor_sqrt_eq_dec qz167 796555 1000 11 qz170 rfl rfl rfl))) (@Ns432p709 16777216 489579 16777216 18957769 1772093440000 138134242406265 281474976710656 7097053113892607 29730794415063040000 Ns432p724 (Ns432p739 rfl) rfl)) 

noncomputable def Ns432p741 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz167) (hardyZApproximantRS₀ qz167) Bool.true 35210692164251634179913 9444732965739290427392 Ns432p619 Ns432p620 (@Eq.refl Real (hardyZApproximantRS₀ qz167)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz167) (@HSub.hSub Real Real Real qz72 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz167) qz167 11) (@HMul.hMul Real Real Real qz29 qz168 qz169)) Bool.true 35210692164251634179913 9444732965739290427392 Ns432p619 Ns432p620 (BSN.hardyZApproximantRS₀_eq qz167 11 (@BSN.floor_sqrt_eq_dec qz167 796555 1000 11 qz170 rfl rfl rfl)) (@Ns432p622 35210692164251634179913 9444732965739290427392 Ns432p619 Ns432p620 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz167) qz167 11) (@HAdd.hAdd Real Real Real qz47 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz167) qz167 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz167) qz167 11)) Bool.true 520003677 134217728 38339 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz167) qz167 11) (Ns432p701 (Ns432p700 rfl) rfl rfl)) (Ns432p740 rfl) rfl rfl)) 

theorem RS433to438.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz167) Bool.true 35210692164251634179913 9444732965739290427392 Ns432p619 Ns432p620 := Ns432p741 

noncomputable def Ns432p742 := nat_lit 19184613836657933680640000 

noncomputable def Ns432p743 := nat_lit 448222389827578921208621563904 

noncomputable abbrev qz549 := (Enclosure.sfrac Bool.false 797852 1000)

noncomputable abbrev qz504 := qz549

noncomputable abbrev qz399 := qz504

noncomputable abbrev qz196 := qz399

noncomputable abbrev qz550 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 797852 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz505 := qz550

noncomputable abbrev qz400 := qz505

noncomputable abbrev qz197 := (@HMul.hMul Real Real Real qz296 qz297 (@HPow.hPow Real Real Real qz298 qz400 qz300))

noncomputable abbrev qz551 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 797852 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz506 := qz551

noncomputable abbrev qz401 := qz506

noncomputable abbrev qz198 := (Zeta.RiemannSiegel.correction qz401)

noncomputable def Ns432p744 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz196) qz196 11) (@HMul.hMul Real Real Real qz29 qz197 qz198) 360378821 134217728 153599 134217728 169591408006541889225 1180591620717411303424 678116940526568152317 Ns432p742 Ns432p743 

noncomputable def Ns432p745 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz196) qz196 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 797852 1000 193 241 268435456 134217728 4503599627370496 Bool.false 411537657379 2597 

noncomputable def Ns432p746 := Ns432p745 618095470 41 84886744 8 643680110 41 80936328 8 Bool.false 505542274 131768 Bool.true 231165896 Bool.true 404365532 14148475504056880 1 Bool.false 203634848 Bool.true Bool.false 267878699 Bool.true Bool.false 360378821 

noncomputable def Ns432p747 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz196) qz196 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 797852 1000 80 140 268435456 134217728 4503599627370496 Bool.false 411537657379 2597 

noncomputable def Ns432p748 := Ns432p747 558195838 41 94906264 8 589812974 41 89478488 8 Bool.false 326262890 107495 Bool.true 87414099 Bool.true 13763595 14148475504056880 1 Bool.false 254327897 Bool.false Bool.false 268082680 Bool.false Bool.false 505542274 

noncomputable def Ns432p749 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz196) qz196 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 797852 1000 65 12 268435456 134217728 4503599627370496 Bool.false 411537657379 2597 

noncomputable def Ns432p750 := Ns432p749 480971758 41 109588312 8 522351262 41 101459064 8 Bool.false 351212338 79715 Bool.false 385645477 Bool.true 161452571 14148475504056880 1 Bool.false 266023485 Bool.true Bool.false 221328163 Bool.false Bool.false 326262890 

noncomputable def Ns432p751 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz196) qz196 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 797852 1000 271 158 268435456 134217728 4503599627370496 Bool.false 411537657379 2597 

noncomputable def Ns432p752 := Ns432p751 372130544 40 134217720 8 432030192 40 120047984 16 Bool.false 302201648 46997 Bool.false 363395527 Bool.false 219630965 14148475504056880 1 Bool.false 262137583 Bool.false Bool.false 183487476 Bool.true Bool.false 351212338 

noncomputable def Ns432p753 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz196) qz196 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 797852 1000 623 417 268435456 134217728 4503599627370496 Bool.false 411537657379 2597 

noncomputable def Ns432p754 := Ns432p753 186065264 40 189812528 16 294906480 40 154981288 8 Bool.false 268435448 2640 Bool.false 392536556 Bool.false 414784910 14148475504056880 1 Bool.false 266857434 Bool.false Bool.false 268347485 Bool.true Bool.false 302201648 

noncomputable def Ns432p755 := nat_lit 489166369545137514002509990960163772978573966920097997 

noncomputable def Ns432p756 := nat_lit 319070673397949463947849096391877980903778025472000 

noncomputable def Ns432p757 := nat_lit 155186293203360599695674573455360000 

noncomputable def Ns432p758 := nat_lit 742894302583181913820675333011611320320 

noncomputable abbrev qz507 := (@Eq.refl Real qz549)

noncomputable abbrev qz402 := qz507

noncomputable abbrev qz199 := qz402

noncomputable def Ns432p759 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz196 797852 1000 2546272255616 16000000 1595704 4000 2000 Ns432p757 Ns432p758 qz199 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns432p760 := nat_lit 5129281151121621138826959162810446884147811759372086773022720 

noncomputable abbrev qz508 := (Real.log (Enclosure.sfrac Bool.false 2546272255616 16000000))

noncomputable abbrev qz509 := (@HSub.hSub Real Real Real qz528 qz529 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz530 (@Nat.cast Real Real.instNatCast 1595704))))

noncomputable abbrev qz403 := (@HSub.hSub Real Real Real qz456 (@HMul.hMul Real Real Real qz453 (Enclosure.sfrac Bool.false 797852 4000) qz508) (@HMul.hMul Real Real Real qz453 qz458 qz509))

noncomputable abbrev qz404 := (Enclosure.sfrac Bool.false 797852 2000)

noncomputable abbrev qz200 := (@HSub.hSub Real Real Real qz303 (@HSub.hSub Real Real Real qz303 qz403 qz404) (@HMul.hMul Real Real Real qz296 qz404 (Real.log Real.pi)))

noncomputable def Ns432p761 := @Enclosure.Real.IsNear.addLit_ft_p qz200 (Enclosure.sfrac Bool.true Ns432p757 Ns432p758) 6904457110766746560321 4503599627370496000 1673406765689625651 173056000000000000000000 Ns432p757 Ns432p758 0 1 Ns432p760 

noncomputable def Ns432p762 := nat_lit 115837568310069632659762446336000 

noncomputable abbrev qz201 := (@HSub.hSub Real Real Real qz303 qz403 qz404)

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz296 qz404 (Real.log Real.pi))

noncomputable def Ns432p763 := @Enclosure.Real.IsNear.subLit_ff_p qz201 qz202 8961082234587638097729 4503599627370496000 157393112019581 42250000000000000000 7661525621343 16777216000 199463 33554432000 Ns432p762 6904457110766746560321 4503599627370496000 

noncomputable abbrev qz203 := qz403

noncomputable abbrev qz204 := qz404

noncomputable def Ns432p764 := @Enclosure.Real.IsNear.subLit_ff_p qz203 qz204 430307408781441623401 180143985094819840 157393112019581 42250000000000000000 797852 2000 0 1 716886578767011047818320 8961082234587638097729 4503599627370496000 157393112019581 42250000000000000000 

noncomputable def Ns432p765 := nat_lit 968966142921432096697453533565288448 

noncomputable def Ns432p766 := nat_lit 57919888742963861467955200 

noncomputable def Ns432p767 := nat_lit 1052493671047625088683851892524024859087002496832961519125971449806092689735680 

noncomputable def Ns432p768 := nat_lit 3300607602380862209961658068474780638359685004022358170680453610116728487936 

noncomputable def Ns432p769 := nat_lit 123102568332618954666730190894774342532956019595614789534385705309962240 

noncomputable def Ns432p770 := BSN.log_dyadic_bound 449120255616 4643424255616 4 3 Ns432p767 134217728 54080000 Ns432p768 Ns432p769 26044976 5092544511232 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 449120255616) (BSN.artanhQ 4643424255616) 0 3 Ns432p768 Ns432p767 Ns432p769 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz405 := qz508

noncomputable abbrev qz205 := qz405

noncomputable abbrev qz406 := (Enclosure.sfrac Bool.false 797852 4000)

noncomputable def Ns432p771 := @Enclosure.Real.IsNear.mulLit_ff qz406 qz205 797852 4000 0 1 53942099905539175 4503599627370496 3125002873 169000000000000000 430378122938342418521 180143985094819840 623322448057199 169000000000000000000 (Enclosure.Real.IsNear.const Bool.false 797852 4000) (BSN.isNear_log_sfrac 2546272255616 16000000 53942099905539175 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2546272255616) qz308)) Bool.false Ns432p766 Ns432p103 1000000919360000 54080000000000000000000 53942099905539175 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2546272255616 16000000 17 5092544511232 4194304000000 26044976 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns432p770 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns432p772 := BSN.arctan_dyadic_bound_f 1000 1595704 1 0 16777216 6760000 0 1 1 0 1 1 10513 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1595704) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1595704) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz510 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz530 (@Nat.cast Real Real.instNatCast 1595704)))

noncomputable abbrev qz407 := qz510

noncomputable abbrev qz206 := qz407

noncomputable def Ns432p773 := @Enclosure.Real.IsNear.subLit_ff_p qz39 qz206 884279719003555 562949953421312 1 2000000000000000 10513 16777216 1 6760000 14829833557281628749824 883926961259939 562949953421312 50000000169 338000000000000000 qz41 (Ns432p772 rfl) rfl rfl 

noncomputable abbrev qz408 := (@HMul.hMul Real Real Real qz453 (Enclosure.sfrac Bool.false 797852 4000) qz508)

noncomputable abbrev qz207 := qz408

noncomputable abbrev qz409 := (@HMul.hMul Real Real Real qz453 qz458 qz509)

noncomputable abbrev qz208 := qz409

noncomputable abbrev qz410 := qz509

noncomputable abbrev qz209 := qz410

noncomputable def Ns432p774 := @Enclosure.Real.IsNear.subLit_ff_p qz207 qz208 430378122938342418521 180143985094819840 623322448057199 169000000000000000000 883926961259939 2251799813685248 50000000169 1352000000000000000 Ns432p765 430307408781441623401 180143985094819840 157393112019581 42250000000000000000 (Ns432p771 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 qz209 1 4 0 1 883926961259939 562949953421312 50000000169 338000000000000000 883926961259939 2251799813685248 50000000169 1352000000000000000 qz46 Ns432p773 rfl) 

noncomputable def Ns432p775 := @Ns432p761 Ns432p755 Ns432p756 1673406765689625651 173056000000000000000000 (@Ns432p763 1673406765689625651 173056000000000000000000 (Ns432p764 (Ns432p774 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 797852 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz204 (Real.log Real.pi) 797852 2000 0 1 38410761 33554432 1 67108864 7661525621343 16777216000 199463 33554432000 (Enclosure.Real.IsNear.const Bool.false 797852 2000) RS433to438.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns432p757 Ns432p758) 

noncomputable def Ns432p776 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz196) Bool.false Ns432p755 Ns432p756 1673406765689625651 173056000000000000000000 12860551793 8388608 325 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz196) (@HAdd.hAdd Real Real Real qz47 qz200 (Enclosure.sfrac Bool.true Ns432p757 Ns432p758)) Bool.false Ns432p755 Ns432p756 1673406765689625651 173056000000000000000000 Ns432p759 (Ns432p775 rfl rfl)) 

noncomputable def Ns432p777 := nat_lit 1208925819614629174706176 

noncomputable def Ns432p778 := BSN.cos_dyadic_bound_f 1891348 68719476736 1 0 33554432 13533204 0 1 1 0 1 1 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1891348) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1891348) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable abbrev qz411 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable def Ns432p779 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz196) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12860551793) qz411) Bool.false 12860551793 8388608 325 33554432 Bool.false 33554431 33554432 1 6760000 (Ns432p776 rfl) (Enclosure.sfrac_false_div 12860551793 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12860551793) qz411) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 33272947299483385856) (@Nat.cast Real Real.instNatCast Ns432p777)) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 244 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q0 12860551793 8388608 226375608064910080 72057594037927936 244 33272947299483385856 Ns432p777 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554431 33554432 33272947299483385856 Ns432p777 1891348 68719476736 13533204 13520000 (Ns432p778 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns432p780 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz196) Bool.false Ns432p755 Ns432p756 1673406765689625651 173056000000000000000000 411537657379 268435456 2597 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz196) (@HAdd.hAdd Real Real Real qz47 qz200 (Enclosure.sfrac Bool.true Ns432p757 Ns432p758)) Bool.false Ns432p755 Ns432p756 1673406765689625651 173056000000000000000000 Ns432p759 (Ns432p775 rfl rfl)) 

noncomputable def Ns432p781 := Ns432p754 46997 BSN.abs_quadSignPos (BSN.cos_quad_nat3 623 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266857434 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 417 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268347485 268435456) qz199 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz196) qz196 1) Bool.false 33554431 33554432 34852413 3544186880000 268435448 268435456 2640 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz196) qz196 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz196)) Bool.false 33554431 33554432 34852413 3544186880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz196) qz196) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz196)) Bool.false 33554431 33554432 2230554432 226827960320000 33554431 33554432 34852413 3544186880000 (Ns432p779 rfl rfl) rfl)) rfl) (Ns432p780 rfl) RS433to438.d7 

noncomputable def Ns432p782 := nat_lit 33265564953411626966536249376124428325916302507627202589725757221140691769498613120359153675497125006001831936 

noncomputable def Ns432p783 := nat_lit 13383240838081341472373718928879214522106136652855374112339383400039885962511516142862997370000098983936 

noncomputable def Ns432p784 := nat_lit 166172531141891114820398621346159474636191918553749419586086540856076858139650262470739871998845556371012714496 

noncomputable def Ns432p785 := BSN.sin_dyadic_bound_f 392536556 268435456 4 3 268435456 134217728 Ns432p782 Ns432p272 Ns432p783 Ns432p784 Ns432p275 Ns432p783 266857434 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 392536556) qz51 0 3 Ns432p782 Ns432p272 Ns432p783 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 392536556) qz52 0 3 Ns432p784 Ns432p275 Ns432p783 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p786 := nat_lit 41488536136640365967517366461722032840201786939526253610637151754463084368953996904778513876449240169638400000 

noncomputable def Ns432p787 := nat_lit 25934350672628848950070317071074286572140549048725381579972149613449975853607191551435158481000000000000 

noncomputable def Ns432p788 := nat_lit 207201282894251344871890143830311984106571447960519349391652019785313046446188764138564021619799299184192000000 

noncomputable def Ns432p789 := BSN.sin_dyadic_bound_f 414784910 268435456 4 3 268435456 134217728 Ns432p786 Ns432p272 Ns432p787 Ns432p788 Ns432p275 Ns432p787 268347485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 414784910) qz51 0 3 Ns432p786 Ns432p272 Ns432p787 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 414784910) qz52 0 3 Ns432p788 Ns432p275 Ns432p787 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p790 := nat_lit 24424100814134669606410351846148727937275147880981610186279038577365717110225562607763807010422453698796268321 

noncomputable def Ns432p791 := nat_lit 5303406637174060336694587327505122190809286352716173957416721396317632054792905104068355812678985657121 

noncomputable def Ns432p792 := nat_lit 122036729996659675468708717341953309499889629543976809816891910534004875156849530337067716916586787643573218081 

noncomputable def Ns432p793 := BSN.sin_dyadic_bound_f 363395527 268435456 4 3 268435456 134217728 Ns432p790 Ns432p272 Ns432p791 Ns432p792 Ns432p275 Ns432p791 262137583 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 363395527) qz51 0 3 Ns432p790 Ns432p272 Ns432p791 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 363395527) qz52 0 3 Ns432p792 Ns432p275 Ns432p791 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p794 := nat_lit 20302938915589336873449365232741620525304115919732239241031167651190625 

noncomputable def Ns432p795 := nat_lit 5414377820922704844003319441432924851541500345157942445793750390625 

noncomputable def Ns432p796 := nat_lit 60897987991126165210660089059341995726209264758506401838201915452790625 

noncomputable def Ns432p797 := BSN.cos_dyadic_bound_f 219630965 268435456 3 2 268435456 134217728 Ns432p794 Ns432p131 Ns432p795 Ns432p796 Ns432p134 Ns432p795 183487476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 219630965) qz49 0 2 Ns432p794 Ns432p131 Ns432p795 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 219630965) qz50 0 2 Ns432p796 Ns432p134 Ns432p795 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p798 := Ns432p752 79715 BSN.abs_quadSignPos (BSN.cos_quad_nat3 271 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 262137583 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 158 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 183487476 268435456) qz199 rfl rfl (Ns432p781 RS433to438.d9 RS433to438.d11 RS433to438.d13 RS433to438.d17 (Ns432p785 rfl rfl) (Ns432p789 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns432p780 rfl) RS433to438.d19 RS433to438.d21 RS433to438.d23 RS433to438.d25 RS433to438.d17 (Ns432p793 rfl rfl) (Ns432p797 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns432p799 := nat_lit 30987216740999217571994816310958294143955932697659866361672193452084237326510214399671664512632693233007853521 

noncomputable def Ns432p800 := nat_lit 10820788433250678983242780547129352103349108260936750972621358469129359016774680390060162232878401978321 

noncomputable def Ns432p801 := nat_lit 154801308977040332475292448391122501728823730883945422927217733931814947377411388811818070013882545480132067281 

noncomputable def Ns432p802 := BSN.sin_dyadic_bound_f 385645477 268435456 4 3 268435456 134217728 Ns432p799 Ns432p272 Ns432p800 Ns432p801 Ns432p275 Ns432p800 266023485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 385645477) qz51 0 3 Ns432p799 Ns432p272 Ns432p800 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 385645477) qz52 0 3 Ns432p801 Ns432p275 Ns432p800 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p803 := nat_lit 5927649076740460714401762596994210310153932594443288718753965027977441 

noncomputable def Ns432p804 := nat_lit 461699837331475441719924792049193585532890380714737986053689665761 

noncomputable def Ns432p805 := nat_lit 17782023830546719192321847941398532543290732002568436680289787704600801 

noncomputable def Ns432p806 := BSN.cos_dyadic_bound_f 161452571 268435456 3 2 268435456 134217728 Ns432p803 Ns432p131 Ns432p804 Ns432p805 Ns432p134 Ns432p804 221328163 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 161452571) qz49 0 2 Ns432p803 Ns432p131 Ns432p804 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 161452571) qz50 0 2 Ns432p805 Ns432p134 Ns432p804 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p807 := Ns432p750 107495 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 266023485 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 221328163 268435456) qz199 rfl rfl (Ns432p798 rfl rfl) (Ns432p780 rfl) RS433to438.d27 RS433to438.d29 RS433to438.d31 RS433to438.d33 RS433to438.d17 (Ns432p802 rfl rfl) (Ns432p806 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p808 := nat_lit 509328109435841332935044260351680172633548968642359458003336937736481 

noncomputable def Ns432p809 := nat_lit 3409195325823206384440924810862870736649086020204028890531367201 

noncomputable def Ns432p810 := nat_lit 1527977509916872352392363899205418792159173607755037965952229750475041 

noncomputable def Ns432p811 := BSN.cos_dyadic_bound_f 87414099 268435456 3 2 268435456 134217728 Ns432p808 Ns432p131 Ns432p809 Ns432p810 Ns432p134 Ns432p809 254327897 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 87414099) qz49 0 2 Ns432p808 Ns432p131 Ns432p809 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 87414099) qz50 0 2 Ns432p810 Ns432p134 Ns432p809 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p812 := nat_lit 35886205462047563388342200625 

noncomputable def Ns432p813 := BSN.cos_dyadic_bound_f 13763595 268435456 2 1 268435456 134217728 Ns432p812 Ns432p166 Ns432p812 Ns432p812 Ns432p167 Ns432p812 268082680 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13763595) qz49 0 1 Ns432p812 Ns432p166 Ns432p812 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13763595) qz50 0 1 Ns432p812 Ns432p167 Ns432p812 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p814 := Ns432p748 131768 BSN.abs_quadSignPos (BSN.cos_quad_nat0 80 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 254327897 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268082680 268435456) qz199 rfl rfl (Ns432p807 rfl) (Ns432p780 rfl) RS433to438.d35 RS433to438.d37 RS433to438.d39 RS433to438.d41 RS433to438.d17 (Ns432p811 rfl rfl) (Ns432p813 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p815 := nat_lit 44845134319067698742402475427781372661980834643534227312988237290536960 

noncomputable def Ns432p816 := nat_lit 8154364164532095519014317037527219882511025741145647650218480500736 

noncomputable def Ns432p817 := nat_lit 117438339960339492361166174368985693853949549072342073818773601078214656 

noncomputable def Ns432p818 := BSN.sin_dyadic_bound_f 231165896 268435456 3 2 268435456 134217728 Ns432p815 Ns432p137 Ns432p816 Ns432p817 Ns432p140 Ns432p816 203634848 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 231165896) qz51 0 2 Ns432p815 Ns432p137 Ns432p816 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 231165896) qz52 0 2 Ns432p817 Ns432p140 Ns432p816 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p819 := nat_lit 37467413337565184479832255750645784466868748742024367793235826754860331996258997919982597757270416312317771776 

noncomputable def Ns432p820 := nat_lit 19111270184058041680986513990338429728175635184051897239382730279202263838489917943822964353847290494976 

noncomputable def Ns432p821 := nat_lit 187140130884649961787967424678233868268395301260130114213159107447552389437566331505518324745663645598284251136 

noncomputable def Ns432p822 := BSN.sin_dyadic_bound_f 404365532 268435456 4 3 268435456 134217728 Ns432p819 Ns432p272 Ns432p820 Ns432p821 Ns432p275 Ns432p820 267878699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 404365532) qz51 0 3 Ns432p819 Ns432p272 Ns432p820 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 404365532) qz52 0 3 Ns432p821 Ns432p275 Ns432p820 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p823 := Ns432p746 153599 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 203634848 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267878699 268435456) qz199 rfl rfl (Ns432p814 rfl) (Ns432p780 rfl) RS433to438.d43 RS433to438.d45 RS433to438.d47 RS433to438.d49 RS433to438.d17 (Ns432p818 rfl rfl) (Ns432p822 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p824 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz196) qz196 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz196) qz196 11) 360378821 268435456 153599 268435456 360378821 268435456 153599 268435456 193476906295754752 360378821 134217728 153599 134217728 (Ns432p823 rfl) 

noncomputable def Ns432p825 := @Enclosure.Real.IsNear.mulLit_tf qz197 qz198 9995725 33554432 1 33554432 16966393934061 35184372088832 1763140781595417 14865397207531520000 169591408006541889225 1180591620717411303424 

noncomputable abbrev qz210 := (@HPow.hPow Real Real Real qz298 qz400 qz300)

noncomputable def Ns432p826 := @Enclosure.Real.IsNear.mulLit_tf qz53 qz210 1 1 0 1 9995725 33554432 1 33554432 9995725 33554432 1 33554432 

noncomputable abbrev qz211 := qz400

noncomputable def Ns432p827 := @Enclosure.Real.IsNear.sqrt_image qz211 1065202830439 8388608000 199463 8388608000 189056259 189056295 16777216 (@Enclosure.Real.IsNear.of_eq qz211 (@HMul.hMul Real Real Real qz29 qz196 qz27) Bool.false 1065202830439 8388608000 199463 8388608000 (BSN.t_div_two_pi_mk qz196 797852 1000 qz199) (@Enclosure.Real.IsNear.mulLit_ff qz196 qz27 797852 1000 0 1 5340353 33554432 1 33554432 1065202830439 8388608000 199463 8388608000 (Enclosure.Real.IsNear.const Bool.false 797852 1000) RS433to438.d52 rfl)) 

noncomputable abbrev qz552 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 797852 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz511 := qz552

noncomputable abbrev qz412 := qz511

noncomputable abbrev qz212 := qz412

noncomputable def Ns432p828 := @Enclosure.Real.IsNear.sqrt_image qz212 189056277 16777216 9 8388608 56319070 56319076 16777216 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 378112554 33554432 36 33554432 189056277 16777216 9 8388608 (Ns432p827 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz213 := (Real.sqrt qz412)

noncomputable def Ns432p829 := @Enclosure.Real.IsNear.inv_image qz213 56319073 16777216 3 16777216 4997862 4997863 16777216 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 112638146 33554432 6 33554432 56319073 16777216 3 16777216 (Ns432p828 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns432p830 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz213) Bool.false 9995725 33554432 1 33554432 9995725 33554432 1 33554432 (Ns432p829 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz413 := (Real.cos (@HMul.hMul Real Real Real qz453 qz451 qz506))

noncomputable abbrev qz214 := (@Inv.inv Real Real.instInv qz413)

noncomputable abbrev qz512 := (@HMul.hMul Real Real Real qz524 qz551 qz551)

noncomputable abbrev qz414 := (@HSub.hSub Real Real Real qz456 (@HSub.hSub Real Real Real qz456 qz512 qz506) qz466)

noncomputable abbrev qz215 := (Real.cos (@HMul.hMul Real Real Real qz296 qz293 qz414))

noncomputable def Ns432p831 := @Enclosure.Real.IsNear.of_eq qz198 (@HMul.hMul Real Real Real qz29 qz214 qz215) Bool.false 16966393934061 

noncomputable def Ns432p832 := @Enclosure.Real.IsNear.mulLit_tt qz214 qz215 17954673 2097152 4251 

noncomputable abbrev qz216 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz413))

noncomputable abbrev qz217 := qz413

noncomputable def Ns432p833 := @Enclosure.Real.IsNear.of_eq qz214 (@Neg.neg Real Real.instNeg qz216) Bool.true 17954673 2097152 4251 8388608 (BSN.inv_eq_neg_inv_neg qz217) 

noncomputable def Ns432p834 := @Enclosure.Real.IsNear.recentre' qz216 Bool.false 287274768 33554432 17004 33554432 17954673 2097152 

noncomputable def Ns432p835 := @Enclosure.Real.IsNear.recentre' qz217 Bool.true 1959622 16777216 1568074432 226827960320000 979811 8388608 24501163 3544186880000 

noncomputable abbrev qz415 := (@HMul.hMul Real Real Real qz453 qz451 qz506)

noncomputable abbrev qz218 := qz415

noncomputable def Ns432p836 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14158847) qz411) Bool.false 14158847 8388608 227 33554432 Bool.true 1959622 16777216 1 

noncomputable def Ns432p837 := nat_lit 242874678700753401497830399 

noncomputable abbrev qz219 := qz401

noncomputable def Ns432p838 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz219 884279719003555 140737488355328 1 500000000000000 4506901 16777216 9 8388608 3985361149856841033055 2361183241434822606848 Ns432p837 

noncomputable def Ns432p839 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz22 189056277 16777216 9 8388608 11 1 0 1 4506901 4506901 16777216 9 

noncomputable def Ns432p840 := @Ns432p839 8388608 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 378112554 33554432 36 33554432 189056277 16777216 9 8388608 (Ns432p827 rfl rfl rfl rfl rfl rfl) rfl) qz64 

noncomputable def Ns432p841 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 3985361149856841033055 2361183241434822606848 Ns432p837 Ns432p185 14158847 8388608 227 33554432 (@Ns432p838 Ns432p185 RS433to438.d51 (Ns432p840 rfl rfl) rfl) 

noncomputable def Ns432p842 := nat_lit 19762912980287389841508770735983448801374618169644159557222044393528675240606725812554526721 

noncomputable def Ns432p843 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns432p844 := nat_lit 64913446149423134469073055932976924912312233121676568816592575143661686219860978135041 

noncomputable def Ns432p845 := nat_lit 119510387454215017892569530585583756825112120263586221139221759710979910869453406396542316545 

noncomputable def Ns432p846 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns432p847 := BSN.cos_dyadic_bound_t 14158847 8388608 4 3 16777216 6760000 Ns432p842 Ns432p843 Ns432p844 Ns432p845 Ns432p846 Ns432p844 1959622 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 14158847) (BSN.cosEvenQ 8388608) 0 3 Ns432p842 Ns432p843 Ns432p844 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 14158847) (BSN.cosOddQ 8388608) 0 3 Ns432p845 Ns432p846 Ns432p844 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz220 := (@Neg.neg Real Real.instNeg qz413)

noncomputable def Ns432p848 := @Enclosure.Real.IsNear.inv_image qz220 979811 8388608 24501163 3544186880000 143628882 143645886 16777216 (@Enclosure.Real.IsNear.neg qz217 Bool.true 979811 8388608 24501163 3544186880000 (Ns432p835 (@Ns432p836 6760000 (Ns432p841 rfl) (Enclosure.sfrac_false_div 14158847 8388608) (Ns432p847 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns432p849 := Ns432p833 (@Enclosure.Real.IsNear.neg qz216 Bool.false 17954673 2097152 4251 8388608 (@Ns432p834 4251 8388608 (Ns432p848 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns432p850 := @Enclosure.Real.IsNear.recentre' qz215 Bool.true 944957 16777216 

noncomputable abbrev qz221 := (@HMul.hMul Real Real Real qz296 qz293 qz414)

noncomputable def Ns432p851 := @Enclosure.Real.IsNear.cos_image qz221 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13649523)) qz411) Bool.true 13649523 8388608 

noncomputable def Ns432p852 := nat_lit 64458050029520086601002161205 

noncomputable def Ns432p853 := nat_lit 1565997395418350393805420907927921 

noncomputable def Ns432p854 := @Enclosure.Real.IsNear.recentre' qz221 Bool.true Ns432p852 Ns432p484 Ns432p853 

noncomputable abbrev qz222 := qz414

noncomputable def Ns432p855 := @Enclosure.Real.IsNear.mulLit_ft qz26 qz222 884279719003555 140737488355328 1 500000000000000 72893280988231 

noncomputable abbrev qz416 := (@HSub.hSub Real Real Real qz456 qz512 qz506)

noncomputable abbrev qz223 := qz416

noncomputable def Ns432p856 := @Enclosure.Real.IsNear.subLit_tf qz223 qz68 55301094943815 281474976710656 58029831 35184372088832 1 16 

noncomputable abbrev qz417 := qz512

noncomputable abbrev qz224 := qz417

noncomputable def Ns432p857 := @Enclosure.Real.IsNear.subLit_ff_n qz224 qz219 20312156623801 281474976710656 20281095 35184372088832 4506901 16777216 9 8388608 

noncomputable def Ns432p858 := @Enclosure.Real.IsNear.mulLit_ff qz219 qz219 4506901 16777216 9 8388608 4506901 16777216 9 8388608 20312156623801 281474976710656 

noncomputable def Ns432p859 := nat_lit 17057847646357175424215520276198720481791032983305971329495803771440563246995194089781447601 

noncomputable def Ns432p860 := nat_lit 41822471704299821781800432274554466874831177558889665707656103268711824936439299558321 

noncomputable def Ns432p861 := nat_lit 103197398793166109491754776264716051775944579109370248835744322916841062502646015743759862705 

noncomputable def Ns432p862 := BSN.cos_dyadic_bound_t 13649523 8388608 4 3 16777216 6760000 Ns432p859 Ns432p843 Ns432p860 Ns432p861 Ns432p846 Ns432p860 944957 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13649523) (BSN.cosEvenQ 8388608) 0 3 Ns432p859 Ns432p843 Ns432p860 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13649523) (BSN.cosOddQ 8388608) 0 3 Ns432p861 Ns432p846 Ns432p860 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p863 := @Ns432p850 596508608 56706990080000 944957 16777216 9320447 886046720000 (@Ns432p851 87 8388608 Bool.true 944957 16777216 1 6760000 (@Ns432p854 Ns432p487 13649523 8388608 87 8388608 (@Ns432p855 281474976710656 58029831 35184372088832 Ns432p852 Ns432p484 Ns432p853 Ns432p487 RS433to438.d51 (@Ns432p856 0 1 1166292495811696 72893280988231 281474976710656 58029831 35184372088832 (@Ns432p857 927798414908892119040 55301094943815 281474976710656 58029831 35184372088832 (@Ns432p858 20281095 35184372088832 (Ns432p840 rfl rfl) (Ns432p840 rfl rfl) rfl) (Ns432p840 rfl rfl) rfl rfl) qz70 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 13649523 8388608) (BSN.cos_neg_of_bound 13649523 8388608 Bool.true 944957 16777216 1 6760000 (Ns432p862 rfl rfl)) rfl rfl) 

noncomputable def Ns432p864 := @Ns432p825 678116940526568152317 Ns432p742 (Ns432p826 qz71 (@Enclosure.Real.IsNear.of_eq qz210 (@Inv.inv Real Real.instInv qz213) Bool.false 9995725 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz211 (BSN.t_div_two_pi_nonneg qz196 797852 1000 qz199)) Ns432p830) rfl) (@Ns432p831 35184372088832 1763140781595417 14865397207531520000 (BSN.correction_mk qz219 (BSN.cos_two_pi_p_ne_zero_mk qz196 797852 1000 11 qz199 rfl rfl (@BSN.floor_sqrt_eq_dec qz196 797852 1000 11 qz199 rfl rfl rfl))) (@Ns432p832 8388608 944957 16777216 9320447 886046720000 16966393934061 35184372088832 1763140781595417 14865397207531520000 Ns432p849 (Ns432p863 rfl) rfl)) 

noncomputable def Ns432p865 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz196) (hardyZApproximantRS₀ qz196) Bool.false 3339517040756187745993 1180591620717411303424 22633022187446125272317 Ns432p742 (@Eq.refl Real (hardyZApproximantRS₀ qz196)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz196) (@HSub.hSub Real Real Real qz72 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz196) qz196 11) (@HMul.hMul Real Real Real qz29 qz197 qz198)) Bool.false 3339517040756187745993 1180591620717411303424 22633022187446125272317 Ns432p742 (BSN.hardyZApproximantRS₀_eq qz196 11 (@BSN.floor_sqrt_eq_dec qz196 797852 1000 11 qz199 rfl rfl rfl)) (@Ns432p744 3339517040756187745993 1180591620717411303424 22633022187446125272317 Ns432p742 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz196) qz196 11) (@HAdd.hAdd Real Real Real qz47 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz196) qz196 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz196) qz196 11)) Bool.false 360378821 134217728 153599 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz196) qz196 11) (Ns432p824 (Ns432p823 rfl) rfl rfl)) (Ns432p864 rfl) rfl rfl)) 

theorem RS433to438.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz196) Bool.false 3339517040756187745993 1180591620717411303424 22633022187446125272317 Ns432p742 := Ns432p865 

noncomputable def Ns432p866 := nat_lit 124699989938276568924160000 

noncomputable def Ns432p867 := nat_lit 6526523729557831881435643904 

noncomputable abbrev qz553 := (Enclosure.sfrac Bool.false 799149 1000)

noncomputable abbrev qz513 := qz553

noncomputable abbrev qz418 := qz513

noncomputable abbrev qz225 := qz418

noncomputable abbrev qz554 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 799149 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz514 := qz554

noncomputable abbrev qz419 := qz514

noncomputable abbrev qz226 := (@HMul.hMul Real Real Real qz296 qz297 (@HPow.hPow Real Real Real qz298 qz419 qz300))

noncomputable abbrev qz555 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 799149 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz515 := qz555

noncomputable abbrev qz420 := qz515

noncomputable abbrev qz227 := (Zeta.RiemannSiegel.correction qz420)

noncomputable def Ns432p868 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz225) qz225 11) (@HMul.hMul Real Real Real qz29 qz226 qz227) 97924639 67108864 153851 134217728 10416497096654132753 73786976294838206464 2984699282385607593907 Ns432p866 Ns432p867 

noncomputable def Ns432p869 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz225) qz225 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 799149 1000 193 241 268435456 134217728 4503599627370496 Bool.false 412381052159 2601 

noncomputable def Ns432p870 := Ns432p869 618095470 41 84886744 8 643680110 41 80936328 8 Bool.true 60231286 131985 Bool.true 189440940 Bool.true 395823855 14148475504056880 1 Bool.false 174102920 Bool.true Bool.false 267193335 Bool.true Bool.true 195849278 

noncomputable def Ns432p871 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz225) qz225 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 799149 1000 79 139 268435456 134217728 4503599627370496 Bool.false 412381052159 2601 

noncomputable def Ns432p872 := Ns432p871 558195838 41 94906264 8 589812974 41 89478488 8 Bool.true 241360422 107673 Bool.true 389656749 Bool.true 357013671 14148475504056880 1 Bool.false 266530284 Bool.false Bool.false 260689349 Bool.false Bool.true 60231286 

noncomputable def Ns432p873 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz225) qz225 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 799149 1000 66 11 268435456 134217728 4503599627370496 Bool.false 412381052159 2601 

noncomputable def Ns432p874 := Ns432p873 480971758 41 109588312 8 522351262 41 101459064 8 Bool.true 257856736 79848 Bool.false 183562459 Bool.true 417204806 14148475504056880 1 Bool.false 208081202 Bool.true Bool.false 268398528 Bool.false Bool.true 241360422 

noncomputable def Ns432p875 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz225) qz225 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 799149 1000 272 159 268435456 134217728 4503599627370496 Bool.false 412381052159 2601 

noncomputable def Ns432p876 := Ns432p875 372130544 40 134217720 8 432030192 40 120047984 16 Bool.true 351195082 47077 Bool.false 302479563 Bool.false 81025158 14148475504056880 1 Bool.false 115301054 Bool.false Bool.false 79800400 Bool.false Bool.true 257856736 

noncomputable def Ns432p877 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz225) qz225 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 799149 1000 625 419 268435456 134217728 4503599627370496 Bool.false 412381052159 2601 

noncomputable def Ns432p878 := Ns432p877 186065264 40 189812528 16 294906480 40 154981288 8 Bool.true 268435440 2648 Bool.false 151289832 Bool.false 32371129 14148475504056880 1 Bool.false 143406712 Bool.true Bool.false 32292727 Bool.false Bool.true 351195082 

noncomputable def Ns432p879 := nat_lit 7208512596991414506964257981919849538485967683586615794707 

noncomputable def Ns432p880 := nat_lit 4692311530615706681803881276644227254246815914000384000 

noncomputable def Ns432p881 := nat_lit 156451766015928090917318145959520000 

noncomputable def Ns432p882 := nat_lit 750169771200528148402407628655162690880 

noncomputable abbrev qz516 := (@Eq.refl Real qz553)

noncomputable abbrev qz421 := qz516

noncomputable abbrev qz228 := qz421

noncomputable def Ns432p883 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz225 799149 1000 2554557496804 16000000 1598298 4000 2000 Ns432p881 Ns432p882 qz228 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns432p884 := nat_lit 20760516279335273780057062987929166670839586928729453488756160 

noncomputable abbrev qz517 := (Real.log (Enclosure.sfrac Bool.false 2554557496804 16000000))

noncomputable abbrev qz518 := (@HSub.hSub Real Real Real qz528 qz529 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz530 (@Nat.cast Real Real.instNatCast 1598298))))

noncomputable abbrev qz422 := (@HSub.hSub Real Real Real qz456 (@HMul.hMul Real Real Real qz453 (Enclosure.sfrac Bool.false 799149 4000) qz517) (@HMul.hMul Real Real Real qz453 qz458 qz518))

noncomputable abbrev qz423 := (Enclosure.sfrac Bool.false 799149 2000)

noncomputable abbrev qz229 := (@HSub.hSub Real Real Real qz303 (@HSub.hSub Real Real Real qz303 qz422 qz423) (@HMul.hMul Real Real Real qz296 qz423 (Real.log Real.pi)))

noncomputable def Ns432p885 := @Enclosure.Real.IsNear.addLit_ft_p qz229 (Enclosure.sfrac Bool.true Ns432p881 Ns432p882) 27674427702539659596507 18014398509481984000 6704466706076167473 692224000000000000000000 Ns432p881 Ns432p882 0 1 Ns432p884 

noncomputable def Ns432p886 := nat_lit 1857199404967566470468283138048000 

noncomputable abbrev qz230 := (@HSub.hSub Real Real Real qz303 qz422 qz423)

noncomputable abbrev qz231 := (@HMul.hMul Real Real Real qz296 qz423 (Real.log Real.pi))

noncomputable def Ns432p887 := @Enclosure.Real.IsNear.subLit_ff_p qz230 qz231 35914301318580437340891 18014398509481984000 2522342921039577 676000000000000000000 30695921242389 67108864000 799149 134217728000 Ns432p886 27674427702539659596507 18014398509481984000 

noncomputable def Ns432p888 := nat_lit 71828602637160874681782000 

noncomputable abbrev qz232 := qz422

noncomputable abbrev qz233 := qz423

noncomputable def Ns432p889 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz233 43112395595807446356699 18014398509481984000 2522342921039577 676000000000000000000 799149 2000 0 1 Ns432p888 35914301318580437340891 18014398509481984000 2522342921039577 676000000000000000000 

noncomputable def Ns432p890 := nat_lit 97080484370163914147258200498322276352 

noncomputable def Ns432p891 := nat_lit 57935597946982476099354624 

noncomputable def Ns432p892 := nat_lit 1063811811890355934138379841259917881926048039606924081896460636321500144046080 

noncomputable def Ns432p893 := nat_lit 3448662186751743317506809549547986713799985423117543661914777259147301974016 

noncomputable def Ns432p894 := nat_lit 137372415665364965319841967227814444115041771787371555110886574809149440 

noncomputable def Ns432p895 := BSN.log_dyadic_bound 457405496804 4651709496804 4 3 Ns432p892 134217728 54080000 Ns432p893 Ns432p894 26480994 5109114993608 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 457405496804) (BSN.artanhQ 4651709496804) 0 3 Ns432p893 Ns432p892 Ns432p894 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz424 := qz517

noncomputable abbrev qz234 := qz424

noncomputable abbrev qz425 := (Enclosure.sfrac Bool.false 799149 4000)

noncomputable def Ns432p896 := @Enclosure.Real.IsNear.mulLit_ff qz425 qz234 799149 4000 0 1 53956730241870951 4503599627370496 3125002873 169000000000000000 43119467016060928620699 18014398509481984000 192103301611929 52000000000000000000 (Enclosure.Real.IsNear.const Bool.false 799149 4000) (BSN.isNear_log_sfrac 2554557496804 16000000 53956730241870951 4503599627370496 3125002873 169000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2554557496804) qz308)) Bool.false Ns432p891 Ns432p103 1000000919360000 54080000000000000000000 53956730241870951 4503599627370496 3125002873 169000000000000000 (BSN.log_rat_reduce_isNear 2554557496804 16000000 17 5109114993608 4194304000000 26480994 134217728 24973259072661432 36028797018963968 54080000 1000000000000000 rfl rfl rfl rfl (Ns432p895 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns432p897 := BSN.arctan_dyadic_bound_f 1000 1598298 1 0 16777216 6760000 0 1 1 0 1 1 10496 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1598298) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1598298) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz519 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz530 (@Nat.cast Real Real.instNatCast 1598298)))

noncomputable abbrev qz426 := qz519

noncomputable abbrev qz235 := qz426

noncomputable def Ns432p898 := @Enclosure.Real.IsNear.subLit_ff_p qz39 qz235 884279719003555 562949953421312 1 2000000000000000 10496 16777216 1 6760000 14829843127430836912128 883927531685283 562949953421312 50000000169 338000000000000000 qz41 (Ns432p897 rfl) rfl rfl 

noncomputable abbrev qz427 := (@HMul.hMul Real Real Real qz453 (Enclosure.sfrac Bool.false 799149 4000) qz517)

noncomputable abbrev qz236 := qz427

noncomputable abbrev qz428 := (@HMul.hMul Real Real Real qz453 qz458 qz518)

noncomputable abbrev qz237 := qz428

noncomputable abbrev qz429 := qz518

noncomputable abbrev qz238 := qz429

noncomputable def Ns432p899 := @Enclosure.Real.IsNear.subLit_ff_p qz236 qz237 43119467016060928620699 18014398509481984000 192103301611929 52000000000000000000 883927531685283 2251799813685248 50000000169 1352000000000000000 Ns432p890 43112395595807446356699 18014398509481984000 2522342921039577 676000000000000000000 (Ns432p896 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 qz238 1 4 0 1 883927531685283 562949953421312 50000000169 338000000000000000 883927531685283 2251799813685248 50000000169 1352000000000000000 qz46 Ns432p898 rfl) 

noncomputable def Ns432p900 := @Ns432p885 Ns432p879 Ns432p880 6704466706076167473 692224000000000000000000 (@Ns432p887 6704466706076167473 692224000000000000000000 (Ns432p889 (Ns432p899 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 799149 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz233 (Real.log Real.pi) 799149 2000 0 1 38410761 33554432 1 67108864 30695921242389 67108864000 799149 134217728000 (Enclosure.Real.IsNear.const Bool.false 799149 2000) RS433to438.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns432p881 Ns432p882) 

noncomputable def Ns432p901 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz225) Bool.false Ns432p879 Ns432p880 6704466706076167473 692224000000000000000000 51547631519 33554432 163 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz225) (@HAdd.hAdd Real Real Real qz47 qz229 (Enclosure.sfrac Bool.true Ns432p881 Ns432p882)) Bool.false Ns432p879 Ns432p880 6704466706076167473 692224000000000000000000 Ns432p883 (Ns432p900 rfl rfl)) 

noncomputable def Ns432p902 := BSN.cos_dyadic_bound_f 22350731 68719476736 1 0 33554432 13533204 0 1 1 0 1 1 33554430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 22350731) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 22350731) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable def Ns432p903 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz225) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51547631519) qz48) Bool.false 51547631519 33554432 163 16777216 Bool.true 33554430 33554432 1 6760000 (Ns432p901 rfl) (Enclosure.sfrac_false_div 51547631519 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51547631519) qz48) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1572792923135974309888) qz316) 226375608064910080 72057594037927936 Bool.false 33554430 33554432 244 1000000000000000 13520000 6760000 (BSN.sin_reduce_arg_pos_rat_q2 51547631519 33554432 226375608064910080 72057594037927936 244 1572792923135974309888 Ns432p103 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554430 33554432 1572792923135974309888 Ns432p103 22350731 68719476736 13533204 13520000 (Ns432p902 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns432p904 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz225) Bool.false Ns432p879 Ns432p880 6704466706076167473 692224000000000000000000 412381052159 268435456 2601 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz225) (@HAdd.hAdd Real Real Real qz47 qz229 (Enclosure.sfrac Bool.true Ns432p881 Ns432p882)) Bool.false Ns432p879 Ns432p880 6704466706076167473 692224000000000000000000 Ns432p883 (Ns432p900 rfl rfl)) 

noncomputable def Ns432p905 := Ns432p878 47077 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 625 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 143406712 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 419 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 32292727 268435456) qz228 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz225) qz225 1) Bool.true 16777215 16777216 17479019 1772093440000 268435440 268435456 2648 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz225) qz225 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz225)) Bool.true 16777215 16777216 17479019 1772093440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz225) qz225) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz225)) Bool.true 33554430 33554432 1118657216 113413980160000 16777215 16777216 17479019 1772093440000 (Ns432p903 rfl rfl) rfl)) rfl) (Ns432p904 rfl) RS433to438.d7 

noncomputable def Ns432p906 := nat_lit 8226114569582765346372632607733384631979824577046310730800176803348480 

noncomputable def Ns432p907 := nat_lit 274459283302388608536346794692921654663892677579198409746442878976 

noncomputable def Ns432p908 := nat_lit 21544141414829514897038312268300790258220560923167114164194206910775296 

noncomputable def Ns432p909 := BSN.sin_dyadic_bound_f 151289832 268435456 3 2 268435456 134217728 Ns432p906 Ns432p137 Ns432p907 Ns432p908 Ns432p140 Ns432p907 143406712 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 151289832) qz51 0 2 Ns432p906 Ns432p137 Ns432p907 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 151289832) qz52 0 2 Ns432p908 Ns432p140 Ns432p907 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p910 := nat_lit 1098073436873405967765441398881 

noncomputable def Ns432p911 := BSN.sin_dyadic_bound_f 32371129 268435456 2 1 268435456 134217728 Ns432p910 Ns432p143 Ns432p910 Ns432p910 Ns432p144 Ns432p910 32292727 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32371129) qz51 0 1 Ns432p910 Ns432p143 Ns432p910 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32371129) qz52 0 1 Ns432p910 Ns432p144 Ns432p910 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p912 := nat_lit 4508639676119140709799321324680829504961065744149787679239474354869599542566396774464737636864612943943926161 

noncomputable def Ns432p913 := nat_lit 586614026309610612647796180311422375947666371958996720987134634332658881924406404870541342845348577681 

noncomputable def Ns432p914 := nat_lit 27334928579543899418678004678579620620570828312226289402743578300054393152420786171619459996567311634882331025 

noncomputable def Ns432p915 := BSN.cos_dyadic_bound_f 302479563 268435456 4 3 268435456 134217728 Ns432p912 Ns432p125 Ns432p913 Ns432p914 Ns432p128 Ns432p913 115301054 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 302479563) qz49 0 3 Ns432p912 Ns432p125 Ns432p913 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 302479563) qz50 0 3 Ns432p914 Ns432p128 Ns432p913 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p916 := nat_lit 43100225891595626321167142401296 

noncomputable def Ns432p917 := BSN.sin_dyadic_bound_f 81025158 268435456 2 1 268435456 134217728 Ns432p916 Ns432p143 Ns432p916 Ns432p916 Ns432p144 Ns432p916 79800400 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 81025158) qz51 0 1 Ns432p916 Ns432p143 Ns432p916 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 81025158) qz52 0 1 Ns432p916 Ns432p144 Ns432p916 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p918 := Ns432p876 79848 BSN.abs_quadSignPos (BSN.cos_quad_nat0 272 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 115301054 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 159 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 79800400 268435456) qz228 rfl rfl (Ns432p905 RS433to438.d9 RS433to438.d11 RS433to438.d13 RS433to438.d17 (Ns432p909 rfl rfl) (Ns432p911 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns432p904 rfl) RS433to438.d19 RS433to438.d21 RS433to438.d23 RS433to438.d25 RS433to438.d17 (Ns432p915 rfl rfl) (Ns432p917 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns432p919 := nat_lit 9905143830640247608034764117316982575672107526688563404792864336063201 

noncomputable def Ns432p920 := nat_lit 1289053477805003273225138737733154472470429660647721195900051729121 

noncomputable def Ns432p921 := nat_lit 29712853384965132817557842074475481418071381720744394771986792904731361 

noncomputable def Ns432p922 := BSN.cos_dyadic_bound_f 183562459 268435456 3 2 268435456 134217728 Ns432p919 Ns432p131 Ns432p920 Ns432p921 Ns432p134 Ns432p920 208081202 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 183562459) qz49 0 2 Ns432p919 Ns432p131 Ns432p920 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 183562459) qz50 0 2 Ns432p921 Ns432p134 Ns432p920 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p923 := nat_lit 42467117059906039791519482648596178609034146619455741694732992513391772796574367651501681940437805861163175936 

noncomputable def Ns432p924 := nat_lit 27809400826490708137142789999754542845988496564001888137108859052053992736281801722921439941839278247936 

noncomputable def Ns432p925 := nat_lit 212082685481564851402636251273272315073339341212224324136018296234788230391965975854190205775005632685983338496 

noncomputable def Ns432p926 := BSN.sin_dyadic_bound_f 417204806 268435456 4 3 268435456 134217728 Ns432p923 Ns432p272 Ns432p924 Ns432p925 Ns432p275 Ns432p924 268398528 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 417204806) qz51 0 3 Ns432p923 Ns432p272 Ns432p924 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 417204806) qz52 0 3 Ns432p925 Ns432p275 Ns432p924 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p927 := Ns432p874 107673 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 208081202 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268398528 268435456) qz228 rfl rfl (Ns432p918 rfl rfl) (Ns432p904 rfl) RS433to438.d27 RS433to438.d29 RS433to438.d31 RS433to438.d33 RS433to438.d17 (Ns432p922 rfl rfl) (Ns432p926 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p928 := nat_lit 32298640443600757200893797423091843953738611466890656614597012988935677443941011005351941683530775220171818801 

noncomputable def Ns432p929 := nat_lit 12251420138222566557149199629696729868883825824095005710334302249976738023609339888721475296472262494001 

noncomputable def Ns432p930 := nat_lit 161346793801676042852573579762555014159407483748589200645151228902256436023164745593888580179842473380902586161 

noncomputable def Ns432p931 := BSN.sin_dyadic_bound_f 389656749 268435456 4 3 268435456 134217728 Ns432p928 Ns432p272 Ns432p929 Ns432p930 Ns432p275 Ns432p929 266530284 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 389656749) qz51 0 3 Ns432p928 Ns432p272 Ns432p929 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 389656749) qz52 0 3 Ns432p930 Ns432p275 Ns432p929 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p932 := nat_lit 22751324409499771756082576669166913497129107639882396796436307335188903047521686029550711412509650805339643041 

noncomputable def Ns432p933 := nat_lit 4287638487009883205903886300923967628664366078952954268835685255762261883940417373571848550623386721441 

noncomputable def Ns432p934 := nat_lit 113683920397572215342779936137148660868902370048906357448622648665699264664542375743259159818813073877812567201 

noncomputable def Ns432p935 := BSN.sin_dyadic_bound_f 357013671 268435456 4 3 268435456 134217728 Ns432p932 Ns432p272 Ns432p933 Ns432p934 Ns432p275 Ns432p933 260689349 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 357013671) qz51 0 3 Ns432p932 Ns432p272 Ns432p933 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 357013671) qz52 0 3 Ns432p934 Ns432p275 Ns432p933 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p936 := Ns432p872 131985 BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266530284 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 139 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 260689349 268435456) qz228 rfl rfl (Ns432p927 rfl) (Ns432p904 rfl) RS433to438.d35 RS433to438.d37 RS433to438.d39 RS433to438.d41 RS433to438.d17 (Ns432p931 rfl rfl) (Ns432p935 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p937 := nat_lit 20224243400055745100050349953111319847044295831861241177001415843840000 

noncomputable def Ns432p938 := nat_lit 1658787370159987841101682525106513629606533051435493113881600000000 

noncomputable def Ns432p939 := nat_lit 52965570868213359091246275724536617624953792791839021808057423667200000 

noncomputable def Ns432p940 := BSN.sin_dyadic_bound_f 189440940 268435456 3 2 268435456 134217728 Ns432p937 Ns432p137 Ns432p938 Ns432p939 Ns432p140 Ns432p938 174102920 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 189440940) qz51 0 2 Ns432p937 Ns432p137 Ns432p938 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 189440940) qz52 0 2 Ns432p939 Ns432p140 Ns432p938 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p941 := nat_lit 34395734083117777333915188790710910666212833532399642481187175670328202918632357344947526567532196109518290625 

noncomputable def Ns432p942 := nat_lit 14791886640224154409403663742540152409465453440739130991913698028952951171025144588343049482090087890625 

noncomputable def Ns432p943 := nat_lit 171812660680115029881060068584260384667083944272083001098621629634365409874564963788628006597284624283239890625 

noncomputable def Ns432p944 := BSN.sin_dyadic_bound_f 395823855 268435456 4 3 268435456 134217728 Ns432p941 Ns432p272 Ns432p942 Ns432p943 Ns432p275 Ns432p942 267193335 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 395823855) qz51 0 3 Ns432p941 Ns432p272 Ns432p942 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 395823855) qz52 0 3 Ns432p943 Ns432p275 Ns432p942 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p945 := Ns432p870 153851 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 174102920 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267193335 268435456) qz228 rfl rfl (Ns432p936 rfl) (Ns432p904 rfl) RS433to438.d43 RS433to438.d45 RS433to438.d47 RS433to438.d49 RS433to438.d17 (Ns432p940 rfl rfl) (Ns432p944 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns432p946 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz225) qz225 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz225) qz225 11) 195849278 268435456 153851 268435456 195849278 268435456 153851 268435456 105145780494401536 97924639 67108864 153851 134217728 (Ns432p945 rfl) 

noncomputable def Ns432p947 := @Enclosure.Real.IsNear.mulLit_tf qz226 qz227 4995833 16777216 1 16777216 2085037089241 4398046511104 1193464622605471 14865397207531520000 10416497096654132753 73786976294838206464 

noncomputable abbrev qz239 := (@HPow.hPow Real Real Real qz298 qz419 qz300)

noncomputable def Ns432p948 := @Enclosure.Real.IsNear.mulLit_tf qz53 qz239 1 1 0 1 4995833 16777216 1 16777216 4995833 16777216 1 16777216 

noncomputable abbrev qz240 := qz419

noncomputable def Ns432p949 := @Enclosure.Real.IsNear.sqrt_image qz240 4267737759597 33554432000 799149 33554432000 189209863 189209899 16777216 (@Enclosure.Real.IsNear.of_eq qz240 (@HMul.hMul Real Real Real qz29 qz225 qz27) Bool.false 4267737759597 33554432000 799149 33554432000 (BSN.t_div_two_pi_mk qz225 799149 1000 qz228) (@Enclosure.Real.IsNear.mulLit_ff qz225 qz27 799149 1000 0 1 5340353 33554432 1 33554432 4267737759597 33554432000 799149 33554432000 (Enclosure.Real.IsNear.const Bool.false 799149 1000) RS433to438.d52 rfl)) 

noncomputable abbrev qz556 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 799149 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz520 := qz556

noncomputable abbrev qz430 := qz520

noncomputable abbrev qz241 := qz430

noncomputable def Ns432p950 := @Enclosure.Real.IsNear.sqrt_image qz241 189209881 16777216 9 8388608 56341944 56341951 16777216 (@Enclosure.Real.IsNear.recentre' qz241 Bool.false 378419762 33554432 36 33554432 189209881 16777216 9 8388608 (Ns432p949 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz242 := (Real.sqrt qz430)

noncomputable def Ns432p951 := @Enclosure.Real.IsNear.inv_image qz242 112683895 33554432 7 33554432 4995832 4995834 16777216 (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 112683895 33554432 7 33554432 112683895 33554432 7 33554432 (Ns432p950 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns432p952 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz242) Bool.false 9991666 33554432 2 33554432 4995833 16777216 1 16777216 (Ns432p951 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz431 := (Real.cos (@HMul.hMul Real Real Real qz453 qz451 qz515))

noncomputable abbrev qz243 := (@Inv.inv Real Real.instInv qz431)

noncomputable abbrev qz521 := (@HMul.hMul Real Real Real qz524 qz555 qz555)

noncomputable abbrev qz432 := (@HSub.hSub Real Real Real qz456 (@HSub.hSub Real Real Real qz456 qz521 qz515) qz466)

noncomputable abbrev qz244 := (Real.cos (@HMul.hMul Real Real Real qz296 qz293 qz432))

noncomputable def Ns432p953 := @Enclosure.Real.IsNear.of_eq qz227 (@HMul.hMul Real Real Real qz29 qz243 qz244) Bool.false 2085037089241 

noncomputable def Ns432p954 := @Enclosure.Real.IsNear.mulLit_tt qz243 qz244 1509091 262144 961 

noncomputable abbrev qz245 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz431))

noncomputable abbrev qz246 := qz431

noncomputable def Ns432p955 := @Enclosure.Real.IsNear.of_eq qz243 (@Neg.neg Real Real.instNeg qz245) Bool.true 1509091 262144 961 4194304 (BSN.inv_eq_neg_inv_neg qz246) 

noncomputable def Ns432p956 := @Enclosure.Real.IsNear.recentre' qz245 Bool.false 193163648 33554432 7688 33554432 1509091 262144 

noncomputable def Ns432p957 := @Enclosure.Real.IsNear.recentre' qz246 Bool.true 2914368 16777216 1568074432 226827960320000 45537 262144 24501163 3544186880000 

noncomputable abbrev qz433 := (@HMul.hMul Real Real Real qz453 qz451 qz515)

noncomputable abbrev qz247 := qz433

noncomputable def Ns432p958 := @Enclosure.Real.IsNear.cos_image qz247 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 58565633) qz48) Bool.false 58565633 33554432 227 33554432 Bool.true 2914368 16777216 1 

noncomputable def Ns432p959 := nat_lit 242874678701413125654365183 

noncomputable abbrev qz248 := qz420

noncomputable def Ns432p960 := @Enclosure.Real.IsNear.mulLit_ff qz26 qz248 884279719003555 140737488355328 1 500000000000000 4660505 16777216 9 8388608 4121190051814663095275 2361183241434822606848 Ns432p959 

noncomputable def Ns432p961 := @Enclosure.Real.IsNear.subLit_ff_p qz241 qz22 189209881 16777216 9 8388608 11 1 0 1 4660505 4660505 16777216 9 

noncomputable def Ns432p962 := @Ns432p961 8388608 (@Enclosure.Real.IsNear.recentre' qz241 Bool.false 378419762 33554432 36 33554432 189209881 16777216 9 8388608 (Ns432p949 rfl rfl rfl rfl rfl rfl) rfl) qz64 

noncomputable def Ns432p963 := @Enclosure.Real.IsNear.recentre' qz247 Bool.false 4121190051814663095275 2361183241434822606848 Ns432p959 Ns432p185 58565633 33554432 227 33554432 (@Ns432p960 Ns432p185 RS433to438.d51 (Ns432p962 rfl rfl) rfl) 

noncomputable def Ns432p964 := nat_lit 379394102026371707740076946464997402843307002531521399828594485187621346509715634875640818146979841 

noncomputable def Ns432p965 := nat_lit 1628223805384284615044043872990703160965065520126975650956385849240925951584362906604007567361 

noncomputable def Ns432p966 := nat_lit 2293219495955555220555769315987829614267446180261016003905050691210216412807097824597610427622600705 

noncomputable def Ns432p967 := BSN.cos_dyadic_bound_t 58565633 33554432 4 3 16777216 6760000 Ns432p964 Ns432p191 Ns432p965 Ns432p966 Ns432p194 Ns432p965 2914368 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 58565633) (BSN.cosEvenQ 33554432) 0 3 Ns432p964 Ns432p191 Ns432p965 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 58565633) (BSN.cosOddQ 33554432) 0 3 Ns432p966 Ns432p194 Ns432p965 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz249 := (@Neg.neg Real Real.instNeg qz431)

noncomputable def Ns432p968 := @Enclosure.Real.IsNear.inv_image qz249 45537 262144 24501163 3544186880000 96577980 96585668 16777216 (@Enclosure.Real.IsNear.neg qz246 Bool.true 45537 262144 24501163 3544186880000 (Ns432p957 (@Ns432p958 6760000 (Ns432p963 rfl) (Enclosure.sfrac_false_div 58565633 33554432) (Ns432p967 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns432p969 := Ns432p955 (@Enclosure.Real.IsNear.neg qz245 Bool.false 1509091 262144 961 4194304 (@Ns432p956 961 4194304 (Ns432p968 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns432p970 := @Enclosure.Real.IsNear.recentre' qz244 Bool.true 1381651 16777216 

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz296 qz293 qz432)

noncomputable def Ns432p971 := @Enclosure.Real.IsNear.cos_image qz250 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13868403)) qz411) Bool.true 13868403 8388608 

noncomputable def Ns432p972 := nat_lit 65491682165927740508304539405 

noncomputable def Ns432p973 := nat_lit 1584650656491694094687761882117487 

noncomputable def Ns432p974 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true Ns432p972 Ns432p484 Ns432p973 

noncomputable abbrev qz251 := qz432

noncomputable def Ns432p975 := @Enclosure.Real.IsNear.mulLit_ft qz26 qz251 884279719003555 140737488355328 1 500000000000000 74062178243471 

noncomputable abbrev qz434 := (@HSub.hSub Real Real Real qz456 qz521 qz515)

noncomputable abbrev qz252 := qz434

noncomputable def Ns432p976 := @Enclosure.Real.IsNear.subLit_tf qz252 qz68 56469992199055 281474976710656 58721049 35184372088832 1 16 

noncomputable abbrev qz435 := qz521

noncomputable abbrev qz253 := qz435

noncomputable def Ns432p977 := @Enclosure.Real.IsNear.subLit_ff_n qz253 qz248 21720306855025 281474976710656 20972313 35184372088832 4660505 16777216 9 8388608 

noncomputable def Ns432p978 := @Enclosure.Real.IsNear.mulLit_ff qz248 qz248 4660505 16777216 9 8388608 4660505 16777216 9 8388608 21720306855025 281474976710656 

noncomputable def Ns432p979 := nat_lit 18183556859215622846080493677880659962582456786719576749618792705511429201343408420644300721 

noncomputable def Ns432p980 := nat_lit 50619452002522624989792954323898966979123653562402621232518551707690153081101649029041 

noncomputable def Ns432p981 := nat_lit 109987750186161753947150128053336746498253667150012129064517587970676675578899712843696154545 

noncomputable def Ns432p982 := BSN.cos_dyadic_bound_t 13868403 8388608 4 3 16777216 6760000 Ns432p979 Ns432p843 Ns432p980 Ns432p981 Ns432p846 Ns432p980 1381651 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13868403) (BSN.cosEvenQ 8388608) 0 3 Ns432p979 Ns432p843 Ns432p980 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13868403) (BSN.cosOddQ 8388608) 0 3 Ns432p981 Ns432p846 Ns432p980 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns432p983 := @Ns432p970 2419834432 226827960320000 1381651 16777216 37809913 3544186880000 (@Ns432p971 353 33554432 Bool.true 1381651 16777216 1 6760000 (@Ns432p974 Ns432p487 13868403 8388608 353 33554432 (@Ns432p975 281474976710656 58721049 35184372088832 Ns432p972 Ns432p484 Ns432p973 Ns432p487 RS433to438.d51 (@Ns432p976 0 1 1184994851895536 74062178243471 281474976710656 58721049 35184372088832 (@Ns432p977 947409256641860730880 56469992199055 281474976710656 58721049 35184372088832 (@Ns432p978 20972313 35184372088832 (Ns432p962 rfl rfl) (Ns432p962 rfl rfl) rfl) (Ns432p962 rfl rfl) rfl rfl) qz70 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 13868403 8388608) (BSN.cos_neg_of_bound 13868403 8388608 Bool.true 1381651 16777216 1 6760000 (Ns432p982 rfl rfl)) rfl rfl) 

noncomputable def Ns432p984 := @Ns432p947 2984699282385607593907 Ns432p866 (Ns432p948 qz71 (@Enclosure.Real.IsNear.of_eq qz239 (@Inv.inv Real Real.instInv qz242) Bool.false 4995833 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz240 (BSN.t_div_two_pi_nonneg qz225 799149 1000 qz228)) Ns432p952) rfl) (@Ns432p953 4398046511104 1193464622605471 14865397207531520000 (BSN.correction_mk qz248 (BSN.cos_two_pi_p_ne_zero_mk qz225 799149 1000 11 qz228 rfl rfl (@BSN.floor_sqrt_eq_dec qz225 799149 1000 11 qz228 rfl rfl rfl))) (@Ns432p954 4194304 1381651 16777216 37809913 3544186880000 2085037089241 4398046511104 1193464622605471 14865397207531520000 Ns432p969 (Ns432p983 rfl) rfl)) 

noncomputable def Ns432p985 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz225) (hardyZApproximantRS₀ qz225) Bool.true 97252782129613040111 73786976294838206464 145925713393381350313907 Ns432p866 (@Eq.refl Real (hardyZApproximantRS₀ qz225)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz225) (@HSub.hSub Real Real Real qz72 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz225) qz225 11) (@HMul.hMul Real Real Real qz29 qz226 qz227)) Bool.true 97252782129613040111 73786976294838206464 145925713393381350313907 Ns432p866 (BSN.hardyZApproximantRS₀_eq qz225 11 (@BSN.floor_sqrt_eq_dec qz225 799149 1000 11 qz228 rfl rfl rfl)) (@Ns432p868 97252782129613040111 73786976294838206464 145925713393381350313907 Ns432p866 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz225) qz225 11) (@HAdd.hAdd Real Real Real qz47 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz225) qz225 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz225) qz225 11)) Bool.true 97924639 67108864 153851 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz225) qz225 11) (Ns432p946 (Ns432p945 rfl) rfl rfl)) (Ns432p984 rfl) rfl rfl)) 

theorem RS433to438.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz225) Bool.true 97252782129613040111 73786976294838206464 145925713393381350313907 Ns432p866 := Ns432p985 

noncomputable def RS433to438.d62 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz436 := (RS433to438.d3 qz452 qz467 (@Enclosure.dec_le_dec qz452 qz467 791361 1000 792660 1000 (@Eq.refl Real qz452) qz470 rfl rfl rfl))

noncomputable abbrev qz254 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz436)

noncomputable def Ns432p986 := @Enclosure.Real.IsNear.of_eq qz254 (hardyZApproximantRS₀ qz28) Bool.true 30104066352671455159079 18889465931478580854784 462454108857420738703427 Ns432p77 

noncomputable abbrev qz437 := (@Enclosure.dec_le_dec qz452 qz467 791361 1000 792660 1000 (@Eq.refl Real qz452) qz470 rfl rfl rfl)

noncomputable abbrev qz255 := qz437

noncomputable def Ns432p987 := @Enclosure.Real.IsNear.neg_val qz254 30104066352671455159079 18889465931478580854784 462454108857420738703427 Ns432p77 (Ns432p986 (RS433to438.d4 qz28 qz73 qz255) RS433to438.d53) rfl 

noncomputable abbrev qz256 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz436)

noncomputable def Ns432p988 := @Enclosure.Real.IsNear.of_eq qz256 (hardyZApproximantRS₀ qz73) Bool.false 1836885842566689846967 9444732965739290427392 18001272371523572458177 Ns432p215 

noncomputable def Ns432p989 := @Enclosure.Real.IsNear.pos_val qz256 1836885842566689846967 9444732965739290427392 18001272371523572458177 Ns432p215 (Ns432p988 (RS433to438.d54 qz28 qz73 qz255) RS433to438.d55) rfl 

noncomputable def Ns432p990 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz254 qz28 qz28 791361 1000 791361 1000 

noncomputable def Ns432p991 := @Enclosure.norm_gt_of_isNear qz254 (hardyZErrorBoundRS₀ qz28) Bool.true Bool.false 30104066352671455159079 18889465931478580854784 462454108857420738703427 

noncomputable def Ns432p992 := @Ns432p991 Ns432p77 265163133 5368709120 1213 5368709120 (Ns432p986 (RS433to438.d4 qz28 qz73 qz255) RS433to438.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz28) (hardyZErrorBoundRS₀ qz28) Bool.false 265163133 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz28)) RS433to438.d56) rfl rfl rfl rfl 

noncomputable def Ns432p993 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz256 qz28 qz73 791361 1000 792660 1000 

noncomputable def Ns432p994 := @Enclosure.norm_gt_of_isNear qz256 (hardyZErrorBoundRS₀ qz28) Bool.false Bool.false 1836885842566689846967 9444732965739290427392 18001272371523572458177 

noncomputable def Ns432p995 := @Ns432p994 Ns432p215 265163133 5368709120 1213 5368709120 (Ns432p988 (RS433to438.d54 qz28 qz73 qz255) RS433to438.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz28) (hardyZErrorBoundRS₀ qz28) Bool.false 265163133 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz28)) RS433to438.d56) rfl rfl rfl rfl 

noncomputable abbrev qz257 := qz436

noncomputable def Ns432p996 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz257 (@BSN.thirtyTwoPi_le_dec qz28 791361 1000 qz32 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz254 qz256 (Ns432p987 rfl rfl) (Ns432p989 rfl rfl)) (Ns432p990 qz32 qz32 rfl rfl rfl rfl (Ns432p992 rfl)) (Ns432p993 qz32 qz76 rfl rfl rfl rfl (Ns432p995 rfl)) 

noncomputable abbrev qz438 := (RS433to438.d3 qz467 qz477 (@Enclosure.dec_le_dec qz467 qz477 792660 1000 793959 1000 qz470 qz480 rfl rfl rfl))

noncomputable abbrev qz258 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz438)

noncomputable def Ns432p997 := @Enclosure.Real.IsNear.of_eq qz258 (hardyZApproximantRS₀ qz73) Bool.false 1836885842566689846967 9444732965739290427392 18001272371523572458177 Ns432p215 

noncomputable abbrev qz439 := (@Enclosure.dec_le_dec qz467 qz477 792660 1000 793959 1000 qz470 qz480 rfl rfl rfl)

noncomputable abbrev qz259 := qz439

noncomputable def Ns432p998 := @Enclosure.Real.IsNear.pos_val qz258 1836885842566689846967 9444732965739290427392 18001272371523572458177 Ns432p215 (Ns432p997 (RS433to438.d4 qz73 qz111 qz259) RS433to438.d55) rfl 

noncomputable abbrev qz260 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz438)

noncomputable def Ns432p999 := @Enclosure.Real.IsNear.of_eq qz260 (hardyZApproximantRS₀ qz111) Bool.true 32998822934472896274027 18889465931478580854784 96721606938963166969403 Ns432p379 

noncomputable def Ns432p1000 := @Enclosure.Real.IsNear.neg_val qz260 32998822934472896274027 18889465931478580854784 96721606938963166969403 Ns432p379 (Ns432p999 (RS433to438.d54 qz73 qz111 qz259) RS433to438.d57) rfl 

noncomputable def Ns432p1001 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz258 qz28 qz73 791361 1000 792660 1000 

noncomputable def Ns432p1002 := @Enclosure.norm_gt_of_isNear qz258 (hardyZErrorBoundRS₀ qz28) Bool.false Bool.false 1836885842566689846967 9444732965739290427392 18001272371523572458177 

noncomputable def Ns432p1003 := @Ns432p1002 Ns432p215 265163133 5368709120 1213 5368709120 (Ns432p997 (RS433to438.d4 qz73 qz111 qz259) RS433to438.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz28) (hardyZErrorBoundRS₀ qz28) Bool.false 265163133 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz28)) RS433to438.d56) rfl rfl rfl rfl 

noncomputable def Ns432p1004 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz260 qz28 qz111 791361 1000 793959 1000 

noncomputable def Ns432p1005 := @Enclosure.norm_gt_of_isNear qz260 (hardyZErrorBoundRS₀ qz28) Bool.true Bool.false 32998822934472896274027 18889465931478580854784 96721606938963166969403 

noncomputable def Ns432p1006 := @Ns432p1005 Ns432p379 265163133 5368709120 1213 5368709120 (Ns432p999 (RS433to438.d54 qz73 qz111 qz259) RS433to438.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz28) (hardyZErrorBoundRS₀ qz28) Bool.false 265163133 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz28)) RS433to438.d56) rfl rfl rfl rfl 

noncomputable abbrev qz261 := qz438

noncomputable def Ns432p1007 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz261 (@BSN.thirtyTwoPi_le_dec qz73 792660 1000 qz76 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz258 qz260 (Ns432p998 rfl rfl) (Ns432p1000 rfl rfl)) (Ns432p1001 qz32 qz76 rfl rfl rfl rfl (Ns432p1003 rfl)) (Ns432p1004 qz32 qz114 rfl rfl rfl rfl (Ns432p1006 rfl)) 

noncomputable abbrev qz440 := (RS433to438.d3 qz477 qz486 (@Enclosure.dec_le_dec qz477 qz486 793959 1000 795257 1000 qz480 qz489 rfl rfl rfl))

noncomputable abbrev qz262 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz440)

noncomputable def Ns432p1008 := @Enclosure.Real.IsNear.of_eq qz262 (hardyZApproximantRS₀ qz111) Bool.true 32998822934472896274027 18889465931478580854784 96721606938963166969403 Ns432p379 

noncomputable abbrev qz441 := (@Enclosure.dec_le_dec qz477 qz486 793959 1000 795257 1000 qz480 qz489 rfl rfl rfl)

noncomputable abbrev qz263 := qz441

noncomputable def Ns432p1009 := @Enclosure.Real.IsNear.neg_val qz262 32998822934472896274027 18889465931478580854784 96721606938963166969403 Ns432p379 (Ns432p1008 (RS433to438.d4 qz111 qz138 qz263) RS433to438.d57) rfl 

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz440)

noncomputable def Ns432p1010 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantRS₀ qz138) Bool.false 26818438294283230266085 18889465931478580854784 Ns432p499 Ns432p77 

noncomputable def Ns432p1011 := @Enclosure.Real.IsNear.pos_val qz264 26818438294283230266085 18889465931478580854784 Ns432p499 Ns432p77 (Ns432p1010 (RS433to438.d54 qz111 qz138 qz263) RS433to438.d58) rfl 

noncomputable def Ns432p1012 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz262 qz28 qz111 791361 1000 793959 1000 

noncomputable def Ns432p1013 := @Enclosure.norm_gt_of_isNear qz262 (hardyZErrorBoundRS₀ qz28) Bool.true Bool.false 32998822934472896274027 18889465931478580854784 96721606938963166969403 

noncomputable def Ns432p1014 := @Ns432p1013 Ns432p379 265163133 5368709120 1213 5368709120 (Ns432p1008 (RS433to438.d4 qz111 qz138 qz263) RS433to438.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz28) (hardyZErrorBoundRS₀ qz28) Bool.false 265163133 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz28)) RS433to438.d56) rfl rfl rfl rfl 

noncomputable def Ns432p1015 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz264 qz28 qz138 791361 1000 795257 1000 

noncomputable def Ns432p1016 := @Enclosure.norm_gt_of_isNear qz264 (hardyZErrorBoundRS₀ qz28) Bool.false Bool.false 26818438294283230266085 18889465931478580854784 Ns432p499 

noncomputable def Ns432p1017 := @Ns432p1016 Ns432p77 265163133 5368709120 1213 5368709120 (Ns432p1010 (RS433to438.d54 qz111 qz138 qz263) RS433to438.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz28) (hardyZErrorBoundRS₀ qz28) Bool.false 265163133 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz28)) RS433to438.d56) rfl rfl rfl rfl 

noncomputable abbrev qz265 := qz440

noncomputable def Ns432p1018 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz265 (@BSN.thirtyTwoPi_le_dec qz111 793959 1000 qz114 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz262 qz264 (Ns432p1009 rfl rfl) (Ns432p1011 rfl rfl)) (Ns432p1012 qz32 qz114 rfl rfl rfl rfl (Ns432p1014 rfl)) (Ns432p1015 qz32 qz141 rfl rfl rfl rfl (Ns432p1017 rfl)) 

noncomputable abbrev qz442 := (RS433to438.d3 qz486 qz495 (@Enclosure.dec_le_dec qz486 qz495 795257 1000 796555 1000 qz489 qz498 rfl rfl rfl))

noncomputable abbrev qz266 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz442)

noncomputable def Ns432p1019 := @Enclosure.Real.IsNear.of_eq qz266 (hardyZApproximantRS₀ qz138) Bool.false 26818438294283230266085 18889465931478580854784 Ns432p499 Ns432p77 

noncomputable abbrev qz443 := (@Enclosure.dec_le_dec qz486 qz495 795257 1000 796555 1000 qz489 qz498 rfl rfl rfl)

noncomputable abbrev qz267 := qz443

noncomputable def Ns432p1020 := @Enclosure.Real.IsNear.pos_val qz266 26818438294283230266085 18889465931478580854784 Ns432p499 Ns432p77 (Ns432p1019 (RS433to438.d4 qz138 qz167 qz267) RS433to438.d58) rfl 

noncomputable abbrev qz268 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz442)

noncomputable def Ns432p1021 := @Enclosure.Real.IsNear.of_eq qz268 (hardyZApproximantRS₀ qz167) Bool.true 35210692164251634179913 9444732965739290427392 Ns432p619 Ns432p620 

noncomputable def Ns432p1022 := @Enclosure.Real.IsNear.neg_val qz268 35210692164251634179913 9444732965739290427392 Ns432p619 Ns432p620 (Ns432p1021 (RS433to438.d54 qz138 qz167 qz267) RS433to438.d59) rfl 

noncomputable def Ns432p1023 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz266 qz28 qz138 791361 1000 795257 1000 

noncomputable def Ns432p1024 := @Enclosure.norm_gt_of_isNear qz266 (hardyZErrorBoundRS₀ qz28) Bool.false Bool.false 26818438294283230266085 18889465931478580854784 Ns432p499 

noncomputable def Ns432p1025 := @Ns432p1024 Ns432p77 265163133 5368709120 1213 5368709120 (Ns432p1019 (RS433to438.d4 qz138 qz167 qz267) RS433to438.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz28) (hardyZErrorBoundRS₀ qz28) Bool.false 265163133 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz28)) RS433to438.d56) rfl rfl rfl rfl 

noncomputable def Ns432p1026 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz268 qz28 qz167 791361 1000 796555 1000 

noncomputable def Ns432p1027 := @Enclosure.norm_gt_of_isNear qz268 (hardyZErrorBoundRS₀ qz28) Bool.true Bool.false 35210692164251634179913 9444732965739290427392 Ns432p619 

noncomputable def Ns432p1028 := @Ns432p1027 Ns432p620 265163133 5368709120 1213 5368709120 (Ns432p1021 (RS433to438.d54 qz138 qz167 qz267) RS433to438.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz28) (hardyZErrorBoundRS₀ qz28) Bool.false 265163133 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz28)) RS433to438.d56) rfl rfl rfl rfl 

noncomputable abbrev qz269 := qz442

noncomputable def Ns432p1029 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz269 (@BSN.thirtyTwoPi_le_dec qz138 795257 1000 qz141 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz266 qz268 (Ns432p1020 rfl rfl) (Ns432p1022 rfl rfl)) (Ns432p1023 qz32 qz141 rfl rfl rfl rfl (Ns432p1025 rfl)) (Ns432p1026 qz32 qz170 rfl rfl rfl rfl (Ns432p1028 rfl)) 

noncomputable abbrev qz444 := (RS433to438.d3 qz495 qz504 (@Enclosure.dec_le_dec qz495 qz504 796555 1000 797852 1000 qz498 qz507 rfl rfl rfl))

noncomputable abbrev qz270 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz444)

noncomputable def Ns432p1030 := @Enclosure.Real.IsNear.of_eq qz270 (hardyZApproximantRS₀ qz167) Bool.true 35210692164251634179913 9444732965739290427392 Ns432p619 Ns432p620 

noncomputable abbrev qz445 := (@Enclosure.dec_le_dec qz495 qz504 796555 1000 797852 1000 qz498 qz507 rfl rfl rfl)

noncomputable abbrev qz271 := qz445

noncomputable def Ns432p1031 := @Enclosure.Real.IsNear.neg_val qz270 35210692164251634179913 9444732965739290427392 Ns432p619 Ns432p620 (Ns432p1030 (RS433to438.d4 qz167 qz196 qz271) RS433to438.d59) rfl 

noncomputable abbrev qz272 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz444)

noncomputable def Ns432p1032 := @Enclosure.Real.IsNear.of_eq qz272 (hardyZApproximantRS₀ qz196) Bool.false 3339517040756187745993 1180591620717411303424 22633022187446125272317 Ns432p742 

noncomputable def Ns432p1033 := @Enclosure.Real.IsNear.pos_val qz272 3339517040756187745993 1180591620717411303424 22633022187446125272317 Ns432p742 (Ns432p1032 (RS433to438.d54 qz167 qz196 qz271) RS433to438.d60) rfl 

noncomputable def Ns432p1034 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz270 qz28 qz167 791361 1000 796555 1000 

noncomputable def Ns432p1035 := @Enclosure.norm_gt_of_isNear qz270 (hardyZErrorBoundRS₀ qz28) Bool.true Bool.false 35210692164251634179913 9444732965739290427392 Ns432p619 

noncomputable def Ns432p1036 := @Ns432p1035 Ns432p620 265163133 5368709120 1213 5368709120 (Ns432p1030 (RS433to438.d4 qz167 qz196 qz271) RS433to438.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz28) (hardyZErrorBoundRS₀ qz28) Bool.false 265163133 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz28)) RS433to438.d56) rfl rfl rfl rfl 

noncomputable def Ns432p1037 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz272 qz28 qz196 791361 1000 797852 1000 

noncomputable def Ns432p1038 := @Enclosure.norm_gt_of_isNear qz272 (hardyZErrorBoundRS₀ qz28) Bool.false Bool.false 3339517040756187745993 1180591620717411303424 22633022187446125272317 

noncomputable def Ns432p1039 := @Ns432p1038 Ns432p742 265163133 5368709120 1213 5368709120 (Ns432p1032 (RS433to438.d54 qz167 qz196 qz271) RS433to438.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz28) (hardyZErrorBoundRS₀ qz28) Bool.false 265163133 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz28)) RS433to438.d56) rfl rfl rfl rfl 

noncomputable abbrev qz273 := qz444

noncomputable def Ns432p1040 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz273 (@BSN.thirtyTwoPi_le_dec qz167 796555 1000 qz170 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz270 qz272 (Ns432p1031 rfl rfl) (Ns432p1033 rfl rfl)) (Ns432p1034 qz32 qz170 rfl rfl rfl rfl (Ns432p1036 rfl)) (Ns432p1037 qz32 qz199 rfl rfl rfl rfl (Ns432p1039 rfl)) 

noncomputable abbrev qz522 := (@Enclosure.dec_le_dec qz549 qz553 797852 1000 799149 1000 (@Eq.refl Real qz549) (@Eq.refl Real qz553) rfl rfl rfl)

noncomputable abbrev qz446 := (RS433to438.d3 qz504 qz513 qz522)

noncomputable abbrev qz274 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz446)

noncomputable def Ns432p1041 := @Enclosure.Real.IsNear.of_eq qz274 (hardyZApproximantRS₀ qz196) Bool.false 3339517040756187745993 1180591620717411303424 22633022187446125272317 Ns432p742 

noncomputable abbrev qz447 := qz522

noncomputable abbrev qz275 := qz447

noncomputable def Ns432p1042 := @Enclosure.Real.IsNear.pos_val qz274 3339517040756187745993 1180591620717411303424 22633022187446125272317 Ns432p742 (Ns432p1041 (RS433to438.d4 qz196 qz225 qz275) RS433to438.d60) rfl 

noncomputable abbrev qz276 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz446)

noncomputable def Ns432p1043 := @Enclosure.Real.IsNear.of_eq qz276 (hardyZApproximantRS₀ qz225) Bool.true 97252782129613040111 73786976294838206464 145925713393381350313907 Ns432p866 

noncomputable def Ns432p1044 := @Enclosure.Real.IsNear.neg_val qz276 97252782129613040111 73786976294838206464 145925713393381350313907 Ns432p866 (Ns432p1043 (RS433to438.d54 qz196 qz225 qz275) RS433to438.d61) rfl 

noncomputable def Ns432p1045 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz274 qz28 qz196 791361 1000 797852 1000 

noncomputable def Ns432p1046 := @Enclosure.norm_gt_of_isNear qz274 (hardyZErrorBoundRS₀ qz28) Bool.false Bool.false 3339517040756187745993 1180591620717411303424 22633022187446125272317 

noncomputable def Ns432p1047 := @Ns432p1046 Ns432p742 265163133 5368709120 1213 5368709120 (Ns432p1041 (RS433to438.d4 qz196 qz225 qz275) RS433to438.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz28) (hardyZErrorBoundRS₀ qz28) Bool.false 265163133 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz28)) RS433to438.d56) rfl rfl rfl rfl 

noncomputable def Ns432p1048 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz276 qz28 qz225 791361 1000 799149 1000 

noncomputable def Ns432p1049 := @Enclosure.norm_gt_of_isNear qz276 (hardyZErrorBoundRS₀ qz28) Bool.true Bool.false 97252782129613040111 73786976294838206464 145925713393381350313907 

noncomputable def Ns432p1050 := @Ns432p1049 Ns432p866 265163133 5368709120 1213 5368709120 (Ns432p1043 (RS433to438.d54 qz196 qz225 qz275) RS433to438.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz28) (hardyZErrorBoundRS₀ qz28) Bool.false 265163133 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz28)) RS433to438.d56) rfl rfl rfl rfl 

noncomputable abbrev qz277 := qz446

noncomputable def Ns432p1051 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz277 (@BSN.thirtyTwoPi_le_dec qz196 797852 1000 qz199 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz274 qz276 (Ns432p1042 rfl rfl) (Ns432p1044 rfl rfl)) (Ns432p1045 qz32 qz199 rfl rfl rfl rfl (Ns432p1047 rfl)) (Ns432p1048 qz32 qz228 rfl rfl rfl rfl (Ns432p1050 rfl)) 

noncomputable def Ns432p1052 := @List.cons RS433to438.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz273 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz273) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz273) Ns432p1040)) (@List.cons RS433to438.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz277 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz277) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz277) Ns432p1051)) (@List.nil RS433to438.d0)) 

noncomputable def Ns432p1053 := @List.cons RS433to438.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz265 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz265) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz265) Ns432p1018)) (@List.cons RS433to438.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz269 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz269) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz269) Ns432p1029)) Ns432p1052) 

noncomputable def Ns432p1054 := @List.cons RS433to438.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz257 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz257) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz257) Ns432p996)) (@List.cons RS433to438.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz261 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz261) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz261) Ns432p1007)) Ns432p1053) 

noncomputable abbrev qz278 := (RS433to438.d2 qz346 qz363 qz441)

noncomputable abbrev qz279 := (RS433to438.d2 qz363 qz381 qz443)

noncomputable abbrev qz448 := (RS433to438.d2 qz504 qz513 qz522)

noncomputable abbrev qz280 := (@List.cons RS433to438.d1 (RS433to438.d2 qz381 qz399 qz445) (@List.cons RS433to438.d1 qz448 (@List.nil RS433to438.d1)))

noncomputable abbrev qz281 := (RS433to438.d2 qz381 qz399 qz445)

noncomputable abbrev qz282 := (@List.cons RS433to438.d1 qz448 (@List.nil RS433to438.d1))

noncomputable abbrev qz283 := qz448

noncomputable def Ns432p1055 := @List.IsChain.cons_cons RS433to438.d1 RS433to438.d62 (RS433to438.d2 qz73 qz111 qz259) qz278 (@List.cons RS433to438.d1 qz279 qz280) (@Enclosure.dec_le_dec qz111 qz111 793959 1000 793959 1000 qz114 qz114 rfl rfl rfl) (@List.IsChain.cons_cons RS433to438.d1 RS433to438.d62 qz278 qz279 qz280 (@Enclosure.dec_le_dec qz138 qz138 795257 1000 795257 1000 qz141 qz141 rfl rfl rfl) (@List.IsChain.cons_cons RS433to438.d1 RS433to438.d62 qz279 qz281 qz282 (@Enclosure.dec_le_dec qz167 qz167 796555 1000 796555 1000 qz170 qz170 rfl rfl rfl) (@List.IsChain.cons_cons RS433to438.d1 RS433to438.d62 qz281 qz283 (@List.nil RS433to438.d1) (@Enclosure.dec_le_dec qz196 qz196 797852 1000 797852 1000 qz199 qz199 rfl rfl rfl) (@List.IsChain.singleton RS433to438.d1 RS433to438.d62 qz283)))) 

noncomputable def Ns432p1056 := @List.IsChain.cons_cons RS433to438.d1 RS433to438.d62 (RS433to438.d2 qz28 qz73 qz255) (RS433to438.d2 qz73 qz111 qz259) (@List.cons RS433to438.d1 qz278 (@List.cons RS433to438.d1 qz279 qz280)) (@Enclosure.dec_le_dec qz73 qz73 792660 1000 792660 1000 qz76 qz76 rfl rfl rfl) Ns432p1055 

noncomputable abbrev qz284 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz285 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns432p1054 Ns432p1056)

noncomputable abbrev qz286 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns432p1054 Ns432p1056))

theorem RS433to438.d63 : Zeta.Certificates.BatchSpec 6 791361 1000 799149 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz284 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 6) (And (@Eq (Option Real) (@Option.map qz284 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz284 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz28)) (@Eq (Option Real) (@Option.map qz284 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz284 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz225)))) qz285 (@And.intro (@Eq Nat (@List.length qz284 qz286) 6) (And (@Eq (Option Real) (@Option.map qz284 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz284 qz286)) (@Option.some Real qz28)) (@Eq (Option Real) (@Option.map qz284 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz284 qz286)) (@Option.some Real qz225))) (@Eq.refl Nat 6) (@And.intro (@Eq (Option Real) (@Option.map qz284 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz284 qz286)) (@Option.some Real qz28)) (@Eq (Option Real) (@Option.map qz284 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz284 qz286)) (@Option.some Real qz225)) (@Eq.refl (Option Real) (@Option.some Real qz28)) (@Eq.refl (Option Real) (@Option.some Real qz225))))

theorem solution : Zeta.Certificates.BatchSpec 6 791361 1000 799149 1000 := RS433to438.d63
#print axioms solution
#check solution
