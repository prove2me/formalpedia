-- Prove2me | solution 1 for RHHeight1000.rs_main_0589_0600
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:26:46.2022+00:00
-- url     : https://prove2.me/submissions/3831d53b-250d-4bd8-bfb3-7ba26faa0cb4

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

noncomputable def RS589to600.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS589to600.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS589to600.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS589to600.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS589to600.d2 a b h 

theorem RS589to600.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS589to600.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS589to600.d3 a b h)) 

noncomputable def Ns588p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns588p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns588p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns588p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns588p0 Ns588p1 Ns588p2 Ns588p1 614572177 536870912 1 174240000 614572177 536870912 1 174240000 307286088 268435456 3 268435456 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns588p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns588p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns588p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns588p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns588p8 := nat_lit 6573389678388862351155759458724141871788046104702795740939545775355827438482086890337971184306503456724674701876007739166027855002689342487126242201873902293161938510715598861337724155978462934346539722102807352693564004597780440630880721700532830491857281958381906437104026277614553345439647264822859384496062743250358046048880947907642984145065307980413206151384068885350206914057384338280179177725692904928360597982006748935836093248417685721122261418062303135764477585928239149568275027355236134745000697766005167655784166499502223346815249842007858448160935771607172549259242715110048115445292136446613946552506617916138661398090061483392335970316672263498462800198746102072055363920390651513279180731193678641632192805423820381724597815072905552156968003637925334143020171520625 

noncomputable def Ns588p9 := nat_lit 702614123509571190207434367497643053726389003684617183996726348470791223755418688598787599501240412886827946200799073391711533512528899996899108221816773619593298708861540359234024488137706935294538610329535191474811214152768697527793266408685885408431698677504366547635987768499962038530066773279961750661013789994039311989768445302208965109624014234440840481147386361324656837522786906307734587964680180646868573806366973424595907336814393861048013934514934272026683624090151873353554279683010347128413433843775162422864773798490322287367830744467164676975854073090397461536167654230134598982106570951920409048997311342333559851528447946435833392322432321465286801524775001800171249769824525762984779161997185015423416919065587459911326773695449510414365759468097615398764501522575 

noncomputable def Ns588p10 := nat_lit 541392566138474909591412279139378993255101875047003589935782329109463644892392322173295519240510467068363239080443023466297029982601757003829684821059136286585994161974307047499333049696728682047261006046816072264069316416942594393775486731411634963656291648112663555457379375292741727868294229136381639619442405391741167595634732196900940186574903289828257139713673376723681752760045249773972946001592268830432998579610986951410273979009689762628244990479410235165324966379611071762421902787196495466840333515349387051622842182127210560393625584510287605139387730811840242457253978115925211125629993337408355023684205061830608267784338105681114876710224147942516826039256450164994945245879666660679160980454641866547806615379410050641833332584350523565507268843323231339375 

noncomputable def Ns588p11 := BSN.log_dyadic_bound Ns588p6 Ns588p7 16 15 Ns588p8 536870912 174240000 Ns588p9 Ns588p10 614572177 Ns588p4 Ns588p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns588p6) (BSN.artanhQ Ns588p7) 0 15 Ns588p9 Ns588p8 Ns588p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns588p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns588p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns588p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns588p15 := nat_lit 6573389678388957581038003304946500209472262679236338533996718496177406624059139082449994147026037314666926693076053053862592074936423388863596813530408382584499373597031431853921413941298322255656576695489433951602693567143885654771592106690789036275646003378131729522606930818530515414843848039000889531334935427389830473690579523667466182538201372727149023132371319359578146651783732835416323469915494090659780509855937937675396353734377829186029766969614606089327824892671842834136516654569045504808111725705550748907924941183733134599012581542910476929082687043869700761244349471219210833189555347464155979117619898077496880661665775336657207488512148128426326823595335945176245554694022845325705851563290369414226074229552025260849280553835909109839168582914725334143020171520625 

noncomputable def Ns588p16 := nat_lit 702614123509582134195699383225799303120857312948289364169564431944606347230839067212220070086773571232938822231607515388838247088164426860334641427891924556959013106220289292017417932077264689683982462259236603120411894481357554273197237433243865910367073588753830073256225145709268648257922640132615276470163987114280905050307903018021985933333474523803420109333064989110261463867307642914581311357336787925252212965840242792007601256472655504246146516404729632839909377990937267835233434162343951883521915890115762575574377037535717851480622294463860980162526686236248764915916362237196611189536095144270945605478817014333998082847306947436470576941659846222535334992451365706225994338058508887942119777908276510373758951874822816373072605980596581754554466975502415398764501522575 

noncomputable def Ns588p17 := nat_lit 541392566138490077533790984620311058177654278555980714203107761719673916425133183846751239616284470803704371181920004286935467360846628369375164068764590875438310007353955324186636582299553928814156491749519256774653872128089233575343481607925575468185460509172779152955629338248076232826253005811067688706928164570779608774451502836676056177667078421728722179008027603013170304530594440809888606240685402729798990208830923560422594844623819537735750113690675240496626214395332044296593456069970973486809806367897564108502902289348063943342100923856630472249952347312756547637419241376870243223562839253667975765230153074010838184467350558565952691487980795548332122966513692688198426849374346091985539852378055886379210372820263137502377721028428076000707268843323231339375 

noncomputable def Ns588p18 := BSN.log_dyadic_bound Ns588p13 Ns588p14 16 15 Ns588p15 536870912 174240000 Ns588p16 Ns588p17 614572177 Ns588p12 Ns588p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns588p13) (BSN.artanhQ Ns588p14) 0 15 Ns588p16 Ns588p15 Ns588p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns588p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 307286088 268435456 3 268435456 38410761 33554432 3 268435456 (Ns588p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns588p0 Ns588p1 614572177 536870912 1 174240000 Bool.false (BSN.logfrac_isNear Ns588p4 Ns588p5 1 Ns588p0 Ns588p1 614572177 536870912 174240000 rfl rfl rfl (Ns588p11 rfl))) (BSN.isNear_log_sfrac Ns588p2 Ns588p1 614572177 536870912 1 174240000 Bool.false (BSN.logfrac_isNear Ns588p12 Ns588p5 1 Ns588p2 Ns588p1 614572177 536870912 174240000 rfl rfl rfl (Ns588p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS589to600.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 3 268435456 := Ns588p19 

noncomputable def Ns588p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 33554432 10890000 385100712855 135135 23258159 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz583 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz316 := qz583

noncomputable abbrev qz0 := qz316

theorem RS589to600.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 23258159 33554432 1 10890000 := BSN.isNear_log_sfrac 2 1 23258159 33554432 1 10890000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 23258159 33554432 10890000 rfl rfl rfl (Ns588p20 rfl)) 

theorem RS589to600.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 372130544 536870912 50 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 23258159 33554432 1 10890000 372130544 536870912 50 536870912 RS589to600.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz584 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz584

noncomputable def Ns588p21 := @Enclosure.Real.IsNear.inv_image qz317 94906265 67108864 1 67108864 23726566 23726567 33554432 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 94906265 67108864 1 67108864 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 94906265 67108864 1 67108864 94906265 67108864 1 67108864 (BSN.sqrt_enclosure 2 1 47453132 47453133 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS589to600.d8 : Enclosure.Real.IsNear qz320 Bool.false 47453133 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 47453133 67108864 1 67108864 47453133 67108864 1 67108864 (Ns588p21 rfl rfl) rfl 

theorem RS589to600.d9 : Enclosure.Real.IsNear qz320 Bool.false 379625064 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 47453133 67108864 1 67108864 379625064 536870912 8 536870912 RS589to600.d8 rfl 

noncomputable def Ns588p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 33554432 10890000 13079757671720842725 316234143225 36863311 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS589to600.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 36863311 33554432 1 10890000 := BSN.isNear_log_sfrac 3 1 36863311 33554432 1 10890000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 36863311 33554432 10890000 rfl rfl rfl (Ns588p22 rfl)) 

theorem RS589to600.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 589812976 536870912 50 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 36863311 33554432 1 10890000 589812976 536870912 50 536870912 RS589to600.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns588p23 := @Enclosure.Real.IsNear.inv_image qz321 116235963 67108864 1 67108864 19372660 19372661 33554432 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 116235963 67108864 1 67108864 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 116235963 67108864 1 67108864 116235963 67108864 1 67108864 (BSN.sqrt_enclosure 3 1 58117981 58117982 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS589to600.d12 : Enclosure.Real.IsNear qz323 Bool.false 38745321 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 38745321 67108864 1 67108864 38745321 67108864 1 67108864 (Ns588p23 rfl rfl) rfl 

theorem RS589to600.d13 : Enclosure.Real.IsNear qz323 Bool.false 309962568 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 38745321 67108864 1 67108864 309962568 536870912 8 536870912 RS589to600.d12 rfl 

noncomputable def Ns588p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns588p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns588p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns588p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns588p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns588p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns588p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns588p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns588p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns588p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns588p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns588p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns588p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns588p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns588p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns588p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns588p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns588p25 Ns588p26 Ns588p27 Ns588p28 200200021673987500790625 Ns588p29 Ns588p30 Ns588p31 Ns588p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns588p32 Ns588p33 151412625 Ns588p34 Ns588p35 1322214852783825 Ns588p27 Ns588p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns588p32 Ns588p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns588p34 Ns588p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns588p36 Ns588p37 1267389585 Ns588p38 Ns588p39 1927077560082675 Ns588p29 Ns588p30 Ns588p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns588p36 Ns588p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns588p38 Ns588p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS589to600.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns588p24 Ns588p25 1 Ns588p26 := Ns588p40 rfl rfl rfl 

noncomputable def Ns588p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns588p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns588p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns588p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns588p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns588p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns588p25 Ns588p26 Ns588p42 Ns588p43 9945 Ns588p44 Ns588p45 65835 Ns588p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns588p42 Ns588p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns588p44 Ns588p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS589to600.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns588p41 Ns588p25 1 Ns588p26 := Ns588p46 rfl 

noncomputable def Ns588p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns588p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS589to600.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns588p47 Ns588p25 1 Ns588p48 := BSN.pi_combine Ns588p24 Ns588p41 Ns588p25 Ns588p26 Ns588p48 Ns588p47 rfl rfl rfl rfl RS589to600.d14 RS589to600.d15 

theorem RS589to600.d17 : Enclosure.Real.IsNear Real.pi Bool.false 28296951008113761 9007199254740992 1 9007199254740992 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns588p47 Ns588p25 1 Ns588p48 28296951008113761 9007199254740992 1 9007199254740992 RS589to600.d16 rfl 

noncomputable def Ns588p49 := nat_lit 129013261453190219981479458510875701904296875 

noncomputable def Ns588p50 := nat_lit 20028702544022979302942508184499384445755625 

noncomputable def Ns588p51 := nat_lit 105610919306899072369715234453255625 

noncomputable def Ns588p52 := nat_lit 11743816085855617508865225 

noncomputable def Ns588p53 := nat_lit 24536140990734100341796875 

noncomputable def Ns588p54 := BSN.log_dyadic_bound 3 5 18 17 Ns588p49 33554432 10890000 Ns588p50 Ns588p51 46516319 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 3) (BSN.artanhQ 5) 0 17 8 816252149187356400 5258090972900390625 87256779635025 Ns588p52 Ns588p53 1210346287688420415225 Ns588p50 Ns588p49 Ns588p51 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 3) (BSN.artanhQ 5) 0 8 816252149187356400 5258090972900390625 87256779635025 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 3) (BSN.artanhQ 5) 8 17 Ns588p52 Ns588p53 1210346287688420415225 rfl rfl rfl rfl)) rfl rfl 

theorem RS589to600.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 46516319 33554432 1 10890000 := BSN.isNear_log_sfrac 4 1 46516319 33554432 1 10890000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 46516319 33554432 10890000 rfl rfl rfl (Ns588p54 rfl rfl)) 

theorem RS589to600.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 744261104 536870912 50 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 46516319 33554432 1 10890000 744261104 536870912 50 536870912 RS589to600.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns588p55 := @Enclosure.Real.IsNear.inv_image qz325 134217729 67108864 1 67108864 16777215 16777216 33554432 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 134217729 67108864 1 67108864 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 134217729 67108864 1 67108864 134217729 67108864 1 67108864 (BSN.sqrt_enclosure 4 1 67108864 67108865 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS589to600.d20 : Enclosure.Real.IsNear qz327 Bool.false 33554431 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 33554431 67108864 1 67108864 33554431 67108864 1 67108864 (Ns588p55 rfl rfl) rfl 

theorem RS589to600.d21 : Enclosure.Real.IsNear qz327 Bool.false 268435448 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 33554431 67108864 1 67108864 268435448 536870912 8 536870912 RS589to600.d20 rfl 

noncomputable def Ns588p56 := nat_lit 24987371385403367883999025651388344673404853859375 

noncomputable def Ns588p57 := nat_lit 5174345737036840691400486158476888201456094182500 

noncomputable def Ns588p58 := nat_lit 9919565729522841605829928920966758400000 

noncomputable def Ns588p59 := nat_lit 1753791174206542693625850900 

noncomputable def Ns588p60 := nat_lit 2517933232285674949199829375 

noncomputable def Ns588p61 := BSN.log_dyadic_bound 2 3 23 22 Ns588p56 33554432 10890000 Ns588p57 Ns588p58 54003774 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 22 11 2054957030503884950940 9923762498944768499025 57668788341964800 Ns588p59 Ns588p60 172009262110757879808000 Ns588p57 Ns588p56 Ns588p58 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 0 11 2054957030503884950940 9923762498944768499025 57668788341964800 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 11 22 Ns588p59 Ns588p60 172009262110757879808000 rfl rfl rfl rfl)) rfl rfl 

theorem RS589to600.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 54003774 33554432 1 10890000 := BSN.isNear_log_sfrac 5 1 54003774 33554432 1 10890000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 54003774 33554432 10890000 rfl rfl rfl (Ns588p61 rfl rfl)) 

theorem RS589to600.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 864060384 536870912 50 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 54003774 33554432 1 10890000 864060384 536870912 50 536870912 RS589to600.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns588p62 := @Enclosure.Real.IsNear.inv_image qz328 150059981 67108864 1 67108864 15005998 15005999 33554432 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 150059981 67108864 1 67108864 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 150059981 67108864 1 67108864 150059981 67108864 1 67108864 (BSN.sqrt_enclosure 5 1 75029990 75029991 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS589to600.d24 : Enclosure.Real.IsNear qz329 Bool.false 30011997 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 30011997 67108864 1 67108864 30011997 67108864 1 67108864 (Ns588p62 rfl rfl) rfl 

theorem RS589to600.d25 : Enclosure.Real.IsNear qz329 Bool.false 240095976 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 30011997 67108864 1 67108864 240095976 536870912 8 536870912 RS589to600.d24 rfl 

noncomputable def Ns588p63 := nat_lit 2166104270535356806332416 

noncomputable def Ns588p64 := nat_lit 1208925819614629174706176 

noncomputable def Ns588p65 := BSN.log_dyadic_bound 2 10 6 5 103950000000000 33554432 10890000 1420244935680 967680 13605151 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 2) (BSN.artanhQ 10) 0 5 1420244935680 103950000000000 967680 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz584)

theorem RS589to600.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683612241143 2251799813685248 50000001089 544500000000000000 := BSN.isNear_log_sfrac 6 1 4034683612241143 2251799813685248 50000001089 544500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false Ns588p63 Ns588p64 1000000021780000 10890000000000000000000 4034683612241143 2251799813685248 50000001089 544500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 13605151 33554432 24973259072661432 36028797018963968 10890000 1000000000000000 rfl rfl rfl rfl (Ns588p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS589to600.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 961943533 536870912 51 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683612241143 2251799813685248 50000001089 544500000000000000 961943533 536870912 51 536870912 RS589to600.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns588p66 := @Enclosure.Real.IsNear.inv_image qz331 164382475 67108864 1 67108864 13698539 13698540 33554432 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 164382475 67108864 1 67108864 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 164382475 67108864 1 67108864 164382475 67108864 1 67108864 (BSN.sqrt_enclosure 6 1 82191237 82191238 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS589to600.d28 : Enclosure.Real.IsNear qz332 Bool.false 27397079 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 27397079 67108864 1 67108864 27397079 67108864 1 67108864 (Ns588p66 rfl rfl) rfl 

theorem RS589to600.d29 : Enclosure.Real.IsNear qz332 Bool.false 219176632 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 27397079 67108864 1 67108864 219176632 536870912 8 536870912 RS589to600.d28 rfl 

noncomputable def Ns588p67 := nat_lit 2352460989330532755046400 

noncomputable def Ns588p68 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 33554432 10890000 11010900719820672 5524329195 18777589 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz584)

theorem RS589to600.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381800050531575 2251799813685248 50000001089 544500000000000000 := BSN.isNear_log_sfrac 7 1 4381800050531575 2251799813685248 50000001089 544500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false Ns588p67 Ns588p64 1000000021780000 10890000000000000000000 4381800050531575 2251799813685248 50000001089 544500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 18777589 33554432 24973259072661432 36028797018963968 10890000 1000000000000000 rfl rfl rfl rfl (Ns588p68 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS589to600.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 1044702541 536870912 51 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381800050531575 2251799813685248 50000001089 544500000000000000 1044702541 536870912 51 536870912 RS589to600.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns588p69 := @Enclosure.Real.IsNear.inv_image qz334 177553365 67108864 1 67108864 12682383 12682384 33554432 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 177553365 67108864 1 67108864 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 177553365 67108864 1 67108864 177553365 67108864 1 67108864 (BSN.sqrt_enclosure 7 1 88776682 88776683 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS589to600.d32 : Enclosure.Real.IsNear qz335 Bool.false 25364767 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 25364767 67108864 1 67108864 25364767 67108864 1 67108864 (Ns588p69 rfl rfl) rfl 

theorem RS589to600.d33 : Enclosure.Real.IsNear qz335 Bool.false 202918136 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 25364767 67108864 1 67108864 202918136 536870912 8 536870912 RS589to600.d32 rfl 

noncomputable def Ns588p70 := nat_lit 2513890570116003237199872 

noncomputable def Ns588p71 := BSN.log_dyadic_bound 0 16 1 0 1 33554432 10890000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz584)

theorem RS589to600.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000003267 1089000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000003267 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false Ns588p70 Ns588p64 1000000032670000 10890000000000000000000 9364972152248037 4503599627370496 100000003267 1089000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 33554432 24973259072661432 36028797018963968 10890000 1000000000000000 rfl rfl rfl rfl (Ns588p71 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS589to600.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 1116391676 536870912 51 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000003267 1089000000000000000 1116391676 536870912 51 536870912 RS589to600.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns588p72 := @Enclosure.Real.IsNear.inv_image qz337 189812531 67108864 1 67108864 11863283 11863284 33554432 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 189812531 67108864 1 67108864 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 189812531 67108864 1 67108864 189812531 67108864 1 67108864 (BSN.sqrt_enclosure 8 1 94906265 94906266 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS589to600.d36 : Enclosure.Real.IsNear qz338 Bool.false 23726567 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 23726567 67108864 1 67108864 23726567 67108864 1 67108864 (Ns588p72 rfl rfl) rfl 

theorem RS589to600.d37 : Enclosure.Real.IsNear qz338 Bool.false 189812536 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 23726567 67108864 1 67108864 189812536 536870912 8 536870912 RS589to600.d36 rfl 

noncomputable def Ns588p73 := nat_lit 2656281492024125531619328 

noncomputable def Ns588p74 := BSN.log_dyadic_bound 1 17 3 2 1252815 33554432 10890000 1448 3 3952142 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz584)

theorem RS589to600.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 100000003267 1089000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 100000003267 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false Ns588p73 Ns588p64 1000000032670000 10890000000000000000000 9895419672221413 4503599627370496 100000003267 1089000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 3952142 33554432 24973259072661432 36028797018963968 10890000 1000000000000000 rfl rfl rfl rfl (Ns588p74 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS589to600.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 1179625948 536870912 51 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 100000003267 1089000000000000000 1179625948 536870912 51 536870912 RS589to600.d38 rfl 

noncomputable abbrev qz340 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns588p75 := @Enclosure.Real.IsNear.inv_image qz340 201326593 67108864 1 67108864 11184810 11184811 33554432 (@Enclosure.Real.IsNear.of_eq qz340 (Real.sqrt qz339) Bool.false 201326593 67108864 1 67108864 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 201326593 67108864 1 67108864 201326593 67108864 1 67108864 (BSN.sqrt_enclosure 9 1 100663296 100663297 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS589to600.d40 : Enclosure.Real.IsNear qz341 Bool.false 22369621 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 22369621 67108864 1 67108864 22369621 67108864 1 67108864 (Ns588p75 rfl rfl) rfl 

theorem RS589to600.d41 : Enclosure.Real.IsNear qz341 Bool.false 178956968 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 22369621 67108864 1 67108864 178956968 536870912 8 536870912 RS589to600.d40 rfl 

noncomputable def Ns588p76 := nat_lit 2783654566499630094221312 

noncomputable def Ns588p77 := BSN.log_dyadic_bound 2 18 4 3 3571283520 33554432 10890000 14806464 960 7487455 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz584)

theorem RS589to600.d42 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921350850277 4503599627370496 100000003267 1089000000000000000 := BSN.isNear_log_sfrac 10 1 10369921350850277 4503599627370496 100000003267 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false Ns588p76 Ns588p64 1000000032670000 10890000000000000000000 10369921350850277 4503599627370496 100000003267 1089000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 7487455 33554432 24973259072661432 36028797018963968 10890000 1000000000000000 rfl rfl rfl rfl (Ns588p77 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS589to600.d43 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 1236190956 536870912 51 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921350850277 4503599627370496 100000003267 1089000000000000000 1236190956 536870912 51 536870912 RS589to600.d42 rfl 

noncomputable abbrev qz343 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns588p78 := @Enclosure.Real.IsNear.inv_image qz343 212216861 67108864 1 67108864 10610843 10610844 33554432 (@Enclosure.Real.IsNear.of_eq qz343 (Real.sqrt qz342) Bool.false 212216861 67108864 1 67108864 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz342) Bool.false 212216861 67108864 1 67108864 212216861 67108864 1 67108864 (BSN.sqrt_enclosure 10 1 106108430 106108431 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz344 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS589to600.d44 : Enclosure.Real.IsNear qz344 Bool.false 21221687 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz344 Bool.false 21221687 67108864 1 67108864 21221687 67108864 1 67108864 (Ns588p78 rfl rfl) rfl 

theorem RS589to600.d45 : Enclosure.Real.IsNear qz344 Bool.false 169773496 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz344 Bool.false 21221687 67108864 1 67108864 169773496 536870912 8 536870912 RS589to600.d44 rfl 

noncomputable def Ns588p79 := nat_lit 2898877505641241362038784 

noncomputable def Ns588p80 := BSN.log_dyadic_bound 3 19 5 4 16049467073745 33554432 10890000 135406373544 688905 10685534 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 19) 0 4 135406373544 16049467073745 688905 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11) qz584)

theorem RS589to600.d46 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 10799160248194789 4503599627370496 100000003267 1089000000000000000 := BSN.isNear_log_sfrac 11 1 10799160248194789 4503599627370496 100000003267 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false Ns588p79 Ns588p64 1000000032670000 10890000000000000000000 10799160248194789 4503599627370496 100000003267 1089000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 10685534 33554432 24973259072661432 36028797018963968 10890000 1000000000000000 rfl rfl rfl rfl (Ns588p80 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS589to600.d47 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 1287360220 536870912 51 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 10799160248194789 4503599627370496 100000003267 1089000000000000000 1287360220 536870912 51 536870912 RS589to600.d46 rfl 

noncomputable abbrev qz346 := (Real.sqrt (@Nat.cast Real Real.instNatCast 11))

noncomputable def Ns588p81 := @Enclosure.Real.IsNear.inv_image qz346 222574921 67108864 1 67108864 10117041 10117042 33554432 (@Enclosure.Real.IsNear.of_eq qz346 (Real.sqrt qz345) Bool.false 222574921 67108864 1 67108864 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz345) Bool.false 222574921 67108864 1 67108864 222574921 67108864 1 67108864 (BSN.sqrt_enclosure 11 1 111287460 111287461 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz347 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

theorem RS589to600.d48 : Enclosure.Real.IsNear qz347 Bool.false 20234083 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz347 Bool.false 20234083 67108864 1 67108864 20234083 67108864 1 67108864 (Ns588p81 rfl rfl) rfl 

theorem RS589to600.d49 : Enclosure.Real.IsNear qz347 Bool.false 161872664 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz347 Bool.false 20234083 67108864 1 67108864 161872664 536870912 8 536870912 RS589to600.d48 rfl 

noncomputable def Ns588p82 := nat_lit 3004067793907357885399040 

noncomputable def Ns588p83 := BSN.log_dyadic_bound 4 20 6 5 106444800000000000 33554432 10890000 1454330814136320 990904320 13605151 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 4) (BSN.artanhQ 20) 0 5 1454330814136320 106444800000000000 990904320 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz738 := (Enclosure.sfrac Bool.false 12 1)

noncomputable abbrev qz585 := qz738

noncomputable abbrev qz348 := qz585

noncomputable abbrev qz1 := qz348

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12) qz584)

theorem RS589to600.d50 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 11191024608564965 4503599627370496 100000003267 1089000000000000000 := BSN.isNear_log_sfrac 12 1 11191024608564965 4503599627370496 100000003267 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz349) Bool.false Ns588p82 Ns588p64 1000000032670000 10890000000000000000000 11191024608564965 4503599627370496 100000003267 1089000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 13605151 33554432 24973259072661432 36028797018963968 10890000 1000000000000000 rfl rfl rfl rfl (Ns588p83 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS589to600.d51 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 1334074092 536870912 51 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 11191024608564965 4503599627370496 100000003267 1089000000000000000 1334074092 536870912 51 536870912 RS589to600.d50 rfl 

noncomputable abbrev qz350 := (Real.sqrt (@Nat.cast Real Real.instNatCast 12))

noncomputable def Ns588p84 := @Enclosure.Real.IsNear.inv_image qz350 232471925 67108864 1 67108864 9686330 9686331 33554432 (@Enclosure.Real.IsNear.of_eq qz350 (Real.sqrt qz349) Bool.false 232471925 67108864 1 67108864 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz349) Bool.false 232471925 67108864 1 67108864 232471925 67108864 1 67108864 (BSN.sqrt_enclosure 12 1 116235962 116235963 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz351 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))

theorem RS589to600.d52 : Enclosure.Real.IsNear qz351 Bool.false 19372661 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz351 Bool.false 19372661 67108864 1 67108864 19372661 67108864 1 67108864 (Ns588p84 rfl rfl) rfl 

theorem RS589to600.d53 : Enclosure.Real.IsNear qz351 Bool.false 154981288 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz351 Bool.false 19372661 67108864 1 67108864 154981288 536870912 8 536870912 RS589to600.d52 rfl 

theorem RS589to600.d54 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz739 := (@instHMul Real Real.instMul)

noncomputable abbrev qz586 := (@HMul.hMul Real Real Real qz739 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz352 := qz586

noncomputable abbrev qz2 := qz352

theorem RS589to600.d55 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS589to600.d54 rfl 

noncomputable abbrev qz353 := (@Inv.inv Real Real.instInv qz586)

noncomputable abbrev qz3 := qz353

theorem RS589to600.d56 : Enclosure.Real.IsNear qz3 Bool.false 10680707 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 10680707 67108864 1 67108864 10680707 67108864 1 67108864 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 5340353 5340354 33554432 RS589to600.d55 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns588p85 := nat_lit 3073029562477593169017091 

noncomputable def Ns588p86 := nat_lit 3214160687403152273571840000 

noncomputable def Ns588p87 := nat_lit 1326281779029828119438842396672 

noncomputable abbrev qz740 := (Enclosure.sfrac Bool.false 989310 1000)

noncomputable abbrev qz587 := qz740

noncomputable abbrev qz354 := qz587

noncomputable abbrev qz4 := qz354

noncomputable abbrev qz588 := qz739

noncomputable abbrev qz355 := qz588

noncomputable abbrev qz5 := qz355

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 12)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz741 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 989310 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz589 := qz741

noncomputable abbrev qz356 := qz589

noncomputable abbrev qz8 := qz356

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz742 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 989310 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz590 := qz742

noncomputable abbrev qz357 := qz590

noncomputable abbrev qz10 := qz357

noncomputable abbrev qz591 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns588p88 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HMul.hMul Real Real Real qz5 qz591 (Zeta.RiemannSiegel.correction qz10)) 266197881 134217728 255895 268435456 515563994530631336057 4722366482869645213696 9024302669329796217091 Ns588p86 Ns588p87 

noncomputable def Ns588p89 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin BSN.quadSignPos 11 12 989310 1000 287 536870912 268435456 9007199254740992 Bool.false 1077755793978 4505 1334074092 51 154981288 8 

noncomputable def Ns588p90 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 989310 1000 172 232 536870912 268435456 9007199254740992 Bool.false 1077755793978 4505 

noncomputable def Ns588p91 := Ns588p90 1236190956 51 169773496 8 1287360220 51 161872664 8 Bool.true 852599615 206049 Bool.true 170125378 Bool.true 193498554 28296951008113761 1 Bool.false 510140777 Bool.false Bool.false 502376466 Bool.false Bool.true 539806733 

noncomputable def Ns588p92 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 989310 1000 31 105 536870912 268435456 9007199254740992 Bool.false 1077755793978 4505 

noncomputable def Ns588p93 := Ns588p92 1116391676 51 189812536 8 1179625948 51 178956968 8 Bool.true 842771045 168278 Bool.true 558894453 Bool.true 711892701 28296951008113761 1 Bool.false 463277267 Bool.false Bool.false 520865475 Bool.true Bool.true 852599615 

noncomputable def Ns588p94 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 989310 1000 149 52 536870912 268435456 9007199254740992 Bool.false 1077755793978 4505 

noncomputable def Ns588p95 := Ns588p94 961943533 51 219176632 8 1044702541 51 202918136 8 Bool.true 839067961 125048 Bool.false 441523722 Bool.false 368750601 28296951008113761 1 Bool.false 393409570 Bool.true Bool.false 415133454 Bool.false Bool.true 842771045 

noncomputable def Ns588p96 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 989310 1000 404 264 536870912 268435456 9007199254740992 Bool.false 1077755793978 4505 

noncomputable def Ns588p97 := Ns588p96 744261104 50 268435448 8 864060384 50 240095976 8 Bool.true 1088945807 73906 Bool.false 751639140 Bool.false 297093358 28296951008113761 1 Bool.false 91230840 Bool.false Bool.false 456744664 Bool.false Bool.true 839067961 

noncomputable def Ns588p98 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 989310 1000 841 586 536870912 268435456 9007199254740992 Bool.false 1077755793978 4505 

noncomputable def Ns588p99 := Ns588p98 372130544 50 379625064 8 589812976 50 309962568 8 Bool.true 536870584 4562 Bool.false 375531149 Bool.false 65412763 28296951008113761 1 Bool.false 345648690 Bool.true Bool.false 532890868 Bool.true Bool.true 1088945807 

noncomputable def Ns588p100 := nat_lit 3390509647814380462864379869540025196806875509028073 

noncomputable def Ns588p101 := nat_lit 1688941054120953734239852095789545142029280870400 

noncomputable def Ns588p102 := nat_lit 1784217600000000000000000 

noncomputable def Ns588p103 := nat_lit 454886987173963821122719248000000000 

noncomputable def Ns588p104 := nat_lit 2700145793548462266670403561993280000000 

noncomputable abbrev qz358 := (@Eq.refl Real qz587)

noncomputable abbrev qz11 := qz358

noncomputable def Ns588p105 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 989310 1000 3914938104400 16000000 1978620 4000 2000 Ns588p103 Ns588p104 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns588p106 := nat_lit 9764667785705415733049414024275272566803801466000850240000000 

noncomputable abbrev qz743 := (@instHSub Real Real.instSub)

noncomputable abbrev qz592 := qz743

noncomputable abbrev qz359 := qz592

noncomputable abbrev qz593 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz744 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz745 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz594 := (@HSub.hSub Real Real Real qz743 qz744 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz745 (@Nat.cast Real Real.instNatCast 1978620))))

noncomputable abbrev qz360 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 989310 4000) (Real.log (Enclosure.sfrac Bool.false 3914938104400 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz594))

noncomputable abbrev qz595 := (Enclosure.sfrac Bool.false 989310 2000)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz360 qz595) (@HMul.hMul Real Real Real qz355 qz595 (Real.log Real.pi)))

noncomputable def Ns588p107 := @Enclosure.Real.IsNear.addLit_ft_p qz12 (Enclosure.sfrac Bool.true Ns588p103 Ns588p104) 3616348653649729544933 1801439850948198400 14969747183775814213 Ns588p102 Ns588p103 Ns588p104 0 1 Ns588p106 

noncomputable def Ns588p108 := nat_lit 24268904997436280366769058611200 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz359 qz360 qz595)

noncomputable def Ns588p109 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (@HMul.hMul Real Real Real qz5 qz595 (Real.log Real.pi)) 4636407412039629529829 1801439850948198400 1246639331564053 435600000000000000000 3800014996491 6710886400 296793 53687091200 Ns588p108 3616348653649729544933 1801439850948198400 

noncomputable def Ns588p110 := nat_lit 9272814824079259059658000 

noncomputable abbrev qz14 := qz360

noncomputable def Ns588p111 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz595 5527498641510410609381 1801439850948198400 1246639331564053 435600000000000000000 989310 2000 0 1 Ns588p110 4636407412039629529829 1801439850948198400 1246639331564053 435600000000000000000 

noncomputable def Ns588p112 := nat_lit 12446820411098604036855077695010111488 

noncomputable def Ns588p113 := nat_lit 120000117649616434309890048 

noncomputable def Ns588p114 := nat_lit 9671406556917033397649408 

noncomputable def Ns588p115 := nat_lit 100395840415646289248966601733400787574534351155477633707479658601095070638427441210602294887194662559107287388938164401715197723888737578685566770505059471026217866514857753313280000000000000000000000000000000000 

noncomputable def Ns588p116 := nat_lit 3238958199471774905590600583264349727741904591782689199306372567151582794590626030166443887292867688224677812084191206091826578128944389683135493418327071293408614498129105911808000000000000000000000000000000000 

noncomputable def Ns588p117 := nat_lit 28810020876356025965256794501168656947225405632988179672668099026078098487393182665075002857061327309998531308456217557382650437383496611592530367096376520153151402147840000000000000000000000000000000000 

noncomputable def Ns588p118 := BSN.log_dyadic_bound 1817786104400 6012090104400 9 8 Ns588p115 268435456 87120000 Ns588p116 Ns588p117 167562588 7829876208800 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1817786104400) (BSN.artanhQ 6012090104400) 0 8 Ns588p116 Ns588p115 Ns588p117 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz361 := (Real.log (Enclosure.sfrac Bool.false 3914938104400 16000000))

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns588p119 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 989310 4000) qz361 989310 4000 0 1 55879409261800551 4503599627370496 12500018513 1089000000000000000 5528205837679190310981 1801439850948198400 412213110503201 145200000000000000000 (Enclosure.Real.IsNear.const Bool.false 989310 4000) (BSN.isNear_log_sfrac 3914938104400 16000000 55879409261800551 4503599627370496 12500018513 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3914938104400) qz362)) Bool.false Ns588p113 Ns588p114 1000001481040000 87120000000000000000000 55879409261800551 4503599627370496 12500018513 1089000000000000000 (BSN.log_rat_reduce_isNear 3914938104400 16000000 17 7829876208800 4194304000000 167562588 268435456 24973259072661432 36028797018963968 87120000 1000000000000000 rfl rfl rfl rfl (Ns588p118 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p120 := BSN.arctan_dyadic_bound_f 1000 1978620 1 0 33554432 10890000 0 1 1 0 1 1 16958 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1978620) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1978620) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz596 := qz744

noncomputable abbrev qz363 := qz596

noncomputable abbrev qz15 := qz363

noncomputable abbrev qz597 := qz745

noncomputable abbrev qz364 := qz597

noncomputable abbrev qz16 := qz364

noncomputable abbrev qz746 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz598 := qz746

noncomputable abbrev qz365 := qz598

noncomputable abbrev qz17 := (@Enclosure.Real.IsNear.mulLit_ff qz365 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def Ns588p121 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1978620))) 884279719003555 562949953421312 1 2000000000000000 16958 33554432 1 10890000 29661957194973775396864 883995210974627 562949953421312 200000001089 2178000000000000000 qz17 (Ns588p120 rfl) rfl rfl 

noncomputable abbrev qz366 := (@HMul.hMul Real Real Real qz588 qz593 qz594)

noncomputable abbrev qz18 := qz366

noncomputable abbrev qz367 := qz593

noncomputable abbrev qz19 := qz367

noncomputable abbrev qz368 := qz594

noncomputable abbrev qz20 := qz368

noncomputable abbrev qz369 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns588p122 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 989310 4000) qz361) qz18 5528205837679190310981 1801439850948198400 412213110503201 145200000000000000000 883995210974627 2251799813685248 200000001089 8712000000000000000 Ns588p112 5527498641510410609381 1801439850948198400 1246639331564053 435600000000000000000 (Ns588p119 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz20 1 4 0 1 883995210974627 562949953421312 200000001089 2178000000000000000 883995210974627 2251799813685248 200000001089 8712000000000000000 qz369 Ns588p121 rfl) 

noncomputable def Ns588p123 := @Ns588p107 Ns588p100 Ns588p101 14969747183775814213 Ns588p102 (@Ns588p109 14969747183775814213 Ns588p102 (Ns588p111 (Ns588p122 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 989310 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz595 (Real.log Real.pi) 989310 2000 0 1 38410761 33554432 3 268435456 3800014996491 6710886400 296793 53687091200 (Enclosure.Real.IsNear.const Bool.false 989310 2000) RS589to600.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns588p103 Ns588p104) 

noncomputable abbrev qz370 := (@instHAdd Real Real.instAdd)

noncomputable def Ns588p124 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns588p100 Ns588p101 14969747183775814213 Ns588p102 134719474247 67108864 141 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz370 qz12 (Enclosure.sfrac Bool.true Ns588p103 Ns588p104)) Bool.false Ns588p100 Ns588p101 14969747183775814213 Ns588p102 Ns588p105 (Ns588p123 rfl rfl)) 

noncomputable def Ns588p125 := nat_lit 15181133252409915965702144 

noncomputable def Ns588p126 := nat_lit 14339918260521337984093928449857706428895337992422979424938158871635764834021570167557937606506062736501816445937758535114688232828479129849856 

noncomputable def Ns588p127 := nat_lit 282877490902138091004622673603363019119652456796264491099280832830873987773707601701812303598028785564314492868916806270538811366318583631052800 

noncomputable def Ns588p128 := nat_lit 10164656365699597378961300447295050203504093923589197284025089530082683711182599015255368255118032261703295183531424451438851439590445056 

noncomputable def Ns588p129 := nat_lit 71610745523513071506346624427588820179552354608965471550338322744172239125901496004769153515947327402754260778178470402720756959774568699990016 

noncomputable def Ns588p130 := nat_lit 9900712181574833185161793576117705669187835987869257188474829149080589572079766059563430625931007494751007250412088219468858397821150427086848000 

noncomputable def Ns588p131 := BSN.sin_dyadic_bound_f 215736879062 137438953472 4 3 67108864 21801270 Ns588p126 Ns588p127 Ns588p128 Ns588p129 Ns588p130 Ns588p128 67108823 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215736879062) (BSN.sinEvenQ 137438953472) 0 3 Ns588p126 Ns588p127 Ns588p128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215736879062) (BSN.sinOddQ 137438953472) 0 3 Ns588p129 Ns588p130 Ns588p128 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz371 := (@Nat.cast Real Real.instNatCast 67108864)

noncomputable abbrev qz372 := (@Nat.cast Real Real.instNatCast Ns588p114)

noncomputable def Ns588p132 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 134719474247) qz371) Bool.false 134719474247 67108864 141 16777216 Bool.true 67108823 67108864 1 10890000 (Ns588p124 rfl) (Enclosure.sfrac_false_div 134719474247 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 134719474247) qz371) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns588p125) qz372) 226375608064910080 72057594037927936 Bool.false 67108823 67108864 319 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q1 134719474247 67108864 226375608064910080 72057594037927936 319 Ns588p125 Ns588p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108823 67108864 Ns588p125 Ns588p114 215736879062 137438953472 21801270 21780000 (Ns588p131 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p133 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns588p100 Ns588p101 14969747183775814213 Ns588p102 1077755793978 536870912 4505 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz370 qz12 (Enclosure.sfrac Bool.true Ns588p103 Ns588p104)) Bool.false Ns588p100 Ns588p101 14969747183775814213 Ns588p102 Ns588p105 (Ns588p123 rfl rfl)) 

noncomputable def Ns588p134 := Ns588p99 73906 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 841 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 345648690 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 586 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 532890868 536870912) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 67108823 67108864 97016701 11418992640000 536870584 536870912 4562 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 67108823 67108864 97016701 11418992640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 67108823 67108864 1552267216 182703882240000 67108823 67108864 97016701 11418992640000 (Ns588p132 rfl rfl) rfl)) rfl) (Ns588p133 rfl) RS589to600.d7 

noncomputable def Ns588p135 := nat_lit 4996656871497898017469303988834759733343519748661515198735588366980191265 

noncomputable def Ns588p136 := nat_lit 2504505714323359787184324207303086996185458423821189873137376790332288532480 

noncomputable def Ns588p137 := nat_lit 395519343655538078730350125812384062971783063115838823953353733280801 

noncomputable def Ns588p138 := nat_lit 13085841917842862031720708927696864965512025978677971305259187912237093921 

noncomputable def Ns588p139 := nat_lit 45915938095928262765045943800556594930066737770055147674185241156091956428800 

noncomputable abbrev qz373 := (BSN.sinEvenQ 536870912)

noncomputable abbrev qz374 := (BSN.sinOddQ 536870912)

noncomputable def Ns588p140 := BSN.sin_dyadic_bound_f 375531149 536870912 3 2 536870912 268435456 Ns588p135 Ns588p136 Ns588p137 Ns588p138 Ns588p139 Ns588p137 345648690 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 375531149) qz373 0 2 Ns588p135 Ns588p136 Ns588p137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 375531149) qz374 0 2 Ns588p138 Ns588p139 Ns588p137 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p141 := nat_lit 18308382431720168996522829400561 

noncomputable def Ns588p142 := nat_lit 1993841993677373809355710590420516864 

noncomputable def Ns588p143 := nat_lit 29907629905160607140335658856307752960 

noncomputable abbrev qz375 := (BSN.cosEvenQ 536870912)

noncomputable abbrev qz376 := (BSN.cosOddQ 536870912)

noncomputable def Ns588p144 := BSN.cos_dyadic_bound_f 65412763 536870912 2 1 536870912 268435456 Ns588p141 Ns588p142 Ns588p141 Ns588p141 Ns588p143 Ns588p141 532890868 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 65412763) qz375 0 1 Ns588p141 Ns588p142 Ns588p141 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 65412763) qz376 0 1 Ns588p141 Ns588p143 Ns588p141 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p145 := nat_lit 44067117396726192950717375625617367509894714257391797400550718402658018659628478498911774832387022263681024000000 

noncomputable def Ns588p146 := nat_lit 274647376664257459544000446540783031995164976078897331880025758552119769180746491160307949742358795015190845849600 

noncomputable def Ns588p147 := nat_lit 32517162675193515486563588403474155876430677988003049797208742373283756149400823292661302890496000000000000 

noncomputable def Ns588p148 := nat_lit 266933688903289231457691591662807896218289778076590023471142289530517723086089545715405721562465223449614745600000 

noncomputable def Ns588p149 := nat_lit 24992911276447428818504040635211255911560012823179657201082344028242898995447930695588023426554650346382366972313600 

noncomputable def Ns588p150 := BSN.cos_dyadic_bound_f 751639140 536870912 4 3 536870912 268435456 Ns588p145 Ns588p146 Ns588p147 Ns588p148 Ns588p149 Ns588p147 91230840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 751639140) qz375 0 3 Ns588p145 Ns588p146 Ns588p147 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 751639140) qz376 0 3 Ns588p148 Ns588p149 Ns588p147 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p151 := nat_lit 1087388636629828421824439336815762267705446906626085739109745766352240896 

noncomputable def Ns588p152 := nat_lit 278278412702595531909369356367009666242828713757909985904152976703587614720 

noncomputable def Ns588p153 := nat_lit 60693689768978717044842173287675160599683840095612298163682115010816 

noncomputable def Ns588p154 := nat_lit 3262044522509947308039228326100711452795141352198065992732909934826701056 

noncomputable def Ns588p155 := nat_lit 12522528571616798935921621036515434980927292119105949365686883951661442662400 

noncomputable def Ns588p156 := BSN.cos_dyadic_bound_f 297093358 536870912 3 2 536870912 268435456 Ns588p151 Ns588p152 Ns588p153 Ns588p154 Ns588p155 Ns588p153 456744664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 297093358) qz375 0 2 Ns588p151 Ns588p152 Ns588p153 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 297093358) qz376 0 2 Ns588p154 Ns588p155 Ns588p153 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p157 := Ns588p97 125048 BSN.abs_quadSignPos (BSN.cos_quad_nat0 404 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 91230840 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 264 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 456744664 536870912) qz11 rfl rfl (Ns588p134 RS589to600.d9 RS589to600.d11 RS589to600.d13 RS589to600.d17 (Ns588p140 rfl rfl) (Ns588p144 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns588p133 rfl) RS589to600.d19 RS589to600.d21 RS589to600.d23 RS589to600.d25 RS589to600.d17 (Ns588p150 rfl rfl) (Ns588p156 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns588p158 := nat_lit 9548675693908033684944478035551888961267990939121018416120901294780965120 

noncomputable def Ns588p159 := nat_lit 1444216615052449609770531802479979522650829573250481365550548300718336 

noncomputable def Ns588p160 := nat_lit 25006098085715717589772099708289027312665208259341214120010516789082317056 

noncomputable def Ns588p161 := BSN.sin_dyadic_bound_f 441523722 536870912 3 2 536870912 268435456 Ns588p158 Ns588p136 Ns588p159 Ns588p160 Ns588p139 Ns588p159 393409570 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 441523722) qz373 0 2 Ns588p158 Ns588p136 Ns588p159 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 441523722) qz374 0 2 Ns588p160 Ns588p139 Ns588p159 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p162 := nat_lit 2580936125098684801997569597477345579276800154381365329886234663882217281 

noncomputable def Ns588p163 := nat_lit 341870710451752393848001957447939533269432052073751563689787056084801 

noncomputable def Ns588p164 := nat_lit 7742124633875150901205012788517140858763861599039948486531324417534482241 

noncomputable def Ns588p165 := BSN.cos_dyadic_bound_f 368750601 536870912 3 2 536870912 268435456 Ns588p162 Ns588p152 Ns588p163 Ns588p164 Ns588p155 Ns588p163 415133454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 368750601) qz375 0 2 Ns588p162 Ns588p152 Ns588p163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 368750601) qz376 0 2 Ns588p164 Ns588p155 Ns588p163 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p166 := Ns588p95 168278 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 149 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 393409570 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 415133454 536870912) qz11 rfl rfl (Ns588p157 rfl rfl) (Ns588p133 rfl) RS589to600.d27 RS589to600.d29 RS589to600.d31 RS589to600.d33 RS589to600.d17 (Ns588p161 rfl rfl) (Ns588p165 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p167 := nat_lit 24521617846456492199896923128951652923949121752754499937816940980158306145 

noncomputable def Ns588p168 := nat_lit 9520031695120747223215010272911949204633394286808093113390457284433761 

noncomputable def Ns588p169 := nat_lit 64207871451308236456606736273479138311630674333130762924479832302906480481 

noncomputable def Ns588p170 := BSN.sin_dyadic_bound_f 558894453 536870912 3 2 536870912 268435456 Ns588p167 Ns588p136 Ns588p168 Ns588p169 Ns588p139 Ns588p168 463277267 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 558894453) qz373 0 2 Ns588p167 Ns588p136 Ns588p168 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 558894453) qz374 0 2 Ns588p169 Ns588p139 Ns588p168 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p171 := nat_lit 92078890217254039950254546696265056319233208133795700746523157993940547312888989916817065781125532704756333682801 

noncomputable def Ns588p172 := nat_lit 3570415896635346974072005805030179415937144689025665314440334861177556999349704385084003346650664335197480996044800 

noncomputable def Ns588p173 := nat_lit 16942382482510021626678617170475240186391509613168820324204636387413279613314201042490319399852730979852401 

noncomputable def Ns588p174 := nat_lit 460103713903658283849249731793617307536474162419095783072330705872656010719603171337818829392088182464449121230961 

noncomputable def Ns588p175 := nat_lit 124964556382237144092520203176056279557800064115898286005411720141214494977239653477940117132773251731911834861568000 

noncomputable def Ns588p176 := BSN.sin_dyadic_bound_f 711892701 536870912 4 3 536870912 268435456 Ns588p171 Ns588p172 Ns588p173 Ns588p174 Ns588p175 Ns588p173 520865475 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 711892701) qz373 0 3 Ns588p171 Ns588p172 Ns588p173 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 711892701) qz374 0 3 Ns588p174 Ns588p175 Ns588p173 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p177 := Ns588p93 206049 BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 463277267 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 520865475 536870912) qz11 rfl rfl (Ns588p166 rfl) (Ns588p133 rfl) RS589to600.d35 RS589to600.d37 RS589to600.d39 RS589to600.d41 RS589to600.d17 (Ns588p170 rfl rfl) (Ns588p176 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p178 := nat_lit 116914344213836433841756716993751391483629737721740329620032721884610816 

noncomputable def Ns588p179 := nat_lit 701702179307938310210004270569177311052926405512751253387444551936 

noncomputable def Ns588p180 := nat_lit 350741629237150685648649730972713036096267107312409963357591390764728576 

noncomputable def Ns588p181 := BSN.cos_dyadic_bound_f 170125378 536870912 3 2 536870912 268435456 Ns588p178 Ns588p152 Ns588p179 Ns588p180 Ns588p155 Ns588p179 510140777 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 170125378) qz375 0 2 Ns588p178 Ns588p152 Ns588p179 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 170125378) qz376 0 2 Ns588p180 Ns588p155 Ns588p179 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p182 := nat_lit 195660895379468245356408659239693736407782441673440582107129819712758016 

noncomputable def Ns588p183 := nat_lit 1965268039122422265278663628768346050372811829747973184946321531136 

noncomputable def Ns588p184 := nat_lit 586978755602326491224695420391823672531246579396662250375019566495211776 

noncomputable def Ns588p185 := BSN.cos_dyadic_bound_f 193498554 536870912 3 2 536870912 268435456 Ns588p182 Ns588p152 Ns588p183 Ns588p184 Ns588p155 Ns588p183 502376466 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 193498554) qz375 0 2 Ns588p182 Ns588p152 Ns588p183 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 193498554) qz376 0 2 Ns588p184 Ns588p155 Ns588p183 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p186 := Ns588p91 240019 BSN.abs_quadSignPos (BSN.cos_quad_nat0 172 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 510140777 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 232 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 502376466 536870912) qz11 rfl rfl (Ns588p177 rfl) (Ns588p133 rfl) RS589to600.d43 RS589to600.d45 RS589to600.d47 RS589to600.d49 RS589to600.d17 (Ns588p181 rfl rfl) (Ns588p185 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p187 := nat_lit 435036519528101219471086037281 

noncomputable def Ns588p188 := nat_lit 9969209968386869046778552952102584320 

noncomputable def Ns588p189 := nat_lit 69784469778708083327449870664718090240 

noncomputable def Ns588p190 := BSN.sin_dyadic_bound_f 25682153 536870912 2 1 536870912 268435456 Ns588p187 Ns588p188 Ns588p187 Ns588p187 Ns588p189 Ns588p187 25672359 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 25682153) qz373 0 1 Ns588p187 Ns588p188 Ns588p187 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 25682153) qz374 0 1 Ns588p187 Ns588p189 Ns588p187 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p191 := Ns588p89 Bool.true 539806733 240019 Bool.true 25682153 28296951008113761 1 Bool.false 25672359 Bool.false Bool.true 532395762 255895 BSN.abs_quadSignPos (BSN.cos_quad_nat3 287 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 25672359 536870912) qz11 rfl (Ns588p186 rfl) (Ns588p133 rfl) RS589to600.d51 RS589to600.d53 RS589to600.d17 (Ns588p190 rfl rfl) rfl 

noncomputable def Ns588p192 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) 532395762 536870912 255895 536870912 532395762 536870912 255895 536870912 571655596579749888 266197881 134217728 255895 268435456 (Ns588p191 rfl rfl rfl rfl) 

noncomputable def Ns588p193 := @Enclosure.Real.IsNear.mulLit_ff qz591 (Zeta.RiemannSiegel.correction qz10) 4736219 16777216 1 33554432 108855607084603 281474976710656 1897559381600413 191578906023690240000 515563994530631336057 4722366482869645213696 

noncomputable abbrev qz599 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns588p194 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz599 1 1 0 1 4736219 16777216 1 33554432 4736219 16777216 1 33554432 

noncomputable abbrev qz21 := (@Enclosure.Real.IsNear.of_eq qz356 (@HMul.hMul Real Real Real qz355 qz354 qz353) Bool.false 1056653024217 6710886400 98931 6710886400 (BSN.t_div_two_pi_mk qz354 989310 1000 qz358) (@Enclosure.Real.IsNear.mulLit_ff qz354 qz353 989310 1000 0 1 10680707 67108864 1 67108864 1056653024217 6710886400 98931 6710886400 (Enclosure.Real.IsNear.const Bool.false 989310 1000) RS589to600.d56 rfl))

noncomputable def Ns588p195 := @Enclosure.Real.IsNear.sqrt_image qz8 1056653024217 6710886400 98931 6710886400 421042686 421042726 33554432 qz21 

noncomputable abbrev qz747 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 989310 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz600 := qz747

noncomputable abbrev qz377 := qz600

noncomputable abbrev qz22 := qz377

noncomputable def Ns588p196 := @Enclosure.Real.IsNear.sqrt_image qz22 210521353 16777216 5 8388608 118860625 118860631 33554432 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 842085412 67108864 40 67108864 210521353 16777216 5 8388608 (Ns588p195 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz601 := (Real.sqrt qz747)

noncomputable abbrev qz378 := qz601

noncomputable abbrev qz23 := qz378

noncomputable def Ns588p197 := @Enclosure.Real.IsNear.inv_image qz23 29715157 8388608 3 33554432 9472437 9472439 33554432 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 237721256 67108864 6 67108864 29715157 8388608 3 33554432 (Ns588p196 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns588p198 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 18944876 67108864 2 67108864 4736219 16777216 1 33554432 (Ns588p197 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz379 := (@HMul.hMul Real Real Real qz588 qz586 qz590)

noncomputable abbrev qz24 := (Real.cos qz379)

noncomputable abbrev qz602 := (@HMul.hMul Real Real Real qz739 qz742 qz742)

noncomputable abbrev qz603 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz380 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz602 qz590) qz603)

noncomputable abbrev qz25 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz380))

noncomputable def Ns588p199 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz24) qz25) Bool.false 108855607084603 

noncomputable def Ns588p200 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz24) qz25 70287967 67108864 285 

noncomputable abbrev qz26 := (@Neg.neg Real Real.instNeg (Real.cos qz379))

noncomputable def Ns588p201 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz24) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz26)) Bool.true 70287967 67108864 285 67108864 (BSN.inv_eq_neg_inv_neg qz24) 

noncomputable def Ns588p202 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz26) Bool.false 70287967 67108864 285 67108864 70287967 67108864 

noncomputable def Ns588p203 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true 64073551 67108864 2822278864 730815528960000 64073551 67108864 176392429 45675970560000 

noncomputable abbrev qz27 := qz379

noncomputable abbrev qz381 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns588p204 := @Enclosure.Real.IsNear.cos_image qz27 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 57772387) qz381) Bool.false 57772387 16777216 253 67108864 Bool.true 64073551 67108864 1 

noncomputable def Ns588p205 := nat_lit 134930377084711425065381091 

noncomputable def Ns588p206 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns588p207 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 9194761 16777216 5 8388608 8130740673384846375355 2361183241434822606848 Ns588p205 

noncomputable def Ns588p208 := @Enclosure.Real.IsNear.subLit_ff_p qz22 qz1 210521353 16777216 5 8388608 12 1 0 1 9194761 9194761 16777216 5 

noncomputable abbrev qz382 := (Enclosure.Real.IsNear.const Bool.false 12 1)

noncomputable def Ns588p209 := @Ns588p208 8388608 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 842085412 67108864 40 67108864 210521353 16777216 5 8388608 (Ns588p195 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns588p210 := @Enclosure.Real.IsNear.recentre' qz27 Bool.false 8130740673384846375355 2361183241434822606848 Ns588p205 Ns588p206 57772387 16777216 253 67108864 (@Ns588p207 Ns588p206 RS589to600.d55 (Ns588p209 rfl rfl) rfl) 

noncomputable def Ns588p211 := nat_lit 2417851639229258349412352 

noncomputable def Ns588p212 := nat_lit 2964483729632873471823497401869596925610561 

noncomputable def Ns588p213 := nat_lit 8563486156235759286349715816696970818296479744 

noncomputable def Ns588p214 := nat_lit 128452292343536389295245737250454562274447196160 

noncomputable abbrev qz383 := (BSN.cosEvenQ 137438953472)

noncomputable abbrev qz384 := (BSN.cosOddQ 137438953472)

noncomputable def Ns588p215 := BSN.cos_dyadic_bound_f 41494187759 137438953472 2 1 67108864 21801270 Ns588p212 Ns588p213 Ns588p212 Ns588p212 Ns588p214 Ns588p212 64073551 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 41494187759) qz383 0 1 Ns588p212 Ns588p213 Ns588p212 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 41494187759) qz384 0 1 Ns588p212 Ns588p214 Ns588p212 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p216 := @Ns588p204 10890000 (Ns588p210 rfl) (Enclosure.sfrac_false_div 57772387 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 57772387) qz381) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 729973470823453927931904) (@Nat.cast Real Real.instNatCast Ns588p211)) 226375608064910080 72057594037927936 Bool.false 64073551 67108864 0 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 57772387 16777216 226375608064910080 72057594037927936 0 729973470823453927931904 Ns588p211 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 64073551 67108864 729973470823453927931904 Ns588p211 41494187759 137438953472 21801270 21780000 (Ns588p215 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p217 := @Enclosure.Real.IsNear.inv_image qz26 64073551 67108864 176392429 45675970560000 35143841 35144126 33554432 (@Enclosure.Real.IsNear.neg qz24 Bool.true 64073551 67108864 176392429 45675970560000 (Ns588p203 (Ns588p216 rfl rfl) rfl)) 

noncomputable def Ns588p218 := Ns588p201 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz26) Bool.false 70287967 67108864 285 67108864 (@Ns588p202 285 67108864 (Ns588p217 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p219 := @Enclosure.Real.IsNear.recentre' qz25 Bool.true 12389672 33554432 

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz355 qz352 qz380)

noncomputable def Ns588p220 := @Enclosure.Real.IsNear.cos_image qz28 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 130794403)) qz371) Bool.true 130794403 67108864 

noncomputable def Ns588p221 := nat_lit 77207388604624737543534295405 

noncomputable def Ns588p222 := nat_lit 39614081257132168796771975168 

noncomputable def Ns588p223 := nat_lit 1186265641867310607743383563738549 

noncomputable def Ns588p224 := @Enclosure.Real.IsNear.recentre' qz28 Bool.true Ns588p221 Ns588p222 Ns588p223 

noncomputable def Ns588p225 := nat_lit 151115727451828646838272000000000000000 

noncomputable abbrev qz29 := qz380

noncomputable def Ns588p226 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz29 884279719003555 140737488355328 1 500000000000000 87311047562671 

noncomputable abbrev qz385 := (@HSub.hSub Real Real Real qz592 qz602 qz590)

noncomputable abbrev qz30 := qz385

noncomputable abbrev qz386 := qz603

noncomputable abbrev qz31 := qz386

noncomputable def Ns588p227 := @Enclosure.Real.IsNear.subLit_tf qz30 qz31 69718861518255 281474976710656 43958435 35184372088832 1 16 

noncomputable abbrev qz387 := qz602

noncomputable abbrev qz32 := qz387

noncomputable def Ns588p228 := @Enclosure.Real.IsNear.subLit_ff_n qz32 qz10 84543629847121 281474976710656 22986915 35184372088832 9194761 16777216 5 8388608 

noncomputable def Ns588p229 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 9194761 16777216 5 8388608 9194761 16777216 5 8388608 84543629847121 281474976710656 

noncomputable def Ns588p230 := nat_lit 2423483421533933358279486614552213050628102545363025509491928323754474833605362673318796739423222942321 

noncomputable def Ns588p231 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600 

noncomputable def Ns588p232 := nat_lit 25065127543065666453578869068732411836337124756472886947747685219870128502410527109193426485693041 

noncomputable def Ns588p233 := nat_lit 14618873374174761139429387527019300572517325464247860809655973615508853838317746392391351642860801280625 

noncomputable def Ns588p234 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600 

noncomputable def Ns588p235 := BSN.cos_dyadic_bound_t 130794403 67108864 4 3 33554432 10890000 Ns588p230 Ns588p231 Ns588p232 Ns588p233 Ns588p234 Ns588p232 12389672 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 130794403) (BSN.cosEvenQ 67108864) 0 3 Ns588p230 Ns588p231 Ns588p232 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 130794403) (BSN.cosOddQ 67108864) 0 3 Ns588p233 Ns588p234 Ns588p232 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz388 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns588p236 := @Ns588p219 363564304 45675970560000 1548709 4194304 22722769 2854748160000 (@Ns588p220 33 4194304 Bool.true 12389672 33554432 1 10890000 (@Ns588p224 Ns588p225 130794403 67108864 33 4194304 (@Ns588p226 281474976710656 43958435 35184372088832 Ns588p221 Ns588p222 Ns588p223 Ns588p225 RS589to600.d55 (@Ns588p227 0 1 1396976761002736 87311047562671 281474976710656 43958435 35184372088832 (@Ns588p228 1169688398965852078080 69718861518255 281474976710656 43958435 35184372088832 (@Ns588p229 22986915 35184372088832 (Ns588p209 rfl rfl) (Ns588p209 rfl rfl) rfl) (Ns588p209 rfl rfl) rfl rfl) qz388 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 130794403 67108864) (BSN.cos_neg_of_bound 130794403 67108864 Bool.true 12389672 33554432 1 10890000 (Ns588p235 rfl rfl)) rfl rfl) 

noncomputable abbrev qz33 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 12) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 12 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns588p237 := @Ns588p193 9024302669329796217091 Ns588p86 (Ns588p194 qz33 (@Enclosure.Real.IsNear.of_eq qz599 (@Inv.inv Real Real.instInv qz23) Bool.false 4736219 16777216 1 33554432 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 989310 1000 qz11)) Ns588p198) rfl) (@Ns588p199 281474976710656 1897559381600413 191578906023690240000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 989310 1000 12 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 989310 1000 12 qz11 rfl rfl rfl))) (@Ns588p200 67108864 1548709 4194304 22722769 2854748160000 108855607084603 281474976710656 1897559381600413 191578906023690240000 Ns588p218 (Ns588p236 rfl) rfl)) 

noncomputable abbrev qz34 := qz359

noncomputable def Ns588p238 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 9881569288893253501049 4722366482869645213696 Ns588p85 Ns588p86 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HMul.hMul Real Real Real qz5 qz591 (Zeta.RiemannSiegel.correction qz10))) Bool.true 9881569288893253501049 4722366482869645213696 Ns588p85 Ns588p86 (BSN.hardyZApproximantRS₀_eq qz4 12 (@BSN.floor_sqrt_eq_dec qz4 989310 1000 12 qz11 rfl rfl rfl)) (@Ns588p88 9881569288893253501049 4722366482869645213696 Ns588p85 Ns588p86 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12)) Bool.true 266197881 134217728 255895 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (Ns588p192 (Ns588p191 rfl rfl rfl rfl) rfl rfl)) (Ns588p237 rfl) rfl rfl)) 

theorem RS589to600.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 9881569288893253501049 4722366482869645213696 Ns588p85 Ns588p86 := Ns588p238 

theorem RS589to600.d58 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS589to600.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS589to600.d3 a b h)) 

noncomputable def Ns588p239 := nat_lit 142851586106806767714304000 

noncomputable def Ns588p240 := nat_lit 3318561340053387532730609172480 

noncomputable abbrev qz748 := (Enclosure.sfrac Bool.false 990552 1000)

noncomputable abbrev qz604 := qz748

noncomputable abbrev qz389 := qz604

noncomputable abbrev qz35 := qz389

noncomputable abbrev qz749 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 990552 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz605 := qz749

noncomputable abbrev qz390 := qz605

noncomputable abbrev qz36 := qz390

noncomputable abbrev qz750 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 990552 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz606 := qz750

noncomputable abbrev qz391 := qz606

noncomputable abbrev qz37 := qz391

noncomputable abbrev qz607 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz36 qz9))

noncomputable def Ns588p241 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HMul.hMul Real Real Real qz5 qz607 (Zeta.RiemannSiegel.correction qz37)) 380772765 268435456 256219 268435456 1034646280101732732525 9444732965739290427392 409713647946360964131 Ns588p239 Ns588p240 

noncomputable def Ns588p242 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos BSN.quadSignNeg 11 12 990552 1000 286 536870912 268435456 9007199254740992 Bool.false 1079442701399 4511 1334074092 51 154981288 8 

noncomputable def Ns588p243 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 990552 1000 172 232 536870912 268435456 9007199254740992 Bool.false 1079442701399 4511 

noncomputable def Ns588p244 := Ns588p243 1236190956 51 169773496 8 1287360220 51 161872664 8 Bool.false 53585866 206310 Bool.true 18567125 Bool.true 105492526 28296951008113761 1 Bool.false 536549881 Bool.false Bool.false 526539832 Bool.false Bool.false 382015569 

noncomputable def Ns588p245 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 990552 1000 31 105 536870912 268435456 9007199254740992 Bool.false 1079442701399 4511 

noncomputable def Ns588p246 := Ns588p245 1116391676 51 189812536 8 1179625948 51 178956968 8 Bool.false 107267998 168492 Bool.true 258545493 Bool.true 490080708 28296951008113761 1 Bool.false 248667186 Bool.false Bool.false 424797787 Bool.true Bool.false 53585866 

noncomputable def Ns588p247 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 990552 1000 150 52 536870912 268435456 9007199254740992 Bool.false 1079442701399 4511 

noncomputable def Ns588p248 := Ns588p247 961943533 51 219176632 8 1044702541 51 202918136 8 Bool.false 291286888 125208 Bool.false 90382418 Bool.false 758137466 28296951008113761 1 Bool.false 529280906 Bool.true Bool.false 84820499 Bool.false Bool.false 107267998 

noncomputable def Ns588p249 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 990552 1000 405 265 536870912 268435456 9007199254740992 Bool.false 1079442701399 4511 

noncomputable def Ns588p250 := Ns588p249 744261104 50 268435448 8 864060384 50 240095976 8 Bool.false 576109458 74002 Bool.false 670859413 Bool.false 67522925 28296951008113761 1 Bool.false 509409911 Bool.true Bool.false 67345048 Bool.true Bool.false 291286888 

noncomputable def Ns588p251 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 990552 1000 842 587 536870912 268435456 9007199254740992 Bool.false 1079442701399 4511 

noncomputable def Ns588p252 := Ns588p251 372130544 50 379625064 8 589812976 50 309962568 8 Bool.false 536870816 4570 Bool.false 756937578 Bool.false 176457611 28296951008113761 1 Bool.false 86005105 Bool.true Bool.false 173297632 Bool.false Bool.false 576109458 

noncomputable def Ns588p253 := nat_lit 1044151599139795863972722169176068976604292208734592089 

noncomputable def Ns588p254 := nat_lit 519318552591496949454897939275800291528914501632000 

noncomputable def Ns588p255 := nat_lit 2230272000000000000000000 

noncomputable def Ns588p256 := nat_lit 457749536941240577144830485135360000 

noncomputable def Ns588p257 := nat_lit 2720548639378669057678245854029782712320 

noncomputable abbrev qz608 := (@Eq.refl Real qz748)

noncomputable abbrev qz392 := qz608

noncomputable abbrev qz38 := qz392

noncomputable def Ns588p258 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz35 990552 1000 3924774058816 16000000 1981104 4000 2000 Ns588p256 Ns588p257 qz38 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns588p259 := nat_lit 12317313456220619113436937614242114161133000954493440886046720 

noncomputable abbrev qz609 := (@HSub.hSub Real Real Real qz743 qz744 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz745 (@Nat.cast Real Real.instNatCast 1981104))))

noncomputable abbrev qz393 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 990552 4000) (Real.log (Enclosure.sfrac Bool.false 3924774058816 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz609))

noncomputable abbrev qz610 := (Enclosure.sfrac Bool.false 990552 2000)

noncomputable abbrev qz39 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz393 qz610) (@HMul.hMul Real Real Real qz355 qz610 (Real.log Real.pi)))

noncomputable def Ns588p260 := @Enclosure.Real.IsNear.addLit_ft_p qz39 (Enclosure.sfrac Bool.true Ns588p256 Ns588p257) 4527511219131896838421 2251799813685248000 18735611360523020237 Ns588p255 Ns588p256 Ns588p257 0 1 Ns588p259 

noncomputable def Ns588p261 := nat_lit 1519180673315983314958124318720 

noncomputable abbrev qz40 := (@HSub.hSub Real Real Real qz359 qz393 qz610)

noncomputable def Ns588p262 := @Enclosure.Real.IsNear.subLit_ff_p qz40 (@HMul.hMul Real Real Real qz5 qz610 (Real.log Real.pi)) 232167416815767236701 90071992547409920 3120479584658419 1089000000000000000000 4755982016259 8388608000 371457 67108864000 Ns588p261 4527511219131896838421 2251799813685248000 

noncomputable def Ns588p263 := nat_lit 11608370840788361835050000 

noncomputable abbrev qz41 := qz393

noncomputable def Ns588p264 := @Enclosure.Real.IsNear.subLit_ff_p qz41 qz610 6919447824916955805973 2251799813685248000 3120479584658419 1089000000000000000000 990552 2000 0 1 Ns588p263 232167416815767236701 90071992547409920 3120479584658419 1089000000000000000000 

noncomputable def Ns588p265 := nat_lit 15581211322952795607547959815180386304 

noncomputable def Ns588p266 := nat_lit 120024385782597279983599616 

noncomputable def Ns588p267 := nat_lit 103056342436060149245128054745675726360738656618274026895700104615368281668009431901662587770988555425582645890642319595723945502435587876838870345999362450024487820196969413384543710323756217813250765342166220800 

noncomputable def Ns588p268 := nat_lit 3351401772567899010932997744812475541262516156674857794603955430652823939097282590226276095637877751533321219664243188933598363356151681292203359080393752789854161556092353475954346686255656671596838113907834880 

noncomputable def Ns588p269 := nat_lit 31408078261141927469513709989760410761526888501748210305189488708982148769855961913263615245323185691246975650020338758723538947219416887905753062617706355762482655372320341269453778119754604045821542400 

noncomputable def Ns588p270 := BSN.log_dyadic_bound 1827622058816 6021926058816 9 8 Ns588p267 268435456 87120000 Ns588p268 Ns588p269 168236164 7849548117632 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1827622058816) (BSN.artanhQ 6021926058816) 0 8 Ns588p268 Ns588p267 Ns588p269 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz394 := (Real.log (Enclosure.sfrac Bool.false 3924774058816 16000000))

noncomputable def Ns588p271 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 990552 4000) qz394 990552 4000 0 1 55890709991844967 4503599627370496 12500018513 1089000000000000000 6920331820480251968973 2251799813685248000 515913264087049 181500000000000000000 (Enclosure.Real.IsNear.const Bool.false 990552 4000) (BSN.isNear_log_sfrac 3924774058816 16000000 55890709991844967 4503599627370496 12500018513 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3924774058816) qz362)) Bool.false Ns588p266 Ns588p114 1000001481040000 87120000000000000000000 55890709991844967 4503599627370496 12500018513 1089000000000000000 (BSN.log_rat_reduce_isNear 3924774058816 16000000 17 7849548117632 4194304000000 168236164 268435456 24973259072661432 36028797018963968 87120000 1000000000000000 rfl rfl rfl rfl (Ns588p270 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p272 := BSN.arctan_dyadic_bound_f 1000 1981104 1 0 33554432 10890000 0 1 1 0 1 1 16937 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1981104) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1981104) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns588p273 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1981104))) 884279719003555 562949953421312 1 2000000000000000 16937 33554432 1 10890000 29661969016922797244416 883995563296163 562949953421312 200000001089 2178000000000000000 qz17 (Ns588p272 rfl) rfl rfl 

noncomputable abbrev qz395 := (@HMul.hMul Real Real Real qz588 qz593 qz609)

noncomputable abbrev qz42 := qz395

noncomputable abbrev qz396 := qz609

noncomputable abbrev qz43 := qz396

noncomputable def Ns588p274 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 990552 4000) qz394) qz42 6920331820480251968973 2251799813685248000 515913264087049 181500000000000000000 883995563296163 2251799813685248 200000001089 8712000000000000000 Ns588p265 6919447824916955805973 2251799813685248000 3120479584658419 1089000000000000000000 (Ns588p271 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz43 1 4 0 1 883995563296163 562949953421312 200000001089 2178000000000000000 883995563296163 2251799813685248 200000001089 8712000000000000000 qz369 Ns588p273 rfl) 

noncomputable def Ns588p275 := @Ns588p260 Ns588p253 Ns588p254 18735611360523020237 Ns588p255 (@Ns588p262 18735611360523020237 Ns588p255 (Ns588p264 (Ns588p274 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 990552 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz610 (Real.log Real.pi) 990552 2000 0 1 38410761 33554432 3 268435456 4755982016259 8388608000 371457 67108864000 (Enclosure.Real.IsNear.const Bool.false 990552 2000) RS589to600.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns588p256 Ns588p257) 

noncomputable def Ns588p276 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns588p253 Ns588p254 18735611360523020237 Ns588p255 67465168837 33554432 565 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz370 qz39 (Enclosure.sfrac Bool.true Ns588p256 Ns588p257)) Bool.false Ns588p253 Ns588p254 18735611360523020237 Ns588p255 Ns588p258 (Ns588p275 rfl rfl)) 

noncomputable def Ns588p277 := nat_lit 7593067951871856815898624 

noncomputable def Ns588p278 := nat_lit 4835703278458516698824704 

noncomputable def Ns588p279 := nat_lit 14358867352480184647282266133104864638079384174397735040767569513677095342667755171663700744884672671853294391867133936608678337336561601427281 

noncomputable def Ns588p280 := nat_lit 10204924106397286488452219219556765988502099688420434558038963620360688396268659939592160824251428262668475641880996435725984378306246481 

noncomputable def Ns588p281 := nat_lit 71705256439848709723068122337819124860550477122629121121383225228748283325945909595064281690938007013715858887930841605652248634640419920623441 

noncomputable def Ns588p282 := BSN.sin_dyadic_bound_f 215807971013 137438953472 4 3 67108864 21801270 Ns588p279 Ns588p127 Ns588p280 Ns588p281 Ns588p130 Ns588p280 67108852 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215807971013) (BSN.sinEvenQ 137438953472) 0 3 Ns588p279 Ns588p127 Ns588p280 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215807971013) (BSN.sinOddQ 137438953472) 0 3 Ns588p281 Ns588p130 Ns588p280 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz397 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable abbrev qz611 := (@Nat.cast Real Real.instNatCast Ns588p278)

noncomputable def Ns588p283 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz35) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 67465168837) qz397) Bool.false 67465168837 33554432 565 67108864 Bool.false 67108852 67108864 1 10890000 (Ns588p276 rfl) (Enclosure.sfrac_false_div 67465168837 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 67465168837) qz397) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns588p277) qz611) 226375608064910080 72057594037927936 Bool.false 67108852 67108864 319 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q3 67465168837 33554432 226375608064910080 72057594037927936 319 Ns588p277 Ns588p278 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108852 67108864 Ns588p277 Ns588p278 215807971013 137438953472 21801270 21780000 (Ns588p282 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p284 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns588p253 Ns588p254 18735611360523020237 Ns588p255 1079442701399 536870912 4511 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz370 qz39 (Enclosure.sfrac Bool.true Ns588p256 Ns588p257)) Bool.false Ns588p253 Ns588p254 18735611360523020237 Ns588p255 Ns588p258 (Ns588p275 rfl rfl)) 

noncomputable def Ns588p285 := Ns588p252 74002 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 842 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 86005105 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 587 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 173297632 536870912) qz38 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) Bool.false 16777213 16777216 388747429 45675970560000 536870816 536870912 4570 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 16777213 16777216 388747429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz35) qz35) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 67108852 67108864 6219958864 730815528960000 16777213 16777216 388747429 45675970560000 (Ns588p283 rfl rfl) rfl)) rfl) (Ns588p284 rfl) RS589to600.d7 

noncomputable def Ns588p286 := nat_lit 45325814264008382688423455297512916622968434895884537393814343423354216827916863536712809105891627899614398058496 

noncomputable def Ns588p287 := nat_lit 35376983148727244606016955571073594019915247909209367459227743042375765116837037131460045953557848781295616 

noncomputable def Ns588p288 := nat_lit 274546262023978725663173545962451476775431976906175675568697977714324139981489634515874866589891976433035153838080 

noncomputable def Ns588p289 := BSN.cos_dyadic_bound_f 756937578 536870912 4 3 536870912 268435456 Ns588p286 Ns588p146 Ns588p287 Ns588p288 Ns588p149 Ns588p287 86005105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 756937578) qz375 0 3 Ns588p286 Ns588p146 Ns588p287 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 756937578) qz376 0 3 Ns588p288 Ns588p149 Ns588p287 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p290 := nat_lit 969530733875987198725153978037041 

noncomputable def Ns588p291 := BSN.sin_dyadic_bound_f 176457611 536870912 2 1 536870912 268435456 Ns588p290 Ns588p188 Ns588p290 Ns588p290 Ns588p189 Ns588p290 173297632 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 176457611) qz373 0 1 Ns588p290 Ns588p188 Ns588p290 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 176457611) qz374 0 1 Ns588p290 Ns588p189 Ns588p290 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p292 := nat_lit 72599593727727861999686773789008657210408715155459648276036351986546772501747669971841263981168885903393019736081 

noncomputable def Ns588p293 := nat_lit 8309563562094450782812444503106062181263824953792059004510928696850253823607891954383737384349099874136081 

noncomputable def Ns588p294 := nat_lit 362817161738614942632467396231054070550639641910667608862626532600660155108257341149658825243947696435228573773841 

noncomputable def Ns588p295 := BSN.sin_dyadic_bound_f 670859413 536870912 4 3 536870912 268435456 Ns588p292 Ns588p172 Ns588p293 Ns588p294 Ns588p175 Ns588p293 509409911 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 670859413) qz373 0 3 Ns588p292 Ns588p172 Ns588p293 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 670859413) qz374 0 3 Ns588p294 Ns588p175 Ns588p293 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p296 := nat_lit 20787630481567732576058719140625 

noncomputable def Ns588p297 := BSN.sin_dyadic_bound_f 67522925 536870912 2 1 536870912 268435456 Ns588p296 Ns588p188 Ns588p296 Ns588p296 Ns588p189 Ns588p296 67345048 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 67522925) qz373 0 1 Ns588p296 Ns588p188 Ns588p296 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 67522925) qz374 0 1 Ns588p296 Ns588p189 Ns588p296 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p298 := Ns588p250 125208 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 405 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 509409911 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 265 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67345048 536870912) qz38 rfl rfl (Ns588p285 RS589to600.d9 RS589to600.d11 RS589to600.d13 RS589to600.d17 (Ns588p289 rfl rfl) (Ns588p291 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns588p284 rfl) RS589to600.d19 RS589to600.d21 RS589to600.d23 RS589to600.d25 RS589to600.d17 (Ns588p295 rfl rfl) (Ns588p297 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns588p299 := nat_lit 66732258478202476494580822172176 

noncomputable def Ns588p300 := BSN.cos_dyadic_bound_f 90382418 536870912 2 1 536870912 268435456 Ns588p299 Ns588p142 Ns588p299 Ns588p299 Ns588p143 Ns588p299 529280906 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 90382418) qz375 0 1 Ns588p299 Ns588p142 Ns588p299 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 90382418) qz376 0 1 Ns588p299 Ns588p143 Ns588p299 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p301 := nat_lit 45614578775066971919311721463024835209145774761773113090783372714450168005428224655094649808017256109791616372736 

noncomputable def Ns588p302 := nat_lit 36055831220450347422111034558663909728691237769220977189510871066066591314872858617578439976688805395501056 

noncomputable def Ns588p303 := nat_lit 276292611115217177824370145802951157118010073138437786367121755084103823445199562633388918644230509459128739368960 

noncomputable def Ns588p304 := BSN.cos_dyadic_bound_f 758137466 536870912 4 3 536870912 268435456 Ns588p301 Ns588p146 Ns588p302 Ns588p303 Ns588p149 Ns588p302 84820499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 758137466) qz375 0 3 Ns588p301 Ns588p146 Ns588p302 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 758137466) qz376 0 3 Ns588p303 Ns588p149 Ns588p302 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p305 := Ns588p248 168492 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 150 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 529280906 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 84820499 536870912) qz38 rfl rfl (Ns588p298 rfl rfl) (Ns588p284 rfl) RS589to600.d27 RS589to600.d29 RS589to600.d31 RS589to600.d33 RS589to600.d17 (Ns588p300 rfl rfl) (Ns588p304 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p306 := nat_lit 1122578949910472007482581297780692112485267215535099672589243930075847265 

noncomputable def Ns588p307 := nat_lit 19966216314100811605581895322268064127922835314151250509210895112801 

noncomputable def Ns588p308 := nat_lit 2940055399701013380187970552071290908214730832287133373804338237320845921 

noncomputable def Ns588p309 := BSN.sin_dyadic_bound_f 258545493 536870912 3 2 536870912 268435456 Ns588p306 Ns588p136 Ns588p307 Ns588p308 Ns588p139 Ns588p307 248667186 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 258545493) qz373 0 2 Ns588p306 Ns588p136 Ns588p307 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 258545493) qz374 0 2 Ns588p308 Ns588p139 Ns588p307 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p310 := nat_lit 14495440661770843869351464222727307034848990728880012365234174794582261760 

noncomputable def Ns588p311 := nat_lit 3327674624468240803729245379240953011852292565229113774946807321788416 

noncomputable def Ns588p312 := nat_lit 37958861688579261553666844662243223548299595816246804296168162964432551936 

noncomputable def Ns588p313 := BSN.sin_dyadic_bound_f 490080708 536870912 3 2 536870912 268435456 Ns588p310 Ns588p136 Ns588p311 Ns588p312 Ns588p139 Ns588p311 424797787 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 490080708) qz373 0 2 Ns588p310 Ns588p136 Ns588p311 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 490080708) qz374 0 2 Ns588p312 Ns588p139 Ns588p311 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p314 := Ns588p246 206310 BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 248667186 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 424797787 536870912) qz38 rfl rfl (Ns588p305 rfl) (Ns588p284 rfl) RS589to600.d35 RS589to600.d37 RS589to600.d39 RS589to600.d41 RS589to600.d17 (Ns588p309 rfl rfl) (Ns588p313 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p315 := nat_lit 118844378803777162148681640625 

noncomputable def Ns588p316 := BSN.cos_dyadic_bound_f 18567125 536870912 2 1 536870912 268435456 Ns588p315 Ns588p142 Ns588p315 Ns588p315 Ns588p143 Ns588p315 536549881 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 18567125) qz375 0 1 Ns588p315 Ns588p142 Ns588p315 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 18567125) qz376 0 1 Ns588p315 Ns588p143 Ns588p315 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p317 := nat_lit 123847363672636551278212195176976 

noncomputable def Ns588p318 := BSN.cos_dyadic_bound_f 105492526 536870912 2 1 536870912 268435456 Ns588p317 Ns588p142 Ns588p317 Ns588p317 Ns588p143 Ns588p317 526539832 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 105492526) qz375 0 1 Ns588p317 Ns588p142 Ns588p317 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 105492526) qz376 0 1 Ns588p317 Ns588p143 Ns588p317 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p319 := Ns588p244 240323 BSN.abs_quadSignPos (BSN.cos_quad_nat0 172 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536549881 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 232 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 526539832 536870912) qz38 rfl rfl (Ns588p314 rfl) (Ns588p284 rfl) RS589to600.d43 RS589to600.d45 RS589to600.d47 RS589to600.d49 RS589to600.d17 (Ns588p316 rfl rfl) (Ns588p318 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p320 := nat_lit 68500292390257851107747738014191553877203483230877084616425878488357936106521968300684860556205365339077175616401 

noncomputable def Ns588p321 := nat_lit 121675525143535449780480338819558446449615062968864306561929804389779964912554642541410982369836355009323921 

noncomputable def Ns588p322 := nat_lit 414587679080891146392424672301567341990751478285706502993704419015910253937299092783234997294107420227581643006865 

noncomputable def Ns588p323 := BSN.cos_dyadic_bound_f 839009611 536870912 4 3 536870912 268435456 Ns588p320 Ns588p146 Ns588p321 Ns588p322 Ns588p149 Ns588p321 4305199 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 839009611) qz375 0 3 Ns588p320 Ns588p146 Ns588p321 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 839009611) qz376 0 3 Ns588p322 Ns588p149 Ns588p321 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz398 := (BSN.cos_quad_nat2 286 rfl)

noncomputable def Ns588p324 := Ns588p242 Bool.false 382015569 240323 Bool.true 839009611 28296951008113761 1 Bool.false 4305199 Bool.true Bool.false 380772765 256219 BSN.abs_quadSignNeg qz398 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 4305199 536870912) qz38 rfl (Ns588p319 rfl) (Ns588p284 rfl) RS589to600.d51 RS589to600.d53 RS589to600.d17 (Ns588p323 rfl rfl) rfl 

noncomputable def Ns588p325 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) 380772765 536870912 256219 536870912 380772765 536870912 256219 536870912 408851643220623360 380772765 268435456 256219 268435456 (Ns588p324 rfl rfl rfl rfl) 

noncomputable def Ns588p326 := @Enclosure.Real.IsNear.mulLit_ff qz607 (Zeta.RiemannSiegel.correction qz37) 9469467 33554432 1 33554432 109261300567575 281474976710656 2693268188187 266081813921792000 1034646280101732732525 9444732965739290427392 

noncomputable abbrev qz612 := (@HPow.hPow Real Real Real qz7 qz36 qz9)

noncomputable def Ns588p327 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz612 1 1 0 1 9469467 33554432 1 33554432 9469467 33554432 1 33554432 

noncomputable def Ns588p328 := @Enclosure.Real.IsNear.sqrt_image qz36 1322474460033 8388608000 123819 8388608000 421306896 421306936 33554432 (@Enclosure.Real.IsNear.of_eq qz36 (@HMul.hMul Real Real Real qz5 qz35 qz3) Bool.false 1322474460033 8388608000 123819 8388608000 (BSN.t_div_two_pi_mk qz35 990552 1000 qz38) (@Enclosure.Real.IsNear.mulLit_ff qz35 qz3 990552 1000 0 1 10680707 67108864 1 67108864 1322474460033 8388608000 123819 8388608000 (Enclosure.Real.IsNear.const Bool.false 990552 1000) RS589to600.d56 rfl)) 

noncomputable abbrev qz751 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 990552 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz613 := qz751

noncomputable abbrev qz399 := qz613

noncomputable abbrev qz44 := qz399

noncomputable def Ns588p329 := @Enclosure.Real.IsNear.sqrt_image qz44 105326729 8388608 5 8388608 118897912 118897919 33554432 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 842613832 67108864 40 67108864 105326729 8388608 5 8388608 (Ns588p328 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns588p330 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz44) 237795831 67108864 7 67108864 9469466 9469468 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz44) Bool.false 237795831 67108864 7 67108864 237795831 67108864 7 67108864 (Ns588p329 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns588p331 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 18938934 67108864 2 67108864 9469467 33554432 1 33554432 (Ns588p330 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz588 qz586 qz606)

noncomputable abbrev qz45 := (Real.cos qz400)

noncomputable abbrev qz614 := (@HMul.hMul Real Real Real qz739 qz750 qz750)

noncomputable abbrev qz401 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz614 qz606) qz603)

noncomputable abbrev qz46 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz401))

noncomputable def Ns588p332 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz37) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz45) qz46) Bool.false 109261300567575 

noncomputable def Ns588p333 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz45) qz46 35738133 33554432 147 

noncomputable abbrev qz47 := (@Neg.neg Real Real.instNeg (Real.cos qz400))

noncomputable def Ns588p334 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz45) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz47)) Bool.true 35738133 33554432 147 33554432 (BSN.inv_eq_neg_inv_neg qz45) 

noncomputable def Ns588p335 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz47) Bool.false 71476266 67108864 294 67108864 35738133 33554432 

noncomputable def Ns588p336 := @Enclosure.Real.IsNear.recentre' qz45 Bool.true 63008322 67108864 702847216 182703882240000 31504161 33554432 43927951 11418992640000 

noncomputable abbrev qz48 := qz400

noncomputable def Ns588p337 := @Enclosure.Real.IsNear.cos_image qz48 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 234409709) qz371) Bool.false 234409709 67108864 63 16777216 Bool.true 63008322 67108864 1 

noncomputable def Ns588p338 := nat_lit 134930377085278811720019171 

noncomputable def Ns588p339 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz37 884279719003555 140737488355328 1 500000000000000 4663433 8388608 5 8388608 4123779222831905504315 1180591620717411303424 Ns588p338 

noncomputable def Ns588p340 := @Enclosure.Real.IsNear.subLit_ff_p qz44 qz1 105326729 8388608 5 8388608 12 1 0 1 4663433 4663433 8388608 5 

noncomputable def Ns588p341 := @Ns588p340 8388608 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 842613832 67108864 40 67108864 105326729 8388608 5 8388608 (Ns588p328 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns588p342 := @Enclosure.Real.IsNear.recentre' qz48 Bool.false 4123779222831905504315 1180591620717411303424 Ns588p338 Ns588p206 234409709 67108864 63 16777216 (@Ns588p339 Ns588p206 RS589to600.d55 (Ns588p341 rfl rfl) rfl) 

noncomputable def Ns588p343 := nat_lit 3398379510250937419563008 

noncomputable def Ns588p344 := nat_lit 5439616772293350374115534605495264742058561 

noncomputable def Ns588p345 := BSN.cos_dyadic_bound_f 48293877487 137438953472 2 1 67108864 21801270 Ns588p344 Ns588p213 Ns588p344 Ns588p344 Ns588p214 Ns588p344 63008322 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 48293877487) qz383 0 1 Ns588p344 Ns588p213 Ns588p344 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 48293877487) qz384 0 1 Ns588p344 Ns588p214 Ns588p344 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p346 := @Ns588p337 10890000 (Ns588p342 rfl) (Enclosure.sfrac_false_div 234409709 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 234409709) qz371) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns588p343) qz372) 226375608064910080 72057594037927936 Bool.false 63008322 67108864 0 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 234409709 67108864 226375608064910080 72057594037927936 0 Ns588p343 Ns588p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 63008322 67108864 Ns588p343 Ns588p114 48293877487 137438953472 21801270 21780000 (Ns588p345 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p347 := @Enclosure.Real.IsNear.inv_image qz47 31504161 33554432 43927951 11418992640000 35737986 35738280 33554432 (@Enclosure.Real.IsNear.neg qz45 Bool.true 31504161 33554432 43927951 11418992640000 (Ns588p336 (Ns588p346 rfl rfl) rfl)) 

noncomputable def Ns588p348 := Ns588p334 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz47) Bool.false 35738133 33554432 147 33554432 (@Ns588p335 147 33554432 (Ns588p347 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p349 := @Enclosure.Real.IsNear.recentre' qz46 Bool.true 12229100 33554432 

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz355 qz352 qz401)

noncomputable def Ns588p350 := @Enclosure.Real.IsNear.cos_image qz49 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65224595)) qz397) Bool.true 65224595 33554432 

noncomputable def Ns588p351 := nat_lit 19250902599416454142159604845 

noncomputable def Ns588p352 := nat_lit 9903520314283042199192993792 

noncomputable def Ns588p353 := nat_lit 2390356261193685155850240675519333 

noncomputable def Ns588p354 := @Enclosure.Real.IsNear.recentre' qz49 Bool.true Ns588p351 Ns588p352 Ns588p353 

noncomputable def Ns588p355 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz50 := qz401

noncomputable def Ns588p356 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz50 884279719003555 140737488355328 1 500000000000000 21770150536879 

noncomputable abbrev qz402 := (@HSub.hSub Real Real Real qz592 qz614 qz606)

noncomputable abbrev qz51 := qz402

noncomputable def Ns588p357 := @Enclosure.Real.IsNear.subLit_tf qz51 qz31 17372104025775 70368744177664 88577395 70368744177664 1 16 

noncomputable abbrev qz403 := qz614

noncomputable abbrev qz52 := qz403

noncomputable def Ns588p358 := @Enclosure.Real.IsNear.subLit_ff_n qz52 qz37 21747607345489 70368744177664 46634355 70368744177664 4663433 8388608 5 8388608 

noncomputable def Ns588p359 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz37 4663433 8388608 5 8388608 4663433 8388608 5 8388608 21747607345489 70368744177664 

noncomputable def Ns588p360 := nat_lit 585396373280502376849475874950638419979144399882069840201471733408640227691130233938240049935640625 

noncomputable def Ns588p361 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600 

noncomputable def Ns588p362 := nat_lit 5928389007331271079636088788862338222571866978470555567933587855197457056506584014492431640625 

noncomputable def Ns588p363 := nat_lit 3531423565769993883656596192012741582928109987364152179868889544113415971397663071927194168489240625 

noncomputable def Ns588p364 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600 

noncomputable def Ns588p365 := BSN.cos_dyadic_bound_t 65224595 33554432 4 3 33554432 10890000 Ns588p360 Ns588p361 Ns588p362 Ns588p363 Ns588p364 Ns588p362 12229100 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65224595) (BSN.cosEvenQ 33554432) 0 3 Ns588p360 Ns588p361 Ns588p362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65224595) (BSN.cosOddQ 33554432) 0 3 Ns588p363 Ns588p364 Ns588p362 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p366 := @Ns588p349 5849698864 730815528960000 3057275 8388608 365606179 45675970560000 (@Ns588p350 531 67108864 Bool.true 12229100 33554432 1 10890000 (@Ns588p354 Ns588p355 65224595 33554432 531 67108864 (@Ns588p356 70368744177664 88577395 70368744177664 Ns588p351 Ns588p352 Ns588p353 Ns588p355 RS589to600.d55 (@Ns588p357 0 1 348322408590064 21770150536879 70368744177664 88577395 70368744177664 (@Ns588p358 145727770807448371200 17372104025775 70368744177664 88577395 70368744177664 (@Ns588p359 46634355 70368744177664 (Ns588p341 rfl rfl) (Ns588p341 rfl rfl) rfl) (Ns588p341 rfl rfl) rfl rfl) qz388 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65224595 33554432) (BSN.cos_neg_of_bound 65224595 33554432 Bool.true 12229100 33554432 1 10890000 (Ns588p365 rfl rfl)) rfl rfl) 

noncomputable def Ns588p367 := @Ns588p326 409713647946360964131 Ns588p239 (Ns588p327 qz33 (@Enclosure.Real.IsNear.of_eq qz612 (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 9469467 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz36 (BSN.t_div_two_pi_nonneg qz35 990552 1000 qz38)) Ns588p331) rfl) (@Ns588p332 281474976710656 2693268188187 266081813921792000 (BSN.correction_mk qz37 (BSN.cos_two_pi_p_ne_zero_mk qz35 990552 1000 12 qz38 rfl rfl (@BSN.floor_sqrt_eq_dec qz35 990552 1000 12 qz38 rfl rfl rfl))) (@Ns588p333 33554432 3057275 8388608 365606179 45675970560000 109261300567575 281474976710656 2693268188187 266081813921792000 Ns588p348 (Ns588p366 rfl) rfl)) 

noncomputable def Ns588p368 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (hardyZApproximantRS₀ qz35) Bool.false 12362604364951653527955 9444732965739290427392 136760146210401609860131 Ns588p239 (@Eq.refl Real (hardyZApproximantRS₀ qz35)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HMul.hMul Real Real Real qz5 qz607 (Zeta.RiemannSiegel.correction qz37))) Bool.false 12362604364951653527955 9444732965739290427392 136760146210401609860131 Ns588p239 (BSN.hardyZApproximantRS₀_eq qz35 12 (@BSN.floor_sqrt_eq_dec qz35 990552 1000 12 qz38 rfl rfl rfl)) (@Ns588p241 12362604364951653527955 9444732965739290427392 136760146210401609860131 Ns588p239 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12)) Bool.false 380772765 268435456 256219 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (Ns588p325 (Ns588p324 rfl rfl rfl rfl) rfl rfl)) (Ns588p367 rfl) rfl rfl)) 

theorem RS589to600.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz35) Bool.false 12362604364951653527955 9444732965739290427392 136760146210401609860131 Ns588p239 := Ns588p368 

noncomputable abbrev qz615 := (@HMul.hMul Real Real Real qz739 (Real.sqrt qz747) qz741)

noncomputable abbrev qz404 := qz615

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv qz404)

noncomputable abbrev qz405 := (@HMul.hMul Real Real Real qz588 (@HMul.hMul Real Real Real qz588 qz615 qz615) qz615)

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz355 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz405))

noncomputable abbrev qz406 := (@HMul.hMul Real Real Real qz588 qz601 qz601)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz355 qz406 qz378))

noncomputable abbrev qz616 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz53)

noncomputable def Ns588p369 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz370 (@HAdd.hAdd Real Real Real qz370 qz616 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55)) Bool.false 

noncomputable def Ns588p370 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz370 qz616 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55) 24064201 2147483648 

noncomputable def Ns588p371 := @Enclosure.Real.IsNear.addLit_ff qz616 qz54 3008025 268435456 25 268435456 

noncomputable def Ns588p372 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz53 25 4 0 1 120321 67108864 1 67108864 3008025 

noncomputable def Ns588p373 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 120321 67108864 1 67108864 120321 67108864 1 67108864 

noncomputable def Ns588p374 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz8 29715157 8388608 3 33554432 1056653024217 6710886400 98931 6710886400 31398610509132957069 56294995342131200 466530004941 

noncomputable def Ns588p375 := @Enclosure.Real.IsNear.sqrt_image qz8 1056653024217 6710886400 98931 6710886400 421042686 421042726 33554432 qz21 

noncomputable def Ns588p376 := @Enclosure.Real.IsNear.sqrt_image qz22 210521353 16777216 5 8388608 118860625 118860631 33554432 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 842085412 67108864 40 67108864 210521353 16777216 5 8388608 (Ns588p375 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz407 := (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 237721256 67108864 6 67108864 29715157 8388608 3 33554432 (Ns588p376 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns588p377 := @Ns588p374 7036874417766400 qz407 

noncomputable def Ns588p378 := Ns588p377 qz21 

noncomputable abbrev qz56 := qz404

noncomputable def Ns588p379 := @Enclosure.Real.IsNear.inv_image qz56 31398610509132957069 56294995342131200 466530004941 7036874417766400 60160 60161 33554432 (Ns588p378 rfl) rfl rfl 

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv qz405)

noncomputable def Ns588p380 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz57 1 32 0 1 1 

noncomputable def Ns588p381 := @Enclosure.Real.IsNear.recentre' qz57 Bool.false 1 67108864 1 67108864 

noncomputable def Ns588p382 := nat_lit 30955034234622023102176740470429164363042569611155768159509 

noncomputable def Ns588p383 := nat_lit 178405961588244985132285746181186892047843328000000 

noncomputable def Ns588p384 := nat_lit 1379817809469312682439196108220559829174998686838583 

noncomputable def Ns588p385 := nat_lit 22300745198530623141535718272648361505980416000000 

noncomputable abbrev qz58 := qz405

noncomputable def Ns588p386 := @Enclosure.Real.IsNear.inv_image qz58 Ns588p382 Ns588p383 Ns588p384 Ns588p385 0 1 

noncomputable def Ns588p387 := nat_lit 985872741904234573528916153824197070761 

noncomputable def Ns588p388 := nat_lit 3169126500570573503741758013440000 

noncomputable def Ns588p389 := nat_lit 14648394786567315028024448531853 

noncomputable def Ns588p390 := nat_lit 198070406285660843983859875840000 

noncomputable abbrev qz408 := (@HMul.hMul Real Real Real qz588 qz615 qz615)

noncomputable abbrev qz59 := qz408

noncomputable def Ns588p391 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz56 Ns588p387 Ns588p388 Ns588p389 Ns588p390 31398610509132957069 56294995342131200 466530004941 

noncomputable def Ns588p392 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 31398610509132957069 56294995342131200 466530004941 7036874417766400 31398610509132957069 56294995342131200 466530004941 7036874417766400 Ns588p387 

noncomputable def Ns588p393 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz55 13 10 0 1 1509787 67108864 1 

noncomputable def Ns588p394 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 1509787 67108864 1 67108864 1509787 67108864 

noncomputable abbrev qz60 := qz406

noncomputable def Ns588p395 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz23 882990555534649 70368744177664 713163777 1125899906842624 29715157 8388608 3 33554432 26238202987229313974893 

noncomputable def Ns588p396 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz23 29715157 8388608 3 33554432 29715157 8388608 3 33554432 882990555534649 70368744177664 713163777 

noncomputable def Ns588p397 := @Ns588p396 1125899906842624 qz407 

noncomputable def Ns588p398 := Ns588p397 qz407 

noncomputable def Ns588p399 := @Ns588p395 590295810358705651712 127150643206226439 37778931862957161709568 (Ns588p398 rfl) qz407 

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz355 qz406 qz378)

noncomputable def Ns588p400 := @Enclosure.Real.IsNear.inv_image qz61 26238202987229313974893 590295810358705651712 127150643206226439 37778931862957161709568 754893 754894 33554432 (Ns588p399 rfl) 

noncomputable def Ns588p401 := @Ns588p370 201 2147483648 19627231 671088640 13 671088640 58298369549795328 434356701 10737418240 1213 10737418240 (@Ns588p371 1 2147483648 1 2147483648 6459684768710656 24064201 2147483648 201 2147483648 (@Ns588p372 268435456 25 268435456 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns588p373 (Ns588p379 rfl rfl rfl rfl) rfl) rfl) (@Ns588p380 67108864 1 67108864 1 2147483648 1 2147483648 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns588p381 1 67108864 1 67108864 (@Ns588p386 33554432 (@Ns588p391 7036874417766400 Ns588p382 Ns588p383 Ns588p384 Ns588p385 (@Ns588p392 Ns588p388 Ns588p389 Ns588p390 (Ns588p378 rfl) (Ns588p378 rfl) rfl) (Ns588p378 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns588p393 67108864 19627231 671088640 13 671088640 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns588p394 1 67108864 (Ns588p400 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS589to600.d60 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 := @Ns588p369 434356701 10737418240 1213 10737418240 (BSN.hardyZErrorBoundRS₀_mk qz4 989310 1000 qz11 rfl rfl) (Ns588p401 rfl rfl) 

noncomputable def Ns588p402 := nat_lit 2054100531646810630362553 

noncomputable def Ns588p403 := nat_lit 2142773791602101515714560000 

noncomputable def Ns588p404 := nat_lit 6099072994232251794769160699904 

noncomputable abbrev qz752 := (Enclosure.sfrac Bool.false 991794 1000)

noncomputable abbrev qz617 := qz752

noncomputable abbrev qz409 := qz617

noncomputable abbrev qz62 := qz409

noncomputable abbrev qz753 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 991794 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz618 := qz753

noncomputable abbrev qz410 := qz618

noncomputable abbrev qz63 := qz410

noncomputable abbrev qz754 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 991794 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz619 := qz754

noncomputable abbrev qz411 := qz619

noncomputable abbrev qz64 := qz411

noncomputable abbrev qz620 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz63 qz9))

noncomputable def Ns588p405 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HMul.hMul Real Real Real qz5 qz620 (Zeta.RiemannSiegel.correction qz64)) 146679583 134217728 256537 268435456 4155002701195196571545 37778931862957161709568 6305622705168001242553 Ns588p403 Ns588p404 

noncomputable def Ns588p406 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos BSN.quadSignNeg 11 12 991794 1000 286 536870912 268435456 9007199254740992 Bool.false 1081130026865 4517 1334074092 51 154981288 8 

noncomputable def Ns588p407 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 991794 1000 171 232 536870912 268435456 9007199254740992 Bool.false 1081130026865 4517 

noncomputable def Ns588p408 := Ns588p407 1236190956 51 169773496 8 1287360220 51 161872664 8 Bool.true 609695615 206565 Bool.true 709905682 Bool.true 17068454 28296951008113761 1 Bool.false 520380344 Bool.false Bool.false 536599610 Bool.false Bool.true 283346032 

noncomputable def Ns588p409 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 991794 1000 30 105 536870912 268435456 9007199254740992 Bool.false 1081130026865 4517 

noncomputable def Ns588p410 := Ns588p409 1116391676 51 189812536 8 1179625948 51 178956968 8 Bool.true 509158015 168699 Bool.true 801093345 Bool.true 267850669 28296951008113761 1 Bool.false 42178002 Bool.true Bool.false 256876274 Bool.true Bool.true 609695615 

noncomputable def Ns588p411 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 991794 1000 150 53 536870912 268435456 9007199254740992 Bool.false 1081130026865 4517 

noncomputable def Ns588p412 := Ns588p411 961943533 51 219176632 8 1044702541 51 202918136 8 Bool.true 297932241 125360 Bool.false 582974016 Bool.false 304627520 28296951008113761 1 Bool.false 250256946 Bool.true Bool.false 288542465 Bool.true Bool.true 509158015 

noncomputable def Ns588p413 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 991794 1000 406 265 536870912 268435456 9007199254740992 Bool.false 1081130026865 4517 

noncomputable def Ns588p414 := Ns588p413 744261104 50 268435448 8 864060384 50 240095976 8 Bool.false 53153119 74089 Bool.false 590497732 Bool.false 681685394 28296951008113761 1 Bool.false 243576275 Bool.true Bool.false 512724173 Bool.true Bool.true 297932241 

noncomputable def Ns588p415 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 991794 1000 844 588 536870912 268435456 9007199254740992 Bool.false 1081130026865 4517 

noncomputable def Ns588p416 := Ns588p415 372130544 50 379625064 8 589812976 50 309962568 8 Bool.true 536870776 4570 Bool.false 295447195 Bool.false 287920504 28296951008113761 1 Bool.false 457607682 Bool.false Bool.false 461498698 Bool.false Bool.false 53153119 

noncomputable def Ns588p417 := nat_lit 269741049142953518769470275410200389951824853469423177923 

noncomputable def Ns588p418 := nat_lit 133948849313801253456195204449904020046400892960768000 

noncomputable def Ns588p419 := nat_lit 8921088000000000000000000 

noncomputable def Ns588p420 := nat_lit 460626479554822098130891994987520000 

noncomputable def Ns588p421 := nat_lit 2741079797088357920769696738828170465280 

noncomputable abbrev qz621 := (@Eq.refl Real qz752)

noncomputable abbrev qz412 := qz621

noncomputable abbrev qz65 := qz412

noncomputable def Ns588p422 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz62 991794 1000 3934622353744 16000000 1983588 4000 2000 Ns588p420 Ns588p421 qz65 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns588p423 := nat_lit 49718670178029192579588761163608135875920356991484080154767360 

noncomputable abbrev qz622 := (@HSub.hSub Real Real Real qz743 qz744 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz745 (@Nat.cast Real Real.instNatCast 1983588))))

noncomputable abbrev qz413 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 991794 4000) (Real.log (Enclosure.sfrac Bool.false 3934622353744 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz622))

noncomputable abbrev qz623 := (Enclosure.sfrac Bool.false 991794 2000)

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz413 qz623) (@HMul.hMul Real Real Real qz355 qz623 (Real.log Real.pi)))

noncomputable def Ns588p424 := @Enclosure.Real.IsNear.addLit_ft_p qz66 (Enclosure.sfrac Bool.true Ns588p420 Ns588p421) 18138353498426448304687 9007199254740992000 75036154965305090831 Ns588p419 Ns588p420 Ns588p421 0 1 Ns588p423 

noncomputable def Ns588p425 := nat_lit 608622149054912366641135222784000 

noncomputable abbrev qz67 := (@HSub.hSub Real Real Real qz359 qz413 qz623)

noncomputable def Ns588p426 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (@HMul.hMul Real Real Real qz5 qz623 (Real.log Real.pi)) 23251453316575221013039 9007199254740992000 6248721680813411 2178000000000000000000 19047781147617 33554432000 1487691 268435456000 Ns588p425 18138353498426448304687 9007199254740992000 

noncomputable def Ns588p427 := nat_lit 46502906633150442026078000 

noncomputable abbrev qz68 := qz413

noncomputable def Ns588p428 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz623 27718096405403514722863 9007199254740992000 6248721680813411 2178000000000000000000 991794 2000 0 1 Ns588p427 23251453316575221013039 9007199254740992000 6248721680813411 2178000000000000000000 

noncomputable def Ns588p429 := nat_lit 62415604321397376768095597881431425024 

noncomputable def Ns588p430 := nat_lit 120048623507273441651720192 

noncomputable def Ns588p431 := nat_lit 105786295397742917008678074714146641922999934492833901833516742732681284640491939316312619637849764640050151503014358028683224303151004773953353193983788478567416352492758246160147114218103183361693311002528972800 

noncomputable def Ns588p432 := nat_lit 3467568121080059367068277810468723565886108447868684414535797353752096055272028036476995171703607411085318842479173273154521792982735133803249202101992202538895365612506493968148367124615201651445472434407342080 

noncomputable def Ns588p433 := nat_lit 34228239140881103829074770567588632927018845664205248257222687068669873435517815722801083808644458095558144069336046753888271493819973890552240104433553672625973573319182199955217392407337674440336998400 

noncomputable def Ns588p434 := BSN.log_dyadic_bound 1837470353744 6031774353744 9 8 Ns588p431 268435456 87120000 Ns588p432 Ns588p433 168908896 7869244707488 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1837470353744) (BSN.artanhQ 6031774353744) 0 8 Ns588p432 Ns588p431 Ns588p433 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz414 := (Real.log (Enclosure.sfrac Bool.false 3934622353744 16000000))

noncomputable def Ns588p435 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 991794 4000) qz414 991794 4000 0 1 55901996561919079 4503599627370496 12500018513 1089000000000000000 27721632389065985518863 9007199254740992000 2066240560180387 726000000000000000000 (Enclosure.Real.IsNear.const Bool.false 991794 4000) (BSN.isNear_log_sfrac 3934622353744 16000000 55901996561919079 4503599627370496 12500018513 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3934622353744) qz362)) Bool.false Ns588p430 Ns588p114 1000001481040000 87120000000000000000000 55901996561919079 4503599627370496 12500018513 1089000000000000000 (BSN.log_rat_reduce_isNear 3934622353744 16000000 17 7869244707488 4194304000000 168908896 268435456 24973259072661432 36028797018963968 87120000 1000000000000000 rfl rfl rfl rfl (Ns588p434 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p436 := BSN.arctan_dyadic_bound_f 1000 1983588 1 0 33554432 10890000 0 1 1 0 1 1 16916 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1983588) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1983588) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns588p437 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1983588))) 884279719003555 562949953421312 1 2000000000000000 16916 33554432 1 10890000 29661980838871819091968 883995915617699 562949953421312 200000001089 2178000000000000000 qz17 (Ns588p436 rfl) rfl rfl 

noncomputable abbrev qz415 := (@HMul.hMul Real Real Real qz588 qz593 qz622)

noncomputable abbrev qz69 := qz415

noncomputable abbrev qz416 := qz622

noncomputable abbrev qz70 := qz416

noncomputable def Ns588p438 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 991794 4000) qz414) qz69 27721632389065985518863 9007199254740992000 2066240560180387 726000000000000000000 883995915617699 2251799813685248 200000001089 8712000000000000000 Ns588p429 27718096405403514722863 9007199254740992000 6248721680813411 2178000000000000000000 (Ns588p435 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz70 1 4 0 1 883995915617699 562949953421312 200000001089 2178000000000000000 883995915617699 2251799813685248 200000001089 8712000000000000000 qz369 Ns588p437 rfl) 

noncomputable def Ns588p439 := @Ns588p424 Ns588p417 Ns588p418 75036154965305090831 Ns588p419 (@Ns588p426 75036154965305090831 Ns588p419 (Ns588p428 (Ns588p438 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 991794 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz623 (Real.log Real.pi) 991794 2000 0 1 38410761 33554432 3 268435456 19047781147617 33554432000 1487691 268435456000 (Enclosure.Real.IsNear.const Bool.false 991794 2000) RS589to600.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns588p420 Ns588p421) 

noncomputable def Ns588p440 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns588p417 Ns588p418 75036154965305090831 Ns588p419 67570626679 33554432 565 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz370 qz66 (Enclosure.sfrac Bool.true Ns588p420 Ns588p421)) Bool.false Ns588p417 Ns588p418 75036154965305090831 Ns588p419 Ns588p422 (Ns588p439 rfl rfl)) 

noncomputable def Ns588p441 := BSN.cos_dyadic_bound_f 97482028 137438953472 1 0 67108864 21801270 0 1 1 0 1 1 67108847 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 97482028) qz383 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 97482028) qz384 0 0 rfl) rfl rfl 

noncomputable def Ns588p442 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz62) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 67570626679) qz397) Bool.false 67570626679 33554432 565 67108864 Bool.true 67108847 67108864 1 10890000 (Ns588p440 rfl) (Enclosure.sfrac_false_div 67570626679 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 67570626679) qz397) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3429843957718783623168) qz611) 226375608064910080 72057594037927936 Bool.false 67108847 67108864 320 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 67570626679 33554432 226375608064910080 72057594037927936 320 3429843957718783623168 Ns588p278 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108847 67108864 3429843957718783623168 Ns588p278 97482028 137438953472 21801270 21780000 (Ns588p441 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p443 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns588p417 Ns588p418 75036154965305090831 Ns588p419 1081130026865 536870912 4517 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz370 qz66 (Enclosure.sfrac Bool.true Ns588p420 Ns588p421)) Bool.false Ns588p417 Ns588p418 75036154965305090831 Ns588p419 Ns588p422 (Ns588p439 rfl rfl)) 

noncomputable def Ns588p444 := Ns588p416 74089 BSN.abs_quadSignPos (BSN.cos_quad_nat0 844 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 457607682 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 588 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 461498698 536870912) qz65 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) Bool.true 67108847 67108864 388747429 45675970560000 536870776 536870912 4570 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 67108847 67108864 388747429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz62) qz62) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 67108847 67108864 6219958864 730815528960000 67108847 67108864 388747429 45675970560000 (Ns588p442 rfl rfl) rfl)) rfl) (Ns588p443 rfl) RS589to600.d7 

noncomputable def Ns588p445 := nat_lit 1063486476322072125185062997287463976595230686768596817394489599465190625 

noncomputable def Ns588p446 := nat_lit 58054911702093361572730498407804015147128375126778605631625500390625 

noncomputable def Ns588p447 := nat_lit 3190343319142812188832043530865576321755397803555536894972205547394790625 

noncomputable def Ns588p448 := BSN.cos_dyadic_bound_f 295447195 536870912 3 2 536870912 268435456 Ns588p445 Ns588p152 Ns588p446 Ns588p447 Ns588p155 Ns588p446 457607682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 295447195) qz375 0 2 Ns588p445 Ns588p152 Ns588p446 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 295447195) qz376 0 2 Ns588p447 Ns588p155 Ns588p446 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p449 := nat_lit 959180934027810733854921567187664581967122674437073305060518204241084416 

noncomputable def Ns588p450 := nat_lit 47225955218567649654171251854408183456075261147263511126627147841536 

noncomputable def Ns588p451 := nat_lit 2877448350172995066265456359059284929534455872788925388159301358427570176 

noncomputable def Ns588p452 := BSN.cos_dyadic_bound_f 287920504 536870912 3 2 536870912 268435456 Ns588p449 Ns588p152 Ns588p450 Ns588p451 Ns588p155 Ns588p450 461498698 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 287920504) qz375 0 2 Ns588p449 Ns588p152 Ns588p450 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 287920504) qz376 0 2 Ns588p451 Ns588p155 Ns588p450 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p453 := nat_lit 16762386950502773175768935536274436288115236991019246777749550183615653810916617709167494901681004465267729760256 

noncomputable def Ns588p454 := nat_lit 1797292685411310422746986382700479441753381716655112783704913666839000246202693830983404800534937312690176 

noncomputable def Ns588p455 := nat_lit 101632798447590250906755156220306895266798805079009163551469127908098775274703131128730546227399715423311101952000 

noncomputable def Ns588p456 := BSN.cos_dyadic_bound_f 590497732 536870912 4 3 536870912 268435456 Ns588p453 Ns588p146 Ns588p454 Ns588p455 Ns588p149 Ns588p454 243576275 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 590497732) qz375 0 3 Ns588p453 Ns588p146 Ns588p454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 590497732) qz376 0 3 Ns588p455 Ns588p149 Ns588p454 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p457 := nat_lit 77404679451370495060764429247502179024463368625756943544994332098544464585329458250133514524771904450843337691136 

noncomputable def Ns588p458 := nat_lit 10069499049805629545867717432601767281135349565211638855711799934998800120412692550981274861983494425153536 

noncomputable def Ns588p459 := nat_lit 386817883902818072703311583009701076226572297607167013306232885608523122430210317957623124629641055343115314794496 

noncomputable def Ns588p460 := BSN.sin_dyadic_bound_f 681685394 536870912 4 3 536870912 268435456 Ns588p457 Ns588p172 Ns588p458 Ns588p459 Ns588p175 Ns588p458 512724173 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 681685394) qz373 0 3 Ns588p457 Ns588p172 Ns588p458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 681685394) qz374 0 3 Ns588p459 Ns588p175 Ns588p458 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p461 := Ns588p414 125360 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 406 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 243576275 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 265 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 512724173 536870912) qz65 rfl rfl (Ns588p444 RS589to600.d9 RS589to600.d11 RS589to600.d13 RS589to600.d17 (Ns588p448 rfl rfl) (Ns588p452 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns588p443 rfl) RS589to600.d19 RS589to600.d21 RS589to600.d23 RS589to600.d25 RS589to600.d17 (Ns588p456 rfl rfl) (Ns588p460 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns588p462 := nat_lit 15923583655213305536106636034851738013785908986546283382115747926930333637477496623603489826357898243715771662336 

noncomputable def Ns588p463 := nat_lit 1540956491290149366394717476873612191743750803155154223360738249235763930573178884137714932492841470918656 

noncomputable def Ns588p464 := nat_lit 96549812838024372482191630950234317550792752376807355299575927746542279203348132897564549596269857606507597660160 

noncomputable def Ns588p465 := BSN.cos_dyadic_bound_f 582974016 536870912 4 3 536870912 268435456 Ns588p462 Ns588p146 Ns588p463 Ns588p464 Ns588p149 Ns588p463 250256946 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 582974016) qz375 0 3 Ns588p462 Ns588p146 Ns588p463 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 582974016) qz376 0 3 Ns588p464 Ns588p149 Ns588p463 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p466 := nat_lit 2163479128298099861801966550513220451232717726113448634512352466698240000 

noncomputable def Ns588p467 := nat_lit 74157158233458348720184457996682553227525995955126120585625600000000 

noncomputable def Ns588p468 := nat_lit 5666134795857883562631032095555011314809035192970342886194260685619200000 

noncomputable def Ns588p469 := BSN.sin_dyadic_bound_f 304627520 536870912 3 2 536870912 268435456 Ns588p466 Ns588p136 Ns588p467 Ns588p468 Ns588p139 Ns588p467 288542465 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 304627520) qz373 0 2 Ns588p466 Ns588p136 Ns588p467 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 304627520) qz374 0 2 Ns588p468 Ns588p139 Ns588p467 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p470 := Ns588p412 168699 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 150 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 250256946 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 288542465 536870912) qz65 rfl rfl (Ns588p461 rfl rfl) (Ns588p443 rfl) RS589to600.d27 RS589to600.d29 RS589to600.d31 RS589to600.d33 RS589to600.d17 (Ns588p465 rfl rfl) (Ns588p469 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p471 := nat_lit 56898050434963924891690516907864411377496789903248971174714869678673816748720192313508093318673559780303646890625 

noncomputable def Ns588p472 := nat_lit 69854998351682280609951650122844455802584987611675557780864879609213976389523417004249380776761074462890625 

noncomputable def Ns588p473 := nat_lit 344504103504595076692762534836912953037982704884606576795027175841669897449244540268230495181711259317910712490625 

noncomputable def Ns588p474 := BSN.cos_dyadic_bound_f 801093345 536870912 4 3 536870912 268435456 Ns588p471 Ns588p146 Ns588p472 Ns588p473 Ns588p149 Ns588p472 42178002 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 801093345) qz375 0 3 Ns588p471 Ns588p146 Ns588p472 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 801093345) qz376 0 3 Ns588p473 Ns588p149 Ns588p472 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p475 := nat_lit 1293126832681757608686434583827237022343411645802039941056361826902634785 

noncomputable def Ns588p476 := nat_lit 26493655415150005813569657287034216208779963269598921697897616535841 

noncomputable def Ns588p477 := nat_lit 3386717857772026351312201940102394145977930571445763352131531998127747361 

noncomputable def Ns588p478 := BSN.sin_dyadic_bound_f 267850669 536870912 3 2 536870912 268435456 Ns588p475 Ns588p136 Ns588p476 Ns588p477 Ns588p139 Ns588p476 256876274 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 267850669) qz373 0 2 Ns588p475 Ns588p136 Ns588p476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 267850669) qz374 0 2 Ns588p477 Ns588p139 Ns588p476 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p479 := Ns588p410 206565 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 42178002 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 256876274 536870912) qz65 rfl rfl (Ns588p470 rfl) (Ns588p443 rfl) RS589to600.d35 RS589to600.d37 RS589to600.d39 RS589to600.d41 RS589to600.d17 (Ns588p474 rfl rfl) (Ns588p478 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p480 := nat_lit 91054117900167282148141866275120989652492285192272879456308367545326720126292341284372911004964840665401499979776 

noncomputable def Ns588p481 := nat_lit 16383543053822166848767081993450675758370322395351283359133150640883300319839546044590689876380232268517376 

noncomputable def Ns588p482 := nat_lit 454986281979786083071449892484366483192004307604894962262689552795479208388300848544344234564177860775820275879936 

noncomputable def Ns588p483 := BSN.sin_dyadic_bound_f 709905682 536870912 4 3 536870912 268435456 Ns588p480 Ns588p172 Ns588p481 Ns588p482 Ns588p175 Ns588p481 520380344 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 709905682) qz373 0 3 Ns588p480 Ns588p172 Ns588p481 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 709905682) qz374 0 3 Ns588p482 Ns588p175 Ns588p481 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p484 := nat_lit 84874405279957260854792413456 

noncomputable def Ns588p485 := BSN.cos_dyadic_bound_f 17068454 536870912 2 1 536870912 268435456 Ns588p484 Ns588p142 Ns588p484 Ns588p484 Ns588p143 Ns588p484 536599610 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 17068454) qz375 0 1 Ns588p484 Ns588p142 Ns588p484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 17068454) qz376 0 1 Ns588p484 Ns588p143 Ns588p484 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p486 := Ns588p408 240621 BSN.abs_quadSignPos (BSN.cos_quad_nat3 171 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 520380344 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 232 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536599610 536870912) qz65 rfl rfl (Ns588p479 rfl) (Ns588p443 rfl) RS589to600.d43 RS589to600.d45 RS589to600.d47 RS589to600.d49 RS589to600.d17 (Ns588p483 rfl rfl) (Ns588p485 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p487 := nat_lit 59068701894303458450628091350957293267672725780437408438383386918169621973701381109613659010940599950828264337441 

noncomputable def Ns588p488 := nat_lit 78132496428250697449237159586617184329905306091543752687641399235954728979637000472651640536357076590768161 

noncomputable def Ns588p489 := nat_lit 357620199866972863396588461440651225054115316377309093649260876552592064310339112049259114595850179091469803302945 

noncomputable def Ns588p490 := BSN.cos_dyadic_bound_f 808604167 536870912 4 3 536870912 268435456 Ns588p487 Ns588p146 Ns588p488 Ns588p489 Ns588p149 Ns588p488 34686512 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 808604167) qz375 0 3 Ns588p487 Ns588p146 Ns588p488 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 808604167) qz376 0 3 Ns588p489 Ns588p149 Ns588p488 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p491 := Ns588p406 Bool.true 283346032 240621 Bool.true 808604167 28296951008113761 1 Bool.false 34686512 Bool.true Bool.true 293359166 256537 BSN.abs_quadSignNeg qz398 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 34686512 536870912) qz65 rfl (Ns588p486 rfl) (Ns588p443 rfl) RS589to600.d51 RS589to600.d53 RS589to600.d17 (Ns588p490 rfl rfl) rfl 

noncomputable def Ns588p492 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) 293359166 536870912 256537 536870912 293359166 536870912 256537 536870912 314992005987958784 146679583 134217728 256537 268435456 (Ns588p491 rfl rfl rfl rfl) 

noncomputable def Ns588p493 := @Enclosure.Real.IsNear.mulLit_ff qz620 (Zeta.RiemannSiegel.correction qz64) 9466501 33554432 1 33554432 438916417079045 1125899906842624 5307749717593087 510877082729840640000 4155002701195196571545 37778931862957161709568 

noncomputable abbrev qz624 := (@HPow.hPow Real Real Real qz7 qz63 qz9)

noncomputable def Ns588p494 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz624 1 1 0 1 9466501 33554432 1 33554432 9466501 33554432 1 33554432 

noncomputable def Ns588p495 := @Enclosure.Real.IsNear.sqrt_image qz63 5296530559179 33554432000 495897 33554432000 421570940 421570980 33554432 (@Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz5 qz62 qz3) Bool.false 5296530559179 33554432000 495897 33554432000 (BSN.t_div_two_pi_mk qz62 991794 1000 qz65) (@Enclosure.Real.IsNear.mulLit_ff qz62 qz3 991794 1000 0 1 10680707 67108864 1 67108864 5296530559179 33554432000 495897 33554432000 (Enclosure.Real.IsNear.const Bool.false 991794 1000) RS589to600.d56 rfl)) 

noncomputable abbrev qz755 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 991794 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz625 := qz755

noncomputable abbrev qz417 := qz625

noncomputable abbrev qz71 := qz417

noncomputable def Ns588p496 := @Enclosure.Real.IsNear.sqrt_image qz71 26348185 2097152 5 8388608 118935164 118935171 33554432 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 843141920 67108864 40 67108864 26348185 2097152 5 8388608 (Ns588p495 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns588p497 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz71) 237870335 67108864 7 67108864 9466500 9466502 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz71) Bool.false 237870335 67108864 7 67108864 237870335 67108864 7 67108864 (Ns588p496 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns588p498 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 18933002 67108864 2 67108864 9466501 33554432 1 33554432 (Ns588p497 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz418 := (@HMul.hMul Real Real Real qz588 qz586 qz619)

noncomputable abbrev qz72 := (Real.cos qz418)

noncomputable abbrev qz626 := (@HMul.hMul Real Real Real qz739 qz754 qz754)

noncomputable abbrev qz419 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz626 qz619) qz603)

noncomputable abbrev qz73 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz419))

noncomputable def Ns588p499 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz72) qz73) Bool.false 438916417079045 

noncomputable def Ns588p500 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz72) qz73 72885913 67108864 305 

noncomputable abbrev qz74 := (@Neg.neg Real Real.instNeg (Real.cos qz418))

noncomputable def Ns588p501 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz72) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz74)) Bool.true 72885913 67108864 305 67108864 (BSN.inv_eq_neg_inv_neg qz72) 

noncomputable def Ns588p502 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz74) Bool.false 72885913 67108864 305 67108864 72885913 67108864 

noncomputable def Ns588p503 := @Enclosure.Real.IsNear.recentre' qz72 Bool.true 61789713 67108864 702847216 182703882240000 61789713 67108864 43927951 11418992640000 

noncomputable abbrev qz75 := qz418

noncomputable def Ns588p504 := @Enclosure.Real.IsNear.cos_image qz75 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 29715973) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 29715973 8388608 63 16777216 Bool.true 61789713 67108864 1 

noncomputable def Ns588p505 := nat_lit 134930377085845841892371683 

noncomputable def Ns588p506 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz64 884279719003555 140737488355328 1 500000000000000 1182361 2097152 5 8388608 1045537852840762293355 295147905179352825856 Ns588p505 

noncomputable def Ns588p507 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz1 26348185 2097152 5 8388608 12 1 0 1 1182361 1182361 2097152 5 

noncomputable def Ns588p508 := @Ns588p507 8388608 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 843141920 67108864 40 67108864 26348185 2097152 5 8388608 (Ns588p495 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns588p509 := @Enclosure.Real.IsNear.recentre' qz75 Bool.false 1045537852840762293355 295147905179352825856 Ns588p505 Ns588p206 29715973 8388608 63 16777216 (@Ns588p506 Ns588p206 RS589to600.d55 (Ns588p508 rfl rfl) rfl) 

noncomputable def Ns588p510 := nat_lit 5521081698698246187557237998636177661328314491556169683353405255066902823015599309339600001 

noncomputable def Ns588p511 := nat_lit 5133330660362904937396483134791632965849700352038159351603073932373040875403608499582161387520 

noncomputable def Ns588p512 := nat_lit 84827705903832167671307828039237112265245547445929654495730270831020655957679679317121 

noncomputable def Ns588p513 := nat_lit 16563075440682930898336371380252454509760412983573617190751224304659046427734882568660165761 

noncomputable def Ns588p514 := nat_lit 230999879716330722182841741065623483463236515841717170822138326956786839393162382481197262438400 

noncomputable def Ns588p515 := BSN.cos_dyadic_bound_f 55089295087 137438953472 3 2 67108864 21801270 Ns588p510 Ns588p511 Ns588p512 Ns588p513 Ns588p514 Ns588p512 61789713 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 55089295087) qz383 0 2 Ns588p510 Ns588p511 Ns588p512 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 55089295087) qz384 0 2 Ns588p513 Ns588p514 Ns588p512 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p516 := @Ns588p504 10890000 (Ns588p509 rfl) (Enclosure.sfrac_false_div 29715973 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 29715973) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 484570564115716611506176) (@Nat.cast Real Real.instNatCast Ns588p64)) 226375608064910080 72057594037927936 Bool.false 61789713 67108864 0 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 29715973 8388608 226375608064910080 72057594037927936 0 484570564115716611506176 Ns588p64 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 61789713 67108864 484570564115716611506176 Ns588p64 55089295087 137438953472 21801270 21780000 (Ns588p515 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p517 := @Enclosure.Real.IsNear.inv_image qz74 61789713 67108864 43927951 11418992640000 36442804 36443109 33554432 (@Enclosure.Real.IsNear.neg qz72 Bool.true 61789713 67108864 43927951 11418992640000 (Ns588p503 (Ns588p516 rfl rfl) rfl)) 

noncomputable def Ns588p518 := Ns588p501 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz74) Bool.false 72885913 67108864 305 67108864 (@Ns588p502 305 67108864 (Ns588p517 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p519 := @Enclosure.Real.IsNear.recentre' qz73 Bool.true 12043930 33554432 

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz355 qz352 qz419)

noncomputable def Ns588p520 := @Enclosure.Real.IsNear.cos_image qz76 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32512989)) qz381) Bool.true 32512989 16777216 

noncomputable def Ns588p521 := nat_lit 1199517576250779438795699725 

noncomputable def Ns588p522 := nat_lit 618970019642690137449562112 

noncomputable def Ns588p523 := nat_lit 96326801577255190794859759098079 

noncomputable def Ns588p524 := @Enclosure.Real.IsNear.recentre' qz76 Bool.true Ns588p521 Ns588p522 Ns588p523 

noncomputable def Ns588p525 := nat_lit 12089258196146291747061760000000000000 

noncomputable abbrev qz77 := qz419

noncomputable def Ns588p526 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz77 884279719003555 140737488355328 1 500000000000000 1356491108495 

noncomputable abbrev qz420 := (@HSub.hSub Real Real Real qz592 qz626 qz619)

noncomputable abbrev qz78 := qz420

noncomputable def Ns588p527 := @Enclosure.Real.IsNear.subLit_tf qz78 qz31 1081613201551 4398046511104 89237505 70368744177664 1 16 

noncomputable abbrev qz421 := qz626

noncomputable abbrev qz79 := qz421

noncomputable def Ns588p528 := @Enclosure.Real.IsNear.subLit_ff_n qz79 qz64 1397977534321 4398046511104 47294465 70368744177664 1182361 2097152 5 8388608 

noncomputable def Ns588p529 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 1182361 2097152 5 8388608 1182361 2097152 5 8388608 1397977534321 4398046511104 

noncomputable def Ns588p530 := nat_lit 141171686994342646100281914322914402319433064185856401817079679270092034424102284154673437273201 

noncomputable def Ns588p531 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns588p532 := nat_lit 1395348742252582399857298869457550292785079283044221513902281139059633027578964309077060721 

noncomputable def Ns588p533 := nat_lit 851681035462449272586413101245727605935638513584364048246704225285514989090135067221665298967665 

noncomputable def Ns588p534 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns588p535 := BSN.cos_dyadic_bound_t 32512989 16777216 4 3 33554432 10890000 Ns588p530 Ns588p531 Ns588p532 Ns588p533 Ns588p534 Ns588p532 12043930 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32512989) (BSN.cosEvenQ 16777216) 0 3 Ns588p530 Ns588p531 Ns588p532 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32512989) (BSN.cosOddQ 16777216) 0 3 Ns588p533 Ns588p534 Ns588p532 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p536 := @Ns588p519 5893258864 730815528960000 6021965 16777216 368328679 45675970560000 (@Ns588p520 535 67108864 Bool.true 12043930 33554432 1 10890000 (@Ns588p524 Ns588p525 32512989 16777216 535 67108864 (@Ns588p526 4398046511104 89237505 70368744177664 Ns588p521 Ns588p522 Ns588p523 Ns588p525 RS589to600.d55 (@Ns588p527 0 1 21703857735920 1356491108495 4398046511104 89237505 70368744177664 (@Ns588p528 2268307288859082752 1081613201551 4398046511104 89237505 70368744177664 (@Ns588p529 47294465 70368744177664 (Ns588p508 rfl rfl) (Ns588p508 rfl rfl) rfl) (Ns588p508 rfl rfl) rfl rfl) qz388 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32512989 16777216) (BSN.cos_neg_of_bound 32512989 16777216 Bool.true 12043930 33554432 1 10890000 (Ns588p535 rfl rfl)) rfl rfl) 

noncomputable def Ns588p537 := @Ns588p493 6305622705168001242553 Ns588p403 (Ns588p494 qz33 (@Enclosure.Real.IsNear.of_eq qz624 (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 9466501 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz63 (BSN.t_div_two_pi_nonneg qz62 991794 1000 qz65)) Ns588p498) rfl) (@Ns588p499 1125899906842624 5307749717593087 510877082729840640000 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz62 991794 1000 12 qz65 rfl rfl (@BSN.floor_sqrt_eq_dec qz62 991794 1000 12 qz65 rfl rfl rfl))) (@Ns588p500 67108864 6021965 16777216 368328679 45675970560000 438916417079045 1125899906842624 5307749717593087 510877082729840640000 Ns588p518 (Ns588p536 rfl) rfl)) 

noncomputable def Ns588p538 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (hardyZApproximantRS₀ qz62) Bool.true 45441634910048930307993 37778931862957161709568 Ns588p402 Ns588p403 (@Eq.refl Real (hardyZApproximantRS₀ qz62)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HMul.hMul Real Real Real qz5 qz620 (Zeta.RiemannSiegel.correction qz64))) Bool.true 45441634910048930307993 37778931862957161709568 Ns588p402 Ns588p403 (BSN.hardyZApproximantRS₀_eq qz62 12 (@BSN.floor_sqrt_eq_dec qz62 991794 1000 12 qz65 rfl rfl rfl)) (@Ns588p405 45441634910048930307993 37778931862957161709568 Ns588p402 Ns588p403 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12)) Bool.true 146679583 134217728 256537 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (Ns588p492 (Ns588p491 rfl rfl rfl rfl) rfl rfl)) (Ns588p537 rfl) rfl rfl)) 

theorem RS589to600.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz62) Bool.true 45441634910048930307993 37778931862957161709568 Ns588p402 Ns588p403 := Ns588p538 

noncomputable def Ns588p539 := nat_lit 342843806656336242514329600 

noncomputable def Ns588p540 := nat_lit 959258768773737767420689383424 

noncomputable abbrev qz756 := (Enclosure.sfrac Bool.false 993035 1000)

noncomputable abbrev qz627 := qz756

noncomputable abbrev qz422 := qz627

noncomputable abbrev qz80 := qz422

noncomputable abbrev qz757 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 993035 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz628 := qz757

noncomputable abbrev qz423 := qz628

noncomputable abbrev qz81 := qz423

noncomputable abbrev qz758 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 993035 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz629 := qz758

noncomputable abbrev qz424 := qz629

noncomputable abbrev qz82 := qz424

noncomputable abbrev qz630 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz81 qz9))

noncomputable def Ns588p541 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HMul.hMul Real Real Real qz5 qz630 (Zeta.RiemannSiegel.correction qz82)) 40219535 134217728 256869 268435456 4173757907383762310877 37778931862957161709568 1040141888107655390591 Ns588p539 Ns588p540 

noncomputable def Ns588p542 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos BSN.quadSignNeg 11 12 993035 1000 286 536870912 268435456 9007199254740992 Bool.false 1082816410551 4523 1334074092 51 154981288 8 

noncomputable def Ns588p543 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 9 10 11 993035 1000 171 231 536870912 268435456 9007199254740992 Bool.false 1082816410551 4523 

noncomputable def Ns588p544 := Ns588p543 1236190956 51 169773496 8 1287360220 51 161872664 8 Bool.true 207427812 206834 Bool.true 557634973 Bool.true 771613657 28296951008113761 1 Bool.false 462639529 Bool.false Bool.false 532090037 Bool.false Bool.false 99302834 

noncomputable def Ns588p545 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 993035 1000 30 105 536870912 268435456 9007199254740992 Bool.false 1082816410551 4523 

noncomputable def Ns588p546 := Ns588p545 1116391676 51 189812536 8 1179625948 51 178956968 8 Bool.true 79086231 168920 Bool.true 500151729 Bool.true 45382785 28296951008113761 1 Bool.false 320268440 Bool.true Bool.false 45328755 Bool.true Bool.true 207427812 

noncomputable def Ns588p547 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 993035 1000 151 53 536870912 268435456 9007199254740992 Bool.false 1082816410551 4523 

noncomputable def Ns588p548 := Ns588p547 961943533 51 219176632 8 1044702541 51 202918136 8 Bool.false 24196219 125527 Bool.false 232270921 Bool.false 694535352 28296951008113761 1 Bool.false 225092512 Bool.false Bool.false 516387364 Bool.true Bool.true 79086231 

noncomputable def Ns588p549 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 993035 1000 407 266 536870912 268435456 9007199254740992 Bool.false 1082816410551 4523 

noncomputable def Ns588p550 := Ns588p549 744261104 50 268435448 8 864060384 50 240095976 8 Bool.true 34367069 74192 Bool.false 509938531 Bool.false 452455287 28296951008113761 1 Bool.false 436647443 Bool.false Bool.false 357235166 Bool.true Bool.false 24196219 

noncomputable def Ns588p551 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 993035 1000 845 589 536870912 268435456 9007199254740992 Bool.false 1082816410551 4523 

noncomputable def Ns588p552 := Ns588p551 372130544 50 379625064 8 589812976 50 309962568 8 Bool.false 536870888 4586 Bool.false 676702019 Bool.false 399031431 28296951008113761 1 Bool.false 511224381 Bool.true Bool.false 363293719 Bool.true Bool.true 34367069 

noncomputable def Ns588p553 := nat_lit 802739918141338883983394906732354122226550415744530797 

noncomputable def Ns588p554 := nat_lit 398006261958792439026586840007288086823926769909760 

noncomputable def Ns588p555 := nat_lit 3568435200000000000000000 

noncomputable def Ns588p556 := nat_lit 463515535384913246463148710500000000 

noncomputable def Ns588p557 := nat_lit 2761723224822768267734582614598205000000 

noncomputable abbrev qz631 := (@Eq.refl Real qz756)

noncomputable abbrev qz425 := qz631

noncomputable abbrev qz83 := qz425

noncomputable def Ns588p558 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz80 993035 1000 3944475044900 16000000 1986070 4000 2000 Ns588p556 Ns588p557 qz83 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns588p559 := nat_lit 4013699590706694419916974533661770611132752078722653985000000 

noncomputable abbrev qz632 := (@HSub.hSub Real Real Real qz743 qz744 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz745 (@Nat.cast Real Real.instNatCast 1986070))))

noncomputable abbrev qz426 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 993035 4000) (Real.log (Enclosure.sfrac Bool.false 3944475044900 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz632))

noncomputable abbrev qz633 := (Enclosure.sfrac Bool.false 993035 2000)

noncomputable abbrev qz84 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz426 qz633) (@HMul.hMul Real Real Real qz355 qz633 (Real.log Real.pi)))

noncomputable def Ns588p560 := @Enclosure.Real.IsNear.addLit_ft_p qz84 (Enclosure.sfrac Bool.true Ns588p556 Ns588p557) 1453331705592045236917 720575940379279360 30051915615206527561 Ns588p555 Ns588p556 Ns588p557 0 1 Ns588p559 

noncomputable def Ns588p561 := nat_lit 97531439777464603286110732288000 

noncomputable abbrev qz85 := (@HSub.hSub Real Real Real qz359 qz426 qz633)

noncomputable def Ns588p562 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (@HMul.hMul Real Real Real qz5 qz633 (Real.log Real.pi)) 9314457598297560956297 3602879701896396800 2502591176920291 871200000000000000000 7628646009927 13421772800 595821 107374182400 Ns588p561 1453331705592045236917 720575940379279360 

noncomputable def Ns588p563 := nat_lit 18628915196595121912594000 

noncomputable abbrev qz86 := qz426

noncomputable def Ns588p564 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz633 11103350420683905154441 3602879701896396800 2502591176920291 871200000000000000000 993035 2000 0 1 Ns588p563 9314457598297560956297 3602879701896396800 2502591176920291 871200000000000000000 

noncomputable def Ns588p565 := nat_lit 25002522408578037627952784558803386368 

noncomputable def Ns588p566 := nat_lit 120072811404123326092673024 

noncomputable def Ns588p567 := nat_lit 108585197196593183197520617332625148561660048494118540422622738464483893511093513541784719796716201199674755187407509840821799153420744272253901920124403108540730667571387806309942500000000000000000000000000000000 

noncomputable def Ns588p568 := nat_lit 3587477117061857071297960705378703223147924595335993994388069513911518437541594111388944440564775526283910278164937484081430313607221500671202979154551354079700355663871216114168000000000000000000000000000000000 

noncomputable def Ns588p569 := nat_lit 37285903632955310550754965919769082565308158503002924248101576400662982129059674231004005575585236030798492069629076001488676246180437514687970664662232965898520708794702500000000000000000000000000000000 

noncomputable def Ns588p570 := BSN.log_dyadic_bound 1847323044900 6041627044900 9 8 Ns588p567 268435456 87120000 Ns588p568 Ns588p569 169580245 7888950089800 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1847323044900) (BSN.artanhQ 6041627044900) 0 8 Ns588p568 Ns588p567 Ns588p569 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz427 := (Real.log (Enclosure.sfrac Bool.false 3944475044900 16000000))

noncomputable def Ns588p571 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 993035 4000) qz427 993035 4000 0 1 55913259929103463 4503599627370496 12500018513 1089000000000000000 11104764814739451476041 3602879701896396800 2482591176811391 871200000000000000000 (Enclosure.Real.IsNear.const Bool.false 993035 4000) (BSN.isNear_log_sfrac 3944475044900 16000000 55913259929103463 4503599627370496 12500018513 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3944475044900) qz362)) Bool.false Ns588p566 Ns588p114 1000001481040000 87120000000000000000000 55913259929103463 4503599627370496 12500018513 1089000000000000000 (BSN.log_rat_reduce_isNear 3944475044900 16000000 17 7888950089800 4194304000000 169580245 268435456 24973259072661432 36028797018963968 87120000 1000000000000000 rfl rfl rfl rfl (Ns588p570 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p572 := BSN.arctan_dyadic_bound_f 1000 1986070 1 0 33554432 10890000 0 1 1 0 1 1 16894 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1986070) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1986070) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns588p573 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1986070))) 884279719003555 562949953421312 1 2000000000000000 16894 33554432 1 10890000 29661993223770794360832 883996284716451 562949953421312 200000001089 2178000000000000000 qz17 (Ns588p572 rfl) rfl rfl 

noncomputable abbrev qz428 := (@HMul.hMul Real Real Real qz588 qz593 qz632)

noncomputable abbrev qz87 := qz428

noncomputable abbrev qz429 := qz632

noncomputable abbrev qz88 := qz429

noncomputable def Ns588p574 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 993035 4000) qz427) qz87 11104764814739451476041 3602879701896396800 2482591176811391 871200000000000000000 883996284716451 2251799813685248 200000001089 8712000000000000000 Ns588p565 11103350420683905154441 3602879701896396800 2502591176920291 871200000000000000000 (Ns588p571 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz88 1 4 0 1 883996284716451 562949953421312 200000001089 2178000000000000000 883996284716451 2251799813685248 200000001089 8712000000000000000 qz369 Ns588p573 rfl) 

noncomputable def Ns588p575 := @Ns588p560 Ns588p553 Ns588p554 30051915615206527561 Ns588p555 (@Ns588p562 30051915615206527561 Ns588p555 (Ns588p564 (Ns588p574 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 993035 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz633 (Real.log Real.pi) 993035 2000 0 1 38410761 33554432 3 268435456 7628646009927 13421772800 595821 107374182400 (Enclosure.Real.IsNear.const Bool.false 993035 2000) RS589to600.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns588p556 Ns588p557) 

noncomputable def Ns588p576 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns588p553 Ns588p554 30051915615206527561 Ns588p555 67676025659 33554432 567 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz370 qz84 (Enclosure.sfrac Bool.true Ns588p556 Ns588p557)) Bool.false Ns588p553 Ns588p554 30051915615206527561 Ns588p555 Ns588p558 (Ns588p575 rfl rfl)) 

noncomputable def Ns588p577 := BSN.cos_dyadic_bound_f 34497563 137438953472 1 0 67108864 21801270 0 1 1 0 1 1 67108861 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 34497563) qz383 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 34497563) qz384 0 0 rfl) rfl rfl 

noncomputable def Ns588p578 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz80) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 67676025659) qz397) Bool.false 67676025659 33554432 567 67108864 Bool.false 67108861 67108864 1 10890000 (Ns588p576 rfl) (Enclosure.sfrac_false_div 67676025659 33554432) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 67676025659) qz397) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1213775115736588484608) qz611) 226375608064910080 72057594037927936 Bool.false 67108861 67108864 321 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q0 67676025659 33554432 226375608064910080 72057594037927936 321 1213775115736588484608 Ns588p278 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108861 67108864 1213775115736588484608 Ns588p278 34497563 137438953472 21801270 21780000 (Ns588p577 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p579 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns588p553 Ns588p554 30051915615206527561 Ns588p555 1082816410551 536870912 4523 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz370 qz84 (Enclosure.sfrac Bool.true Ns588p556 Ns588p557)) Bool.false Ns588p553 Ns588p554 30051915615206527561 Ns588p555 Ns588p558 (Ns588p575 rfl rfl)) 

noncomputable def Ns588p580 := Ns588p552 74192 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 845 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 511224381 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 589 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 363293719 536870912) qz83 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) Bool.false 67108861 67108864 390108679 45675970560000 536870888 536870912 4586 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 67108861 67108864 390108679 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz80) qz80) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 67108861 67108864 6241738864 730815528960000 67108861 67108864 390108679 45675970560000 (Ns588p578 rfl rfl) rfl)) rfl) (Ns588p579 rfl) RS589to600.d7 

noncomputable def Ns588p581 := nat_lit 75164082319435715479169601781992810528709910224015291392250230395913342946770859104909397162053592535431120619761 

noncomputable def Ns588p582 := nat_lit 9220822604481244101564346171391645413947242441613754257061386363639604712010611632171371802313754307922161 

noncomputable def Ns588p583 := nat_lit 375626615309697180778666793238003115716849479114857638089464801034011116991100127488228303451806488775680969083121 

noncomputable def Ns588p584 := BSN.sin_dyadic_bound_f 676702019 536870912 4 3 536870912 268435456 Ns588p581 Ns588p172 Ns588p582 Ns588p583 Ns588p175 Ns588p582 511224381 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 676702019) qz373 0 3 Ns588p581 Ns588p172 Ns588p582 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 676702019) qz374 0 3 Ns588p583 Ns588p175 Ns588p582 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p585 := nat_lit 6369913460372590403753767808261860273576467462170105954160031644697621185 

noncomputable def Ns588p586 := nat_lit 642771844711027959546388275376975700334095319104314213764664057000641 

noncomputable def Ns588p587 := nat_lit 16682066003703442726468221535859023708233064341833632418834940089544340161 

noncomputable def Ns588p588 := BSN.sin_dyadic_bound_f 399031431 536870912 3 2 536870912 268435456 Ns588p585 Ns588p136 Ns588p586 Ns588p587 Ns588p139 Ns588p586 363293719 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 399031431) qz373 0 2 Ns588p585 Ns588p136 Ns588p586 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 399031431) qz374 0 2 Ns588p587 Ns588p139 Ns588p586 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p589 := nat_lit 16992194745962571435214935258389629833709407917726787758694711232292647585 

noncomputable def Ns588p590 := nat_lit 4572383283256359166351161261690497054205221040055383752623864571425441 

noncomputable def Ns588p591 := nat_lit 44495964285538605367865023796596769712103545617124354460981900303841292961 

noncomputable def Ns588p592 := BSN.sin_dyadic_bound_f 509938531 536870912 3 2 536870912 268435456 Ns588p589 Ns588p136 Ns588p590 Ns588p591 Ns588p139 Ns588p590 436647443 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 509938531) qz373 0 2 Ns588p589 Ns588p136 Ns588p590 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 509938531) qz374 0 2 Ns588p591 Ns588p139 Ns588p590 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p593 := nat_lit 5850888674644225528789453078056898598438104798866835048267445956382907201 

noncomputable def Ns588p594 := nat_lit 1756326842902757443529443939279517129494221951797923012061801584089921 

noncomputable def Ns588p595 := nat_lit 17549153370246871071481300346292136761055325952696909298778214265980541761 

noncomputable def Ns588p596 := BSN.cos_dyadic_bound_f 452455287 536870912 3 2 536870912 268435456 Ns588p593 Ns588p152 Ns588p594 Ns588p595 Ns588p155 Ns588p594 357235166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 452455287) qz375 0 2 Ns588p593 Ns588p152 Ns588p594 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 452455287) qz376 0 2 Ns588p595 Ns588p155 Ns588p594 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p597 := Ns588p550 125527 BSN.abs_quadSignPos (BSN.cos_quad_nat3 407 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 436647443 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 266 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 357235166 536870912) qz83 rfl rfl (Ns588p580 RS589to600.d9 RS589to600.d11 RS589to600.d13 RS589to600.d17 (Ns588p584 rfl rfl) (Ns588p588 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns588p579 rfl) RS589to600.d19 RS589to600.d21 RS589to600.d23 RS589to600.d25 RS589to600.d17 (Ns588p592 rfl rfl) (Ns588p596 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns588p598 := nat_lit 731215995959048122355157680686877113060228323933574798106223126366644545 

noncomputable def Ns588p599 := nat_lit 8471469196255889494289616181797767115190116516836497859501021194561 

noncomputable def Ns588p600 := nat_lit 1915075797514046382347184123372764766391935302494525783567383281687849281 

noncomputable def Ns588p601 := BSN.sin_dyadic_bound_f 232270921 536870912 3 2 536870912 268435456 Ns588p598 Ns588p136 Ns588p599 Ns588p600 Ns588p139 Ns588p599 225092512 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 232270921) qz373 0 2 Ns588p598 Ns588p136 Ns588p599 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 232270921) qz374 0 2 Ns588p600 Ns588p139 Ns588p599 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p602 := nat_lit 83413745604915160150803061619757719377346096992378854233493555304804788687952887473260764232070604634776190058496 

noncomputable def Ns588p603 := nat_lit 12598889758577644054235710471143398035702123525926104026199523461159892119954447888170834855863058427805696 

noncomputable def Ns588p604 := nat_lit 416830095525693320374382963268264594659877791355627441158388000832980181875645708688189785112358089353584292397056 

noncomputable def Ns588p605 := BSN.sin_dyadic_bound_f 694535352 536870912 4 3 536870912 268435456 Ns588p602 Ns588p172 Ns588p603 Ns588p604 Ns588p175 Ns588p603 516387364 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 694535352) qz373 0 3 Ns588p602 Ns588p172 Ns588p603 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 694535352) qz374 0 3 Ns588p604 Ns588p175 Ns588p603 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p606 := Ns588p548 168920 BSN.abs_quadSignPos (BSN.cos_quad_nat3 151 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 225092512 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 516387364 536870912) qz83 rfl rfl (Ns588p597 rfl rfl) (Ns588p579 rfl) RS589to600.d27 RS589to600.d29 RS589to600.d31 RS589to600.d33 RS589to600.d17 (Ns588p601 rfl rfl) (Ns588p605 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p607 := nat_lit 8737567613938460216521807552237524640087399666976345871683572144013306241 

noncomputable def Ns588p608 := nat_lit 3915743140604301097644825911866586623206415919842869061868604222335361 

noncomputable def Ns588p609 := nat_lit 26204871355534172047370133004888840747015786169089351876926979223595248001 

noncomputable def Ns588p610 := BSN.cos_dyadic_bound_f 500151729 536870912 3 2 536870912 268435456 Ns588p607 Ns588p152 Ns588p608 Ns588p609 Ns588p155 Ns588p608 320268440 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 500151729) qz375 0 2 Ns588p607 Ns588p152 Ns588p608 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 500151729) qz376 0 2 Ns588p609 Ns588p155 Ns588p608 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p611 := nat_lit 4241940520616146282743196250625 

noncomputable def Ns588p612 := BSN.sin_dyadic_bound_f 45382785 536870912 2 1 536870912 268435456 Ns588p611 Ns588p188 Ns588p611 Ns588p611 Ns588p189 Ns588p611 45328755 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 45382785) qz373 0 1 Ns588p611 Ns588p188 Ns588p611 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 45382785) qz374 0 1 Ns588p611 Ns588p189 Ns588p611 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p613 := Ns588p546 206834 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 320268440 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 45328755 536870912) qz83 rfl rfl (Ns588p606 rfl) (Ns588p579 rfl) RS589to600.d35 RS589to600.d37 RS589to600.d39 RS589to600.d41 RS589to600.d17 (Ns588p610 rfl rfl) (Ns588p612 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p614 := nat_lit 24301239289668961807212683284854308472953651572749598823954282166892665505 

noncomputable def Ns588p615 := nat_lit 9349750623547842885350996983313724469107397031294900944249652290296481 

noncomputable def Ns588p616 := nat_lit 63630965210028203463742649846169252351452437381055424223113382428629834401 

noncomputable def Ns588p617 := BSN.sin_dyadic_bound_f 557634973 536870912 3 2 536870912 268435456 Ns588p614 Ns588p136 Ns588p615 Ns588p616 Ns588p139 Ns588p615 462639529 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 557634973) qz373 0 2 Ns588p614 Ns588p136 Ns588p615 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 557634973) qz374 0 2 Ns588p616 Ns588p139 Ns588p615 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p618 := nat_lit 127136488783660571448846565751884701498968565319560717118543114582175340359535102167413833912202870577993363940001 

noncomputable def Ns588p619 := nat_lit 44544990313533644034999664643386930957994970417690866284589322069391754488478433887137422709043686132605601 

noncomputable def Ns588p620 := nat_lit 635128555876843795784445062997041877618607444934867562625116015883972660489486737621386020744545072941741556032161 

noncomputable def Ns588p621 := BSN.sin_dyadic_bound_f 771613657 536870912 4 3 536870912 268435456 Ns588p618 Ns588p172 Ns588p619 Ns588p620 Ns588p175 Ns588p619 532090037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 771613657) qz373 0 3 Ns588p618 Ns588p172 Ns588p619 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 771613657) qz374 0 3 Ns588p620 Ns588p175 Ns588p619 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz634 := (BSN.cos_quad_nat3 231 rfl)

noncomputable def Ns588p622 := Ns588p544 240933 BSN.abs_quadSignPos (BSN.cos_quad_nat3 171 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 462639529 536870912) BSN.abs_quadSignPos qz634 (BSN.sfrac_eq_quadSignPos_mul Bool.false 532090037 536870912) qz83 rfl rfl (Ns588p613 rfl) (Ns588p579 rfl) RS589to600.d43 RS589to600.d45 RS589to600.d47 RS589to600.d49 RS589to600.d17 (Ns588p617 rfl rfl) (Ns588p621 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p623 := nat_lit 50548543995199040548731051193729773270293165876583836920105534414790337217009940121217758147010175180502026859121 

noncomputable def Ns588p624 := nat_lit 49029599094850120207042337470782320458400626583919357158118207768117877961366111848895359559692201702896241 

noncomputable def Ns588p625 := nat_lit 306126197734367783354545487608584998050279293560663100999716613299826897575976711159934688943543623352251962798705 

noncomputable def Ns588p626 := BSN.cos_dyadic_bound_f 777806429 536870912 4 3 536870912 268435456 Ns588p623 Ns588p146 Ns588p624 Ns588p625 Ns588p149 Ns588p624 65345993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 777806429) qz375 0 3 Ns588p623 Ns588p146 Ns588p624 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 777806429) qz376 0 3 Ns588p625 Ns588p149 Ns588p624 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p627 := Ns588p542 Bool.false 99302834 240933 Bool.true 777806429 28296951008113761 1 Bool.false 65345993 Bool.true Bool.false 80439070 256869 BSN.abs_quadSignNeg qz398 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65345993 536870912) qz83 rfl (Ns588p622 rfl) (Ns588p579 rfl) RS589to600.d51 RS589to600.d53 RS589to600.d17 (Ns588p626 rfl rfl) rfl 

noncomputable def Ns588p628 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) 80439070 536870912 256869 536870912 80439070 536870912 256869 536870912 86370793742663680 40219535 134217728 256869 268435456 (Ns588p627 rfl rfl rfl rfl) 

noncomputable def Ns588p629 := @Enclosure.Real.IsNear.mulLit_ff qz630 (Zeta.RiemannSiegel.correction qz82) 4731771 16777216 1 33554432 882070985130887 2251799813685248 218974963396399 20435083309193625600 4173757907383762310877 37778931862957161709568 

noncomputable abbrev qz635 := (@HPow.hPow Real Real Real qz7 qz81 qz9)

noncomputable def Ns588p630 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz635 1 1 0 1 4731771 16777216 1 33554432 4731771 16777216 1 33554432 

noncomputable def Ns588p631 := @Enclosure.Real.IsNear.sqrt_image qz81 2121263175149 13421772800 198607 13421772800 421834607 421834647 33554432 (@Enclosure.Real.IsNear.of_eq qz81 (@HMul.hMul Real Real Real qz5 qz80 qz3) Bool.false 2121263175149 13421772800 198607 13421772800 (BSN.t_div_two_pi_mk qz80 993035 1000 qz83) (@Enclosure.Real.IsNear.mulLit_ff qz80 qz3 993035 1000 0 1 10680707 67108864 1 67108864 2121263175149 13421772800 198607 13421772800 (Enclosure.Real.IsNear.const Bool.false 993035 1000) RS589to600.d56 rfl)) 

noncomputable abbrev qz759 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 993035 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz636 := qz759

noncomputable abbrev qz430 := qz636

noncomputable abbrev qz89 := qz430

noncomputable def Ns588p632 := @Enclosure.Real.IsNear.sqrt_image qz89 421834627 33554432 5 8388608 118972352 118972359 33554432 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 843669254 67108864 40 67108864 421834627 33554432 5 8388608 (Ns588p631 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns588p633 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz89) 237944711 67108864 7 67108864 9463541 9463543 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz89) Bool.false 237944711 67108864 7 67108864 237944711 67108864 7 67108864 (Ns588p632 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns588p634 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 18927084 67108864 2 67108864 4731771 16777216 1 33554432 (Ns588p633 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz431 := (@HMul.hMul Real Real Real qz588 qz586 qz629)

noncomputable abbrev qz90 := (Real.cos qz431)

noncomputable abbrev qz637 := (@HMul.hMul Real Real Real qz739 qz758 qz758)

noncomputable abbrev qz432 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz637 qz629) qz603)

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz432))

noncomputable def Ns588p635 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz82) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz90) qz91) Bool.false 882070985130887 

noncomputable def Ns588p636 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz90) qz91 74535581 67108864 319 

noncomputable abbrev qz92 := (@Neg.neg Real Real.instNeg (Real.cos qz431))

noncomputable def Ns588p637 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz90) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz92)) Bool.true 74535581 67108864 319 67108864 (BSN.inv_eq_neg_inv_neg qz90) 

noncomputable def Ns588p638 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz92) Bool.false 74535581 67108864 319 67108864 74535581 67108864 

noncomputable def Ns588p639 := @Enclosure.Real.IsNear.recentre' qz90 Bool.true 60422144 67108864 702847216 182703882240000 29503 32768 43927951 11418992640000 

noncomputable abbrev qz93 := qz431

noncomputable def Ns588p640 := @Enclosure.Real.IsNear.cos_image qz93 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 241041121) qz371) Bool.false 241041121 67108864 63 16777216 Bool.true 60422144 67108864 1 

noncomputable def Ns588p641 := nat_lit 134930377086412062463388899 

noncomputable def Ns588p642 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz82 884279719003555 140737488355328 1 500000000000000 19181443 33554432 5 8388608 16961761026122707029865 4722366482869645213696 Ns588p641 

noncomputable def Ns588p643 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz1 421834627 33554432 5 8388608 12 1 0 1 19181443 19181443 33554432 5 

noncomputable def Ns588p644 := @Ns588p643 8388608 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 843669254 67108864 40 67108864 421834627 33554432 5 8388608 (Ns588p631 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns588p645 := @Enclosure.Real.IsNear.recentre' qz93 Bool.false 16961761026122707029865 4722366482869645213696 Ns588p641 Ns588p206 241041121 67108864 63 16777216 (@Ns588p642 Ns588p206 RS589to600.d55 (Ns588p644 rfl rfl) rfl) 

noncomputable def Ns588p646 := nat_lit 4354066697839424959414272 

noncomputable def Ns588p647 := nat_lit 8786590105198419642993921760091225088879130513967117165079374101394304420909423446519145601 

noncomputable def Ns588p648 := nat_lit 214843498436926818965480151834557173259147470149944483928857763164465429748135680238721 

noncomputable def Ns588p649 := nat_lit 26359340628598385075343834319970006152290873246961051606270264588656584331868774068196959361 

noncomputable def Ns588p650 := BSN.cos_dyadic_bound_f 61875009263 137438953472 3 2 67108864 21801270 Ns588p647 Ns588p511 Ns588p648 Ns588p649 Ns588p514 Ns588p648 60422144 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 61875009263) qz383 0 2 Ns588p647 Ns588p511 Ns588p648 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 61875009263) qz384 0 2 Ns588p649 Ns588p514 Ns588p648 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p651 := @Ns588p640 10890000 (Ns588p645 rfl) (Enclosure.sfrac_false_div 241041121 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 241041121) qz371) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns588p646) qz372) 226375608064910080 72057594037927936 Bool.false 60422144 67108864 0 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 241041121 67108864 226375608064910080 72057594037927936 0 Ns588p646 Ns588p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 60422144 67108864 Ns588p646 Ns588p114 61875009263 137438953472 21801270 21780000 (Ns588p650 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p652 := @Enclosure.Real.IsNear.inv_image qz92 29503 32768 43927951 11418992640000 37267631 37267950 33554432 (@Enclosure.Real.IsNear.neg qz90 Bool.true 29503 32768 43927951 11418992640000 (Ns588p639 (Ns588p651 rfl rfl) rfl)) 

noncomputable def Ns588p653 := Ns588p637 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz92) Bool.false 74535581 67108864 319 67108864 (@Ns588p638 319 67108864 (Ns588p652 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p654 := @Enclosure.Real.IsNear.recentre' qz91 Bool.true 11834227 33554432 

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz355 qz352 qz432)

noncomputable def Ns588p655 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32400795)) qz381) Bool.true 32400795 16777216 

noncomputable def Ns588p656 := nat_lit 306016857977148149672439912005 

noncomputable def Ns588p657 := nat_lit 158456325028528675187087900672 

noncomputable def Ns588p658 := nat_lit 4851916766585854945462982324987399 

noncomputable def Ns588p659 := @Enclosure.Real.IsNear.recentre' qz94 Bool.true Ns588p656 Ns588p657 Ns588p658 

noncomputable def Ns588p660 := nat_lit 604462909807314587353088000000000000000 

noncomputable abbrev qz95 := qz432

noncomputable def Ns588p661 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz95 884279719003555 140737488355328 1 500000000000000 346063413420791 

noncomputable abbrev qz433 := (@HSub.hSub Real Real Real qz592 qz637 qz629)

noncomputable abbrev qz96 := qz433

noncomputable def Ns588p662 := @Enclosure.Real.IsNear.subLit_tf qz96 qz31 275694669243127 1125899906842624 179793345 140737488355328 1 16 

noncomputable abbrev qz434 := qz637

noncomputable abbrev qz97 := qz434

noncomputable def Ns588p663 := @Enclosure.Real.IsNear.subLit_ff_n qz97 qz82 367927755562249 1125899906842624 95907265 140737488355328 19181443 33554432 5 8388608 

noncomputable def Ns588p664 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz82 19181443 33554432 5 8388608 19181443 33554432 5 8388608 367927755562249 1125899906842624 

noncomputable def Ns588p665 := nat_lit 139217205686122932179388867820024485308049698151379958669746545217816359092698706225557038140625 

noncomputable def Ns588p666 := nat_lit 1338652941116445021679458403237259839658764849808306781801554168859510694298927656494140625 

noncomputable def Ns588p667 := nat_lit 839953785995739034318367561439053825476238312539788676150879843205871934374145654107408327740625 

noncomputable def Ns588p668 := BSN.cos_dyadic_bound_t 32400795 16777216 4 3 33554432 10890000 Ns588p665 Ns588p531 Ns588p666 Ns588p667 Ns588p534 Ns588p666 11834227 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32400795) (BSN.cosEvenQ 16777216) 0 3 Ns588p665 Ns588p531 Ns588p666 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32400795) (BSN.cosOddQ 16777216) 0 3 Ns588p667 Ns588p534 Ns588p666 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p669 := @Ns588p654 1486927216 182703882240000 11834227 33554432 92932951 11418992640000 (@Ns588p655 135 16777216 Bool.true 11834227 33554432 1 10890000 (@Ns588p659 Ns588p660 32400795 16777216 135 16777216 (@Ns588p661 1125899906842624 179793345 140737488355328 Ns588p656 Ns588p657 Ns588p658 Ns588p660 RS589to600.d55 (@Ns588p662 0 1 5537014614732656 346063413420791 1125899906842624 179793345 140737488355328 (@Ns588p663 9250778031880996388864 275694669243127 1125899906842624 179793345 140737488355328 (@Ns588p664 95907265 140737488355328 (Ns588p644 rfl rfl) (Ns588p644 rfl rfl) rfl) (Ns588p644 rfl rfl) rfl rfl) qz388 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32400795 16777216) (BSN.cos_neg_of_bound 32400795 16777216 Bool.true 11834227 33554432 1 10890000 (Ns588p668 rfl rfl)) rfl rfl) 

noncomputable def Ns588p670 := @Ns588p629 1040141888107655390591 Ns588p539 (Ns588p630 qz33 (@Enclosure.Real.IsNear.of_eq qz635 (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 4731771 16777216 1 33554432 (BSN.rpow_neg_quarter_mk qz81 (BSN.t_div_two_pi_nonneg qz80 993035 1000 qz83)) Ns588p634) rfl) (@Ns588p635 2251799813685248 218974963396399 20435083309193625600 (BSN.correction_mk qz82 (BSN.cos_two_pi_p_ne_zero_mk qz80 993035 1000 12 qz83 rfl rfl (@BSN.floor_sqrt_eq_dec qz80 993035 1000 12 qz83 rfl rfl rfl))) (@Ns588p636 67108864 11834227 33554432 92932951 11418992640000 882070985130887 2251799813685248 218974963396399 20435083309193625600 Ns588p653 (Ns588p669 rfl) rfl)) 

noncomputable def Ns588p671 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (hardyZApproximantRS₀ qz80) Bool.false 7147034770054651554083 37778931862957161709568 329111355297436243780991 Ns588p539 (@Eq.refl Real (hardyZApproximantRS₀ qz80)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HMul.hMul Real Real Real qz5 qz630 (Zeta.RiemannSiegel.correction qz82))) Bool.false 7147034770054651554083 37778931862957161709568 329111355297436243780991 Ns588p539 (BSN.hardyZApproximantRS₀_eq qz80 12 (@BSN.floor_sqrt_eq_dec qz80 993035 1000 12 qz83 rfl rfl rfl)) (@Ns588p541 7147034770054651554083 37778931862957161709568 329111355297436243780991 Ns588p539 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12)) Bool.false 40219535 134217728 256869 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (Ns588p628 (Ns588p627 rfl rfl rfl rfl) rfl rfl)) (Ns588p670 rfl) rfl rfl)) 

theorem RS589to600.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz80) Bool.false 7147034770054651554083 37778931862957161709568 329111355297436243780991 Ns588p539 := Ns588p671 

noncomputable def Ns588p672 := nat_lit 3089389395164512680861727 

noncomputable def Ns588p673 := nat_lit 46977068980167063729332027392 

noncomputable abbrev qz760 := (Enclosure.sfrac Bool.false 994276 1000)

noncomputable abbrev qz638 := qz760

noncomputable abbrev qz435 := qz638

noncomputable abbrev qz98 := qz435

noncomputable abbrev qz761 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 994276 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz639 := qz761

noncomputable abbrev qz436 := qz639

noncomputable abbrev qz99 := qz436

noncomputable abbrev qz762 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 994276 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz640 := qz762

noncomputable abbrev qz437 := qz640

noncomputable abbrev qz100 := qz437

noncomputable abbrev qz641 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz99 qz9))

noncomputable def Ns588p674 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HMul.hMul Real Real Real qz5 qz641 (Zeta.RiemannSiegel.correction qz100)) 129358125 268435456 128587 134217728 32772456737191205707 295147905179352825856 10069796555980569501727 Ns588p86 Ns588p673 

noncomputable def Ns588p675 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos BSN.quadSignNeg 11 12 994276 1000 286 536870912 268435456 9007199254740992 Bool.false 1084503210784 4528 1334074092 51 154981288 8 

noncomputable def Ns588p676 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 9 10 11 994276 1000 171 231 536870912 268435456 9007199254740992 Bool.false 1084503210784 4528 

noncomputable def Ns588p677 := Ns588p676 1236190956 51 169773496 8 1287360220 51 161872664 8 Bool.true 372499873 207077 Bool.true 404947716 Bool.true 682427457 28296951008113761 1 Bool.false 367627558 Bool.false Bool.false 512943728 Bool.false Bool.true 101587481 

noncomputable def Ns588p678 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 994276 1000 30 104 536870912 268435456 9007199254740992 Bool.false 1084503210784 4528 

noncomputable def Ns588p679 := Ns588p678 1116391676 51 189812536 8 1179625948 51 178956968 8 Bool.true 253646959 169117 Bool.true 198793566 Bool.true 665813210 28296951008113761 1 Bool.false 500484689 Bool.true Bool.false 174285452 Bool.false Bool.true 372499873 

noncomputable def Ns588p680 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 994276 1000 151 54 536870912 268435456 9007199254740992 Bool.false 1084503210784 4528 

noncomputable def Ns588p681 := Ns588p680 961943533 51 219176632 8 1044702541 51 202918136 8 Bool.true 284824642 125670 Bool.false 725299230 Bool.false 241544875 28296951008113761 1 Bool.false 523951889 Bool.false Bool.false 483444313 Bool.true Bool.true 253646959 

noncomputable def Ns588p682 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 994276 1000 408 267 536870912 268435456 9007199254740992 Bool.false 1084503210784 4528 

noncomputable def Ns588p683 := Ns588p682 744261104 50 268435448 8 864060384 50 240095976 8 Bool.true 568886148 74271 Bool.false 429795877 Bool.false 223641727 28296951008113761 1 Bool.false 373826913 Bool.false Bool.false 217229651 Bool.false Bool.true 284824642 

noncomputable def Ns588p684 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 994276 1000 847 590 536870912 268435456 9007199254740992 Bool.false 1084503210784 4528 

noncomputable def Ns588p685 := Ns588p684 372130544 50 379625064 8 589812976 50 309962568 8 Bool.true 536870824 4578 Bool.false 215058534 Bool.false 510558904 28296951008113761 1 Bool.false 209353030 Bool.false Bool.false 311856216 Bool.true Bool.true 568886148 

noncomputable def Ns588p686 := nat_lit 2414100717757527203933373939938017991097454821551101907 

noncomputable def Ns588p687 := nat_lit 1195072952402765045897485135866941933062295912448000 

noncomputable def Ns588p688 := nat_lit 466419069225459094412552138260480000 

noncomputable def Ns588p689 := nat_lit 2782496047212660885177285261142398074880 

noncomputable abbrev qz642 := (@Eq.refl Real qz760)

noncomputable abbrev qz438 := qz642

noncomputable abbrev qz101 := qz438

noncomputable def Ns588p690 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz98 994276 1000 3954340056704 16000000 1988552 4000 2000 Ns588p688 Ns588p689 qz101 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns588p691 := nat_lit 25313680742233168453916415124444471530330047869627682332344320 

noncomputable abbrev qz643 := (@HSub.hSub Real Real Real qz743 qz744 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz745 (@Nat.cast Real Real.instNatCast 1988552))))

noncomputable abbrev qz439 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 994276 4000) (Real.log (Enclosure.sfrac Bool.false 3954340056704 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz643))

noncomputable abbrev qz644 := (Enclosure.sfrac Bool.false 994276 2000)

noncomputable abbrev qz102 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz439 qz644) (@HMul.hMul Real Real Real qz355 qz644 (Real.log Real.pi)))

noncomputable def Ns588p692 := @Enclosure.Real.IsNear.addLit_ft_p qz102 (Enclosure.sfrac Bool.true Ns588p688 Ns588p689) 9097473064932349979839 4503599627370496000 379916278337007813 45056000000000000000000 Ns588p688 Ns588p689 0 1 Ns588p691 

noncomputable def Ns588p693 := nat_lit 152630270664552060999354548224000 

noncomputable abbrev qz103 := (@HSub.hSub Real Real Real qz359 qz439 qz644)

noncomputable def Ns588p694 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (@HMul.hMul Real Real Real qz5 qz644 (Real.log Real.pi)) 11660420831701300554943 4503599627370496000 15818773241889 5500000000000000000 9547724451009 16777216000 745707 134217728000 Ns588p693 9097473064932349979839 4503599627370496000 

noncomputable def Ns588p695 := nat_lit 23320841663402601109886000 

noncomputable abbrev qz104 := qz439

noncomputable def Ns588p696 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz644 13899331343253014195391 4503599627370496000 15818773241889 5500000000000000000 994276 2000 0 1 Ns588p695 11660420831701300554943 4503599627370496000 15818773241889 5500000000000000000 

noncomputable def Ns588p697 := nat_lit 31298511729086665181169240733246291968 

noncomputable def Ns588p698 := nat_lit 120096969108841308641820672 

noncomputable def Ns588p699 := nat_lit 111457040570277068237291539065302346945299083647327166048793947020095341732413825842386987276266143108247347266636289413956508535983571265067023963818022612874228901269011990102356699084252446389387252932070604800 

noncomputable def Ns588p700 := nat_lit 3711342156759586636146541575241373151160210358598841273679345811403450138858307635349226531951551395665465151661531086378872751006286355990430922723965617146137552426488615112772289679624941530500452467374817280 

noncomputable def Ns588p701 := nat_lit 40602541504196299341110454107459708271730131149649080974502890175038238235946072657374610249169969901756512983851007647826308144911687525315775107411200433842868692281397594272647770106320191607957094400 

noncomputable def Ns588p702 := BSN.log_dyadic_bound 1857188056704 6051492056704 9 8 Ns588p699 268435456 87120000 Ns588p700 Ns588p701 170250756 7908680113408 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1857188056704) (BSN.artanhQ 6051492056704) 0 8 Ns588p700 Ns588p699 Ns588p701 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz440 := (Real.log (Enclosure.sfrac Bool.false 3954340056704 16000000))

noncomputable def Ns588p703 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 994276 4000) qz440 994276 4000 0 1 55924509236980839 4503599627370496 12500018513 1089000000000000000 13901099336527090169391 4503599627370496000 3107117101757897 1089000000000000000000 (Enclosure.Real.IsNear.const Bool.false 994276 4000) (BSN.isNear_log_sfrac 3954340056704 16000000 55924509236980839 4503599627370496 12500018513 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3954340056704) qz362)) Bool.false Ns588p698 Ns588p114 1000001481040000 87120000000000000000000 55924509236980839 4503599627370496 12500018513 1089000000000000000 (BSN.log_rat_reduce_isNear 3954340056704 16000000 17 7908680113408 4194304000000 170250756 268435456 24973259072661432 36028797018963968 87120000 1000000000000000 rfl rfl rfl rfl (Ns588p702 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p704 := BSN.arctan_dyadic_bound_f 1000 1988552 1 0 33554432 10890000 0 1 1 0 1 1 16873 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1988552) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1988552) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns588p705 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1988552))) 884279719003555 562949953421312 1 2000000000000000 16873 33554432 1 10890000 29662005045719816208384 883996637037987 562949953421312 200000001089 2178000000000000000 qz17 (Ns588p704 rfl) rfl rfl 

noncomputable abbrev qz441 := (@HMul.hMul Real Real Real qz588 qz593 qz643)

noncomputable abbrev qz105 := qz441

noncomputable abbrev qz442 := qz643

noncomputable abbrev qz106 := qz442

noncomputable def Ns588p706 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 994276 4000) qz440) qz105 13901099336527090169391 4503599627370496000 3107117101757897 1089000000000000000000 883996637037987 2251799813685248 200000001089 8712000000000000000 Ns588p697 13899331343253014195391 4503599627370496000 15818773241889 5500000000000000000 (Ns588p703 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz106 1 4 0 1 883996637037987 562949953421312 200000001089 2178000000000000000 883996637037987 2251799813685248 200000001089 8712000000000000000 qz369 Ns588p705 rfl) 

noncomputable def Ns588p707 := @Ns588p692 Ns588p686 Ns588p687 379916278337007813 45056000000000000000000 (@Ns588p694 379916278337007813 45056000000000000000000 (Ns588p696 (Ns588p706 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 994276 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz644 (Real.log Real.pi) 994276 2000 0 1 38410761 33554432 3 268435456 9547724451009 16777216000 745707 134217728000 (Enclosure.Real.IsNear.const Bool.false 994276 2000) RS589to600.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns588p688 Ns588p689) 

noncomputable def Ns588p708 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns588p686 Ns588p687 379916278337007813 45056000000000000000000 33890725337 16777216 283 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz370 qz102 (Enclosure.sfrac Bool.true Ns588p688 Ns588p689)) Bool.false Ns588p686 Ns588p687 379916278337007813 45056000000000000000000 Ns588p690 (Ns588p707 rfl rfl)) 

noncomputable def Ns588p709 := BSN.cos_dyadic_bound_f 78152458 137438953472 1 0 67108864 21801270 0 1 1 0 1 1 67108853 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 78152458) qz383 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 78152458) qz384 0 0 rfl) rfl rfl 

noncomputable def Ns588p710 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz98) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 33890725337) qz381) Bool.false 33890725337 16777216 283 33554432 Bool.true 67108853 67108864 1 10890000 (Ns588p708 rfl) (Enclosure.sfrac_false_div 33890725337 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 33890725337) qz381) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1374872597654650486784) (@Nat.cast Real Real.instNatCast Ns588p211)) 226375608064910080 72057594037927936 Bool.false 67108853 67108864 321 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 33890725337 16777216 226375608064910080 72057594037927936 321 1374872597654650486784 Ns588p211 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108853 67108864 1374872597654650486784 Ns588p211 78152458 137438953472 21801270 21780000 (Ns588p709 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p711 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns588p686 Ns588p687 379916278337007813 45056000000000000000000 1084503210784 536870912 4528 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz370 qz102 (Enclosure.sfrac Bool.true Ns588p688 Ns588p689)) Bool.false Ns588p686 Ns588p687 379916278337007813 45056000000000000000000 Ns588p690 (Ns588p707 rfl rfl)) 

noncomputable def Ns588p712 := Ns588p685 74271 BSN.abs_quadSignPos (BSN.cos_quad_nat3 847 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 209353030 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 590 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 311856216 536870912) qz101 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) Bool.true 67108853 67108864 194714027 22837985280000 536870824 536870912 4578 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 67108853 67108864 194714027 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz98) qz98) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 67108853 67108864 3115424432 365407764480000 67108853 67108864 194714027 22837985280000 (Ns588p710 rfl rfl) rfl)) rfl) (Ns588p711 rfl) RS589to600.d7 

noncomputable def Ns588p713 := nat_lit 2139078506806141927425110864472336 

noncomputable def Ns588p714 := BSN.sin_dyadic_bound_f 215058534 536870912 2 1 536870912 268435456 Ns588p713 Ns588p188 Ns588p713 Ns588p713 Ns588p189 Ns588p713 209353030 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 215058534) qz373 0 1 Ns588p713 Ns588p188 Ns588p713 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 215058534) qz374 0 1 Ns588p713 Ns588p189 Ns588p713 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p715 := nat_lit 9364390889618881239422433360886713898665802337270307802685120961258853026574917278769059908573496363890870583296 

noncomputable def Ns588p716 := nat_lit 313725813980631249114466897612426812414756080134928063525818455890181038031142942166610197821193942204416 

noncomputable def Ns588p717 := nat_lit 56792206630599537072638028750432961603483530585470278922478668613121084056052388253602469180977102683197071687680 

noncomputable def Ns588p718 := BSN.cos_dyadic_bound_f 510558904 536870912 4 3 536870912 268435456 Ns588p715 Ns588p146 Ns588p716 Ns588p717 Ns588p149 Ns588p716 311856216 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 510558904) qz375 0 3 Ns588p715 Ns588p146 Ns588p716 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 510558904) qz376 0 3 Ns588p717 Ns588p149 Ns588p716 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p719 := nat_lit 4763694766334961226328045604692860670350155581731678768416465684706894561 

noncomputable def Ns588p720 := nat_lit 1164388641174914984403506829508227593957383437044626882841168303366881 

noncomputable def Ns588p721 := nat_lit 14288755521722533849015329800419565555862551978320947051483714717513949921 

noncomputable def Ns588p722 := BSN.cos_dyadic_bound_f 429795877 536870912 3 2 536870912 268435456 Ns588p719 Ns588p152 Ns588p720 Ns588p721 Ns588p155 Ns588p720 373826913 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 429795877) qz375 0 2 Ns588p719 Ns588p152 Ns588p720 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 429795877) qz376 0 2 Ns588p721 Ns588p155 Ns588p720 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p723 := nat_lit 628459010804594633780285185100744678364566149111482965891873884938107905 

noncomputable def Ns588p724 := nat_lit 6257814689263122885031541459991758271985327690634803406744842337281 

noncomputable def Ns588p725 := nat_lit 1645953944216822376749409243244348456679518604761432454320820683188403201 

noncomputable def Ns588p726 := BSN.sin_dyadic_bound_f 223641727 536870912 3 2 536870912 268435456 Ns588p723 Ns588p136 Ns588p724 Ns588p725 Ns588p139 Ns588p724 217229651 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 223641727) qz373 0 2 Ns588p723 Ns588p136 Ns588p724 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 223641727) qz374 0 2 Ns588p725 Ns588p139 Ns588p724 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p727 := Ns588p683 125670 BSN.abs_quadSignPos (BSN.cos_quad_nat0 408 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 373826913 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 267 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 217229651 536870912) qz101 rfl rfl (Ns588p712 RS589to600.d9 RS589to600.d11 RS589to600.d13 RS589to600.d17 (Ns588p714 rfl rfl) (Ns588p718 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns588p711 rfl) RS589to600.d19 RS589to600.d21 RS589to600.d23 RS589to600.d25 RS589to600.d17 (Ns588p722 rfl rfl) (Ns588p726 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns588p728 := nat_lit 99221356517333223270518370055575314351116906968129213905816026783472884624630036525896263900377816950670502400000 

noncomputable def Ns588p729 := nat_lit 21193690936794547853892801008878028485652330598219120526203504377558150200469070929955683367921000000000000 

noncomputable def Ns588p730 := nat_lit 495769239022938332635867311331892796955387073921812699427341078455389258470614231111817658580146857832488512000000 

noncomputable def Ns588p731 := BSN.sin_dyadic_bound_f 725299230 536870912 4 3 536870912 268435456 Ns588p728 Ns588p172 Ns588p729 Ns588p730 Ns588p175 Ns588p729 523951889 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 725299230) qz373 0 3 Ns588p728 Ns588p172 Ns588p729 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 725299230) qz374 0 3 Ns588p730 Ns588p175 Ns588p729 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p732 := nat_lit 475106180213253404402739729150634538097573594797376805954032691650390625 

noncomputable def Ns588p733 := nat_lit 11587309784676528114457586922449313562887636456127226352691650390625 

noncomputable def Ns588p734 := nat_lit 1425295366020190860151990272278058715665595009119218163409392691650390625 

noncomputable def Ns588p735 := BSN.cos_dyadic_bound_f 241544875 536870912 3 2 536870912 268435456 Ns588p732 Ns588p152 Ns588p733 Ns588p734 Ns588p155 Ns588p733 483444313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 241544875) qz375 0 2 Ns588p732 Ns588p152 Ns588p733 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 241544875) qz376 0 2 Ns588p734 Ns588p155 Ns588p733 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p736 := Ns588p681 169117 BSN.abs_quadSignPos (BSN.cos_quad_nat3 151 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 523951889 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 483444313 536870912) qz101 rfl rfl (Ns588p727 rfl rfl) (Ns588p711 rfl) RS589to600.d27 RS589to600.d29 RS589to600.d31 RS589to600.d33 RS589to600.d17 (Ns588p731 rfl rfl) (Ns588p735 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p737 := nat_lit 217973117369044073324325546469122268136025347405007253379761880864030976 

noncomputable def Ns588p738 := nat_lit 2439038153532602835033857100503535224604024785908206466917341757696 

noncomputable def Ns588p739 := nat_lit 653914474030825154767306571693165797337626834165449943726351807908577536 

noncomputable def Ns588p740 := BSN.cos_dyadic_bound_f 198793566 536870912 3 2 536870912 268435456 Ns588p737 Ns588p152 Ns588p738 Ns588p739 Ns588p155 Ns588p738 500484689 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 198793566) qz375 0 2 Ns588p737 Ns588p152 Ns588p738 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 198793566) qz376 0 2 Ns588p739 Ns588p155 Ns588p738 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p741 := nat_lit 27108503915315025707922257553531771903244130523580758614344102441960526009311581630824932201361001619192384000000 

noncomputable def Ns588p742 := nat_lit 7589774797676968569336262533633730042574378265446999500118364451811202973250326767436567734241000000000000 

noncomputable def Ns588p743 := nat_lit 164304057790082004160599769612833271212508620487542455726347731485443259790583152216635166279505917111866329600000 

noncomputable def Ns588p744 := BSN.cos_dyadic_bound_f 665813210 536870912 4 3 536870912 268435456 Ns588p741 Ns588p146 Ns588p742 Ns588p743 Ns588p149 Ns588p742 174285452 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 665813210) qz375 0 3 Ns588p741 Ns588p146 Ns588p742 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 665813210) qz376 0 3 Ns588p743 Ns588p149 Ns588p742 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p745 := Ns588p679 207077 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 500484689 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 104 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 174285452 536870912) qz101 rfl rfl (Ns588p736 rfl) (Ns588p711 rfl) RS589to600.d35 RS589to600.d37 RS589to600.d39 RS589to600.d41 RS589to600.d17 (Ns588p740 rfl rfl) (Ns588p744 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p746 := nat_lit 6756216877298310958432551394130015894189906781969906506502905659249459200 

noncomputable def Ns588p747 := nat_lit 723088792571269035236866027544336725352307397586660395546437862096896 

noncomputable def Ns588p748 := nat_lit 17693683011069508550790108249153065082465852121753662447819582493876617216 

noncomputable def Ns588p749 := BSN.sin_dyadic_bound_f 404947716 536870912 3 2 536870912 268435456 Ns588p746 Ns588p136 Ns588p747 Ns588p748 Ns588p139 Ns588p747 367627558 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 404947716) qz373 0 2 Ns588p746 Ns588p136 Ns588p747 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 404947716) qz374 0 2 Ns588p748 Ns588p139 Ns588p747 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p750 := nat_lit 77742563455437501394689613129307618784039511439169890258018634644774700533659193787705568947666281175231164076801 

noncomputable def Ns588p751 := nat_lit 10201825825761888536855905736213315290605730308690593596475263164757885116187420246287114240114096900166401 

noncomputable def Ns588p752 := nat_lit 388505507185088398588019980906185093159823129393911070455465569964028502667213268468895176883530267199797034504961 

noncomputable def Ns588p753 := BSN.sin_dyadic_bound_f 682427457 536870912 4 3 536870912 268435456 Ns588p750 Ns588p172 Ns588p751 Ns588p752 Ns588p175 Ns588p751 512943728 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 682427457) qz373 0 3 Ns588p750 Ns588p172 Ns588p751 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 682427457) qz374 0 3 Ns588p752 Ns588p175 Ns588p751 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p754 := Ns588p677 241218 BSN.abs_quadSignPos (BSN.cos_quad_nat3 171 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 367627558 536870912) BSN.abs_quadSignPos qz634 (BSN.sfrac_eq_quadSignPos_mul Bool.false 512943728 536870912) qz101 rfl rfl (Ns588p745 rfl) (Ns588p711 rfl) RS589to600.d43 RS589to600.d45 RS589to600.d47 RS589to600.d49 RS589to600.d17 (Ns588p749 rfl rfl) (Ns588p753 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p755 := nat_lit 42892799694999328029287207300386812357686447019803632458210142684188036351656670101114624525072297058526111890625 

noncomputable def Ns588p756 := nat_lit 29991693978806086278680148347497750861536669863240836743116747831289114975164801284324455123503965087890625 

noncomputable def Ns588p757 := nat_lit 259830845667396301146252132515910900077773937205619273721121594695531443786520672736149068060623568332651833490625 

noncomputable def Ns588p758 := BSN.cos_dyadic_bound_f 746592145 536870912 4 3 536870912 268435456 Ns588p755 Ns588p146 Ns588p756 Ns588p757 Ns588p149 Ns588p756 96200327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 746592145) qz375 0 3 Ns588p755 Ns588p146 Ns588p756 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 746592145) qz376 0 3 Ns588p757 Ns588p149 Ns588p756 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p759 := Ns588p675 Bool.true 101587481 241218 Bool.true 746592145 28296951008113761 1 Bool.false 96200327 Bool.true Bool.true 129358125 257174 BSN.abs_quadSignNeg qz398 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 96200327 536870912) qz101 rfl (Ns588p754 rfl) (Ns588p711 rfl) RS589to600.d51 RS589to600.d53 RS589to600.d17 (Ns588p758 rfl rfl) rfl 

noncomputable def Ns588p760 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) 129358125 536870912 257174 536870912 129358125 536870912 257174 536870912 138897229086720000 129358125 268435456 128587 134217728 (Ns588p759 rfl rfl rfl rfl) 

noncomputable def Ns588p761 := @Enclosure.Real.IsNear.mulLit_ff qz641 (Zeta.RiemannSiegel.correction qz100) 2365147 8388608 1 33554432 13856414310481 35184372088832 1060406753535143 95789453011845120000 32772456737191205707 295147905179352825856 

noncomputable abbrev qz645 := (@HPow.hPow Real Real Real qz7 qz99 qz9)

noncomputable def Ns588p762 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz645 1 1 0 1 2365147 8388608 1 33554432 2365147 8388608 1 33554432 

noncomputable def Ns588p763 := @Enclosure.Real.IsNear.sqrt_image qz99 2654892658283 16777216000 248569 16777216000 422098109 422098149 33554432 (@Enclosure.Real.IsNear.of_eq qz99 (@HMul.hMul Real Real Real qz5 qz98 qz3) Bool.false 2654892658283 16777216000 248569 16777216000 (BSN.t_div_two_pi_mk qz98 994276 1000 qz101) (@Enclosure.Real.IsNear.mulLit_ff qz98 qz3 994276 1000 0 1 10680707 67108864 1 67108864 2654892658283 16777216000 248569 16777216000 (Enclosure.Real.IsNear.const Bool.false 994276 1000) RS589to600.d56 rfl)) 

noncomputable abbrev qz763 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 994276 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz646 := qz763

noncomputable abbrev qz443 := qz646

noncomputable abbrev qz107 := qz443

noncomputable def Ns588p764 := @Enclosure.Real.IsNear.sqrt_image qz107 422098129 33554432 5 8388608 119009505 119009511 33554432 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 844196258 67108864 40 67108864 422098129 33554432 5 8388608 (Ns588p763 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns588p765 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 29752377 8388608 3 33554432 9460587 9460589 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 238019016 67108864 6 67108864 29752377 8388608 3 33554432 (Ns588p764 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns588p766 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 18921176 67108864 2 67108864 2365147 8388608 1 33554432 (Ns588p765 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz444 := (@HMul.hMul Real Real Real qz588 qz586 qz640)

noncomputable abbrev qz108 := (Real.cos qz444)

noncomputable abbrev qz647 := (@HMul.hMul Real Real Real qz739 qz762 qz762)

noncomputable abbrev qz445 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz647 qz640) qz603)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz445))

noncomputable def Ns588p767 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz100) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz108) qz109) Bool.false 13856414310481 

noncomputable def Ns588p768 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz108) qz109 1194547 1048576 21 

noncomputable abbrev qz110 := (@Neg.neg Real Real.instNeg (Real.cos qz444))

noncomputable def Ns588p769 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz108) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz110)) Bool.true 1194547 1048576 21 4194304 (BSN.inv_eq_neg_inv_neg qz108) 

noncomputable def Ns588p770 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz110) Bool.false 76451008 67108864 336 67108864 1194547 1048576 

noncomputable def Ns588p771 := @Enclosure.Real.IsNear.recentre' qz108 Bool.true 58908310 67108864 702847216 182703882240000 29454155 33554432 43927951 11418992640000 

noncomputable abbrev qz111 := qz444

noncomputable def Ns588p772 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 244352385) qz371) Bool.false 244352385 67108864 63 16777216 Bool.true 58908310 67108864 1 

noncomputable def Ns588p773 := nat_lit 26986075417395585739920839 

noncomputable def Ns588p774 := nat_lit 7205759403792793600000000000000 

noncomputable def Ns588p775 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz100 884279719003555 140737488355328 1 500000000000000 19444945 33554432 5 8388608 17194770500639581779475 4722366482869645213696 Ns588p773 

noncomputable def Ns588p776 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz1 422098129 33554432 5 8388608 12 1 0 1 19444945 19444945 33554432 5 

noncomputable def Ns588p777 := @Ns588p776 8388608 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 844196258 67108864 40 67108864 422098129 33554432 5 8388608 (Ns588p763 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns588p778 := @Enclosure.Real.IsNear.recentre' qz111 Bool.false 17194770500639581779475 4722366482869645213696 Ns588p773 Ns588p774 244352385 67108864 63 16777216 (@Ns588p775 Ns588p774 RS589to600.d55 (Ns588p777 rfl rfl) rfl) 

noncomputable def Ns588p779 := nat_lit 4831270131968235777556480 

noncomputable def Ns588p780 := nat_lit 13319588845084023408238726256472198958389200587582437774639516595219662961695979011539690625 

noncomputable def Ns588p781 := nat_lit 493687536703117430352212901737299942490696405846759089313557057110244738484941062890625 

noncomputable def Ns588p782 := nat_lit 39957779160178663989855474343613122275282620369935619805739922671544768395610967152493290625 

noncomputable def Ns588p783 := BSN.cos_dyadic_bound_f 68656477935 137438953472 3 2 67108864 21801270 Ns588p780 Ns588p511 Ns588p781 Ns588p782 Ns588p514 Ns588p781 58908310 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 68656477935) qz383 0 2 Ns588p780 Ns588p511 Ns588p781 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 68656477935) qz384 0 2 Ns588p782 Ns588p514 Ns588p781 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p784 := @Ns588p772 10890000 (Ns588p778 rfl) (Enclosure.sfrac_false_div 244352385 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 244352385) qz371) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns588p779) qz372) 226375608064910080 72057594037927936 Bool.false 58908310 67108864 0 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 244352385 67108864 226375608064910080 72057594037927936 0 Ns588p779 Ns588p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 58908310 67108864 Ns588p779 Ns588p114 68656477935 137438953472 21801270 21780000 (Ns588p783 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p785 := @Enclosure.Real.IsNear.inv_image qz110 29454155 33554432 43927951 11418992640000 38225336 38225672 33554432 (@Enclosure.Real.IsNear.neg qz108 Bool.true 29454155 33554432 43927951 11418992640000 (Ns588p771 (Ns588p784 rfl rfl) rfl)) 

noncomputable def Ns588p786 := Ns588p769 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz110) Bool.false 1194547 1048576 21 4194304 (@Ns588p770 21 4194304 (Ns588p785 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p787 := @Enclosure.Real.IsNear.recentre' qz109 Bool.true 11599723 33554432 

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz355 qz352 qz445)

noncomputable def Ns588p788 := @Enclosure.Real.IsNear.cos_image qz112 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 64551331)) qz397) Bool.true 64551331 33554432 

noncomputable def Ns588p789 := nat_lit 304835044174815439684906974845 

noncomputable def Ns588p790 := nat_lit 4887471190796589541464637196780081 

noncomputable def Ns588p791 := @Enclosure.Real.IsNear.recentre' qz112 Bool.true Ns588p789 Ns588p657 Ns588p790 

noncomputable abbrev qz113 := qz445

noncomputable def Ns588p792 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz113 884279719003555 140737488355328 1 500000000000000 344726942870879 

noncomputable abbrev qz446 := (@HSub.hSub Real Real Real qz592 qz647 qz640)

noncomputable abbrev qz114 := qz446

noncomputable def Ns588p793 := @Enclosure.Real.IsNear.subLit_tf qz114 qz31 274358198693215 1125899906842624 181110855 140737488355328 1 16 

noncomputable abbrev qz447 := qz647

noncomputable abbrev qz115 := qz447

noncomputable def Ns588p794 := @Enclosure.Real.IsNear.subLit_ff_n qz115 qz100 378105886053025 1125899906842624 97224775 140737488355328 19444945 33554432 5 8388608 

noncomputable def Ns588p795 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz100 19444945 33554432 5 8388608 19444945 33554432 5 8388608 378105886053025 1125899906842624 

noncomputable def Ns588p796 := nat_lit 561404788899593564521378150682039781785308032891131653406909557449746938346395809223934456558985841 

noncomputable def Ns588p797 := nat_lit 5234345895472089198135190031767750432080051711402007950658340138389162140672038613354760053361 

noncomputable def Ns588p798 := nat_lit 3387467346179715549185321686254511275286403438006000904811255231124317883421314658966603614649262705 

noncomputable def Ns588p799 := BSN.cos_dyadic_bound_t 64551331 33554432 4 3 33554432 10890000 Ns588p796 Ns588p361 Ns588p797 Ns588p798 Ns588p364 Ns588p797 11599723 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 64551331) (BSN.cosEvenQ 33554432) 0 3 Ns588p796 Ns588p361 Ns588p797 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 64551331) (BSN.cosOddQ 33554432) 0 3 Ns588p798 Ns588p364 Ns588p797 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p800 := @Ns588p787 187227152 22837985280000 11599723 33554432 11701697 1427374080000 (@Ns588p788 17 2097152 Bool.true 11599723 33554432 1 10890000 (@Ns588p791 Ns588p660 64551331 33554432 17 2097152 (@Ns588p792 1125899906842624 181110855 140737488355328 Ns588p789 Ns588p657 Ns588p790 Ns588p660 RS589to600.d55 (@Ns588p793 0 1 5515631085934064 344726942870879 1125899906842624 181110855 140737488355328 (@Ns588p794 9205933521693971578880 274358198693215 1125899906842624 181110855 140737488355328 (@Ns588p795 97224775 140737488355328 (Ns588p777 rfl rfl) (Ns588p777 rfl rfl) rfl) (Ns588p777 rfl rfl) rfl rfl) qz388 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 64551331 33554432) (BSN.cos_neg_of_bound 64551331 33554432 Bool.true 11599723 33554432 1 10890000 (Ns588p799 rfl rfl)) rfl rfl) 

noncomputable def Ns588p801 := @Ns588p761 10069796555980569501727 Ns588p86 (Ns588p762 qz33 (@Enclosure.Real.IsNear.of_eq qz645 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 2365147 8388608 1 33554432 (BSN.rpow_neg_quarter_mk qz99 (BSN.t_div_two_pi_nonneg qz98 994276 1000 qz101)) Ns588p766) rfl) (@Ns588p767 35184372088832 1060406753535143 95789453011845120000 (BSN.correction_mk qz100 (BSN.cos_two_pi_p_ne_zero_mk qz98 994276 1000 12 qz101 rfl rfl (@BSN.floor_sqrt_eq_dec qz98 994276 1000 12 qz101 rfl rfl rfl))) (@Ns588p768 4194304 11599723 33554432 11701697 1427374080000 13856414310481 35184372088832 1060406753535143 95789453011845120000 Ns588p786 (Ns588p800 rfl) rfl)) 

noncomputable def Ns588p802 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (hardyZApproximantRS₀ qz98) Bool.true 175003219321992485707 295147905179352825856 Ns588p672 Ns588p86 (@Eq.refl Real (hardyZApproximantRS₀ qz98)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HMul.hMul Real Real Real qz5 qz641 (Zeta.RiemannSiegel.correction qz100))) Bool.true 175003219321992485707 295147905179352825856 Ns588p672 Ns588p86 (BSN.hardyZApproximantRS₀_eq qz98 12 (@BSN.floor_sqrt_eq_dec qz98 994276 1000 12 qz101 rfl rfl rfl)) (@Ns588p674 175003219321992485707 295147905179352825856 Ns588p672 Ns588p86 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12)) Bool.true 129358125 268435456 128587 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (Ns588p760 (Ns588p759 rfl rfl rfl rfl) rfl rfl)) (Ns588p801 rfl) rfl rfl)) 

theorem RS589to600.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz98) Bool.true 175003219321992485707 295147905179352825856 Ns588p672 Ns588p86 := Ns588p802 

noncomputable def Ns588p803 := nat_lit 2750191611708841905656299 

noncomputable def Ns588p804 := nat_lit 2857031722136135354286080000 

noncomputable def Ns588p805 := nat_lit 47100814557582672329040287760384 

noncomputable abbrev qz764 := (Enclosure.sfrac Bool.false 995516 1000)

noncomputable abbrev qz648 := qz764

noncomputable abbrev qz448 := qz648

noncomputable abbrev qz116 := qz448

noncomputable abbrev qz765 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 995516 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz649 := qz765

noncomputable abbrev qz449 := qz649

noncomputable abbrev qz117 := qz449

noncomputable abbrev qz766 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 995516 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz650 := qz766

noncomputable abbrev qz450 := qz650

noncomputable abbrev qz118 := qz450

noncomputable abbrev qz651 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz117 qz9))

noncomputable def Ns588p806 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HMul.hMul Real Real Real qz5 qz651 (Zeta.RiemannSiegel.correction qz118)) 1276721319 268435456 257507 268435456 4218344244745084677993 37778931862957161709568 9474425406486203896299 Ns588p804 Ns588p805 

noncomputable def Ns588p807 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos BSN.quadSignNeg 11 12 995516 1000 286 536870912 268435456 9007199254740992 Bool.false 1086189066911 4534 1334074092 51 154981288 8 

noncomputable def Ns588p808 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 9 10 11 995516 1000 171 231 536870912 268435456 9007199254740992 Bool.false 1086189066911 4534 

noncomputable def Ns588p809 := Ns588p808 1236190956 51 169773496 8 1287360220 51 161872664 8 Bool.false 1092047307 207347 Bool.true 251968375 Bool.true 592898003 28296951008113761 1 Bool.false 242819603 Bool.false Bool.false 479520174 Bool.false Bool.false 1313414377 

noncomputable def Ns588p810 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 995516 1000 29 104 536870912 268435456 9007199254740992 Bool.false 1086189066911 4534 

noncomputable def Ns588p811 := Ns588p810 1116391676 51 189812536 8 1179625948 51 178956968 8 Bool.false 1156907374 169339 Bool.true 740577974 Bool.true 442693258 28296951008113761 1 Bool.false 527070886 Bool.true Bool.false 364462917 Bool.false Bool.false 1092047307 

noncomputable def Ns588p812 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 995516 1000 152 54 536870912 268435456 9007199254740992 Bool.false 1086189066911 4534 

noncomputable def Ns588p813 := Ns588p812 961943533 51 219176632 8 1044702541 51 202918136 8 Bool.false 1066900766 125837 Bool.false 375030520 Bool.false 631969852 28296951008113761 1 Bool.false 411123011 Bool.false Bool.false 205928498 Bool.true Bool.false 1156907374 

noncomputable def Ns588p814 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 995516 1000 409 267 536870912 268435456 9007199254740992 Bool.false 1086189066911 4534 

noncomputable def Ns588p815 := Ns588p814 744261104 50 268435448 8 864060384 50 240095976 8 Bool.false 989463656 74374 Bool.false 349453379 Bool.false 838062978 28296951008113761 1 Bool.false 325294764 Bool.true Bool.false 536845224 Bool.false Bool.false 1066900766 

noncomputable def Ns588p816 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 995516 1000 848 591 536870912 268435456 9007199254740992 Bool.false 1086189066911 4534 

noncomputable def Ns588p817 := Ns588p816 372130544 50 379625064 8 589812976 50 309962568 8 Bool.false 536870704 4594 Bool.false 596157930 Bool.false 621732084 28296951008113761 1 Bool.false 238518710 Bool.false Bool.false 491789417 Bool.false Bool.false 989463656 

noncomputable def Ns588p818 := nat_lit 2436002317097851202475735411244952097272713741097368237 

noncomputable def Ns588p819 := nat_lit 1204043407776899988240563459791723565787610349568000 

noncomputable def Ns588p820 := nat_lit 4460544000000000000000000 

noncomputable def Ns588p821 := nat_lit 469334778176072012055731498516480000 

noncomputable def Ns588p822 := nat_lit 2803382016198942410388410696274888622080 

noncomputable abbrev qz652 := (@Eq.refl Real qz764)

noncomputable abbrev qz451 := qz652

noncomputable abbrev qz119 := qz451

noncomputable def Ns588p823 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz116 995516 1000 3964209425024 16000000 1991032 4000 2000 Ns588p821 Ns588p822 qz119 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns588p824 := nat_lit 25543335656531964224871967345815868903498330837849139964805120 

noncomputable abbrev qz653 := (@HSub.hSub Real Real Real qz743 qz744 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz745 (@Nat.cast Real Real.instNatCast 1991032))))

noncomputable abbrev qz452 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 995516 4000) (Real.log (Enclosure.sfrac Bool.false 3964209425024 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz653))

noncomputable abbrev qz654 := (Enclosure.sfrac Bool.false 995516 2000)

noncomputable abbrev qz120 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz452 qz654) (@HMul.hMul Real Real Real qz355 qz654 (Real.log Real.pi)))

noncomputable def Ns588p825 := @Enclosure.Real.IsNear.addLit_ft_p qz120 (Enclosure.sfrac Bool.true Ns588p821 Ns588p822) 9111615050189153268089 4503599627370496000 37658490866468496617 Ns588p820 Ns588p821 Ns588p822 0 1 Ns588p824 

noncomputable def Ns588p826 := nat_lit 152867533805874265235835060224000 

noncomputable abbrev qz121 := (@HSub.hSub Real Real Real qz359 qz452 qz654)

noncomputable def Ns588p827 := @Enclosure.Real.IsNear.subLit_ff_p qz121 (@HMul.hMul Real Real Real qz5 qz654 (Real.log Real.pi)) 11677759168102849868153 4503599627370496000 783998026908263 272250000000000000000 9559631786919 16777216000 746637 134217728000 Ns588p826 9111615050189153268089 4503599627370496000 

noncomputable def Ns588p828 := nat_lit 23355518336205699736306000 

noncomputable abbrev qz122 := qz452

noncomputable def Ns588p829 := @Enclosure.Real.IsNear.subLit_ff_p qz122 qz654 13919461911423533216121 4503599627370496000 783998026908263 272250000000000000000 995516 2000 0 1 Ns588p828 11677759168102849868153 4503599627370496000 783998026908263 272250000000000000000 

noncomputable def Ns588p830 := nat_lit 31343841738742418095739709674653483008 

noncomputable def Ns588p831 := nat_lit 120121077237934593096548352 

noncomputable def Ns588p832 := nat_lit 114401289201550054133913789525849784434243007668884733696948652636450478507651593768601307580774396013950143754593552294040594726207766988159769907674221298756636771421325165318342234662416821327706980969401548800 

noncomputable def Ns588p833 := nat_lit 3839183534248782462683188183633551322634997536337709138385318946247866849356437778049140142269178310847715157915265373553210826478880820086800946267199969695601403638877137020425529210079807626840117304025415680 

noncomputable def Ns588p834 := nat_lit 44195893339947546571554417830238065796589907479296610168088623548503070091732115224586506353041279411206507319168503736362105029829670720977722448211709430624402343766019025827475734092064100918388326400 

noncomputable def Ns588p835 := BSN.log_dyadic_bound 1867057425024 6061361425024 9 8 Ns588p832 268435456 87120000 Ns588p833 Ns588p834 170919891 7928418850048 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1867057425024) (BSN.artanhQ 6061361425024) 0 8 Ns588p833 Ns588p832 Ns588p834 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz453 := (Real.log (Enclosure.sfrac Bool.false 3964209425024 16000000))

noncomputable def Ns588p836 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 995516 4000) qz453 995516 4000 0 1 55935735459408999 4503599627370496 12500018513 1089000000000000000 13921229905402252262121 4503599627370496000 3110992107496927 1089000000000000000000 (Enclosure.Real.IsNear.const Bool.false 995516 4000) (BSN.isNear_log_sfrac 3964209425024 16000000 55935735459408999 4503599627370496 12500018513 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3964209425024) qz362)) Bool.false Ns588p831 Ns588p114 1000001481040000 87120000000000000000000 55935735459408999 4503599627370496 12500018513 1089000000000000000 (BSN.log_rat_reduce_isNear 3964209425024 16000000 17 7928418850048 4194304000000 170919891 268435456 24973259072661432 36028797018963968 87120000 1000000000000000 rfl rfl rfl rfl (Ns588p835 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p837 := BSN.arctan_dyadic_bound_f 1000 1991032 1 0 33554432 10890000 0 1 1 0 1 1 16852 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1991032) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1991032) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns588p838 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1991032))) 884279719003555 562949953421312 1 2000000000000000 16852 33554432 1 10890000 29662016867668838055936 883996989359523 562949953421312 200000001089 2178000000000000000 qz17 (Ns588p837 rfl) rfl rfl 

noncomputable abbrev qz454 := (@HMul.hMul Real Real Real qz588 qz593 qz653)

noncomputable abbrev qz123 := qz454

noncomputable abbrev qz455 := qz653

noncomputable abbrev qz124 := qz455

noncomputable def Ns588p839 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 995516 4000) qz453) qz123 13921229905402252262121 4503599627370496000 3110992107496927 1089000000000000000000 883996989359523 2251799813685248 200000001089 8712000000000000000 Ns588p830 13919461911423533216121 4503599627370496000 783998026908263 272250000000000000000 (Ns588p836 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz124 1 4 0 1 883996989359523 562949953421312 200000001089 2178000000000000000 883996989359523 2251799813685248 200000001089 8712000000000000000 qz369 Ns588p838 rfl) 

noncomputable def Ns588p840 := @Ns588p825 Ns588p818 Ns588p819 37658490866468496617 Ns588p820 (@Ns588p827 37658490866468496617 Ns588p820 (Ns588p829 (Ns588p839 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 995516 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz654 (Real.log Real.pi) 995516 2000 0 1 38410761 33554432 3 268435456 9559631786919 16777216000 746637 134217728000 (Enclosure.Real.IsNear.const Bool.false 995516 2000) RS589to600.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns588p821 Ns588p822) 

noncomputable def Ns588p841 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns588p818 Ns588p819 37658490866468496617 Ns588p820 135773633363 67108864 71 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz370 qz120 (Enclosure.sfrac Bool.true Ns588p821 Ns588p822)) Bool.false Ns588p818 Ns588p819 37658490866468496617 Ns588p820 Ns588p823 (Ns588p840 rfl rfl)) 

noncomputable def Ns588p842 := nat_lit 15183373571174345627140096 

noncomputable def Ns588p843 := nat_lit 14348401833814713567681094477785763743366079765196763990994129003665291175508950585474969913883367787984921796612820590459634797267634686529536 

noncomputable def Ns588p844 := nat_lit 10182671275412721071890383785860013964056322554172213039277055812627575690622674784029095411776474964455249154016735037157573619262427136 

noncomputable def Ns588p845 := nat_lit 71653058422159928422917157182838258510364806730733715086165651114716102324265913449316409862246168175528866637316165611957655260942559687479296 

noncomputable def Ns588p846 := BSN.sin_dyadic_bound_f 215768715906 137438953472 4 3 67108864 21801270 Ns588p843 Ns588p127 Ns588p844 Ns588p845 Ns588p130 Ns588p844 67108838 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215768715906) (BSN.sinEvenQ 137438953472) 0 3 Ns588p843 Ns588p127 Ns588p844 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215768715906) (BSN.sinOddQ 137438953472) 0 3 Ns588p845 Ns588p130 Ns588p844 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p847 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz116) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 135773633363) qz371) Bool.false 135773633363 67108864 71 8388608 Bool.false 67108838 67108864 1 10890000 (Ns588p841 rfl) (Enclosure.sfrac_false_div 135773633363 67108864) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 135773633363) qz371) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns588p842) qz372) 226375608064910080 72057594037927936 Bool.false 67108838 67108864 321 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q3 135773633363 67108864 226375608064910080 72057594037927936 321 Ns588p842 Ns588p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108838 67108864 Ns588p842 Ns588p114 215768715906 137438953472 21801270 21780000 (Ns588p846 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p848 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns588p818 Ns588p819 37658490866468496617 Ns588p820 1086189066911 536870912 4534 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz370 qz120 (Enclosure.sfrac Bool.true Ns588p821 Ns588p822)) Bool.false Ns588p818 Ns588p819 37658490866468496617 Ns588p820 Ns588p823 (Ns588p840 rfl rfl)) 

noncomputable def Ns588p849 := Ns588p817 74374 BSN.abs_quadSignPos (BSN.cos_quad_nat0 848 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 238518710 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 591 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 491789417 536870912) qz119 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) Bool.false 33554419 33554432 48848663 5709496320000 536870704 536870912 4594 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 33554419 33554432 48848663 5709496320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz116) qz116) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 67108838 67108864 781578608 91351941120000 33554419 33554432 48848663 5709496320000 (Ns588p847 rfl rfl) rfl)) rfl) (Ns588p848 rfl) RS589to600.d7 

noncomputable def Ns588p850 := nat_lit 17414978138163493174227772025185498112912295315308147858783247181924858084184979623333872636074322564928064000000 

noncomputable def Ns588p851 := nat_lit 2015282357586543444244239527432981411508169961363478507782241245264386287268766208648440974401000000000000 

noncomputable def Ns588p852 := nat_lit 105587170949399118696315043777352341028372078579722888245148807971366168421736143220816456787460635380444121600000 

noncomputable def Ns588p853 := BSN.cos_dyadic_bound_f 596157930 536870912 4 3 536870912 268435456 Ns588p850 Ns588p146 Ns588p851 Ns588p852 Ns588p149 Ns588p851 238518710 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 596157930) qz375 0 3 Ns588p850 Ns588p146 Ns588p851 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 596157930) qz376 0 3 Ns588p852 Ns588p149 Ns588p851 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p854 := nat_lit 53546296582553998405418744518903641160456394214492182113843095738776502461707830261485671730118597493530040467456 

noncomputable def Ns588p855 := nat_lit 3336102245418575309856342335480960866437637371993810085396007727528412180201008992643172377465970759827456 

noncomputable def Ns588p856 := nat_lit 267633089018078036599444898475814245885274175001640030626899914198871269371658829404507152575865499255851467145216 

noncomputable def Ns588p857 := BSN.sin_dyadic_bound_f 621732084 536870912 4 3 536870912 268435456 Ns588p854 Ns588p172 Ns588p855 Ns588p856 Ns588p175 Ns588p855 491789417 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 621732084) qz373 0 3 Ns588p854 Ns588p172 Ns588p855 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 621732084) qz374 0 3 Ns588p856 Ns588p175 Ns588p855 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p858 := nat_lit 3746657894433256030990505870807340543746242831225750254233327987303485345 

noncomputable def Ns588p859 := nat_lit 222389333637484540600448840558583838041300584385966768458516496224161 

noncomputable def Ns588p860 := nat_lit 9812315378880257487147495601610701812169045309407006719652640463848574881 

noncomputable def Ns588p861 := BSN.sin_dyadic_bound_f 349453379 536870912 3 2 536870912 268435456 Ns588p858 Ns588p136 Ns588p859 Ns588p860 Ns588p139 Ns588p859 325294764 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 349453379) qz373 0 2 Ns588p858 Ns588p136 Ns588p859 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 349453379) qz374 0 2 Ns588p860 Ns588p139 Ns588p859 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p862 := nat_lit 177017788845672417947162257314732610391988108200121654278014968587796049966831819629686043121046489334812188348416 

noncomputable def Ns588p863 := nat_lit 120038309303601246931796806022526765299561819008800300124806944901452514668406972393636809089840815795081216 

noncomputable def Ns588p864 := nat_lit 884016213571170724827454137060573697327399661078191285106876598918761598899334074954628366054462759647660374757376 

noncomputable def Ns588p865 := BSN.sin_dyadic_bound_f 838062978 536870912 4 3 536870912 268435456 Ns588p862 Ns588p172 Ns588p863 Ns588p864 Ns588p175 Ns588p863 536845224 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 838062978) qz373 0 3 Ns588p862 Ns588p172 Ns588p863 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 838062978) qz374 0 3 Ns588p864 Ns588p175 Ns588p863 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p866 := Ns588p815 125837 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 409 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 325294764 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 267 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536845224 536870912) qz119 rfl rfl (Ns588p849 RS589to600.d9 RS589to600.d11 RS589to600.d13 RS589to600.d17 (Ns588p853 rfl rfl) (Ns588p857 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns588p848 rfl) RS589to600.d19 RS589to600.d21 RS589to600.d23 RS589to600.d25 RS589to600.d17 (Ns588p861 rfl rfl) (Ns588p865 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns588p867 := nat_lit 2761320247993150536073577226869552897429350146468076478160230730956800000 

noncomputable def Ns588p868 := nat_lit 391320767426563100227763185417186925204648179893115831720345600000000 

noncomputable def Ns588p869 := nat_lit 8283178102444598482020276154237824318437641143044443202817251501670400000 

noncomputable def Ns588p870 := BSN.cos_dyadic_bound_f 375030520 536870912 3 2 536870912 268435456 Ns588p867 Ns588p152 Ns588p868 Ns588p869 Ns588p155 Ns588p868 411123011 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 375030520) qz375 0 2 Ns588p867 Ns588p152 Ns588p868 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 375030520) qz376 0 2 Ns588p869 Ns588p155 Ns588p868 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p871 := nat_lit 21997144030270796069450969298916101640119122619115754122328391810323169467934101679967902167473143474436414898176 

noncomputable def Ns588p872 := nat_lit 4058413837767719439170323289473222151386723014123846951727160055307613850828614149257916976481996107677696 

noncomputable def Ns588p873 := nat_lit 133347759184626142307798814709322634241864744094526324253001037695438970828915982946399840591534353154728567767040 

noncomputable def Ns588p874 := BSN.cos_dyadic_bound_f 631969852 536870912 4 3 536870912 268435456 Ns588p871 Ns588p146 Ns588p872 Ns588p873 Ns588p149 Ns588p872 205928498 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 631969852) qz375 0 3 Ns588p871 Ns588p146 Ns588p872 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 631969852) qz376 0 3 Ns588p873 Ns588p149 Ns588p872 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p875 := Ns588p813 169339 BSN.abs_quadSignPos (BSN.cos_quad_nat0 152 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 411123011 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 205928498 536870912) qz119 rfl rfl (Ns588p866 rfl rfl) (Ns588p848 rfl) RS589to600.d27 RS589to600.d29 RS589to600.d31 RS589to600.d33 RS589to600.d17 (Ns588p870 rfl rfl) (Ns588p874 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p876 := nat_lit 107860152858603722117721018352167458341908347049243188506889999385164237240680023480013445589542091154910072344576 

noncomputable def Ns588p877 := nat_lit 27217579199266568933500580549603285660632112978360562167978697270162663113418971260770327204532219111346176 

noncomputable def Ns588p878 := nat_lit 538901952570361753477741863898220376426937667848366885966470234047190008572149971619293942026902103335888903540736 

noncomputable def Ns588p879 := BSN.sin_dyadic_bound_f 740577974 536870912 4 3 536870912 268435456 Ns588p876 Ns588p172 Ns588p877 Ns588p878 Ns588p175 Ns588p877 527070886 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 740577974) qz373 0 3 Ns588p876 Ns588p172 Ns588p877 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 740577974) qz374 0 3 Ns588p878 Ns588p175 Ns588p877 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p880 := nat_lit 5361914751039304664984657470018709784677102351356798822368912536129495296 

noncomputable def Ns588p881 := nat_lit 1475106115480740915691116354538088159680248949974004336681910601769216 

noncomputable def Ns588p882 := nat_lit 16082794040886952513122590177347053177711946556170448458433373787184947456 

noncomputable def Ns588p883 := BSN.cos_dyadic_bound_f 442693258 536870912 3 2 536870912 268435456 Ns588p880 Ns588p152 Ns588p881 Ns588p882 Ns588p155 Ns588p881 364462917 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 442693258) qz375 0 2 Ns588p880 Ns588p152 Ns588p881 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 442693258) qz376 0 2 Ns588p882 Ns588p155 Ns588p881 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p884 := Ns588p811 207347 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 527070886 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 104 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 364462917 536870912) qz119 rfl rfl (Ns588p875 rfl) (Ns588p848 rfl) RS589to600.d35 RS589to600.d37 RS589to600.d39 RS589to600.d41 RS589to600.d17 (Ns588p879 rfl rfl) (Ns588p883 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p885 := nat_lit 1012633737002815934157450785118656219964956608326156055832053371337890625 

noncomputable def Ns588p886 := nat_lit 16246816712041893885535243935292152662319049042139112949371337890625 

noncomputable def Ns588p887 := nat_lit 2652109673494603188298461189677728198327718790965292873377269371337890625 

noncomputable def Ns588p888 := BSN.sin_dyadic_bound_f 251968375 536870912 3 2 536870912 268435456 Ns588p885 Ns588p136 Ns588p886 Ns588p887 Ns588p139 Ns588p886 242819603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 251968375) qz373 0 2 Ns588p885 Ns588p136 Ns588p886 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 251968375) qz374 0 2 Ns588p887 Ns588p139 Ns588p886 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p889 := nat_lit 31059524456121238262211531787225979513202818566216362918804034715124704545 

noncomputable def Ns588p890 := nat_lit 15270030357304565504477992804384913187885825401208409135459811791414561 

noncomputable def Ns588p891 := nat_lit 81321650669262845199737237930575227913226995384678994029696013130045269281 

noncomputable def Ns588p892 := BSN.sin_dyadic_bound_f 592898003 536870912 3 2 536870912 268435456 Ns588p889 Ns588p136 Ns588p890 Ns588p891 Ns588p139 Ns588p890 479520174 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 592898003) qz373 0 2 Ns588p889 Ns588p136 Ns588p890 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 592898003) qz374 0 2 Ns588p891 Ns588p139 Ns588p890 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p893 := Ns588p809 241531 BSN.abs_quadSignPos (BSN.cos_quad_nat3 171 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 242819603 536870912) BSN.abs_quadSignPos qz634 (BSN.sfrac_eq_quadSignPos_mul Bool.false 479520174 536870912) qz119 rfl rfl (Ns588p884 rfl) (Ns588p848 rfl) RS589to600.d43 RS589to600.d45 RS589to600.d47 RS589to600.d49 RS589to600.d17 (Ns588p888 rfl rfl) (Ns588p892 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p894 := nat_lit 36065512401318721843491630968395024801072498361414901569225829333943178545201550604379917042253907677391582396416 

noncomputable def Ns588p895 := nat_lit 17847781782492627420949283443097648658899552586729550774696610765207230389240780797292687429960187443675136 

noncomputable def Ns588p896 := nat_lit 218524739886131004643013656480117146263955811168580623214168281898940604936480381151201111448225720456428671467520 

noncomputable def Ns588p897 := BSN.cos_dyadic_bound_f 714987892 536870912 4 3 536870912 268435456 Ns588p894 Ns588p146 Ns588p895 Ns588p896 Ns588p149 Ns588p895 127108474 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 714987892) qz375 0 3 Ns588p894 Ns588p146 Ns588p895 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 714987892) qz376 0 3 Ns588p896 Ns588p149 Ns588p895 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p898 := Ns588p807 Bool.false 1313414377 241531 Bool.true 714987892 28296951008113761 1 Bool.false 127108474 Bool.true Bool.false 1276721319 257507 BSN.abs_quadSignNeg qz398 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127108474 536870912) qz119 rfl (Ns588p893 rfl) (Ns588p848 rfl) RS589to600.d51 RS589to600.d53 RS589to600.d17 (Ns588p897 rfl rfl) rfl 

noncomputable def Ns588p899 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) 1276721319 536870912 257507 536870912 1276721319 536870912 257507 536870912 1370869077802745856 1276721319 268435456 257507 268435456 (Ns588p898 rfl rfl rfl rfl) 

noncomputable def Ns588p900 := @Enclosure.Real.IsNear.mulLit_ff qz651 (Zeta.RiemannSiegel.correction qz118) 18915281 67108864 1 67108864 223012507440153 562949953421312 4499961500468213 383157812047380480000 4218344244745084677993 37778931862957161709568 

noncomputable abbrev qz655 := (@HPow.hPow Real Real Real qz7 qz117 qz9)

noncomputable def Ns588p901 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz655 1 1 0 1 18915281 67108864 1 67108864 18915281 67108864 1 67108864 

noncomputable def Ns588p902 := @Enclosure.Real.IsNear.sqrt_image qz117 2658203677453 16777216000 248879 16777216000 422361234 422361275 33554432 (@Enclosure.Real.IsNear.of_eq qz117 (@HMul.hMul Real Real Real qz5 qz116 qz3) Bool.false 2658203677453 16777216000 248879 16777216000 (BSN.t_div_two_pi_mk qz116 995516 1000 qz119) (@Enclosure.Real.IsNear.mulLit_ff qz116 qz3 995516 1000 0 1 10680707 67108864 1 67108864 2658203677453 16777216000 248879 16777216000 (Enclosure.Real.IsNear.const Bool.false 995516 1000) RS589to600.d56 rfl)) 

noncomputable abbrev qz767 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 995516 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz656 := qz767

noncomputable abbrev qz456 := qz656

noncomputable abbrev qz125 := qz456

noncomputable def Ns588p903 := @Enclosure.Real.IsNear.sqrt_image qz125 844722509 67108864 41 67108864 119046593 119046599 33554432 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 844722509 67108864 41 67108864 844722509 67108864 41 67108864 (Ns588p902 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns588p904 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz125) 29761649 8388608 3 33554432 9457640 9457641 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz125) Bool.false 238093192 67108864 6 67108864 29761649 8388608 3 33554432 (Ns588p903 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns588p905 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 18915281 67108864 1 67108864 18915281 67108864 1 67108864 (Ns588p904 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz457 := (@HMul.hMul Real Real Real qz588 qz586 qz650)

noncomputable abbrev qz126 := (Real.cos qz457)

noncomputable abbrev qz657 := (@HMul.hMul Real Real Real qz739 qz766 qz766)

noncomputable abbrev qz458 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz657 qz650) qz603)

noncomputable abbrev qz127 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz458))

noncomputable def Ns588p906 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz118) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz126) qz127) Bool.false 223012507440153 

noncomputable def Ns588p907 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz126) qz127 78660611 67108864 365 

noncomputable abbrev qz128 := (@Neg.neg Real Real.instNeg (Real.cos qz457))

noncomputable def Ns588p908 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz126) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz128)) Bool.true 78660611 67108864 365 67108864 (BSN.inv_eq_neg_inv_neg qz126) 

noncomputable def Ns588p909 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz128) Bool.false 78660611 67108864 365 67108864 78660611 67108864 

noncomputable def Ns588p910 := @Enclosure.Real.IsNear.recentre' qz126 Bool.true 57253555 67108864 2887618864 730815528960000 57253555 67108864 180476179 45675970560000 

noncomputable abbrev qz129 := qz457

noncomputable def Ns588p911 := @Enclosure.Real.IsNear.cos_image qz129 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 247658917) qz371) Bool.false 247658917 67108864 259 67108864 Bool.true 57253555 67108864 1 

noncomputable def Ns588p912 := nat_lit 1106429092109387936720977119 

noncomputable def Ns588p913 := nat_lit 288230376151711744000000000000000 

noncomputable def Ns588p914 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz118 884279719003555 140737488355328 1 500000000000000 39416141 67108864 41 67108864 34854894087684503381255 9444732965739290427392 Ns588p912 

noncomputable def Ns588p915 := @Enclosure.Real.IsNear.subLit_ff_p qz125 qz1 844722509 67108864 41 67108864 12 1 0 1 39416141 39416141 67108864 41 

noncomputable def Ns588p916 := @Ns588p915 67108864 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 844722509 67108864 41 67108864 844722509 67108864 41 67108864 (Ns588p902 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns588p917 := @Enclosure.Real.IsNear.recentre' qz129 Bool.false 34854894087684503381255 9444732965739290427392 Ns588p912 Ns588p913 247658917 67108864 259 67108864 (@Ns588p914 Ns588p913 RS589to600.d55 (Ns588p916 rfl rfl) rfl) 

noncomputable def Ns588p918 := nat_lit 5307791613027071645712384 

noncomputable def Ns588p919 := nat_lit 19404763062334328020130860303705759721935565591888837517955543318283278465206430639308301441 

noncomputable def Ns588p920 := nat_lit 1047785795682775032058882663955033499890521692670300424456034586992705154364836941816961 

noncomputable def Ns588p921 := nat_lit 58212193615411618510328463145789369098806915732281171953017717885675849985310562244041270401 

noncomputable def Ns588p922 := BSN.cos_dyadic_bound_f 75428255471 137438953472 3 2 67108864 21801270 Ns588p919 Ns588p511 Ns588p920 Ns588p921 Ns588p514 Ns588p920 57253555 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 75428255471) qz383 0 2 Ns588p919 Ns588p511 Ns588p920 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 75428255471) qz384 0 2 Ns588p921 Ns588p514 Ns588p920 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p923 := @Ns588p911 10890000 (Ns588p917 rfl) (Enclosure.sfrac_false_div 247658917 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 247658917) qz371) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns588p918) qz372) 226375608064910080 72057594037927936 Bool.false 57253555 67108864 0 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 247658917 67108864 226375608064910080 72057594037927936 0 Ns588p918 Ns588p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 57253555 67108864 Ns588p918 Ns588p114 75428255471 137438953472 21801270 21780000 (Ns588p922 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p924 := @Enclosure.Real.IsNear.inv_image qz128 57253555 67108864 180476179 45675970560000 39330123 39330488 33554432 (@Enclosure.Real.IsNear.neg qz126 Bool.true 57253555 67108864 180476179 45675970560000 (Ns588p910 (Ns588p923 rfl rfl) rfl)) 

noncomputable def Ns588p925 := Ns588p908 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz128) Bool.false 78660611 67108864 365 67108864 (@Ns588p909 365 67108864 (Ns588p924 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p926 := @Enclosure.Real.IsNear.recentre' qz127 Bool.true 11340492 33554432 

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz355 qz352 qz458)

noncomputable def Ns588p927 := @Enclosure.Real.IsNear.cos_image qz130 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 128550965)) qz371) Bool.true 128550965 67108864 

noncomputable def Ns588p928 := nat_lit 1214129540476815739057528489445 

noncomputable def Ns588p929 := nat_lit 633825300114114700748351602688 

noncomputable def Ns588p930 := nat_lit 161473574996157450890601165532101597 

noncomputable def Ns588p931 := @Enclosure.Real.IsNear.recentre' qz130 Bool.true Ns588p928 Ns588p929 Ns588p930 

noncomputable def Ns588p932 := nat_lit 19342813113834066795298816000000000000000 

noncomputable abbrev qz131 := qz458

noncomputable def Ns588p933 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz131 884279719003555 140737488355328 1 500000000000000 1373015251152599 

noncomputable abbrev qz459 := (@HSub.hSub Real Real Real qz592 qz657 qz650)

noncomputable abbrev qz132 := qz459

noncomputable def Ns588p934 := @Enclosure.Real.IsNear.subLit_tf qz132 qz31 1091540274441943 4503599627370496 5983588667 4503599627370496 1 16 

noncomputable abbrev qz460 := qz657

noncomputable abbrev qz133 := qz460

noncomputable def Ns588p935 := @Enclosure.Real.IsNear.subLit_ff_n qz133 qz118 1553632171331881 4503599627370496 3232125243 4503599627370496 39416141 67108864 41 67108864 

noncomputable def Ns588p936 := @Enclosure.Real.IsNear.mulLit_ff qz118 qz118 39416141 67108864 41 67108864 39416141 67108864 41 67108864 1553632171331881 4503599627370496 

noncomputable def Ns588p937 := nat_lit 2260147833521359142032357223050660358099323847711412537295257407476669745630177883240065171954713140625 

noncomputable def Ns588p938 := nat_lit 20365922818675747343406394335744435661085022455850173264383637468124585281315297485376953369140625 

noncomputable def Ns588p939 := nat_lit 13638783235447346930393416596184461963233372053762234251244571900037762606435114632270764804748722740625 

noncomputable def Ns588p940 := BSN.cos_dyadic_bound_t 128550965 67108864 4 3 33554432 10890000 Ns588p937 Ns588p231 Ns588p938 Ns588p939 Ns588p234 Ns588p938 11340492 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 128550965) (BSN.cosEvenQ 67108864) 0 3 Ns588p937 Ns588p231 Ns588p938 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 128550965) (BSN.cosOddQ 67108864) 0 3 Ns588p939 Ns588p234 Ns588p938 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p941 := @Ns588p926 6176398864 730815528960000 2835123 8388608 386024929 45675970560000 (@Ns588p927 561 67108864 Bool.true 11340492 33554432 1 10890000 (@Ns588p931 Ns588p932 128550965 67108864 561 67108864 (@Ns588p933 4503599627370496 5983588667 4503599627370496 Ns588p928 Ns588p929 Ns588p930 Ns588p932 RS589to600.d55 (@Ns588p934 0 1 21968244018441584 1373015251152599 4503599627370496 5983588667 4503599627370496 (@Ns588p935 73252027828047028682752 1091540274441943 4503599627370496 5983588667 4503599627370496 (@Ns588p936 3232125243 4503599627370496 (Ns588p916 rfl rfl) (Ns588p916 rfl rfl) rfl) (Ns588p916 rfl rfl) rfl rfl) qz388 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 128550965 67108864) (BSN.cos_neg_of_bound 128550965 67108864 Bool.true 11340492 33554432 1 10890000 (Ns588p940 rfl rfl)) rfl rfl) 

noncomputable def Ns588p942 := @Ns588p900 9474425406486203896299 Ns588p804 (Ns588p901 qz33 (@Enclosure.Real.IsNear.of_eq qz655 (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 18915281 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz117 (BSN.t_div_two_pi_nonneg qz116 995516 1000 qz119)) Ns588p905) rfl) (@Ns588p906 562949953421312 4499961500468213 383157812047380480000 (BSN.correction_mk qz118 (BSN.cos_two_pi_p_ne_zero_mk qz116 995516 1000 12 qz119 rfl rfl (@BSN.floor_sqrt_eq_dec qz116 995516 1000 12 qz119 rfl rfl rfl))) (@Ns588p907 67108864 2835123 8388608 386024929 45675970560000 223012507440153 562949953421312 4499961500468213 383157812047380480000 Ns588p925 (Ns588p941 rfl) rfl)) 

noncomputable def Ns588p943 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (hardyZApproximantRS₀ qz116) Bool.false 175464207521016420159639 37778931862957161709568 Ns588p803 Ns588p804 (@Eq.refl Real (hardyZApproximantRS₀ qz116)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HMul.hMul Real Real Real qz5 qz651 (Zeta.RiemannSiegel.correction qz118))) Bool.false 175464207521016420159639 37778931862957161709568 Ns588p803 Ns588p804 (BSN.hardyZApproximantRS₀_eq qz116 12 (@BSN.floor_sqrt_eq_dec qz116 995516 1000 12 qz119 rfl rfl rfl)) (@Ns588p806 175464207521016420159639 37778931862957161709568 Ns588p803 Ns588p804 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12)) Bool.false 1276721319 268435456 257507 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (Ns588p899 (Ns588p898 rfl rfl rfl rfl) rfl rfl)) (Ns588p942 rfl) rfl rfl)) 

theorem RS589to600.d64 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz116) Bool.false 175464207521016420159639 37778931862957161709568 Ns588p803 Ns588p804 := Ns588p943 

noncomputable def Ns588p944 := nat_lit 49568160450404225674682819 

noncomputable def Ns588p945 := nat_lit 51426570998450436377149440000 

noncomputable def Ns588p946 := nat_lit 15266064231888833671495401078784 

noncomputable abbrev qz768 := (Enclosure.sfrac Bool.false 996757 1000)

noncomputable abbrev qz658 := qz768

noncomputable abbrev qz461 := qz658

noncomputable abbrev qz134 := qz461

noncomputable abbrev qz769 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 996757 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz659 := qz769

noncomputable abbrev qz462 := qz659

noncomputable abbrev qz135 := qz462

noncomputable abbrev qz770 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 996757 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz660 := qz770

noncomputable abbrev qz463 := qz660

noncomputable abbrev qz136 := qz463

noncomputable abbrev qz661 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz135 qz9))

noncomputable def Ns588p947 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HMul.hMul Real Real Real qz5 qz661 (Zeta.RiemannSiegel.correction qz136)) 194505427 67108864 257831 268435456 8488441775322813234333 75557863725914323419136 173179531410147405242819 Ns588p945 Ns588p946 

noncomputable def Ns588p948 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos BSN.quadSignNeg 11 12 996757 1000 286 536870912 268435456 9007199254740992 Bool.false 1087876697870 4540 1334074092 51 154981288 8 

noncomputable def Ns588p949 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 9 10 11 996757 1000 171 231 536870912 268435456 9007199254740992 Bool.false 1087876697870 4540 

noncomputable def Ns588p950 := Ns588p949 1236190956 51 169773496 8 1287360220 51 161872664 8 Bool.true 893775056 207609 Bool.true 98450392 Bool.true 502881077 28296951008113761 1 Bool.false 97899544 Bool.false Bool.false 432503683 Bool.false Bool.true 732411739 

noncomputable def Ns588p951 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 996757 1000 29 104 536870912 268435456 9007199254740992 Bool.false 1087876697870 4540 

noncomputable def Ns588p952 := Ns588p951 1116391676 51 189812536 8 1179625948 51 178956968 8 Bool.true 919716390 169553 Bool.true 438389085 Bool.true 218978101 28296951008113761 1 Bool.false 391269871 Bool.true Bool.false 492828389 Bool.false Bool.true 893775056 

noncomputable def Ns588p953 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 996757 1000 153 55 536870912 268435456 9007199254740992 Bool.false 1087876697870 4540 

noncomputable def Ns588p954 := Ns588p953 961943533 51 219176632 8 1044702541 51 202918136 8 Bool.true 975977869 125997 Bool.false 25574698 Bool.false 179810101 28296951008113761 1 Bool.false 25565026 Bool.true Bool.false 176467264 Bool.false Bool.true 919716390 

noncomputable def Ns588p955 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 996757 1000 410 268 536870912 268435456 9007199254740992 Bool.false 1087876697870 4540 

noncomputable def Ns588p956 := Ns588p955 744261104 50 268435448 8 864060384 50 240095976 8 Bool.true 841869317 74469 Bool.false 270141451 Bool.false 610080144 28296951008113761 1 Bool.false 470328275 Bool.true Bool.false 225967140 Bool.false Bool.true 975977869 

noncomputable def Ns588p957 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 996757 1000 850 592 536870912 268435456 9007199254740992 Bool.false 1087876697870 4540 

noncomputable def Ns588p958 := Ns588p957 372130544 50 379625064 8 589812976 50 309962568 8 Bool.true 536870640 4602 Bool.false 135345171 Bool.false 734090283 28296951008113761 1 Bool.false 519900814 Bool.true Bool.false 108472654 Bool.false Bool.true 841869317 

noncomputable def Ns588p959 := nat_lit 322187115749528296003802961582638860229588711838143958861139 

noncomputable def Ns588p960 := nat_lit 159000455663424767808826418983363561749922459674476544000 

noncomputable def Ns588p961 := nat_lit 5947392000000000000000000 

noncomputable def Ns588p962 := nat_lit 472267419439843474867302052267360000 

noncomputable def Ns588p963 := nat_lit 2824415468854808747224652502853877709120 

noncomputable abbrev qz662 := (@Eq.refl Real qz768)

noncomputable abbrev qz464 := qz662

noncomputable abbrev qz137 := qz464

noncomputable def Ns588p964 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz134 996757 1000 3974099068196 16000000 1993514 4000 2000 Ns588p962 Ns588p963 qz137 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns588p965 := nat_lit 103099877039849054721216947706444435273468387788206066835564480 

noncomputable abbrev qz663 := (@HSub.hSub Real Real Real qz743 qz744 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz745 (@Nat.cast Real Real.instNatCast 1993514))))

noncomputable abbrev qz465 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 996757 4000) (Real.log (Enclosure.sfrac Bool.false 3974099068196 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz663))

noncomputable abbrev qz664 := (Enclosure.sfrac Bool.false 996757 2000)

noncomputable abbrev qz138 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz465 qz664) (@HMul.hMul Real Real Real qz355 qz664 (Real.log Real.pi)))

noncomputable def Ns588p966 := @Enclosure.Real.IsNear.addLit_ft_p qz138 (Enclosure.sfrac Bool.true Ns588p962 Ns588p963) 36503087695262329193779 18014398509481984000 50273743870432147537 Ns588p961 Ns588p962 Ns588p963 0 1 Ns588p965 

noncomputable def Ns588p967 := nat_lit 2449680747721433094188544557056000 

noncomputable abbrev qz139 := (@HSub.hSub Real Real Real qz359 qz465 qz664)

noncomputable def Ns588p968 := @Enclosure.Real.IsNear.subLit_ff_p qz139 (@HMul.hMul Real Real Real qz5 qz664 (Real.log Real.pi)) 46780459882306244035891 18014398509481984000 4186493651168947 1452000000000000000000 38286194902077 67108864000 2990271 536870912000 Ns588p967 36503087695262329193779 18014398509481984000 

noncomputable def Ns588p969 := nat_lit 18712183952922497614356400 

noncomputable abbrev qz140 := qz465

noncomputable def Ns588p970 := @Enclosure.Real.IsNear.subLit_ff_p qz140 qz664 11151689757972822199767 3602879701896396800 4186493651168947 1452000000000000000000 996757 2000 0 1 Ns588p969 46780459882306244035891 18014398509481984000 4186493651168947 1452000000000000000000 

noncomputable def Ns588p971 := nat_lit 25111372919278889391788939710316937216 

noncomputable def Ns588p972 := nat_lit 120145174774561553975869440 

noncomputable def Ns588p973 := nat_lit 117424606279855777701149292542367372967669405206586549650479909430862966694655956456479238186344838625689454222940162390999212581224596335490576372384281881944378709115103745313344835715878069174403110131256524800 

noncomputable def Ns588p974 := nat_lit 3971336228948420341363029288435577709306003482968528120852810074603353288128150496398533652795281815953150930548509986438234512313892726616674028884002536349875217519393856372499599518630544749423031278140129280 

noncomputable def Ns588p975 := nat_lit 48094067551301791304624765645330417743115281567055625077995793852325944382338168135017877035018802784771524707462355421625186652085895196220873803346730889889272128817342953149808136689115191442826854400 

noncomputable def Ns588p976 := BSN.log_dyadic_bound 1876947068196 6071251068196 9 8 Ns588p973 268435456 87120000 Ns588p974 Ns588p975 171588732 7948198136392 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1876947068196) (BSN.artanhQ 6071251068196) 0 8 Ns588p974 Ns588p973 Ns588p975 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz466 := (Real.log (Enclosure.sfrac Bool.false 3974099068196 16000000))

noncomputable def Ns588p977 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 996757 4000) qz466 996757 4000 0 1 55946956749335655 4503599627370496 12500018513 1089000000000000000 11153104153719511894167 3602879701896396800 12459480952962341 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 996757 4000) (BSN.isNear_log_sfrac 3974099068196 16000000 55946956749335655 4503599627370496 12500018513 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3974099068196) qz362)) Bool.false Ns588p972 Ns588p114 1000001481040000 87120000000000000000000 55946956749335655 4503599627370496 12500018513 1089000000000000000 (BSN.log_rat_reduce_isNear 3974099068196 16000000 17 7948198136392 4194304000000 171588732 268435456 24973259072661432 36028797018963968 87120000 1000000000000000 rfl rfl rfl rfl (Ns588p976 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p978 := BSN.arctan_dyadic_bound_f 1000 1993514 1 0 33554432 10890000 0 1 1 0 1 1 16831 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1993514) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1993514) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns588p979 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1993514))) 884279719003555 562949953421312 1 2000000000000000 16831 33554432 1 10890000 29662028689617859903488 883997341681059 562949953421312 200000001089 2178000000000000000 qz17 (Ns588p978 rfl) rfl rfl 

noncomputable abbrev qz467 := (@HMul.hMul Real Real Real qz588 qz593 qz663)

noncomputable abbrev qz141 := qz467

noncomputable abbrev qz468 := qz663

noncomputable abbrev qz142 := qz468

noncomputable def Ns588p980 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 996757 4000) qz466) qz141 11153104153719511894167 3602879701896396800 12459480952962341 4356000000000000000000 883997341681059 2251799813685248 200000001089 8712000000000000000 Ns588p971 11151689757972822199767 3602879701896396800 4186493651168947 1452000000000000000000 (Ns588p977 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz142 1 4 0 1 883997341681059 562949953421312 200000001089 2178000000000000000 883997341681059 2251799813685248 200000001089 8712000000000000000 qz369 Ns588p979 rfl) 

noncomputable def Ns588p981 := @Ns588p966 Ns588p959 Ns588p960 50273743870432147537 Ns588p961 (@Ns588p968 50273743870432147537 Ns588p961 (Ns588p970 (Ns588p980 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 996757 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz664 (Real.log Real.pi) 996757 2000 0 1 38410761 33554432 3 268435456 38286194902077 67108864000 2990271 536870912000 (Enclosure.Real.IsNear.const Bool.false 996757 2000) RS589to600.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns588p962 Ns588p963) 

noncomputable def Ns588p982 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns588p959 Ns588p960 50273743870432147537 Ns588p961 135984587233 67108864 569 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz370 qz138 (Enclosure.sfrac Bool.true Ns588p962 Ns588p963)) Bool.false Ns588p959 Ns588p960 50273743870432147537 Ns588p961 Ns588p964 (Ns588p981 rfl rfl)) 

noncomputable def Ns588p983 := BSN.cos_dyadic_bound_f 136431849 137438953472 1 0 67108864 21801270 0 1 1 0 1 1 67108830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 136431849) qz383 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 136431849) qz384 0 0 rfl) rfl rfl 

noncomputable def Ns588p984 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz134) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 135984587233) qz371) Bool.false 135984587233 67108864 569 67108864 Bool.true 67108830 67108864 1 10890000 (Ns588p982 rfl) (Enclosure.sfrac_false_div 135984587233 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 135984587233) qz371) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9600537917934194917376) qz372) 226375608064910080 72057594037927936 Bool.false 67108830 67108864 322 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 135984587233 67108864 226375608064910080 72057594037927936 322 9600537917934194917376 Ns588p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108830 67108864 9600537917934194917376 Ns588p114 136431849 137438953472 21801270 21780000 (Ns588p983 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p985 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns588p959 Ns588p960 50273743870432147537 Ns588p961 1087876697870 536870912 4540 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz370 qz138 (Enclosure.sfrac Bool.true Ns588p962 Ns588p963)) Bool.false Ns588p959 Ns588p960 50273743870432147537 Ns588p961 Ns588p964 (Ns588p981 rfl rfl)) 

noncomputable def Ns588p986 := Ns588p958 74469 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 850 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 519900814 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 592 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 108472654 536870912) qz137 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) Bool.true 33554415 33554432 391469929 45675970560000 536870640 536870912 4602 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 33554415 33554432 391469929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz134) qz134) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 67108830 67108864 6263518864 730815528960000 33554415 33554432 391469929 45675970560000 (Ns588p984 rfl rfl) rfl)) rfl) (Ns588p985 rfl) RS589to600.d7 

noncomputable def Ns588p987 := nat_lit 335560675907195213378875236216081 

noncomputable def Ns588p988 := BSN.cos_dyadic_bound_f 135345171 536870912 2 1 536870912 268435456 Ns588p987 Ns588p142 Ns588p987 Ns588p987 Ns588p143 Ns588p987 519900814 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 135345171) qz375 0 1 Ns588p987 Ns588p142 Ns588p987 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 135345171) qz376 0 1 Ns588p987 Ns588p143 Ns588p987 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p989 := nat_lit 40085340825999373768148430691756824868170823716688601184039723901179844987507071972850259167251102717051298196241 

noncomputable def Ns588p990 := nat_lit 24490277453356609605926798436481635810702961770168348439804921468541087955569871069733635307425105045170961 

noncomputable def Ns588p991 := nat_lit 242847648633534565852870098184688705042662198277247581474275163472339508515896573644342837780072778754373349878545 

noncomputable def Ns588p992 := BSN.cos_dyadic_bound_f 734090283 536870912 4 3 536870912 268435456 Ns588p989 Ns588p146 Ns588p990 Ns588p991 Ns588p149 Ns588p990 108472654 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 734090283) qz375 0 3 Ns588p989 Ns588p146 Ns588p990 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 734090283) qz376 0 3 Ns588p991 Ns588p149 Ns588p990 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p993 := nat_lit 743310491721070877845793686364556309737508423521494763742557440995466081 

noncomputable def Ns588p994 := nat_lit 28361541115777208270122350271983219042020866684114066365760848501601 

noncomputable def Ns588p995 := nat_lit 2229874752080981079120840814393124962774441228831116063094940801289395041 

noncomputable def Ns588p996 := BSN.cos_dyadic_bound_f 270141451 536870912 3 2 536870912 268435456 Ns588p993 Ns588p152 Ns588p994 Ns588p995 Ns588p155 Ns588p994 470328275 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 270141451) qz375 0 2 Ns588p993 Ns588p152 Ns588p994 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 270141451) qz376 0 2 Ns588p995 Ns588p155 Ns588p994 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p997 := nat_lit 19101311637809928310148799554367292492378532139955214250558173525747214317660881672961745210623666693533719330816 

noncomputable def Ns588p998 := nat_lit 2658536854935592451183568783923019962625425348200300457115253155055112946588733748182148839823754223681536 

noncomputable def Ns588p999 := nat_lit 115804673399529660025544585661637965762735678983685899546759564522387173840972315931613921550387833774618779320320 

noncomputable def Ns588p1000 := BSN.cos_dyadic_bound_f 610080144 536870912 4 3 536870912 268435456 Ns588p997 Ns588p146 Ns588p998 Ns588p999 Ns588p149 Ns588p998 225967140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 610080144) qz375 0 3 Ns588p997 Ns588p146 Ns588p998 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 610080144) qz376 0 3 Ns588p999 Ns588p149 Ns588p998 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1001 := Ns588p956 125997 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 410 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 470328275 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 268 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 225967140 536870912) qz137 rfl rfl (Ns588p986 RS589to600.d9 RS589to600.d11 RS589to600.d13 RS589to600.d17 (Ns588p988 rfl rfl) (Ns588p992 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns588p985 rfl) RS589to600.d19 RS589to600.d21 RS589to600.d23 RS589to600.d25 RS589to600.d17 (Ns588p996 rfl rfl) (Ns588p1000 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns588p1002 := nat_lit 427801256799039298232219769616 

noncomputable def Ns588p1003 := BSN.sin_dyadic_bound_f 25574698 536870912 2 1 536870912 268435456 Ns588p1002 Ns588p188 Ns588p1002 Ns588p1002 Ns588p189 Ns588p1002 25565026 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 25574698) qz373 0 1 Ns588p1002 Ns588p188 Ns588p1002 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 25574698) qz374 0 1 Ns588p1002 Ns588p189 Ns588p1002 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1004 := nat_lit 1045337041579602905824170395300401 

noncomputable def Ns588p1005 := BSN.sin_dyadic_bound_f 179810101 536870912 2 1 536870912 268435456 Ns588p1004 Ns588p188 Ns588p1004 Ns588p1004 Ns588p189 Ns588p1004 176467264 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 179810101) qz373 0 1 Ns588p1004 Ns588p188 Ns588p1004 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 179810101) qz374 0 1 Ns588p1004 Ns588p189 Ns588p1004 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1006 := Ns588p954 169553 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 153 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 25565026 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 176467264 536870912) qz137 rfl rfl (Ns588p1001 rfl rfl) (Ns588p985 rfl) RS589to600.d27 RS589to600.d29 RS589to600.d31 RS589to600.d33 RS589to600.d17 (Ns588p1003 rfl rfl) (Ns588p1005 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1007 := nat_lit 9280343674732697658500373349089665247795412524376891617803951363703230625 

noncomputable def Ns588p1008 := nat_lit 1364199419731288140041704814859158704626284056809121760232465875390625 

noncomputable def Ns588p1009 := nat_lit 24303453301429881305750434106486970344418590246799882325684258150662590625 

noncomputable def Ns588p1010 := BSN.sin_dyadic_bound_f 438389085 536870912 3 2 536870912 268435456 Ns588p1007 Ns588p136 Ns588p1008 Ns588p1009 Ns588p139 Ns588p1008 391269871 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 438389085) qz373 0 2 Ns588p1007 Ns588p136 Ns588p1008 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 438389085) qz374 0 2 Ns588p1009 Ns588p139 Ns588p1008 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1011 := nat_lit 320921397190618178843374244997482333819545383869467562981556258179837281 

noncomputable def Ns588p1012 := nat_lit 5286953389572196560936652584728036769586770500561492077566876904801 

noncomputable def Ns588p1013 := nat_lit 962753617665075392137000861687277545385096978067401565960513640785702241 

noncomputable def Ns588p1014 := BSN.cos_dyadic_bound_f 218978101 536870912 3 2 536870912 268435456 Ns588p1011 Ns588p152 Ns588p1012 Ns588p1013 Ns588p155 Ns588p1012 492828389 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 218978101) qz375 0 2 Ns588p1011 Ns588p152 Ns588p1012 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 218978101) qz376 0 2 Ns588p1013 Ns588p155 Ns588p1012 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1015 := Ns588p952 207609 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 391269871 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 104 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 492828389 536870912) qz137 rfl rfl (Ns588p1006 rfl) (Ns588p985 rfl) RS589to600.d35 RS589to600.d37 RS589to600.d39 RS589to600.d41 RS589to600.d17 (Ns588p1010 rfl rfl) (Ns588p1014 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1016 := nat_lit 93944162443239477747633827024896 

noncomputable def Ns588p1017 := BSN.sin_dyadic_bound_f 98450392 536870912 2 1 536870912 268435456 Ns588p1016 Ns588p188 Ns588p1016 Ns588p1016 Ns588p189 Ns588p1016 97899544 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 98450392) qz373 0 1 Ns588p1016 Ns588p188 Ns588p1016 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 98450392) qz374 0 1 Ns588p1016 Ns588p189 Ns588p1016 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1018 := nat_lit 16070633667694021450647875436408095237402570085050486346826182459126091105 

noncomputable def Ns588p1019 := nat_lit 4089990980570841113674851217915577718583089643687879791116515931491681 

noncomputable def Ns588p1020 := nat_lit 42083132953801512913703247812430290876890929982375779102978193986203061601 

noncomputable def Ns588p1021 := BSN.sin_dyadic_bound_f 502881077 536870912 3 2 536870912 268435456 Ns588p1018 Ns588p136 Ns588p1019 Ns588p1020 Ns588p139 Ns588p1019 432503683 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 502881077) qz373 0 2 Ns588p1018 Ns588p136 Ns588p1019 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 502881077) qz374 0 2 Ns588p1020 Ns588p139 Ns588p1019 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1022 := Ns588p950 241835 BSN.abs_quadSignPos (BSN.cos_quad_nat3 171 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 97899544 536870912) BSN.abs_quadSignPos qz634 (BSN.sfrac_eq_quadSignPos_mul Bool.false 432503683 536870912) qz137 rfl rfl (Ns588p1015 rfl) (Ns588p985 rfl) RS589to600.d43 RS589to600.d45 RS589to600.d47 RS589to600.d49 RS589to600.d17 (Ns588p1017 rfl rfl) (Ns588p1021 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1023 := nat_lit 30012265582026533427610667013027594489099246311324733721024873097044529693708557316437539282594161297288588090241 

noncomputable def Ns588p1024 := nat_lit 10294673743191122918678634672973481086875497089414771713624917421924726505490093225099555057388287389784961 

noncomputable def Ns588p1025 := nat_lit 181885459945985097626006379958616114780148715842779708796884540352673796871060094320933778998014560886953081756545 

noncomputable def Ns588p1026 := BSN.cos_dyadic_bound_f 682942881 536870912 4 3 536870912 268435456 Ns588p1023 Ns588p146 Ns588p1024 Ns588p1025 Ns588p149 Ns588p1024 157997560 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 682942881) qz375 0 3 Ns588p1023 Ns588p146 Ns588p1024 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 682942881) qz376 0 3 Ns588p1025 Ns588p149 Ns588p1024 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1027 := Ns588p948 Bool.true 732411739 241835 Bool.true 682942881 28296951008113761 1 Bool.false 157997560 Bool.true Bool.true 778021708 257831 BSN.abs_quadSignNeg qz398 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 157997560 536870912) qz137 rfl (Ns588p1022 rfl) (Ns588p985 rfl) RS589to600.d51 RS589to600.d53 RS589to600.d17 (Ns588p1026 rfl rfl) rfl 

noncomputable def Ns588p1028 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) 778021708 536870912 257831 536870912 778021708 536870912 257831 536870912 835394447859515392 194505427 67108864 257831 268435456 (Ns588p1027 rfl rfl rfl rfl) 

noncomputable def Ns588p1029 := @Enclosure.Real.IsNear.mulLit_ff qz661 (Zeta.RiemannSiegel.correction qz136) 18909391 67108864 1 67108864 448900854359763 1125899906842624 4571114667942491 383157812047380480000 8488441775322813234333 75557863725914323419136 

noncomputable abbrev qz665 := (@HPow.hPow Real Real Real qz7 qz135 qz9)

noncomputable def Ns588p1030 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz665 1 1 0 1 18909391 67108864 1 67108864 18909391 67108864 1 67108864 

noncomputable def Ns588p1031 := @Enclosure.Real.IsNear.sqrt_image qz135 10646069467199 67108864000 996757 67108864000 422624408 422624448 33554432 (@Enclosure.Real.IsNear.of_eq qz135 (@HMul.hMul Real Real Real qz5 qz134 qz3) Bool.false 10646069467199 67108864000 996757 67108864000 (BSN.t_div_two_pi_mk qz134 996757 1000 qz137) (@Enclosure.Real.IsNear.mulLit_ff qz134 qz3 996757 1000 0 1 10680707 67108864 1 67108864 10646069467199 67108864000 996757 67108864000 (Enclosure.Real.IsNear.const Bool.false 996757 1000) RS589to600.d56 rfl)) 

noncomputable abbrev qz771 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 996757 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz666 := qz771

noncomputable abbrev qz469 := qz666

noncomputable abbrev qz143 := qz469

noncomputable def Ns588p1032 := @Enclosure.Real.IsNear.sqrt_image qz143 105656107 8388608 5 8388608 119083676 119083682 33554432 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 845248856 67108864 40 67108864 105656107 8388608 5 8388608 (Ns588p1031 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns588p1033 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz143) 119083679 33554432 3 33554432 9454695 9454696 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz143) Bool.false 238167358 67108864 6 67108864 119083679 33554432 3 33554432 (Ns588p1032 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns588p1034 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 18909391 67108864 1 67108864 18909391 67108864 1 67108864 (Ns588p1033 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz144 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz463))

noncomputable abbrev qz667 := (@HMul.hMul Real Real Real qz739 qz770 qz770)

noncomputable abbrev qz470 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz667 qz660) qz603)

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz470))

noncomputable def Ns588p1035 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz136) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz144) qz145) Bool.false 448900854359763 

noncomputable def Ns588p1036 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz144) qz145 40602601 33554432 95 

noncomputable abbrev qz668 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz144))

noncomputable def Ns588p1037 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz144) (@Neg.neg Real Real.instNeg qz668) Bool.true 40602601 33554432 95 16777216 (BSN.inv_eq_neg_inv_neg qz144) 

noncomputable def Ns588p1038 := @Enclosure.Real.IsNear.recentre' qz668 Bool.false 81205202 67108864 380 67108864 40602601 33554432 

noncomputable def Ns588p1039 := @Enclosure.Real.IsNear.recentre' qz144 Bool.true 55459497 67108864 2822278864 730815528960000 55459497 67108864 176392429 45675970560000 

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz355 qz352 qz463)

noncomputable def Ns588p1040 := @Enclosure.Real.IsNear.cos_image qz146 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 250966053) qz371) Bool.false 250966053 67108864 253 67108864 Bool.true 55459497 67108864 1 

noncomputable def Ns588p1041 := nat_lit 134930377088108147196062947 

noncomputable def Ns588p1042 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz136 884279719003555 140737488355328 1 500000000000000 4992811 8388608 5 8388608 4415041508117858443105 1180591620717411303424 Ns588p1041 

noncomputable def Ns588p1043 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz1 105656107 8388608 5 8388608 12 1 0 1 4992811 4992811 8388608 5 

noncomputable def Ns588p1044 := @Ns588p1043 8388608 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 845248856 67108864 40 67108864 105656107 8388608 5 8388608 (Ns588p1031 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns588p1045 := @Enclosure.Real.IsNear.recentre' qz146 Bool.false 4415041508117858443105 1180591620717411303424 Ns588p1041 Ns588p206 250966053 67108864 253 67108864 (@Ns588p1042 Ns588p206 RS589to600.d55 (Ns588p1044 rfl rfl) rfl) 

noncomputable def Ns588p1046 := nat_lit 5784400139659505330814976 

noncomputable def Ns588p1047 := nat_lit 27371325358774713256652846196043502273000096849730222851260946988219874722263502675377022081 

noncomputable def Ns588p1048 := nat_lit 2084626331133301684244675256170089287230798672084244259009761199083227516660503589840001 

noncomputable def Ns588p1049 := nat_lit 82109806823661873166590049237618166640425828951846500065264821442261457711757187018951386241 

noncomputable def Ns588p1050 := BSN.cos_dyadic_bound_f 82201269999 137438953472 3 2 67108864 21801270 Ns588p1047 Ns588p511 Ns588p1048 Ns588p1049 Ns588p514 Ns588p1048 55459497 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 82201269999) qz383 0 2 Ns588p1047 Ns588p511 Ns588p1048 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 82201269999) qz384 0 2 Ns588p1049 Ns588p514 Ns588p1048 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1051 := @Ns588p1040 10890000 (Ns588p1045 rfl) (Enclosure.sfrac_false_div 250966053 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 250966053) qz371) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns588p1046) qz372) 226375608064910080 72057594037927936 Bool.false 55459497 67108864 0 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 250966053 67108864 226375608064910080 72057594037927936 0 Ns588p1046 Ns588p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 55459497 67108864 Ns588p1046 Ns588p114 82201269999 137438953472 21801270 21780000 (Ns588p1050 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p1052 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz144) 55459497 67108864 176392429 45675970560000 40602411 40602791 33554432 (@Enclosure.Real.IsNear.neg qz144 Bool.true 55459497 67108864 176392429 45675970560000 (Ns588p1039 (Ns588p1051 rfl rfl) rfl)) 

noncomputable def Ns588p1053 := Ns588p1037 (@Enclosure.Real.IsNear.neg qz668 Bool.false 40602601 33554432 95 16777216 (@Ns588p1038 95 16777216 (Ns588p1052 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p1054 := @Enclosure.Real.IsNear.recentre' qz145 Bool.true 11055963 33554432 

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz355 qz352 qz470)

noncomputable def Ns588p1055 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 63973647)) qz397) Bool.true 63973647 33554432 

noncomputable def Ns588p1056 := nat_lit 18881688041145709902643604405 

noncomputable def Ns588p1057 := nat_lit 2479242456650899684384056887611057 

noncomputable def Ns588p1058 := @Enclosure.Real.IsNear.recentre' qz147 Bool.true Ns588p1056 Ns588p352 Ns588p1057 

noncomputable abbrev qz148 := qz470

noncomputable def Ns588p1059 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz148 884279719003555 140737488355328 1 500000000000000 21352619126471 

noncomputable abbrev qz471 := (@HSub.hSub Real Real Real qz592 qz667 qz660)

noncomputable abbrev qz149 := qz471

noncomputable def Ns588p1060 := @Enclosure.Real.IsNear.subLit_tf qz149 qz31 16954572615367 70368744177664 91871175 70368744177664 1 16 

noncomputable abbrev qz472 := qz667

noncomputable abbrev qz150 := qz472

noncomputable def Ns588p1061 := @Enclosure.Real.IsNear.subLit_ff_n qz150 qz136 24928161681721 70368744177664 49928135 70368744177664 4992811 8388608 5 8388608 

noncomputable def Ns588p1062 := @Enclosure.Real.IsNear.mulLit_ff qz136 qz136 4992811 8388608 5 8388608 4992811 8388608 5 8388608 24928161681721 70368744177664 

noncomputable def Ns588p1063 := nat_lit 541421380982603687977442121758881863034696037181793702604788010384884235019780578119510297740825921 

noncomputable def Ns588p1064 := nat_lit 4699085157156219013745091312476733419610343400177129602217925734033668305872680683041963627841 

noncomputable def Ns588p1065 := nat_lit 3267511530127588273442891449320641299084970497387208517036386357651893071319442957191107715329414465 

noncomputable def Ns588p1066 := BSN.cos_dyadic_bound_t 63973647 33554432 4 3 33554432 10890000 Ns588p1063 Ns588p361 Ns588p1064 Ns588p1065 Ns588p364 Ns588p1064 11055963 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 63973647) (BSN.cosEvenQ 33554432) 0 3 Ns588p1063 Ns588p361 Ns588p1064 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 63973647) (BSN.cosOddQ 33554432) 0 3 Ns588p1065 Ns588p364 Ns588p1064 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1067 := @Ns588p1054 759798608 91351941120000 11055963 33554432 47487413 5709496320000 (@Ns588p1055 69 8388608 Bool.true 11055963 33554432 1 10890000 (@Ns588p1058 Ns588p355 63973647 33554432 69 8388608 (@Ns588p1059 70368744177664 91871175 70368744177664 Ns588p1056 Ns588p352 Ns588p1057 Ns588p355 RS589to600.d55 (@Ns588p1060 0 1 341641906023536 21352619126471 70368744177664 91871175 70368744177664 (@Ns588p1061 142225263477848539136 16954572615367 70368744177664 91871175 70368744177664 (@Ns588p1062 49928135 70368744177664 (Ns588p1044 rfl rfl) (Ns588p1044 rfl rfl) rfl) (Ns588p1044 rfl rfl) rfl rfl) qz388 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 63973647 33554432) (BSN.cos_neg_of_bound 63973647 33554432 Bool.true 11055963 33554432 1 10890000 (Ns588p1066 rfl rfl)) rfl rfl) 

noncomputable def Ns588p1068 := @Ns588p1029 173179531410147405242819 Ns588p945 (Ns588p1030 qz33 (@Enclosure.Real.IsNear.of_eq qz665 (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 18909391 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz135 (BSN.t_div_two_pi_nonneg qz134 996757 1000 qz137)) Ns588p1034) rfl) (@Ns588p1035 1125899906842624 4571114667942491 383157812047380480000 (BSN.correction_mk qz136 (BSN.cos_two_pi_p_ne_zero_mk qz134 996757 1000 12 qz137 rfl rfl (@BSN.floor_sqrt_eq_dec qz134 996757 1000 12 qz137 rfl rfl rfl))) (@Ns588p1036 16777216 11055963 33554432 47487413 5709496320000 448900854359763 1125899906842624 4571114667942491 383157812047380480000 Ns588p1053 (Ns588p1067 rfl) rfl)) 

noncomputable def Ns588p1069 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (hardyZApproximantRS₀ qz134) Bool.true 227482083915007616154781 75557863725914323419136 Ns588p944 Ns588p945 (@Eq.refl Real (hardyZApproximantRS₀ qz134)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HMul.hMul Real Real Real qz5 qz661 (Zeta.RiemannSiegel.correction qz136))) Bool.true 227482083915007616154781 75557863725914323419136 Ns588p944 Ns588p945 (BSN.hardyZApproximantRS₀_eq qz134 12 (@BSN.floor_sqrt_eq_dec qz134 996757 1000 12 qz137 rfl rfl rfl)) (@Ns588p947 227482083915007616154781 75557863725914323419136 Ns588p944 Ns588p945 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12)) Bool.true 194505427 67108864 257831 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (Ns588p1028 (Ns588p1027 rfl rfl rfl rfl) rfl rfl)) (Ns588p1068 rfl) rfl rfl)) 

theorem RS589to600.d65 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz134) Bool.true 227482083915007616154781 75557863725914323419136 Ns588p944 Ns588p945 := Ns588p1069 

noncomputable def Ns588p1070 := nat_lit 2068329359657870810280587 

noncomputable def Ns588p1071 := nat_lit 362234086983200433117658611712 

noncomputable abbrev qz772 := (Enclosure.sfrac Bool.false 997997 1000)

noncomputable abbrev qz669 := qz772

noncomputable abbrev qz473 := qz669

noncomputable abbrev qz151 := qz473

noncomputable abbrev qz773 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 997997 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz670 := qz773

noncomputable abbrev qz474 := qz670

noncomputable abbrev qz152 := qz474

noncomputable abbrev qz774 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 997997 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz671 := qz774

noncomputable abbrev qz475 := qz671

noncomputable abbrev qz153 := qz475

noncomputable abbrev qz672 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz152 qz9))

noncomputable def Ns588p1072 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 12) (@HMul.hMul Real Real Real qz5 qz672 (Zeta.RiemannSiegel.correction qz153)) 644006201 268435456 258143 268435456 66757482707969996775 590295810358705651712 7714628921476242600587 Ns588p403 Ns588p1071 

noncomputable def Ns588p1073 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.cos BSN.quadSignNeg 11 12 997997 1000 286 536870912 268435456 9007199254740992 Bool.false 1089563382772 4545 1334074092 51 154981288 8 

noncomputable def Ns588p1074 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 997997 1000 170 231 536870912 268435456 9007199254740992 Bool.false 1089563382772 4545 

noncomputable def Ns588p1075 := Ns588p1074 1236190956 51 169773496 8 1287360220 51 161872664 8 Bool.false 603452875 207859 Bool.true 787957132 Bool.true 412522848 28296951008113761 1 Bool.false 55259682 Bool.true Bool.false 373111302 Bool.false Bool.false 698475514 

noncomputable def Ns588p1076 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 997997 1000 29 103 536870912 268435456 9007199254740992 Bool.false 1089563382772 4545 

noncomputable def Ns588p1077 := Ns588p1076 1116391676 51 189812536 8 1179625948 51 178956968 8 Bool.false 472084450 169756 Bool.true 136029861 Bool.true 838344231 28296951008113761 1 Bool.false 134579027 Bool.true Bool.false 536847901 Bool.false Bool.false 603452875 

noncomputable def Ns588p1078 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 997997 1000 153 55 536870912 268435456 9007199254740992 Bool.false 1089563382772 4545 

noncomputable def Ns588p1079 := Ns588p1078 961943533 51 219176632 8 1044702541 51 202918136 8 Bool.false 475194537 126146 Bool.false 519449619 Bool.false 571063852 28296951008113761 1 Bool.false 442112354 Bool.true Bool.false 469307395 Bool.false Bool.false 472084450 

noncomputable def Ns588p1080 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 997997 1000 411 269 536870912 268435456 9007199254740992 Bool.false 1089563382772 4545 

noncomputable def Ns588p1081 := Ns588p1080 744261104 50 268435448 8 864060384 50 240095976 8 Bool.false 538657219 74555 Bool.false 190627728 Bool.false 382015313 28296951008113761 1 Bool.false 186647306 Bool.false Bool.false 350584888 Bool.true Bool.false 475194537 

noncomputable def Ns588p1082 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 997997 1000 851 594 536870912 268435456 9007199254740992 Bool.false 1089563382772 4545 

noncomputable def Ns588p1083 := Ns588p1082 372130544 50 379625064 8 589812976 50 309962568 8 Bool.false 536870584 4602 Bool.false 517273342 Bool.false 2777382 28296951008113761 1 Bool.false 440874083 Bool.false Bool.false 536863727 Bool.true Bool.false 538657219 

noncomputable def Ns588p1084 := nat_lit 325102749278273013328411974292112320739967106954607887256939 

noncomputable def Ns588p1085 := nat_lit 160190964801541580888524186584933553550708558763393024000 

noncomputable def Ns588p1086 := nat_lit 17842176000000000000000000 

noncomputable def Ns588p1087 := nat_lit 475212321285658659074051403083360000 

noncomputable def Ns588p1088 := nat_lit 2845563159353431730532054661341120179520 

noncomputable abbrev qz673 := (@Eq.refl Real qz772)

noncomputable abbrev qz476 := qz673

noncomputable abbrev qz154 := qz476

noncomputable def Ns588p1089 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz151 997997 1000 3983993048036 16000000 1995994 4000 2000 Ns588p1087 Ns588p1088 qz154 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns588p1090 := nat_lit 104032879769047364265091831773475942636789474225474523922220480 

noncomputable abbrev qz674 := (@HSub.hSub Real Real Real qz743 qz744 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz745 (@Nat.cast Real Real.instNatCast 1995994))))

noncomputable abbrev qz477 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 997997 4000) (Real.log (Enclosure.sfrac Bool.false 3983993048036 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz674))

noncomputable abbrev qz675 := (Enclosure.sfrac Bool.false 997997 2000)

noncomputable abbrev qz155 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz477 qz675) (@HMul.hMul Real Real Real qz355 qz675 (Real.log Real.pi)))

noncomputable def Ns588p1091 := @Enclosure.Real.IsNear.addLit_ft_p qz155 (Enclosure.sfrac Bool.true Ns588p1087 Ns588p1088) 36559683445349998057499 18014398509481984000 151008348855715335131 Ns588p1086 Ns588p1087 Ns588p1088 0 1 Ns588p1090 

noncomputable def Ns588p1092 := nat_lit 2453478824217044452040964571136000 

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz359 qz477 qz675)

noncomputable def Ns588p1093 := @Enclosure.Real.IsNear.subLit_ff_p qz156 (@HMul.hMul Real Real Real qz5 qz675 (Real.log Real.pi)) 46849841036972896999451 18014398509481984000 12574980976462961 4356000000000000000000 38333824245717 67108864000 2993991 536870912000 Ns588p1092 36559683445349998057499 18014398509481984000 

noncomputable def Ns588p1094 := nat_lit 3747987282957831759956080 

noncomputable abbrev qz157 := qz477

noncomputable def Ns588p1095 := @Enclosure.Real.IsNear.subLit_ff_p qz157 qz675 2233559954864265711699 720575940379279360 12574980976462961 4356000000000000000000 997997 2000 0 1 Ns588p1094 46849841036972896999451 18014398509481984000 12574980976462961 4356000000000000000000 

noncomputable def Ns588p1096 := nat_lit 5029529890218184461936948462697316352 

noncomputable def Ns588p1097 := nat_lit 120169222915707801855590400 

noncomputable def Ns588p1098 := nat_lit 120524079791683615934212189024286478508733930510110505497787467477031203013983550746044302555188968685317889718455737824261435789880124167255441065257953871134033428114885479107688666088873522692159779673787596800 

noncomputable def Ns588p1099 := nat_lit 4107719812370634922779791955319288796562780528392808665076361554997481173027333916663800018996245367087065246522701487069187279006010294054236014882721327167194779466057539591674680479825060343516536108461588480 

noncomputable def Ns588p1100 := nat_lit 52314750253524439488135783721066040521843841406000893153397677545668975593438950202185268698567617668641900208017948046527445671758380256566698530086076567297111037690313481624671965806831175561799270400 

noncomputable def Ns588p1101 := BSN.log_dyadic_bound 1886841048036 6081145048036 9 8 Ns588p1098 268435456 87120000 Ns588p1099 Ns588p1100 172256202 7967986096072 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1886841048036) (BSN.artanhQ 6081145048036) 0 8 Ns588p1099 Ns588p1098 Ns588p1100 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz478 := (Real.log (Enclosure.sfrac Bool.false 3983993048036 16000000))

noncomputable def Ns588p1102 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 997997 4000) qz478 997997 4000 0 1 55958155037699175 4503599627370496 12500018513 1089000000000000000 2233842834126346542099 720575940379279360 1134089179628951 396000000000000000000 (Enclosure.Real.IsNear.const Bool.false 997997 4000) (BSN.isNear_log_sfrac 3983993048036 16000000 55958155037699175 4503599627370496 12500018513 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3983993048036) qz362)) Bool.false Ns588p1097 Ns588p114 1000001481040000 87120000000000000000000 55958155037699175 4503599627370496 12500018513 1089000000000000000 (BSN.log_rat_reduce_isNear 3983993048036 16000000 17 7967986096072 4194304000000 172256202 268435456 24973259072661432 36028797018963968 87120000 1000000000000000 rfl rfl rfl rfl (Ns588p1101 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p1103 := BSN.arctan_dyadic_bound_f 1000 1995994 1 0 33554432 10890000 0 1 1 0 1 1 16810 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1995994) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1995994) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns588p1104 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1995994))) 884279719003555 562949953421312 1 2000000000000000 16810 33554432 1 10890000 29662040511566881751040 883997694002595 562949953421312 200000001089 2178000000000000000 qz17 (Ns588p1103 rfl) rfl rfl 

noncomputable abbrev qz479 := (@HMul.hMul Real Real Real qz588 qz593 qz674)

noncomputable abbrev qz158 := qz479

noncomputable abbrev qz480 := qz674

noncomputable abbrev qz159 := qz480

noncomputable def Ns588p1105 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 997997 4000) qz478) qz158 2233842834126346542099 720575940379279360 1134089179628951 396000000000000000000 883997694002595 2251799813685248 200000001089 8712000000000000000 Ns588p1096 2233559954864265711699 720575940379279360 12574980976462961 4356000000000000000000 (Ns588p1102 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz159 1 4 0 1 883997694002595 562949953421312 200000001089 2178000000000000000 883997694002595 2251799813685248 200000001089 8712000000000000000 qz369 Ns588p1104 rfl) 

noncomputable def Ns588p1106 := @Ns588p1091 Ns588p1084 Ns588p1085 151008348855715335131 Ns588p1086 (@Ns588p1093 151008348855715335131 Ns588p1086 (Ns588p1095 (Ns588p1105 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 997997 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz675 (Real.log Real.pi) 997997 2000 0 1 38410761 33554432 3 268435456 38333824245717 67108864000 2993991 536870912000 (Enclosure.Real.IsNear.const Bool.false 997997 2000) RS589to600.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns588p1087 Ns588p1088) 

noncomputable def Ns588p1107 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz151) Bool.false Ns588p1084 Ns588p1085 151008348855715335131 Ns588p1086 68097711423 33554432 569 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz151) (@HAdd.hAdd Real Real Real qz370 qz155 (Enclosure.sfrac Bool.true Ns588p1087 Ns588p1088)) Bool.false Ns588p1084 Ns588p1085 151008348855715335131 Ns588p1086 Ns588p1089 (Ns588p1106 rfl rfl)) 

noncomputable def Ns588p1108 := BSN.cos_dyadic_bound_f 150560728 137438953472 1 0 67108864 21801270 0 1 1 0 1 1 67108823 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 150560728) qz383 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 150560728) qz384 0 0 rfl) rfl rfl 

noncomputable def Ns588p1109 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz151) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 68097711423) qz397) Bool.false 68097711423 33554432 569 67108864 Bool.false 67108823 67108864 1 10890000 (Ns588p1107 rfl) (Enclosure.sfrac_false_div 68097711423 33554432) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 68097711423) qz397) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5297384705295002894336) qz611) 226375608064910080 72057594037927936 Bool.false 67108823 67108864 323 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q0 68097711423 33554432 226375608064910080 72057594037927936 323 5297384705295002894336 Ns588p278 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108823 67108864 5297384705295002894336 Ns588p278 150560728 137438953472 21801270 21780000 (Ns588p1108 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p1110 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz151) Bool.false Ns588p1084 Ns588p1085 151008348855715335131 Ns588p1086 1089563382772 536870912 4545 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz151) (@HAdd.hAdd Real Real Real qz370 qz155 (Enclosure.sfrac Bool.true Ns588p1087 Ns588p1088)) Bool.false Ns588p1084 Ns588p1085 151008348855715335131 Ns588p1086 Ns588p1089 (Ns588p1106 rfl rfl)) 

noncomputable def Ns588p1111 := Ns588p1083 74555 BSN.abs_quadSignPos (BSN.cos_quad_nat3 851 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 440874083 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 594 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536863727 536870912) qz154 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 1) Bool.false 67108823 67108864 391469929 45675970560000 536870584 536870912 4602 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz151)) Bool.false 67108823 67108864 391469929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz151) qz151) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz151)) Bool.false 67108823 67108864 6263518864 730815528960000 67108823 67108864 391469929 45675970560000 (Ns588p1109 rfl rfl) rfl)) rfl) (Ns588p1110 rfl) RS589to600.d7 

noncomputable def Ns588p1112 := nat_lit 17991419178486314739621806185514168381868244313746364890109771012857135360 

noncomputable def Ns588p1113 := nat_lit 5125789638193332541098444219192449304989281313358862854666946101903616 

noncomputable def Ns588p1114 := nat_lit 47112084665192797017752475861896510367923038175780755600903749025698939136 

noncomputable def Ns588p1115 := BSN.sin_dyadic_bound_f 517273342 536870912 3 2 536870912 268435456 Ns588p1112 Ns588p136 Ns588p1113 Ns588p1114 Ns588p139 Ns588p1113 440874083 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 517273342) qz373 0 2 Ns588p1112 Ns588p136 Ns588p1113 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 517273342) qz374 0 2 Ns588p1114 Ns588p139 Ns588p1113 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1116 := BSN.cos_dyadic_bound_f 2777382 536870912 1 0 536870912 268435456 0 1 1 0 1 1 536863727 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 2777382) qz375 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 2777382) qz376 0 0 rfl) rfl rfl 

noncomputable def Ns588p1117 := nat_lit 1320517883143323437001301525856256 

noncomputable def Ns588p1118 := BSN.sin_dyadic_bound_f 190627728 536870912 2 1 536870912 268435456 Ns588p1117 Ns588p188 Ns588p1117 Ns588p1117 Ns588p189 Ns588p1117 186647306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 190627728) qz373 0 1 Ns588p1117 Ns588p188 Ns588p1117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 190627728) qz374 0 1 Ns588p1117 Ns588p189 Ns588p1117 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1119 := nat_lit 5350830409210308897534276723755055450589371054493728570850578069476701825 

noncomputable def Ns588p1120 := nat_lit 453571935374407785716678979367997929344531528766110653559558128891521 

noncomputable def Ns588p1121 := nat_lit 14013345288607821880936707272439501802515128282151286839740988992611251841 

noncomputable def Ns588p1122 := BSN.sin_dyadic_bound_f 382015313 536870912 3 2 536870912 268435456 Ns588p1119 Ns588p136 Ns588p1120 Ns588p1121 Ns588p139 Ns588p1120 350584888 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 382015313) qz373 0 2 Ns588p1119 Ns588p136 Ns588p1120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 382015313) qz374 0 2 Ns588p1121 Ns588p139 Ns588p1120 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1123 := Ns588p1081 126146 BSN.abs_quadSignPos (BSN.cos_quad_nat3 411 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 186647306 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 269 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 350584888 536870912) qz154 rfl rfl (Ns588p1111 RS589to600.d9 RS589to600.d11 RS589to600.d13 RS589to600.d17 (Ns588p1115 rfl rfl) (Ns588p1116 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns588p1110 rfl) RS589to600.d19 RS589to600.d21 RS589to600.d23 RS589to600.d25 RS589to600.d17 (Ns588p1118 rfl rfl) (Ns588p1122 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns588p1124 := nat_lit 18296198209123233736146110124754093799711116378172237583342696406607837985 

noncomputable def Ns588p1125 := nat_lit 5300873697253706022227494279069499933024177066156989749323473833278241 

noncomputable def Ns588p1126 := nat_lit 47910031990289106165870491526475561713637551370439225211065300202528553761 

noncomputable def Ns588p1127 := BSN.sin_dyadic_bound_f 519449619 536870912 3 2 536870912 268435456 Ns588p1124 Ns588p136 Ns588p1125 Ns588p1126 Ns588p139 Ns588p1125 442112354 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 519449619) qz373 0 2 Ns588p1124 Ns588p136 Ns588p1125 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 519449619) qz374 0 2 Ns588p1126 Ns588p139 Ns588p1125 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1128 := nat_lit 26729065543387329898483434471587367604647226538873186820316920711682785280 

noncomputable def Ns588p1129 := nat_lit 11310384356283341015233909535847063204269574288174601542043725327302656 

noncomputable def Ns588p1130 := nat_lit 69986383419913786229622425857766019909840585433915587555476245356258328576 

noncomputable def Ns588p1131 := BSN.sin_dyadic_bound_f 571063852 536870912 3 2 536870912 268435456 Ns588p1128 Ns588p136 Ns588p1129 Ns588p1130 Ns588p139 Ns588p1129 469307395 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 571063852) qz373 0 2 Ns588p1128 Ns588p136 Ns588p1129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 571063852) qz374 0 2 Ns588p1130 Ns588p139 Ns588p1129 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1132 := Ns588p1079 169756 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 153 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 442112354 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 469307395 536870912) qz154 rfl rfl (Ns588p1123 rfl rfl) (Ns588p1110 rfl) RS589to600.d27 RS589to600.d29 RS589to600.d31 RS589to600.d33 RS589to600.d17 (Ns588p1127 rfl rfl) (Ns588p1131 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1133 := nat_lit 342402571095953903683194763021041 

noncomputable def Ns588p1134 := BSN.sin_dyadic_bound_f 136029861 536870912 2 1 536870912 268435456 Ns588p1133 Ns588p188 Ns588p1133 Ns588p1133 Ns588p189 Ns588p1133 134579027 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 136029861) qz373 0 1 Ns588p1133 Ns588p188 Ns588p1133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 136029861) qz374 0 1 Ns588p1133 Ns588p189 Ns588p1133 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1135 := nat_lit 177256003249821143977971219786084541849826217357844279828675953486250294476619637414787261254067069456885081049761 

noncomputable def Ns588p1136 := nat_lit 120522619261485186832120713644480029287091871518979269503392534695859915276728117498367130542568643250752161 

noncomputable def Ns588p1137 := nat_lit 885204401502435117424571234657299820290309545972528263899561536149441687388361621872916529388198895610899179113121 

noncomputable def Ns588p1138 := BSN.sin_dyadic_bound_f 838344231 536870912 4 3 536870912 268435456 Ns588p1135 Ns588p172 Ns588p1136 Ns588p1137 Ns588p175 Ns588p1136 536847901 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 838344231) qz373 0 3 Ns588p1135 Ns588p172 Ns588p1136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 838344231) qz374 0 3 Ns588p1137 Ns588p175 Ns588p1136 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1139 := Ns588p1077 207859 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134579027 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 103 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536847901 536870912) qz154 rfl rfl (Ns588p1132 rfl) (Ns588p1110 rfl) RS589to600.d35 RS589to600.d37 RS589to600.d39 RS589to600.d41 RS589to600.d17 (Ns588p1134 rfl rfl) (Ns588p1138 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1140 := nat_lit 53246787250166604507741410391858132816714184961258267255318876288854125501598512517424337584306048107254598598656 

noncomputable def Ns588p1141 := nat_lit 57283703666875381488282265853916806489543436790911377951755599838502853264808725731562232399078591169560576 

noncomputable def Ns588p1142 := nat_lit 322437054051811080725731371698583572186451408775067781864264573065857659873833451191578310271908238605209619660800 

noncomputable def Ns588p1143 := BSN.cos_dyadic_bound_f 787957132 536870912 4 3 536870912 268435456 Ns588p1140 Ns588p146 Ns588p1141 Ns588p1142 Ns588p149 Ns588p1141 55259682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 787957132) qz375 0 3 Ns588p1140 Ns588p146 Ns588p1141 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 787957132) qz376 0 3 Ns588p1142 Ns588p149 Ns588p1141 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1144 := nat_lit 7276178980177508810713885698696725130997027977106222183090439089689722880 

noncomputable def Ns588p1145 := nat_lit 838656387702873300258432320222559147329508512680050387424438288121856 

noncomputable def Ns588p1146 := nat_lit 19055301409170527947478806034734872152087015973876718969371510430054219776 

noncomputable def Ns588p1147 := BSN.sin_dyadic_bound_f 412522848 536870912 3 2 536870912 268435456 Ns588p1144 Ns588p136 Ns588p1145 Ns588p1146 Ns588p139 Ns588p1145 373111302 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 412522848) qz373 0 2 Ns588p1144 Ns588p136 Ns588p1145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 412522848) qz374 0 2 Ns588p1146 Ns588p139 Ns588p1145 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1148 := Ns588p1075 242128 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 170 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55259682 536870912) BSN.abs_quadSignPos qz634 (BSN.sfrac_eq_quadSignPos_mul Bool.false 373111302 536870912) qz154 rfl rfl (Ns588p1139 rfl) (Ns588p1110 rfl) RS589to600.d43 RS589to600.d45 RS589to600.d47 RS589to600.d49 RS589to600.d17 (Ns588p1143 rfl rfl) (Ns588p1147 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1149 := nat_lit 24697737832501243423894308458601940453609611909347548291380082782556095934437937986009504584112657648190285476721 

noncomputable def Ns588p1150 := nat_lit 5741780001055356748068041986448379282630805188421353043062310798456271278105806136568870414073008673321841 

noncomputable def Ns588p1151 := nat_lit 149704920869178518035074571162508123127358436044691218357967389371513947071912100371983360418887366795067591553905 

noncomputable def Ns588p1152 := BSN.cos_dyadic_bound_f 650509853 536870912 4 3 536870912 268435456 Ns588p1149 Ns588p146 Ns588p1150 Ns588p1151 Ns588p149 Ns588p1150 188687226 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 650509853) qz375 0 3 Ns588p1149 Ns588p146 Ns588p1150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 650509853) qz376 0 3 Ns588p1151 Ns588p149 Ns588p1150 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1153 := Ns588p1073 Bool.false 698475514 242128 Bool.true 650509853 28296951008113761 1 Bool.false 188687226 Bool.true Bool.false 644006201 258143 BSN.abs_quadSignNeg qz398 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 188687226 536870912) qz154 rfl (Ns588p1148 rfl) (Ns588p1110 rfl) RS589to600.d51 RS589to600.d53 RS589to600.d17 (Ns588p1152 rfl rfl) rfl 

noncomputable def Ns588p1154 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 12) 644006201 536870912 258143 536870912 644006201 536870912 258143 536870912 691496392929050624 644006201 268435456 258143 268435456 (Ns588p1153 rfl rfl rfl rfl) 

noncomputable def Ns588p1155 := @Enclosure.Real.IsNear.mulLit_ff qz672 (Zeta.RiemannSiegel.correction qz153) 9451757 33554432 1 33554432 7062970695075 17592186044416 4880990608003159 383157812047380480000 66757482707969996775 590295810358705651712 

noncomputable abbrev qz676 := (@HPow.hPow Real Real Real qz7 qz152 qz9)

noncomputable def Ns588p1156 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz676 1 1 0 1 9451757 33554432 1 33554432 9451757 33554432 1 33554432 

noncomputable def Ns588p1157 := @Enclosure.Real.IsNear.sqrt_image qz152 10659313543879 67108864000 997997 67108864000 422887205 422887246 33554432 (@Enclosure.Real.IsNear.of_eq qz152 (@HMul.hMul Real Real Real qz5 qz151 qz3) Bool.false 10659313543879 67108864000 997997 67108864000 (BSN.t_div_two_pi_mk qz151 997997 1000 qz154) (@Enclosure.Real.IsNear.mulLit_ff qz151 qz3 997997 1000 0 1 10680707 67108864 1 67108864 10659313543879 67108864000 997997 67108864000 (Enclosure.Real.IsNear.const Bool.false 997997 1000) RS589to600.d56 rfl)) 

noncomputable abbrev qz775 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 997997 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz677 := qz775

noncomputable abbrev qz481 := qz677

noncomputable abbrev qz160 := qz481

noncomputable def Ns588p1158 := @Enclosure.Real.IsNear.sqrt_image qz160 845774451 67108864 41 67108864 119120694 119120701 33554432 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 845774451 67108864 41 67108864 845774451 67108864 41 67108864 (Ns588p1157 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns588p1159 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz160) 238241395 67108864 7 67108864 9451756 9451758 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz160) Bool.false 238241395 67108864 7 67108864 238241395 67108864 7 67108864 (Ns588p1158 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns588p1160 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz160)) Bool.false 18903514 67108864 2 67108864 9451757 33554432 1 33554432 (Ns588p1159 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz161 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz475))

noncomputable abbrev qz678 := (@HMul.hMul Real Real Real qz739 qz774 qz774)

noncomputable abbrev qz482 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz678 qz671) qz603)

noncomputable abbrev qz162 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz482))

noncomputable def Ns588p1161 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz153) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz161) qz162) Bool.false 7062970695075 

noncomputable def Ns588p1162 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz161) qz162 42063275 33554432 209 

noncomputable abbrev qz679 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz161))

noncomputable def Ns588p1163 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz161) (@Neg.neg Real Real.instNeg qz679) Bool.true 42063275 33554432 209 33554432 (BSN.inv_eq_neg_inv_neg qz161) 

noncomputable def Ns588p1164 := @Enclosure.Real.IsNear.recentre' qz679 Bool.false 84126550 67108864 418 67108864 42063275 33554432 

noncomputable def Ns588p1165 := @Enclosure.Real.IsNear.recentre' qz161 Bool.true 53533630 67108864 2887618864 730815528960000 26766815 33554432 180476179 45675970560000 

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz355 qz352 qz475)

noncomputable def Ns588p1166 := @Enclosure.Real.IsNear.cos_image qz163 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15891779) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false 15891779 4194304 259 67108864 Bool.true 53533630 67108864 1 

noncomputable def Ns588p1167 := nat_lit 1106429092118424049695554783 

noncomputable def Ns588p1168 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz153 884279719003555 140737488355328 1 500000000000000 40468083 67108864 41 67108864 35785105063852541035065 9444732965739290427392 Ns588p1167 

noncomputable def Ns588p1169 := @Enclosure.Real.IsNear.subLit_ff_p qz160 qz1 845774451 67108864 41 67108864 12 1 0 1 40468083 40468083 67108864 41 

noncomputable def Ns588p1170 := @Ns588p1169 67108864 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 845774451 67108864 41 67108864 845774451 67108864 41 67108864 (Ns588p1157 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns588p1171 := @Enclosure.Real.IsNear.recentre' qz163 Bool.false 35785105063852541035065 9444732965739290427392 Ns588p1167 Ns588p913 15891779 4194304 259 67108864 (@Ns588p1168 Ns588p913 RS589to600.d55 (Ns588p1170 rfl rfl) rfl) 

noncomputable def Ns588p1172 := nat_lit 37554596008119812341071269889124843393674210889501303366122973470105933482080254169182610561 

noncomputable def Ns588p1173 := nat_lit 3924082642713713356038144263248872391322011814863726017881289598587509439287279711921281 

noncomputable def Ns588p1174 := nat_lit 112655939859074009596501733378848032436239988644874182646333157831120625427362187948123989121 

noncomputable def Ns588p1175 := BSN.cos_dyadic_bound_f 88964607727 137438953472 3 2 67108864 21801270 Ns588p1172 Ns588p511 Ns588p1173 Ns588p1174 Ns588p514 Ns588p1173 53533630 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 88964607727) qz383 0 2 Ns588p1172 Ns588p511 Ns588p1173 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 88964607727) qz384 0 2 Ns588p1174 Ns588p514 Ns588p1173 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1176 := @Ns588p1166 10890000 (Ns588p1171 rfl) (Enclosure.sfrac_false_div 15891779 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15891779) (@Nat.cast Real Real.instNatCast 4194304)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 391270482626767537307648) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 53533630 67108864 0 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 15891779 4194304 226375608064910080 72057594037927936 0 391270482626767537307648 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 53533630 67108864 391270482626767537307648 604462909807314587353088 88964607727 137438953472 21801270 21780000 (Ns588p1175 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p1177 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz161) 26766815 33554432 180476179 45675970560000 42063066 42063484 33554432 (@Enclosure.Real.IsNear.neg qz161 Bool.true 26766815 33554432 180476179 45675970560000 (Ns588p1165 (Ns588p1176 rfl rfl) rfl)) 

noncomputable def Ns588p1178 := Ns588p1163 (@Enclosure.Real.IsNear.neg qz679 Bool.false 42063275 33554432 209 33554432 (@Ns588p1164 209 33554432 (Ns588p1177 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p1179 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true 10746432 33554432 

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz355 qz352 qz482)

noncomputable def Ns588p1180 := @Enclosure.Real.IsNear.cos_image qz164 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 127292721)) qz371) Bool.true 127292721 67108864 

noncomputable def Ns588p1181 := nat_lit 1202245760380317637536550367845 

noncomputable def Ns588p1182 := nat_lit 32760274691870628283602955202444701 

noncomputable def Ns588p1183 := @Enclosure.Real.IsNear.recentre' qz164 Bool.true Ns588p1181 Ns588p929 Ns588p1182 

noncomputable def Ns588p1184 := nat_lit 3868562622766813359059763200000000000000 

noncomputable abbrev qz165 := qz482

noncomputable def Ns588p1185 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz165 884279719003555 140737488355328 1 500000000000000 1359576313403479 

noncomputable abbrev qz483 := (@HSub.hSub Real Real Real qz592 qz678 qz671)

noncomputable abbrev qz166 := qz483

noncomputable def Ns588p1186 := @Enclosure.Real.IsNear.subLit_tf qz166 qz31 1078101336692823 4503599627370496 6069847911 4503599627370496 1 16 

noncomputable abbrev qz484 := qz678

noncomputable abbrev qz167 := qz484

noncomputable def Ns588p1187 := @Enclosure.Real.IsNear.subLit_ff_n qz167 qz153 1637665741694889 4503599627370496 3318384487 4503599627370496 40468083 67108864 41 67108864 

noncomputable def Ns588p1188 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz153 40468083 67108864 41 67108864 40468083 67108864 41 67108864 1637665741694889 4503599627370496 

noncomputable def Ns588p1189 := nat_lit 2172282133936709388400806743631878533876769850586368126502345478186148219972837425268573604191532896321 

noncomputable def Ns588p1190 := nat_lit 18098510763099917347226820292934345539660033779930993670054044318011119057782337862995840957567041 

noncomputable def Ns588p1191 := nat_lit 13111242477378848798769541196765029329292920814308875094412443837979683049656737174072577905649387458625 

noncomputable def Ns588p1192 := BSN.cos_dyadic_bound_t 127292721 67108864 4 3 33554432 10890000 Ns588p1189 Ns588p231 Ns588p1190 Ns588p1191 Ns588p234 Ns588p1190 10746432 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 127292721) (BSN.cosEvenQ 67108864) 0 3 Ns588p1189 Ns588p231 Ns588p1190 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 127292721) (BSN.cosOddQ 67108864) 0 3 Ns588p1191 Ns588p234 Ns588p1190 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1193 := @Ns588p1179 6263518864 730815528960000 167913 524288 391469929 45675970560000 (@Ns588p1180 569 67108864 Bool.true 10746432 33554432 1 10890000 (@Ns588p1183 Ns588p1184 127292721 67108864 569 67108864 (@Ns588p1185 4503599627370496 6069847911 4503599627370496 Ns588p1181 Ns588p929 Ns588p1182 Ns588p1184 RS589to600.d55 (@Ns588p1186 0 1 21753221014455664 1359576313403479 4503599627370496 6069847911 4503599627370496 (@Ns588p1187 72350155982336868483072 1078101336692823 4503599627370496 6069847911 4503599627370496 (@Ns588p1188 3318384487 4503599627370496 (Ns588p1170 rfl rfl) (Ns588p1170 rfl rfl) rfl) (Ns588p1170 rfl rfl) rfl rfl) qz388 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 127292721 67108864) (BSN.cos_neg_of_bound 127292721 67108864 Bool.true 10746432 33554432 1 10890000 (Ns588p1192 rfl rfl)) rfl rfl) 

noncomputable def Ns588p1194 := @Ns588p1155 7714628921476242600587 Ns588p403 (Ns588p1156 qz33 (@Enclosure.Real.IsNear.of_eq qz676 (@Inv.inv Real Real.instInv (Real.sqrt qz160)) Bool.false 9451757 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz152 (BSN.t_div_two_pi_nonneg qz151 997997 1000 qz154)) Ns588p1160) rfl) (@Ns588p1161 17592186044416 4880990608003159 383157812047380480000 (BSN.correction_mk qz153 (BSN.cos_two_pi_p_ne_zero_mk qz151 997997 1000 12 qz154 rfl rfl (@BSN.floor_sqrt_eq_dec qz151 997997 1000 12 qz154 rfl rfl rfl))) (@Ns588p1162 33554432 167913 524288 391469929 45675970560000 7062970695075 17592186044416 4880990608003159 383157812047380480000 Ns588p1178 (Ns588p1193 rfl) rfl)) 

noncomputable def Ns588p1195 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz151) (hardyZApproximantRS₀ qz151) Bool.false 1349427130010725681177 590295810358705651712 Ns588p1070 Ns588p403 (@Eq.refl Real (hardyZApproximantRS₀ qz151)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz151) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 12) (@HMul.hMul Real Real Real qz5 qz672 (Zeta.RiemannSiegel.correction qz153))) Bool.false 1349427130010725681177 590295810358705651712 Ns588p1070 Ns588p403 (BSN.hardyZApproximantRS₀_eq qz151 12 (@BSN.floor_sqrt_eq_dec qz151 997997 1000 12 qz154 rfl rfl rfl)) (@Ns588p1072 1349427130010725681177 590295810358705651712 Ns588p1070 Ns588p403 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 12)) Bool.false 644006201 268435456 258143 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz151) qz151 12) (Ns588p1154 (Ns588p1153 rfl rfl rfl rfl) rfl rfl)) (Ns588p1194 rfl) rfl rfl)) 

theorem RS589to600.d66 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz151) Bool.false 1349427130010725681177 590295810358705651712 Ns588p1070 Ns588p403 := Ns588p1195 

noncomputable def Ns588p1196 := nat_lit 4142357147607170194262831 

noncomputable def Ns588p1197 := nat_lit 4285547583204203031429120000 

noncomputable def Ns588p1198 := nat_lit 6318112395513893481727144230912 

noncomputable abbrev qz776 := (Enclosure.sfrac Bool.false 999236 1000)

noncomputable abbrev qz680 := qz776

noncomputable abbrev qz485 := qz680

noncomputable abbrev qz168 := qz485

noncomputable abbrev qz777 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 999236 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz681 := qz777

noncomputable abbrev qz486 := qz681

noncomputable abbrev qz169 := qz486

noncomputable abbrev qz778 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 999236 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz682 := qz778

noncomputable abbrev qz487 := qz682

noncomputable abbrev qz170 := qz487

noncomputable abbrev qz683 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz169 qz9))

noncomputable def Ns588p1199 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 12) (@HMul.hMul Real Real Real qz5 qz683 (Zeta.RiemannSiegel.correction qz170)) 303902501 268435456 129227 134217728 2151565463778593137963 18889465931478580854784 16162599486600420182831 Ns588p1197 Ns588p1198 

noncomputable def Ns588p1200 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos BSN.quadSignNeg 11 12 999236 1000 286 536870912 268435456 9007199254740992 Bool.false 1091249121066 4550 1334074092 51 154981288 8 

noncomputable def Ns588p1201 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 999236 1000 170 231 536870912 268435456 9007199254740992 Bool.false 1091249121066 4550 

noncomputable def Ns588p1202 := Ns588p1201 1236190956 51 169773496 8 1287360220 51 161872664 8 Bool.true 267428200 208108 Bool.true 633859433 Bool.true 321823866 28296951008113761 1 Bool.false 204182177 Bool.true Bool.false 302893560 Bool.false Bool.true 240670436 

noncomputable def Ns588p1203 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 999236 1000 28 103 536870912 268435456 9007199254740992 Bool.false 1091249121066 4550 

noncomputable def Ns588p1204 := Ns588p1203 1116391676 51 189812536 8 1179625948 51 178956968 8 Bool.true 488256898 169959 Bool.true 676815710 Bool.true 614162486 28296951008113761 1 Bool.false 163842974 Bool.false Bool.false 488704381 Bool.false Bool.true 267428200 

noncomputable def Ns588p1205 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 999236 1000 154 56 536870912 268435456 9007199254740992 Bool.false 1091249121066 4550 

noncomputable def Ns588p1206 := Ns588p1205 961943533 51 219176632 8 1044702541 51 202918136 8 Bool.true 477925394 126296 Bool.false 170025019 Bool.false 119100841 28296951008113761 1 Bool.false 510172040 Bool.true Bool.false 523714182 Bool.false Bool.true 488256898 

noncomputable def Ns588p1207 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 999236 1000 412 270 536870912 268435456 9007199254740992 Bool.false 1091249121066 4550 

noncomputable def Ns588p1208 := Ns588p1207 744261104 50 268435448 8 864060384 50 240095976 8 Bool.true 510350396 74641 Bool.false 110911658 Bool.false 153867935 28296951008113761 1 Bool.false 525455032 Bool.false Bool.false 514972048 Bool.true Bool.true 477925394 

noncomputable def Ns588p1209 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 999236 1000 853 595 536870912 268435456 9007199254740992 Bool.false 1091249121066 4550 

noncomputable def Ns588p1210 := Ns588p1209 372130544 50 379625064 8 589812976 50 309962568 8 Bool.true 536870824 4602 Bool.false 55312179 Bool.false 114422542 28296951008113761 1 Bool.false 55214378 Bool.true Bool.false 113558256 Bool.false Bool.true 510350396 

noncomputable def Ns588p1211 := nat_lit 2502736578831355364634102478836687837677349188820177139 

noncomputable def Ns588p1212 := nat_lit 1231292143685592443628847148997389501456531324928000 

noncomputable def Ns588p1213 := nat_lit 478169502904833795244222017044480000 

noncomputable def Ns588p1214 := nat_lit 2866825423402694155529251203400524103680 

noncomputable abbrev qz684 := (@Eq.refl Real qz776)

noncomputable abbrev qz488 := qz684

noncomputable abbrev qz171 := qz488

noncomputable def Ns588p1215 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz168 999236 1000 3993891334784 16000000 1998472 4000 2000 Ns588p1213 Ns588p1214 qz171 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns588p1216 := nat_lit 26243095108846672828265686408486587860803641030163060637040640 

noncomputable abbrev qz685 := (@HSub.hSub Real Real Real qz743 qz744 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz745 (@Nat.cast Real Real.instNatCast 1998472))))

noncomputable abbrev qz489 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 999236 4000) (Real.log (Enclosure.sfrac Bool.false 3993891334784 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz685))

noncomputable abbrev qz686 := (Enclosure.sfrac Bool.false 999236 2000)

noncomputable abbrev qz172 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz489 qz686) (@HMul.hMul Real Real Real qz355 qz686 (Real.log Real.pi)))

noncomputable def Ns588p1217 := @Enclosure.Real.IsNear.addLit_ft_p qz172 (Enclosure.sfrac Bool.true Ns588p1213 Ns588p1214) 9154061858144886669223 4503599627370496000 37798828799782666007 Ns588p820 Ns588p1213 Ns588p1214 0 1 Ns588p1216 

noncomputable def Ns588p1218 := nat_lit 153579673071458122945074823168000 

noncomputable abbrev qz173 := (@HSub.hSub Real Real Real qz359 qz489 qz686)

noncomputable def Ns588p1219 := @Enclosure.Real.IsNear.subLit_ff_p qz173 (@HMul.hMul Real Real Real qz5 qz686 (Real.log Real.pi)) 11729795029492821344167 4503599627370496000 1573808562425071 544500000000000000000 9595353794649 16777216000 749427 134217728000 Ns588p1218 9154061858144886669223 4503599627370496000 

noncomputable def Ns588p1220 := nat_lit 4691918011797128537666800 

noncomputable abbrev qz174 := qz489

noncomputable def Ns588p1221 := @Enclosure.Real.IsNear.subLit_ff_p qz174 qz686 2795974893624082762939 900719925474099200 1573808562425071 544500000000000000000 999236 2000 0 1 Ns588p1220 11729795029492821344167 4503599627370496000 1573808562425071 544500000000000000000 

noncomputable def Ns588p1222 := nat_lit 6295975744531340661788678995545423872 

noncomputable def Ns588p1223 := nat_lit 120193221877546118849495040 

noncomputable def Ns588p1224 := nat_lit 123701525458374701770067443133552663033142203280905363184773434746086903965545127855816380091821562790659069437687848366834917171404201959368554805070439415514284698283673806326513181350658466304990470189403340800 

noncomputable def Ns588p1225 := nat_lit 4248460104025894888748209787898969150769627738205238104890053424415179474385183815907590265175547154844024934038739833431087576660627815404198252695455401715091595184920771094050796147439941144099523889337466880 

noncomputable def Ns588p1226 := nat_lit 56882872154362018178137130149510855606349457476609093174697310649997281494892738248532368359687662311771097911687729913696735951850762179994282757435204190949461616310595469451931837712258843879564902400 

noncomputable def Ns588p1227 := BSN.log_dyadic_bound 1896739334784 6091043334784 9 8 Ns588p1224 268435456 87120000 Ns588p1225 Ns588p1226 172922307 7987782669568 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1896739334784) (BSN.artanhQ 6091043334784) 0 8 Ns588p1225 Ns588p1224 Ns588p1226 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz490 := (Real.log (Enclosure.sfrac Bool.false 3993891334784 16000000))

noncomputable def Ns588p1228 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 999236 4000) qz490 999236 4000 0 1 55969330425162855 4503599627370496 12500018513 1089000000000000000 2796328492835901528939 900719925474099200 3122617124714017 1089000000000000000000 (Enclosure.Real.IsNear.const Bool.false 999236 4000) (BSN.isNear_log_sfrac 3993891334784 16000000 55969330425162855 4503599627370496 12500018513 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3993891334784) qz362)) Bool.false Ns588p1223 Ns588p114 1000001481040000 87120000000000000000000 55969330425162855 4503599627370496 12500018513 1089000000000000000 (BSN.log_rat_reduce_isNear 3993891334784 16000000 17 7987782669568 4194304000000 172922307 268435456 24973259072661432 36028797018963968 87120000 1000000000000000 rfl rfl rfl rfl (Ns588p1227 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p1229 := BSN.arctan_dyadic_bound_f 1000 1998472 1 0 33554432 10890000 0 1 1 0 1 1 16790 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1998472) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1998472) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns588p1230 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1998472))) 884279719003555 562949953421312 1 2000000000000000 16790 33554432 1 10890000 29662051770565950177280 883998029546915 562949953421312 200000001089 2178000000000000000 qz17 (Ns588p1229 rfl) rfl rfl 

noncomputable abbrev qz491 := (@HMul.hMul Real Real Real qz588 qz593 qz685)

noncomputable abbrev qz175 := qz491

noncomputable abbrev qz492 := qz685

noncomputable abbrev qz176 := qz492

noncomputable def Ns588p1231 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 999236 4000) qz490) qz175 2796328492835901528939 900719925474099200 3122617124714017 1089000000000000000000 883998029546915 2251799813685248 200000001089 8712000000000000000 Ns588p1222 2795974893624082762939 900719925474099200 1573808562425071 544500000000000000000 (Ns588p1228 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz176 1 4 0 1 883998029546915 562949953421312 200000001089 2178000000000000000 883998029546915 2251799813685248 200000001089 8712000000000000000 qz369 Ns588p1230 rfl) 

noncomputable def Ns588p1232 := @Ns588p1217 Ns588p1211 Ns588p1212 37798828799782666007 Ns588p820 (@Ns588p1219 37798828799782666007 Ns588p820 (Ns588p1221 (Ns588p1231 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 999236 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz686 (Real.log Real.pi) 999236 2000 0 1 38410761 33554432 3 268435456 9595353794649 16777216000 749427 134217728000 (Enclosure.Real.IsNear.const Bool.false 999236 2000) RS589to600.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns588p1213 Ns588p1214) 

noncomputable def Ns588p1233 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns588p1211 Ns588p1212 37798828799782666007 Ns588p820 136406140133 67108864 569 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz370 qz172 (Enclosure.sfrac Bool.true Ns588p1213 Ns588p1214)) Bool.false Ns588p1211 Ns588p1212 37798828799782666007 Ns588p820 Ns588p1215 (Ns588p1232 rfl rfl)) 

noncomputable def Ns588p1234 := nat_lit 15186346321704335825698816 

noncomputable def Ns588p1235 := nat_lit 14359664788398737796547590819299735698622383852047301661433535827526842597679851232750047186162569504252173179401576531278475283790674710757376 

noncomputable def Ns588p1236 := nat_lit 10206621019633175741581284700075555577322666843887642612422328435478832832838505667300878848389270200138377747238266636169288034000306176 

noncomputable def Ns588p1237 := nat_lit 71709233742377977865507747146649111344961737192202302629605965968055283744666393023653502099383872008601236425132222529747217527695043446439936 

noncomputable def Ns588p1238 := BSN.sin_dyadic_bound_f 215810961232 137438953472 4 3 67108864 21801270 Ns588p1235 Ns588p127 Ns588p1236 Ns588p1237 Ns588p130 Ns588p1236 67108853 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215810961232) (BSN.sinEvenQ 137438953472) 0 3 Ns588p1235 Ns588p127 Ns588p1236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215810961232) (BSN.sinOddQ 137438953472) 0 3 Ns588p1237 Ns588p130 Ns588p1236 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1239 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz168) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 136406140133) qz371) Bool.false 136406140133 67108864 569 67108864 Bool.true 67108853 67108864 1 10890000 (Ns588p1233 rfl) (Enclosure.sfrac_false_div 136406140133 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 136406140133) qz371) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns588p1234) qz372) 226375608064910080 72057594037927936 Bool.false 67108853 67108864 323 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q1 136406140133 67108864 226375608064910080 72057594037927936 323 Ns588p1234 Ns588p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108853 67108864 Ns588p1234 Ns588p114 215810961232 137438953472 21801270 21780000 (Ns588p1238 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p1240 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns588p1211 Ns588p1212 37798828799782666007 Ns588p820 1091249121066 536870912 4550 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz370 qz172 (Enclosure.sfrac Bool.true Ns588p1213 Ns588p1214)) Bool.false Ns588p1211 Ns588p1212 37798828799782666007 Ns588p820 Ns588p1215 (Ns588p1232 rfl rfl)) 

noncomputable def Ns588p1241 := Ns588p1210 74641 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 853 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55214378 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 595 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 113558256 536870912) qz171 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) Bool.true 67108853 67108864 391469929 45675970560000 536870824 536870912 4602 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.true 67108853 67108864 391469929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz168) qz168) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.true 67108853 67108864 6263518864 730815528960000 67108853 67108864 391469929 45675970560000 (Ns588p1239 rfl rfl) rfl)) rfl) (Ns588p1240 rfl) RS589to600.d7 

noncomputable def Ns588p1242 := nat_lit 9360155648660542382495933697681 

noncomputable def Ns588p1243 := BSN.sin_dyadic_bound_f 55312179 536870912 2 1 536870912 268435456 Ns588p1242 Ns588p188 Ns588p1242 Ns588p1242 Ns588p189 Ns588p1242 55214378 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 55312179) qz373 0 1 Ns588p1242 Ns588p188 Ns588p1242 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 55312179) qz374 0 1 Ns588p1242 Ns588p189 Ns588p1242 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1244 := nat_lit 171414030663396342906626989831696 

noncomputable def Ns588p1245 := BSN.sin_dyadic_bound_f 114422542 536870912 2 1 536870912 268435456 Ns588p1244 Ns588p188 Ns588p1244 Ns588p1244 Ns588p189 Ns588p1244 113558256 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 114422542) qz373 0 1 Ns588p1244 Ns588p188 Ns588p1244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 114422542) qz374 0 1 Ns588p1244 Ns588p189 Ns588p1244 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1246 := nat_lit 151324340604082351353432098753296 

noncomputable def Ns588p1247 := BSN.cos_dyadic_bound_f 110911658 536870912 2 1 536870912 268435456 Ns588p1246 Ns588p142 Ns588p1246 Ns588p1246 Ns588p143 Ns588p1246 525455032 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 110911658) qz375 0 1 Ns588p1246 Ns588p142 Ns588p1246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 110911658) qz376 0 1 Ns588p1246 Ns588p143 Ns588p1246 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1248 := nat_lit 78231746210413354179031975455983295727312154474368742768110239453690625 

noncomputable def Ns588p1249 := nat_lit 314184678644011988300786199020189995290319846891723517047312890625 

noncomputable def Ns588p1250 := nat_lit 234694610261882774513119324795551846801945882783412444857296623735290625 

noncomputable def Ns588p1251 := BSN.cos_dyadic_bound_f 153867935 536870912 3 2 536870912 268435456 Ns588p1248 Ns588p152 Ns588p1249 Ns588p1250 Ns588p155 Ns588p1249 514972048 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 153867935) qz375 0 2 Ns588p1248 Ns588p152 Ns588p1249 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 153867935) qz376 0 2 Ns588p1250 Ns588p155 Ns588p1249 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1252 := Ns588p1208 126296 BSN.abs_quadSignPos (BSN.cos_quad_nat0 412 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 525455032 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 270 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 514972048 536870912) qz171 rfl rfl (Ns588p1241 RS589to600.d9 RS589to600.d11 RS589to600.d13 RS589to600.d17 (Ns588p1243 rfl rfl) (Ns588p1245 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns588p1240 rfl) RS589to600.d19 RS589to600.d21 RS589to600.d23 RS589to600.d25 RS589to600.d17 (Ns588p1247 rfl rfl) (Ns588p1251 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns588p1253 := nat_lit 116638709888859764563340711974589861732881835185439650491175095179697121 

noncomputable def Ns588p1254 := nat_lit 698397468335087652228883764876850521412718610219444400273871363041 

noncomputable def Ns588p1255 := nat_lit 349914732871642623514717678156239831497602680119098512584724737796365281 

noncomputable def Ns588p1256 := BSN.cos_dyadic_bound_f 170025019 536870912 3 2 536870912 268435456 Ns588p1253 Ns588p152 Ns588p1254 Ns588p1255 Ns588p155 Ns588p1254 510172040 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 170025019) qz375 0 2 Ns588p1253 Ns588p152 Ns588p1254 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 170025019) qz376 0 2 Ns588p1255 Ns588p155 Ns588p1254 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1257 := nat_lit 201214517974466206983990370812961 

noncomputable def Ns588p1258 := BSN.cos_dyadic_bound_f 119100841 536870912 2 1 536870912 268435456 Ns588p1257 Ns588p142 Ns588p1257 Ns588p1257 Ns588p143 Ns588p1257 523714182 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 119100841) qz375 0 1 Ns588p1257 Ns588p142 Ns588p1257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 119100841) qz376 0 1 Ns588p1257 Ns588p143 Ns588p1257 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1259 := Ns588p1206 169959 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 154 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 510172040 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 523714182 536870912) qz171 rfl rfl (Ns588p1252 rfl rfl) (Ns588p1240 rfl) RS589to600.d27 RS589to600.d29 RS589to600.d31 RS589to600.d33 RS589to600.d17 (Ns588p1256 rfl rfl) (Ns588p1258 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1260 := nat_lit 28948031331040274032508948459133756904478926889861238731135028223287450814885477367043195614001327083896384000000 

noncomputable def Ns588p1261 := nat_lit 9239429797915769432872274803845970754948241535888599345853731006630969173325937702019869872241000000000000 

noncomputable def Ns588p1262 := nat_lit 175442250651074527871766195468776652936840814805288096847790172457326780792642431079386529284681606494803929600000 

noncomputable def Ns588p1263 := BSN.cos_dyadic_bound_f 676815710 536870912 4 3 536870912 268435456 Ns588p1260 Ns588p146 Ns588p1261 Ns588p1262 Ns588p149 Ns588p1261 163842974 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 676815710) qz375 0 3 Ns588p1260 Ns588p146 Ns588p1261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 676815710) qz376 0 3 Ns588p1262 Ns588p149 Ns588p1261 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1264 := nat_lit 35763524471169023235317195944252728957691441614405122987714088301302964480 

noncomputable def Ns588p1265 := nat_lit 20242599574713138726296556199528762030606002728329544173886912272589056 

noncomputable def Ns588p1266 := nat_lit 93633599882321715772654842572529338798285175461881836182017271502590238976 

noncomputable def Ns588p1267 := BSN.sin_dyadic_bound_f 614162486 536870912 3 2 536870912 268435456 Ns588p1264 Ns588p136 Ns588p1265 Ns588p1266 Ns588p139 Ns588p1265 488704381 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 614162486) qz373 0 2 Ns588p1264 Ns588p136 Ns588p1265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 614162486) qz374 0 2 Ns588p1266 Ns588p139 Ns588p1265 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1268 := Ns588p1204 208108 BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 163842974 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 103 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 488704381 536870912) qz171 rfl rfl (Ns588p1259 rfl) (Ns588p1240 rfl) RS589to600.d35 RS589to600.d37 RS589to600.d39 RS589to600.d41 RS589to600.d17 (Ns588p1263 rfl rfl) (Ns588p1267 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1269 := nat_lit 22261716323627599761558578252536417748932258889169741029324758919946104289553958712552934127737135769018779839841 

noncomputable def Ns588p1270 := nat_lit 4206447702233255181902289487739788550738125137605813343663492426458815935525432025856698109535065263582561 

noncomputable def Ns588p1271 := nat_lit 134950375451671729010033163719530833788480246654668804253122411602445890839539794349040510425744346098535166651745 

noncomputable def Ns588p1272 := BSN.cos_dyadic_bound_f 633859433 536870912 4 3 536870912 268435456 Ns588p1269 Ns588p146 Ns588p1270 Ns588p1271 Ns588p149 Ns588p1270 204182177 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 633859433) qz375 0 3 Ns588p1269 Ns588p146 Ns588p1270 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 633859433) qz376 0 3 Ns588p1271 Ns588p149 Ns588p1270 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1273 := nat_lit 2694963065865709651532723624645915498158851900894895263180991543798636800 

noncomputable def Ns588p1274 := nat_lit 115065725729952496550165038318423127641613502848260318239336690852096 

noncomputable def Ns588p1275 := nat_lit 7058050304187581545210337797343929810114144747148685648768304641020764416 

noncomputable def Ns588p1276 := BSN.sin_dyadic_bound_f 321823866 536870912 3 2 536870912 268435456 Ns588p1273 Ns588p136 Ns588p1274 Ns588p1275 Ns588p139 Ns588p1274 302893560 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 321823866) qz373 0 2 Ns588p1273 Ns588p136 Ns588p1274 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 321823866) qz374 0 2 Ns588p1275 Ns588p139 Ns588p1274 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1277 := Ns588p1202 242419 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 170 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 204182177 536870912) BSN.abs_quadSignPos qz634 (BSN.sfrac_eq_quadSignPos_mul Bool.false 302893560 536870912) qz171 rfl rfl (Ns588p1268 rfl) (Ns588p1240 rfl) RS589to600.d43 RS589to600.d45 RS589to600.d47 RS589to600.d49 RS589to600.d17 (Ns588p1272 rfl rfl) (Ns588p1276 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1278 := nat_lit 20073264305287729818555147893549993159705070876175782151520327615193236149124924450961281129906972946642071024961 

noncomputable def Ns588p1279 := nat_lit 3084902462391146535707529588713133065196281645871445067000761194345699882519790826175738573753225219241281 

noncomputable def Ns588p1280 := nat_lit 121693198455891473445264752953612729311069016564879868518582055746973064284779293553703109273232217458672259134785 

noncomputable def Ns588p1281 := BSN.cos_dyadic_bound_f 617689359 536870912 4 3 536870912 268435456 Ns588p1278 Ns588p146 Ns588p1279 Ns588p1280 Ns588p149 Ns588p1279 219042290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 617689359) qz375 0 3 Ns588p1278 Ns588p146 Ns588p1279 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 617689359) qz376 0 3 Ns588p1280 Ns588p149 Ns588p1279 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1282 := Ns588p1200 Bool.true 240670436 242419 Bool.true 617689359 28296951008113761 1 Bool.false 219042290 Bool.true Bool.true 303902501 258454 BSN.abs_quadSignNeg qz398 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 219042290 536870912) qz171 rfl (Ns588p1277 rfl) (Ns588p1240 rfl) RS589to600.d51 RS589to600.d53 RS589to600.d17 (Ns588p1281 rfl rfl) rfl 

noncomputable def Ns588p1283 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 12) 303902501 536870912 258454 536870912 303902501 536870912 258454 536870912 326312825741901824 303902501 268435456 129227 134217728 (Ns588p1282 rfl rfl rfl rfl) 

noncomputable def Ns588p1284 := @Enclosure.Real.IsNear.mulLit_ff qz683 (Zeta.RiemannSiegel.correction qz170) 4724413 16777216 1 33554432 455414347513351 1125899906842624 10230437125087193 766315624094760960000 2151565463778593137963 18889465931478580854784 

noncomputable abbrev qz687 := (@HPow.hPow Real Real Real qz7 qz169 qz9)

noncomputable def Ns588p1285 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz687 1 1 0 1 4724413 16777216 1 33554432 4724413 16777216 1 33554432 

noncomputable def Ns588p1286 := @Enclosure.Real.IsNear.sqrt_image qz169 2668136734963 16777216000 249809 16777216000 423149628 423149669 33554432 (@Enclosure.Real.IsNear.of_eq qz169 (@HMul.hMul Real Real Real qz5 qz168 qz3) Bool.false 2668136734963 16777216000 249809 16777216000 (BSN.t_div_two_pi_mk qz168 999236 1000 qz171) (@Enclosure.Real.IsNear.mulLit_ff qz168 qz3 999236 1000 0 1 10680707 67108864 1 67108864 2668136734963 16777216000 249809 16777216000 (Enclosure.Real.IsNear.const Bool.false 999236 1000) RS589to600.d56 rfl)) 

noncomputable abbrev qz779 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 999236 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz688 := qz779

noncomputable abbrev qz493 := qz688

noncomputable abbrev qz177 := qz493

noncomputable def Ns588p1287 := @Enclosure.Real.IsNear.sqrt_image qz177 846299297 67108864 41 67108864 119157649 119157656 33554432 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 846299297 67108864 41 67108864 846299297 67108864 41 67108864 (Ns588p1286 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns588p1288 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz177) 238315305 67108864 7 67108864 9448825 9448827 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz177) Bool.false 238315305 67108864 7 67108864 238315305 67108864 7 67108864 (Ns588p1287 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns588p1289 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz177)) Bool.false 18897652 67108864 2 67108864 4724413 16777216 1 33554432 (Ns588p1288 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz178 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz487))

noncomputable abbrev qz689 := (@HMul.hMul Real Real Real qz739 qz778 qz778)

noncomputable abbrev qz494 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz689 qz682) qz603)

noncomputable abbrev qz179 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz494))

noncomputable def Ns588p1290 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz170) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz178) qz179) Bool.false 455414347513351 

noncomputable def Ns588p1291 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz178) qz179 43740259 33554432 225 

noncomputable abbrev qz690 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz178))

noncomputable def Ns588p1292 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz178) (@Neg.neg Real Real.instNeg qz690) Bool.true 43740259 33554432 225 33554432 (BSN.inv_eq_neg_inv_neg qz178) 

noncomputable def Ns588p1293 := @Enclosure.Real.IsNear.recentre' qz690 Bool.false 87480518 67108864 450 67108864 43740259 33554432 

noncomputable def Ns588p1294 := @Enclosure.Real.IsNear.recentre' qz178 Bool.true 51481172 67108864 1438364432 365407764480000 12870293 16777216 89897777 22837985280000 

noncomputable abbrev qz180 := (@HMul.hMul Real Real Real qz355 qz352 qz487)

noncomputable def Ns588p1295 := @Enclosure.Real.IsNear.cos_image qz180 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 257566169) qz371) Bool.false 257566169 67108864 129 33554432 Bool.true 51481172 67108864 1 

noncomputable def Ns588p1296 := nat_lit 221285818424586488501285523 

noncomputable def Ns588p1297 := nat_lit 57646075230342348800000000000000 

noncomputable def Ns588p1298 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz170 884279719003555 140737488355328 1 500000000000000 40992929 67108864 41 67108864 36249215737252680862595 9444732965739290427392 Ns588p1296 

noncomputable def Ns588p1299 := @Enclosure.Real.IsNear.subLit_ff_p qz177 qz1 846299297 67108864 41 67108864 12 1 0 1 40992929 40992929 67108864 41 

noncomputable def Ns588p1300 := @Ns588p1299 67108864 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 846299297 67108864 41 67108864 846299297 67108864 41 67108864 (Ns588p1286 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns588p1301 := @Enclosure.Real.IsNear.recentre' qz180 Bool.false 36249215737252680862595 9444732965739290427392 Ns588p1296 Ns588p1297 257566169 67108864 129 33554432 (@Ns588p1298 Ns588p1297 RS589to600.d55 (Ns588p1300 rfl rfl) rfl) 

noncomputable def Ns588p1302 := nat_lit 6735577098321970885296128 

noncomputable def Ns588p1303 := nat_lit 50325661919099639699739576635953360563607850120136236075788079982742838439301538849075848321 

noncomputable def Ns588p1304 := nat_lit 7046283111144136206240453733286028008737117045319249495045522113198864778813652259136641 

noncomputable def Ns588p1305 := nat_lit 150962893191076630826806249000393509634806076126318069728374148904002117588346989242709271681 

noncomputable def Ns588p1306 := BSN.cos_dyadic_bound_f 95718307567 137438953472 3 2 67108864 21801270 Ns588p1303 Ns588p511 Ns588p1304 Ns588p1305 Ns588p514 Ns588p1304 51481172 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 95718307567) qz383 0 2 Ns588p1303 Ns588p511 Ns588p1304 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 95718307567) qz384 0 2 Ns588p1305 Ns588p514 Ns588p1304 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1307 := @Ns588p1295 10890000 (Ns588p1301 rfl) (Enclosure.sfrac_false_div 257566169 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 257566169) qz371) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns588p1302) qz372) 226375608064910080 72057594037927936 Bool.false 51481172 67108864 0 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 257566169 67108864 226375608064910080 72057594037927936 0 Ns588p1302 Ns588p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 51481172 67108864 Ns588p1302 Ns588p114 95718307567 137438953472 21801270 21780000 (Ns588p1306 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p1308 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz178) 12870293 16777216 89897777 22837985280000 43740034 43740484 33554432 (@Enclosure.Real.IsNear.neg qz178 Bool.true 12870293 16777216 89897777 22837985280000 (Ns588p1294 (Ns588p1307 rfl rfl) rfl)) 

noncomputable def Ns588p1309 := Ns588p1292 (@Enclosure.Real.IsNear.neg qz690 Bool.false 43740259 33554432 225 33554432 (@Ns588p1293 225 33554432 (Ns588p1308 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p1310 := @Enclosure.Real.IsNear.recentre' qz179 Bool.true 10411789 33554432 

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz355 qz352 qz494)

noncomputable def Ns588p1311 := @Enclosure.Real.IsNear.cos_image qz181 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 126587461)) qz371) Bool.true 126587461 67108864 

noncomputable def Ns588p1312 := nat_lit 1195584775307299167511145333405 

noncomputable def Ns588p1313 := nat_lit 164962783225487517045790009273815093 

noncomputable def Ns588p1314 := @Enclosure.Real.IsNear.recentre' qz181 Bool.true Ns588p1312 Ns588p929 Ns588p1313 

noncomputable abbrev qz182 := qz494

noncomputable def Ns588p1315 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz182 884279719003555 140737488355328 1 500000000000000 1352043645934271 

noncomputable abbrev qz495 := (@HSub.hSub Real Real Real qz592 qz689 qz682)

noncomputable abbrev qz183 := qz495

noncomputable def Ns588p1316 := @Enclosure.Real.IsNear.subLit_tf qz183 qz31 1070568669223615 4503599627370496 6112885283 4503599627370496 1 16 

noncomputable abbrev qz496 := qz689

noncomputable abbrev qz184 := qz496

noncomputable def Ns588p1317 := @Enclosure.Real.IsNear.subLit_ff_n qz184 qz170 1680420227999041 4503599627370496 3361421859 4503599627370496 40992929 67108864 41 67108864 

noncomputable def Ns588p1318 := @Enclosure.Real.IsNear.mulLit_ff qz170 qz170 40992929 67108864 41 67108864 40992929 67108864 41 67108864 1680420227999041 4503599627370496 

noncomputable def Ns588p1319 := nat_lit 2124181193774183360353623698677953973103655618169504450087203839920074728727083817791714669226765810001 

noncomputable def Ns588p1320 := nat_lit 16931220677545428685862719823101861790314964648621192350298885954007215717218982661010102425975121 

noncomputable def Ns588p1321 := nat_lit 12822356467462302715510495001715167176900901316647377946987441933578563996811242777610999879691214747985 

noncomputable def Ns588p1322 := BSN.cos_dyadic_bound_t 126587461 67108864 4 3 33554432 10890000 Ns588p1319 Ns588p231 Ns588p1320 Ns588p1321 Ns588p234 Ns588p1320 10411789 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 126587461) (BSN.cosEvenQ 67108864) 0 3 Ns588p1319 Ns588p231 Ns588p1320 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 126587461) (BSN.cosOddQ 67108864) 0 3 Ns588p1321 Ns588p234 Ns588p1320 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1323 := @Ns588p1310 3158984432 365407764480000 10411789 33554432 197436527 22837985280000 (@Ns588p1311 287 33554432 Bool.true 10411789 33554432 1 10890000 (@Ns588p1314 Ns588p932 126587461 67108864 287 33554432 (@Ns588p1315 4503599627370496 6112885283 4503599627370496 Ns588p1312 Ns588p929 Ns588p1313 Ns588p932 RS589to600.d55 (@Ns588p1316 0 1 21632698334948336 1352043645934271 4503599627370496 6112885283 4503599627370496 (@Ns588p1317 71844647225588564623360 1070568669223615 4503599627370496 6112885283 4503599627370496 (@Ns588p1318 3361421859 4503599627370496 (Ns588p1300 rfl rfl) (Ns588p1300 rfl rfl) rfl) (Ns588p1300 rfl rfl) rfl rfl) qz388 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 126587461 67108864) (BSN.cos_neg_of_bound 126587461 67108864 Bool.true 10411789 33554432 1 10890000 (Ns588p1322 rfl rfl)) rfl rfl) 

noncomputable def Ns588p1324 := @Ns588p1284 16162599486600420182831 Ns588p1197 (Ns588p1285 qz33 (@Enclosure.Real.IsNear.of_eq qz687 (@Inv.inv Real Real.instInv (Real.sqrt qz177)) Bool.false 4724413 16777216 1 33554432 (BSN.rpow_neg_quarter_mk qz169 (BSN.t_div_two_pi_nonneg qz168 999236 1000 qz171)) Ns588p1289) rfl) (@Ns588p1290 1125899906842624 10230437125087193 766315624094760960000 (BSN.correction_mk qz170 (BSN.cos_two_pi_p_ne_zero_mk qz168 999236 1000 12 qz171 rfl rfl (@BSN.floor_sqrt_eq_dec qz168 999236 1000 12 qz171 rfl rfl rfl))) (@Ns588p1291 33554432 10411789 33554432 197436527 22837985280000 455414347513351 1125899906842624 10230437125087193 766315624094760960000 Ns588p1309 (Ns588p1323 rfl) rfl)) 

noncomputable def Ns588p1325 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (hardyZApproximantRS₀ qz168) Bool.true 23536802811599871075627 18889465931478580854784 Ns588p1196 Ns588p1197 (@Eq.refl Real (hardyZApproximantRS₀ qz168)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 12) (@HMul.hMul Real Real Real qz5 qz683 (Zeta.RiemannSiegel.correction qz170))) Bool.true 23536802811599871075627 18889465931478580854784 Ns588p1196 Ns588p1197 (BSN.hardyZApproximantRS₀_eq qz168 12 (@BSN.floor_sqrt_eq_dec qz168 999236 1000 12 qz171 rfl rfl rfl)) (@Ns588p1199 23536802811599871075627 18889465931478580854784 Ns588p1196 Ns588p1197 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 12)) Bool.true 303902501 268435456 129227 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz168) qz168 12) (Ns588p1283 (Ns588p1282 rfl rfl rfl rfl) rfl rfl)) (Ns588p1324 rfl) rfl rfl)) 

theorem RS589to600.d67 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz168) Bool.true 23536802811599871075627 18889465931478580854784 Ns588p1196 Ns588p1197 := Ns588p1325 

noncomputable def Ns588p1326 := nat_lit 51946031311566097350656000 

noncomputable def Ns588p1327 := nat_lit 6415591536580290013764876500992 

noncomputable abbrev qz780 := (Enclosure.sfrac Bool.false 1000476 1000)

noncomputable abbrev qz691 := qz780

noncomputable abbrev qz497 := qz691

noncomputable abbrev qz185 := qz497

noncomputable abbrev qz781 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 1000476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz692 := qz781

noncomputable abbrev qz498 := qz692

noncomputable abbrev qz186 := qz498

noncomputable abbrev qz782 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 1000476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz693 := qz782

noncomputable abbrev qz499 := qz693

noncomputable abbrev qz187 := qz499

noncomputable abbrev qz694 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz186 qz9))

noncomputable def Ns588p1328 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz185) qz185 12) (@HMul.hMul Real Real Real qz5 qz694 (Zeta.RiemannSiegel.correction qz187)) 710088065 268435456 258787 268435456 1084061784681804553773 9444732965739290427392 205709807385649744263 Ns588p1326 Ns588p1327 

noncomputable def Ns588p1329 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz185) qz185 Real.cos BSN.quadSignNeg 11 12 1000476 1000 286 536870912 268435456 9007199254740992 Bool.false 1092936632719 4556 1334074092 51 154981288 8 

noncomputable def Ns588p1330 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz185) qz185 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 1000476 1000 170 231 536870912 268435456 9007199254740992 Bool.false 1092936632719 4556 

noncomputable def Ns588p1331 := Ns588p1330 1236190956 51 169773496 8 1287360220 51 161872664 8 Bool.false 821048891 208379 Bool.true 479224565 Bool.true 230638886 28296951008113761 1 Bool.false 336816598 Bool.true Bool.false 223609811 Bool.false Bool.false 781959018 

noncomputable def Ns588p1332 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz185) qz185 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 1000476 1000 28 103 536870912 268435456 9007199254740992 Bool.false 1092936632719 4556 

noncomputable def Ns588p1333 := Ns588p1332 1116391676 51 189812536 8 1179625948 51 178956968 8 Bool.false 556665423 170182 Bool.true 373629735 Bool.true 389387009 28296951008113761 1 Bool.false 412022466 Bool.false Bool.false 356134579 Bool.false Bool.false 821048891 

noncomputable def Ns588p1334 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz185) qz185 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 1000476 1000 154 56 536870912 268435456 9007199254740992 Bool.false 1092936632719 4556 

noncomputable def Ns588p1335 := Ns588p1334 961943533 51 219176632 8 1044702541 51 202918136 8 Bool.false 510557567 126464 Bool.false 664726691 Bool.false 511181343 28296951008113761 1 Bool.false 175312768 Bool.true Bool.false 311349347 Bool.false Bool.false 556665423 

noncomputable def Ns588p1336 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz185) qz185 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 1000476 1000 413 270 536870912 268435456 9007199254740992 Bool.false 1092936632719 4556 

noncomputable def Ns588p1337 := Ns588p1336 744261104 50 268435448 8 864060384 50 240095976 8 Bool.false 559370321 74745 Bool.false 32224685 Bool.false 769944712 28296951008113761 1 Bool.false 32205338 Bool.true Bool.false 73141972 Bool.true Bool.false 510557567 

noncomputable def Ns588p1338 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz185) qz185 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 1000476 1000 854 596 536870912 268435456 9007199254740992 Bool.false 1092936632719 4556 

noncomputable def Ns588p1339 := Ns588p1338 372130544 50 379625064 8 589812976 50 309962568 8 Bool.false 536870600 4618 Bool.false 438067101 Bool.false 227251248 28296951008113761 1 Bool.false 367846160 Bool.true Bool.false 489488356 Bool.false Bool.false 559370321 

noncomputable def Ns588p1340 := nat_lit 280592025052998037646690420589269928090963884683542949 

noncomputable def Ns588p1341 := nat_lit 137832049800846921590075166199554974926789148672000 

noncomputable def Ns588p1342 := nat_lit 481143792516904726100921413140480000 

noncomputable def Ns588p1343 := nat_lit 2888237238413706175774979628147545210880 

noncomputable abbrev qz695 := (@Eq.refl Real qz780)

noncomputable abbrev qz500 := qz695

noncomputable abbrev qz188 := qz500

noncomputable def Ns588p1344 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz185 1000476 1000 4003809906304 16000000 2000952 4000 2000 Ns588p1342 Ns588p1343 qz188 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns588p1345 := nat_lit 26479985693577522329107444901383287370611949171133765816156160 

noncomputable abbrev qz696 := (@HSub.hSub Real Real Real qz743 qz744 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz745 (@Nat.cast Real Real.instNatCast 2000952))))

noncomputable abbrev qz501 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 1000476 4000) (Real.log (Enclosure.sfrac Bool.false 4003809906304 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz696))

noncomputable abbrev qz697 := (Enclosure.sfrac Bool.false 1000476 2000)

noncomputable abbrev qz189 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz501 qz697) (@HMul.hMul Real Real Real qz355 qz697 (Real.log Real.pi)))

noncomputable def Ns588p1346 := @Enclosure.Real.IsNear.addLit_ft_p qz189 (Enclosure.sfrac Bool.true Ns588p1342 Ns588p1343) 9168217730964515292257 4503599627370496000 37845608110887389137 Ns588p820 Ns588p1342 Ns588p1343 0 1 Ns588p1345 

noncomputable def Ns588p1347 := nat_lit 153817169207421561393498816512000 

noncomputable abbrev qz190 := (@HSub.hSub Real Real Real qz359 qz501 qz697)

noncomputable def Ns588p1348 := @Enclosure.Real.IsNear.subLit_ff_p qz190 (@HMul.hMul Real Real Real qz5 qz697 (Real.log Real.pi)) 11747147253457195992161 4503599627370496000 787873032647293 272250000000000000000 9607261130559 16777216000 750357 134217728000 Ns588p1347 9168217730964515292257 4503599627370496000 

noncomputable def Ns588p1349 := nat_lit 23494294506914391984322000 

noncomputable abbrev qz191 := qz501

noncomputable def Ns588p1350 := @Enclosure.Real.IsNear.subLit_ff_p qz191 qz697 14000018923853758170209 4503599627370496000 787873032647293 272250000000000000000 1000476 2000 0 1 Ns588p1349 11747147253457195992161 4503599627370496000 787873032647293 272250000000000000000 

noncomputable def Ns588p1351 := nat_lit 31525240004323838854556788449536376832 

noncomputable def Ns588p1352 := nat_lit 120217210427062097362812928 

noncomputable def Ns588p1353 := nat_lit 126964129528862796449003008985897507950707405851824660894322673781872990270408997224125128023972487392676641608025020559849177074281967197340571156745156101996571378816363610707682424923877064639692665535646924800 

noncomputable def Ns588p1354 := nat_lit 4393924798031829421334570525995114720844582236882476483107805190923984219274709647467995506155708762047349580692747365591622695342850101642952904498385955414023454032626301535164382084926738004096788194425569280 

noncomputable def Ns588p1355 := nat_lit 61833462095563578582622039827356446659514980619372515858905232722909060752726512930907996957805884998216434591228355285070548164283254393516241277257568934990934453529747275422308474446588686184638054400 

noncomputable def Ns588p1356 := BSN.log_dyadic_bound 1906657906304 6100961906304 9 8 Ns588p1353 268435456 87120000 Ns588p1354 Ns588p1355 173588123 8007619812608 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1906657906304) (BSN.artanhQ 6100961906304) 0 8 Ns588p1354 Ns588p1353 Ns588p1355 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz502 := (Real.log (Enclosure.sfrac Bool.false 4003809906304 16000000))

noncomputable def Ns588p1357 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1000476 4000) qz502 1000476 4000 0 1 55980500964011111 4503599627370496 12500018513 1089000000000000000 14001786920617495072209 4503599627370496000 347388014494783 121000000000000000000 (Enclosure.Real.IsNear.const Bool.false 1000476 4000) (BSN.isNear_log_sfrac 4003809906304 16000000 55980500964011111 4503599627370496 12500018513 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4003809906304) qz362)) Bool.false Ns588p1352 Ns588p114 1000001481040000 87120000000000000000000 55980500964011111 4503599627370496 12500018513 1089000000000000000 (BSN.log_rat_reduce_isNear 4003809906304 16000000 17 8007619812608 4194304000000 173588123 268435456 24973259072661432 36028797018963968 87120000 1000000000000000 rfl rfl rfl rfl (Ns588p1356 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p1358 := BSN.arctan_dyadic_bound_f 1000 2000952 1 0 33554432 10890000 0 1 1 0 1 1 16769 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 2000952) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 2000952) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns588p1359 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 2000952))) 884279719003555 562949953421312 1 2000000000000000 16769 33554432 1 10890000 29662063592514972024832 883998381868451 562949953421312 200000001089 2178000000000000000 qz17 (Ns588p1358 rfl) rfl rfl 

noncomputable abbrev qz503 := (@HMul.hMul Real Real Real qz588 qz593 qz696)

noncomputable abbrev qz192 := qz503

noncomputable abbrev qz504 := qz696

noncomputable abbrev qz193 := qz504

noncomputable def Ns588p1360 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 1000476 4000) qz502) qz192 14001786920617495072209 4503599627370496000 347388014494783 121000000000000000000 883998381868451 2251799813685248 200000001089 8712000000000000000 Ns588p1351 14000018923853758170209 4503599627370496000 787873032647293 272250000000000000000 (Ns588p1357 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz193 1 4 0 1 883998381868451 562949953421312 200000001089 2178000000000000000 883998381868451 2251799813685248 200000001089 8712000000000000000 qz369 Ns588p1359 rfl) 

noncomputable def Ns588p1361 := @Ns588p1346 Ns588p1340 Ns588p1341 37845608110887389137 Ns588p820 (@Ns588p1348 37845608110887389137 Ns588p820 (Ns588p1350 (Ns588p1360 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1000476 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz697 (Real.log Real.pi) 1000476 2000 0 1 38410761 33554432 3 268435456 9607261130559 16777216000 750357 134217728000 (Enclosure.Real.IsNear.const Bool.false 1000476 2000) RS589to600.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns588p1342 Ns588p1343) 

noncomputable def Ns588p1362 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz185) Bool.false Ns588p1340 Ns588p1341 37845608110887389137 Ns588p820 136617079089 67108864 571 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz185) (@HAdd.hAdd Real Real Real qz370 qz189 (Enclosure.sfrac Bool.true Ns588p1342 Ns588p1343)) Bool.false Ns588p1340 Ns588p1341 37845608110887389137 Ns588p820 Ns588p1344 (Ns588p1361 rfl rfl)) 

noncomputable def Ns588p1363 := BSN.cos_dyadic_bound_f 148133303 137438953472 1 0 67108864 21801270 0 1 1 0 1 1 67108825 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 148133303) qz383 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 148133303) qz384 0 0 rfl) rfl rfl 

noncomputable def Ns588p1364 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz185) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 136617079089) qz371) Bool.false 136617079089 67108864 571 67108864 Bool.false 67108825 67108864 1 10890000 (Ns588p1362 rfl) (Enclosure.sfrac_false_div 136617079089 67108864) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 136617079089) qz371) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10423954532961079001088) qz372) 226375608064910080 72057594037927936 Bool.false 67108825 67108864 324 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q0 136617079089 67108864 226375608064910080 72057594037927936 324 10423954532961079001088 Ns588p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108825 67108864 10423954532961079001088 Ns588p114 148133303 137438953472 21801270 21780000 (Ns588p1363 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p1365 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz185) Bool.false Ns588p1340 Ns588p1341 37845608110887389137 Ns588p820 1092936632719 536870912 4556 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz185) (@HAdd.hAdd Real Real Real qz370 qz189 (Enclosure.sfrac Bool.true Ns588p1342 Ns588p1343)) Bool.false Ns588p1340 Ns588p1341 37845608110887389137 Ns588p820 Ns588p1344 (Ns588p1361 rfl rfl)) 

noncomputable def Ns588p1366 := Ns588p1339 74745 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 854 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 367846160 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 596 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 489488356 536870912) qz188 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz185) qz185 1) Bool.false 67108825 67108864 392831179 45675970560000 536870600 536870912 4618 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz185) qz185 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz185)) Bool.false 67108825 67108864 392831179 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz185) qz185) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz185)) Bool.false 67108825 67108864 6285298864 730815528960000 67108825 67108864 392831179 45675970560000 (Ns588p1364 rfl rfl) rfl)) rfl) (Ns588p1365 rfl) RS589to600.d7 

noncomputable def Ns588p1367 := nat_lit 5141216723332515751496697414521715085689398387370309306772245453285829281 

noncomputable def Ns588p1368 := nat_lit 1356204277516345408942759224287694235709641791930429800384781188016801 

noncomputable def Ns588p1369 := nat_lit 15420937761442514563672206725116569868596775878527067060715966797481454241 

noncomputable def Ns588p1370 := BSN.cos_dyadic_bound_f 438067101 536870912 3 2 536870912 268435456 Ns588p1367 Ns588p152 Ns588p1368 Ns588p1369 Ns588p155 Ns588p1368 367846160 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 438067101) qz375 0 2 Ns588p1367 Ns588p152 Ns588p1368 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 438067101) qz376 0 2 Ns588p1369 Ns588p155 Ns588p1368 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1371 := nat_lit 372239267802736996088783086194325724822447556735933331448434478794407936 

noncomputable def Ns588p1372 := nat_lit 7112957526193574367060744659170959502564219392687966953537594720256 

noncomputable def Ns588p1373 := nat_lit 1116703577493158601117615137093658832548337541769014618411396361193783296 

noncomputable def Ns588p1374 := BSN.cos_dyadic_bound_f 227251248 536870912 3 2 536870912 268435456 Ns588p1371 Ns588p152 Ns588p1372 Ns588p1373 Ns588p155 Ns588p1372 489488356 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 227251248) qz375 0 2 Ns588p1371 Ns588p152 Ns588p1372 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 227251248) qz376 0 2 Ns588p1373 Ns588p155 Ns588p1372 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1375 := nat_lit 1078337536451175988221308100625 

noncomputable def Ns588p1376 := BSN.sin_dyadic_bound_f 32224685 536870912 2 1 536870912 268435456 Ns588p1375 Ns588p188 Ns588p1375 Ns588p1375 Ns588p189 Ns588p1375 32205338 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32224685) qz373 0 1 Ns588p1375 Ns588p188 Ns588p1375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32224685) qz374 0 1 Ns588p1375 Ns588p189 Ns588p1375 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1377 := nat_lit 48530574249933632490210203956553128824553238863929326041687849033062974620560795453965348712173493756750658011136 

noncomputable def Ns588p1378 := nat_lit 43402474137816036572444415734622510330265079160197756647498918219482902697255550423564305261405212514451456 

noncomputable def Ns588p1379 := nat_lit 293925615126246366376678153164747585707793742220719607347987463106838070715381669933825178844433787622136752373760 

noncomputable def Ns588p1380 := BSN.cos_dyadic_bound_f 769944712 536870912 4 3 536870912 268435456 Ns588p1377 Ns588p146 Ns588p1378 Ns588p1379 Ns588p149 Ns588p1378 73141972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 769944712) qz375 0 3 Ns588p1377 Ns588p146 Ns588p1378 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 769944712) qz376 0 3 Ns588p1379 Ns588p149 Ns588p1378 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1381 := Ns588p1337 126464 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 413 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 32205338 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 270 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 73141972 536870912) qz188 rfl rfl (Ns588p1366 RS589to600.d9 RS589to600.d11 RS589to600.d13 RS589to600.d17 (Ns588p1370 rfl rfl) (Ns588p1374 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns588p1365 rfl) RS589to600.d19 RS589to600.d21 RS589to600.d23 RS589to600.d25 RS589to600.d17 (Ns588p1376 rfl rfl) (Ns588p1380 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns588p1382 := nat_lit 26931739947616142196040743672040325308071376229012386139178292111893855715233859601176216891488822396236302888561 

noncomputable def Ns588p1383 := nat_lit 7442475437337110099525223564756260215252788498773255512676662203433255709872116194413858618956907849952881 

noncomputable def Ns588p1384 := nat_lit 163233691568965599490030769563242326749193591032394811664232612478403265107332877767960875234959825644476794383985 

noncomputable def Ns588p1385 := BSN.cos_dyadic_bound_f 664726691 536870912 4 3 536870912 268435456 Ns588p1382 Ns588p146 Ns588p1383 Ns588p1384 Ns588p149 Ns588p1383 175312768 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 664726691) qz375 0 3 Ns588p1382 Ns588p146 Ns588p1383 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 664726691) qz376 0 3 Ns588p1384 Ns588p149 Ns588p1383 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1386 := nat_lit 9410162576979862097097566045733133717806157662043891920399303091923990216837863139611248765365157824630230871681 

noncomputable def Ns588p1387 := nat_lit 318346394622896797022272695801844711829628780436649819566810949920014960908986333170272998540932073385601 

noncomputable def Ns588p1388 := nat_lit 57069707660946534799176529429253375041467535215050398662806551256187376298916043055014787040672025346234250948225 

noncomputable def Ns588p1389 := BSN.cos_dyadic_bound_f 511181343 536870912 4 3 536870912 268435456 Ns588p1386 Ns588p146 Ns588p1387 Ns588p1388 Ns588p149 Ns588p1387 311349347 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 511181343) qz375 0 3 Ns588p1386 Ns588p146 Ns588p1387 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 511181343) qz376 0 3 Ns588p1388 Ns588p149 Ns588p1387 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1390 := Ns588p1335 170182 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 154 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 175312768 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 311349347 536870912) qz188 rfl rfl (Ns588p1381 rfl rfl) (Ns588p1365 rfl) RS589to600.d27 RS589to600.d29 RS589to600.d31 RS589to600.d33 RS589to600.d17 (Ns588p1385 rfl rfl) (Ns588p1389 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1391 := nat_lit 2720289607399698082946440525689099693962797450766126246726246674544690625 

noncomputable def Ns588p1392 := nat_lit 379779444640104797847108399911790424383129456516106386923873187890625 

noncomputable def Ns588p1393 := nat_lit 8160109263309814039243627360267475501039626093385346527404892277258290625 

noncomputable def Ns588p1394 := BSN.cos_dyadic_bound_f 373629735 536870912 3 2 536870912 268435456 Ns588p1391 Ns588p152 Ns588p1392 Ns588p1393 Ns588p155 Ns588p1392 412022466 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 373629735) qz375 0 2 Ns588p1391 Ns588p152 Ns588p1392 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 373629735) qz376 0 2 Ns588p1393 Ns588p155 Ns588p1392 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1395 := nat_lit 5775995639792455820858301981066668887397158818543197760744512016796391425 

noncomputable def Ns588p1396 := nat_lit 528508121624555277527677434252640971742348509858323295068807255070721 

noncomputable def Ns588p1397 := nat_lit 15126751948211896917512888948852485667324023579549556849948372451291863041 

noncomputable def Ns588p1398 := BSN.sin_dyadic_bound_f 389387009 536870912 3 2 536870912 268435456 Ns588p1395 Ns588p136 Ns588p1396 Ns588p1397 Ns588p139 Ns588p1396 356134579 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 389387009) qz373 0 2 Ns588p1395 Ns588p136 Ns588p1396 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 389387009) qz374 0 2 Ns588p1397 Ns588p139 Ns588p1396 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1399 := Ns588p1333 208379 BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 412022466 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 103 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 356134579 536870912) qz188 rfl rfl (Ns588p1390 rfl) (Ns588p1365 rfl) RS589to600.d35 RS589to600.d37 RS589to600.d39 RS589to600.d41 RS589to600.d17 (Ns588p1394 rfl rfl) (Ns588p1398 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1400 := nat_lit 7363921520436218129312671728472714449045087104206653733805563286291190625 

noncomputable def Ns588p1401 := nat_lit 2781714630649713832297712213876000338643854303480941522860295750390625 

noncomputable def Ns588p1402 := nat_lit 22086201132047354960273419760990391346457973604012999318370969267372790625 

noncomputable def Ns588p1403 := BSN.cos_dyadic_bound_f 479224565 536870912 3 2 536870912 268435456 Ns588p1400 Ns588p152 Ns588p1401 Ns588p1402 Ns588p155 Ns588p1401 336816598 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 479224565) qz375 0 2 Ns588p1400 Ns588p152 Ns588p1401 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 479224565) qz376 0 2 Ns588p1402 Ns588p155 Ns588p1401 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1404 := nat_lit 710880010502589191714812424779527582992534868180899345279002165909070080 

noncomputable def Ns588p1405 := nat_lit 8006823473693136177693842010706779815934888004205090592127693824256 

noncomputable def Ns588p1406 := nat_lit 1861815635506871427508792465345031096860746474464634334155475561114706176 

noncomputable def Ns588p1407 := BSN.sin_dyadic_bound_f 230638886 536870912 3 2 536870912 268435456 Ns588p1404 Ns588p136 Ns588p1405 Ns588p1406 Ns588p139 Ns588p1405 223609811 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 230638886) qz373 0 2 Ns588p1404 Ns588p136 Ns588p1405 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 230638886) qz374 0 2 Ns588p1406 Ns588p139 Ns588p1405 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1408 := Ns588p1331 242732 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 170 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 336816598 536870912) BSN.abs_quadSignPos qz634 (BSN.sfrac_eq_quadSignPos_mul Bool.false 223609811 536870912) qz188 rfl rfl (Ns588p1399 rfl) (Ns588p1365 rfl) RS589to600.d43 RS589to600.d45 RS589to600.d47 RS589to600.d49 RS589to600.d17 (Ns588p1403 rfl rfl) (Ns588p1407 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1409 := nat_lit 16083345010303493060282048216527010661290237066783253568046060532898276515854490885943999110643633828921344000000 

noncomputable def Ns588p1410 := nat_lit 1587765158067304498672776879895322889532190678817257142723766211127656798121565442819967553536000000000000 

noncomputable def Ns588p1411 := nat_lit 97517958443128153995993577185990110193933008035789667965810233176372669170550215877148830729526421109971353600000 

noncomputable def Ns588p1412 := BSN.cos_dyadic_bound_f 584429580 536870912 4 3 536870912 268435456 Ns588p1409 Ns588p146 Ns588p1410 Ns588p1411 Ns588p149 Ns588p1410 248968274 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 584429580) qz375 0 3 Ns588p1409 Ns588p146 Ns588p1410 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 584429580) qz376 0 3 Ns588p1411 Ns588p149 Ns588p1410 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1413 := Ns588p1329 Bool.false 781959018 242732 Bool.true 584429580 28296951008113761 1 Bool.false 248968274 Bool.true Bool.false 710088065 258787 BSN.abs_quadSignNeg qz398 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 248968274 536870912) qz188 rfl (Ns588p1408 rfl) (Ns588p1365 rfl) RS589to600.d51 RS589to600.d53 RS589to600.d17 (Ns588p1412 rfl rfl) rfl 

noncomputable def Ns588p1414 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz185) qz185 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz185) qz185 12) 710088065 536870912 258787 536870912 710088065 536870912 258787 536870912 762451254113730560 710088065 268435456 258787 268435456 (Ns588p1413 rfl rfl rfl rfl) 

noncomputable def Ns588p1415 := @Enclosure.Real.IsNear.mulLit_ff qz694 (Zeta.RiemannSiegel.correction qz187) 9445897 33554432 1 33554432 114765361583109 281474976710656 477638987180757 34058472181989376000 1084061784681804553773 9444732965739290427392 

noncomputable abbrev qz698 := (@HPow.hPow Real Real Real qz7 qz186 qz9)

noncomputable def Ns588p1416 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz698 1 1 0 1 9445897 33554432 1 33554432 9445897 33554432 1 33554432 

noncomputable def Ns588p1417 := @Enclosure.Real.IsNear.sqrt_image qz186 2671447754133 16777216000 250119 16777216000 423412100 423412141 33554432 (@Enclosure.Real.IsNear.of_eq qz186 (@HMul.hMul Real Real Real qz5 qz185 qz3) Bool.false 2671447754133 16777216000 250119 16777216000 (BSN.t_div_two_pi_mk qz185 1000476 1000 qz188) (@Enclosure.Real.IsNear.mulLit_ff qz185 qz3 1000476 1000 0 1 10680707 67108864 1 67108864 2671447754133 16777216000 250119 16777216000 (Enclosure.Real.IsNear.const Bool.false 1000476 1000) RS589to600.d56 rfl)) 

noncomputable abbrev qz783 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 1000476 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz699 := qz783

noncomputable abbrev qz505 := qz699

noncomputable abbrev qz194 := qz505

noncomputable def Ns588p1418 := @Enclosure.Real.IsNear.sqrt_image qz194 846824241 67108864 41 67108864 119194599 119194606 33554432 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 846824241 67108864 41 67108864 846824241 67108864 41 67108864 (Ns588p1417 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns588p1419 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz194) 238389205 67108864 7 67108864 9445896 9445898 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz194) Bool.false 238389205 67108864 7 67108864 238389205 67108864 7 67108864 (Ns588p1418 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns588p1420 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz194)) Bool.false 18891794 67108864 2 67108864 9445897 33554432 1 33554432 (Ns588p1419 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz506 := (@HMul.hMul Real Real Real qz588 qz586 qz693)

noncomputable abbrev qz195 := (Real.cos qz506)

noncomputable abbrev qz700 := (@HMul.hMul Real Real Real qz739 qz782 qz782)

noncomputable abbrev qz507 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz700 qz693) qz603)

noncomputable abbrev qz196 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz507))

noncomputable def Ns588p1421 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz187) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz195) qz196) Bool.false 114765361583109 

noncomputable def Ns588p1422 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz195) qz196 45671739 33554432 123 

noncomputable abbrev qz197 := (@Neg.neg Real Real.instNeg (Real.cos qz506))

noncomputable def Ns588p1423 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz195) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz197)) Bool.true 45671739 33554432 123 16777216 (BSN.inv_eq_neg_inv_neg qz195) 

noncomputable def Ns588p1424 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz197) Bool.false 91343478 67108864 492 67108864 45671739 33554432 

noncomputable def Ns588p1425 := @Enclosure.Real.IsNear.recentre' qz195 Bool.true 49304009 67108864 2887618864 730815528960000 49304009 67108864 180476179 45675970560000 

noncomputable abbrev qz198 := qz506

noncomputable def Ns588p1426 := @Enclosure.Real.IsNear.cos_image qz198 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 260864489) qz371) Bool.false 260864489 67108864 259 67108864 Bool.true 49304009 67108864 1 

noncomputable def Ns588p1427 := nat_lit 1106429092127441677130890463 

noncomputable def Ns588p1428 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz187 884279719003555 140737488355328 1 500000000000000 41517873 67108864 41 67108864 36713413070065283038515 9444732965739290427392 Ns588p1427 

noncomputable def Ns588p1429 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz1 846824241 67108864 41 67108864 12 1 0 1 41517873 41517873 67108864 41 

noncomputable def Ns588p1430 := @Ns588p1429 67108864 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 846824241 67108864 41 67108864 846824241 67108864 41 67108864 (Ns588p1417 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns588p1431 := @Enclosure.Real.IsNear.recentre' qz198 Bool.false 36713413070065283038515 9444732965739290427392 Ns588p1427 Ns588p913 260864489 67108864 259 67108864 (@Ns588p1428 Ns588p913 RS589to600.d55 (Ns588p1430 rfl rfl) rfl) 

noncomputable def Ns588p1432 := nat_lit 7210915105456327825031168 

noncomputable def Ns588p1433 := nat_lit 66110561878978421732753761205613910636899457053596661488779164944498886940028578889717343361 

noncomputable def Ns588p1434 := nat_lit 12158630390507702672731221665135568553140140357510284152662755335666497290088110840702081 

noncomputable def Ns588p1435 := nat_lit 198307368376154249792915821173511460773592090880074963898032169322825327825505560447470625921 

noncomputable def Ns588p1436 := BSN.cos_dyadic_bound_f 102473266927 137438953472 3 2 67108864 21801270 Ns588p1433 Ns588p511 Ns588p1434 Ns588p1435 Ns588p514 Ns588p1434 49304009 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 102473266927) qz383 0 2 Ns588p1433 Ns588p511 Ns588p1434 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 102473266927) qz384 0 2 Ns588p1435 Ns588p514 Ns588p1434 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1437 := @Ns588p1426 10890000 (Ns588p1431 rfl) (Enclosure.sfrac_false_div 260864489 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 260864489) qz371) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns588p1432) qz372) 226375608064910080 72057594037927936 Bool.false 49304009 67108864 0 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 260864489 67108864 226375608064910080 72057594037927936 0 Ns588p1432 Ns588p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 49304009 67108864 Ns588p1432 Ns588p114 102473266927 137438953472 21801270 21780000 (Ns588p1436 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p1438 := @Enclosure.Real.IsNear.inv_image qz197 49304009 67108864 180476179 45675970560000 45671493 45671985 33554432 (@Enclosure.Real.IsNear.neg qz195 Bool.true 49304009 67108864 180476179 45675970560000 (Ns588p1425 (Ns588p1437 rfl rfl) rfl)) 

noncomputable def Ns588p1439 := Ns588p1423 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz197) Bool.false 45671739 33554432 123 16777216 (@Ns588p1424 123 16777216 (Ns588p1438 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p1440 := @Enclosure.Real.IsNear.recentre' qz196 Bool.true 10051324 33554432 

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz355 qz352 qz507)

noncomputable def Ns588p1441 := @Enclosure.Real.IsNear.cos_image qz199 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 125830475)) qz371) Bool.true 125830475 67108864 

noncomputable def Ns588p1442 := nat_lit 1188435236767554103178960400445 

noncomputable def Ns588p1443 := nat_lit 33224881970343826784052974619813841 

noncomputable def Ns588p1444 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true Ns588p1442 Ns588p929 Ns588p1443 

noncomputable abbrev qz200 := qz507

noncomputable def Ns588p1445 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz200 884279719003555 140737488355328 1 500000000000000 1343958490992799 

noncomputable abbrev qz508 := (@HSub.hSub Real Real Real qz592 qz700 qz693)

noncomputable abbrev qz201 := qz508

noncomputable def Ns588p1446 := @Enclosure.Real.IsNear.subLit_tf qz201 qz31 1062483514282143 4503599627370496 6155930691 4503599627370496 1 16 

noncomputable abbrev qz509 := qz700

noncomputable abbrev qz202 := qz509

noncomputable def Ns588p1447 := @Enclosure.Real.IsNear.subLit_ff_n qz202 qz187 1723733778444129 4503599627370496 3404467267 4503599627370496 41517873 67108864 41 67108864 

noncomputable def Ns588p1448 := @Enclosure.Real.IsNear.mulLit_ff qz187 qz187 41517873 67108864 41 67108864 41517873 67108864 41 67108864 1723733778444129 4503599627370496 

noncomputable def Ns588p1449 := nat_lit 2073456716046544735332974525828089575264965042203205283049773639728400604894248963871033067968369140625 

noncomputable def Ns588p1450 := nat_lit 15755421724580276759726214623872620473663716288231132337080265057161571434101805746555328369140625 

noncomputable def Ns588p1451 := nat_lit 12517644377526969727710608434813050219401542066219561370999123878592187403748816861307738065344369140625 

noncomputable def Ns588p1452 := BSN.cos_dyadic_bound_t 125830475 67108864 4 3 33554432 10890000 Ns588p1449 Ns588p231 Ns588p1450 Ns588p1451 Ns588p234 Ns588p1450 10051324 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 125830475) (BSN.cosEvenQ 67108864) 0 3 Ns588p1449 Ns588p231 Ns588p1450 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 125830475) (BSN.cosOddQ 67108864) 0 3 Ns588p1451 Ns588p234 Ns588p1450 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1453 := @Ns588p1440 6350638864 730815528960000 2512831 8388608 396914929 45675970560000 (@Ns588p1441 577 67108864 Bool.true 10051324 33554432 1 10890000 (@Ns588p1444 Ns588p1184 125830475 67108864 577 67108864 (@Ns588p1445 4503599627370496 6155930691 4503599627370496 Ns588p1442 Ns588p929 Ns588p1443 Ns588p1184 RS589to600.d55 (@Ns588p1446 0 1 21503335855884784 1343958490992799 4503599627370496 6155930691 4503599627370496 (@Ns588p1447 71302061662202392215552 1062483514282143 4503599627370496 6155930691 4503599627370496 (@Ns588p1448 3404467267 4503599627370496 (Ns588p1430 rfl rfl) (Ns588p1430 rfl rfl) rfl) (Ns588p1430 rfl rfl) rfl rfl) qz388 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 125830475 67108864) (BSN.cos_neg_of_bound 125830475 67108864 Bool.true 10051324 33554432 1 10890000 (Ns588p1452 rfl rfl)) rfl rfl) 

noncomputable def Ns588p1454 := @Ns588p1415 205709807385649744263 Ns588p1326 (Ns588p1416 qz33 (@Enclosure.Real.IsNear.of_eq qz698 (@Inv.inv Real Real.instInv (Real.sqrt qz194)) Bool.false 9445897 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz186 (BSN.t_div_two_pi_nonneg qz185 1000476 1000 qz188)) Ns588p1420) rfl) (@Ns588p1421 281474976710656 477638987180757 34058472181989376000 (BSN.correction_mk qz187 (BSN.cos_two_pi_p_ne_zero_mk qz185 1000476 1000 12 qz188 rfl rfl (@BSN.floor_sqrt_eq_dec qz185 1000476 1000 12 qz188 rfl rfl rfl))) (@Ns588p1422 16777216 2512831 8388608 396914929 45675970560000 114765361583109 281474976710656 477638987180757 34058472181989376000 Ns588p1439 (Ns588p1453 rfl) rfl)) 

noncomputable def Ns588p1455 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz185) (hardyZApproximantRS₀ qz185) Bool.false 23899940910116918436307 9444732965739290427392 50284629356024767056263 Ns588p1326 (@Eq.refl Real (hardyZApproximantRS₀ qz185)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz185) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz185) qz185 12) (@HMul.hMul Real Real Real qz5 qz694 (Zeta.RiemannSiegel.correction qz187))) Bool.false 23899940910116918436307 9444732965739290427392 50284629356024767056263 Ns588p1326 (BSN.hardyZApproximantRS₀_eq qz185 12 (@BSN.floor_sqrt_eq_dec qz185 1000476 1000 12 qz188 rfl rfl rfl)) (@Ns588p1328 23899940910116918436307 9444732965739290427392 50284629356024767056263 Ns588p1326 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz185) qz185 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz185) qz185 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz185) qz185 12)) Bool.false 710088065 268435456 258787 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz185) qz185 12) (Ns588p1414 (Ns588p1413 rfl rfl rfl rfl) rfl rfl)) (Ns588p1454 rfl) rfl rfl)) 

theorem RS589to600.d68 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz185) Bool.false 23899940910116918436307 9444732965739290427392 50284629356024767056263 Ns588p1326 := Ns588p1455 

noncomputable def Ns588p1456 := nat_lit 5163394782434928567606807887872 

noncomputable abbrev qz784 := (Enclosure.sfrac Bool.false 1001715 1000)

noncomputable abbrev qz701 := qz784

noncomputable abbrev qz510 := qz701

noncomputable abbrev qz203 := qz510

noncomputable abbrev qz785 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 1001715 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz702 := qz785

noncomputable abbrev qz511 := qz702

noncomputable abbrev qz204 := qz511

noncomputable abbrev qz786 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 1001715 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz703 := qz786

noncomputable abbrev qz512 := qz703

noncomputable abbrev qz205 := qz512

noncomputable abbrev qz704 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz204 qz9))

noncomputable def Ns588p1457 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz203) qz203 12) (@HMul.hMul Real Real Real qz5 qz704 (Zeta.RiemannSiegel.correction qz205)) 121142187 134217728 259099 268435456 4371794715764475694277 37778931862957161709568 2709092177935366337 649325391394576216883200 Ns588p1456 

noncomputable def Ns588p1458 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.cos BSN.quadSignNeg 11 12 1001715 1000 286 536870912 268435456 9007199254740992 Bool.false 1094623195356 4561 1334074092 51 154981288 8 

noncomputable def Ns588p1459 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 1001715 1000 170 231 536870912 268435456 9007199254740992 Bool.false 1094623195356 4561 

noncomputable def Ns588p1460 := Ns588p1459 1236190956 51 169773496 8 1287360220 51 161872664 8 Bool.true 63702584 208628 Bool.true 324302522 Bool.true 139115562 28296951008113761 1 Bool.false 441864128 Bool.true Bool.false 137563968 Bool.false Bool.true 161955201 

noncomputable def Ns588p1461 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 1001715 1000 28 103 536870912 268435456 9007199254740992 Bool.false 1094623195356 4561 

noncomputable def Ns588p1462 := Ns588p1461 1116391676 51 189812536 8 1179625948 51 178956968 8 Bool.true 305832749 170384 Bool.true 70276385 Bool.true 164380921 28296951008113761 1 Bool.false 532277887 Bool.false Bool.false 161824529 Bool.false Bool.true 63702584 

noncomputable def Ns588p1463 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 1001715 1000 155 57 536870912 268435456 9007199254740992 Bool.false 1094623195356 4561 

noncomputable def Ns588p1464 := Ns588p1463 961943533 51 219176632 8 1044702541 51 202918136 8 Bool.true 404914447 126613 Bool.false 316126434 Bool.false 60042675 28296951008113761 1 Bool.false 298172510 Bool.false Bool.false 59917586 Bool.true Bool.true 305832749 

noncomputable def Ns588p1465 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 1001715 1000 413 271 536870912 268435456 9007199254740992 Bool.false 1094623195356 4561 

noncomputable def Ns588p1466 := Ns588p1465 744261104 50 268435448 8 864060384 50 240095976 8 Bool.true 340904224 74831 Bool.false 796647814 Bool.false 542621677 28296951008113761 1 Bool.false 534843942 Bool.true Bool.false 454842470 Bool.false Bool.true 404914447 

noncomputable def Ns588p1467 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz203) qz203 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 1001715 1000 855 597 536870912 268435456 9007199254740992 Bool.false 1094623195356 4561 

noncomputable def Ns588p1468 := Ns588p1467 372130544 50 379625064 8 589812976 50 309962568 8 Bool.true 536870664 4618 Bool.false 820245137 Bool.false 339720752 28296951008113761 1 Bool.false 536375327 Bool.false Bool.false 317499100 Bool.true Bool.true 340904224 

noncomputable def Ns588p1469 := nat_lit 474995937331667280502435726376133448998841966535798881 

noncomputable def Ns588p1470 := nat_lit 232967383802400419318140830517808353902301754163200 

noncomputable def Ns588p1471 := nat_lit 484130447679679151910830914500000000 

noncomputable def Ns588p1472 := nat_lit 2909764726696245326441708049320205000000 

noncomputable abbrev qz787 := (@Eq.refl Real (Enclosure.sfrac Bool.false 1001715 1000))

noncomputable abbrev qz705 := qz787

noncomputable abbrev qz513 := qz705

noncomputable abbrev qz206 := qz513

noncomputable def Ns588p1473 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz203 1001715 1000 4013732764900 16000000 2003430 4000 2000 Ns588p1471 Ns588p1472 qz206 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns588p1474 := nat_lit 21374817179925027622609607686926005204947888494110949645000000 

noncomputable abbrev qz706 := (@HSub.hSub Real Real Real qz743 qz744 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz745 (@Nat.cast Real Real.instNatCast 2003430))))

noncomputable abbrev qz514 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 1001715 4000) (Real.log (Enclosure.sfrac Bool.false 4013732764900 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz706))

noncomputable abbrev qz707 := (Enclosure.sfrac Bool.false 1001715 2000)

noncomputable abbrev qz207 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz514 qz707) (@HMul.hMul Real Real Real qz355 qz707 (Real.log Real.pi)))

noncomputable def Ns588p1475 := @Enclosure.Real.IsNear.addLit_ft_p qz207 (Enclosure.sfrac Bool.true Ns588p1471 Ns588p1472) 7345892514291977607169 3602879701896396800 30313879757392977089 Ns588p555 Ns588p1471 Ns588p1472 0 1 Ns588p1474 

noncomputable def Ns588p1476 := nat_lit 98594900340047676306109969203200 

noncomputable abbrev qz208 := (@HSub.hSub Real Real Real qz359 qz514 qz707)

noncomputable def Ns588p1477 := @Enclosure.Real.IsNear.subLit_ff_p qz208 (@HMul.hMul Real Real Real qz5 qz707 (Real.log Real.pi)) 9411591151039890118657 3602879701896396800 2524291209058859 871200000000000000000 7695327091023 13421772800 601029 107374182400 Ns588p1476 7345892514291977607169 3602879701896396800 

noncomputable def Ns588p1478 := nat_lit 18823182302079780237314000 

noncomputable abbrev qz209 := qz514

noncomputable def Ns588p1479 := @Enclosure.Real.IsNear.subLit_ff_p qz209 qz707 11216120471332464678913 3602879701896396800 2524291209058859 871200000000000000000 1001715 2000 0 1 Ns588p1478 9411591151039890118657 3602879701896396800 2524291209058859 871200000000000000000 

noncomputable def Ns588p1480 := nat_lit 25256457987617739945545027199564775424 

noncomputable def Ns588p1481 := nat_lit 120241149941385333066170368 

noncomputable def Ns588p1482 := nat_lit 130308736219724959626082016549650313091567755337067463880797091787662683050314526794946469122028060864913938950836373958242381455442325557624041421234207643826406225505658570133942500000000000000000000000000000000 

noncomputable def Ns588p1483 := nat_lit 4544023875536480343725867530965803915120200234629076931026767899434919511251497912619779072552512769156919338322557324855569753868630380764121494259754230239567271526686069080568000000000000000000000000000000000 

noncomputable def Ns588p1484 := nat_lit 67188215736610668905563415273948142832489343689020367395798284454519426870077732075015082360373434473820914631788703189157969767381326200728496441795621703144836306666702500000000000000000000000000000000 

noncomputable def Ns588p1485 := BSN.log_dyadic_bound 1916580764900 6110884764900 9 8 Ns588p1482 268435456 87120000 Ns588p1483 Ns588p1484 174252578 8027465529800 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1916580764900) (BSN.artanhQ 6110884764900) 0 8 Ns588p1483 Ns588p1482 Ns588p1484 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz515 := (Real.log (Enclosure.sfrac Bool.false 4013732764900 16000000))

noncomputable def Ns588p1486 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1001715 4000) qz515 1001715 4000 0 1 55991648669068391 4503599627370496 12500018513 1089000000000000000 11217534869307168658113 3602879701896396800 75887612392423 26400000000000000000 (Enclosure.Real.IsNear.const Bool.false 1001715 4000) (BSN.isNear_log_sfrac 4013732764900 16000000 55991648669068391 4503599627370496 12500018513 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4013732764900) qz362)) Bool.false Ns588p1481 Ns588p114 1000001481040000 87120000000000000000000 55991648669068391 4503599627370496 12500018513 1089000000000000000 (BSN.log_rat_reduce_isNear 4013732764900 16000000 17 8027465529800 4194304000000 174252578 268435456 24973259072661432 36028797018963968 87120000 1000000000000000 rfl rfl rfl rfl (Ns588p1485 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p1487 := BSN.arctan_dyadic_bound_f 1000 2003430 1 0 33554432 10890000 0 1 1 0 1 1 16748 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 2003430) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 2003430) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns588p1488 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 2003430))) 884279719003555 562949953421312 1 2000000000000000 16748 33554432 1 10890000 29662075414463993872384 883998734189987 562949953421312 200000001089 2178000000000000000 qz17 (Ns588p1487 rfl) rfl rfl 

noncomputable abbrev qz516 := (@HMul.hMul Real Real Real qz588 qz593 qz706)

noncomputable abbrev qz210 := qz516

noncomputable abbrev qz517 := qz706

noncomputable abbrev qz211 := qz517

noncomputable def Ns588p1489 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 1001715 4000) qz515) qz210 11217534869307168658113 3602879701896396800 75887612392423 26400000000000000000 883998734189987 2251799813685248 200000001089 8712000000000000000 Ns588p1480 11216120471332464678913 3602879701896396800 2524291209058859 871200000000000000000 (Ns588p1486 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz211 1 4 0 1 883998734189987 562949953421312 200000001089 2178000000000000000 883998734189987 2251799813685248 200000001089 8712000000000000000 qz369 Ns588p1488 rfl) 

noncomputable def Ns588p1490 := @Ns588p1475 Ns588p1469 Ns588p1470 30313879757392977089 Ns588p555 (@Ns588p1477 30313879757392977089 Ns588p555 (Ns588p1479 (Ns588p1489 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1001715 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz707 (Real.log Real.pi) 1001715 2000 0 1 38410761 33554432 3 268435456 7695327091023 13421772800 601029 107374182400 (Enclosure.Real.IsNear.const Bool.false 1001715 2000) RS589to600.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns588p1471 Ns588p1472) 

noncomputable def Ns588p1491 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz203) Bool.false Ns588p1469 Ns588p1470 30313879757392977089 Ns588p555 136827899419 67108864 571 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz203) (@HAdd.hAdd Real Real Real qz370 qz207 (Enclosure.sfrac Bool.true Ns588p1471 Ns588p1472)) Bool.false Ns588p1469 Ns588p1470 30313879757392977089 Ns588p555 Ns588p1473 (Ns588p1490 rfl rfl)) 

noncomputable def Ns588p1492 := BSN.cos_dyadic_bound_f 130962598 137438953472 1 0 67108864 21801270 0 1 1 0 1 1 67108833 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 130962598) qz383 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 130962598) qz384 0 0 rfl) rfl rfl 

noncomputable def Ns588p1493 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz203) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 136827899419) qz371) Bool.false 136827899419 67108864 571 67108864 Bool.true 67108833 67108864 1 10890000 (Ns588p1491 rfl) (Enclosure.sfrac_false_div 136827899419 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 136827899419) qz371) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9215673606253584580608) qz372) 226375608064910080 72057594037927936 Bool.false 67108833 67108864 324 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 136827899419 67108864 226375608064910080 72057594037927936 324 9215673606253584580608 Ns588p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108833 67108864 9215673606253584580608 Ns588p114 130962598 137438953472 21801270 21780000 (Ns588p1492 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p1494 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz203) Bool.false Ns588p1469 Ns588p1470 30313879757392977089 Ns588p555 1094623195356 536870912 4561 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz203) (@HAdd.hAdd Real Real Real qz370 qz207 (Enclosure.sfrac Bool.true Ns588p1471 Ns588p1472)) Bool.false Ns588p1469 Ns588p1470 30313879757392977089 Ns588p555 Ns588p1473 (Ns588p1490 rfl rfl)) 

noncomputable def Ns588p1495 := Ns588p1468 74831 BSN.abs_quadSignPos (BSN.cos_quad_nat3 855 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536375327 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 597 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 317499100 536870912) qz206 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 1) Bool.true 67108833 67108864 392831179 45675970560000 536870664 536870912 4618 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz203)) Bool.true 67108833 67108864 392831179 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz203) qz203) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz203)) Bool.true 67108833 67108864 6285298864 730815528960000 67108833 67108864 392831179 45675970560000 (Ns588p1493 rfl rfl) rfl)) rfl) (Ns588p1494 rfl) RS589to600.d7 

noncomputable def Ns588p1496 := nat_lit 162410756520180234059588157275321255437106952509756368431198014401527241189973261921526336881408270775251474546881 

noncomputable def Ns588p1497 := nat_lit 92752146948908131583050916586487832504768549126789605740860307926787716297146846758076712292691630463090881 

noncomputable def Ns588p1498 := nat_lit 811150526824104216841556844430942431126820629899578674702581251238616275774324062274997321234225969563534213480641 

noncomputable def Ns588p1499 := BSN.sin_dyadic_bound_f 820245137 536870912 4 3 536870912 268435456 Ns588p1496 Ns588p172 Ns588p1497 Ns588p1498 Ns588p175 Ns588p1497 536375327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 820245137) qz373 0 3 Ns588p1496 Ns588p172 Ns588p1497 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 820245137) qz374 0 3 Ns588p1498 Ns588p175 Ns588p1497 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1500 := nat_lit 3346359657467750824903189728226338956784479074003724920124009879783342080 

noncomputable def Ns588p1501 := nat_lit 177409394680023792757063274988897471589930652832872383983232542048256 

noncomputable def Ns588p1502 := nat_lit 8763988059109865455272461661957096195672013877524216806941195880078770176 

noncomputable def Ns588p1503 := BSN.sin_dyadic_bound_f 339720752 536870912 3 2 536870912 268435456 Ns588p1500 Ns588p136 Ns588p1501 Ns588p1502 Ns588p139 Ns588p1501 317499100 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 339720752) qz373 0 2 Ns588p1500 Ns588p136 Ns588p1501 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 339720752) qz374 0 2 Ns588p1502 Ns588p139 Ns588p1501 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1504 := nat_lit 144483903256234438636465007644022888000248201509717697632022344085862535716787261607397486159718644880567813738496 

noncomputable def Ns588p1505 := nat_lit 65342602121333577427682459343714504219140307206289108325819056260650094920753791399981441701882589673885696 

noncomputable def Ns588p1506 := nat_lit 721704406489126581803235086321844543823213334974741175886245129613621923943544338344104858638989152529515461677056 

noncomputable def Ns588p1507 := BSN.sin_dyadic_bound_f 796647814 536870912 4 3 536870912 268435456 Ns588p1504 Ns588p172 Ns588p1505 Ns588p1506 Ns588p175 Ns588p1505 534843942 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 796647814) qz373 0 3 Ns588p1504 Ns588p172 Ns588p1505 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 796647814) qz374 0 3 Ns588p1506 Ns588p175 Ns588p1505 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1508 := nat_lit 21787112900056440783597841738718998622264025092740176107479416931111574305 

noncomputable def Ns588p1509 := nat_lit 7515832867854159227371629615803813502843861945015892789026286045666081 

noncomputable def Ns588p1510 := nat_lit 57049317675504628651626221915362266407877366133075197407454335118361140001 

noncomputable def Ns588p1511 := BSN.sin_dyadic_bound_f 542621677 536870912 3 2 536870912 268435456 Ns588p1508 Ns588p136 Ns588p1509 Ns588p1510 Ns588p139 Ns588p1509 454842470 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 542621677) qz373 0 2 Ns588p1508 Ns588p136 Ns588p1509 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 542621677) qz374 0 2 Ns588p1510 Ns588p139 Ns588p1509 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1512 := Ns588p1466 126613 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 413 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 534843942 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 271 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 454842470 536870912) qz206 rfl rfl (Ns588p1495 RS589to600.d9 RS589to600.d11 RS589to600.d13 RS589to600.d17 (Ns588p1499 rfl rfl) (Ns588p1503 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns588p1494 rfl) RS589to600.d19 RS589to600.d21 RS589to600.d23 RS589to600.d25 RS589to600.d17 (Ns588p1507 rfl rfl) (Ns588p1511 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns588p1513 := nat_lit 2509122113765221024131617370792480969477146983682997172333838795891769600 

noncomputable def Ns588p1514 := nat_lit 99743935346303748871936905128466812479656128409010907345000577597696 

noncomputable def Ns588p1515 := nat_lit 6571348807775494380941776644705337402362798847342806576548162083543286016 

noncomputable def Ns588p1516 := BSN.sin_dyadic_bound_f 316126434 536870912 3 2 536870912 268435456 Ns588p1513 Ns588p136 Ns588p1514 Ns588p1515 Ns588p139 Ns588p1514 298172510 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 316126434) qz373 0 2 Ns588p1513 Ns588p136 Ns588p1514 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 316126434) qz374 0 2 Ns588p1515 Ns588p139 Ns588p1514 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1517 := nat_lit 12996910555617092519060469140625 

noncomputable def Ns588p1518 := BSN.sin_dyadic_bound_f 60042675 536870912 2 1 536870912 268435456 Ns588p1517 Ns588p188 Ns588p1517 Ns588p1517 Ns588p189 Ns588p1517 59917586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 60042675) qz373 0 1 Ns588p1517 Ns588p188 Ns588p1517 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 60042675) qz374 0 1 Ns588p1517 Ns588p189 Ns588p1517 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1519 := Ns588p1464 170384 BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 298172510 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59917586 536870912) qz206 rfl rfl (Ns588p1512 rfl rfl) (Ns588p1494 rfl) RS589to600.d27 RS589to600.d29 RS589to600.d31 RS589to600.d33 RS589to600.d17 (Ns588p1516 rfl rfl) (Ns588p1518 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1520 := nat_lit 24391451964232022495844124650625 

noncomputable def Ns588p1521 := BSN.cos_dyadic_bound_f 70276385 536870912 2 1 536870912 268435456 Ns588p1520 Ns588p142 Ns588p1520 Ns588p1520 Ns588p143 Ns588p1520 532277887 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 70276385) qz375 0 1 Ns588p1520 Ns588p142 Ns588p1520 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 70276385) qz376 0 1 Ns588p1520 Ns588p143 Ns588p1520 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1522 := nat_lit 730139152865176848404485869514081 

noncomputable def Ns588p1523 := BSN.sin_dyadic_bound_f 164380921 536870912 2 1 536870912 268435456 Ns588p1522 Ns588p188 Ns588p1522 Ns588p1522 Ns588p189 Ns588p1522 161824529 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 164380921) qz373 0 1 Ns588p1522 Ns588p188 Ns588p1522 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 164380921) qz374 0 1 Ns588p1522 Ns588p189 Ns588p1522 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1524 := Ns588p1462 208628 BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 532277887 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 103 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 161824529 536870912) qz206 rfl rfl (Ns588p1519 rfl) (Ns588p1494 rfl) RS589to600.d35 RS589to600.d37 RS589to600.d39 RS589to600.d41 RS589to600.d17 (Ns588p1521 rfl rfl) (Ns588p1523 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1525 := nat_lit 1543918959797070259234145747879366267858261356609647671921463558353756416 

noncomputable def Ns588p1526 := nat_lit 122349615391195379461446889804200070116594086993933954235817860833536 

noncomputable def Ns588p1527 := nat_lit 4631512180160428386943514349858490403434550881654955147855919039339602176 

noncomputable def Ns588p1528 := BSN.cos_dyadic_bound_f 324302522 536870912 3 2 536870912 268435456 Ns588p1525 Ns588p152 Ns588p1526 Ns588p1527 Ns588p155 Ns588p1526 441864128 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 324302522) qz375 0 2 Ns588p1525 Ns588p152 Ns588p1526 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 324302522) qz376 0 2 Ns588p1527 Ns588p155 Ns588p1526 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1529 := nat_lit 374544012012314146728459516312336 

noncomputable def Ns588p1530 := BSN.sin_dyadic_bound_f 139115562 536870912 2 1 536870912 268435456 Ns588p1529 Ns588p188 Ns588p1529 Ns588p1529 Ns588p189 Ns588p1529 137563968 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 139115562) qz373 0 1 Ns588p1529 Ns588p188 Ns588p1529 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 139115562) qz374 0 1 Ns588p1529 Ns588p189 Ns588p1529 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1531 := Ns588p1460 243024 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 170 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 441864128 536870912) BSN.abs_quadSignPos qz634 (BSN.sfrac_eq_quadSignPos_mul Bool.false 137563968 536870912) qz206 rfl rfl (Ns588p1524 rfl) (Ns588p1494 rfl) RS589to600.d43 RS589to600.d45 RS589to600.d47 RS589to600.d49 RS589to600.d17 (Ns588p1528 rfl rfl) (Ns588p1530 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1532 := nat_lit 12685238068244804979999035982300693427290000322143942046202941607601709051992458429184853759110828703752754469281 

noncomputable def Ns588p1533 := nat_lit 779440232427212039459951967646609810616362519045573547306301483564442200871579410677897899327389715831201 

noncomputable def Ns588p1534 := nat_lit 76923299734222344388238986351971405787469981468999903982110319318972340422850343780775962404632010867176314411425 

noncomputable def Ns588p1535 := BSN.cos_dyadic_bound_f 550784743 536870912 4 3 536870912 268435456 Ns588p1532 Ns588p146 Ns588p1533 Ns588p1534 Ns588p149 Ns588p1533 278268406 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 550784743) qz375 0 3 Ns588p1532 Ns588p146 Ns588p1533 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 550784743) qz376 0 3 Ns588p1534 Ns588p149 Ns588p1533 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1536 := Ns588p1458 Bool.true 161955201 243024 Bool.true 550784743 28296951008113761 1 Bool.false 278268406 Bool.true Bool.true 242284374 259099 BSN.abs_quadSignNeg qz398 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 278268406 536870912) qz206 rfl (Ns588p1531 rfl) (Ns588p1494 rfl) RS589to600.d51 RS589to600.d53 RS589to600.d17 (Ns588p1535 rfl rfl) rfl 

noncomputable def Ns588p1537 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 12) 242284374 536870912 259099 536870912 242284374 536870912 259099 536870912 260150865665458176 121142187 134217728 259099 268435456 (Ns588p1536 rfl rfl rfl rfl) 

noncomputable def Ns588p1538 := @Enclosure.Real.IsNear.mulLit_ff qz704 (Zeta.RiemannSiegel.correction qz205) 18885949 67108864 1 67108864 231483983980073 562949953421312 114587343372643 7740561859543040000 4371794715764475694277 37778931862957161709568 

noncomputable abbrev qz708 := (@HPow.hPow Real Real Real qz7 qz204 qz9)

noncomputable def Ns588p1539 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz708 1 1 0 1 18885949 67108864 1 67108864 18885949 67108864 1 67108864 

noncomputable def Ns588p1540 := @Enclosure.Real.IsNear.sqrt_image qz204 2139804882501 13421772800 200343 13421772800 423674198 423674239 33554432 (@Enclosure.Real.IsNear.of_eq qz204 (@HMul.hMul Real Real Real qz5 qz203 qz3) Bool.false 2139804882501 13421772800 200343 13421772800 (BSN.t_div_two_pi_mk qz203 1001715 1000 qz206) (@Enclosure.Real.IsNear.mulLit_ff qz203 qz3 1001715 1000 0 1 10680707 67108864 1 67108864 2139804882501 13421772800 200343 13421772800 (Enclosure.Real.IsNear.const Bool.false 1001715 1000) RS589to600.d56 rfl)) 

noncomputable abbrev qz788 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 1001715 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz709 := qz788

noncomputable abbrev qz518 := qz709

noncomputable abbrev qz212 := qz518

noncomputable def Ns588p1541 := @Enclosure.Real.IsNear.sqrt_image qz212 847348437 67108864 41 67108864 119231485 119231491 33554432 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 847348437 67108864 41 67108864 847348437 67108864 41 67108864 (Ns588p1540 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns588p1542 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz212) 116437 32768 3 33554432 9442974 9442975 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz212) Bool.false 238462976 67108864 6 67108864 116437 32768 3 33554432 (Ns588p1541 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns588p1543 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz212)) Bool.false 18885949 67108864 1 67108864 18885949 67108864 1 67108864 (Ns588p1542 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz519 := (@HMul.hMul Real Real Real qz588 qz586 qz703)

noncomputable abbrev qz213 := (Real.cos qz519)

noncomputable abbrev qz710 := (@HMul.hMul Real Real Real qz739 qz786 qz786)

noncomputable abbrev qz520 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz710 qz703) qz603)

noncomputable abbrev qz214 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz520))

noncomputable def Ns588p1544 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz205) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz213) qz214) Bool.false 231483983980073 

noncomputable def Ns588p1545 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz213) qz214 95798593 67108864 539 

noncomputable abbrev qz215 := (@Neg.neg Real Real.instNeg (Real.cos qz519))

noncomputable def Ns588p1546 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz213) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz215)) Bool.true 95798593 67108864 539 67108864 (BSN.inv_eq_neg_inv_neg qz213) 

noncomputable def Ns588p1547 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz215) Bool.false 95798593 67108864 539 67108864 95798593 67108864 

noncomputable def Ns588p1548 := @Enclosure.Real.IsNear.recentre' qz213 Bool.true 47011125 67108864 1438364432 365407764480000 47011125 67108864 89897777 22837985280000 

noncomputable abbrev qz216 := qz519

noncomputable def Ns588p1549 := @Enclosure.Real.IsNear.cos_image qz216 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 132079055) qz397) Bool.false 132079055 33554432 129 33554432 Bool.true 47011125 67108864 1 

noncomputable def Ns588p1550 := nat_lit 221285818426388897296855699 

noncomputable def Ns588p1551 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz205 884279719003555 140737488355328 1 500000000000000 42042069 67108864 41 67108864 37176948961648070555295 9444732965739290427392 Ns588p1550 

noncomputable def Ns588p1552 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz1 847348437 67108864 41 67108864 12 1 0 1 42042069 42042069 67108864 41 

noncomputable def Ns588p1553 := @Ns588p1552 67108864 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 847348437 67108864 41 67108864 847348437 67108864 41 67108864 (Ns588p1540 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns588p1554 := @Enclosure.Real.IsNear.recentre' qz216 Bool.false 37176948961648070555295 9444732965739290427392 Ns588p1550 Ns588p1297 132079055 33554432 129 33554432 (@Ns588p1551 Ns588p1297 RS589to600.d55 (Ns588p1553 rfl rfl) rfl) 

noncomputable def Ns588p1555 := nat_lit 3842787957660958159011840 

noncomputable def Ns588p1556 := nat_lit 85317512313858836771208009345619451580549822967779432177650488910477891721330651060435690625 

noncomputable def Ns588p1557 := nat_lit 20247570949266488787342495308557099346604084809388937113140133431659818658144685062890625 

noncomputable def Ns588p1558 := nat_lit 255912041799677977336049343046241240542956260733719518658725186464570355526675663811181290625 

noncomputable def Ns588p1559 := BSN.cos_dyadic_bound_f 109218602735 137438953472 3 2 67108864 21801270 Ns588p1556 Ns588p511 Ns588p1557 Ns588p1558 Ns588p514 Ns588p1557 47011125 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 109218602735) qz383 0 2 Ns588p1556 Ns588p511 Ns588p1557 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 109218602735) qz384 0 2 Ns588p1558 Ns588p514 Ns588p1557 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1560 := @Ns588p1549 10890000 (Ns588p1554 rfl) (Enclosure.sfrac_false_div 132079055 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 132079055) qz397) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns588p1555) qz611) 226375608064910080 72057594037927936 Bool.false 47011125 67108864 0 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 132079055 33554432 226375608064910080 72057594037927936 0 Ns588p1555 Ns588p278 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 47011125 67108864 Ns588p1555 Ns588p278 109218602735 137438953472 21801270 21780000 (Ns588p1559 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p1561 := @Enclosure.Real.IsNear.inv_image qz215 47011125 67108864 89897777 22837985280000 47899027 47899566 33554432 (@Enclosure.Real.IsNear.neg qz213 Bool.true 47011125 67108864 89897777 22837985280000 (Ns588p1548 (Ns588p1560 rfl rfl) rfl)) 

noncomputable def Ns588p1562 := Ns588p1546 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz215) Bool.false 95798593 67108864 539 67108864 (@Ns588p1547 539 67108864 (Ns588p1561 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p1563 := @Enclosure.Real.IsNear.recentre' qz214 Bool.true 9665444 33554432 

noncomputable abbrev qz217 := (@HMul.hMul Real Real Real qz355 qz352 qz520)

noncomputable def Ns588p1564 := @Enclosure.Real.IsNear.cos_image qz217 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31255769)) qz381) Bool.true 31255769 16777216 

noncomputable def Ns588p1565 := nat_lit 1180809571659326122282986311605 

noncomputable def Ns588p1566 := nat_lit 167284381260024836553389412670064333 

noncomputable def Ns588p1567 := @Enclosure.Real.IsNear.recentre' qz217 Bool.true Ns588p1565 Ns588p929 Ns588p1566 

noncomputable abbrev qz218 := qz520

noncomputable def Ns588p1568 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz218 884279719003555 140737488355328 1 500000000000000 1335334901709511 

noncomputable abbrev qz521 := (@HSub.hSub Real Real Real qz592 qz710 qz703)

noncomputable abbrev qz219 := qz521

noncomputable def Ns588p1569 := @Enclosure.Real.IsNear.subLit_tf qz219 qz31 1053859924998855 4503599627370496 6198914763 4503599627370496 1 16 

noncomputable abbrev qz522 := qz710

noncomputable abbrev qz220 := qz522

noncomputable def Ns588p1570 := @Enclosure.Real.IsNear.subLit_ff_n qz220 qz205 1767535565800761 4503599627370496 3447451339 4503599627370496 42042069 67108864 41 67108864 

noncomputable def Ns588p1571 := @Enclosure.Real.IsNear.mulLit_ff qz205 qz205 42042069 67108864 41 67108864 42042069 67108864 41 67108864 1767535565800761 4503599627370496 

noncomputable def Ns588p1572 := nat_lit 120423612394569842487536310960574283360625680757918922086386650683331054977509609340552483745441 

noncomputable def Ns588p1573 := nat_lit 869285153124072013425267317645182838974291533277243462682328257513955408864357724559552161 

noncomputable def Ns588p1574 := nat_lit 727098170999337395256760600099476545377289725830548423301082311998639314159945114338402798186145 

noncomputable def Ns588p1575 := BSN.cos_dyadic_bound_t 31255769 16777216 4 3 33554432 10890000 Ns588p1572 Ns588p531 Ns588p1573 Ns588p1574 Ns588p534 Ns588p1573 9665444 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 31255769) (BSN.cosEvenQ 16777216) 0 3 Ns588p1572 Ns588p531 Ns588p1573 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 31255769) (BSN.cosOddQ 16777216) 0 3 Ns588p1574 Ns588p534 Ns588p1573 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1576 := @Ns588p1563 6394198864 730815528960000 2416361 8388608 399637429 45675970560000 (@Ns588p1564 581 67108864 Bool.true 9665444 33554432 1 10890000 (@Ns588p1567 Ns588p932 31255769 16777216 581 67108864 (@Ns588p1568 4503599627370496 6198914763 4503599627370496 Ns588p1565 Ns588p929 Ns588p1566 Ns588p932 RS589to600.d55 (@Ns588p1569 0 1 21365358427352176 1335334901709511 4503599627370496 6198914763 4503599627370496 (@Ns588p1570 70723342381798360350720 1053859924998855 4503599627370496 6198914763 4503599627370496 (@Ns588p1571 3447451339 4503599627370496 (Ns588p1553 rfl rfl) (Ns588p1553 rfl rfl) rfl) (Ns588p1553 rfl rfl) rfl rfl) qz388 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 31255769 16777216) (BSN.cos_neg_of_bound 31255769 16777216 Bool.true 9665444 33554432 1 10890000 (Ns588p1575 rfl rfl)) rfl rfl) 

noncomputable def Ns588p1577 := @Ns588p1538 2709092177935366337 649325391394576216883200 (Ns588p1539 qz33 (@Enclosure.Real.IsNear.of_eq qz708 (@Inv.inv Real Real.instInv (Real.sqrt qz212)) Bool.false 18885949 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz204 (BSN.t_div_two_pi_nonneg qz203 1001715 1000 qz206)) Ns588p1543) rfl) (@Ns588p1544 562949953421312 114587343372643 7740561859543040000 (BSN.correction_mk qz205 (BSN.cos_two_pi_p_ne_zero_mk qz203 1001715 1000 12 qz206 rfl rfl (@BSN.floor_sqrt_eq_dec qz203 1001715 1000 12 qz206 rfl rfl rfl))) (@Ns588p1545 67108864 2416361 8388608 399637429 45675970560000 231483983980073 562949953421312 114587343372643 7740561859543040000 Ns588p1562 (Ns588p1576 rfl) rfl)) 

noncomputable def Ns588p1578 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz203) (hardyZApproximantRS₀ qz203) Bool.true 38470288980267409738949 37778931862957161709568 629450291317229779137 649325391394576216883200 (@Eq.refl Real (hardyZApproximantRS₀ qz203)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz203) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz203) qz203 12) (@HMul.hMul Real Real Real qz5 qz704 (Zeta.RiemannSiegel.correction qz205))) Bool.true 38470288980267409738949 37778931862957161709568 629450291317229779137 649325391394576216883200 (BSN.hardyZApproximantRS₀_eq qz203 12 (@BSN.floor_sqrt_eq_dec qz203 1001715 1000 12 qz206 rfl rfl rfl)) (@Ns588p1457 38470288980267409738949 37778931862957161709568 629450291317229779137 649325391394576216883200 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz203) qz203 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz203) qz203 12)) Bool.true 121142187 134217728 259099 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz203) qz203 12) (Ns588p1537 (Ns588p1536 rfl rfl rfl rfl) rfl rfl)) (Ns588p1577 rfl) rfl rfl)) 

theorem RS589to600.d69 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz203) Bool.true 38470288980267409738949 37778931862957161709568 629450291317229779137 649325391394576216883200 := Ns588p1578 

noncomputable def Ns588p1579 := nat_lit 2496391536416185499476609 

noncomputable def Ns588p1580 := nat_lit 2571328549922521818857472000 

noncomputable def Ns588p1581 := nat_lit 3495036988356256330727865450496 

noncomputable abbrev qz789 := (Enclosure.sfrac Bool.false 1002953 1000)

noncomputable abbrev qz711 := qz789

noncomputable abbrev qz523 := qz711

noncomputable abbrev qz221 := qz523

noncomputable abbrev qz790 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 1002953 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz712 := qz790

noncomputable abbrev qz524 := qz712

noncomputable abbrev qz222 := qz524

noncomputable abbrev qz791 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 1002953 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz713 := qz791

noncomputable abbrev qz525 := qz713

noncomputable abbrev qz223 := qz525

noncomputable abbrev qz714 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz222 qz9))

noncomputable def Ns588p1582 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz221) qz221 12) (@HMul.hMul Real Real Real qz5 qz714 (Zeta.RiemannSiegel.correction qz223)) 216359177 268435456 64855 67108864 2204896191313817412187 18889465931478580854784 11421546382899396436609 Ns588p1580 Ns588p1581 

noncomputable def Ns588p1583 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.cos BSN.quadSignNeg 11 12 1002953 1000 286 536870912 268435456 9007199254740992 Bool.false 1096308807456 4568 1334074092 51 154981288 8 

noncomputable def Ns588p1584 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 1002953 1000 170 231 536870912 268435456 9007199254740992 Bool.false 1096308807456 4568 

noncomputable def Ns588p1585 := Ns588p1584 1236190956 51 169773496 8 1287360220 51 161872664 8 Bool.false 452114361 208886 Bool.true 169094826 Bool.true 47255414 28296951008113761 1 Bool.false 510460963 Bool.true Bool.false 47194418 Bool.false Bool.false 304922076 

noncomputable def Ns588p1586 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 1002953 1000 27 102 536870912 268435456 9007199254740992 Bool.false 1096308807456 4568 

noncomputable def Ns588p1587 := Ns588p1586 1116391676 51 189812536 8 1179625948 51 178956968 8 Bool.false 300176322 170594 Bool.true 610072036 Bool.true 782460602 28296951008113761 1 Bool.false 486996820 Bool.false Bool.false 60724026 Bool.true Bool.false 452114361 

noncomputable def Ns588p1588 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 1002953 1000 155 57 536870912 268435456 9007199254740992 Bool.false 1096308807456 4568 

noncomputable def Ns588p1589 := Ns588p1588 961943533 51 219176632 8 1044702541 51 202918136 8 Bool.false 232839781 126767 Bool.false 810852440 Bool.false 452313030 28296951008113761 1 Bool.false 535889775 Bool.false Bool.false 400671359 Bool.true Bool.false 300176322 

noncomputable def Ns588p1590 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 1002953 1000 414 272 536870912 268435456 9007199254740992 Bool.false 1096308807456 4568 

noncomputable def Ns588p1591 := Ns588p1590 744261104 50 268435448 8 864060384 50 240095976 8 Bool.false 95260481 74919 Bool.false 717549811 Bool.false 315212165 28296951008113761 1 Bool.false 124617956 Bool.true Bool.false 446963766 Bool.false Bool.false 232839781 

noncomputable def Ns588p1592 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 1002953 1000 857 598 536870912 268435456 9007199254740992 Bool.false 1096308807456 4568 

noncomputable def Ns588p1593 := Ns588p1592 372130544 50 379625064 8 589812976 50 309962568 8 Bool.false 536870672 4618 Bool.false 358529911 Bool.false 451829531 28296951008113761 1 Bool.false 332468624 Bool.true Bool.false 357702040 Bool.true Bool.false 95260481 

noncomputable def Ns588p1594 := nat_lit 336983873869872924041290554340063178008709416194432492660983 

noncomputable def Ns588p1595 := nat_lit 165023612382965351288217371909516444715904441069338624000 

noncomputable def Ns588p1596 := nat_lit 487129487490617748335366225596640000 

noncomputable def Ns588p1597 := nat_lit 2931408225190163663999551813601777267520 

noncomputable abbrev qz792 := (@Eq.refl Real (Enclosure.sfrac Bool.false 1002953 1000))

noncomputable abbrev qz715 := qz792

noncomputable abbrev qz526 := qz715

noncomputable abbrev qz224 := qz526

noncomputable def Ns588p1598 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz221 1002953 1000 4023659880836 16000000 2005906 4000 2000 Ns588p1596 Ns588p1597 qz224 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns588p1599 := nat_lit 107834839638359335693212977388820216962787013182218397651514560 

noncomputable abbrev qz716 := (@HSub.hSub Real Real Real qz743 qz744 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz745 (@Nat.cast Real Real.instNatCast 2005906))))

noncomputable abbrev qz527 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 1002953 4000) (Real.log (Enclosure.sfrac Bool.false 4023659880836 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz716))

noncomputable abbrev qz717 := (Enclosure.sfrac Bool.false 1002953 2000)

noncomputable abbrev qz225 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz527 qz717) (@HMul.hMul Real Real Real qz355 qz717 (Real.log Real.pi)))

noncomputable def Ns588p1600 := @Enclosure.Real.IsNear.addLit_ft_p qz225 (Enclosure.sfrac Bool.true Ns588p1596 Ns588p1597) 36786022324375747523103 18014398509481984000 151756214229376650719 Ns588p1086 Ns588p1596 Ns588p1597 0 1 Ns588p1599 

noncomputable def Ns588p1601 := nat_lit 2468668169267495925426256084992000 

noncomputable abbrev qz226 := (@HSub.hSub Real Real Real qz359 qz527 qz717)

noncomputable def Ns588p1602 := @Enclosure.Real.IsNear.subLit_ff_p qz226 (@HMul.hMul Real Real Real qz5 qz717 (Real.log Real.pi)) 47127280291074005496351 18014398509481984000 12636931068213389 4356000000000000000000 38524187977233 67108864000 3008859 536870912000 Ns588p1601 36786022324375747523103 18014398509481984000 

noncomputable def Ns588p1603 := nat_lit 94254560582148010992702000 

noncomputable abbrev qz227 := qz527

noncomputable def Ns588p1604 := @Enclosure.Real.IsNear.subLit_ff_p qz227 qz717 56161077805214247645727 18014398509481984000 12636931068213389 4356000000000000000000 1002953 2000 0 1 Ns588p1603 47127280291074005496351 18014398509481984000 12636931068213389 4356000000000000000000 

noncomputable def Ns588p1605 := nat_lit 126463504538144159517451201619790135296 

noncomputable def Ns588p1606 := nat_lit 120265040564631014035423232 

noncomputable def Ns588p1607 := nat_lit 133737295842090136563321443874511054627283442370899495818793878745114657946256904978734143663558991011010626644372293918490059184859975074503558901386091879267239231564020843218029363831892722167216759664069836800 

noncomputable def Ns588p1608 := nat_lit 4698894521187936759359098681036522286848079933315238252957813038852983716921328304743070409501221306596875199423697031737660501143688456788507284610695028535672458002012492701628196131319507043337568399109652480 

noncomputable def Ns588p1609 := nat_lit 72977964190236481815471363303270761740730122792906088131782662900267903712124602322186214473727108060361152345203711122058760885707423794837257692310599495256870041332640196916028832873621469067109990400 

noncomputable def Ns588p1610 := BSN.log_dyadic_bound 1926507880836 6120811880836 9 8 Ns588p1607 268435456 87120000 Ns588p1608 Ns588p1609 174915676 8047319761672 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1926507880836) (BSN.artanhQ 6120811880836) 0 8 Ns588p1608 Ns588p1607 Ns588p1609 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz528 := (Real.log (Enclosure.sfrac Bool.false 4023659880836 16000000))

noncomputable def Ns588p1611 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1002953 4000) qz528 1002953 4000 0 1 56002773607443559 4503599627370496 12500018513 1089000000000000000 56168149797906339829727 18014398509481984000 12536931067668889 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 1002953 4000) (BSN.isNear_log_sfrac 4023659880836 16000000 56002773607443559 4503599627370496 12500018513 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4023659880836) qz362)) Bool.false Ns588p1606 Ns588p114 1000001481040000 87120000000000000000000 56002773607443559 4503599627370496 12500018513 1089000000000000000 (BSN.log_rat_reduce_isNear 4023659880836 16000000 17 8047319761672 4194304000000 174915676 268435456 24973259072661432 36028797018963968 87120000 1000000000000000 rfl rfl rfl rfl (Ns588p1610 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p1612 := BSN.arctan_dyadic_bound_f 1000 2005906 1 0 33554432 10890000 0 1 1 0 1 1 16727 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 2005906) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 2005906) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns588p1613 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 2005906))) 884279719003555 562949953421312 1 2000000000000000 16727 33554432 1 10890000 29662087236413015719936 883999086511523 562949953421312 200000001089 2178000000000000000 qz17 (Ns588p1612 rfl) rfl rfl 

noncomputable abbrev qz529 := (@HMul.hMul Real Real Real qz588 qz593 qz716)

noncomputable abbrev qz228 := qz529

noncomputable abbrev qz530 := qz716

noncomputable abbrev qz229 := qz530

noncomputable def Ns588p1614 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 1002953 4000) qz528) qz228 56168149797906339829727 18014398509481984000 12536931067668889 4356000000000000000000 883999086511523 2251799813685248 200000001089 8712000000000000000 Ns588p1605 56161077805214247645727 18014398509481984000 12636931068213389 4356000000000000000000 (Ns588p1611 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz229 1 4 0 1 883999086511523 562949953421312 200000001089 2178000000000000000 883999086511523 2251799813685248 200000001089 8712000000000000000 qz369 Ns588p1613 rfl) 

noncomputable def Ns588p1615 := @Ns588p1600 Ns588p1594 Ns588p1595 151756214229376650719 Ns588p1086 (@Ns588p1602 151756214229376650719 Ns588p1086 (Ns588p1604 (Ns588p1614 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1002953 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz717 (Real.log Real.pi) 1002953 2000 0 1 38410761 33554432 3 268435456 38524187977233 67108864000 3008859 536870912000 (Enclosure.Real.IsNear.const Bool.false 1002953 2000) RS589to600.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns588p1596 Ns588p1597) 

noncomputable def Ns588p1616 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz221) Bool.false Ns588p1594 Ns588p1595 151756214229376650719 Ns588p1086 34259650233 16777216 571 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz221) (@HAdd.hAdd Real Real Real qz370 qz225 (Enclosure.sfrac Bool.true Ns588p1596 Ns588p1597)) Bool.false Ns588p1594 Ns588p1595 151756214229376650719 Ns588p1086 Ns588p1598 (Ns588p1615 rfl rfl)) 

noncomputable def Ns588p1617 := nat_lit 3795673488230822713491456 

noncomputable def Ns588p1618 := nat_lit 14345827876445295707693635962431562045488181167840439293652971614472169634484334071962425190029281336194408247711870258716714759251304000000000 

noncomputable def Ns588p1619 := nat_lit 10177203221323789076855003797116526916596039623537796740847662493512781482165002201313899314022576219845355693143476806640625000000000000 

noncomputable def Ns588p1620 := nat_lit 71640220489585182389978519038377597935597091815371088164182968408966802429116625013572036883842666476371261964491822218744148833756520000000000 

noncomputable def Ns588p1621 := BSN.sin_dyadic_bound_f 215759057950 137438953472 4 3 67108864 21801270 Ns588p1618 Ns588p127 Ns588p1619 Ns588p1620 Ns588p130 Ns588p1619 67108834 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215759057950) (BSN.sinEvenQ 137438953472) 0 3 Ns588p1618 Ns588p127 Ns588p1619 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215759057950) (BSN.sinOddQ 137438953472) 0 3 Ns588p1620 Ns588p130 Ns588p1619 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1622 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz221) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 34259650233) qz381) Bool.false 34259650233 16777216 571 67108864 Bool.false 67108834 67108864 1 10890000 (Ns588p1616 rfl) (Enclosure.sfrac_false_div 34259650233 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 34259650233) qz381) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns588p1617) (@Nat.cast Real Real.instNatCast Ns588p211)) 226375608064910080 72057594037927936 Bool.false 67108834 67108864 324 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q3 34259650233 16777216 226375608064910080 72057594037927936 324 Ns588p1617 Ns588p211 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108834 67108864 Ns588p1617 Ns588p211 215759057950 137438953472 21801270 21780000 (Ns588p1621 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p1623 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz221) Bool.false Ns588p1594 Ns588p1595 151756214229376650719 Ns588p1086 1096308807456 536870912 4568 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz221) (@HAdd.hAdd Real Real Real qz370 qz225 (Enclosure.sfrac Bool.true Ns588p1596 Ns588p1597)) Bool.false Ns588p1594 Ns588p1595 151756214229376650719 Ns588p1086 Ns588p1598 (Ns588p1615 rfl rfl)) 

noncomputable def Ns588p1624 := Ns588p1593 74919 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 857 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 332468624 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 598 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 357702040 536870912) qz224 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 1) Bool.false 33554417 33554432 392831179 45675970560000 536870672 536870912 4618 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz221)) Bool.false 33554417 33554432 392831179 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz221) qz221) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz221)) Bool.false 67108834 67108864 6285298864 730815528960000 33554417 33554432 392831179 45675970560000 (Ns588p1622 rfl rfl) rfl)) rfl) (Ns588p1623 rfl) RS589to600.d7 

noncomputable def Ns588p1625 := nat_lit 4151369789352905692812074483850912039124948631760221800097213799489002305 

noncomputable def Ns588p1626 := nat_lit 273025459368093639243619108161359867188908668283223733474133906742081 

noncomputable def Ns588p1627 := nat_lit 10872193121371014186710943502958222662685131040575741399924220877098376001 

noncomputable def Ns588p1628 := BSN.sin_dyadic_bound_f 358529911 536870912 3 2 536870912 268435456 Ns588p1625 Ns588p136 Ns588p1626 Ns588p1627 Ns588p139 Ns588p1626 332468624 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 358529911) qz373 0 2 Ns588p1625 Ns588p136 Ns588p1626 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 358529911) qz374 0 2 Ns588p1627 Ns588p139 Ns588p1626 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1629 := nat_lit 5818578467168645271850207647876314014904010533741878925969159571397943521 

noncomputable def Ns588p1630 := nat_lit 1736988325642349691750437305919180003664606351067308356760587146633441 

noncomputable def Ns588p1631 := nat_lit 17452261424854651116167122069017103684704702388523502161193957539900563681 

noncomputable def Ns588p1632 := BSN.cos_dyadic_bound_f 451829531 536870912 3 2 536870912 268435456 Ns588p1629 Ns588p152 Ns588p1630 Ns588p1631 Ns588p155 Ns588p1630 357702040 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 451829531) qz375 0 2 Ns588p1629 Ns588p152 Ns588p1630 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 451829531) qz376 0 2 Ns588p1631 Ns588p155 Ns588p1630 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1633 := nat_lit 36586197741056231306446682379129091670810533988490810939206278405267963493591563542411204448678765989917041210801 

noncomputable def Ns588p1634 := nat_lit 18630506095118673972893055410395772169783196115712456609805261907085573045414172441060141421594399962150321 

noncomputable def Ns588p1635 := nat_lit 221675647110519153633110537061128630973406869061265377577853931897050266314623681339345883129995221197490497631665 

noncomputable def Ns588p1636 := BSN.cos_dyadic_bound_f 717549811 536870912 4 3 536870912 268435456 Ns588p1633 Ns588p146 Ns588p1634 Ns588p1635 Ns588p149 Ns588p1634 124617956 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 717549811) qz375 0 3 Ns588p1633 Ns588p146 Ns588p1634 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 717549811) qz376 0 3 Ns588p1635 Ns588p149 Ns588p1634 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1637 := nat_lit 1377943391322736363290554144893299156313610047524067673326841749949190625 

noncomputable def Ns588p1638 := nat_lit 97459405783200167283622464827419648608612756077519861816694000390625 

noncomputable def Ns588p1639 := nat_lit 4133635255156642689537095189750242629643612917060047980256891861846790625 

noncomputable def Ns588p1640 := BSN.cos_dyadic_bound_f 315212165 536870912 3 2 536870912 268435456 Ns588p1637 Ns588p152 Ns588p1638 Ns588p1639 Ns588p155 Ns588p1638 446963766 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 315212165) qz375 0 2 Ns588p1637 Ns588p152 Ns588p1638 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 315212165) qz376 0 2 Ns588p1639 Ns588p155 Ns588p1638 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1641 := Ns588p1591 126767 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 414 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 124617956 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 272 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 446963766 536870912) qz224 rfl rfl (Ns588p1624 RS589to600.d9 RS589to600.d11 RS589to600.d13 RS589to600.d17 (Ns588p1628 rfl rfl) (Ns588p1632 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns588p1623 rfl) RS589to600.d19 RS589to600.d21 RS589to600.d23 RS589to600.d25 RS589to600.d17 (Ns588p1636 rfl rfl) (Ns588p1640 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns588p1642 := nat_lit 155085877636999688659661894150290795761913317468641902965081988832192062904046579467903287082207558662252134400000 

noncomputable def Ns588p1643 := nat_lit 80779644023209660845873521656462732103439624940953565134179487766672388955358485737282612494336000000000000 

noncomputable def Ns588p1644 := nat_lit 774605652224884742085421241194378960527714869743491794097635616639568415907381698520495333951485241481756672000000 

noncomputable def Ns588p1645 := BSN.sin_dyadic_bound_f 810852440 536870912 4 3 536870912 268435456 Ns588p1642 Ns588p172 Ns588p1643 Ns588p1644 Ns588p175 Ns588p1643 535889775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 810852440) qz373 0 3 Ns588p1642 Ns588p172 Ns588p1643 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 810852440) qz374 0 3 Ns588p1644 Ns588p175 Ns588p1643 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1646 := nat_lit 10516955348777147286430589977342985004948182760346910365810425740295840000 

noncomputable def Ns588p1647 := nat_lit 1751914030884363313018066010520057287273040326765834361511136100000000 

noncomputable def Ns588p1648 := nat_lit 27541570433604430114335230214738404444018227068950953892918192242327200000 

noncomputable def Ns588p1649 := BSN.sin_dyadic_bound_f 452313030 536870912 3 2 536870912 268435456 Ns588p1646 Ns588p136 Ns588p1647 Ns588p1648 Ns588p139 Ns588p1647 400671359 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 452313030) qz373 0 2 Ns588p1646 Ns588p136 Ns588p1647 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 452313030) qz374 0 2 Ns588p1648 Ns588p139 Ns588p1647 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1650 := Ns588p1589 170594 BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 535889775 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 400671359 536870912) qz224 rfl rfl (Ns588p1641 rfl rfl) (Ns588p1623 rfl) RS589to600.d27 RS589to600.d29 RS589to600.d31 RS589to600.d33 RS589to600.d17 (Ns588p1645 rfl rfl) (Ns588p1649 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1651 := nat_lit 34819710845316301965661178705683119992218259567736095207986282317578567680 

noncomputable def Ns588p1652 := nat_lit 19188850037096759010426686809382569798770994662120129407990011181203456 

noncomputable def Ns588p1653 := nat_lit 91163413123387396109762396260050123438040288686046340573303517480317157376 

noncomputable def Ns588p1654 := BSN.sin_dyadic_bound_f 610072036 536870912 3 2 536870912 268435456 Ns588p1651 Ns588p136 Ns588p1652 Ns588p1653 Ns588p139 Ns588p1652 486996820 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 610072036) qz373 0 2 Ns588p1651 Ns588p136 Ns588p1652 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 610072036) qz374 0 2 Ns588p1653 Ns588p139 Ns588p1652 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1655 := nat_lit 51772591805071973236420856808104610016079660282556664665205722878047492055668395662599811110989596169368741810176 

noncomputable def Ns588p1656 := nat_lit 52668354871967611969798598853692796380286704234317814715841211566376945750172857770656256407086074689949696 

noncomputable def Ns588p1657 := nat_lit 313525929865776553476081333210009891870694726829958040182087708898621429610063986654959540709760323542351130071040 

noncomputable def Ns588p1658 := BSN.cos_dyadic_bound_f 782460602 536870912 4 3 536870912 268435456 Ns588p1655 Ns588p146 Ns588p1656 Ns588p1657 Ns588p149 Ns588p1656 60724026 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 782460602) qz375 0 3 Ns588p1655 Ns588p146 Ns588p1656 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 782460602) qz376 0 3 Ns588p1657 Ns588p149 Ns588p1656 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1659 := Ns588p1587 208886 BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 486996820 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 102 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 60724026 536870912) qz224 rfl rfl (Ns588p1650 rfl) (Ns588p1623 rfl) RS589to600.d35 RS589to600.d37 RS589to600.d39 RS589to600.d41 RS589to600.d17 (Ns588p1654 rfl rfl) (Ns588p1658 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1660 := nat_lit 114107081965551219400748322624209872687957755801298215593600474509107456 

noncomputable def Ns588p1661 := nat_lit 668409406874987558389589676348520593359082317624588503967973662976 

noncomputable def Ns588p1662 := nat_lit 342319909077839908227128188693276921022686549239259397603793487579996416 

noncomputable def Ns588p1663 := BSN.cos_dyadic_bound_f 169094826 536870912 3 2 536870912 268435456 Ns588p1660 Ns588p152 Ns588p1661 Ns588p1662 Ns588p155 Ns588p1661 510460963 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 169094826) qz375 0 2 Ns588p1660 Ns588p152 Ns588p1661 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 169094826) qz376 0 2 Ns588p1662 Ns588p155 Ns588p1661 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1664 := nat_lit 4986620169721259821369351468816 

noncomputable def Ns588p1665 := BSN.sin_dyadic_bound_f 47255414 536870912 2 1 536870912 268435456 Ns588p1664 Ns588p188 Ns588p1664 Ns588p1664 Ns588p189 Ns588p1664 47194418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 47255414) qz373 0 1 Ns588p1664 Ns588p188 Ns588p1664 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 47255414) qz374 0 1 Ns588p1664 Ns588p189 Ns588p1664 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1666 := Ns588p1585 243325 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 170 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 510460963 536870912) BSN.abs_quadSignPos qz634 (BSN.sfrac_eq_quadSignPos_mul Bool.false 47194418 536870912) qz224 rfl rfl (Ns588p1659 rfl) (Ns588p1623 rfl) RS589to600.d43 RS589to600.d45 RS589to600.d47 RS589to600.d49 RS589to600.d17 (Ns588p1663 rfl rfl) (Ns588p1665 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1667 := nat_lit 9827655366030258970003654121822598133897091830411384944509562085189571043142471505821023013653540408001606274241 

noncomputable def Ns588p1668 := nat_lit 362601883710155741171440528376164809194424070992812156346868847336275159562049816094467189643691177888961 

noncomputable def Ns588p1669 := nat_lit 59600809931738365430898192446962424928269650259093498186322568086693317240005924145352679840513560281098011364545 

noncomputable def Ns588p1670 := BSN.cos_dyadic_bound_f 516756369 536870912 4 3 536870912 268435456 Ns588p1667 Ns588p146 Ns588p1668 Ns588p1669 Ns588p149 Ns588p1668 306790869 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 516756369) qz375 0 3 Ns588p1667 Ns588p146 Ns588p1668 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 516756369) qz376 0 3 Ns588p1669 Ns588p149 Ns588p1668 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1671 := Ns588p1583 Bool.false 304922076 243325 Bool.true 516756369 28296951008113761 1 Bool.false 306790869 Bool.true Bool.false 216359177 259420 BSN.abs_quadSignNeg qz398 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 306790869 536870912) qz224 rfl (Ns588p1666 rfl) (Ns588p1623 rfl) RS589to600.d51 RS589to600.d53 RS589to600.d17 (Ns588p1670 rfl rfl) rfl 

noncomputable def Ns588p1672 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 12) 216359177 536870912 259420 536870912 216359177 536870912 259420 536870912 232313897351118848 216359177 268435456 64855 67108864 (Ns588p1671 rfl rfl rfl rfl) 

noncomputable def Ns588p1673 := @Enclosure.Real.IsNear.mulLit_ff qz714 (Zeta.RiemannSiegel.correction qz223) 9440059 33554432 1 33554432 233568051991393 562949953421312 6032669247770707 383157812047380480000 2204896191313817412187 18889465931478580854784 

noncomputable abbrev qz718 := (@HPow.hPow Real Real Real qz7 qz222 qz9)

noncomputable def Ns588p1674 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz718 1 1 0 1 9440059 33554432 1 33554432 9440059 33554432 1 33554432 

noncomputable def Ns588p1675 := @Enclosure.Real.IsNear.sqrt_image qz222 10712247127771 67108864000 1002953 67108864000 423935923 423935964 33554432 (@Enclosure.Real.IsNear.of_eq qz222 (@HMul.hMul Real Real Real qz5 qz221 qz3) Bool.false 10712247127771 67108864000 1002953 67108864000 (BSN.t_div_two_pi_mk qz221 1002953 1000 qz224) (@Enclosure.Real.IsNear.mulLit_ff qz221 qz3 1002953 1000 0 1 10680707 67108864 1 67108864 10712247127771 67108864000 1002953 67108864000 (Enclosure.Real.IsNear.const Bool.false 1002953 1000) RS589to600.d56 rfl)) 

noncomputable abbrev qz793 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 1002953 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz719 := qz793

noncomputable abbrev qz531 := qz719

noncomputable abbrev qz230 := qz531

noncomputable def Ns588p1676 := @Enclosure.Real.IsNear.sqrt_image qz230 847871887 67108864 41 67108864 119268307 119268313 33554432 (@Enclosure.Real.IsNear.recentre' qz230 Bool.false 847871887 67108864 41 67108864 847871887 67108864 41 67108864 (Ns588p1675 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns588p1677 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz230) 59634155 16777216 3 33554432 9440058 9440060 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz230) Bool.false 238536620 67108864 6 67108864 59634155 16777216 3 33554432 (Ns588p1676 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns588p1678 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz230)) Bool.false 18880118 67108864 2 67108864 9440059 33554432 1 33554432 (Ns588p1677 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz532 := (@HMul.hMul Real Real Real qz588 qz586 qz713)

noncomputable abbrev qz231 := (Real.cos qz532)

noncomputable abbrev qz720 := (@HMul.hMul Real Real Real qz739 qz791 qz791)

noncomputable abbrev qz533 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz720 qz713) qz603)

noncomputable abbrev qz232 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz533))

noncomputable def Ns588p1679 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz223) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz231) qz232) Bool.false 233568051991393 

noncomputable def Ns588p1680 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz231) qz232 100958263 67108864 601 

noncomputable abbrev qz233 := (@Neg.neg Real Real.instNeg (Real.cos qz532))

noncomputable def Ns588p1681 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz231) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz233)) Bool.true 100958263 67108864 601 67108864 (BSN.inv_eq_neg_inv_neg qz231) 

noncomputable def Ns588p1682 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz233) Bool.false 100958263 67108864 601 67108864 100958263 67108864 

noncomputable def Ns588p1683 := @Enclosure.Real.IsNear.recentre' qz231 Bool.true 44608529 67108864 2887618864 730815528960000 44608529 67108864 180476179 45675970560000 

noncomputable abbrev qz234 := qz532

noncomputable def Ns588p1684 := @Enclosure.Real.IsNear.cos_image qz234 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 267447043) qz371) Bool.false 267447043 67108864 259 67108864 Bool.true 44608529 67108864 1 

noncomputable def Ns588p1685 := nat_lit 221285818427288177549292179 

noncomputable def Ns588p1686 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz223 884279719003555 140737488355328 1 500000000000000 42565519 67108864 41 67108864 37639825180560481420045 9444732965739290427392 Ns588p1685 

noncomputable def Ns588p1687 := @Enclosure.Real.IsNear.subLit_ff_p qz230 qz1 847871887 67108864 41 67108864 12 1 0 1 42565519 42565519 67108864 41 

noncomputable def Ns588p1688 := @Ns588p1687 67108864 (@Enclosure.Real.IsNear.recentre' qz230 Bool.false 847871887 67108864 41 67108864 847871887 67108864 41 67108864 (Ns588p1675 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns588p1689 := @Enclosure.Real.IsNear.recentre' qz234 Bool.false 37639825180560481420045 9444732965739290427392 Ns588p1685 Ns588p1297 267447043 67108864 259 67108864 (@Ns588p1686 Ns588p1297 RS589to600.d55 (Ns588p1688 rfl rfl) rfl) 

noncomputable def Ns588p1690 := nat_lit 8159561113185805198688256 

noncomputable def Ns588p1691 := nat_lit 108399577569977870943527061728794756873763500621145309092704378099145247920676105245264110721 

noncomputable def Ns588p1692 := nat_lit 32681049285000106246567515168847031667348613537260645200510424228497136635564527101863041 

noncomputable def Ns588p1693 := nat_lit 325133370611363612618088050156046576557955804636361405987712113448978749488757186681588606081 

noncomputable def Ns588p1694 := BSN.cos_dyadic_bound_f 115954337519 137438953472 3 2 67108864 21801270 Ns588p1691 Ns588p511 Ns588p1692 Ns588p1693 Ns588p514 Ns588p1692 44608529 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 115954337519) qz383 0 2 Ns588p1691 Ns588p511 Ns588p1692 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 115954337519) qz384 0 2 Ns588p1693 Ns588p514 Ns588p1692 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1695 := @Ns588p1684 10890000 (Ns588p1689 rfl) (Enclosure.sfrac_false_div 267447043 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 267447043) qz371) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns588p1690) qz372) 226375608064910080 72057594037927936 Bool.false 44608529 67108864 0 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 267447043 67108864 226375608064910080 72057594037927936 0 Ns588p1690 Ns588p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 44608529 67108864 Ns588p1690 Ns588p114 115954337519 137438953472 21801270 21780000 (Ns588p1694 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p1696 := @Enclosure.Real.IsNear.inv_image qz233 44608529 67108864 180476179 45675970560000 50478831 50479432 33554432 (@Enclosure.Real.IsNear.neg qz231 Bool.true 44608529 67108864 180476179 45675970560000 (Ns588p1683 (Ns588p1695 rfl rfl) rfl)) 

noncomputable def Ns588p1697 := Ns588p1681 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz233) Bool.false 100958263 67108864 601 67108864 (@Ns588p1682 601 67108864 (Ns588p1696 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p1698 := @Enclosure.Real.IsNear.recentre' qz232 Bool.true 9254044 33554432 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz355 qz352 qz533)

noncomputable def Ns588p1699 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 62082741)) qz397) Bool.true 62082741 33554432 

noncomputable def Ns588p1700 := nat_lit 1172709828458414264386124732605 

noncomputable def Ns588p1701 := nat_lit 168442701876121011927376903268451033 

noncomputable def Ns588p1702 := @Enclosure.Real.IsNear.recentre' qz235 Bool.true Ns588p1700 Ns588p929 Ns588p1701 

noncomputable abbrev qz236 := qz533

noncomputable def Ns588p1703 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz236 884279719003555 140737488355328 1 500000000000000 1326175194631711 

noncomputable abbrev qz534 := (@HSub.hSub Real Real Real qz592 qz720 qz713)

noncomputable abbrev qz237 := qz534

noncomputable def Ns588p1704 := @Enclosure.Real.IsNear.subLit_tf qz237 qz31 1044700217921055 4503599627370496 6241837663 4503599627370496 1 16 

noncomputable abbrev qz535 := qz720

noncomputable abbrev qz238 := qz535

noncomputable def Ns588p1705 := @Enclosure.Real.IsNear.subLit_ff_n qz238 qz223 1811823407739361 4503599627370496 3490374239 4503599627370496 42565519 67108864 41 67108864 

noncomputable def Ns588p1706 := @Enclosure.Real.IsNear.mulLit_ff qz223 qz223 42565519 67108864 41 67108864 42565519 67108864 41 67108864 1811823407739361 4503599627370496 

noncomputable def Ns588p1707 := nat_lit 479766870069304340951399647343191857026731560611245189763200862389393425800787862689795912680297361 

noncomputable def Ns588p1708 := nat_lit 3278314368982196877304460192028586276204327716053814313565161332131971980170944798449512174481 

noncomputable def Ns588p1709 := nat_lit 2897127747504000658797315713744826740206882842129039158223089101944935831724537891735124670264595345 

noncomputable def Ns588p1710 := BSN.cos_dyadic_bound_t 62082741 33554432 4 3 33554432 10890000 Ns588p1707 Ns588p361 Ns588p1708 Ns588p1709 Ns588p364 Ns588p1708 9254044 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 62082741) (BSN.cosEvenQ 33554432) 0 3 Ns588p1707 Ns588p361 Ns588p1708 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 62082741) (BSN.cosOddQ 33554432) 0 3 Ns588p1709 Ns588p364 Ns588p1708 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1711 := @Ns588p1698 3224324432 365407764480000 2313511 8388608 201520277 22837985280000 (@Ns588p1699 293 33554432 Bool.true 9254044 33554432 1 10890000 (@Ns588p1702 Ns588p932 62082741 33554432 293 33554432 (@Ns588p1703 4503599627370496 6241837663 4503599627370496 Ns588p1700 Ns588p929 Ns588p1701 Ns588p932 RS589to600.d55 (@Ns588p1704 0 1 21218803114107376 1326175194631711 4503599627370496 6241837663 4503599627370496 (@Ns588p1705 70108644845234442731520 1044700217921055 4503599627370496 6241837663 4503599627370496 (@Ns588p1706 3490374239 4503599627370496 (Ns588p1688 rfl rfl) (Ns588p1688 rfl rfl) rfl) (Ns588p1688 rfl rfl) rfl rfl) qz388 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 62082741 33554432) (BSN.cos_neg_of_bound 62082741 33554432 Bool.true 9254044 33554432 1 10890000 (Ns588p1710 rfl rfl)) rfl rfl) 

noncomputable def Ns588p1712 := @Ns588p1673 11421546382899396436609 Ns588p1580 (Ns588p1674 qz33 (@Enclosure.Real.IsNear.of_eq qz718 (@Inv.inv Real Real.instInv (Real.sqrt qz230)) Bool.false 9440059 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz222 (BSN.t_div_two_pi_nonneg qz221 1002953 1000 qz224)) Ns588p1678) rfl) (@Ns588p1679 562949953421312 6032669247770707 383157812047380480000 (BSN.correction_mk qz223 (BSN.cos_two_pi_p_ne_zero_mk qz221 1002953 1000 12 qz224 rfl rfl (@BSN.floor_sqrt_eq_dec qz221 1002953 1000 12 qz224 rfl rfl rfl))) (@Ns588p1680 67108864 2313511 8388608 201520277 22837985280000 233568051991393 562949953421312 6032669247770707 383157812047380480000 Ns588p1697 (Ns588p1711 rfl) rfl)) 

noncomputable def Ns588p1713 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz221) (hardyZApproximantRS₀ qz221) Bool.false 13020027385489107410341 18889465931478580854784 Ns588p1579 Ns588p1580 (@Eq.refl Real (hardyZApproximantRS₀ qz221)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz221) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz221) qz221 12) (@HMul.hMul Real Real Real qz5 qz714 (Zeta.RiemannSiegel.correction qz223))) Bool.false 13020027385489107410341 18889465931478580854784 Ns588p1579 Ns588p1580 (BSN.hardyZApproximantRS₀_eq qz221 12 (@BSN.floor_sqrt_eq_dec qz221 1002953 1000 12 qz224 rfl rfl rfl)) (@Ns588p1582 13020027385489107410341 18889465931478580854784 Ns588p1579 Ns588p1580 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz221) qz221 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 12)) Bool.false 216359177 268435456 64855 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz221) qz221 12) (Ns588p1672 (Ns588p1671 rfl rfl rfl rfl) rfl rfl)) (Ns588p1712 rfl) rfl rfl)) 

theorem RS589to600.d70 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz221) Bool.false 13020027385489107410341 18889465931478580854784 Ns588p1579 Ns588p1580 := Ns588p1713 

noncomputable def Ns588p1714 := nat_lit 25002839817510061472714191 

noncomputable def Ns588p1715 := nat_lit 25713285499225218188574720000 

noncomputable def Ns588p1716 := nat_lit 289131152733224888933323636736 

noncomputable abbrev qz794 := (Enclosure.sfrac Bool.false 1004192 1000)

noncomputable abbrev qz721 := qz794

noncomputable abbrev qz536 := qz721

noncomputable abbrev qz239 := qz536

noncomputable abbrev qz795 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 1004192 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz722 := qz795

noncomputable abbrev qz537 := qz722

noncomputable abbrev qz240 := qz537

noncomputable abbrev qz796 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 1004192 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz723 := qz796

noncomputable abbrev qz538 := qz723

noncomputable abbrev qz241 := qz538

noncomputable abbrev qz724 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz240 qz9))

noncomputable def Ns588p1717 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz239) qz239 12) (@HMul.hMul Real Real Real qz5 qz724 (Zeta.RiemannSiegel.correction qz241)) 114546439 67108864 259747 268435456 278145381814073156151 2361183241434822606848 121816766042327088074191 Ns588p1715 Ns588p1716 

noncomputable def Ns588p1718 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.cos BSN.quadSignNeg 11 12 1004192 1000 286 536870912 268435456 9007199254740992 Bool.false 1097996192006 4573 1334074092 51 154981288 8 

noncomputable def Ns588p1719 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 1004192 1000 170 230 536870912 268435456 9007199254740992 Bool.false 1097996192006 4573 

noncomputable def Ns588p1720 := Ns588p1719 1236190956 51 169773496 8 1287360220 51 161872664 8 Bool.true 178345654 209151 Bool.true 13350871 Bool.true 798225033 28296951008113761 1 Bool.false 536704916 Bool.true Bool.false 45036833 Bool.true Bool.true 361645773 

noncomputable def Ns588p1721 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 1004192 1000 27 102 536870912 268435456 9007199254740992 Bool.false 1097996192006 4573 

noncomputable def Ns588p1722 := Ns588p1721 1116391676 51 189812536 8 1179625948 51 178956968 8 Bool.true 189655310 170812 Bool.true 305896773 Bool.true 556632601 28296951008113761 1 Bool.false 289612012 Bool.false Bool.false 273250970 Bool.true Bool.true 178345654 

noncomputable def Ns588p1723 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 1004192 1000 156 58 536870912 268435456 9007199254740992 Bool.false 1097996192006 4573 

noncomputable def Ns588p1724 := Ns588p1723 961943533 51 219176632 8 1044702541 51 202918136 8 Bool.true 129314812 126932 Bool.false 463074096 Bool.false 1996275 28296951008113761 1 Bool.false 349239027 Bool.false Bool.false 536867200 Bool.true Bool.true 189655310 

noncomputable def Ns588p1725 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 1004192 1000 415 273 536870912 268435456 9007199254740992 Bool.false 1097996192006 4573 

noncomputable def Ns588p1726 := Ns588p1725 744261104 50 268435448 8 864060384 50 240095976 8 Bool.true 339141464 75021 Bool.false 639479996 Bool.false 88711042 28296951008113761 1 Bool.false 498638316 Bool.false Bool.false 88307908 Bool.true Bool.true 129314812 

noncomputable def Ns588p1727 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 1004192 1000 858 599 536870912 268435456 9007199254740992 Bool.false 1097996192006 4573 

noncomputable def Ns588p1728 := Ns588p1727 372130544 50 379625064 8 589812976 50 309962568 8 Bool.true 536870848 4634 Bool.false 741529860 Bool.false 565120947 28296951008113761 1 Bool.false 101176329 Bool.true Bool.false 466392527 Bool.false Bool.true 339141464 

noncomputable def Ns588p1729 := nat_lit 2594084835384833165075596761806766632471520497158541221 

noncomputable def Ns588p1730 := nat_lit 1268391185249378424048693691707910052865650982912000 

noncomputable def Ns588p1731 := nat_lit 490145811922229717371343159951360000 

noncomputable def Ns588p1732 := nat_lit 2953203360665073674285536845465912606720 

noncomputable abbrev qz797 := (@Eq.refl Real (Enclosure.sfrac Bool.false 1004192 1000))

noncomputable abbrev qz725 := qz797

noncomputable abbrev qz539 := qz725

noncomputable abbrev qz242 := qz539

noncomputable def Ns588p1733 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz239 1004192 1000 4033607291456 16000000 2008384 4000 2000 Ns588p1731 Ns588p1732 qz242 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns588p1734 := nat_lit 3400118875435608526127886187635365160513071346035643149189120 

noncomputable abbrev qz726 := (@HSub.hSub Real Real Real qz743 qz744 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz745 (@Nat.cast Real Real.instNatCast 2008384))))

noncomputable abbrev qz540 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 1004192 4000) (Real.log (Enclosure.sfrac Bool.false 4033607291456 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz726))

noncomputable abbrev qz727 := (Enclosure.sfrac Bool.false 1004192 2000)

noncomputable abbrev qz243 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz540 qz727) (@HMul.hMul Real Real Real qz355 qz727 (Real.log Real.pi)))

noncomputable def Ns588p1735 := @Enclosure.Real.IsNear.addLit_ft_p qz243 (Enclosure.sfrac Bool.true Ns588p1731 Ns588p1732) 1151332548462713908421 562949953421312000 4748224392899749363 557568000000000000000000 Ns588p1731 Ns588p1732 0 1 Ns588p1734 

noncomputable def Ns588p1736 := nat_lit 2414519356673677398472916992000 

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz359 qz540 qz727)

noncomputable def Ns588p1737 := @Enclosure.Real.IsNear.subLit_ff_p qz244 (@HMul.hMul Real Real Real qz5 qz727 (Real.log Real.pi)) 1474896081602310712517 562949953421312000 3163104647787749 1089000000000000000000 1205368090941 2097152000 94143 16777216000 Ns588p1736 1151332548462713908421 562949953421312000 

noncomputable def Ns588p1738 := nat_lit 2949792163204621425034000 

noncomputable abbrev qz245 := qz540

noncomputable def Ns588p1739 := @Enclosure.Real.IsNear.subLit_ff_p qz245 qz727 1757551001415337782469 562949953421312000 3163104647787749 1089000000000000000000 1004192 2000 0 1 Ns588p1738 1474896081602310712517 562949953421312000 3163104647787749 1089000000000000000000 

noncomputable def Ns588p1740 := nat_lit 3957653017529378662513386263058317312 

noncomputable def Ns588p1741 := nat_lit 120288920991727138637873152 

noncomputable def Ns588p1742 := nat_lit 137257557532791764859839001792529448216365951290396308473200272648628466728141373203645892538265743512186233022354883670269568918743378958087641405739938318844204929996001561836683790039581437108632528746237132800 

noncomputable def Ns588p1743 := nat_lit 4858940180171343908387182358223727529236666444749990001308350468513128127977515998191456262917218357609542390483636562238474892486676110840525084034585975003469437962401270697102372324998429561693704219084718080 

noncomputable def Ns588p1744 := nat_lit 79246245838378520517677872903291897470937436691202270407433815177952402684978597673421744614541778989974237494996389514557709606532277812480319561508020104230797709805077543699135406872557466627237478400 

noncomputable def Ns588p1745 := BSN.log_dyadic_bound 1936455291456 6130759291456 9 8 Ns588p1742 268435456 87120000 Ns588p1743 Ns588p1744 175578491 8067214582912 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 1936455291456) (BSN.artanhQ 6130759291456) 0 8 Ns588p1743 Ns588p1742 Ns588p1744 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz541 := (Real.log (Enclosure.sfrac Bool.false 4033607291456 16000000))

noncomputable def Ns588p1746 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1004192 4000) qz541 1004192 4000 0 1 56013893797866599 4503599627370496 12500018513 1089000000000000000 1757772001270851743219 562949953421312000 392263080956453 136125000000000000000 (Enclosure.Real.IsNear.const Bool.false 1004192 4000) (BSN.isNear_log_sfrac 4033607291456 16000000 56013893797866599 4503599627370496 12500018513 1089000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4033607291456) qz362)) Bool.false Ns588p1741 Ns588p114 1000001481040000 87120000000000000000000 56013893797866599 4503599627370496 12500018513 1089000000000000000 (BSN.log_rat_reduce_isNear 4033607291456 16000000 17 8067214582912 4194304000000 175578491 268435456 24973259072661432 36028797018963968 87120000 1000000000000000 rfl rfl rfl rfl (Ns588p1745 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p1747 := BSN.arctan_dyadic_bound_f 1000 2008384 1 0 33554432 10890000 0 1 1 0 1 1 16707 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 2008384) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 2008384) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns588p1748 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 2008384))) 884279719003555 562949953421312 1 2000000000000000 16707 33554432 1 10890000 29662098495412084146176 883999422055843 562949953421312 200000001089 2178000000000000000 qz17 (Ns588p1747 rfl) rfl rfl 

noncomputable abbrev qz542 := (@HMul.hMul Real Real Real qz588 qz593 qz726)

noncomputable abbrev qz246 := qz542

noncomputable abbrev qz543 := qz726

noncomputable abbrev qz247 := qz543

noncomputable def Ns588p1749 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 1004192 4000) qz541) qz246 1757772001270851743219 562949953421312000 392263080956453 136125000000000000000 883999422055843 2251799813685248 200000001089 8712000000000000000 Ns588p1740 1757551001415337782469 562949953421312000 3163104647787749 1089000000000000000000 (Ns588p1746 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz247 1 4 0 1 883999422055843 562949953421312 200000001089 2178000000000000000 883999422055843 2251799813685248 200000001089 8712000000000000000 qz369 Ns588p1748 rfl) 

noncomputable def Ns588p1750 := @Ns588p1735 Ns588p1729 Ns588p1730 4748224392899749363 557568000000000000000000 (@Ns588p1737 4748224392899749363 557568000000000000000000 (Ns588p1739 (Ns588p1749 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1004192 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz727 (Real.log Real.pi) 1004192 2000 0 1 38410761 33554432 3 268435456 1205368090941 2097152000 94143 16777216000 (Enclosure.Real.IsNear.const Bool.false 1004192 2000) RS589to600.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns588p1731 Ns588p1732) 

noncomputable def Ns588p1751 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz239) Bool.false Ns588p1729 Ns588p1730 4748224392899749363 557568000000000000000000 4289047625 2097152 573 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz239) (@HAdd.hAdd Real Real Real qz370 qz243 (Enclosure.sfrac Bool.true Ns588p1731 Ns588p1732)) Bool.false Ns588p1729 Ns588p1730 4748224392899749363 557568000000000000000000 Ns588p1733 (Ns588p1750 rfl rfl)) 

noncomputable def Ns588p1752 := BSN.cos_dyadic_bound_f 63691397 137438953472 1 0 67108864 21801270 0 1 1 0 1 1 67108856 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 63691397) qz383 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 63691397) qz384 0 0 rfl) rfl rfl 

noncomputable def Ns588p1753 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz239) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4289047625) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 4289047625 2097152 573 67108864 Bool.true 67108856 67108864 1 10890000 (Ns588p1751 rfl) (Enclosure.sfrac_false_div 4289047625 2097152) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4289047625) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 140058863867715911680) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 67108856 67108864 325 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 4289047625 2097152 226375608064910080 72057594037927936 325 140058863867715911680 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108856 67108864 140058863867715911680 302231454903657293676544 63691397 137438953472 21801270 21780000 (Ns588p1752 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p1754 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz239) Bool.false Ns588p1729 Ns588p1730 4748224392899749363 557568000000000000000000 1097996192006 536870912 4573 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz239) (@HAdd.hAdd Real Real Real qz370 qz243 (Enclosure.sfrac Bool.true Ns588p1731 Ns588p1732)) Bool.false Ns588p1729 Ns588p1730 4748224392899749363 557568000000000000000000 Ns588p1733 (Ns588p1750 rfl rfl)) 

noncomputable def Ns588p1755 := Ns588p1728 75021 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 858 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 101176329 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 599 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 466392527 536870912) qz242 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 1) Bool.true 8388607 8388608 394192429 45675970560000 536870848 536870912 4634 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz239)) Bool.true 8388607 8388608 394192429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz239) qz239) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz239)) Bool.true 67108856 67108864 6307078864 730815528960000 8388607 8388608 394192429 45675970560000 (Ns588p1753 rfl rfl) rfl)) rfl) (Ns588p1754 rfl) RS589to600.d7 

noncomputable def Ns588p1756 := nat_lit 41738745316756979515834692188025703139815333803522038583778416267937393724900443890650202836111678536679424000000 

noncomputable def Ns588p1757 := nat_lit 27640362036221613812257283948062489882141489356555621624205178049468950470699975501314921271296000000000000 

noncomputable def Ns588p1758 := nat_lit 252850006390938614401944118554160973870380788979226435440738640268895561078724781514000454662121154246711705600000 

noncomputable def Ns588p1759 := BSN.cos_dyadic_bound_f 741529860 536870912 4 3 536870912 268435456 Ns588p1756 Ns588p146 Ns588p1757 Ns588p1758 Ns588p149 Ns588p1757 101176329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 741529860) qz375 0 3 Ns588p1756 Ns588p146 Ns588p1757 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 741529860) qz376 0 3 Ns588p1758 Ns588p149 Ns588p1757 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1760 := nat_lit 25633221134518391553573383470047165082304606772150466521680955454997862945 

noncomputable def Ns588p1761 := nat_lit 10402344744318761799556939228859170252899279335856594339448596380195361 

noncomputable def Ns588p1762 := nat_lit 67117784889390699883111959758038707987531180808136025451662442749902658081 

noncomputable def Ns588p1763 := BSN.sin_dyadic_bound_f 565120947 536870912 3 2 536870912 268435456 Ns588p1760 Ns588p136 Ns588p1761 Ns588p1762 Ns588p139 Ns588p1761 466392527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 565120947) qz373 0 2 Ns588p1760 Ns588p136 Ns588p1761 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 565120947) qz374 0 2 Ns588p1762 Ns588p139 Ns588p1761 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1764 := nat_lit 59931472031854611202861718943092758454918724530989204173309409561079015728017606091696437233791435077380699324416 

noncomputable def Ns588p1765 := nat_lit 4676528257384548239454419037212927762915895322611538381261639292178256178927205814562327851911044153737216 

noncomputable def Ns588p1766 := nat_lit 299534116483188465660837838599427464767035798995898362814750486257166999064994022775426964611968781867238478053376 

noncomputable def Ns588p1767 := BSN.sin_dyadic_bound_f 639479996 536870912 4 3 536870912 268435456 Ns588p1764 Ns588p172 Ns588p1765 Ns588p1766 Ns588p175 Ns588p1765 498638316 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 639479996) qz373 0 3 Ns588p1764 Ns588p172 Ns588p1765 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 639479996) qz374 0 3 Ns588p1766 Ns588p175 Ns588p1765 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1768 := nat_lit 61931374953923672617555949383696 

noncomputable def Ns588p1769 := BSN.sin_dyadic_bound_f 88711042 536870912 2 1 536870912 268435456 Ns588p1768 Ns588p188 Ns588p1768 Ns588p1768 Ns588p189 Ns588p1768 88307908 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 88711042) qz373 0 1 Ns588p1768 Ns588p188 Ns588p1768 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 88711042) qz374 0 1 Ns588p1768 Ns588p189 Ns588p1768 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1770 := Ns588p1726 126932 BSN.abs_quadSignPos (BSN.cos_quad_nat3 415 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 498638316 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 273 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 88307908 536870912) qz242 rfl rfl (Ns588p1755 RS589to600.d9 RS589to600.d11 RS589to600.d13 RS589to600.d17 (Ns588p1759 rfl rfl) (Ns588p1763 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns588p1754 rfl) RS589to600.d19 RS589to600.d21 RS589to600.d23 RS589to600.d25 RS589to600.d17 (Ns588p1767 rfl rfl) (Ns588p1769 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns588p1771 := nat_lit 6419981722144103652708479342444707265329905565427318200915342527578505216 

noncomputable def Ns588p1772 := nat_lit 2114481552990218109538568774721416622660410634378820620221026544910336 

noncomputable def Ns588p1773 := nat_lit 19255716203326330521906360889784678962744395875013196961505585529645694976 

noncomputable def Ns588p1774 := BSN.cos_dyadic_bound_f 463074096 536870912 3 2 536870912 268435456 Ns588p1771 Ns588p152 Ns588p1772 Ns588p1773 Ns588p155 Ns588p1772 349239027 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 463074096) qz375 0 2 Ns588p1771 Ns588p152 Ns588p1772 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 463074096) qz376 0 2 Ns588p1773 Ns588p155 Ns588p1772 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1775 := BSN.cos_dyadic_bound_f 1996275 536870912 1 0 536870912 268435456 0 1 1 0 1 1 536867200 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1996275) qz375 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1996275) qz376 0 0 rfl) rfl rfl 

noncomputable def Ns588p1776 := Ns588p1724 170812 BSN.abs_quadSignPos (BSN.cos_quad_nat0 156 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 349239027 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536867200 536870912) qz242 rfl rfl (Ns588p1770 rfl rfl) (Ns588p1754 rfl) RS589to600.d27 RS589to600.d29 RS589to600.d31 RS589to600.d33 RS589to600.d17 (Ns588p1774 rfl rfl) (Ns588p1775 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1777 := nat_lit 2199763552364067640817173004515905098193091328152492891041145721716135905 

noncomputable def Ns588p1778 := nat_lit 76665357293148114576593275115591979073020793718715222644374032013281 

noncomputable def Ns588p1779 := nat_lit 5761161369422654914716614813191469060634835254352412985223481237014239201 

noncomputable def Ns588p1780 := BSN.sin_dyadic_bound_f 305896773 536870912 3 2 536870912 268435456 Ns588p1777 Ns588p136 Ns588p1778 Ns588p1779 Ns588p139 Ns588p1778 289612012 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 305896773) qz373 0 2 Ns588p1777 Ns588p136 Ns588p1778 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 305896773) qz374 0 2 Ns588p1779 Ns588p139 Ns588p1778 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1781 := nat_lit 13232988076901280836129614405154699284083209237041960034302147065478792461018886236521660199837367659611546789281 

noncomputable def Ns588p1782 := nat_lit 884756299171931740719616110337521930351831424827795355671133489087318324851677736747640778159504661751201 

noncomputable def Ns588p1783 := nat_lit 80243335374956378922416121622056895049557082958308561092588252228679244454938950536481713901717503989075764651425 

noncomputable def Ns588p1784 := BSN.cos_dyadic_bound_f 556632601 536870912 4 3 536870912 268435456 Ns588p1781 Ns588p146 Ns588p1782 Ns588p1783 Ns588p149 Ns588p1782 273250970 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 556632601) qz375 0 3 Ns588p1781 Ns588p146 Ns588p1782 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 556632601) qz376 0 3 Ns588p1783 Ns588p149 Ns588p1782 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1785 := Ns588p1722 209151 BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 289612012 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 102 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 273250970 536870912) qz242 rfl rfl (Ns588p1776 rfl) (Ns588p1754 rfl) RS589to600.d35 RS589to600.d37 RS589to600.d39 RS589to600.d41 RS589to600.d17 (Ns588p1780 rfl rfl) (Ns588p1784 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1786 := nat_lit 31771549695513159765543566881 

noncomputable def Ns588p1787 := BSN.cos_dyadic_bound_f 13350871 536870912 2 1 536870912 268435456 Ns588p1786 Ns588p142 Ns588p1786 Ns588p1786 Ns588p143 Ns588p1786 536704916 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13350871) qz375 0 1 Ns588p1786 Ns588p142 Ns588p1786 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13350871) qz376 0 1 Ns588p1786 Ns588p143 Ns588p1786 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1788 := nat_lit 56085170812964687519028334814099300017574577176642799914974916972442089858600441898706383476404360475216071190241 

noncomputable def Ns588p1789 := nat_lit 66912017075515996072798998967059524562793450864355909358790875882294263407048572857049737121782698200884961 

noncomputable def Ns588p1790 := nat_lit 339591800768834484960961483713341582377658844792938571017025328090907326795550731753750503115588394507323726456545 

noncomputable def Ns588p1791 := BSN.cos_dyadic_bound_f 798225033 536870912 4 3 536870912 268435456 Ns588p1788 Ns588p146 Ns588p1789 Ns588p1790 Ns588p149 Ns588p1789 45036833 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 798225033) qz375 0 3 Ns588p1788 Ns588p146 Ns588p1789 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 798225033) qz376 0 3 Ns588p1790 Ns588p149 Ns588p1789 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1792 := Ns588p1720 243632 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 170 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536704916 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 230 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 45036833 536870912) qz242 rfl rfl (Ns588p1785 rfl) (Ns588p1754 rfl) RS589to600.d43 RS589to600.d45 RS589to600.d47 RS589to600.d49 RS589to600.d17 (Ns588p1787 rfl rfl) (Ns588p1791 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns588p1793 := nat_lit 7554204856442093730623105223460452808437085625740662259805780058503980321 

noncomputable def Ns588p1794 := nat_lit 2927273577754786698872926383574504021336718568413343981057183167358241 

noncomputable def Ns588p1795 := nat_lit 22656760022170771618471569817614209417268583440085160091455225809177224481 

noncomputable def Ns588p1796 := BSN.cos_dyadic_bound_f 482289619 536870912 3 2 536870912 268435456 Ns588p1793 Ns588p152 Ns588p1794 Ns588p1795 Ns588p155 Ns588p1794 334424299 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 482289619) qz375 0 2 Ns588p1793 Ns588p152 Ns588p1794 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 482289619) qz376 0 2 Ns588p1795 Ns588p155 Ns588p1794 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1797 := Ns588p1718 Bool.true 361645773 243632 Bool.true 482289619 28296951008113761 1 Bool.false 334424299 Bool.true Bool.true 458185756 259747 BSN.abs_quadSignNeg qz398 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 334424299 536870912) qz242 rfl (Ns588p1792 rfl) (Ns588p1754 rfl) RS589to600.d51 RS589to600.d53 RS589to600.d17 (Ns588p1796 rfl rfl) rfl 

noncomputable def Ns588p1798 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 12) 458185756 536870912 259747 536870912 458185756 536870912 259747 536870912 491973209378258944 114546439 67108864 259747 268435456 (Ns588p1797 rfl rfl rfl rfl) 

noncomputable def Ns588p1799 := @Enclosure.Real.IsNear.mulLit_ff qz724 (Zeta.RiemannSiegel.correction qz241) 4718573 16777216 1 33554432 58946927771187 140737488355328 12874208701063253 766315624094760960000 278145381814073156151 2361183241434822606848 

noncomputable abbrev qz728 := (@HPow.hPow Real Real Real qz7 qz240 qz9)

noncomputable def Ns588p1800 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz728 1 1 0 1 4718573 16777216 1 33554432 4718573 16777216 1 33554432 

noncomputable def Ns588p1801 := @Enclosure.Real.IsNear.sqrt_image qz240 335171266367 2097152000 31381 2097152000 424197697 424197738 33554432 (@Enclosure.Real.IsNear.of_eq qz240 (@HMul.hMul Real Real Real qz5 qz239 qz3) Bool.false 335171266367 2097152000 31381 2097152000 (BSN.t_div_two_pi_mk qz239 1004192 1000 qz242) (@Enclosure.Real.IsNear.mulLit_ff qz239 qz3 1004192 1000 0 1 10680707 67108864 1 67108864 335171266367 2097152000 31381 2097152000 (Enclosure.Real.IsNear.const Bool.false 1004192 1000) RS589to600.d56 rfl)) 

noncomputable abbrev qz798 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 1004192 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz729 := qz798

noncomputable abbrev qz544 := qz729

noncomputable abbrev qz248 := qz544

noncomputable def Ns588p1802 := @Enclosure.Real.IsNear.sqrt_image qz248 848395435 67108864 41 67108864 119305124 119305131 33554432 (@Enclosure.Real.IsNear.recentre' qz248 Bool.false 848395435 67108864 41 67108864 848395435 67108864 41 67108864 (Ns588p1801 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns588p1803 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz248) 238610255 67108864 7 67108864 9437145 9437147 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz248) Bool.false 238610255 67108864 7 67108864 238610255 67108864 7 67108864 (Ns588p1802 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns588p1804 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz248)) Bool.false 18874292 67108864 2 67108864 4718573 16777216 1 33554432 (Ns588p1803 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz545 := (@HMul.hMul Real Real Real qz588 qz586 qz723)

noncomputable abbrev qz249 := (Real.cos qz545)

noncomputable abbrev qz730 := (@HMul.hMul Real Real Real qz739 qz796 qz796)

noncomputable abbrev qz546 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz730 qz723) qz603)

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz546))

noncomputable def Ns588p1805 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz241) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz249) qz250) Bool.false 58946927771187 

noncomputable def Ns588p1806 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz249) qz250 13372263 8388608 337 

noncomputable abbrev qz251 := (@Neg.neg Real Real.instNeg (Real.cos qz545))

noncomputable def Ns588p1807 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz249) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz251)) Bool.true 13372263 8388608 337 33554432 (BSN.inv_eq_neg_inv_neg qz249) 

noncomputable def Ns588p1808 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz251) Bool.false 106978104 67108864 674 67108864 13372263 8388608 

noncomputable def Ns588p1809 := @Enclosure.Real.IsNear.recentre' qz249 Bool.true 42098331 67108864 2887618864 730815528960000 42098331 67108864 180476179 45675970560000 

noncomputable abbrev qz252 := qz545

noncomputable def Ns588p1810 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16921037) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false 16921037 4194304 259 67108864 Bool.true 42098331 67108864 1 

noncomputable def Ns588p1811 := nat_lit 1106429092140938130822233311 

noncomputable def Ns588p1812 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz241 884279719003555 140737488355328 1 500000000000000 43089067 67108864 41 67108864 38102788058885354633185 9444732965739290427392 Ns588p1811 

noncomputable def Ns588p1813 := @Enclosure.Real.IsNear.subLit_ff_p qz248 qz1 848395435 67108864 41 67108864 12 1 0 1 43089067 43089067 67108864 41 

noncomputable def Ns588p1814 := @Ns588p1813 67108864 (@Enclosure.Real.IsNear.recentre' qz248 Bool.false 848395435 67108864 41 67108864 848395435 67108864 41 67108864 (Ns588p1801 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns588p1815 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 38102788058885354633185 9444732965739290427392 Ns588p1811 Ns588p913 16921037 4194304 259 67108864 (@Ns588p1812 Ns588p913 RS589to600.d55 (Ns588p1814 rfl rfl) rfl) 

noncomputable def Ns588p1816 := nat_lit 135884002339173261450742034788820177211247375074998971627059593357341428467508700224436544641 

noncomputable def Ns588p1817 := nat_lit 51346530588190881035668264094905400976057898835447862106693547650023186963701420821292161 

noncomputable def Ns588p1818 := nat_lit 407549313956343402590154767838270720831790009427326019156965392976724239028598697831667049601 

noncomputable def Ns588p1819 := BSN.cos_dyadic_bound_f 122691333871 137438953472 3 2 67108864 21801270 Ns588p1816 Ns588p511 Ns588p1817 Ns588p1818 Ns588p514 Ns588p1817 42098331 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 122691333871) qz383 0 2 Ns588p1816 Ns588p511 Ns588p1817 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 122691333871) qz384 0 2 Ns588p1818 Ns588p514 Ns588p1817 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1820 := @Ns588p1810 10890000 (Ns588p1815 rfl) (Enclosure.sfrac_false_div 16921037 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16921037) (@Nat.cast Real Real.instNatCast 4194304)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 539602192875346800410624) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 42098331 67108864 0 1000000000000000 21780000 10890000 (BSN.sin_reduce_arg_pos_rat_q2 16921037 4194304 226375608064910080 72057594037927936 0 539602192875346800410624 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 42098331 67108864 539602192875346800410624 604462909807314587353088 122691333871 137438953472 21801270 21780000 (Ns588p1819 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns588p1821 := @Enclosure.Real.IsNear.inv_image qz251 42098331 67108864 180476179 45675970560000 53488715 53489389 33554432 (@Enclosure.Real.IsNear.neg qz249 Bool.true 42098331 67108864 180476179 45675970560000 (Ns588p1809 (Ns588p1820 rfl rfl) rfl)) 

noncomputable def Ns588p1822 := Ns588p1807 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz251) Bool.false 13372263 8388608 337 33554432 (@Ns588p1808 337 33554432 (Ns588p1821 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns588p1823 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true 8816298 33554432 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz355 qz352 qz546)

noncomputable def Ns588p1824 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 61628203)) qz397) Bool.true 61628203 33554432 

noncomputable def Ns588p1825 := nat_lit 1164123847620681340089983545525 

noncomputable def Ns588p1826 := nat_lit 169601239352314451044144152897509793 

noncomputable def Ns588p1827 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns588p1825 Ns588p929 Ns588p1826 

noncomputable abbrev qz254 := qz546

noncomputable def Ns588p1828 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 1316465618970055 

noncomputable abbrev qz547 := (@HSub.hSub Real Real Real qz592 qz730 qz723)

noncomputable abbrev qz255 := qz547

noncomputable def Ns588p1829 := @Enclosure.Real.IsNear.subLit_tf qz255 qz31 1034990642259399 4503599627370496 6284768599 4503599627370496 1 16 

noncomputable abbrev qz548 := qz730

noncomputable abbrev qz256 := qz548

noncomputable def Ns588p1830 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz241 1856667694930489 4503599627370496 3533305175 4503599627370496 43089067 67108864 41 67108864 

noncomputable def Ns588p1831 := @Enclosure.Real.IsNear.mulLit_ff qz241 qz241 43089067 67108864 41 67108864 43089067 67108864 41 67108864 1856667694930489 4503599627370496 

noncomputable def Ns588p1832 := nat_lit 465776336463389019858316913170449568642035117312410844358620558964784963658435307417309637071042321 

noncomputable def Ns588p1833 := nat_lit 3001608546623989392458114563751778999263000358996071009140393831836317195849887892707215636241 

noncomputable def Ns588p1834 := nat_lit 2813020647698378240335663160847974398966709200923661494387450562269684168828438887911623013932693265 

noncomputable def Ns588p1835 := BSN.cos_dyadic_bound_t 61628203 33554432 4 3 33554432 10890000 Ns588p1832 Ns588p361 Ns588p1833 Ns588p1834 Ns588p364 Ns588p1833 8816298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 61628203) (BSN.cosEvenQ 33554432) 0 3 Ns588p1832 Ns588p361 Ns588p1833 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 61628203) (BSN.cosOddQ 33554432) 0 3 Ns588p1834 Ns588p364 Ns588p1833 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns588p1836 := @Ns588p1823 3246104432 365407764480000 4408149 16777216 202881527 22837985280000 (@Ns588p1824 295 33554432 Bool.true 8816298 33554432 1 10890000 (@Ns588p1827 Ns588p932 61628203 33554432 295 33554432 (@Ns588p1828 4503599627370496 6284768599 4503599627370496 Ns588p1825 Ns588p929 Ns588p1826 Ns588p932 RS589to600.d55 (@Ns588p1829 0 1 21063449903520880 1316465618970055 4503599627370496 6284768599 4503599627370496 (@Ns588p1830 69457046252658660212736 1034990642259399 4503599627370496 6284768599 4503599627370496 (@Ns588p1831 3533305175 4503599627370496 (Ns588p1814 rfl rfl) (Ns588p1814 rfl rfl) rfl) (Ns588p1814 rfl rfl) rfl rfl) qz388 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 61628203 33554432) (BSN.cos_neg_of_bound 61628203 33554432 Bool.true 8816298 33554432 1 10890000 (Ns588p1835 rfl rfl)) rfl rfl) 

noncomputable def Ns588p1837 := @Ns588p1799 121816766042327088074191 Ns588p1715 (Ns588p1800 qz33 (@Enclosure.Real.IsNear.of_eq qz728 (@Inv.inv Real Real.instInv (Real.sqrt qz248)) Bool.false 4718573 16777216 1 33554432 (BSN.rpow_neg_quarter_mk qz240 (BSN.t_div_two_pi_nonneg qz239 1004192 1000 qz242)) Ns588p1804) rfl) (@Ns588p1805 140737488355328 12874208701063253 766315624094760960000 (BSN.correction_mk qz241 (BSN.cos_two_pi_p_ne_zero_mk qz239 1004192 1000 12 qz242 rfl rfl (@BSN.floor_sqrt_eq_dec qz239 1004192 1000 12 qz242 rfl rfl rfl))) (@Ns588p1806 33554432 4408149 16777216 202881527 22837985280000 58946927771187 140737488355328 12874208701063253 766315624094760960000 Ns588p1822 (Ns588p1836 rfl) rfl)) 

noncomputable def Ns588p1838 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz239) (hardyZApproximantRS₀ qz239) Bool.true 4308389913040770425399 2361183241434822606848 Ns588p1714 Ns588p1715 (@Eq.refl Real (hardyZApproximantRS₀ qz239)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz239) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz239) qz239 12) (@HMul.hMul Real Real Real qz5 qz724 (Zeta.RiemannSiegel.correction qz241))) Bool.true 4308389913040770425399 2361183241434822606848 Ns588p1714 Ns588p1715 (BSN.hardyZApproximantRS₀_eq qz239 12 (@BSN.floor_sqrt_eq_dec qz239 1004192 1000 12 qz242 rfl rfl rfl)) (@Ns588p1717 4308389913040770425399 2361183241434822606848 Ns588p1714 Ns588p1715 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz239) qz239 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 12)) Bool.true 114546439 67108864 259747 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz239) qz239 12) (Ns588p1798 (Ns588p1797 rfl rfl rfl rfl) rfl rfl)) (Ns588p1837 rfl) rfl rfl)) 

theorem RS589to600.d71 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz239) Bool.true 4308389913040770425399 2361183241434822606848 Ns588p1714 Ns588p1715 := Ns588p1838 

noncomputable def RS589to600.d72 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz549 := (RS589to600.d3 qz587 qz604 (@Enclosure.dec_le_dec qz587 qz604 989310 1000 990552 1000 (@Eq.refl Real qz587) qz608 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz549)

noncomputable def Ns588p1839 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 9881569288893253501049 4722366482869645213696 Ns588p85 Ns588p86 

noncomputable abbrev qz550 := (@Enclosure.dec_le_dec qz587 qz604 989310 1000 990552 1000 (@Eq.refl Real qz587) qz608 rfl rfl rfl)

noncomputable abbrev qz258 := qz550

noncomputable def Ns588p1840 := @Enclosure.Real.IsNear.neg_val qz257 9881569288893253501049 4722366482869645213696 Ns588p85 Ns588p86 (Ns588p1839 (RS589to600.d4 qz4 qz35 qz258) RS589to600.d57) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz549)

noncomputable def Ns588p1841 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz35) Bool.false 12362604364951653527955 9444732965739290427392 136760146210401609860131 Ns588p239 

noncomputable def Ns588p1842 := @Enclosure.Real.IsNear.pos_val qz259 12362604364951653527955 9444732965739290427392 136760146210401609860131 Ns588p239 (Ns588p1841 (RS589to600.d58 qz4 qz35 qz258) RS589to600.d59) rfl 

noncomputable def Ns588p1843 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 989310 1000 989310 1000 

noncomputable def Ns588p1844 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 9881569288893253501049 4722366482869645213696 Ns588p85 

noncomputable def Ns588p1845 := @Ns588p1844 Ns588p86 434356701 10737418240 1213 10737418240 (Ns588p1839 (RS589to600.d4 qz4 qz35 qz258) RS589to600.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable def Ns588p1846 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz35 989310 1000 990552 1000 

noncomputable def Ns588p1847 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 12362604364951653527955 9444732965739290427392 136760146210401609860131 

noncomputable def Ns588p1848 := @Ns588p1847 Ns588p239 434356701 10737418240 1213 10737418240 (Ns588p1841 (RS589to600.d58 qz4 qz35 qz258) RS589to600.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz549

noncomputable def Ns588p1849 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 989310 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns588p1840 rfl rfl) (Ns588p1842 rfl rfl)) (Ns588p1843 qz11 qz11 rfl rfl rfl rfl (Ns588p1845 rfl)) (Ns588p1846 qz11 qz38 rfl rfl rfl rfl (Ns588p1848 rfl)) 

noncomputable abbrev qz551 := (RS589to600.d3 qz604 qz617 (@Enclosure.dec_le_dec qz604 qz617 990552 1000 991794 1000 qz608 qz621 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns588p1850 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz35) Bool.false 12362604364951653527955 9444732965739290427392 136760146210401609860131 Ns588p239 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz604 qz617 990552 1000 991794 1000 qz608 qz621 rfl rfl rfl)

noncomputable abbrev qz262 := qz552

noncomputable def Ns588p1851 := @Enclosure.Real.IsNear.pos_val qz261 12362604364951653527955 9444732965739290427392 136760146210401609860131 Ns588p239 (Ns588p1850 (RS589to600.d4 qz35 qz62 qz262) RS589to600.d59) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns588p1852 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz62) Bool.true 45441634910048930307993 37778931862957161709568 Ns588p402 Ns588p403 

noncomputable def Ns588p1853 := @Enclosure.Real.IsNear.neg_val qz263 45441634910048930307993 37778931862957161709568 Ns588p402 Ns588p403 (Ns588p1852 (RS589to600.d58 qz35 qz62 qz262) RS589to600.d61) rfl 

noncomputable def Ns588p1854 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz35 989310 1000 990552 1000 

noncomputable def Ns588p1855 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 12362604364951653527955 9444732965739290427392 136760146210401609860131 

noncomputable def Ns588p1856 := @Ns588p1855 Ns588p239 434356701 10737418240 1213 10737418240 (Ns588p1850 (RS589to600.d4 qz35 qz62 qz262) RS589to600.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable def Ns588p1857 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz62 989310 1000 991794 1000 

noncomputable def Ns588p1858 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 45441634910048930307993 37778931862957161709568 Ns588p402 

noncomputable def Ns588p1859 := @Ns588p1858 Ns588p403 434356701 10737418240 1213 10737418240 (Ns588p1852 (RS589to600.d58 qz35 qz62 qz262) RS589to600.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz551

noncomputable def Ns588p1860 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz35 990552 1000 qz38 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns588p1851 rfl rfl) (Ns588p1853 rfl rfl)) (Ns588p1854 qz11 qz38 rfl rfl rfl rfl (Ns588p1856 rfl)) (Ns588p1857 qz11 qz65 rfl rfl rfl rfl (Ns588p1859 rfl)) 

noncomputable abbrev qz553 := (RS589to600.d3 qz617 qz627 (@Enclosure.dec_le_dec qz617 qz627 991794 1000 993035 1000 qz621 qz631 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns588p1861 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz62) Bool.true 45441634910048930307993 37778931862957161709568 Ns588p402 Ns588p403 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz617 qz627 991794 1000 993035 1000 qz621 qz631 rfl rfl rfl)

noncomputable abbrev qz266 := qz554

noncomputable def Ns588p1862 := @Enclosure.Real.IsNear.neg_val qz265 45441634910048930307993 37778931862957161709568 Ns588p402 Ns588p403 (Ns588p1861 (RS589to600.d4 qz62 qz80 qz266) RS589to600.d61) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns588p1863 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz80) Bool.false 7147034770054651554083 37778931862957161709568 329111355297436243780991 Ns588p539 

noncomputable def Ns588p1864 := @Enclosure.Real.IsNear.pos_val qz267 7147034770054651554083 37778931862957161709568 329111355297436243780991 Ns588p539 (Ns588p1863 (RS589to600.d58 qz62 qz80 qz266) RS589to600.d62) rfl 

noncomputable def Ns588p1865 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz62 989310 1000 991794 1000 

noncomputable def Ns588p1866 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 45441634910048930307993 37778931862957161709568 Ns588p402 

noncomputable def Ns588p1867 := @Ns588p1866 Ns588p403 434356701 10737418240 1213 10737418240 (Ns588p1861 (RS589to600.d4 qz62 qz80 qz266) RS589to600.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable def Ns588p1868 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz80 989310 1000 993035 1000 

noncomputable def Ns588p1869 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 7147034770054651554083 37778931862957161709568 329111355297436243780991 

noncomputable def Ns588p1870 := @Ns588p1869 Ns588p539 434356701 10737418240 1213 10737418240 (Ns588p1863 (RS589to600.d58 qz62 qz80 qz266) RS589to600.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz553

noncomputable def Ns588p1871 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz62 991794 1000 qz65 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns588p1862 rfl rfl) (Ns588p1864 rfl rfl)) (Ns588p1865 qz11 qz65 rfl rfl rfl rfl (Ns588p1867 rfl)) (Ns588p1868 qz11 qz83 rfl rfl rfl rfl (Ns588p1870 rfl)) 

noncomputable abbrev qz555 := (RS589to600.d3 qz627 qz638 (@Enclosure.dec_le_dec qz627 qz638 993035 1000 994276 1000 qz631 qz642 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns588p1872 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz80) Bool.false 7147034770054651554083 37778931862957161709568 329111355297436243780991 Ns588p539 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz627 qz638 993035 1000 994276 1000 qz631 qz642 rfl rfl rfl)

noncomputable abbrev qz270 := qz556

noncomputable def Ns588p1873 := @Enclosure.Real.IsNear.pos_val qz269 7147034770054651554083 37778931862957161709568 329111355297436243780991 Ns588p539 (Ns588p1872 (RS589to600.d4 qz80 qz98 qz270) RS589to600.d62) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns588p1874 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz98) Bool.true 175003219321992485707 295147905179352825856 Ns588p672 Ns588p86 

noncomputable def Ns588p1875 := @Enclosure.Real.IsNear.neg_val qz271 175003219321992485707 295147905179352825856 Ns588p672 Ns588p86 (Ns588p1874 (RS589to600.d58 qz80 qz98 qz270) RS589to600.d63) rfl 

noncomputable def Ns588p1876 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz80 989310 1000 993035 1000 

noncomputable def Ns588p1877 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 7147034770054651554083 37778931862957161709568 329111355297436243780991 

noncomputable def Ns588p1878 := @Ns588p1877 Ns588p539 434356701 10737418240 1213 10737418240 (Ns588p1872 (RS589to600.d4 qz80 qz98 qz270) RS589to600.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable def Ns588p1879 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz98 989310 1000 994276 1000 

noncomputable def Ns588p1880 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 175003219321992485707 295147905179352825856 Ns588p672 

noncomputable def Ns588p1881 := @Ns588p1880 Ns588p86 434356701 10737418240 1213 10737418240 (Ns588p1874 (RS589to600.d58 qz80 qz98 qz270) RS589to600.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz555

noncomputable def Ns588p1882 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz80 993035 1000 qz83 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns588p1873 rfl rfl) (Ns588p1875 rfl rfl)) (Ns588p1876 qz11 qz83 rfl rfl rfl rfl (Ns588p1878 rfl)) (Ns588p1879 qz11 qz101 rfl rfl rfl rfl (Ns588p1881 rfl)) 

noncomputable abbrev qz557 := (RS589to600.d3 qz638 qz648 (@Enclosure.dec_le_dec qz638 qz648 994276 1000 995516 1000 qz642 qz652 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns588p1883 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz98) Bool.true 175003219321992485707 295147905179352825856 Ns588p672 Ns588p86 

noncomputable abbrev qz558 := (@Enclosure.dec_le_dec qz638 qz648 994276 1000 995516 1000 qz642 qz652 rfl rfl rfl)

noncomputable abbrev qz274 := qz558

noncomputable def Ns588p1884 := @Enclosure.Real.IsNear.neg_val qz273 175003219321992485707 295147905179352825856 Ns588p672 Ns588p86 (Ns588p1883 (RS589to600.d4 qz98 qz116 qz274) RS589to600.d63) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns588p1885 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz116) Bool.false 175464207521016420159639 37778931862957161709568 Ns588p803 Ns588p804 

noncomputable def Ns588p1886 := @Enclosure.Real.IsNear.pos_val qz275 175464207521016420159639 37778931862957161709568 Ns588p803 Ns588p804 (Ns588p1885 (RS589to600.d58 qz98 qz116 qz274) RS589to600.d64) rfl 

noncomputable def Ns588p1887 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz98 989310 1000 994276 1000 

noncomputable def Ns588p1888 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 175003219321992485707 295147905179352825856 Ns588p672 

noncomputable def Ns588p1889 := @Ns588p1888 Ns588p86 434356701 10737418240 1213 10737418240 (Ns588p1883 (RS589to600.d4 qz98 qz116 qz274) RS589to600.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable def Ns588p1890 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz116 989310 1000 995516 1000 

noncomputable def Ns588p1891 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 175464207521016420159639 37778931862957161709568 Ns588p803 

noncomputable def Ns588p1892 := @Ns588p1891 Ns588p804 434356701 10737418240 1213 10737418240 (Ns588p1885 (RS589to600.d58 qz98 qz116 qz274) RS589to600.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz557

noncomputable def Ns588p1893 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz98 994276 1000 qz101 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns588p1884 rfl rfl) (Ns588p1886 rfl rfl)) (Ns588p1887 qz11 qz101 rfl rfl rfl rfl (Ns588p1889 rfl)) (Ns588p1890 qz11 qz119 rfl rfl rfl rfl (Ns588p1892 rfl)) 

noncomputable abbrev qz559 := (RS589to600.d3 qz648 qz658 (@Enclosure.dec_le_dec qz648 qz658 995516 1000 996757 1000 qz652 qz662 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns588p1894 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz116) Bool.false 175464207521016420159639 37778931862957161709568 Ns588p803 Ns588p804 

noncomputable abbrev qz560 := (@Enclosure.dec_le_dec qz648 qz658 995516 1000 996757 1000 qz652 qz662 rfl rfl rfl)

noncomputable abbrev qz278 := qz560

noncomputable def Ns588p1895 := @Enclosure.Real.IsNear.pos_val qz277 175464207521016420159639 37778931862957161709568 Ns588p803 Ns588p804 (Ns588p1894 (RS589to600.d4 qz116 qz134 qz278) RS589to600.d64) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns588p1896 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz134) Bool.true 227482083915007616154781 75557863725914323419136 Ns588p944 Ns588p945 

noncomputable def Ns588p1897 := @Enclosure.Real.IsNear.neg_val qz279 227482083915007616154781 75557863725914323419136 Ns588p944 Ns588p945 (Ns588p1896 (RS589to600.d58 qz116 qz134 qz278) RS589to600.d65) rfl 

noncomputable def Ns588p1898 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz116 989310 1000 995516 1000 

noncomputable def Ns588p1899 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 175464207521016420159639 37778931862957161709568 Ns588p803 

noncomputable def Ns588p1900 := @Ns588p1899 Ns588p804 434356701 10737418240 1213 10737418240 (Ns588p1894 (RS589to600.d4 qz116 qz134 qz278) RS589to600.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable def Ns588p1901 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz134 989310 1000 996757 1000 

noncomputable def Ns588p1902 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 227482083915007616154781 75557863725914323419136 Ns588p944 

noncomputable def Ns588p1903 := @Ns588p1902 Ns588p945 434356701 10737418240 1213 10737418240 (Ns588p1896 (RS589to600.d58 qz116 qz134 qz278) RS589to600.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz559

noncomputable def Ns588p1904 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz116 995516 1000 qz119 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns588p1895 rfl rfl) (Ns588p1897 rfl rfl)) (Ns588p1898 qz11 qz119 rfl rfl rfl rfl (Ns588p1900 rfl)) (Ns588p1901 qz11 qz137 rfl rfl rfl rfl (Ns588p1903 rfl)) 

noncomputable abbrev qz561 := (RS589to600.d3 qz658 qz669 (@Enclosure.dec_le_dec qz658 qz669 996757 1000 997997 1000 qz662 qz673 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns588p1905 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz134) Bool.true 227482083915007616154781 75557863725914323419136 Ns588p944 Ns588p945 

noncomputable abbrev qz562 := (@Enclosure.dec_le_dec qz658 qz669 996757 1000 997997 1000 qz662 qz673 rfl rfl rfl)

noncomputable abbrev qz282 := qz562

noncomputable def Ns588p1906 := @Enclosure.Real.IsNear.neg_val qz281 227482083915007616154781 75557863725914323419136 Ns588p944 Ns588p945 (Ns588p1905 (RS589to600.d4 qz134 qz151 qz282) RS589to600.d65) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns588p1907 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz151) Bool.false 1349427130010725681177 590295810358705651712 Ns588p1070 Ns588p403 

noncomputable def Ns588p1908 := @Enclosure.Real.IsNear.pos_val qz283 1349427130010725681177 590295810358705651712 Ns588p1070 Ns588p403 (Ns588p1907 (RS589to600.d58 qz134 qz151 qz282) RS589to600.d66) rfl 

noncomputable def Ns588p1909 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz134 989310 1000 996757 1000 

noncomputable def Ns588p1910 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 227482083915007616154781 75557863725914323419136 Ns588p944 

noncomputable def Ns588p1911 := @Ns588p1910 Ns588p945 434356701 10737418240 1213 10737418240 (Ns588p1905 (RS589to600.d4 qz134 qz151 qz282) RS589to600.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable def Ns588p1912 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz151 989310 1000 997997 1000 

noncomputable def Ns588p1913 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1349427130010725681177 590295810358705651712 Ns588p1070 

noncomputable def Ns588p1914 := @Ns588p1913 Ns588p403 434356701 10737418240 1213 10737418240 (Ns588p1907 (RS589to600.d58 qz134 qz151 qz282) RS589to600.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz561

noncomputable def Ns588p1915 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz134 996757 1000 qz137 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns588p1906 rfl rfl) (Ns588p1908 rfl rfl)) (Ns588p1909 qz11 qz137 rfl rfl rfl rfl (Ns588p1911 rfl)) (Ns588p1912 qz11 qz154 rfl rfl rfl rfl (Ns588p1914 rfl)) 

noncomputable abbrev qz563 := (RS589to600.d3 qz669 qz680 (@Enclosure.dec_le_dec qz669 qz680 997997 1000 999236 1000 qz673 qz684 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns588p1916 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz151) Bool.false 1349427130010725681177 590295810358705651712 Ns588p1070 Ns588p403 

noncomputable abbrev qz564 := (@Enclosure.dec_le_dec qz669 qz680 997997 1000 999236 1000 qz673 qz684 rfl rfl rfl)

noncomputable abbrev qz286 := qz564

noncomputable def Ns588p1917 := @Enclosure.Real.IsNear.pos_val qz285 1349427130010725681177 590295810358705651712 Ns588p1070 Ns588p403 (Ns588p1916 (RS589to600.d4 qz151 qz168 qz286) RS589to600.d66) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns588p1918 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz168) Bool.true 23536802811599871075627 18889465931478580854784 Ns588p1196 Ns588p1197 

noncomputable def Ns588p1919 := @Enclosure.Real.IsNear.neg_val qz287 23536802811599871075627 18889465931478580854784 Ns588p1196 Ns588p1197 (Ns588p1918 (RS589to600.d58 qz151 qz168 qz286) RS589to600.d67) rfl 

noncomputable def Ns588p1920 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz151 989310 1000 997997 1000 

noncomputable def Ns588p1921 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1349427130010725681177 590295810358705651712 Ns588p1070 

noncomputable def Ns588p1922 := @Ns588p1921 Ns588p403 434356701 10737418240 1213 10737418240 (Ns588p1916 (RS589to600.d4 qz151 qz168 qz286) RS589to600.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable def Ns588p1923 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz168 989310 1000 999236 1000 

noncomputable def Ns588p1924 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 23536802811599871075627 18889465931478580854784 Ns588p1196 

noncomputable def Ns588p1925 := @Ns588p1924 Ns588p1197 434356701 10737418240 1213 10737418240 (Ns588p1918 (RS589to600.d58 qz151 qz168 qz286) RS589to600.d67) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz563

noncomputable def Ns588p1926 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz151 997997 1000 qz154 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns588p1917 rfl rfl) (Ns588p1919 rfl rfl)) (Ns588p1920 qz11 qz154 rfl rfl rfl rfl (Ns588p1922 rfl)) (Ns588p1923 qz11 qz171 rfl rfl rfl rfl (Ns588p1925 rfl)) 

noncomputable abbrev qz731 := (@Enclosure.dec_le_dec qz776 qz780 999236 1000 1000476 1000 (@Eq.refl Real qz776) (@Eq.refl Real qz780) rfl rfl rfl)

noncomputable abbrev qz565 := (RS589to600.d3 qz680 qz691 qz731)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz565)

noncomputable def Ns588p1927 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz168) Bool.true 23536802811599871075627 18889465931478580854784 Ns588p1196 Ns588p1197 

noncomputable abbrev qz566 := qz731

noncomputable abbrev qz290 := qz566

noncomputable def Ns588p1928 := @Enclosure.Real.IsNear.neg_val qz289 23536802811599871075627 18889465931478580854784 Ns588p1196 Ns588p1197 (Ns588p1927 (RS589to600.d4 qz168 qz185 qz290) RS589to600.d67) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz565)

noncomputable def Ns588p1929 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz185) Bool.false 23899940910116918436307 9444732965739290427392 50284629356024767056263 Ns588p1326 

noncomputable def Ns588p1930 := @Enclosure.Real.IsNear.pos_val qz291 23899940910116918436307 9444732965739290427392 50284629356024767056263 Ns588p1326 (Ns588p1929 (RS589to600.d58 qz168 qz185 qz290) RS589to600.d68) rfl 

noncomputable def Ns588p1931 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz168 989310 1000 999236 1000 

noncomputable def Ns588p1932 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 23536802811599871075627 18889465931478580854784 Ns588p1196 

noncomputable def Ns588p1933 := @Ns588p1932 Ns588p1197 434356701 10737418240 1213 10737418240 (Ns588p1927 (RS589to600.d4 qz168 qz185 qz290) RS589to600.d67) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable def Ns588p1934 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz185 989310 1000 1000476 1000 

noncomputable def Ns588p1935 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 23899940910116918436307 9444732965739290427392 50284629356024767056263 

noncomputable def Ns588p1936 := @Ns588p1935 Ns588p1326 434356701 10737418240 1213 10737418240 (Ns588p1929 (RS589to600.d58 qz168 qz185 qz290) RS589to600.d68) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz565

noncomputable def Ns588p1937 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz168 999236 1000 qz171 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns588p1928 rfl rfl) (Ns588p1930 rfl rfl)) (Ns588p1931 qz11 qz171 rfl rfl rfl rfl (Ns588p1933 rfl)) (Ns588p1934 qz11 qz188 rfl rfl rfl rfl (Ns588p1936 rfl)) 

noncomputable abbrev qz732 := (@Enclosure.dec_le_dec qz780 qz784 1000476 1000 1001715 1000 (@Eq.refl Real qz780) qz787 rfl rfl rfl)

noncomputable abbrev qz567 := (RS589to600.d3 qz691 qz701 qz732)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz567)

noncomputable def Ns588p1938 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz185) Bool.false 23899940910116918436307 9444732965739290427392 50284629356024767056263 Ns588p1326 

noncomputable abbrev qz568 := qz732

noncomputable abbrev qz294 := qz568

noncomputable def Ns588p1939 := @Enclosure.Real.IsNear.pos_val qz293 23899940910116918436307 9444732965739290427392 50284629356024767056263 Ns588p1326 (Ns588p1938 (RS589to600.d4 qz185 qz203 qz294) RS589to600.d68) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz567)

noncomputable def Ns588p1940 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz203) Bool.true 38470288980267409738949 37778931862957161709568 629450291317229779137 649325391394576216883200 

noncomputable def Ns588p1941 := @Enclosure.Real.IsNear.neg_val qz295 38470288980267409738949 37778931862957161709568 629450291317229779137 649325391394576216883200 (Ns588p1940 (RS589to600.d58 qz185 qz203 qz294) RS589to600.d69) rfl 

noncomputable def Ns588p1942 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz185 989310 1000 1000476 1000 

noncomputable def Ns588p1943 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 23899940910116918436307 9444732965739290427392 50284629356024767056263 

noncomputable def Ns588p1944 := @Ns588p1943 Ns588p1326 434356701 10737418240 1213 10737418240 (Ns588p1938 (RS589to600.d4 qz185 qz203 qz294) RS589to600.d68) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable def Ns588p1945 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz203 989310 1000 1001715 1000 

noncomputable def Ns588p1946 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 38470288980267409738949 37778931862957161709568 629450291317229779137 

noncomputable def Ns588p1947 := @Ns588p1946 649325391394576216883200 434356701 10737418240 1213 10737418240 (Ns588p1940 (RS589to600.d58 qz185 qz203 qz294) RS589to600.d69) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz567

noncomputable def Ns588p1948 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz185 1000476 1000 qz188 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns588p1939 rfl rfl) (Ns588p1941 rfl rfl)) (Ns588p1942 qz11 qz188 rfl rfl rfl rfl (Ns588p1944 rfl)) (Ns588p1945 qz11 qz206 rfl rfl rfl rfl (Ns588p1947 rfl)) 

noncomputable abbrev qz733 := (@Enclosure.dec_le_dec qz784 qz789 1001715 1000 1002953 1000 qz787 qz792 rfl rfl rfl)

noncomputable abbrev qz569 := (RS589to600.d3 qz701 qz711 qz733)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz569)

noncomputable def Ns588p1949 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz203) Bool.true 38470288980267409738949 37778931862957161709568 629450291317229779137 649325391394576216883200 

noncomputable abbrev qz570 := qz733

noncomputable abbrev qz298 := qz570

noncomputable def Ns588p1950 := @Enclosure.Real.IsNear.neg_val qz297 38470288980267409738949 37778931862957161709568 629450291317229779137 649325391394576216883200 (Ns588p1949 (RS589to600.d4 qz203 qz221 qz298) RS589to600.d69) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz569)

noncomputable def Ns588p1951 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz221) Bool.false 13020027385489107410341 18889465931478580854784 Ns588p1579 Ns588p1580 

noncomputable def Ns588p1952 := @Enclosure.Real.IsNear.pos_val qz299 13020027385489107410341 18889465931478580854784 Ns588p1579 Ns588p1580 (Ns588p1951 (RS589to600.d58 qz203 qz221 qz298) RS589to600.d70) rfl 

noncomputable def Ns588p1953 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz203 989310 1000 1001715 1000 

noncomputable def Ns588p1954 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 38470288980267409738949 37778931862957161709568 629450291317229779137 

noncomputable def Ns588p1955 := @Ns588p1954 649325391394576216883200 434356701 10737418240 1213 10737418240 (Ns588p1949 (RS589to600.d4 qz203 qz221 qz298) RS589to600.d69) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable def Ns588p1956 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz221 989310 1000 1002953 1000 

noncomputable def Ns588p1957 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 13020027385489107410341 18889465931478580854784 Ns588p1579 

noncomputable def Ns588p1958 := @Ns588p1957 Ns588p1580 434356701 10737418240 1213 10737418240 (Ns588p1951 (RS589to600.d58 qz203 qz221 qz298) RS589to600.d70) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz569

noncomputable def Ns588p1959 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz203 1001715 1000 qz206 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns588p1950 rfl rfl) (Ns588p1952 rfl rfl)) (Ns588p1953 qz11 qz206 rfl rfl rfl rfl (Ns588p1955 rfl)) (Ns588p1956 qz11 qz224 rfl rfl rfl rfl (Ns588p1958 rfl)) 

noncomputable abbrev qz799 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 1002953 1000) (Enclosure.sfrac Bool.false 1004192 1000) 1002953 1000 1004192 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 1002953 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 1004192 1000)) rfl rfl rfl)

noncomputable abbrev qz734 := qz799

noncomputable abbrev qz571 := (RS589to600.d3 qz711 qz721 qz734)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz571)

noncomputable def Ns588p1960 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz221) Bool.false 13020027385489107410341 18889465931478580854784 Ns588p1579 Ns588p1580 

noncomputable abbrev qz572 := qz734

noncomputable abbrev qz302 := qz572

noncomputable def Ns588p1961 := @Enclosure.Real.IsNear.pos_val qz301 13020027385489107410341 18889465931478580854784 Ns588p1579 Ns588p1580 (Ns588p1960 (RS589to600.d4 qz221 qz239 qz302) RS589to600.d70) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz571)

noncomputable def Ns588p1962 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz239) Bool.true 4308389913040770425399 2361183241434822606848 Ns588p1714 Ns588p1715 

noncomputable def Ns588p1963 := @Enclosure.Real.IsNear.neg_val qz303 4308389913040770425399 2361183241434822606848 Ns588p1714 Ns588p1715 (Ns588p1962 (RS589to600.d58 qz221 qz239 qz302) RS589to600.d71) rfl 

noncomputable def Ns588p1964 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz221 989310 1000 1002953 1000 

noncomputable def Ns588p1965 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 13020027385489107410341 18889465931478580854784 Ns588p1579 

noncomputable def Ns588p1966 := @Ns588p1965 Ns588p1580 434356701 10737418240 1213 10737418240 (Ns588p1960 (RS589to600.d4 qz221 qz239 qz302) RS589to600.d70) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable def Ns588p1967 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz239 989310 1000 1004192 1000 

noncomputable def Ns588p1968 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 4308389913040770425399 2361183241434822606848 Ns588p1714 

noncomputable def Ns588p1969 := @Ns588p1968 Ns588p1715 434356701 10737418240 1213 10737418240 (Ns588p1962 (RS589to600.d58 qz221 qz239 qz302) RS589to600.d71) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 434356701 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS589to600.d60) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz571

noncomputable def Ns588p1970 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz221 1002953 1000 qz224 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns588p1961 rfl rfl) (Ns588p1963 rfl rfl)) (Ns588p1964 qz11 qz224 rfl rfl rfl rfl (Ns588p1966 rfl)) (Ns588p1967 qz11 qz242 rfl rfl rfl rfl (Ns588p1969 rfl)) 

noncomputable def Ns588p1971 := @List.cons RS589to600.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns588p1959)) (@List.cons RS589to600.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns588p1970)) (@List.nil RS589to600.d0)) 

noncomputable def Ns588p1972 := @List.cons RS589to600.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns588p1937)) (@List.cons RS589to600.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns588p1948)) Ns588p1971) 

noncomputable def Ns588p1973 := @List.cons RS589to600.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns588p1915)) (@List.cons RS589to600.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns588p1926)) Ns588p1972) 

noncomputable def Ns588p1974 := @List.cons RS589to600.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns588p1893)) (@List.cons RS589to600.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns588p1904)) Ns588p1973) 

noncomputable def Ns588p1975 := @List.cons RS589to600.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns588p1871)) (@List.cons RS589to600.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns588p1882)) Ns588p1974) 

noncomputable def Ns588p1976 := @List.cons RS589to600.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns588p1849)) (@List.cons RS589to600.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns588p1860)) Ns588p1975) 

noncomputable abbrev qz573 := (RS589to600.d2 qz680 qz691 qz731)

noncomputable abbrev qz735 := (RS589to600.d2 qz784 qz789 (@Enclosure.dec_le_dec qz784 qz789 1001715 1000 1002953 1000 qz787 qz792 rfl rfl rfl))

noncomputable abbrev qz736 := (@List.cons RS589to600.d1 (RS589to600.d2 qz789 qz794 qz799) (@List.nil RS589to600.d1))

noncomputable abbrev qz574 := (@List.cons RS589to600.d1 (RS589to600.d2 qz691 qz701 qz732) (@List.cons RS589to600.d1 qz735 qz736))

noncomputable abbrev qz305 := (@List.cons RS589to600.d1 (RS589to600.d2 qz473 qz485 qz564) (@List.cons RS589to600.d1 qz573 qz574))

noncomputable def Ns588p1977 := @List.cons RS589to600.d1 (RS589to600.d2 qz116 qz134 qz278) (@List.cons RS589to600.d1 (RS589to600.d2 qz134 qz151 qz282) qz305) 

noncomputable abbrev qz306 := (RS589to600.d2 qz435 qz448 qz558)

noncomputable def Ns588p1978 := @List.IsChain.cons_cons RS589to600.d1 RS589to600.d72 qz306 (RS589to600.d2 qz116 qz134 qz278) (@List.cons RS589to600.d1 (RS589to600.d2 qz134 qz151 qz282) qz305) 

noncomputable def Ns588p1979 := @List.IsChain.cons_cons RS589to600.d1 RS589to600.d72 (RS589to600.d2 qz116 qz134 qz278) (RS589to600.d2 qz134 qz151 qz282) qz305 (@Enclosure.dec_le_dec qz134 qz134 996757 1000 996757 1000 qz137 qz137 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS589to600.d2 qz473 qz485 qz564)

noncomputable abbrev qz308 := qz573

noncomputable abbrev qz309 := qz574

noncomputable abbrev qz575 := (RS589to600.d2 qz691 qz701 qz732)

noncomputable abbrev qz310 := qz575

noncomputable abbrev qz576 := (@List.cons RS589to600.d1 qz735 qz736)

noncomputable abbrev qz311 := qz576

noncomputable abbrev qz577 := qz735

noncomputable abbrev qz312 := qz577

noncomputable abbrev qz578 := qz736

noncomputable abbrev qz313 := qz578

noncomputable abbrev qz737 := (RS589to600.d2 qz789 qz794 qz799)

noncomputable abbrev qz579 := qz737

noncomputable abbrev qz314 := qz579

noncomputable def Ns588p1980 := @List.IsChain.cons_cons RS589to600.d1 RS589to600.d72 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz168 qz168 999236 1000 999236 1000 qz171 qz171 rfl rfl rfl) (@List.IsChain.cons_cons RS589to600.d1 RS589to600.d72 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz185 qz185 1000476 1000 1000476 1000 qz188 qz188 rfl rfl rfl) (@List.IsChain.cons_cons RS589to600.d1 RS589to600.d72 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz203 qz203 1001715 1000 1001715 1000 qz206 qz206 rfl rfl rfl) (@List.IsChain.cons_cons RS589to600.d1 RS589to600.d72 qz312 qz314 (@List.nil RS589to600.d1) (@Enclosure.dec_le_dec qz221 qz221 1002953 1000 1002953 1000 qz224 qz224 rfl rfl rfl) (@List.IsChain.singleton RS589to600.d1 RS589to600.d72 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS589to600.d1 qz573 qz574)

noncomputable def Ns588p1981 := @List.IsChain.cons_cons RS589to600.d1 RS589to600.d72 (RS589to600.d2 qz134 qz151 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz151 qz151 997997 1000 997997 1000 qz154 qz154 rfl rfl rfl) Ns588p1980 

noncomputable def Ns588p1982 := @List.IsChain.cons_cons RS589to600.d1 RS589to600.d72 (RS589to600.d2 qz4 qz35 qz258) (RS589to600.d2 qz35 qz62 qz262) (@List.cons RS589to600.d1 (RS589to600.d2 qz62 qz80 qz266) (@List.cons RS589to600.d1 (RS589to600.d2 qz80 qz98 qz270) (@List.cons RS589to600.d1 qz306 Ns588p1977))) (@Enclosure.dec_le_dec qz35 qz35 990552 1000 990552 1000 qz38 qz38 rfl rfl rfl) (@List.IsChain.cons_cons RS589to600.d1 RS589to600.d72 (RS589to600.d2 qz35 qz62 qz262) (RS589to600.d2 qz62 qz80 qz266) (@List.cons RS589to600.d1 (RS589to600.d2 qz80 qz98 qz270) (@List.cons RS589to600.d1 qz306 Ns588p1977)) (@Enclosure.dec_le_dec qz62 qz62 991794 1000 991794 1000 qz65 qz65 rfl rfl rfl) (@List.IsChain.cons_cons RS589to600.d1 RS589to600.d72 (RS589to600.d2 qz62 qz80 qz266) (RS589to600.d2 qz80 qz98 qz270) (@List.cons RS589to600.d1 qz306 Ns588p1977) (@Enclosure.dec_le_dec qz80 qz80 993035 1000 993035 1000 qz83 qz83 rfl rfl rfl) (@List.IsChain.cons_cons RS589to600.d1 RS589to600.d72 (RS589to600.d2 qz80 qz98 qz270) qz306 Ns588p1977 (@Enclosure.dec_le_dec qz98 qz98 994276 1000 994276 1000 qz101 qz101 rfl rfl rfl) (Ns588p1978 (@Enclosure.dec_le_dec qz116 qz116 995516 1000 995516 1000 qz119 qz119 rfl rfl rfl) (Ns588p1979 Ns588p1981))))) 

noncomputable abbrev qz580 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz581 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns588p1976 Ns588p1982)

noncomputable abbrev qz582 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns588p1976 Ns588p1982))

theorem RS589to600.d73 : Zeta.Certificates.BatchSpec 12 989310 1000 1004192 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz580 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz580 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz580 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz580 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz580 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz239)))) qz581 (@And.intro (@Eq Nat (@List.length qz580 qz582) 12) (And (@Eq (Option Real) (@Option.map qz580 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz580 qz582)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz580 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz580 qz582)) (@Option.some Real qz239))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz580 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz580 qz582)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz580 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz580 qz582)) (@Option.some Real qz239)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz239))))

theorem solution : Zeta.Certificates.BatchSpec 12 989310 1000 1004192 1000 := RS589to600.d73
#print axioms solution
#check solution
