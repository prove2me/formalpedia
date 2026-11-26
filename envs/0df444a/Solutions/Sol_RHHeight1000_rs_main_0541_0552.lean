-- Prove2me | solution 1 for RHHeight1000.rs_main_0541_0552
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:05:46.094103+00:00
-- url     : https://prove2.me/submissions/90a9f540-124c-45b3-b8af-a4ba8d71475d

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

noncomputable def RS541to552.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS541to552.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS541to552.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS541to552.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS541to552.d2 a b h 

theorem RS541to552.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS541to552.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS541to552.d3 a b h)) 

noncomputable def Ns540p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns540p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns540p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns540p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns540p0 Ns540p1 Ns540p2 Ns540p1 614572177 536870912 1 153760000 614572177 536870912 1 153760000 307286088 268435456 3 268435456 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns540p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns540p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns540p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns540p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns540p8 := nat_lit 6573389678388862351155759458724141871788046104702795740939545775355827438482086890337971184306503456724674701876007739166027855002689342487126242201873902293161938510715598861337724155978462934346539722102807352693564004597780440630880721700532830491857281958381906437104026277614553345439647264822859384496062743250358046048880947907642984145065307980413206151384068885350206914057384338280179177725692904928360597982006748935836093248417685721122261418062303135764477585928239149568275027355236134745000697766005167655784166499502223346815249842007858448160935771607172549259242715110048115445292136446613946552506617916138661398090061483392335970316672263498462800198746102072055363920390651513279180731193678641632192805423820381724597815072905552156968003637925334143020171520625 

noncomputable def Ns540p9 := nat_lit 702614123509571190207434367497643053726389003684617183996726348470791223755418688598787599501240412886827946200799073391711533512528899996899108221816773619593298708861540359234024488137706935294538610329535191474811214152768697527793266408685885408431698677504366547635987768499962038530066773279961750661013789994039311989768445302208965109624014234440840481147386361324656837522786906307734587964680180646868573806366973424595907336814393861048013934514934272026683624090151873353554279683010347128413433843775162422864773798490322287367830744467164676975854073090397461536167654230134598982106570951920409048997311342333559851528447946435833392322432321465286801524775001800171249769824525762984779161997185015423416919065587459911326773695449510414365759468097615398764501522575 

noncomputable def Ns540p10 := nat_lit 541392566138474909591412279139378993255101875047003589935782329109463644892392322173295519240510467068363239080443023466297029982601757003829684821059136286585994161974307047499333049696728682047261006046816072264069316416942594393775486731411634963656291648112663555457379375292741727868294229136381639619442405391741167595634732196900940186574903289828257139713673376723681752760045249773972946001592268830432998579610986951410273979009689762628244990479410235165324966379611071762421902787196495466840333515349387051622842182127210560393625584510287605139387730811840242457253978115925211125629993337408355023684205061830608267784338105681114876710224147942516826039256450164994945245879666660679160980454641866547806615379410050641833332584350523565507268843323231339375 

noncomputable def Ns540p11 := BSN.log_dyadic_bound Ns540p6 Ns540p7 16 15 Ns540p8 536870912 153760000 Ns540p9 Ns540p10 614572177 Ns540p4 Ns540p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns540p6) (BSN.artanhQ Ns540p7) 0 15 Ns540p9 Ns540p8 Ns540p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns540p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns540p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns540p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns540p15 := nat_lit 6573389678388957581038003304946500209472262679236338533996718496177406624059139082449994147026037314666926693076053053862592074936423388863596813530408382584499373597031431853921413941298322255656576695489433951602693567143885654771592106690789036275646003378131729522606930818530515414843848039000889531334935427389830473690579523667466182538201372727149023132371319359578146651783732835416323469915494090659780509855937937675396353734377829186029766969614606089327824892671842834136516654569045504808111725705550748907924941183733134599012581542910476929082687043869700761244349471219210833189555347464155979117619898077496880661665775336657207488512148128426326823595335945176245554694022845325705851563290369414226074229552025260849280553835909109839168582914725334143020171520625 

noncomputable def Ns540p16 := nat_lit 702614123509582134195699383225799303120857312948289364169564431944606347230839067212220070086773571232938822231607515388838247088164426860334641427891924556959013106220289292017417932077264689683982462259236603120411894481357554273197237433243865910367073588753830073256225145709268648257922640132615276470163987114280905050307903018021985933333474523803420109333064989110261463867307642914581311357336787925252212965840242792007601256472655504246146516404729632839909377990937267835233434162343951883521915890115762575574377037535717851480622294463860980162526686236248764915916362237196611189536095144270945605478817014333998082847306947436470576941659846222535334992451365706225994338058508887942119777908276510373758951874822816373072605980596581754554466975502415398764501522575 

noncomputable def Ns540p17 := nat_lit 541392566138490077533790984620311058177654278555980714203107761719673916425133183846751239616284470803704371181920004286935467360846628369375164068764590875438310007353955324186636582299553928814156491749519256774653872128089233575343481607925575468185460509172779152955629338248076232826253005811067688706928164570779608774451502836676056177667078421728722179008027603013170304530594440809888606240685402729798990208830923560422594844623819537735750113690675240496626214395332044296593456069970973486809806367897564108502902289348063943342100923856630472249952347312756547637419241376870243223562839253667975765230153074010838184467350558565952691487980795548332122966513692688198426849374346091985539852378055886379210372820263137502377721028428076000707268843323231339375 

noncomputable def Ns540p18 := BSN.log_dyadic_bound Ns540p13 Ns540p14 16 15 Ns540p15 536870912 153760000 Ns540p16 Ns540p17 614572177 Ns540p12 Ns540p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns540p13) (BSN.artanhQ Ns540p14) 0 15 Ns540p16 Ns540p15 Ns540p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns540p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 307286088 268435456 3 268435456 38410761 33554432 3 268435456 (Ns540p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns540p0 Ns540p1 614572177 536870912 1 153760000 Bool.false (BSN.logfrac_isNear Ns540p4 Ns540p5 1 Ns540p0 Ns540p1 614572177 536870912 153760000 rfl rfl rfl (Ns540p11 rfl))) (BSN.isNear_log_sfrac Ns540p2 Ns540p1 614572177 536870912 1 153760000 Bool.false (BSN.logfrac_isNear Ns540p12 Ns540p5 1 Ns540p2 Ns540p1 614572177 536870912 153760000 rfl rfl rfl (Ns540p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS541to552.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 3 268435456 := Ns540p19 

noncomputable def Ns540p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 33554432 9610000 385100712855 135135 23258159 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz316

theorem RS541to552.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 23258159 33554432 1 9610000 := BSN.isNear_log_sfrac 2 1 23258159 33554432 1 9610000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 23258159 33554432 9610000 rfl rfl rfl (Ns540p20 rfl)) 

theorem RS541to552.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 372130544 536870912 56 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 23258159 33554432 1 9610000 372130544 536870912 56 536870912 RS541to552.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz575 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz575

noncomputable def Ns540p21 := @Enclosure.Real.IsNear.inv_image qz317 94906265 67108864 1 67108864 23726566 23726567 33554432 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 94906265 67108864 1 67108864 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 94906265 67108864 1 67108864 94906265 67108864 1 67108864 (BSN.sqrt_enclosure 2 1 47453132 47453133 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS541to552.d8 : Enclosure.Real.IsNear qz320 Bool.false 47453133 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 47453133 67108864 1 67108864 47453133 67108864 1 67108864 (Ns540p21 rfl rfl) rfl 

theorem RS541to552.d9 : Enclosure.Real.IsNear qz320 Bool.false 379625064 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 47453133 67108864 1 67108864 379625064 536870912 8 536870912 RS541to552.d8 rfl 

noncomputable def Ns540p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 33554432 9610000 13079757671720842725 316234143225 36863311 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS541to552.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 36863311 33554432 1 9610000 := BSN.isNear_log_sfrac 3 1 36863311 33554432 1 9610000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 36863311 33554432 9610000 rfl rfl rfl (Ns540p22 rfl)) 

theorem RS541to552.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 589812976 536870912 56 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 36863311 33554432 1 9610000 589812976 536870912 56 536870912 RS541to552.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns540p23 := @Enclosure.Real.IsNear.inv_image qz321 116235963 67108864 1 67108864 19372660 19372661 33554432 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 116235963 67108864 1 67108864 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 116235963 67108864 1 67108864 116235963 67108864 1 67108864 (BSN.sqrt_enclosure 3 1 58117981 58117982 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS541to552.d12 : Enclosure.Real.IsNear qz323 Bool.false 38745321 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 38745321 67108864 1 67108864 38745321 67108864 1 67108864 (Ns540p23 rfl rfl) rfl 

theorem RS541to552.d13 : Enclosure.Real.IsNear qz323 Bool.false 309962568 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 38745321 67108864 1 67108864 309962568 536870912 8 536870912 RS541to552.d12 rfl 

noncomputable def Ns540p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns540p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns540p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns540p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns540p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns540p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns540p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns540p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns540p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns540p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns540p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns540p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns540p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns540p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns540p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns540p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns540p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns540p25 Ns540p26 Ns540p27 Ns540p28 200200021673987500790625 Ns540p29 Ns540p30 Ns540p31 Ns540p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns540p32 Ns540p33 151412625 Ns540p34 Ns540p35 1322214852783825 Ns540p27 Ns540p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns540p32 Ns540p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns540p34 Ns540p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns540p36 Ns540p37 1267389585 Ns540p38 Ns540p39 1927077560082675 Ns540p29 Ns540p30 Ns540p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns540p36 Ns540p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns540p38 Ns540p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS541to552.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns540p24 Ns540p25 1 Ns540p26 := Ns540p40 rfl rfl rfl 

noncomputable def Ns540p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns540p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns540p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns540p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns540p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns540p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns540p25 Ns540p26 Ns540p42 Ns540p43 9945 Ns540p44 Ns540p45 65835 Ns540p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns540p42 Ns540p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns540p44 Ns540p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS541to552.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns540p41 Ns540p25 1 Ns540p26 := Ns540p46 rfl 

noncomputable def Ns540p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns540p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS541to552.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns540p47 Ns540p25 1 Ns540p48 := BSN.pi_combine Ns540p24 Ns540p41 Ns540p25 Ns540p26 Ns540p48 Ns540p47 rfl rfl rfl rfl RS541to552.d14 RS541to552.d15 

theorem RS541to552.d17 : Enclosure.Real.IsNear Real.pi Bool.false 28296951008113761 9007199254740992 1 9007199254740992 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns540p47 Ns540p25 1 Ns540p48 28296951008113761 9007199254740992 1 9007199254740992 RS541to552.d16 rfl 

noncomputable def Ns540p49 := nat_lit 129013261453190219981479458510875701904296875 

noncomputable def Ns540p50 := nat_lit 20028702544022979302942508184499384445755625 

noncomputable def Ns540p51 := nat_lit 105610919306899072369715234453255625 

noncomputable def Ns540p52 := nat_lit 11743816085855617508865225 

noncomputable def Ns540p53 := nat_lit 24536140990734100341796875 

noncomputable def Ns540p54 := BSN.log_dyadic_bound 3 5 18 17 Ns540p49 33554432 9610000 Ns540p50 Ns540p51 46516319 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 3) (BSN.artanhQ 5) 0 17 8 816252149187356400 5258090972900390625 87256779635025 Ns540p52 Ns540p53 1210346287688420415225 Ns540p50 Ns540p49 Ns540p51 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 3) (BSN.artanhQ 5) 0 8 816252149187356400 5258090972900390625 87256779635025 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 3) (BSN.artanhQ 5) 8 17 Ns540p52 Ns540p53 1210346287688420415225 rfl rfl rfl rfl)) rfl rfl 

theorem RS541to552.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 46516319 33554432 1 9610000 := BSN.isNear_log_sfrac 4 1 46516319 33554432 1 9610000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 46516319 33554432 9610000 rfl rfl rfl (Ns540p54 rfl rfl)) 

theorem RS541to552.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 744261104 536870912 56 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 46516319 33554432 1 9610000 744261104 536870912 56 536870912 RS541to552.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns540p55 := @Enclosure.Real.IsNear.inv_image qz325 134217729 67108864 1 67108864 16777215 16777216 33554432 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 134217729 67108864 1 67108864 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 134217729 67108864 1 67108864 134217729 67108864 1 67108864 (BSN.sqrt_enclosure 4 1 67108864 67108865 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS541to552.d20 : Enclosure.Real.IsNear qz327 Bool.false 33554431 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 33554431 67108864 1 67108864 33554431 67108864 1 67108864 (Ns540p55 rfl rfl) rfl 

theorem RS541to552.d21 : Enclosure.Real.IsNear qz327 Bool.false 268435448 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 33554431 67108864 1 67108864 268435448 536870912 8 536870912 RS541to552.d20 rfl 

noncomputable def Ns540p56 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns540p57 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns540p58 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns540p59 := nat_lit 885951608314392539099884620 

noncomputable def Ns540p60 := nat_lit 1286943652057122751813246125 

noncomputable def Ns540p61 := BSN.log_dyadic_bound 2 3 22 21 Ns540p56 33554432 9610000 Ns540p57 Ns540p58 54003774 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns540p59 Ns540p60 84004523356416638976000 Ns540p57 Ns540p56 Ns540p58 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns540p59 Ns540p60 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS541to552.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 54003774 33554432 1 9610000 := BSN.isNear_log_sfrac 5 1 54003774 33554432 1 9610000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 54003774 33554432 9610000 rfl rfl rfl (Ns540p61 rfl rfl)) 

theorem RS541to552.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 864060384 536870912 56 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 54003774 33554432 1 9610000 864060384 536870912 56 536870912 RS541to552.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns540p62 := @Enclosure.Real.IsNear.inv_image qz328 150059981 67108864 1 67108864 15005998 15005999 33554432 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 150059981 67108864 1 67108864 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 150059981 67108864 1 67108864 150059981 67108864 1 67108864 (BSN.sqrt_enclosure 5 1 75029990 75029991 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS541to552.d24 : Enclosure.Real.IsNear qz329 Bool.false 30011997 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 30011997 67108864 1 67108864 30011997 67108864 1 67108864 (Ns540p62 rfl rfl) rfl 

theorem RS541to552.d25 : Enclosure.Real.IsNear qz329 Bool.false 240095976 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 30011997 67108864 1 67108864 240095976 536870912 8 536870912 RS541to552.d24 rfl 

noncomputable def Ns540p63 := nat_lit 2166104270535356806332416 

noncomputable def Ns540p64 := nat_lit 1208925819614629174706176 

noncomputable def Ns540p65 := BSN.log_dyadic_bound 2 10 6 5 103950000000000 33554432 9610000 1420244935680 967680 13605151 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 2) (BSN.artanhQ 10) 0 5 1420244935680 103950000000000 967680 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz575)

theorem RS541to552.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683612241143 2251799813685248 50000000961 480500000000000000 := BSN.isNear_log_sfrac 6 1 4034683612241143 2251799813685248 50000000961 480500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false Ns540p63 Ns540p64 1000000019220000 9610000000000000000000 4034683612241143 2251799813685248 50000000961 480500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 13605151 33554432 24973259072661432 36028797018963968 9610000 1000000000000000 rfl rfl rfl rfl (Ns540p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS541to552.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 961943533 536870912 57 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683612241143 2251799813685248 50000000961 480500000000000000 961943533 536870912 57 536870912 RS541to552.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns540p66 := @Enclosure.Real.IsNear.inv_image qz331 164382475 67108864 1 67108864 13698539 13698540 33554432 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 164382475 67108864 1 67108864 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 164382475 67108864 1 67108864 164382475 67108864 1 67108864 (BSN.sqrt_enclosure 6 1 82191237 82191238 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS541to552.d28 : Enclosure.Real.IsNear qz332 Bool.false 27397079 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 27397079 67108864 1 67108864 27397079 67108864 1 67108864 (Ns540p66 rfl rfl) rfl 

theorem RS541to552.d29 : Enclosure.Real.IsNear qz332 Bool.false 219176632 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 27397079 67108864 1 67108864 219176632 536870912 8 536870912 RS541to552.d28 rfl 

noncomputable def Ns540p67 := nat_lit 2352460989330532755046400 

noncomputable def Ns540p68 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 33554432 9610000 11010900719820672 5524329195 18777589 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz575)

theorem RS541to552.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381800050531575 2251799813685248 50000000961 480500000000000000 := BSN.isNear_log_sfrac 7 1 4381800050531575 2251799813685248 50000000961 480500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false Ns540p67 Ns540p64 1000000019220000 9610000000000000000000 4381800050531575 2251799813685248 50000000961 480500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 18777589 33554432 24973259072661432 36028797018963968 9610000 1000000000000000 rfl rfl rfl rfl (Ns540p68 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS541to552.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 1044702541 536870912 57 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381800050531575 2251799813685248 50000000961 480500000000000000 1044702541 536870912 57 536870912 RS541to552.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns540p69 := @Enclosure.Real.IsNear.inv_image qz334 177553365 67108864 1 67108864 12682383 12682384 33554432 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 177553365 67108864 1 67108864 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 177553365 67108864 1 67108864 177553365 67108864 1 67108864 (BSN.sqrt_enclosure 7 1 88776682 88776683 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS541to552.d32 : Enclosure.Real.IsNear qz335 Bool.false 25364767 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 25364767 67108864 1 67108864 25364767 67108864 1 67108864 (Ns540p69 rfl rfl) rfl 

theorem RS541to552.d33 : Enclosure.Real.IsNear qz335 Bool.false 202918136 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 25364767 67108864 1 67108864 202918136 536870912 8 536870912 RS541to552.d32 rfl 

noncomputable def Ns540p70 := nat_lit 2513890570116003237199872 

noncomputable def Ns540p71 := BSN.log_dyadic_bound 0 16 1 0 1 33554432 9610000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz575)

theorem RS541to552.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000002883 961000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000002883 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false Ns540p70 Ns540p64 1000000028830000 9610000000000000000000 9364972152248037 4503599627370496 100000002883 961000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 33554432 24973259072661432 36028797018963968 9610000 1000000000000000 rfl rfl rfl rfl (Ns540p71 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS541to552.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 1116391676 536870912 57 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000002883 961000000000000000 1116391676 536870912 57 536870912 RS541to552.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns540p72 := @Enclosure.Real.IsNear.inv_image qz337 189812531 67108864 1 67108864 11863283 11863284 33554432 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 189812531 67108864 1 67108864 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 189812531 67108864 1 67108864 189812531 67108864 1 67108864 (BSN.sqrt_enclosure 8 1 94906265 94906266 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS541to552.d36 : Enclosure.Real.IsNear qz338 Bool.false 23726567 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 23726567 67108864 1 67108864 23726567 67108864 1 67108864 (Ns540p72 rfl rfl) rfl 

theorem RS541to552.d37 : Enclosure.Real.IsNear qz338 Bool.false 189812536 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 23726567 67108864 1 67108864 189812536 536870912 8 536870912 RS541to552.d36 rfl 

noncomputable def Ns540p73 := nat_lit 2656281492024125531619328 

noncomputable def Ns540p74 := BSN.log_dyadic_bound 1 17 3 2 1252815 33554432 9610000 1448 3 3952142 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz575)

theorem RS541to552.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 100000002883 961000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 100000002883 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false Ns540p73 Ns540p64 1000000028830000 9610000000000000000000 9895419672221413 4503599627370496 100000002883 961000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 3952142 33554432 24973259072661432 36028797018963968 9610000 1000000000000000 rfl rfl rfl rfl (Ns540p74 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS541to552.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 1179625948 536870912 57 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 100000002883 961000000000000000 1179625948 536870912 57 536870912 RS541to552.d38 rfl 

noncomputable abbrev qz340 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns540p75 := @Enclosure.Real.IsNear.inv_image qz340 201326593 67108864 1 67108864 11184810 11184811 33554432 (@Enclosure.Real.IsNear.of_eq qz340 (Real.sqrt qz339) Bool.false 201326593 67108864 1 67108864 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 201326593 67108864 1 67108864 201326593 67108864 1 67108864 (BSN.sqrt_enclosure 9 1 100663296 100663297 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS541to552.d40 : Enclosure.Real.IsNear qz341 Bool.false 22369621 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 22369621 67108864 1 67108864 22369621 67108864 1 67108864 (Ns540p75 rfl rfl) rfl 

theorem RS541to552.d41 : Enclosure.Real.IsNear qz341 Bool.false 178956968 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 22369621 67108864 1 67108864 178956968 536870912 8 536870912 RS541to552.d40 rfl 

noncomputable def Ns540p76 := nat_lit 2783654566499630094221312 

noncomputable def Ns540p77 := BSN.log_dyadic_bound 2 18 4 3 3571283520 33554432 9610000 14806464 960 7487455 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz575)

theorem RS541to552.d42 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921350850277 4503599627370496 100000002883 961000000000000000 := BSN.isNear_log_sfrac 10 1 10369921350850277 4503599627370496 100000002883 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false Ns540p76 Ns540p64 1000000028830000 9610000000000000000000 10369921350850277 4503599627370496 100000002883 961000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 7487455 33554432 24973259072661432 36028797018963968 9610000 1000000000000000 rfl rfl rfl rfl (Ns540p77 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS541to552.d43 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 1236190956 536870912 57 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921350850277 4503599627370496 100000002883 961000000000000000 1236190956 536870912 57 536870912 RS541to552.d42 rfl 

noncomputable abbrev qz343 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns540p78 := @Enclosure.Real.IsNear.inv_image qz343 212216861 67108864 1 67108864 10610843 10610844 33554432 (@Enclosure.Real.IsNear.of_eq qz343 (Real.sqrt qz342) Bool.false 212216861 67108864 1 67108864 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz342) Bool.false 212216861 67108864 1 67108864 212216861 67108864 1 67108864 (BSN.sqrt_enclosure 10 1 106108430 106108431 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz344 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS541to552.d44 : Enclosure.Real.IsNear qz344 Bool.false 21221687 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz344 Bool.false 21221687 67108864 1 67108864 21221687 67108864 1 67108864 (Ns540p78 rfl rfl) rfl 

theorem RS541to552.d45 : Enclosure.Real.IsNear qz344 Bool.false 169773496 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz344 Bool.false 21221687 67108864 1 67108864 169773496 536870912 8 536870912 RS541to552.d44 rfl 

noncomputable def Ns540p79 := nat_lit 2898877505641241362038784 

noncomputable def Ns540p80 := BSN.log_dyadic_bound 3 19 5 4 16049467073745 33554432 9610000 135406373544 688905 10685534 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 19) 0 4 135406373544 16049467073745 688905 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11) qz575)

theorem RS541to552.d46 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 10799160248194789 4503599627370496 100000002883 961000000000000000 := BSN.isNear_log_sfrac 11 1 10799160248194789 4503599627370496 100000002883 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false Ns540p79 Ns540p64 1000000028830000 9610000000000000000000 10799160248194789 4503599627370496 100000002883 961000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 10685534 33554432 24973259072661432 36028797018963968 9610000 1000000000000000 rfl rfl rfl rfl (Ns540p80 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS541to552.d47 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 1287360220 536870912 57 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 10799160248194789 4503599627370496 100000002883 961000000000000000 1287360220 536870912 57 536870912 RS541to552.d46 rfl 

noncomputable abbrev qz346 := (Real.sqrt (@Nat.cast Real Real.instNatCast 11))

noncomputable def Ns540p81 := @Enclosure.Real.IsNear.inv_image qz346 222574921 67108864 1 67108864 10117041 10117042 33554432 (@Enclosure.Real.IsNear.of_eq qz346 (Real.sqrt qz345) Bool.false 222574921 67108864 1 67108864 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz345) Bool.false 222574921 67108864 1 67108864 222574921 67108864 1 67108864 (BSN.sqrt_enclosure 11 1 111287460 111287461 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz347 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

theorem RS541to552.d48 : Enclosure.Real.IsNear qz347 Bool.false 20234083 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz347 Bool.false 20234083 67108864 1 67108864 20234083 67108864 1 67108864 (Ns540p81 rfl rfl) rfl 

theorem RS541to552.d49 : Enclosure.Real.IsNear qz347 Bool.false 161872664 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz347 Bool.false 20234083 67108864 1 67108864 161872664 536870912 8 536870912 RS541to552.d48 rfl 

noncomputable def Ns540p82 := nat_lit 3004067793907357885399040 

noncomputable def Ns540p83 := BSN.log_dyadic_bound 4 20 6 5 106444800000000000 33554432 9610000 1454330814136320 990904320 13605151 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 4) (BSN.artanhQ 20) 0 5 1454330814136320 106444800000000000 990904320 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz716 := (Enclosure.sfrac Bool.false 12 1)

noncomputable abbrev qz576 := qz716

noncomputable abbrev qz348 := qz576

noncomputable abbrev qz1 := qz348

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12) qz575)

theorem RS541to552.d50 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 11191024608564965 4503599627370496 100000002883 961000000000000000 := BSN.isNear_log_sfrac 12 1 11191024608564965 4503599627370496 100000002883 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz349) Bool.false Ns540p82 Ns540p64 1000000028830000 9610000000000000000000 11191024608564965 4503599627370496 100000002883 961000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 13605151 33554432 24973259072661432 36028797018963968 9610000 1000000000000000 rfl rfl rfl rfl (Ns540p83 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS541to552.d51 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 1334074092 536870912 57 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 11191024608564965 4503599627370496 100000002883 961000000000000000 1334074092 536870912 57 536870912 RS541to552.d50 rfl 

noncomputable abbrev qz350 := (Real.sqrt (@Nat.cast Real Real.instNatCast 12))

noncomputable def Ns540p84 := @Enclosure.Real.IsNear.inv_image qz350 232471925 67108864 1 67108864 9686330 9686331 33554432 (@Enclosure.Real.IsNear.of_eq qz350 (Real.sqrt qz349) Bool.false 232471925 67108864 1 67108864 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz349) Bool.false 232471925 67108864 1 67108864 232471925 67108864 1 67108864 (BSN.sqrt_enclosure 12 1 116235962 116235963 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz351 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))

theorem RS541to552.d52 : Enclosure.Real.IsNear qz351 Bool.false 19372661 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz351 Bool.false 19372661 67108864 1 67108864 19372661 67108864 1 67108864 (Ns540p84 rfl rfl) rfl 

theorem RS541to552.d53 : Enclosure.Real.IsNear qz351 Bool.false 154981288 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz351 Bool.false 19372661 67108864 1 67108864 154981288 536870912 8 536870912 RS541to552.d52 rfl 

theorem RS541to552.d54 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz717 := (@instHMul Real Real.instMul)

noncomputable abbrev qz577 := (@HMul.hMul Real Real Real qz717 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz352 := qz577

noncomputable abbrev qz2 := qz352

theorem RS541to552.d55 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS541to552.d54 rfl 

noncomputable abbrev qz353 := (@Inv.inv Real Real.instInv qz577)

noncomputable abbrev qz3 := qz353

theorem RS541to552.d56 : Enclosure.Real.IsNear qz3 Bool.false 10680707 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 10680707 67108864 1 67108864 10680707 67108864 1 67108864 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 5340353 5340354 33554432 RS541to552.d55 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns540p85 := nat_lit 18140446675227174740999337 

noncomputable def Ns540p86 := nat_lit 18152776760150916201447424000 

noncomputable def Ns540p87 := nat_lit 11424940202536982123278764081152 

noncomputable abbrev qz718 := (Enclosure.sfrac Bool.false 929330 1000)

noncomputable abbrev qz578 := qz718

noncomputable abbrev qz354 := qz578

noncomputable abbrev qz4 := qz354

noncomputable abbrev qz579 := qz717

noncomputable abbrev qz355 := qz579

noncomputable abbrev qz5 := qz355

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 12)

noncomputable abbrev qz356 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz719 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 929330 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz580 := qz719

noncomputable abbrev qz357 := qz580

noncomputable abbrev qz358 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz7 := (@HPow.hPow Real Real Real qz356 qz357 qz358)

noncomputable abbrev qz720 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 929330 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz581 := qz720

noncomputable abbrev qz359 := qz581

noncomputable abbrev qz8 := qz359

noncomputable def Ns540p88 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8)) 63891841 67108864 33399 33554432 26373239928266570869725 151115727451828646838272 71757835187192833031337 Ns540p86 Ns540p87 

noncomputable def Ns540p89 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos BSN.quadSignPos 11 12 929330 1000 288 536870912 268435456 9007199254740992 Bool.false 996798206349 4425 1334074092 57 154981288 8 

noncomputable def Ns540p90 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 929330 1000 180 236 536870912 268435456 9007199254740992 Bool.false 996798206349 4425 

noncomputable def Ns540p91 := Ns540p90 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 641392671 215137 Bool.true 234460614 Bool.true 561960761 28296951008113761 1 Bool.false 486482986 Bool.false Bool.false 268651191 Bool.false Bool.true 406551859 

noncomputable def Ns540p92 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 929330 1000 48 117 536870912 268435456 9007199254740992 Bool.false 996798206349 4425 

noncomputable def Ns540p93 := Ns540p92 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 637382093 175692 Bool.true 218956794 Bool.true 795737691 28296951008113761 1 Bool.false 492836840 Bool.false Bool.false 534764161 Bool.true Bool.true 641392671 

noncomputable def Ns540p94 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 929330 1000 121 30 536870912 268435456 9007199254740992 Bool.false 996798206349 4425 

noncomputable def Ns540p95 := Ns540p94 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 338985797 130546 Bool.false 794125185 Bool.false 625348225 28296951008113761 1 Bool.false 534619037 Bool.true Bool.false 212027826 Bool.true Bool.true 637382093 

noncomputable def Ns540p96 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 929330 1000 361 229 536870912 268435456 9007199254740992 Bool.false 996798206349 4425 

noncomputable def Ns540p97 := Ns540p96 744261104 56 268435448 8 864060384 56 240095976 8 Bool.false 148913593 77039 Bool.false 697371360 Bool.false 681867540 28296951008113761 1 Bool.false 517156059 Bool.true Bool.false 512778156 Bool.true Bool.true 338985797 

noncomputable def Ns540p98 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 929330 1000 771 532 536870912 268435456 9007199254740992 Bool.false 996798206349 4425 

noncomputable def Ns540p99 := Ns540p98 372130544 56 379625064 8 589812976 56 309962568 8 Bool.true 536870904 4488 Bool.false 770373506 Bool.false 23809687 28296951008113761 1 Bool.false 531923482 Bool.false Bool.false 536343030 Bool.false Bool.false 148913593 

noncomputable def Ns540p100 := nat_lit 19391873430232703471784834669794815172893891792831271 

noncomputable def Ns540p101 := nat_lit 10444373502641615006612090166316599062546507366400 

noncomputable def Ns540p102 := nat_lit 1574502400000000000000000 

noncomputable def Ns540p103 := nat_lit 332729525544264562106762864000000000 

noncomputable def Ns540p104 := nat_lit 1855293430466818273070133600966720000000 

noncomputable abbrev qz360 := (@Eq.refl Real qz578)

noncomputable abbrev qz9 := qz360

noncomputable def Ns540p105 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 929330 1000 3454617995600 16000000 1858660 4000 2000 Ns540p103 Ns540p104 qz9 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns540p106 := nat_lit 6205399497674465110971147094334340855326045373706006720000000 

noncomputable abbrev qz721 := (@instHSub Real Real.instSub)

noncomputable abbrev qz582 := qz721

noncomputable abbrev qz361 := qz582

noncomputable abbrev qz583 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz722 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz723 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz584 := (@HSub.hSub Real Real Real qz721 qz722 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz723 (@Nat.cast Real Real.instNatCast 1858660))))

noncomputable abbrev qz362 := (@HSub.hSub Real Real Real qz582 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 929330 4000) (Real.log (Enclosure.sfrac Bool.false 3454617995600 16000000))) (@HMul.hMul Real Real Real qz579 qz583 qz584))

noncomputable abbrev qz585 := (Enclosure.sfrac Bool.false 929330 2000)

noncomputable abbrev qz10 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz362 qz585) (@HMul.hMul Real Real Real qz355 qz585 (Real.log Real.pi)))

noncomputable def Ns540p107 := @Enclosure.Real.IsNear.addLit_ft_p qz10 (Enclosure.sfrac Bool.true Ns540p103 Ns540p104) 3344700086339078393251 1801439850948198400 12975583542322825091 Ns540p102 Ns540p103 Ns540p104 0 1 Ns540p106 

noncomputable def Ns540p108 := nat_lit 22445902321491746977801987686400 

noncomputable abbrev qz11 := (@HSub.hSub Real Real Real qz361 qz362 qz585)

noncomputable def Ns540p109 := @Enclosure.Real.IsNear.subLit_ff_p qz11 (@HMul.hMul Real Real Real qz5 qz585 (Real.log Real.pi)) 4302914605483214966179 1801439850948198400 1171664018294471 384400000000000000000 3569627252013 6710886400 278799 53687091200 Ns540p108 3344700086339078393251 1801439850948198400 

noncomputable def Ns540p110 := nat_lit 1721165842193285986471600 

noncomputable abbrev qz12 := qz362

noncomputable def Ns540p111 := @Enclosure.Real.IsNear.subLit_ff_p qz12 qz585 1027996130764811915143 360287970189639680 1171664018294471 384400000000000000000 929330 2000 0 1 Ns540p110 4302914605483214966179 1801439850948198400 1171664018294471 384400000000000000000 

noncomputable def Ns540p112 := nat_lit 2314841495725359310113505103486910464 

noncomputable def Ns540p113 := nat_lit 118790344288580731026800640 

noncomputable def Ns540p114 := nat_lit 9671406556917033397649408 

noncomputable def Ns540p115 := nat_lit 115863176536306064547583955184197435012353291719106923720053719921163095688586932844186159344592163399618290217634167787361483997839360000000000000000000000000 

noncomputable def Ns540p116 := nat_lit 2395510299876717185029492059002086818961929257734722632059783786595471874554130465274103091822896851673793839013941338168944589012992000000000000000000000000 

noncomputable def Ns540p117 := nat_lit 406979005297041695591414094958463684067561455578586888620087646506442395922671967616458487907694975747051295384080625665310720000000000000000000000000 

noncomputable def Ns540p118 := BSN.log_dyadic_bound 1357465995600 5551769995600 7 6 Ns540p115 268435456 76880000 Ns540p116 Ns540p117 133984632 6909235991200 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1357465995600) (BSN.artanhQ 5551769995600) 0 6 Ns540p116 Ns540p115 Ns540p117 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz363 := (Real.log (Enclosure.sfrac Bool.false 3454617995600 16000000))

noncomputable abbrev qz364 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns540p119 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 929330 4000) qz363 929330 4000 0 1 55316064641150055 4503599627370496 12500016337 961000000000000000 1028137567059199612263 360287970189639680 1161664018246421 384400000000000000000 (Enclosure.Real.IsNear.const Bool.false 929330 4000) (BSN.isNear_log_sfrac 3454617995600 16000000 55316064641150055 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3454617995600) qz364)) Bool.false Ns540p113 Ns540p114 1000001306960000 76880000000000000000000 55316064641150055 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3454617995600 16000000 17 6909235991200 4194304000000 133984632 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns540p118 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p120 := BSN.arctan_dyadic_bound_f 1000 1858660 1 0 33554432 9610000 0 1 1 0 1 1 18053 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1858660) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1858660) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz586 := qz722

noncomputable abbrev qz365 := qz586

noncomputable abbrev qz13 := qz365

noncomputable abbrev qz587 := qz723

noncomputable abbrev qz366 := qz587

noncomputable abbrev qz14 := qz366

noncomputable abbrev qz724 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz588 := qz724

noncomputable abbrev qz367 := qz588

noncomputable abbrev qz15 := (@Enclosure.Real.IsNear.mulLit_ff qz367 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz368 := (@Nat.cast Real Real.instNatCast 1858660)

noncomputable def Ns540p121 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz368)) 884279719003555 562949953421312 1 2000000000000000 18053 33554432 1 9610000 29661340764774779060224 883976839923107 562949953421312 200000000961 1922000000000000000 qz15 (Ns540p120 rfl) rfl rfl 

noncomputable abbrev qz369 := (@HMul.hMul Real Real Real qz579 qz583 qz584)

noncomputable abbrev qz16 := qz369

noncomputable abbrev qz370 := qz583

noncomputable abbrev qz17 := qz370

noncomputable abbrev qz371 := qz584

noncomputable abbrev qz18 := qz371

noncomputable abbrev qz372 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns540p122 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 929330 4000) qz363) qz16 1028137567059199612263 360287970189639680 1161664018246421 384400000000000000000 883976839923107 2251799813685248 200000000961 7688000000000000000 Ns540p112 1027996130764811915143 360287970189639680 1171664018294471 384400000000000000000 (Ns540p119 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz18 1 4 0 1 883976839923107 562949953421312 200000000961 1922000000000000000 883976839923107 2251799813685248 200000000961 7688000000000000000 qz372 Ns540p121 rfl) 

noncomputable def Ns540p123 := @Ns540p107 Ns540p100 Ns540p101 12975583542322825091 Ns540p102 (@Ns540p109 12975583542322825091 Ns540p102 (Ns540p111 (Ns540p122 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 929330 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz585 (Real.log Real.pi) 929330 2000 0 1 38410761 33554432 3 268435456 3569627252013 6710886400 278799 53687091200 (Enclosure.Real.IsNear.const Bool.false 929330 2000) RS541to552.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns540p103 Ns540p104) 

noncomputable abbrev qz373 := (@instHAdd Real Real.instAdd)

noncomputable def Ns540p124 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns540p100 Ns540p101 12975583542322825091 Ns540p102 124599775793 67108864 277 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz373 qz10 (Enclosure.sfrac Bool.true Ns540p103 Ns540p104)) Bool.false Ns540p100 Ns540p101 12975583542322825091 Ns540p102 Ns540p105 (Ns540p123 rfl rfl)) 

noncomputable abbrev qz589 := (BSN.cosEvenQ 137438953472)

noncomputable abbrev qz590 := (BSN.cosOddQ 137438953472)

noncomputable def Ns540p125 := BSN.cos_dyadic_bound_f 11756143 137438953472 1 0 67108864 19238770 0 1 1 0 1 1 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 11756143) qz589 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 11756143) qz590 0 0 rfl) rfl rfl 

noncomputable abbrev qz374 := (@Nat.cast Real Real.instNatCast 67108864)

noncomputable abbrev qz375 := (@Nat.cast Real Real.instNatCast Ns540p114)

noncomputable def Ns540p126 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 124599775793) qz374) Bool.false 124599775793 67108864 277 33554432 Bool.true 67108863 67108864 1 9610000 (Ns540p124 rfl) (Enclosure.sfrac_false_div 124599775793 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 124599775793) qz374) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 827265060617800646656) qz375) 226375608064910080 72057594037927936 Bool.false 67108863 67108864 295 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q2 124599775793 67108864 226375608064910080 72057594037927936 295 827265060617800646656 Ns540p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108863 67108864 827265060617800646656 Ns540p114 11756143 137438953472 19238770 19220000 (Ns540p125 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns540p127 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns540p100 Ns540p101 12975583542322825091 Ns540p102 996798206349 536870912 4425 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz373 qz10 (Enclosure.sfrac Bool.true Ns540p103 Ns540p104)) Bool.false Ns540p100 Ns540p101 12975583542322825091 Ns540p102 Ns540p105 (Ns540p123 rfl rfl)) 

noncomputable def Ns540p128 := Ns540p99 77039 BSN.abs_quadSignPos (BSN.cos_quad_nat3 771 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 531923482 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 532 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536343030 536870912) qz9 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 67108863 67108864 168470277 20153630720000 536870904 536870912 4488 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 67108863 67108864 168470277 20153630720000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 67108863 67108864 2695524432 322458091520000 67108863 67108864 168470277 20153630720000 (Ns540p126 rfl rfl) rfl)) rfl) (Ns540p127 rfl) RS541to552.d7 

noncomputable def Ns540p129 := nat_lit 126319971069987943774448538089793229469848707807826280917744270541295615574375857376288411270242655973654098087936 

noncomputable def Ns540p130 := nat_lit 3570415896635346974072005805030179415937144689025665314440334861177556999349704385084003346650664335197480996044800 

noncomputable def Ns540p131 := nat_lit 43693422276319769556787344303867440803944317361541459773904811775430240678273381581847816216570275157774336 

noncomputable def Ns540p132 := nat_lit 631053050252009920976808359164588676424585173811806851938314276881743568086983789647787646047082092118221861687296 

noncomputable def Ns540p133 := nat_lit 124964556382237144092520203176056279557800064115898286005411720141214494977239653477940117132773251731911834861568000 

noncomputable abbrev qz376 := (BSN.sinEvenQ 536870912)

noncomputable abbrev qz377 := (BSN.sinOddQ 536870912)

noncomputable def Ns540p134 := BSN.sin_dyadic_bound_f 770373506 536870912 4 3 536870912 268435456 Ns540p129 Ns540p130 Ns540p131 Ns540p132 Ns540p133 Ns540p131 531923482 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 770373506) qz376 0 3 Ns540p129 Ns540p130 Ns540p131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 770373506) qz377 0 3 Ns540p132 Ns540p133 Ns540p131 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p135 := nat_lit 321376964935477367947351644961 

noncomputable def Ns540p136 := nat_lit 1993841993677373809355710590420516864 

noncomputable def Ns540p137 := nat_lit 29907629905160607140335658856307752960 

noncomputable abbrev qz19 := (BSN.cosEvenQ 536870912)

noncomputable abbrev qz378 := (BSN.cosOddQ 536870912)

noncomputable def Ns540p138 := BSN.cos_dyadic_bound_f 23809687 536870912 2 1 536870912 268435456 Ns540p135 Ns540p136 Ns540p135 Ns540p135 Ns540p137 Ns540p135 536343030 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 23809687) qz19 0 1 Ns540p135 Ns540p136 Ns540p135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 23809687) qz378 0 1 Ns540p135 Ns540p137 Ns540p135 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p139 := nat_lit 84785821935465223341395252631692463089199265819631757871152487533090800433026851180506552821312828538775142400000 

noncomputable def Ns540p140 := nat_lit 13230287782270762660478002051402126568098414027300316685548090657387856552384595511739307524096000000000000 

noncomputable def Ns540p141 := nat_lit 423682568703908719510416522237221711581961226209149807857517901743528638927865168996083972762593375092211712000000 

noncomputable def Ns540p142 := BSN.sin_dyadic_bound_f 697371360 536870912 4 3 536870912 268435456 Ns540p139 Ns540p130 Ns540p140 Ns540p141 Ns540p133 Ns540p140 517156059 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 697371360) qz376 0 3 Ns540p139 Ns540p130 Ns540p140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 697371360) qz377 0 3 Ns540p141 Ns540p133 Ns540p140 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p143 := nat_lit 77487513759684598365981781878929803881652404678486332071270408673667228811656136574946764996457701420197478400000 

noncomputable def Ns540p144 := nat_lit 10101833322627132414815217099641131959246510108637434654255526137633935230089066983815900041216000000000000 

noncomputable def Ns540p145 := nat_lit 387231615685641552314888983489035163991469182551165173855805091540795531405984111800620994238155452211003392000000 

noncomputable def Ns540p146 := BSN.sin_dyadic_bound_f 681867540 536870912 4 3 536870912 268435456 Ns540p143 Ns540p130 Ns540p144 Ns540p145 Ns540p133 Ns540p144 512778156 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 681867540) qz376 0 3 Ns540p143 Ns540p130 Ns540p144 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 681867540) qz377 0 3 Ns540p145 Ns540p133 Ns540p144 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p147 := Ns540p97 130546 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 361 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 517156059 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 512778156 536870912) qz9 rfl rfl (Ns540p128 RS541to552.d9 RS541to552.d11 RS541to552.d13 RS541to552.d17 (Ns540p134 rfl rfl) (Ns540p138 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns540p127 rfl) RS541to552.d19 RS541to552.d21 RS541to552.d23 RS541to552.d25 RS541to552.d17 (Ns540p142 rfl rfl) (Ns540p146 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns540p148 := nat_lit 142659632250525231010265285056071315187402147058373155531768060280715749542245053714520876473951078142230867290625 

noncomputable def Ns540p149 := nat_lit 62902460574088228803615818408730136993509243704849565684678190172652928415414320547736156793636543212890625 

noncomputable def Ns540p150 := nat_lit 712600970641700909841655997736954616166120015533872041460336451451940196341270935410393256610176437353077484890625 

noncomputable def Ns540p151 := BSN.sin_dyadic_bound_f 794125185 536870912 4 3 536870912 268435456 Ns540p148 Ns540p130 Ns540p149 Ns540p150 Ns540p133 Ns540p149 534619037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 794125185) qz376 0 3 Ns540p148 Ns540p130 Ns540p149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 794125185) qz377 0 3 Ns540p150 Ns540p133 Ns540p149 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p152 := nat_lit 21088616047587072364509915038974000948537496468222370753451635900068679327656327820703722145969984897433212890625 

noncomputable def Ns540p153 := nat_lit 274647376664257459544000446540783031995164976078897331880025758552119769180746491160307949742358795015190845849600 

noncomputable def Ns540p154 := nat_lit 3576539762299393868603714474394949609984510472459530498457432524006885363726051609611883223056793212890625 

noncomputable def Ns540p155 := nat_lit 127844232491484796985061512913794276671484396890633668194303748460522432642690373353803432596210964890009212890625 

noncomputable def Ns540p156 := nat_lit 24992911276447428818504040635211255911560012823179657201082344028242898995447930695588023426554650346382366972313600 

noncomputable def Ns540p157 := BSN.cos_dyadic_bound_f 625348225 536870912 4 3 536870912 268435456 Ns540p152 Ns540p153 Ns540p154 Ns540p155 Ns540p156 Ns540p154 212027826 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 625348225) qz19 0 3 Ns540p152 Ns540p153 Ns540p154 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 625348225) qz378 0 3 Ns540p155 Ns540p156 Ns540p154 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p158 := Ns540p95 175692 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 121 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 534619037 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 212027826 536870912) qz9 rfl rfl (Ns540p147 rfl rfl) (Ns540p127 rfl) RS541to552.d27 RS541to552.d29 RS541to552.d31 RS541to552.d33 RS541to552.d17 (Ns540p151 rfl rfl) (Ns540p157 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p159 := nat_lit 320796508230038585201982518609158994022394479093651552291999244412887296 

noncomputable def Ns540p160 := nat_lit 278278412702595531909369356367009666242828713757909985904152976703587614720 

noncomputable def Ns540p161 := nat_lit 5282839343121337560910015067890597379127036107105034476123299881216 

noncomputable def Ns540p162 := nat_lit 962378959011429512930825735797341200872425183208740446807045486638899456 

noncomputable def Ns540p163 := nat_lit 12522528571616798935921621036515434980927292119105949365686883951661442662400 

noncomputable def Ns540p164 := BSN.cos_dyadic_bound_f 218956794 536870912 3 2 536870912 268435456 Ns540p159 Ns540p160 Ns540p161 Ns540p162 Ns540p163 Ns540p161 492836840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 218956794) qz19 0 2 Ns540p159 Ns540p160 Ns540p161 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 218956794) qz378 0 2 Ns540p162 Ns540p163 Ns540p161 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p165 := nat_lit 143823725764266389412624100564423663996343084626949194062119210426905208799572472982328252935386792544532760700881 

noncomputable def Ns540p166 := nat_lit 64452408748390145670534683260744311688807931333093547323509379229444315203237825907959162756796310947964881 

noncomputable def Ns540p167 := nat_lit 718410029901945296262363054902503746687459916019629600975636791956147065054507790589816232906886718172182688114641 

noncomputable def Ns540p168 := BSN.sin_dyadic_bound_f 795737691 536870912 4 3 536870912 268435456 Ns540p165 Ns540p130 Ns540p166 Ns540p167 Ns540p133 Ns540p166 534764161 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 795737691) qz376 0 3 Ns540p165 Ns540p130 Ns540p166 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 795737691) qz377 0 3 Ns540p167 Ns540p133 Ns540p166 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p169 := Ns540p93 215137 BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 492836840 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 534764161 536870912) qz9 rfl rfl (Ns540p158 rfl) (Ns540p127 rfl) RS541to552.d35 RS541to552.d37 RS541to552.d39 RS541to552.d41 RS541to552.d17 (Ns540p164 rfl rfl) (Ns540p168 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p170 := nat_lit 421772027858471753411692093303394238692732917939074595591670566438215936 

noncomputable def Ns540p171 := nat_lit 9131858718371717178470467840534871014492148596203870285144286208256 

noncomputable def Ns540p172 := nat_lit 1265297819857978516800719338974501646336169769520031379034441410742231296 

noncomputable def Ns540p173 := BSN.cos_dyadic_bound_f 234460614 536870912 3 2 536870912 268435456 Ns540p170 Ns540p160 Ns540p171 Ns540p172 Ns540p163 Ns540p171 486482986 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 234460614) qz19 0 2 Ns540p170 Ns540p160 Ns540p171 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 234460614) qz378 0 2 Ns540p172 Ns540p163 Ns540p171 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p174 := nat_lit 13747348162817451288549061839703454823170206965623673092937275777072306708722416916720354502892694267567272679201 

noncomputable def Ns540p175 := nat_lit 991909165678436855224337960853175609143479375996526241588949351351403379355709577043895633351883637970721 

noncomputable def Ns540p176 := nat_lit 83360872709784062311259996370523579624765082271173173312154608948300187623927247477881679901421743640198209394465 

noncomputable def Ns540p177 := BSN.cos_dyadic_bound_f 561960761 536870912 4 3 536870912 268435456 Ns540p174 Ns540p153 Ns540p175 Ns540p176 Ns540p156 Ns540p175 268651191 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 561960761) qz19 0 3 Ns540p174 Ns540p153 Ns540p175 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 561960761) qz378 0 3 Ns540p176 Ns540p156 Ns540p175 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz379 := (BSN.cos_quad_nat0 236 rfl)

noncomputable def Ns540p178 := Ns540p91 250613 BSN.abs_quadSignPos (BSN.cos_quad_nat0 180 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 486482986 536870912) BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 268651191 536870912) qz9 rfl rfl (Ns540p169 rfl) (Ns540p127 rfl) RS541to552.d43 RS541to552.d45 RS541to552.d47 RS541to552.d49 RS541to552.d17 (Ns540p173 rfl rfl) (Ns540p177 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p179 := nat_lit 222923200549789068475883387739361 

noncomputable def Ns540p180 := BSN.cos_dyadic_bound_f 122190887 536870912 2 1 536870912 268435456 Ns540p179 Ns540p136 Ns540p179 Ns540p179 Ns540p137 Ns540p179 523025616 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 122190887) qz19 0 1 Ns540p179 Ns540p136 Ns540p179 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 122190887) qz378 0 1 Ns540p179 Ns540p137 Ns540p179 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz380 := (BSN.cos_quad_nat0 288 rfl)

noncomputable def Ns540p181 := Ns540p89 Bool.true 406551859 250613 Bool.true 122190887 28296951008113761 1 Bool.false 523025616 Bool.false Bool.true 255567364 267192 BSN.abs_quadSignPos qz380 (BSN.sfrac_eq_quadSignPos_mul Bool.false 523025616 536870912) qz9 rfl (Ns540p178 rfl) (Ns540p127 rfl) RS541to552.d51 RS541to552.d53 RS541to552.d17 (Ns540p180 rfl rfl) rfl 

noncomputable def Ns540p182 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) 255567364 536870912 267192 536870912 255567364 536870912 267192 536870912 274413367576231936 63891841 67108864 33399 33554432 (Ns540p181 rfl rfl rfl rfl) 

noncomputable def Ns540p183 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8) 19243425 67108864 1 67108864 1370506545911997 2251799813685248 232524873326757 16906090788683776000 26373239928266570869725 151115727451828646838272 

noncomputable def Ns540p184 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz7 1 1 0 1 19243425 67108864 1 67108864 19243425 67108864 1 67108864 

noncomputable abbrev qz20 := qz357

noncomputable abbrev qz21 := (@Enclosure.Real.IsNear.of_eq qz357 (@HMul.hMul Real Real Real qz355 qz354 qz353) Bool.false 992590143631 6710886400 92933 6710886400 (BSN.t_div_two_pi_mk qz354 929330 1000 qz360) (@Enclosure.Real.IsNear.mulLit_ff qz354 qz353 929330 1000 0 1 10680707 67108864 1 67108864 992590143631 6710886400 92933 6710886400 (Enclosure.Real.IsNear.const Bool.false 929330 1000) RS541to552.d56 rfl))

noncomputable def Ns540p185 := @Enclosure.Real.IsNear.sqrt_image qz20 992590143631 6710886400 92933 6710886400 408079620 408079659 33554432 qz21 

noncomputable abbrev qz725 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 929330 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz591 := qz725

noncomputable abbrev qz381 := qz591

noncomputable abbrev qz22 := qz381

noncomputable def Ns540p186 := @Enclosure.Real.IsNear.sqrt_image qz22 816159279 67108864 39 67108864 117016579 117016586 33554432 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 816159279 67108864 39 67108864 816159279 67108864 39 67108864 (Ns540p185 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz592 := (Real.sqrt qz725)

noncomputable abbrev qz382 := qz592

noncomputable abbrev qz23 := qz382

noncomputable def Ns540p187 := @Enclosure.Real.IsNear.inv_image qz23 234033165 67108864 7 67108864 9621712 9621713 33554432 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 234033165 67108864 7 67108864 234033165 67108864 7 67108864 (Ns540p186 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns540p188 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 19243425 67108864 1 67108864 19243425 67108864 1 67108864 (Ns540p187 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz24 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz359))

noncomputable abbrev qz593 := (@HMul.hMul Real Real Real qz717 qz720 qz720)

noncomputable abbrev qz594 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz383 := (@HSub.hSub Real Real Real qz582 (@HSub.hSub Real Real Real qz582 qz593 qz581) qz594)

noncomputable abbrev qz25 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz383))

noncomputable def Ns540p189 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz8) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz24) qz25) Bool.false 1370506545911997 

noncomputable def Ns540p190 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz24) qz25 127422117 67108864 913 

noncomputable def Ns540p191 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz24) Bool.false 127422117 67108864 913 67108864 127422117 67108864 913 

noncomputable def Ns540p192 := @Enclosure.Real.IsNear.recentre' qz24 Bool.false 17671970 33554432 1215584432 322458091520000 8835985 16777216 75974027 20153630720000 

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz355 qz352 qz359)

noncomputable abbrev qz384 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable def Ns540p193 := @Enclosure.Real.IsNear.cos_image qz26 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 34095425) qz384) Bool.false 34095425 33554432 123 33554432 Bool.false 17671970 33554432 1 

noncomputable def Ns540p194 := nat_lit 42098277641837742734975481 

noncomputable def Ns540p195 := nat_lit 11529215046068469760000000000000 

noncomputable def Ns540p196 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz8 884279719003555 140737488355328 1 500000000000000 10852911 67108864 39 67108864 9597009089450591098605 9444732965739290427392 Ns540p194 

noncomputable def Ns540p197 := @Enclosure.Real.IsNear.subLit_ff_p qz22 qz1 816159279 67108864 39 67108864 12 1 0 1 10852911 10852911 67108864 39 

noncomputable abbrev qz385 := (Enclosure.Real.IsNear.const Bool.false 12 1)

noncomputable def Ns540p198 := @Ns540p197 67108864 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 816159279 67108864 39 67108864 816159279 67108864 39 67108864 (Ns540p185 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns540p199 := @Enclosure.Real.IsNear.recentre' qz26 Bool.false 9597009089450591098605 9444732965739290427392 Ns540p194 Ns540p195 34095425 33554432 123 33554432 (@Ns540p196 Ns540p195 RS541to552.d55 (Ns540p198 rfl rfl) rfl) 

noncomputable def Ns540p200 := nat_lit 2879842798669557208045480493410311761802999821478900431212890625 

noncomputable def Ns540p201 := nat_lit 64791741944522487909851911563195676133695224709322207119351480320 

noncomputable def Ns540p202 := nat_lit 1826286321761458310952933902571129332958939779150543212890625 

noncomputable def Ns540p203 := nat_lit 8635875823365148707514535612425793026743081584878400207212890625 

noncomputable def Ns540p204 := nat_lit 2915628387503511955943336020343805426016285111919499320370816614400 

noncomputable abbrev qz595 := (BSN.cosEvenQ 33554432)

noncomputable def Ns540p205 := BSN.cos_dyadic_bound_f 34095425 33554432 3 2 33554432 9610000 Ns540p200 Ns540p201 Ns540p202 Ns540p203 Ns540p204 Ns540p202 17671970 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 34095425) qz595 0 2 Ns540p200 Ns540p201 Ns540p202 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 34095425) (BSN.cosOddQ 33554432) 0 2 Ns540p203 Ns540p204 Ns540p202 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p206 := @Enclosure.Real.IsNear.inv_image qz24 8835985 16777216 75974027 20153630720000 63710602 63711515 33554432 (Ns540p192 (@Ns540p193 9610000 (Ns540p199 rfl) (Enclosure.sfrac_false_div 34095425 33554432) (Ns540p205 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns540p207 := @Enclosure.Real.IsNear.recentre' qz25 Bool.false 10755641 33554432 

noncomputable abbrev qz27 := (@HMul.hMul Real Real Real qz355 qz352 qz383)

noncomputable def Ns540p208 := @Enclosure.Real.IsNear.cos_image qz27 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 83516549)) qz374) Bool.true 83516549 67108864 

noncomputable def Ns540p209 := nat_lit 788791505588936324193211627645 

noncomputable def Ns540p210 := nat_lit 633825300114114700748351602688 

noncomputable def Ns540p211 := nat_lit 93473673792719224605717883334734613 

noncomputable def Ns540p212 := @Enclosure.Real.IsNear.recentre' qz27 Bool.true Ns540p209 Ns540p210 Ns540p211 

noncomputable def Ns540p213 := nat_lit 19342813113834066795298816000000000000000 

noncomputable abbrev qz28 := qz383

noncomputable def Ns540p214 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz28 884279719003555 140737488355328 1 500000000000000 892015827839839 

noncomputable abbrev qz386 := (@HSub.hSub Real Real Real qz582 qz593 qz581)

noncomputable abbrev qz29 := qz386

noncomputable abbrev qz387 := qz594

noncomputable abbrev qz30 := qz387

noncomputable def Ns540p215 := @Enclosure.Real.IsNear.subLit_tf qz29 qz30 610540851129183 4503599627370496 3463774275 4503599627370496 1 16 

noncomputable abbrev qz388 := qz593

noncomputable abbrev qz31 := qz388

noncomputable def Ns540p216 := @Enclosure.Real.IsNear.subLit_ff_n qz31 qz8 117785677173921 4503599627370496 846528579 4503599627370496 10852911 67108864 39 67108864 

noncomputable def Ns540p217 := @Enclosure.Real.IsNear.mulLit_ff qz8 qz8 10852911 67108864 39 67108864 10852911 67108864 39 67108864 117785677173921 4503599627370496 

noncomputable def Ns540p218 := nat_lit 400013586290040779370528267032680558636716156951340774236871300261608100388175180265173132421833164881 

noncomputable def Ns540p219 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600 

noncomputable def Ns540p220 := nat_lit 115151734965787103441949693518036014178349733946711212937524926334171137794736439417985266616401 

noncomputable def Ns540p221 := nat_lit 2424441891321425199546660954759514433253799286675621967531650987014114107209335888324854260369939236945 

noncomputable def Ns540p222 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600 

noncomputable abbrev qz596 := (BSN.cosEvenQ 67108864)

noncomputable def Ns540p223 := BSN.cos_dyadic_bound_f 83516549 67108864 4 3 33554432 9610000 Ns540p218 Ns540p219 Ns540p220 Ns540p221 Ns540p222 Ns540p220 10755641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 83516549) qz596 0 3 Ns540p218 Ns540p219 Ns540p220 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 83516549) (BSN.cosOddQ 67108864) 0 3 Ns540p221 Ns540p222 Ns540p220 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz389 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns540p224 := @Ns540p207 3190358864 644916183040000 10755641 33554432 199397429 40307261440000 (@Ns540p208 325 67108864 Bool.false 10755641 33554432 1 9610000 (@Ns540p212 Ns540p213 83516549 67108864 325 67108864 (@Ns540p214 4503599627370496 3463774275 4503599627370496 Ns540p209 Ns540p210 Ns540p211 Ns540p213 RS541to552.d55 (@Ns540p215 0 1 14272253245437424 892015827839839 4503599627370496 3463774275 4503599627370496 (@Ns540p216 40972702944872588378112 610540851129183 4503599627370496 3463774275 4503599627370496 (@Ns540p217 846528579 4503599627370496 (Ns540p198 rfl rfl) (Ns540p198 rfl rfl) rfl) (Ns540p198 rfl rfl) rfl rfl) qz389 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 83516549 67108864) (BSN.cos_neg_of_bound 83516549 67108864 Bool.false 10755641 33554432 1 9610000 (Ns540p223 rfl rfl)) rfl rfl) 

noncomputable abbrev qz32 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 12) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 12 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns540p225 := @Ns540p183 71757835187192833031337 Ns540p86 (Ns540p184 qz32 (@Enclosure.Real.IsNear.of_eq qz7 (@Inv.inv Real Real.instInv qz23) Bool.false 19243425 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz20 (BSN.t_div_two_pi_nonneg qz4 929330 1000 qz9)) Ns540p188) rfl) (@Ns540p189 2251799813685248 232524873326757 16906090788683776000 (BSN.correction_mk qz8 (BSN.cos_two_pi_p_ne_zero_mk qz4 929330 1000 12 qz9 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 929330 1000 12 qz9 rfl rfl rfl))) (@Ns540p190 67108864 10755641 33554432 199397429 40307261440000 1370506545911997 2251799813685248 232524873326757 16906090788683776000 (@Ns540p191 67108864 (Ns540p206 rfl rfl rfl rfl rfl) rfl) (Ns540p224 rfl) rfl)) 

noncomputable abbrev qz33 := qz361

noncomputable def Ns540p226 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 170244875588074060131293 151115727451828646838272 Ns540p85 Ns540p86 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz33 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8))) Bool.true 170244875588074060131293 151115727451828646838272 Ns540p85 Ns540p86 (BSN.hardyZApproximantRS₀_eq qz4 12 (@BSN.floor_sqrt_eq_dec qz4 929330 1000 12 qz9 rfl rfl rfl)) (@Ns540p88 170244875588074060131293 151115727451828646838272 Ns540p85 Ns540p86 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12)) Bool.true 63891841 67108864 33399 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (Ns540p182 (Ns540p181 rfl rfl rfl rfl) rfl rfl)) (Ns540p225 rfl) rfl rfl)) 

theorem RS541to552.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 170244875588074060131293 151115727451828646838272 Ns540p85 Ns540p86 := Ns540p226 

theorem RS541to552.d58 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS541to552.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS541to552.d3 a b h)) 

noncomputable def Ns540p227 := nat_lit 90860337679787918654493607 

noncomputable def Ns540p228 := nat_lit 90763883800754581007237120000 

noncomputable def Ns540p229 := nat_lit 21655864095270242706264749506560 

noncomputable abbrev qz726 := (Enclosure.sfrac Bool.false 930587 1000)

noncomputable abbrev qz597 := qz726

noncomputable abbrev qz390 := qz597

noncomputable abbrev qz34 := qz390

noncomputable abbrev qz727 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 930587 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz598 := qz727

noncomputable abbrev qz391 := qz598

noncomputable abbrev qz35 := (@HPow.hPow Real Real Real qz356 qz391 qz358)

noncomputable abbrev qz728 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 930587 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz599 := qz728

noncomputable abbrev qz392 := qz599

noncomputable abbrev qz36 := qz392

noncomputable def Ns540p230 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz34) qz34 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz35) (Zeta.RiemannSiegel.correction qz36)) 166264155 134217728 33445 33554432 25848035787927735336825 151115727451828646838272 392464651383296523293607 Ns540p228 Ns540p229 

noncomputable def Ns540p231 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz34) qz34 Real.cos BSN.quadSignPos 11 12 930587 1000 288 536870912 268435456 9007199254740992 Bool.false 998484399613 4432 1334074092 57 154981288 8 

noncomputable def Ns540p232 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz34) qz34 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 930587 1000 180 236 536870912 268435456 9007199254740992 Bool.false 998484399613 4432 

noncomputable def Ns540p233 := Ns540p232 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 83797874 215434 Bool.true 102159382 Bool.true 493979294 28296951008113761 1 Bool.false 527180420 Bool.false Bool.false 325201029 Bool.false Bool.false 180963014 

noncomputable def Ns540p234 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz34) qz34 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 930587 1000 47 117 536870912 268435456 9007199254740992 Bool.false 998484399613 4432 

noncomputable def Ns540p235 := Ns540p234 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 112510700 175935 Bool.true 779382723 Bool.true 592334244 28296951008113761 1 Bool.false 533068797 Bool.false Bool.false 479266383 Bool.true Bool.true 83797874 

noncomputable def Ns540p236 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz34) qz34 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 930587 1000 122 31 536870912 268435456 9007199254740992 Bool.false 998484399613 4432 

noncomputable def Ns540p237 := Ns540p236 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 17111461 130727 Bool.false 427840572 Bool.false 155035538 28296951008113761 1 Bool.false 375227839 Bool.true Bool.false 152889725 Bool.false Bool.true 112510700 

noncomputable def Ns540p238 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz34) qz34 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 930587 1000 362 230 536870912 268435456 9007199254740992 Bool.false 998484399613 4432 

noncomputable def Ns540p239 := Ns540p238 744261104 56 268435448 8 864060384 56 240095976 8 Bool.false 262625408 77147 Bool.false 604713560 Bool.false 438622045 28296951008113761 1 Bool.false 230823844 Bool.true Bool.false 367441750 Bool.true Bool.true 17111461 

noncomputable def Ns540p240 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz34) qz34 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 930587 1000 773 533 536870912 268435456 9007199254740992 Bool.false 998484399613 4432 

noncomputable def Ns540p241 := Ns540p240 372130544 56 379625064 8 589812976 56 309962568 8 Bool.false 536870768 4496 Bool.false 302168963 Bool.false 125293184 28296951008113761 1 Bool.false 286466160 Bool.true Bool.false 124158934 Bool.true Bool.false 262625408 

noncomputable def Ns540p242 := nat_lit 195828523158125389096816298263873728307901207356717180552157 

noncomputable def Ns540p243 := nat_lit 105294221786700054890541055354301045490363395897032704000 

noncomputable def Ns540p244 := nat_lit 334985849114608609152131197619360000 

noncomputable def Ns540p245 := nat_lit 1870401110201315029445031529929740185920 

noncomputable abbrev qz600 := (@Eq.refl Real qz726)

noncomputable abbrev qz393 := qz600

noncomputable abbrev qz37 := qz393

noncomputable def Ns540p246 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz34 930587 1000 3463969658276 16000000 1861174 4000 2000 Ns540p244 Ns540p245 qz37 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns540p247 := nat_lit 62665127410600124510981215444439593058528386354149497776690240 

noncomputable abbrev qz601 := (@HSub.hSub Real Real Real qz721 qz722 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz723 (@Nat.cast Real Real.instNatCast 1861174))))

noncomputable abbrev qz394 := (@HSub.hSub Real Real Real qz582 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 930587 4000) (Real.log (Enclosure.sfrac Bool.false 3463969658276 16000000))) (@HMul.hMul Real Real Real qz579 qz583 qz601))

noncomputable abbrev qz602 := (Enclosure.sfrac Bool.false 930587 2000)

noncomputable abbrev qz38 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz394 qz602) (@HMul.hMul Real Real Real qz355 qz602 (Real.log Real.pi)))

noncomputable def Ns540p248 := @Enclosure.Real.IsNear.addLit_ft_p qz38 (Enclosure.sfrac Bool.true Ns540p244 Ns540p245) 33503580116258555514397 18014398509481984000 4191315725959813379 507904000000000000000000 Ns540p244 Ns540p245 0 1 Ns540p247 

noncomputable def Ns540p249 := nat_lit 2248387201535099590852118315008000 

noncomputable abbrev qz39 := (@HSub.hSub Real Real Real qz361 qz394 qz602)

noncomputable def Ns540p250 := @Enclosure.Real.IsNear.subLit_ff_p qz39 (@HMul.hMul Real Real Real qz5 qz602 (Real.log Real.pi)) 43098685996051359157789 18014398509481984000 378462990434849 124000000000000000000 35744554846707 67108864000 2791761 536870912000 Ns540p249 33503580116258555514397 18014398509481984000 

noncomputable def Ns540p251 := nat_lit 86197371992102718315578000 

noncomputable abbrev qz40 := qz394

noncomputable def Ns540p252 := @Enclosure.Real.IsNear.subLit_ff_p qz40 qz602 51480668528923014680093 18014398509481984000 378462990434849 124000000000000000000 930587 2000 0 1 Ns540p251 43098685996051359157789 18014398509481984000 378462990434849 124000000000000000000 

noncomputable def Ns540p253 := nat_lit 115924159801820854696137110186113368064 

noncomputable def Ns540p254 := nat_lit 118816489449828670685315072 

noncomputable def Ns540p255 := nat_lit 118226980698035137492061190424369543570706664302235999884177642673113481290618298050672825665455737542658401159342476804205623023877254557046164229562575093760 

noncomputable def Ns540p256 := nat_lit 2470821908803744653919295653707449246512480625798015256554126951115495951145409563568607570495707631820854507944476525332958447456069815023837112263006748672 

noncomputable def Ns540p257 := nat_lit 441927945062734090495183432481211072613996921293852965574169609995809905282126967838653386925305828174245479098732775320732643146618710046870622699520 

noncomputable def Ns540p258 := BSN.log_dyadic_bound 1366817658276 5561121658276 7 6 Ns540p255 268435456 76880000 Ns540p256 Ns540p257 134710306 6927939316552 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1366817658276) (BSN.artanhQ 5561121658276) 0 6 Ns540p256 Ns540p255 Ns540p257 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz395 := (Real.log (Enclosure.sfrac Bool.false 3463969658276 16000000))

noncomputable def Ns540p259 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 930587 4000) qz395 930587 4000 0 1 55328239430593639 4503599627370496 12500016337 961000000000000000 51487740346997842736093 18014398509481984000 11632352702999819 3844000000000000000000 (Enclosure.Real.IsNear.const Bool.false 930587 4000) (BSN.isNear_log_sfrac 3463969658276 16000000 55328239430593639 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3463969658276) qz364)) Bool.false Ns540p254 Ns540p114 1000001306960000 76880000000000000000000 55328239430593639 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3463969658276 16000000 17 6927939316552 4194304000000 134710306 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns540p258 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p260 := BSN.arctan_dyadic_bound_f 1000 1861174 1 0 33554432 9610000 0 1 1 0 1 1 18028 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1861174) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1861174) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns540p261 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1861174))) 884279719003555 562949953421312 1 2000000000000000 18028 33554432 1 9610000 29661354838523614593024 883977259353507 562949953421312 200000000961 1922000000000000000 qz15 (Ns540p260 rfl) rfl rfl 

noncomputable abbrev qz396 := (@HMul.hMul Real Real Real qz579 qz583 qz601)

noncomputable abbrev qz41 := qz396

noncomputable abbrev qz397 := qz601

noncomputable abbrev qz42 := qz397

noncomputable def Ns540p262 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 930587 4000) qz395) qz41 51487740346997842736093 18014398509481984000 11632352702999819 3844000000000000000000 883977259353507 2251799813685248 200000000961 7688000000000000000 Ns540p253 51480668528923014680093 18014398509481984000 378462990434849 124000000000000000000 (Ns540p259 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz42 1 4 0 1 883977259353507 562949953421312 200000000961 1922000000000000000 883977259353507 2251799813685248 200000000961 7688000000000000000 qz372 Ns540p261 rfl) 

noncomputable def Ns540p263 := @Ns540p248 Ns540p242 Ns540p243 4191315725959813379 507904000000000000000000 (@Ns540p250 4191315725959813379 507904000000000000000000 (Ns540p252 (Ns540p262 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 930587 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz602 (Real.log Real.pi) 930587 2000 0 1 38410761 33554432 3 268435456 35744554846707 67108864000 2791761 536870912000 (Enclosure.Real.IsNear.const Bool.false 930587 2000) RS541to552.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns540p244 Ns540p245) 

noncomputable def Ns540p264 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz34) Bool.false Ns540p242 Ns540p243 4191315725959813379 507904000000000000000000 124810549951 67108864 555 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz34) (@HAdd.hAdd Real Real Real qz373 qz38 (Enclosure.sfrac Bool.true Ns540p244 Ns540p245)) Bool.false Ns540p242 Ns540p243 4191315725959813379 507904000000000000000000 Ns540p246 (Ns540p263 rfl rfl)) 

noncomputable def Ns540p265 := nat_lit 15184774792215425619853312 

noncomputable def Ns540p266 := nat_lit 14353709856124251256622195532406172456132484281370964145502464010965776095870048317372086995215371395678504587153129334620880528717969965790625 

noncomputable def Ns540p267 := nat_lit 282877490902138091004622673603363019119652456796264491099280832830873987773707601701812303598028785564314492868916806270538811366318583631052800 

noncomputable def Ns540p268 := nat_lit 10193953683382048278829442603198895817564095594512166992715002172220923442843456514630524751916055859147846131546089467456753144775390625 

noncomputable def Ns540p269 := nat_lit 71679532825786961842179630964753310515424016107964486755871481145467917874635675431307588989460257383840915643130838322070653444580086727390625 

noncomputable def Ns540p270 := nat_lit 9900712181574833185161793576117705669187835987869257188474829149080589572079766059563430625931007494751007250412088219468858397821150427086848000 

noncomputable def Ns540p271 := BSN.sin_dyadic_bound_f 215788628455 137438953472 4 3 67108864 19238770 Ns540p266 Ns540p267 Ns540p268 Ns540p269 Ns540p270 Ns540p268 67108846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215788628455) (BSN.sinEvenQ 137438953472) 0 3 Ns540p266 Ns540p267 Ns540p268 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215788628455) (BSN.sinOddQ 137438953472) 0 3 Ns540p269 Ns540p270 Ns540p268 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p272 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz34) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 124810549951) qz374) Bool.false 124810549951 67108864 555 67108864 Bool.false 67108846 67108864 1 9610000 (Ns540p264 rfl) (Enclosure.sfrac_false_div 124810549951 67108864) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 124810549951) qz374) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns540p265) qz375) 226375608064910080 72057594037927936 Bool.false 67108846 67108864 295 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q3 124810549951 67108864 226375608064910080 72057594037927936 295 Ns540p265 Ns540p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108846 67108864 Ns540p265 Ns540p114 215788628455 137438953472 19238770 19220000 (Ns540p271 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns540p273 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz34) Bool.false Ns540p242 Ns540p243 4191315725959813379 507904000000000000000000 998484399613 536870912 4432 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz34) (@HAdd.hAdd Real Real Real qz373 qz38 (Enclosure.sfrac Bool.true Ns540p244 Ns540p245)) Bool.false Ns540p242 Ns540p243 4191315725959813379 507904000000000000000000 Ns540p246 (Ns540p263 rfl rfl)) 

noncomputable def Ns540p274 := Ns540p241 77147 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 773 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 286466160 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 533 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 124158934 536870912) qz37 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz34) qz34 1) Bool.false 33554423 33554432 337541179 40307261440000 536870768 536870912 4496 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz34) qz34 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz34)) Bool.false 33554423 33554432 337541179 40307261440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz34) qz34) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz34)) Bool.false 67108846 67108864 5400658864 644916183040000 33554423 33554432 337541179 40307261440000 (Ns540p272 rfl rfl) rfl)) rfl) (Ns540p273 rfl) RS541to552.d7 

noncomputable def Ns540p275 := nat_lit 2094474668281756251395314989317211143964858744028797178605646737494085025 

noncomputable def Ns540p276 := nat_lit 2504505714323359787184324207303086996185458423821189873137376790332288532480 

noncomputable def Ns540p277 := nat_lit 69502245024545210855601615304839901066247402856473878863973839637921 

noncomputable def Ns540p278 := nat_lit 5485416365674559966170153997977440398163379929042224986258533116744142241 

noncomputable def Ns540p279 := nat_lit 45915938095928262765045943800556594930066737770055147674185241156091956428800 

noncomputable def Ns540p280 := BSN.sin_dyadic_bound_f 302168963 536870912 3 2 536870912 268435456 Ns540p275 Ns540p276 Ns540p277 Ns540p278 Ns540p279 Ns540p277 286466160 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 302168963) qz376 0 2 Ns540p275 Ns540p276 Ns540p277 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 302168963) qz377 0 2 Ns540p278 Ns540p279 Ns540p277 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p281 := nat_lit 246439196063400288239228588916736 

noncomputable def Ns540p282 := nat_lit 9969209968386869046778552952102584320 

noncomputable def Ns540p283 := nat_lit 69784469778708083327449870664718090240 

noncomputable def Ns540p284 := BSN.sin_dyadic_bound_f 125293184 536870912 2 1 536870912 268435456 Ns540p281 Ns540p282 Ns540p281 Ns540p281 Ns540p283 Ns540p281 124158934 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 125293184) qz376 0 1 Ns540p281 Ns540p282 Ns540p281 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 125293184) qz377 0 1 Ns540p281 Ns540p283 Ns540p281 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p285 := nat_lit 18437392424550095989246498062599018389732343038872339700042242501233746291474059789420863777203179533369344000000 

noncomputable def Ns540p286 := nat_lit 2391093105356322504242868941685796462072546342458812850632533684837768411362378064769409089536000000000000 

noncomputable def Ns540p287 := nat_lit 111782125883994284997074644927347640435890624256574101656781112628103691161831041566824282286094428860422553600000 

noncomputable def Ns540p288 := BSN.cos_dyadic_bound_f 604713560 536870912 4 3 536870912 268435456 Ns540p285 Ns540p153 Ns540p286 Ns540p287 Ns540p156 Ns540p286 230823844 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 604713560) qz19 0 3 Ns540p285 Ns540p153 Ns540p286 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 604713560) qz378 0 3 Ns540p287 Ns540p156 Ns540p286 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p289 := nat_lit 5167324790030335742417731530753577326353014527036137416824042164576190625 

noncomputable def Ns540p290 := nat_lit 1370009703242549610656651173831795666306881559105773668941513875390625 

noncomputable def Ns540p291 := nat_lit 15499234350684522128031881289913068387726429817990200703134243465977790625 

noncomputable def Ns540p292 := BSN.cos_dyadic_bound_f 438622045 536870912 3 2 536870912 268435456 Ns540p289 Ns540p160 Ns540p290 Ns540p291 Ns540p163 Ns540p290 367441750 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 438622045) qz19 0 2 Ns540p289 Ns540p160 Ns540p290 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 438622045) qz378 0 2 Ns540p291 Ns540p163 Ns540p290 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p293 := Ns540p239 130727 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 362 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 230823844 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 230 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 367441750 536870912) qz37 rfl rfl (Ns540p274 RS541to552.d9 RS541to552.d11 RS541to552.d13 RS541to552.d17 (Ns540p280 rfl rfl) (Ns540p284 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns540p273 rfl) RS541to552.d19 RS541to552.d21 RS541to552.d23 RS541to552.d25 RS541to552.d17 (Ns540p288 rfl rfl) (Ns540p292 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns540p294 := nat_lit 4677576429863205236385717788589043232558257439749818908926360949966831616 

noncomputable def Ns540p295 := nat_lit 1122679337492858857719342091670307633467428407771514610647868584820736 

noncomputable def Ns540p296 := nat_lit 14030483930914629991441714681583789082407837462433913697557787112730853376 

noncomputable def Ns540p297 := BSN.cos_dyadic_bound_f 427840572 536870912 3 2 536870912 268435456 Ns540p294 Ns540p160 Ns540p295 Ns540p296 Ns540p163 Ns540p295 375227839 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 427840572) qz19 0 2 Ns540p294 Ns540p160 Ns540p295 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 427840572) qz378 0 2 Ns540p296 Ns540p163 Ns540p295 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p298 := nat_lit 577730163360991219992638739909136 

noncomputable def Ns540p299 := BSN.sin_dyadic_bound_f 155035538 536870912 2 1 536870912 268435456 Ns540p298 Ns540p282 Ns540p298 Ns540p298 Ns540p283 Ns540p298 152889725 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 155035538) qz376 0 1 Ns540p298 Ns540p282 Ns540p298 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 155035538) qz377 0 1 Ns540p298 Ns540p283 Ns540p298 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p300 := Ns540p237 175935 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 122 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 375227839 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 152889725 536870912) qz37 rfl rfl (Ns540p293 rfl rfl) (Ns540p273 rfl) RS541to552.d27 RS541to552.d29 RS541to552.d31 RS541to552.d33 RS541to552.d17 (Ns540p297 rfl rfl) (Ns540p299 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p301 := nat_lit 132342312682239205891569852787851101082313720398467983686550670722109952106326962953996446040440169388580588423921 

noncomputable def Ns540p302 := nat_lit 50235333740861168679134105738252072721580815072496089104791271701389837733417224525766804002370254274235121 

noncomputable def Ns540p303 := nat_lit 661111448179850717718697389365406795654100726072441391874615873759801051433679927738686962503336512944666165578481 

noncomputable def Ns540p304 := BSN.sin_dyadic_bound_f 779382723 536870912 4 3 536870912 268435456 Ns540p301 Ns540p130 Ns540p302 Ns540p303 Ns540p133 Ns540p302 533068797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 779382723) qz376 0 3 Ns540p301 Ns540p130 Ns540p302 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 779382723) qz377 0 3 Ns540p303 Ns540p133 Ns540p302 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p305 := nat_lit 30941502863197733923830511342005428878196731394362671792759060097950351360 

noncomputable def Ns540p306 := nat_lit 15154259724808915790288059203402149887402438956986391454819419768815616 

noncomputable def Ns540p307 := nat_lit 81012733935487231555895634752256329295459454465019495775823068815006171136 

noncomputable def Ns540p308 := BSN.sin_dyadic_bound_f 592334244 536870912 3 2 536870912 268435456 Ns540p305 Ns540p276 Ns540p306 Ns540p307 Ns540p279 Ns540p306 479266383 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 592334244) qz376 0 2 Ns540p305 Ns540p276 Ns540p306 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 592334244) qz377 0 2 Ns540p307 Ns540p279 Ns540p306 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p309 := Ns540p235 215434 BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 533068797 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 479266383 536870912) qz37 rfl rfl (Ns540p300 rfl) (Ns540p273 rfl) RS541to552.d35 RS541to552.d37 RS541to552.d39 RS541to552.d41 RS541to552.d17 (Ns540p304 rfl rfl) (Ns540p308 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p310 := nat_lit 108921353199618317472928629461776 

noncomputable def Ns540p311 := BSN.cos_dyadic_bound_f 102159382 536870912 2 1 536870912 268435456 Ns540p310 Ns540p136 Ns540p310 Ns540p310 Ns540p137 Ns540p310 527180420 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 102159382) qz19 0 1 Ns540p310 Ns540p136 Ns540p310 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 102159382) qz378 0 1 Ns540p310 Ns540p137 Ns540p310 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p312 := nat_lit 8313980479156157336293685953769156946771301273989242296426275750581207296 

noncomputable def Ns540p313 := nat_lit 3545438535747578805803361519054922078904847223757452677579835919401216 

noncomputable def Ns540p314 := nat_lit 24934850560396976851269451138269360996156094127520211983923667579904819456 

noncomputable def Ns540p315 := BSN.cos_dyadic_bound_f 493979294 536870912 3 2 536870912 268435456 Ns540p312 Ns540p160 Ns540p313 Ns540p314 Ns540p163 Ns540p313 325201029 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 493979294) qz19 0 2 Ns540p312 Ns540p160 Ns540p313 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 493979294) qz378 0 2 Ns540p314 Ns540p163 Ns540p313 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p316 := Ns540p233 250958 BSN.abs_quadSignPos (BSN.cos_quad_nat0 180 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 527180420 536870912) BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 325201029 536870912) qz37 rfl rfl (Ns540p309 rfl) (Ns540p273 rfl) RS541to552.d43 RS541to552.d45 RS541to552.d47 RS541to552.d49 RS541to552.d17 (Ns540p311 rfl rfl) (Ns540p315 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p317 := nat_lit 162636564452039912131336666372401 

noncomputable def Ns540p318 := BSN.cos_dyadic_bound_f 112928757 536870912 2 1 536870912 268435456 Ns540p317 Ns540p136 Ns540p317 Ns540p317 Ns540p137 Ns540p317 525037572 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 112928757) qz19 0 1 Ns540p317 Ns540p136 Ns540p317 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 112928757) qz378 0 1 Ns540p317 Ns540p137 Ns540p317 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p319 := Ns540p231 Bool.false 180963014 250958 Bool.true 112928757 28296951008113761 1 Bool.false 525037572 Bool.false Bool.false 332528310 267560 BSN.abs_quadSignPos qz380 (BSN.sfrac_eq_quadSignPos_mul Bool.false 525037572 536870912) qz37 rfl (Ns540p316 rfl) (Ns540p273 rfl) RS541to552.d51 RS541to552.d53 RS541to552.d17 (Ns540p318 rfl rfl) rfl 

noncomputable def Ns540p320 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz34) qz34 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz34) qz34 12) 332528310 536870912 267560 536870912 332528310 536870912 267560 536870912 357049554111037440 166264155 134217728 33445 33554432 (Ns540p319 rfl rfl rfl rfl) 

noncomputable def Ns540p321 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz35) (Zeta.RiemannSiegel.correction qz36) 19236923 67108864 1 67108864 1343667892621275 2251799813685248 20359679689709793 1352487263094702080000 25848035787927735336825 151115727451828646838272 

noncomputable def Ns540p322 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz35 1 1 0 1 19236923 67108864 1 67108864 19236923 67108864 1 67108864 

noncomputable abbrev qz43 := qz391

noncomputable def Ns540p323 := @Enclosure.Real.IsNear.sqrt_image qz43 9939327085009 67108864000 930587 67108864000 408355509 408355548 33554432 (@Enclosure.Real.IsNear.of_eq qz43 (@HMul.hMul Real Real Real qz5 qz34 qz3) Bool.false 9939327085009 67108864000 930587 67108864000 (BSN.t_div_two_pi_mk qz34 930587 1000 qz37) (@Enclosure.Real.IsNear.mulLit_ff qz34 qz3 930587 1000 0 1 10680707 67108864 1 67108864 9939327085009 67108864000 930587 67108864000 (Enclosure.Real.IsNear.const Bool.false 930587 1000) RS541to552.d56 rfl)) 

noncomputable abbrev qz729 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 930587 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz603 := qz729

noncomputable abbrev qz398 := qz603

noncomputable abbrev qz44 := qz398

noncomputable def Ns540p324 := @Enclosure.Real.IsNear.sqrt_image qz44 816711057 67108864 39 67108864 117056128 117056134 33554432 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 816711057 67108864 39 67108864 816711057 67108864 39 67108864 (Ns540p323 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns540p325 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz44) 117056131 33554432 3 33554432 9618461 9618462 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz44) Bool.false 234112262 67108864 6 67108864 117056131 33554432 3 33554432 (Ns540p324 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns540p326 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 19236923 67108864 1 67108864 19236923 67108864 1 67108864 (Ns540p325 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz45 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz392))

noncomputable abbrev qz604 := (@HMul.hMul Real Real Real qz717 qz728 qz728)

noncomputable abbrev qz399 := (@HSub.hSub Real Real Real qz582 (@HSub.hSub Real Real Real qz582 qz604 qz599) qz594)

noncomputable abbrev qz46 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz399))

noncomputable def Ns540p327 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz36) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz45) qz46) Bool.false 1343667892621275 

noncomputable def Ns540p328 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz45) qz46 139210695 67108864 1089 

noncomputable def Ns540p329 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz45) Bool.false 139210695 67108864 1089 67108864 139210695 67108864 1089 

noncomputable def Ns540p330 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 16175480 33554432 1215584432 322458091520000 2021935 4194304 75974027 20153630720000 

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz355 qz352 qz392)

noncomputable def Ns540p331 := @Enclosure.Real.IsNear.cos_image qz47 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 35828887) qz384) Bool.false 35828887 33554432 123 33554432 Bool.false 16175480 33554432 1 

noncomputable def Ns540p332 := nat_lit 1052456941050683305303691601 

noncomputable def Ns540p333 := nat_lit 288230376151711744000000000000000 

noncomputable def Ns540p334 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz36 884279719003555 140737488355328 1 500000000000000 11404689 67108864 39 67108864 10084935184242934669395 9444732965739290427392 Ns540p332 

noncomputable def Ns540p335 := @Enclosure.Real.IsNear.subLit_ff_p qz44 qz1 816711057 67108864 39 67108864 12 1 0 1 11404689 11404689 67108864 39 

noncomputable def Ns540p336 := @Ns540p335 67108864 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 816711057 67108864 39 67108864 816711057 67108864 39 67108864 (Ns540p323 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns540p337 := @Enclosure.Real.IsNear.recentre' qz47 Bool.false 10084935184242934669395 9444732965739290427392 Ns540p332 Ns540p333 35828887 33554432 123 33554432 (@Ns540p334 Ns540p333 RS541to552.d55 (Ns540p336 rfl rfl) rfl) 

noncomputable def Ns540p338 := nat_lit 3512190316495439626453081182359194266691198140617199160120756801 

noncomputable def Ns540p339 := nat_lit 2715604617782180571563196748146123545569136044930237474720321 

noncomputable def Ns540p340 := nat_lit 10531139740250754518216117153581290552982456149761737005412829761 

noncomputable def Ns540p341 := BSN.cos_dyadic_bound_f 35828887 33554432 3 2 33554432 9610000 Ns540p338 Ns540p201 Ns540p339 Ns540p340 Ns540p204 Ns540p339 16175480 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 35828887) qz595 0 2 Ns540p338 Ns540p201 Ns540p339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 35828887) (BSN.cosOddQ 33554432) 0 2 Ns540p340 Ns540p204 Ns540p339 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p342 := @Enclosure.Real.IsNear.inv_image qz45 2021935 4194304 75974027 20153630720000 69604803 69605892 33554432 (Ns540p330 (@Ns540p331 9610000 (Ns540p337 rfl) (Enclosure.sfrac_false_div 35828887 33554432) (Ns540p341 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns540p343 := @Enclosure.Real.IsNear.recentre' qz46 Bool.false 9652045 33554432 

noncomputable abbrev qz48 := (@HMul.hMul Real Real Real qz355 qz352 qz399)

noncomputable def Ns540p344 := @Enclosure.Real.IsNear.cos_image qz48 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 42916809)) qz384) Bool.true 42916809 33554432 

noncomputable def Ns540p345 := nat_lit 810675607678956750865416606205 

noncomputable def Ns540p346 := nat_lit 18927023792972365042490265109327621 

noncomputable def Ns540p347 := @Enclosure.Real.IsNear.recentre' qz48 Bool.true Ns540p345 Ns540p210 Ns540p346 

noncomputable def Ns540p348 := nat_lit 3868562622766813359059763200000000000000 

noncomputable abbrev qz49 := qz399

noncomputable def Ns540p349 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz49 884279719003555 140737488355328 1 500000000000000 916763768587231 

noncomputable abbrev qz400 := (@HSub.hSub Real Real Real qz582 qz604 qz599)

noncomputable abbrev qz50 := qz400

noncomputable def Ns540p350 := @Enclosure.Real.IsNear.subLit_tf qz50 qz30 635288791876575 4503599627370496 3506812959 4503599627370496 1 16 

noncomputable abbrev qz401 := qz604

noncomputable abbrev qz51 := qz401

noncomputable def Ns540p351 := @Enclosure.Real.IsNear.subLit_ff_n qz51 qz36 130066931186721 4503599627370496 889567263 4503599627370496 11404689 67108864 39 67108864 

noncomputable def Ns540p352 := @Enclosure.Real.IsNear.mulLit_ff qz36 qz36 11404689 67108864 39 67108864 11404689 67108864 39 67108864 130066931186721 4503599627370496 

noncomputable def Ns540p353 := nat_lit 108974769977485620261124315350806040876178192168418814373800006059146786562888722085514810952801761 

noncomputable def Ns540p354 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600 

noncomputable def Ns540p355 := nat_lit 39041732362828932905302022266351835280040108977471545966240785861015928735439095300683750881 

noncomputable def Ns540p356 := nat_lit 660412445052857608449574038711308059204706796447733554608498092654865802346765022695744285205618145 

noncomputable def Ns540p357 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600 

noncomputable def Ns540p358 := BSN.cos_dyadic_bound_f 42916809 33554432 4 3 33554432 9610000 Ns540p353 Ns540p354 Ns540p355 Ns540p356 Ns540p357 Ns540p355 9652045 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 42916809) qz595 0 3 Ns540p353 Ns540p354 Ns540p355 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 42916809) (BSN.cosOddQ 33554432) 0 3 Ns540p356 Ns540p357 Ns540p355 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p359 := @Ns540p343 3228798864 644916183040000 9652045 33554432 201799929 40307261440000 (@Ns540p344 329 67108864 Bool.false 9652045 33554432 1 9610000 (@Ns540p347 Ns540p348 42916809 33554432 329 67108864 (@Ns540p349 4503599627370496 3506812959 4503599627370496 Ns540p345 Ns540p210 Ns540p346 Ns540p348 RS541to552.d55 (@Ns540p350 0 1 14668220297395696 916763768587231 4503599627370496 3506812959 4503599627370496 (@Ns540p351 42633509134769376460800 635288791876575 4503599627370496 3506812959 4503599627370496 (@Ns540p352 889567263 4503599627370496 (Ns540p336 rfl rfl) (Ns540p336 rfl rfl) rfl) (Ns540p336 rfl rfl) rfl rfl) qz389 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 42916809 33554432) (BSN.cos_neg_of_bound 42916809 33554432 Bool.false 9652045 33554432 1 9610000 (Ns540p358 rfl rfl)) rfl rfl) 

noncomputable def Ns540p360 := @Ns540p321 392464651383296523293607 Ns540p228 (Ns540p322 qz32 (@Enclosure.Real.IsNear.of_eq qz35 (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 19236923 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz43 (BSN.t_div_two_pi_nonneg qz34 930587 1000 qz37)) Ns540p326) rfl) (@Ns540p327 2251799813685248 20359679689709793 1352487263094702080000 (BSN.correction_mk qz36 (BSN.cos_two_pi_p_ne_zero_mk qz34 930587 1000 12 qz37 rfl rfl (@BSN.floor_sqrt_eq_dec qz34 930587 1000 12 qz37 rfl rfl rfl))) (@Ns540p328 67108864 9652045 33554432 201799929 40307261440000 1343667892621275 2251799813685248 20359679689709793 1352487263094702080000 (@Ns540p329 67108864 (Ns540p342 rfl rfl rfl rfl rfl) rfl) (Ns540p359 rfl) rfl)) 

noncomputable def Ns540p361 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz34) (hardyZApproximantRS₀ qz34) Bool.false 161348760837839862005895 151115727451828646838272 Ns540p227 Ns540p228 (@Eq.refl Real (hardyZApproximantRS₀ qz34)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz34) (@HSub.hSub Real Real Real qz33 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz34) qz34 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz35) (Zeta.RiemannSiegel.correction qz36))) Bool.false 161348760837839862005895 151115727451828646838272 Ns540p227 Ns540p228 (BSN.hardyZApproximantRS₀_eq qz34 12 (@BSN.floor_sqrt_eq_dec qz34 930587 1000 12 qz37 rfl rfl rfl)) (@Ns540p230 161348760837839862005895 151115727451828646838272 Ns540p227 Ns540p228 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz34) qz34 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz34) qz34 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz34) qz34 12)) Bool.false 166264155 134217728 33445 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz34) qz34 12) (Ns540p320 (Ns540p319 rfl rfl rfl rfl) rfl rfl)) (Ns540p360 rfl) rfl rfl)) 

theorem RS541to552.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz34) Bool.false 161348760837839862005895 151115727451828646838272 Ns540p227 Ns540p228 := Ns540p361 

noncomputable abbrev qz605 := (@HMul.hMul Real Real Real qz717 (Real.sqrt qz725) qz719)

noncomputable abbrev qz402 := qz605

noncomputable abbrev qz52 := (@Inv.inv Real Real.instInv qz402)

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz579 (@HMul.hMul Real Real Real qz579 qz605 qz605) qz605)

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz355 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz403))

noncomputable abbrev qz404 := (@HMul.hMul Real Real Real qz579 qz592 qz592)

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz355 qz404 qz382))

noncomputable abbrev qz606 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz52)

noncomputable def Ns540p362 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz373 (@HAdd.hAdd Real Real Real qz373 qz606 qz53) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz54)) Bool.false 

noncomputable def Ns540p363 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz373 qz606 qz53) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz54) 26021001 2147483648 

noncomputable def Ns540p364 := @Enclosure.Real.IsNear.addLit_ff qz606 qz53 3252625 268435456 25 268435456 

noncomputable def Ns540p365 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz52 25 4 0 1 130105 67108864 1 67108864 3252625 

noncomputable def Ns540p366 := @Enclosure.Real.IsNear.recentre' qz52 Bool.false 130105 67108864 1 67108864 130105 67108864 1 67108864 

noncomputable def Ns540p367 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz20 234033165 67108864 7 67108864 992590143631 6710886400 92933 6710886400 46459802572353504423 90071992547409920 28697535778893 

noncomputable def Ns540p368 := @Enclosure.Real.IsNear.sqrt_image qz20 992590143631 6710886400 92933 6710886400 408079620 408079659 33554432 qz21 

noncomputable def Ns540p369 := @Enclosure.Real.IsNear.sqrt_image qz22 816159279 67108864 39 67108864 117016579 117016586 33554432 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 816159279 67108864 39 67108864 816159279 67108864 39 67108864 (Ns540p368 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz405 := (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 234033165 67108864 7 67108864 234033165 67108864 7 67108864 (Ns540p369 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns540p370 := @Ns540p367 450359962737049600 qz405 

noncomputable def Ns540p371 := Ns540p370 qz21 

noncomputable abbrev qz55 := qz402

noncomputable def Ns540p372 := @Enclosure.Real.IsNear.inv_image qz55 46459802572353504423 90071992547409920 28697535778893 450359962737049600 65052 65053 33554432 (Ns540p371 rfl) rfl rfl 

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv qz403)

noncomputable def Ns540p373 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz56 1 32 0 1 1 

noncomputable def Ns540p374 := @Enclosure.Real.IsNear.recentre' qz56 Bool.false 1 67108864 1 67108864 

noncomputable def Ns540p375 := nat_lit 100284099679991677733322107929184361314569406001986731334967 

noncomputable def Ns540p376 := nat_lit 730750818665451459101842416358141509827966271488000 

noncomputable def Ns540p377 := nat_lit 4645801426405456907507342262081014794201538864240921637 

noncomputable def Ns540p378 := nat_lit 91343852333181432387730302044767688728495783936000000 

noncomputable abbrev qz57 := qz403

noncomputable def Ns540p379 := @Enclosure.Real.IsNear.inv_image qz57 Ns540p375 Ns540p376 Ns540p377 Ns540p378 0 1 

noncomputable def Ns540p380 := nat_lit 2158513255062065306585942517289080562929 

noncomputable def Ns540p381 := nat_lit 8112963841460668169578900514406400 

noncomputable def Ns540p382 := nat_lit 13332819289552757086242218439742839 

noncomputable def Ns540p383 := nat_lit 202824096036516704239472512860160000 

noncomputable abbrev qz406 := (@HMul.hMul Real Real Real qz579 qz605 qz605)

noncomputable abbrev qz58 := qz406

noncomputable def Ns540p384 := @Enclosure.Real.IsNear.mulLit_ff qz58 qz55 Ns540p380 Ns540p381 Ns540p382 Ns540p383 46459802572353504423 90071992547409920 28697535778893 

noncomputable def Ns540p385 := @Enclosure.Real.IsNear.mulLit_ff qz55 qz55 46459802572353504423 90071992547409920 28697535778893 450359962737049600 46459802572353504423 90071992547409920 28697535778893 450359962737049600 Ns540p380 

noncomputable def Ns540p386 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz54 13 10 0 1 1582295 67108864 1 

noncomputable def Ns540p387 := @Enclosure.Real.IsNear.recentre' qz54 Bool.false 1582295 67108864 1 67108864 1582295 67108864 

noncomputable def Ns540p388 := nat_lit 12818352720398370704767125 

noncomputable abbrev qz59 := qz404

noncomputable def Ns540p389 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz23 54771522319917225 4503599627370496 3276464359 4503599627370496 234033165 67108864 7 67108864 Ns540p388 

noncomputable def Ns540p390 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz23 234033165 67108864 7 67108864 234033165 67108864 7 67108864 54771522319917225 4503599627370496 3276464359 

noncomputable def Ns540p391 := @Ns540p390 4503599627370496 qz405 

noncomputable def Ns540p392 := Ns540p391 qz405 

noncomputable def Ns540p393 := @Ns540p389 302231454903657293676544 1150202003121137323 302231454903657293676544 (Ns540p392 rfl) qz405 

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz355 qz404 qz382)

noncomputable def Ns540p394 := @Enclosure.Real.IsNear.inv_image qz60 Ns540p388 302231454903657293676544 1150202003121137323 302231454903657293676544 791147 791148 33554432 (Ns540p393 rfl) 

noncomputable def Ns540p395 := @Ns540p363 201 2147483648 4113967 134217728 13 671088640 12327156495417344 91844473 2147483648 1213 10737418240 (@Ns540p364 1 2147483648 1 2147483648 6984959269011456 26021001 2147483648 201 2147483648 (@Ns540p365 268435456 25 268435456 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns540p366 (Ns540p372 rfl rfl rfl rfl) rfl) rfl) (@Ns540p373 67108864 1 67108864 1 2147483648 1 2147483648 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns540p374 1 67108864 1 67108864 (@Ns540p379 33554432 (@Ns540p384 450359962737049600 Ns540p375 Ns540p376 Ns540p377 Ns540p378 (@Ns540p385 Ns540p381 Ns540p382 Ns540p383 (Ns540p371 rfl) (Ns540p371 rfl) rfl) (Ns540p371 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns540p386 67108864 4113967 134217728 13 671088640 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns540p387 1 67108864 (Ns540p394 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS541to552.d60 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 := @Ns540p362 91844473 2147483648 1213 10737418240 (BSN.hardyZErrorBoundRS₀_mk qz4 929330 1000 qz9 rfl rfl) (Ns540p395 rfl rfl) 

noncomputable def Ns540p396 := nat_lit 45511341012230349195712029 

noncomputable def Ns540p397 := nat_lit 45381941900377290503618560000 

noncomputable def Ns540p398 := nat_lit 460996764393336507128086528 

noncomputable abbrev qz730 := (Enclosure.sfrac Bool.false 931844 1000)

noncomputable abbrev qz607 := qz730

noncomputable abbrev qz407 := qz607

noncomputable abbrev qz61 := qz407

noncomputable abbrev qz731 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 931844 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz608 := qz731

noncomputable abbrev qz408 := qz608

noncomputable abbrev qz62 := (@HPow.hPow Real Real Real qz356 qz408 qz358)

noncomputable abbrev qz732 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 931844 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz609 := qz732

noncomputable abbrev qz409 := qz609

noncomputable abbrev qz63 := qz409

noncomputable def Ns540p399 := @Enclosure.Real.IsNear.subLit_ff_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz62) (Zeta.RiemannSiegel.correction qz63)) 1016183 8388608 66979 67108864 197970139897920808515 1180591620717411303424 217218814820323887552029 Ns540p397 Ns540p398 

noncomputable def Ns540p400 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.cos BSN.quadSignPos 11 12 931844 1000 288 536870912 268435456 9007199254740992 Bool.false 1000171048450 4438 1334074092 57 154981288 8 

noncomputable def Ns540p401 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 931844 1000 179 236 536870912 268435456 9007199254740992 Bool.false 1000171048450 4438 

noncomputable def Ns540p402 := Ns540p401 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 402736184 215719 Bool.true 812717433 Bool.true 425542253 28296951008113761 1 Bool.false 535999241 Bool.false Bool.false 376868161 Bool.false Bool.true 119608314 

noncomputable def Ns540p403 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 931844 1000 47 117 536870912 268435456 9007199254740992 Bool.false 1000171048450 4438 

noncomputable def Ns540p404 := Ns540p403 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 435719684 176167 Bool.true 496038223 Bool.true 388475223 28296951008113761 1 Bool.false 428414554 Bool.false Bool.false 355451770 Bool.true Bool.true 402736184 

noncomputable def Ns540p405 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 931844 1000 123 31 536870912 268435456 9007199254740992 Bool.false 1000171048450 4438 

noncomputable def Ns540p406 := Ns540p405 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 629997696 130898 Bool.false 62011531 Bool.false 528493281 28296951008113761 1 Bool.false 61873734 Bool.false Bool.false 447180024 Bool.false Bool.true 435719684 

noncomputable def Ns540p407 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 931844 1000 363 231 536870912 268435456 9007199254740992 Bool.false 1000171048450 4438 

noncomputable def Ns540p408 := Ns540p407 744261104 56 268435448 8 864060384 56 240095976 8 Bool.true 934716901 77245 Bool.false 512511332 Bool.false 195832122 28296951008113761 1 Bool.false 438139325 Bool.false Bool.false 191518211 Bool.false Bool.true 629997696 

noncomputable def Ns540p409 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 931844 1000 774 534 536870912 268435456 9007199254740992 Bool.false 1000171048450 4438 

noncomputable def Ns540p410 := Ns540p409 372130544 56 379625064 8 589812976 56 309962568 8 Bool.true 536870776 4496 Bool.false 677734850 Bool.false 227232253 28296951008113761 1 Bool.false 162967442 Bool.true Bool.false 489496158 Bool.true Bool.true 934716901 

noncomputable def Ns540p411 := nat_lit 301749392054914600551318654382960952468959115051035031 

noncomputable def Ns540p412 := nat_lit 161972766117255296152495551741274649139198138777600 

noncomputable def Ns540p413 := nat_lit 3936256000000000000000000 

noncomputable def Ns540p414 := nat_lit 337254396681645940039399510507520000 

noncomputable def Ns540p415 := nat_lit 1885611169473911823617475476829272801280 

noncomputable abbrev qz610 := (@Eq.refl Real qz730)

noncomputable abbrev qz410 := qz610

noncomputable abbrev qz64 := qz410

noncomputable def Ns540p416 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz61 931844 1000 3473333961344 16000000 1863688 4000 2000 Ns540p414 Ns540p415 qz64 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns540p417 := nat_lit 3164071705233741321876995093382676636960912730237541086658560 

noncomputable abbrev qz611 := (@HSub.hSub Real Real Real qz721 qz722 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz723 (@Nat.cast Real Real.instNatCast 1863688))))

noncomputable abbrev qz411 := (@HSub.hSub Real Real Real qz582 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 931844 4000) (Real.log (Enclosure.sfrac Bool.false 3473333961344 16000000))) (@HMul.hMul Real Real Real qz579 qz583 qz611))

noncomputable abbrev qz612 := (Enclosure.sfrac Bool.false 931844 2000)

noncomputable abbrev qz65 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz411 qz612) (@HMul.hMul Real Real Real qz355 qz612 (Real.log Real.pi)))

noncomputable def Ns540p418 := @Enclosure.Real.IsNear.addLit_ft_p qz65 (Enclosure.sfrac Bool.true Ns540p414 Ns540p415) 1678008732780405050827 900719925474099200 32526434896570044647 Ns540p413 Ns540p414 Ns540p415 0 1 Ns540p417 

noncomputable def Ns540p419 := nat_lit 140761574798715680526077788160000 

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz361 qz411 qz612)

noncomputable def Ns540p420 := @Enclosure.Real.IsNear.subLit_ff_p qz66 (@HMul.hMul Real Real Real qz5 qz612 (Real.log Real.pi)) 10792060305938085643511 4503599627370496000 1468508153001991 480500000000000000000 8948209293321 16777216000 698883 134217728000 Ns540p419 1678008732780405050827 900719925474099200 

noncomputable def Ns540p421 := nat_lit 21584120611876171287022000 

noncomputable abbrev qz67 := qz411

noncomputable def Ns540p422 := @Enclosure.Real.IsNear.subLit_ff_p qz67 qz612 12890386451521801880823 4503599627370496000 1468508153001991 480500000000000000000 931844 2000 0 1 Ns540p421 10792060305938085643511 4503599627370496000 1468508153001991 480500000000000000000 

noncomputable def Ns540p423 := nat_lit 29026569809867638575792691381329199104 

noncomputable def Ns540p424 := nat_lit 118842599302855531759140864 

noncomputable def Ns540p425 := nat_lit 120638201703928141962154388640614653457268560208728476135272805466885847960922422720848508872839449178880947572141277489935282359521143507567360514553397903360 

noncomputable def Ns540p426 := nat_lit 2548298908577024556045607866998654142919016629590425579530468041327172499081948235662274844857798557132430477687590098225416754848638520830143195321353633792 

noncomputable def Ns540p427 := nat_lit 479661459671685146524592698457680420100297954181368579651970276485405312644992088324508248515482626980616518511203606146934901651892296970209559838720 

noncomputable def Ns540p428 := BSN.log_dyadic_bound 1376181961344 5570485961344 7 6 Ns540p425 268435456 76880000 Ns540p426 Ns540p427 135435000 6946667922688 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1376181961344) (BSN.artanhQ 5570485961344) 0 6 Ns540p426 Ns540p425 Ns540p427 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz412 := (Real.log (Enclosure.sfrac Bool.false 3473333961344 16000000))

noncomputable def Ns540p429 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 931844 4000) qz412 931844 4000 0 1 55340397778365543 4503599627370496 12500016337 961000000000000000 12892154406845815262823 4503599627370496000 2912016305883857 961000000000000000000 (Enclosure.Real.IsNear.const Bool.false 931844 4000) (BSN.isNear_log_sfrac 3473333961344 16000000 55340397778365543 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3473333961344) qz364)) Bool.false Ns540p424 Ns540p114 1000001306960000 76880000000000000000000 55340397778365543 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3473333961344 16000000 17 6946667922688 4194304000000 135435000 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns540p428 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p430 := BSN.arctan_dyadic_bound_f 1000 1863688 1 0 33554432 9610000 0 1 1 0 1 1 18004 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1863688) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1863688) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns540p431 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1863688))) 884279719003555 562949953421312 1 2000000000000000 18004 33554432 1 9610000 29661368349322496704512 883977662006691 562949953421312 200000000961 1922000000000000000 qz15 (Ns540p430 rfl) rfl rfl 

noncomputable abbrev qz413 := (@HMul.hMul Real Real Real qz579 qz583 qz611)

noncomputable abbrev qz68 := qz413

noncomputable abbrev qz414 := qz611

noncomputable abbrev qz69 := qz414

noncomputable def Ns540p432 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 931844 4000) qz412) qz68 12892154406845815262823 4503599627370496000 2912016305883857 961000000000000000000 883977662006691 2251799813685248 200000000961 7688000000000000000 Ns540p423 12890386451521801880823 4503599627370496000 1468508153001991 480500000000000000000 (Ns540p429 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz69 1 4 0 1 883977662006691 562949953421312 200000000961 1922000000000000000 883977662006691 2251799813685248 200000000961 7688000000000000000 qz372 Ns540p431 rfl) 

noncomputable def Ns540p433 := @Ns540p418 Ns540p411 Ns540p412 32526434896570044647 Ns540p413 (@Ns540p420 32526434896570044647 Ns540p413 (Ns540p422 (Ns540p432 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 931844 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz612 (Real.log Real.pi) 931844 2000 0 1 38410761 33554432 3 268435456 8948209293321 16777216000 698883 134217728000 (Enclosure.Real.IsNear.const Bool.false 931844 2000) RS541to552.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns540p414 Ns540p415) 

noncomputable def Ns540p434 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz61) Bool.false Ns540p411 Ns540p412 32526434896570044647 Ns540p413 1953459079 1048576 555 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz61) (@HAdd.hAdd Real Real Real qz373 qz65 (Enclosure.sfrac Bool.true Ns540p414 Ns540p415)) Bool.false Ns540p411 Ns540p412 32526434896570044647 Ns540p413 Ns540p416 (Ns540p433 rfl rfl)) 

noncomputable def Ns540p435 := nat_lit 14355015324914620971551709614698760615251485675074982760250626535178249509928953789207217306608159688439901513286650416775788708837864000000000 

noncomputable def Ns540p436 := nat_lit 10196729781834693752104840346000140772592879631247887704775121040030881902431741928975451114868994698002859142103027587890625000000000000 

noncomputable def Ns540p437 := nat_lit 71686044005658328641954851818499462090756350838046020340745349844718151001854926360274848844512696157624282262784128704063401581689320000000000 

noncomputable def Ns540p438 := BSN.sin_dyadic_bound_f 215793524950 137438953472 4 3 67108864 19238770 Ns540p435 Ns540p267 Ns540p436 Ns540p437 Ns540p270 Ns540p436 67108847 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215793524950) (BSN.sinEvenQ 137438953472) 0 3 Ns540p435 Ns540p267 Ns540p436 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215793524950) (BSN.sinOddQ 137438953472) 0 3 Ns540p437 Ns540p270 Ns540p436 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p439 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz61) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1953459079) (@Nat.cast Real Real.instNatCast 1048576)) Bool.false 1953459079 1048576 555 67108864 Bool.true 67108847 67108864 1 9610000 (Ns540p434 rfl) (Enclosure.sfrac_false_div 1953459079 1048576) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1953459079) (@Nat.cast Real Real.instNatCast 1048576)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 237267489881878679257088) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 67108847 67108864 296 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q1 1953459079 1048576 226375608064910080 72057594037927936 296 237267489881878679257088 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108847 67108864 237267489881878679257088 151115727451828646838272 215793524950 137438953472 19238770 19220000 (Ns540p438 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns540p440 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz61) Bool.false Ns540p411 Ns540p412 32526434896570044647 Ns540p413 1000171048450 536870912 4438 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz61) (@HAdd.hAdd Real Real Real qz373 qz65 (Enclosure.sfrac Bool.true Ns540p414 Ns540p415)) Bool.false Ns540p411 Ns540p412 32526434896570044647 Ns540p413 Ns540p416 (Ns540p433 rfl rfl)) 

noncomputable def Ns540p441 := Ns540p410 77245 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 774 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 162967442 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 534 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 489496158 536870912) qz64 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 1) Bool.true 67108847 67108864 337541179 40307261440000 536870776 536870912 4496 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz61)) Bool.true 67108847 67108864 337541179 40307261440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz61) qz61) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz61)) Bool.true 67108847 67108864 5400658864 644916183040000 67108847 67108864 337541179 40307261440000 (Ns540p439 rfl rfl) rfl)) rfl) (Ns540p440 rfl) RS541to552.d7 

noncomputable def Ns540p442 := nat_lit 29105839739992559054499650267340173093839876509746311060430588477332117691955124012906477396552306747240000000000 

noncomputable def Ns540p443 := nat_lit 9391129262553791052920137225268180411747042258107854340626229011964404410622779858554931640625000000000000 

noncomputable def Ns540p444 := nat_lit 176397702296789732457937801475409849539958059230226326709453520430375696501714756277710173355710668433256000000000 

noncomputable def Ns540p445 := BSN.cos_dyadic_bound_f 677734850 536870912 4 3 536870912 268435456 Ns540p442 Ns540p153 Ns540p443 Ns540p444 Ns540p156 Ns540p443 162967442 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 677734850) qz19 0 3 Ns540p442 Ns540p153 Ns540p443 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 677734850) qz378 0 3 Ns540p444 Ns540p156 Ns540p443 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p446 := nat_lit 372114825212648287516705018081418112584594665238044179399295928684161441 

noncomputable def Ns540p447 := nat_lit 7108202573803075216259109249230513504338732185661273692407773702561 

noncomputable def Ns540p448 := nat_lit 1116330259232797256399682536025755876726775318249761215650502970505079201 

noncomputable def Ns540p449 := BSN.cos_dyadic_bound_f 227232253 536870912 3 2 536870912 268435456 Ns540p446 Ns540p160 Ns540p447 Ns540p448 Ns540p163 Ns540p447 489496158 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 227232253) qz19 0 2 Ns540p446 Ns540p160 Ns540p447 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 227232253) qz378 0 2 Ns540p448 Ns540p163 Ns540p447 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p450 := nat_lit 17337817557786308587861519274963674106403221009688491388300294340428759040 

noncomputable def Ns540p451 := nat_lit 4760228270239029375098409553461196046219980899537077681430671067774976 

noncomputable def Ns540p452 := nat_lit 45400862757955183111125248295151637866028841722965845986445121233679876096 

noncomputable def Ns540p453 := BSN.sin_dyadic_bound_f 512511332 536870912 3 2 536870912 268435456 Ns540p450 Ns540p276 Ns540p451 Ns540p452 Ns540p279 Ns540p451 438139325 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 512511332) qz376 0 2 Ns540p450 Ns540p276 Ns540p451 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 512511332) qz377 0 2 Ns540p452 Ns540p279 Ns540p451 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p454 := nat_lit 1470739374587058292918280899677456 

noncomputable def Ns540p455 := BSN.sin_dyadic_bound_f 195832122 536870912 2 1 536870912 268435456 Ns540p454 Ns540p282 Ns540p454 Ns540p454 Ns540p283 Ns540p454 191518211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 195832122) qz376 0 1 Ns540p454 Ns540p282 Ns540p454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 195832122) qz377 0 1 Ns540p454 Ns540p283 Ns540p454 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p456 := Ns540p408 130898 BSN.abs_quadSignPos (BSN.cos_quad_nat3 363 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 438139325 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 231 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 191518211 536870912) qz64 rfl rfl (Ns540p441 RS541to552.d9 RS541to552.d11 RS541to552.d13 RS541to552.d17 (Ns540p445 rfl rfl) (Ns540p449 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns540p440 rfl) RS541to552.d19 RS541to552.d21 RS541to552.d23 RS541to552.d25 RS541to552.d17 (Ns540p453 rfl rfl) (Ns540p455 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns540p457 := nat_lit 14787331707733049627119092809521 

noncomputable def Ns540p458 := BSN.sin_dyadic_bound_f 62011531 536870912 2 1 536870912 268435456 Ns540p457 Ns540p282 Ns540p457 Ns540p457 Ns540p283 Ns540p457 61873734 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 62011531) qz376 0 1 Ns540p457 Ns540p282 Ns540p457 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 62011531) qz377 0 1 Ns540p457 Ns540p283 Ns540p457 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p459 := nat_lit 19604420233244125553443087802583221498753193838029446546662366356094371585 

noncomputable def Ns540p460 := nat_lit 6085773183686517912629795949380246945449937833585686649869260635293441 

noncomputable def Ns540p461 := nat_lit 51335056978103883991920972194276107335013350628822745081920694986837640961 

noncomputable def Ns540p462 := BSN.sin_dyadic_bound_f 528493281 536870912 3 2 536870912 268435456 Ns540p459 Ns540p276 Ns540p460 Ns540p461 Ns540p279 Ns540p460 447180024 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 528493281) qz376 0 2 Ns540p459 Ns540p276 Ns540p460 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 528493281) qz377 0 2 Ns540p461 Ns540p279 Ns540p460 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p463 := Ns540p406 176167 BSN.abs_quadSignPos (BSN.cos_quad_nat3 123 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 61873734 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 447180024 536870912) qz64 rfl rfl (Ns540p456 rfl rfl) (Ns540p440 rfl) RS541to552.d27 RS541to552.d29 RS541to552.d31 RS541to552.d33 RS541to552.d17 (Ns540p458 rfl rfl) (Ns540p462 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p464 := nat_lit 15213407701622643229049728422626561370724256908256331201675419491797381505 

noncomputable def Ns540p465 := nat_lit 3665398047330240678034869896979128394571542433216905264514839409668481 

noncomputable def Ns540p466 := nat_lit 39838704764554102353080089412760170715448509405303278157769265119472726401 

noncomputable def Ns540p467 := BSN.sin_dyadic_bound_f 496038223 536870912 3 2 536870912 268435456 Ns540p464 Ns540p276 Ns540p465 Ns540p466 Ns540p279 Ns540p465 428414554 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 496038223) qz376 0 2 Ns540p464 Ns540p276 Ns540p465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 496038223) qz377 0 2 Ns540p466 Ns540p279 Ns540p465 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p468 := nat_lit 5722080347190689796940778674870783973878140121581054227111450314761917505 

noncomputable def Ns540p469 := nat_lit 518688473808522103358478605487859809119221899703861194415625457980481 

noncomputable def Ns540p470 := nat_lit 14985561127970402337153744706919358634751793006779431010024744573634958401 

noncomputable def Ns540p471 := BSN.sin_dyadic_bound_f 388475223 536870912 3 2 536870912 268435456 Ns540p468 Ns540p276 Ns540p469 Ns540p470 Ns540p279 Ns540p469 355451770 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 388475223) qz376 0 2 Ns540p468 Ns540p276 Ns540p469 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 388475223) qz377 0 2 Ns540p470 Ns540p279 Ns540p469 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p472 := Ns540p404 215719 BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 428414554 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 355451770 536870912) qz64 rfl rfl (Ns540p463 rfl) (Ns540p440 rfl) RS541to552.d35 RS541to552.d37 RS541to552.d39 RS541to552.d41 RS541to552.d17 (Ns540p467 rfl rfl) (Ns540p471 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p473 := nat_lit 156520106231386483770573868900617038401781054631030741845994673557878110600764784651975352397053710465454118640161 

noncomputable def Ns540p474 := nat_lit 83037622662434188974523488750965034145788888361906031607336489835977132535183145321606338185945259933014561 

noncomputable def Ns540p475 := nat_lit 781761512574676660898965059772599624229027979311701887210071495718722556329712733737342518936748877294596446591521 

noncomputable def Ns540p476 := BSN.sin_dyadic_bound_f 812717433 536870912 4 3 536870912 268435456 Ns540p473 Ns540p130 Ns540p474 Ns540p475 Ns540p133 Ns540p474 535999241 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 812717433) qz376 0 3 Ns540p473 Ns540p130 Ns540p474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 812717433) qz377 0 3 Ns540p475 Ns540p133 Ns540p474 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p477 := nat_lit 4577850019685644722877848367328793845549606135386496755446907473646321441 

noncomputable def Ns540p478 := nat_lit 1075329372606036940187245636718905281892200348320514972937463545462561 

noncomputable def Ns540p479 := nat_lit 13731399400311722094753170610712943726085034005462849236394847493848039201 

noncomputable def Ns540p480 := BSN.cos_dyadic_bound_f 425542253 536870912 3 2 536870912 268435456 Ns540p477 Ns540p160 Ns540p478 Ns540p479 Ns540p163 Ns540p478 376868161 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 425542253) qz19 0 2 Ns540p477 Ns540p160 Ns540p478 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 425542253) qz378 0 2 Ns540p479 Ns540p163 Ns540p478 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz613 := (BSN.cos_quad_nat3 179 rfl)

noncomputable def Ns540p481 := Ns540p402 251291 BSN.abs_quadSignPos qz613 (BSN.sfrac_eq_quadSignPos_mul Bool.false 535999241 536870912) BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 376868161 536870912) qz64 rfl rfl (Ns540p472 rfl) (Ns540p440 rfl) RS541to552.d43 RS541to552.d45 RS541to552.d47 RS541to552.d49 RS541to552.d17 (Ns540p476 rfl rfl) (Ns540p480 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p482 := nat_lit 113476217882754958543179492119056 

noncomputable def Ns540p483 := BSN.cos_dyadic_bound_f 103211054 536870912 2 1 536870912 268435456 Ns540p482 Ns540p136 Ns540p482 Ns540p482 Ns540p137 Ns540p482 526980495 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 103211054) qz19 0 1 Ns540p482 Ns540p136 Ns540p482 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 103211054) qz378 0 1 Ns540p482 Ns540p137 Ns540p482 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p484 := Ns540p400 Bool.true 119608314 251291 Bool.true 103211054 28296951008113761 1 Bool.false 526980495 Bool.false Bool.false 32517856 267916 BSN.abs_quadSignPos qz380 (BSN.sfrac_eq_quadSignPos_mul Bool.false 526980495 536870912) qz64 rfl (Ns540p481 rfl) (Ns540p440 rfl) RS541to552.d51 RS541to552.d53 RS541to552.d17 (Ns540p483 rfl rfl) rfl 

noncomputable def Ns540p485 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 12) 32517856 536870912 267916 536870912 32517856 536870912 267916 536870912 34915782014009344 1016183 8388608 66979 67108864 (Ns540p484 rfl rfl rfl rfl) 

noncomputable def Ns540p486 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz62) (Zeta.RiemannSiegel.correction qz63) 19230433 67108864 1 67108864 10294627265955 17592186044416 22549994383717037 1352487263094702080000 197970139897920808515 1180591620717411303424 

noncomputable def Ns540p487 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz62 1 1 0 1 19230433 67108864 1 67108864 19230433 67108864 1 67108864 

noncomputable abbrev qz70 := qz408

noncomputable def Ns540p488 := @Enclosure.Real.IsNear.sqrt_image qz70 2488188183427 16777216000 232961 16777216000 408631211 408631250 33554432 (@Enclosure.Real.IsNear.of_eq qz70 (@HMul.hMul Real Real Real qz5 qz61 qz3) Bool.false 2488188183427 16777216000 232961 16777216000 (BSN.t_div_two_pi_mk qz61 931844 1000 qz64) (@Enclosure.Real.IsNear.mulLit_ff qz61 qz3 931844 1000 0 1 10680707 67108864 1 67108864 2488188183427 16777216000 232961 16777216000 (Enclosure.Real.IsNear.const Bool.false 931844 1000) RS541to552.d56 rfl)) 

noncomputable abbrev qz733 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 931844 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz614 := qz733

noncomputable abbrev qz415 := qz614

noncomputable abbrev qz71 := qz415

noncomputable def Ns540p489 := @Enclosure.Real.IsNear.sqrt_image qz71 817262461 67108864 39 67108864 117095636 117095643 33554432 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 817262461 67108864 39 67108864 817262461 67108864 39 67108864 (Ns540p488 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns540p490 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz71) 234191279 67108864 7 67108864 9615216 9615217 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz71) Bool.false 234191279 67108864 7 67108864 234191279 67108864 7 67108864 (Ns540p489 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns540p491 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 19230433 67108864 1 67108864 19230433 67108864 1 67108864 (Ns540p490 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz72 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz409))

noncomputable abbrev qz615 := (@HMul.hMul Real Real Real qz717 qz732 qz732)

noncomputable abbrev qz416 := (@HSub.hSub Real Real Real qz582 (@HSub.hSub Real Real Real qz582 qz615 qz609) qz594)

noncomputable abbrev qz73 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz416))

noncomputable def Ns540p492 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz63) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz72) qz73) Bool.false 10294627265955 

noncomputable def Ns540p493 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz72) qz73 9615261 4194304 665 

noncomputable def Ns540p494 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz72) Bool.false 153844176 67108864 1330 67108864 9615261 4194304 665 

noncomputable def Ns540p495 := @Enclosure.Real.IsNear.recentre' qz72 Bool.false 14636887 33554432 1215584432 322458091520000 14636887 33554432 75974027 20153630720000 

noncomputable abbrev qz74 := (@HMul.hMul Real Real Real qz355 qz352 qz409)

noncomputable def Ns540p496 := @Enclosure.Real.IsNear.cos_image qz74 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 75122347) qz374) Bool.false 75122347 67108864 123 33554432 Bool.false 14636887 33554432 1 

noncomputable def Ns540p497 := nat_lit 1052456941055419829597458769 

noncomputable def Ns540p498 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz63 884279719003555 140737488355328 1 500000000000000 11956093 67108864 39 67108864 10572530558420370910615 9444732965739290427392 Ns540p497 

noncomputable def Ns540p499 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz1 817262461 67108864 39 67108864 12 1 0 1 11956093 11956093 67108864 39 

noncomputable def Ns540p500 := @Ns540p499 67108864 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 817262461 67108864 39 67108864 817262461 67108864 39 67108864 (Ns540p488 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns540p501 := @Enclosure.Real.IsNear.recentre' qz74 Bool.false 10572530558420370910615 9444732965739290427392 Ns540p497 Ns540p333 75122347 67108864 123 33554432 (@Ns540p498 Ns540p333 RS541to552.d55 (Ns540p500 rfl rfl) rfl) 

noncomputable def Ns540p502 := nat_lit 1086203367319251661678352756103091883605059080603628293258096454241 

noncomputable def Ns540p503 := nat_lit 16586685937797756904922089360178093090225977525586485022553978961920 

noncomputable def Ns540p504 := nat_lit 1014269072169090512451460442832710087160812977552029383767140961 

noncomputable def Ns540p505 := nat_lit 3256581563813416804010155347423610230640855615855780821006755080801 

noncomputable def Ns540p506 := nat_lit 746400867200899060721494021208014189060168988651391826014929053286400 

noncomputable def Ns540p507 := BSN.cos_dyadic_bound_f 75122347 67108864 3 2 33554432 9610000 Ns540p502 Ns540p503 Ns540p504 Ns540p505 Ns540p506 Ns540p504 14636887 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 75122347) qz596 0 2 Ns540p502 Ns540p503 Ns540p504 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 75122347) (BSN.cosOddQ 67108864) 0 2 Ns540p505 Ns540p506 Ns540p504 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p508 := @Enclosure.Real.IsNear.inv_image qz72 14636887 33554432 75974027 20153630720000 76921423 76922753 33554432 (Ns540p495 (@Ns540p496 9610000 (Ns540p501 rfl) (Enclosure.sfrac_false_div 75122347 67108864) (Ns540p507 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns540p509 := @Enclosure.Real.IsNear.recentre' qz73 Bool.false 8565240 33554432 

noncomputable abbrev qz75 := (@HMul.hMul Real Real Real qz355 qz352 qz416)

noncomputable abbrev qz616 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns540p510 := @Enclosure.Real.IsNear.cos_image qz75 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 22023041)) qz616) Bool.true 22023041 16777216 

noncomputable def Ns540p511 := nat_lit 832006970091291914096080946245 

noncomputable def Ns540p512 := nat_lit 19159155379841444769436535769884797 

noncomputable def Ns540p513 := @Enclosure.Real.IsNear.recentre' qz75 Bool.true Ns540p511 Ns540p210 Ns540p512 

noncomputable abbrev qz76 := qz416

noncomputable def Ns540p514 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz76 884279719003555 140737488355328 1 500000000000000 940886635994359 

noncomputable abbrev qz417 := (@HSub.hSub Real Real Real qz582 qz615 qz609)

noncomputable abbrev qz77 := qz417

noncomputable def Ns540p515 := @Enclosure.Real.IsNear.subLit_tf qz77 qz30 659411659283703 4503599627370496 3549822471 4503599627370496 1 16 

noncomputable abbrev qz418 := qz615

noncomputable abbrev qz78 := qz418

noncomputable def Ns540p516 := @Enclosure.Real.IsNear.subLit_ff_n qz78 qz63 142948159824649 4503599627370496 932576775 4503599627370496 11956093 67108864 39 67108864 

noncomputable def Ns540p517 := @Enclosure.Real.IsNear.mulLit_ff qz63 qz63 11956093 67108864 39 67108864 11956093 67108864 39 67108864 142948159824649 4503599627370496 

noncomputable def Ns540p518 := nat_lit 29523041666642475280402955719903511596418835085014999418362709459875553636596186874891260725761 

noncomputable def Ns540p519 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns540p520 := nat_lit 13017495845534087777207623158499325271062951803748087268756168826311029357448233873902081 

noncomputable def Ns540p521 := nat_lit 178895731130966821038408491118172309202585701741338618291623669519393025976881232743032501635585 

noncomputable def Ns540p522 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns540p523 := BSN.cos_dyadic_bound_f 22023041 16777216 4 3 33554432 9610000 Ns540p518 Ns540p519 Ns540p520 Ns540p521 Ns540p522 Ns540p520 8565240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 22023041) (BSN.cosEvenQ 16777216) 0 3 Ns540p518 Ns540p519 Ns540p520 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 22023041) (BSN.cosOddQ 16777216) 0 3 Ns540p521 Ns540p522 Ns540p520 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p524 := @Ns540p509 3267238864 644916183040000 1070655 4194304 204202429 40307261440000 (@Ns540p510 333 67108864 Bool.false 8565240 33554432 1 9610000 (@Ns540p513 Ns540p348 22023041 16777216 333 67108864 (@Ns540p514 4503599627370496 3549822471 4503599627370496 Ns540p511 Ns540p210 Ns540p512 Ns540p348 RS541to552.d55 (@Ns540p515 0 1 15054186175909744 940886635994359 4503599627370496 3549822471 4503599627370496 (@Ns540p516 44252367362884362043392 659411659283703 4503599627370496 3549822471 4503599627370496 (@Ns540p517 932576775 4503599627370496 (Ns540p500 rfl rfl) (Ns540p500 rfl rfl) rfl) (Ns540p500 rfl rfl) rfl rfl) qz389 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 22023041 16777216) (BSN.cos_neg_of_bound 22023041 16777216 Bool.false 8565240 33554432 1 9610000 (Ns540p523 rfl rfl)) rfl rfl) 

noncomputable def Ns540p525 := @Ns540p486 217218814820323887552029 Ns540p397 (Ns540p487 qz32 (@Enclosure.Real.IsNear.of_eq qz62 (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 19230433 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz70 (BSN.t_div_two_pi_nonneg qz61 931844 1000 qz64)) Ns540p491) rfl) (@Ns540p492 17592186044416 22549994383717037 1352487263094702080000 (BSN.correction_mk qz63 (BSN.cos_two_pi_p_ne_zero_mk qz61 931844 1000 12 qz64 rfl rfl (@BSN.floor_sqrt_eq_dec qz61 931844 1000 12 qz64 rfl rfl rfl))) (@Ns540p493 33554432 1070655 4194304 204202429 40307261440000 10294627265955 17592186044416 22549994383717037 1352487263094702080000 (@Ns540p494 33554432 (Ns540p508 rfl rfl rfl rfl rfl) rfl) (Ns540p524 rfl) rfl)) 

noncomputable def Ns540p526 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz61) (hardyZApproximantRS₀ qz61) Bool.true 54955096768538535491 1180591620717411303424 Ns540p396 Ns540p397 (@Eq.refl Real (hardyZApproximantRS₀ qz61)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz61) (@HSub.hSub Real Real Real qz33 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz62) (Zeta.RiemannSiegel.correction qz63))) Bool.true 54955096768538535491 1180591620717411303424 Ns540p396 Ns540p397 (BSN.hardyZApproximantRS₀_eq qz61 12 (@BSN.floor_sqrt_eq_dec qz61 931844 1000 12 qz64 rfl rfl rfl)) (@Ns540p399 54955096768538535491 1180591620717411303424 Ns540p396 Ns540p397 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 12)) Bool.false 1016183 8388608 66979 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz61) qz61 12) (Ns540p485 (Ns540p484 rfl rfl rfl rfl) rfl rfl)) (Ns540p525 rfl) rfl rfl)) 

theorem RS541to552.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz61) Bool.true 54955096768538535491 1180591620717411303424 Ns540p396 Ns540p397 := Ns540p526 

noncomputable def Ns540p527 := nat_lit 709092842193395164119040000 

noncomputable def Ns540p528 := nat_lit 400610449788807907847669022720 

noncomputable abbrev qz734 := (Enclosure.sfrac Bool.false 933729 1000)

noncomputable abbrev qz617 := qz734

noncomputable abbrev qz419 := qz617

noncomputable abbrev qz79 := qz419

noncomputable abbrev qz735 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 933729 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz618 := qz735

noncomputable abbrev qz420 := qz618

noncomputable abbrev qz80 := (@HPow.hPow Real Real Real qz356 qz420 qz358)

noncomputable abbrev qz736 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 933729 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz619 := qz736

noncomputable abbrev qz421 := qz619

noncomputable abbrev qz81 := qz421

noncomputable def Ns540p529 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz79) qz79 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz80) (Zeta.RiemannSiegel.correction qz81)) 700519055 134217728 268459 268435456 96134941683201389855 590295810358705651712 4078130149870075903851 Ns540p527 Ns540p528 

noncomputable def Ns540p530 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz79) qz79 Real.cos BSN.quadSignPos 11 12 933729 1000 288 536870912 268435456 9007199254740992 Bool.false 1002701204315 4446 1334074092 57 154981288 8 

noncomputable def Ns540p531 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz79) qz79 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 933729 1000 179 236 536870912 268435456 9007199254740992 Bool.false 1002701204315 4446 

noncomputable def Ns540p532 := Ns540p531 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.false 960153560 216158 Bool.true 612781520 Bool.true 322060403 28296951008113761 1 Bool.false 488131063 Bool.false Bool.false 443133770 Bool.false Bool.false 1248124015 

noncomputable def Ns540p533 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz79) qz79 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 933729 1000 47 117 536870912 268435456 9007199254740992 Bool.false 1002701204315 4446 

noncomputable def Ns540p534 := Ns540p533 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.false 962575439 176527 Bool.true 70280667 Bool.true 81914270 28296951008113761 1 Bool.false 70080106 Bool.false Bool.false 81596815 Bool.true Bool.false 960153560 

noncomputable def Ns540p535 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz79) qz79 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 933729 1000 123 32 536870912 268435456 9007199254740992 Bool.false 1002701204315 4446 

noncomputable def Ns540p536 := Ns540p535 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.false 562999832 131167 Bool.false 778903836 Bool.false 246070000 28296951008113761 1 Bool.false 533011692 Bool.false Bool.false 481459248 Bool.false Bool.false 962575439 

noncomputable def Ns540p537 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz79) qz79 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 933729 1000 364 232 536870912 268435456 9007199254740992 Bool.false 1002701204315 4446 

noncomputable def Ns540p538 := Ns540p537 744261104 56 268435448 8 864060384 56 240095976 8 Bool.false 325843299 77407 Bool.false 796420160 Bool.false 253919307 28296951008113761 1 Bool.false 46835087 Bool.false Bool.false 477934902 Bool.false Bool.false 562999832 

noncomputable def Ns540p539 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz79) qz79 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 933729 1000 776 535 536870912 268435456 9007199254740992 Bool.false 1002701204315 4446 

noncomputable def Ns540p540 := Ns540p539 372130544 56 379625064 8 589812976 56 309962568 8 Bool.false 160104 4512 Bool.false 819794927 Bool.false 802275802 28296951008113761 1 Bool.false 23512406 Bool.false Bool.false 535303138 Bool.false Bool.false 325843299 

noncomputable def Ns540p541 := nat_lit 22297023236562628171532850765399046994570369156886895686871 

noncomputable def Ns540p542 := nat_lit 11938375209268107112638364292897503524314420623704064000 

noncomputable def Ns540p543 := nat_lit 15745024000000000000000000 

noncomputable def Ns540p544 := nat_lit 340679334418993358510177116631520000 

noncomputable def Ns540p545 := nat_lit 1908613300887881863121458512397011228480 

noncomputable abbrev qz620 := (@Eq.refl Real qz734)

noncomputable abbrev qz422 := qz620

noncomputable abbrev qz82 := qz422

noncomputable def Ns540p546 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz79 933729 1000 3487400381764 16000000 1867458 4000 2000 Ns540p544 Ns540p545 qz82 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns540p547 := nat_lit 64215426921300369134014610204349255344362663171834259578188480 

noncomputable abbrev qz621 := (@HSub.hSub Real Real Real qz721 qz722 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz723 (@Nat.cast Real Real.instNatCast 1867458))))

noncomputable abbrev qz423 := (@HSub.hSub Real Real Real qz582 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 933729 4000) (Real.log (Enclosure.sfrac Bool.false 3487400381764 16000000))) (@HMul.hMul Real Real Real qz579 qz583 qz621))

noncomputable abbrev qz622 := (Enclosure.sfrac Bool.false 933729 2000)

noncomputable abbrev qz83 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz423 qz622) (@HMul.hMul Real Real Real qz355 qz622 (Real.log Real.pi)))

noncomputable def Ns540p548 := @Enclosure.Real.IsNear.addLit_ft_p qz83 (Enclosure.sfrac Bool.true Ns540p544 Ns540p545) 33645072592002169095751 18014398509481984000 130368098117446798983 Ns540p543 Ns540p544 Ns540p545 0 1 Ns540p547 

noncomputable def Ns540p549 := nat_lit 451576520169360210710351367372800 

noncomputable abbrev qz84 := (@HSub.hSub Real Real Real qz361 qz423 qz622)

noncomputable def Ns540p550 := @Enclosure.Real.IsNear.subLit_ff_p qz84 (@HMul.hMul Real Real Real qz5 qz622 (Real.log Real.pi)) 8654515007453699070683 3602879701896396800 11771627754811173 3844000000000000000000 35865241457769 67108864000 2801187 536870912000 Ns540p549 33645072592002169095751 18014398509481984000 

noncomputable def Ns540p551 := nat_lit 86545150074536990706830000 

noncomputable abbrev qz85 := qz423

noncomputable def Ns540p552 := @Enclosure.Real.IsNear.subLit_ff_p qz85 qz622 51682858190198547072583 18014398509481984000 11771627754811173 3844000000000000000000 933729 2000 0 1 Ns540p551 8654515007453699070683 3602879701896396800 11771627754811173 3844000000000000000000 

noncomputable def Ns540p553 := nat_lit 116379450443410181940031270811372355584 

noncomputable def Ns540p554 := nat_lit 118881687809432534223159296 

noncomputable def Ns540p555 := nat_lit 124344984470616690697920512130486428633669861338559049665391531098928938067746905040004166019257211699969693738798164082445643839213216787861491898576231464960 

noncomputable def Ns540p556 := nat_lit 2668668488806641216351632202088398832466018896010953237797846986840361007387453499985060957487491083973356822257754115106542243332663285267924965343008653312 

noncomputable def Ns540p557 := nat_lit 541917620644927862697377568736989021171517238499498864814721710301042232077824068264395996666038758232098827854259326379531037468553509862551500881920 

noncomputable def Ns540p558 := BSN.log_dyadic_bound 1390248381764 5584552381764 7 6 Ns540p555 268435456 76880000 Ns540p556 Ns540p557 136519924 6974800763528 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1390248381764) (BSN.artanhQ 5584552381764) 0 6 Ns540p556 Ns540p555 Ns540p557 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz424 := (Real.log (Enclosure.sfrac Bool.false 3487400381764 16000000))

noncomputable def Ns540p559 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 933729 4000) qz424 933729 4000 0 1 55358599782657127 4503599627370496 12500016337 961000000000000000 51689930016460656536583 18014398509481984000 11671627754330673 3844000000000000000000 (Enclosure.Real.IsNear.const Bool.false 933729 4000) (BSN.isNear_log_sfrac 3487400381764 16000000 55358599782657127 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3487400381764) qz364)) Bool.false Ns540p554 Ns540p114 1000001306960000 76880000000000000000000 55358599782657127 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3487400381764 16000000 17 6974800763528 4194304000000 136519924 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns540p558 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p560 := BSN.arctan_dyadic_bound_f 1000 1867458 1 0 33554432 9610000 0 1 1 0 1 1 17967 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1867458) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1867458) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns540p561 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1867458))) 884279719003555 562949953421312 1 2000000000000000 17967 33554432 1 9610000 29661389178470773293056 883978282763683 562949953421312 200000000961 1922000000000000000 qz15 (Ns540p560 rfl) rfl rfl 

noncomputable abbrev qz425 := (@HMul.hMul Real Real Real qz579 qz583 qz621)

noncomputable abbrev qz86 := qz425

noncomputable abbrev qz426 := qz621

noncomputable abbrev qz87 := qz426

noncomputable def Ns540p562 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 933729 4000) qz424) qz86 51689930016460656536583 18014398509481984000 11671627754330673 3844000000000000000000 883978282763683 2251799813685248 200000000961 7688000000000000000 Ns540p553 51682858190198547072583 18014398509481984000 11771627754811173 3844000000000000000000 (Ns540p559 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz87 1 4 0 1 883978282763683 562949953421312 200000000961 1922000000000000000 883978282763683 2251799813685248 200000000961 7688000000000000000 qz372 Ns540p561 rfl) 

noncomputable def Ns540p563 := @Ns540p548 Ns540p541 Ns540p542 130368098117446798983 Ns540p543 (@Ns540p550 130368098117446798983 Ns540p543 (Ns540p552 (Ns540p562 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 933729 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz622 (Real.log Real.pi) 933729 2000 0 1 38410761 33554432 3 268435456 35865241457769 67108864000 2801187 536870912000 (Enclosure.Real.IsNear.const Bool.false 933729 2000) RS541to552.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns540p544 Ns540p545) 

noncomputable def Ns540p564 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz79) Bool.false Ns540p541 Ns540p542 130368098117446798983 Ns540p543 125337650539 67108864 557 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz79) (@HAdd.hAdd Real Real Real qz373 qz83 (Enclosure.sfrac Bool.true Ns540p544 Ns540p545)) Bool.false Ns540p541 Ns540p542 130368098117446798983 Ns540p543 Ns540p546 (Ns540p563 rfl rfl)) 

noncomputable def Ns540p565 := nat_lit 15188925694002875699560448 

noncomputable def Ns540p566 := nat_lit 5535591731032468534434450997135769218919710556699498194494166549564908108893564786021457454987511239320483664783267186238820186409331476467441 

noncomputable def Ns540p567 := nat_lit 21759806992472160846509436431027924547665573599712653161483140986990306751823661669370177199848368120331884066839754328502985489716814125465600 

noncomputable def Ns540p568 := nat_lit 10227443368087306570257253671772212132104983737412748887741427091904453882467544288776118240857619719419500582411351462826575098557304561 

noncomputable def Ns540p569 := nat_lit 33501760084231759553671186463119007680419851560337397447834863865143613832859851121198659075520505183847717961644921325942377889007801861738225 

noncomputable def Ns540p570 := nat_lit 1980142436314966637032358715223541133837567197573851437694965829816117914415953211912686125186201498950201450082417643893771679564230085417369600 

noncomputable def Ns540p571 := BSN.cos_dyadic_bound_f 215847616317 137438953472 4 3 67108864 19238770 Ns540p566 Ns540p567 Ns540p568 Ns540p569 Ns540p570 Ns540p568 20013 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 215847616317) qz589 0 3 Ns540p566 Ns540p567 Ns540p568 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 215847616317) qz590 0 3 Ns540p569 Ns540p570 Ns540p568 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p572 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz79) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 125337650539) qz374) Bool.false 125337650539 67108864 557 67108864 Bool.false 20013 67108864 1 9610000 (Ns540p564 rfl) (Enclosure.sfrac_false_div 125337650539 67108864) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 125337650539) qz374) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns540p565) qz375) 226375608064910080 72057594037927936 Bool.false 20013 67108864 297 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q0 125337650539 67108864 226375608064910080 72057594037927936 297 Ns540p565 Ns540p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 20013 67108864 Ns540p565 Ns540p114 215847616317 137438953472 19238770 19220000 (Ns540p571 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns540p573 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz79) Bool.false Ns540p541 Ns540p542 130368098117446798983 Ns540p543 1002701204315 536870912 4446 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz79) (@HAdd.hAdd Real Real Real qz373 qz83 (Enclosure.sfrac Bool.true Ns540p544 Ns540p545)) Bool.false Ns540p541 Ns540p542 130368098117446798983 Ns540p543 Ns540p546 (Ns540p563 rfl rfl)) 

noncomputable def Ns540p574 := Ns540p540 77407 BSN.abs_quadSignPos (BSN.cos_quad_nat0 776 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 23512406 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 535 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 535303138 536870912) qz82 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz79) qz79 1) Bool.false 20013 67108864 338742429 40307261440000 160104 536870912 4512 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz79) qz79 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz79)) Bool.false 20013 67108864 338742429 40307261440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz79) qz79) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz79)) Bool.false 20013 67108864 5419878864 644916183040000 20013 67108864 338742429 40307261440000 (Ns540p572 rfl rfl) rfl)) rfl) (Ns540p573 rfl) RS541to552.d7 

noncomputable def Ns540p575 := nat_lit 62417942343814039593531955925736512251425581242002370170818750276382954438666984099667435295450789223953601336001 

noncomputable def Ns540p576 := nat_lit 92143078556257110289888414980306184726835689277606114119527562650588526091626682721483332751645792036131521 

noncomputable def Ns540p577 := nat_lit 377854060505829175163238300422064682830880358698606954259530678150913045428278234219954316624416744128020499600065 

noncomputable def Ns540p578 := BSN.cos_dyadic_bound_f 819794927 536870912 4 3 536870912 268435456 Ns540p575 Ns540p153 Ns540p576 Ns540p577 Ns540p156 Ns540p576 23512406 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 819794927) qz19 0 3 Ns540p575 Ns540p153 Ns540p576 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 819794927) qz378 0 3 Ns540p577 Ns540p156 Ns540p576 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p579 := nat_lit 148617047258343218450421259961170762425506371586428265698687777675262361178011397786428159716052551920767039901696 

noncomputable def Ns540p580 := nat_lit 71102409804103289364239929090167374808114397270155889106284309384119458075362205592075912555392109423824896 

noncomputable def Ns540p581 := nat_lit 742328689394046375563036440020344639161030894037028659419302833941953483093042490100382236736331252742403026784256 

noncomputable def Ns540p582 := BSN.sin_dyadic_bound_f 802275802 536870912 4 3 536870912 268435456 Ns540p579 Ns540p130 Ns540p580 Ns540p581 Ns540p133 Ns540p580 535303138 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 802275802) qz376 0 3 Ns540p579 Ns540p130 Ns540p580 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 802275802) qz377 0 3 Ns540p581 Ns540p133 Ns540p580 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p583 := nat_lit 55578175939860680257170142319797504884839729358876846462595828525484209751821918402881944666268173131055104000000 

noncomputable def Ns540p584 := nat_lit 65118882478059088454370141579085479667115066952378119019580719063474160008878743704042949574656000000000000 

noncomputable def Ns540p585 := nat_lit 336527847801845316526849256563486801717730773796241989194346077814385802137675428374798921398372693261785497600000 

noncomputable def Ns540p586 := BSN.cos_dyadic_bound_f 796420160 536870912 4 3 536870912 268435456 Ns540p583 Ns540p153 Ns540p584 Ns540p585 Ns540p156 Ns540p584 46835087 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 796420160) qz19 0 3 Ns540p583 Ns540p153 Ns540p584 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 796420160) qz378 0 3 Ns540p585 Ns540p156 Ns540p584 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p587 := nat_lit 580209199446924524734076496127120363044637007333839856693248534415024481 

noncomputable def Ns540p588 := nat_lit 17280877557324060952434404169325485168372634025813806002245654684001 

noncomputable def Ns540p589 := nat_lit 1740593036585658926080324619573022438163574276733467942467741111935705441 

noncomputable def Ns540p590 := BSN.cos_dyadic_bound_f 253919307 536870912 3 2 536870912 268435456 Ns540p587 Ns540p160 Ns540p588 Ns540p589 Ns540p163 Ns540p588 477934902 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 253919307) qz19 0 2 Ns540p587 Ns540p160 Ns540p588 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 253919307) qz378 0 2 Ns540p589 Ns540p163 Ns540p588 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p591 := Ns540p538 131167 BSN.abs_quadSignPos (BSN.cos_quad_nat0 364 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 46835087 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 232 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 477934902 536870912) qz82 rfl rfl (Ns540p574 RS541to552.d9 RS541to552.d11 RS541to552.d13 RS541to552.d17 (Ns540p578 rfl rfl) (Ns540p582 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns540p573 rfl) RS541to552.d19 RS541to552.d21 RS541to552.d23 RS541to552.d25 RS541to552.d17 (Ns540p586 rfl rfl) (Ns540p590 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns540p592 := nat_lit 132016868947910045404761106502664643860885278727726127286672505195605789407679116794423399122388940549955619127296 

noncomputable def Ns540p593 := nat_lit 49866181367551119248959107864799465006242387396003071389089799873198124741981793184799129586849918794858496 

noncomputable def Ns540p594 := nat_lit 659487173560467828970454172815797977576945227410524849936045321198944668384071429318990134091895886172595584761856 

noncomputable def Ns540p595 := BSN.sin_dyadic_bound_f 778903836 536870912 4 3 536870912 268435456 Ns540p592 Ns540p130 Ns540p593 Ns540p594 Ns540p133 Ns540p593 533011692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 778903836) qz376 0 3 Ns540p592 Ns540p130 Ns540p593 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 778903836) qz377 0 3 Ns540p594 Ns540p133 Ns540p593 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p596 := nat_lit 511722913828605405433413260391697453704731724461051084800000000000000000 

noncomputable def Ns540p597 := nat_lit 13442169087479732008408540291854720100000000000000000000000000000000 

noncomputable def Ns540p598 := nat_lit 1535141857147641256836222964094508651673995173383153254400000000000000000 

noncomputable def Ns540p599 := BSN.cos_dyadic_bound_f 246070000 536870912 3 2 536870912 268435456 Ns540p596 Ns540p160 Ns540p597 Ns540p598 Ns540p163 Ns540p597 481459248 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 246070000) qz19 0 2 Ns540p596 Ns540p160 Ns540p597 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 246070000) qz378 0 2 Ns540p598 Ns540p163 Ns540p597 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p600 := Ns540p536 176527 BSN.abs_quadSignPos (BSN.cos_quad_nat3 123 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 533011692 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 481459248 536870912) qz82 rfl rfl (Ns540p591 rfl rfl) (Ns540p573 rfl) RS541to552.d27 RS541to552.d29 RS541to552.d31 RS541to552.d33 RS541to552.d17 (Ns540p595 rfl rfl) (Ns540p599 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p601 := nat_lit 24397397275363747124603044782321 

noncomputable def Ns540p602 := BSN.sin_dyadic_bound_f 70280667 536870912 2 1 536870912 268435456 Ns540p601 Ns540p282 Ns540p601 Ns540p601 Ns540p283 Ns540p601 70080106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 70280667) qz376 0 1 Ns540p601 Ns540p282 Ns540p601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 70280667) qz377 0 1 Ns540p601 Ns540p283 Ns540p601 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p603 := nat_lit 45023397192416173350188762410000 

noncomputable def Ns540p604 := BSN.sin_dyadic_bound_f 81914270 536870912 2 1 536870912 268435456 Ns540p603 Ns540p282 Ns540p603 Ns540p603 Ns540p283 Ns540p603 81596815 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 81914270) qz376 0 1 Ns540p603 Ns540p282 Ns540p603 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 81914270) qz377 0 1 Ns540p603 Ns540p283 Ns540p603 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p605 := Ns540p534 216158 BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 70080106 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 81596815 536870912) qz82 rfl rfl (Ns540p600 rfl) (Ns540p573 rfl) RS541to552.d35 RS541to552.d37 RS541to552.d39 RS541to552.d41 RS541to552.d17 (Ns540p602 rfl rfl) (Ns540p604 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p606 := nat_lit 35442765741796281383485597017592720088437948162039991528681931790090240000 

noncomputable def Ns540p607 := nat_lit 19881322787761305741130545394106109624033767208457242479794585600000000 

noncomputable def Ns540p608 := nat_lit 92794102420191028176024257020199999863660476229862475611104439644979200000 

noncomputable def Ns540p609 := BSN.sin_dyadic_bound_f 612781520 536870912 3 2 536870912 268435456 Ns540p606 Ns540p276 Ns540p607 Ns540p608 Ns540p279 Ns540p607 488131063 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 612781520) qz376 0 2 Ns540p606 Ns540p276 Ns540p607 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 612781520) qz377 0 2 Ns540p608 Ns540p279 Ns540p607 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p610 := nat_lit 1501659896046939242658739755138229605080894450327341159169193006987639841 

noncomputable def Ns540p611 := nat_lit 115744045094688995777888757841686281938050695608251523000965522684961 

noncomputable def Ns540p612 := nat_lit 4504748200050628349984663487899005442678807249590806974461577089917549601 

noncomputable def Ns540p613 := BSN.cos_dyadic_bound_f 322060403 536870912 3 2 536870912 268435456 Ns540p610 Ns540p160 Ns540p611 Ns540p612 Ns540p163 Ns540p611 443133770 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 322060403) qz19 0 2 Ns540p610 Ns540p160 Ns540p611 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 322060403) qz378 0 2 Ns540p612 Ns540p163 Ns540p611 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p614 := Ns540p532 251801 BSN.abs_quadSignPos qz613 (BSN.sfrac_eq_quadSignPos_mul Bool.false 488131063 536870912) BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 443133770 536870912) qz82 rfl rfl (Ns540p605 rfl) (Ns540p573 rfl) RS541to552.d43 RS541to552.d45 RS541to552.d47 RS541to552.d49 RS541to552.d17 (Ns540p609 rfl rfl) (Ns540p613 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p615 := nat_lit 59385213901567960651592036905216 

noncomputable def Ns540p616 := BSN.cos_dyadic_bound_f 87784852 536870912 2 1 536870912 268435456 Ns540p615 Ns540p136 Ns540p615 Ns540p615 Ns540p137 Ns540p615 529709948 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 87784852) qz19 0 1 Ns540p615 Ns540p136 Ns540p615 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 87784852) qz378 0 1 Ns540p615 Ns540p137 Ns540p615 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p617 := Ns540p530 Bool.false 1248124015 251801 Bool.true 87784852 28296951008113761 1 Bool.false 529709948 Bool.false Bool.false 1401038110 268459 BSN.abs_quadSignPos qz380 (BSN.sfrac_eq_quadSignPos_mul Bool.false 529709948 536870912) qz82 rfl (Ns540p614 rfl) (Ns540p573 rfl) RS541to552.d51 RS541to552.d53 RS541to552.d17 (Ns540p616 rfl rfl) rfl 

noncomputable def Ns540p618 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz79) qz79 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz79) qz79 12) 1401038110 536870912 268459 536870912 1401038110 536870912 268459 536870912 1504353215724912640 700519055 134217728 268459 268435456 (Ns540p617 rfl rfl rfl rfl) 

noncomputable def Ns540p619 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz80) (Zeta.RiemannSiegel.correction qz81) 1201295 4194304 1 33554432 80026089913969 140737488355328 1692387510648739 84530453943418880000 96134941683201389855 590295810358705651712 

noncomputable def Ns540p620 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz80 1 1 0 1 1201295 4194304 1 33554432 1201295 4194304 1 33554432 

noncomputable abbrev qz88 := qz420

noncomputable def Ns540p621 := @Enclosure.Real.IsNear.sqrt_image qz88 9972885866403 67108864000 933729 67108864000 409044306 409044345 33554432 (@Enclosure.Real.IsNear.of_eq qz88 (@HMul.hMul Real Real Real qz5 qz79 qz3) Bool.false 9972885866403 67108864000 933729 67108864000 (BSN.t_div_two_pi_mk qz79 933729 1000 qz82) (@Enclosure.Real.IsNear.mulLit_ff qz79 qz3 933729 1000 0 1 10680707 67108864 1 67108864 9972885866403 67108864000 933729 67108864000 (Enclosure.Real.IsNear.const Bool.false 933729 1000) RS541to552.d56 rfl)) 

noncomputable abbrev qz737 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 933729 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz623 := qz737

noncomputable abbrev qz427 := qz623

noncomputable abbrev qz89 := qz427

noncomputable def Ns540p622 := @Enclosure.Real.IsNear.sqrt_image qz89 818088651 67108864 39 67108864 117154809 117154815 33554432 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 818088651 67108864 39 67108864 818088651 67108864 39 67108864 (Ns540p621 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns540p623 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz89) 29288703 8388608 3 33554432 9610359 9610361 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz89) Bool.false 234309624 67108864 6 67108864 29288703 8388608 3 33554432 (Ns540p622 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns540p624 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 19220720 67108864 2 67108864 1201295 4194304 1 33554432 (Ns540p623 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz90 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz421))

noncomputable abbrev qz624 := (@HMul.hMul Real Real Real qz717 qz736 qz736)

noncomputable abbrev qz428 := (@HSub.hSub Real Real Real qz582 (@HSub.hSub Real Real Real qz582 qz624 qz619) qz594)

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz428))

noncomputable def Ns540p625 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz81) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz90) qz91) Bool.false 80026089913969 

noncomputable def Ns540p626 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz90) qz91 22959077 8388608 237 

noncomputable def Ns540p627 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz90) Bool.false 183672616 67108864 1896 67108864 22959077 8388608 237 

noncomputable def Ns540p628 := @Enclosure.Real.IsNear.recentre' qz90 Bool.false 12259856 33554432 1215584432 322458091520000 766241 2097152 75974027 20153630720000 

noncomputable abbrev qz92 := (@HMul.hMul Real Real Real qz355 qz352 qz421)

noncomputable def Ns540p629 := @Enclosure.Real.IsNear.cos_image qz92 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20078363) qz616) Bool.false 20078363 16777216 123 33554432 Bool.false 12259856 33554432 1 

noncomputable def Ns540p630 := nat_lit 1052456941062516747658023249 

noncomputable def Ns540p631 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz81 884279719003555 140737488355328 1 500000000000000 12782283 67108864 39 67108864 11303113619463918016065 9444732965739290427392 Ns540p630 

noncomputable def Ns540p632 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz1 818088651 67108864 39 67108864 12 1 0 1 12782283 12782283 67108864 39 

noncomputable def Ns540p633 := @Ns540p632 67108864 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 818088651 67108864 39 67108864 818088651 67108864 39 67108864 (Ns540p621 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns540p634 := @Enclosure.Real.IsNear.recentre' qz92 Bool.false 11303113619463918016065 9444732965739290427392 Ns540p630 Ns540p333 20078363 16777216 123 33554432 (@Ns540p631 Ns540p333 RS541to552.d55 (Ns540p633 rfl rfl) rfl) 

noncomputable def Ns540p635 := nat_lit 21658682391424554093753827630580140610116670033068339078373601 

noncomputable def Ns540p636 := nat_lit 253092741970790968397859029543733109897246971520789871559966720 

noncomputable def Ns540p637 := nat_lit 26413528017710213537618963675519016363847086384979978756321 

noncomputable def Ns540p638 := nat_lit 64923220118238241854186244964389383797622315926435057277608161 

noncomputable def Ns540p639 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400 

noncomputable def Ns540p640 := BSN.cos_dyadic_bound_f 20078363 16777216 3 2 33554432 9610000 Ns540p635 Ns540p636 Ns540p637 Ns540p638 Ns540p639 Ns540p637 12259856 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 20078363) (BSN.cosEvenQ 16777216) 0 2 Ns540p635 Ns540p636 Ns540p637 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 20078363) (BSN.cosOddQ 16777216) 0 2 Ns540p638 Ns540p639 Ns540p637 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p641 := @Enclosure.Real.IsNear.inv_image qz90 766241 2097152 75974027 20153630720000 91835360 91837256 33554432 (Ns540p628 (@Ns540p629 9610000 (Ns540p634 rfl) (Enclosure.sfrac_false_div 20078363 16777216) (Ns540p640 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns540p642 := @Enclosure.Real.IsNear.recentre' qz91 Bool.false 6971194 33554432 

noncomputable abbrev qz93 := (@HMul.hMul Real Real Real qz355 qz352 qz428)

noncomputable def Ns540p643 := @Enclosure.Real.IsNear.cos_image qz93 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 91369669)) qz374) Bool.true 91369669 67108864 

noncomputable def Ns540p644 := nat_lit 862962130912240794204984905845 

noncomputable def Ns540p645 := nat_lit 19506967139919875104408816246491433 

noncomputable def Ns540p646 := @Enclosure.Real.IsNear.recentre' qz93 Bool.true Ns540p644 Ns540p210 Ns540p645 

noncomputable abbrev qz94 := qz428

noncomputable def Ns540p647 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz94 884279719003555 140737488355328 1 500000000000000 975892709475079 

noncomputable abbrev qz429 := (@HSub.hSub Real Real Real qz582 qz624 qz619)

noncomputable abbrev qz95 := qz429

noncomputable def Ns540p648 := @Enclosure.Real.IsNear.subLit_tf qz95 qz30 694417732764423 4503599627370496 3614265291 4503599627370496 1 16 

noncomputable abbrev qz430 := qz624

noncomputable abbrev qz96 := qz430

noncomputable def Ns540p649 := @Enclosure.Real.IsNear.subLit_ff_n qz96 qz81 163386758692089 4503599627370496 997019595 4503599627370496 12782283 67108864 39 67108864 

noncomputable def Ns540p650 := @Enclosure.Real.IsNear.mulLit_ff qz81 qz81 12782283 67108864 39 67108864 12782283 67108864 39 67108864 163386758692089 4503599627370496 

noncomputable def Ns540p651 := nat_lit 573403955319735028479315036398247047447025655622775056710013487386042042506003987860220654563813257041 

noncomputable def Ns540p652 := nat_lit 338551404187112027506971746614435483397140285044205808949312810813906123869225555512376690241361 

noncomputable def Ns540p653 := nat_lit 3473915131996115454590425978372461973947523319434433395671607202700692770106896527082572451128651837265 

noncomputable def Ns540p654 := BSN.cos_dyadic_bound_f 91369669 67108864 4 3 33554432 9610000 Ns540p651 Ns540p219 Ns540p652 Ns540p653 Ns540p222 Ns540p652 6971194 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 91369669) qz596 0 3 Ns540p651 Ns540p219 Ns540p652 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 91369669) (BSN.cosOddQ 67108864) 0 3 Ns540p653 Ns540p222 Ns540p652 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p655 := @Ns540p642 833627216 161229045760000 3485597 16777216 52101701 10076815360000 (@Ns540p643 85 16777216 Bool.false 6971194 33554432 1 9610000 (@Ns540p646 Ns540p348 91369669 67108864 85 16777216 (@Ns540p647 4503599627370496 3614265291 4503599627370496 Ns540p644 Ns540p210 Ns540p645 Ns540p348 RS541to552.d55 (@Ns540p648 0 1 15614283351601264 975892709475079 4503599627370496 3614265291 4503599627370496 (@Ns540p649 46601585187276007145472 694417732764423 4503599627370496 3614265291 4503599627370496 (@Ns540p650 997019595 4503599627370496 (Ns540p633 rfl rfl) (Ns540p633 rfl rfl) rfl) (Ns540p633 rfl rfl) rfl rfl) qz389 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 91369669 67108864) (BSN.cos_neg_of_bound 91369669 67108864 Bool.false 6971194 33554432 1 9610000 (Ns540p654 rfl rfl)) rfl rfl) 

noncomputable def Ns540p656 := @Ns540p619 4078130149870075903851 Ns540p527 (Ns540p620 qz32 (@Enclosure.Real.IsNear.of_eq qz80 (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 1201295 4194304 1 33554432 (BSN.rpow_neg_quarter_mk qz88 (BSN.t_div_two_pi_nonneg qz79 933729 1000 qz82)) Ns540p624) rfl) (@Ns540p625 140737488355328 1692387510648739 84530453943418880000 (BSN.correction_mk qz81 (BSN.cos_two_pi_p_ne_zero_mk qz79 933729 1000 12 qz82 rfl rfl (@BSN.floor_sqrt_eq_dec qz79 933729 1000 12 qz82 rfl rfl rfl))) (@Ns540p626 8388608 3485597 16777216 52101701 10076815360000 80026089913969 140737488355328 1692387510648739 84530453943418880000 (@Ns540p627 8388608 (Ns540p641 rfl rfl rfl rfl rfl) rfl) (Ns540p655 rfl) rfl)) 

noncomputable def Ns540p657 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz79) (hardyZApproximantRS₀ qz79) Bool.false 2984780444121419696865 590295810358705651712 713233165624754110463851 Ns540p527 (@Eq.refl Real (hardyZApproximantRS₀ qz79)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz79) (@HSub.hSub Real Real Real qz33 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz79) qz79 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz80) (Zeta.RiemannSiegel.correction qz81))) Bool.false 2984780444121419696865 590295810358705651712 713233165624754110463851 Ns540p527 (BSN.hardyZApproximantRS₀_eq qz79 12 (@BSN.floor_sqrt_eq_dec qz79 933729 1000 12 qz82 rfl rfl rfl)) (@Ns540p529 2984780444121419696865 590295810358705651712 713233165624754110463851 Ns540p527 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz79) qz79 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz79) qz79 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz79) qz79 12)) Bool.false 700519055 134217728 268459 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz79) qz79 12) (Ns540p618 (Ns540p617 rfl rfl rfl rfl) rfl rfl)) (Ns540p656 rfl) rfl rfl)) 

theorem RS541to552.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz79) Bool.false 2984780444121419696865 590295810358705651712 713233165624754110463851 Ns540p527 := Ns540p657 

noncomputable def Ns540p658 := nat_lit 4572730372582571187042723 

noncomputable def Ns540p659 := nat_lit 4538194190037729050361856000 

noncomputable def Ns540p660 := nat_lit 1308717755099250937544310784 

noncomputable abbrev qz738 := (Enclosure.sfrac Bool.false 934750 1000)

noncomputable abbrev qz625 := qz738

noncomputable abbrev qz431 := qz625

noncomputable abbrev qz97 := qz431

noncomputable abbrev qz739 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 934750 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz626 := qz739

noncomputable abbrev qz432 := qz626

noncomputable abbrev qz98 := (@HPow.hPow Real Real Real qz356 qz432 qz358)

noncomputable abbrev qz740 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 934750 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz627 := qz740

noncomputable abbrev qz433 := qz627

noncomputable abbrev qz99 := qz433

noncomputable def Ns540p661 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz97) qz97 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz98) (Zeta.RiemannSiegel.correction qz99)) 12356053 33554432 268749 268435456 11831580558135701181 73786976294838206464 29235379214595070818723 Ns540p659 Ns540p660 

noncomputable def Ns540p662 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz97) qz97 Real.cos BSN.quadSignPos 11 12 934750 1000 288 536870912 268435456 9007199254740992 Bool.false 1004072075595 4451 1334074092 57 154981288 8 

noncomputable def Ns540p663 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz97) qz97 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 934750 1000 179 236 536870912 268435456 9007199254740992 Bool.false 1004072075595 4451 

noncomputable def Ns540p664 := Ns540p663 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 531611975 216390 Bool.true 504061206 Bool.true 265583908 28296951008113761 1 Bool.false 433201815 Bool.false Bool.false 472509003 Bool.false Bool.true 252154709 

noncomputable def Ns540p665 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz97) qz97 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 934750 1000 46 116 536870912 268435456 9007199254740992 Bool.false 1004072075595 4451 

noncomputable def Ns540p666 := Ns540p665 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 503692001 176715 Bool.true 682560145 Bool.true 758755940 28296951008113761 1 Bool.false 158363307 Bool.true Bool.false 84209737 Bool.false Bool.true 531611975 

noncomputable def Ns540p667 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz97) qz97 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 934750 1000 124 32 536870912 268435456 9007199254740992 Bool.false 1004072075595 4451 

noncomputable def Ns540p668 := Ns540p667 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 789411390 131306 Bool.false 324315913 Bool.false 550299986 28296951008113761 1 Bool.false 441856522 Bool.false Bool.false 278682852 Bool.false Bool.true 503692001 

noncomputable def Ns540p669 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz97) qz97 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 934750 1000 365 232 536870912 268435456 9007199254740992 Bool.false 1004072075595 4451 

noncomputable def Ns540p670 := Ns540p669 744261104 56 268435448 8 864060384 56 240095976 8 Bool.true 601255824 77487 Bool.false 564085996 Bool.false 742584935 28296951008113761 1 Bool.false 465879053 Bool.true Bool.false 100139964 Bool.false Bool.true 789411390 

noncomputable def Ns540p671 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz97) qz97 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 934750 1000 778 536 536870912 268435456 9007199254740992 Bool.false 1004072075595 4451 

noncomputable def Ns540p672 := Ns540p671 372130544 56 379625064 8 589812976 56 309962568 8 Bool.true 297999600 4512 Bool.false 124091208 Bool.false 727633177 28296951008113761 1 Bool.false 522593555 Bool.true Bool.false 114788591 Bool.false Bool.true 601255824 

noncomputable def Ns540p673 := nat_lit 16569921441616017197404355619533150378285021 

noncomputable def Ns540p674 := nat_lit 8859830934798151668770757672960000000000 

noncomputable def Ns540p675 := nat_lit 342546016395106554906250000000000000 

noncomputable def Ns540p676 := nat_lit 1921169589472486724853515625000000000000 

noncomputable abbrev qz628 := (@Eq.refl Real qz738)

noncomputable abbrev qz434 := qz628

noncomputable abbrev qz100 := qz434

noncomputable def Ns540p677 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz97 934750 1000 3495031250000 16000000 1869500 4000 2000 Ns540p675 Ns540p676 qz100 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns540p678 := nat_lit 258905022525250268709443056555205474660703453125000000000000 

noncomputable abbrev qz629 := (@HSub.hSub Real Real Real qz721 qz722 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz723 (@Nat.cast Real Real.instNatCast 1869500))))

noncomputable abbrev qz435 := (@HSub.hSub Real Real Real qz582 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 934750 4000) (Real.log (Enclosure.sfrac Bool.false 3495031250000 16000000))) (@HMul.hMul Real Real Real qz579 qz583 qz629))

noncomputable abbrev qz630 := (Enclosure.sfrac Bool.false 934750 2000)

noncomputable abbrev qz101 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz435 qz630) (@HMul.hMul Real Real Real qz355 qz630 (Real.log Real.pi)))

noncomputable def Ns540p679 := @Enclosure.Real.IsNear.addLit_ft_p qz101 (Enclosure.sfrac Bool.true Ns540p675 Ns540p676) 134764285582608044029 72057594037927936 104408162551388153 12596019200000000000000 Ns540p675 Ns540p676 0 1 Ns540p678 

noncomputable def Ns540p680 := nat_lit 36175512452881615968192692224 

noncomputable abbrev qz102 := (@HSub.hSub Real Real Real qz361 qz435 qz630)

noncomputable def Ns540p681 := @Enclosure.Real.IsNear.subLit_ff_p qz102 (@HMul.hMul Real Real Real qz5 qz630 (Real.log Real.pi)) 173316404712302841853 72057594037927936 9427512217193 3075200000000000000 143617835379 268435456 11217 2147483648 Ns540p680 134764285582608044029 72057594037927936 

noncomputable abbrev qz103 := qz435

noncomputable def Ns540p682 := @Enclosure.Real.IsNear.subLit_ff_p qz103 qz630 206994322725779410941 72057594037927936 9427512217193 3075200000000000000 934750 2000 0 1 346632809424605683706000 173316404712302841853 72057594037927936 9427512217193 3075200000000000000 

noncomputable def Ns540p683 := nat_lit 466109777347814173495388843821498368 

noncomputable def Ns540p684 := nat_lit 118902826913449876914176000 

noncomputable def Ns540p685 := nat_lit 126399273605390964524899813160905455139894001399202911898176322516941375556659482955458820029199123382568359375000000000000000000000000000000000000000000000000 

noncomputable def Ns540p686 := nat_lit 2736024080476153093728333842764431673754773287331397832352548681743966508483398889431102740287780761718750000000000000000000000000000000000000000000000000000 

noncomputable def Ns540p687 := nat_lit 578709208936878133705844920586409165778907545653202741796497884587147241125612216925323009490966796875000000000000000000000000000000000000000000000000 

noncomputable def Ns540p688 := BSN.log_dyadic_bound 1397879250000 5592183250000 7 6 Ns540p685 268435456 76880000 Ns540p686 Ns540p687 137106652 6990062500000 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1397879250000) (BSN.artanhQ 5592183250000) 0 6 Ns540p686 Ns540p685 Ns540p687 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz436 := (Real.log (Enclosure.sfrac Bool.false 3495031250000 16000000))

noncomputable def Ns540p689 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 934750 4000) qz436 934750 4000 0 1 55368443445046375 4503599627370496 12500016337 961000000000000000 207022610041028396125 72057594037927936 46737561084043 15376000000000000000 (Enclosure.Real.IsNear.const Bool.false 934750 4000) (BSN.isNear_log_sfrac 3495031250000 16000000 55368443445046375 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3495031250000) qz364)) Bool.false Ns540p684 Ns540p114 1000001306960000 76880000000000000000000 55368443445046375 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3495031250000 16000000 17 6990062500000 4194304000000 137106652 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns540p688 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p690 := BSN.arctan_dyadic_bound_f 1000 1869500 1 0 33554432 9610000 0 1 1 0 1 1 17948 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1869500) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1869500) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns540p691 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1869500))) 884279719003555 562949953421312 1 2000000000000000 17948 33554432 1 9610000 29661399874519888297984 883978601530787 562949953421312 200000000961 1922000000000000000 qz15 (Ns540p690 rfl) rfl rfl 

noncomputable abbrev qz437 := (@HMul.hMul Real Real Real qz579 qz583 qz629)

noncomputable abbrev qz104 := qz437

noncomputable abbrev qz438 := qz629

noncomputable abbrev qz105 := qz438

noncomputable def Ns540p692 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 934750 4000) qz436) qz104 207022610041028396125 72057594037927936 46737561084043 15376000000000000000 883978601530787 2251799813685248 200000000961 7688000000000000000 Ns540p683 206994322725779410941 72057594037927936 9427512217193 3075200000000000000 (Ns540p689 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz105 1 4 0 1 883978601530787 562949953421312 200000000961 1922000000000000000 883978601530787 2251799813685248 200000000961 7688000000000000000 qz372 Ns540p691 rfl) 

noncomputable def Ns540p693 := @Ns540p679 Ns540p673 Ns540p674 104408162551388153 12596019200000000000000 (@Ns540p681 104408162551388153 12596019200000000000000 (Ns540p682 (Ns540p692 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 934750 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz630 (Real.log Real.pi) 934750 2000 0 1 38410761 33554432 3 268435456 143617835379 268435456 11217 2147483648 (Enclosure.Real.IsNear.const Bool.false 934750 2000) RS541to552.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns540p675 Ns540p676) 

noncomputable def Ns540p694 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz97) Bool.false Ns540p673 Ns540p674 104408162551388153 12596019200000000000000 125509009449 67108864 557 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz97) (@HAdd.hAdd Real Real Real qz373 qz101 (Enclosure.sfrac Bool.true Ns540p675 Ns540p676)) Bool.false Ns540p673 Ns540p674 104408162551388153 12596019200000000000000 Ns540p677 (Ns540p693 rfl rfl)) 

noncomputable def Ns540p695 := nat_lit 9500727448035827780681728 

noncomputable def Ns540p696 := nat_lit 199295524724410277677018689789837772369595025917119275129039539804823469204023943325338894336 

noncomputable def Ns540p697 := nat_lit 5133330660362904937396483134791632965849700352038159351603073932373040875403608499582161387520 

noncomputable def Ns540p698 := nat_lit 110412049453539602075702338107417496098913938132741618824071972186923381740029087076909056 

noncomputable def Ns540p699 := nat_lit 597665750074323753826904664693298482116587249875092342149470475470096560848591771801862864896 

noncomputable def Ns540p700 := nat_lit 230999879716330722182841741065623483463236515841717170822138326956786839393162382481197262438400 

noncomputable def Ns540p701 := BSN.cos_dyadic_bound_f 135013457452 137438953472 3 2 67108864 19238770 Ns540p696 Ns540p697 Ns540p698 Ns540p699 Ns540p700 Ns540p698 37249950 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 135013457452) qz589 0 2 Ns540p696 Ns540p697 Ns540p698 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 135013457452) qz590 0 2 Ns540p699 Ns540p700 Ns540p698 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p702 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz97) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 125509009449) qz374) Bool.false 125509009449 67108864 557 67108864 Bool.true 37249950 67108864 1 9610000 (Ns540p694 rfl) (Enclosure.sfrac_false_div 125509009449 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 125509009449) qz374) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns540p695) qz375) 226375608064910080 72057594037927936 Bool.false 37249950 67108864 297 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q2 125509009449 67108864 226375608064910080 72057594037927936 297 Ns540p695 Ns540p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 37249950 67108864 Ns540p695 Ns540p114 135013457452 137438953472 19238770 19220000 (Ns540p701 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns540p703 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz97) Bool.false Ns540p673 Ns540p674 104408162551388153 12596019200000000000000 1004072075595 536870912 4451 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz97) (@HAdd.hAdd Real Real Real qz373 qz101 (Enclosure.sfrac Bool.true Ns540p675 Ns540p676)) Bool.false Ns540p673 Ns540p674 104408162551388153 12596019200000000000000 Ns540p677 (Ns540p693 rfl rfl)) 

noncomputable def Ns540p704 := Ns540p672 77487 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 778 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 522593555 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 536 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 114788591 536870912) qz100 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz97) qz97 1) Bool.true 18624975 33554432 338742429 40307261440000 297999600 536870912 4512 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz97) qz97 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz97)) Bool.true 18624975 33554432 338742429 40307261440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz97) qz97) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz97)) Bool.true 37249950 67108864 5419878864 644916183040000 18624975 33554432 338742429 40307261440000 (Ns540p702 rfl rfl) rfl)) rfl) (Ns540p703 rfl) RS541to552.d7 

noncomputable def Ns540p705 := nat_lit 237117741291947785048136931741696 

noncomputable def Ns540p706 := BSN.cos_dyadic_bound_f 124091208 536870912 2 1 536870912 268435456 Ns540p705 Ns540p136 Ns540p705 Ns540p705 Ns540p137 Ns540p705 522593555 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 124091208) qz19 0 1 Ns540p705 Ns540p136 Ns540p705 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 124091208) qz378 0 1 Ns540p705 Ns540p137 Ns540p705 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p707 := nat_lit 38690676141062429414180312215142180785992150611355221048421602202928249273815035830601712857964632517357706308001 

noncomputable def Ns540p708 := nat_lit 22026724204281885366416278493715487436626409981320017959836173500333952413442143511964450110274904649263521 

noncomputable def Ns540p709 := nat_lit 234409666819617282063166382491709722224610651571693478794514658909053834449185609801868639007056793618819700124065 

noncomputable def Ns540p710 := BSN.cos_dyadic_bound_f 727633177 536870912 4 3 536870912 268435456 Ns540p707 Ns540p153 Ns540p708 Ns540p709 Ns540p156 Ns540p708 114788591 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 727633177) qz19 0 3 Ns540p707 Ns540p153 Ns540p708 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 727633177) qz378 0 3 Ns540p709 Ns540p156 Ns540p708 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p711 := nat_lit 25445884264341321590805368981872255008428279749580392969783985113802014720 

noncomputable def Ns540p712 := nat_lit 10250912925725113920481267271321706242191576596535640562192536567873536 

noncomputable def Ns540p713 := nat_lit 66627385880918953981952330043607099402443851077268542931381173095990624256 

noncomputable def Ns540p714 := BSN.sin_dyadic_bound_f 564085996 536870912 3 2 536870912 268435456 Ns540p711 Ns540p276 Ns540p712 Ns540p713 Ns540p279 Ns540p712 465879053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 564085996) qz376 0 2 Ns540p711 Ns540p276 Ns540p712 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 564085996) qz377 0 2 Ns540p713 Ns540p279 Ns540p712 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p715 := nat_lit 41977320109932118997514401894801034145794901548133973072298725643597493637167330604793661742855161428854319390625 

noncomputable def Ns540p716 := nat_lit 28116005015010459972885827288908703812905482319767161453557753892269285998200792072164140037493769775390625 

noncomputable def Ns540p717 := nat_lit 254293183344555911701681948724331433637307375761439622223350636103472594088284697173397834180372062656651208990625 

noncomputable def Ns540p718 := BSN.cos_dyadic_bound_f 742584935 536870912 4 3 536870912 268435456 Ns540p715 Ns540p153 Ns540p716 Ns540p717 Ns540p156 Ns540p716 100139964 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 742584935) qz19 0 3 Ns540p715 Ns540p153 Ns540p716 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 742584935) qz378 0 3 Ns540p717 Ns540p156 Ns540p716 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p719 := Ns540p670 131306 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 365 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 465879053 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 232 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 100139964 536870912) qz100 rfl rfl (Ns540p704 RS541to552.d9 RS541to552.d11 RS541to552.d13 RS541to552.d17 (Ns540p706 rfl rfl) (Ns540p710 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns540p703 rfl) RS541to552.d19 RS541to552.d21 RS541to552.d23 RS541to552.d25 RS541to552.d17 (Ns540p714 rfl rfl) (Ns540p718 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns540p720 := nat_lit 1544173999911950577908798095329014537959088857133979182807507714807918401 

noncomputable def Ns540p721 := nat_lit 122390037414184991025278676126021493292524976846399563152273776013121 

noncomputable def Ns540p722 := nat_lit 4632277219661023363744343728634791570890681521448244749296218596871728961 

noncomputable def Ns540p723 := BSN.cos_dyadic_bound_f 324315913 536870912 3 2 536870912 268435456 Ns540p720 Ns540p160 Ns540p721 Ns540p722 Ns540p163 Ns540p721 441856522 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 324315913) qz19 0 2 Ns540p720 Ns540p160 Ns540p721 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 324315913) qz378 0 2 Ns540p722 Ns540p163 Ns540p721 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p724 := nat_lit 12640609542210681413810586673880377575601179433316282709138878270944770696483309803085183296538108927168127307776 

noncomputable def Ns540p725 := nat_lit 771247947289667873924692058356402797182817394573544852379390030235001668475997206145235199339740721975296 

noncomputable def Ns540p726 := nat_lit 76652790688251224460717787333514646263457529028657942149314536427664153545348518802418260342939015242205446410240 

noncomputable def Ns540p727 := BSN.cos_dyadic_bound_f 550299986 536870912 4 3 536870912 268435456 Ns540p724 Ns540p153 Ns540p725 Ns540p726 Ns540p156 Ns540p725 278682852 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 550299986) qz19 0 3 Ns540p724 Ns540p153 Ns540p725 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 550299986) qz378 0 3 Ns540p726 Ns540p156 Ns540p725 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p728 := Ns540p668 176715 BSN.abs_quadSignPos (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 441856522 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 278682852 536870912) qz100 rfl rfl (Ns540p719 rfl rfl) (Ns540p703 rfl) RS541to552.d27 RS541to552.d29 RS541to552.d31 RS541to552.d33 RS541to552.d17 (Ns540p723 rfl rfl) (Ns540p727 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p729 := nat_lit 29944939595800445685178597580519068272996524459676725596382469925999042080818053790519579936806936415982511890625 

noncomputable def Ns540p730 := nat_lit 10225654440263917525004301303298334158688147842827212059026252669338187417240314967416811291710215087890625 

noncomputable def Ns540p731 := nat_lit 181477861225100176012270862209281123185154660025218162879773362593467289121312562222044496776788521172593993490625 

noncomputable def Ns540p732 := BSN.cos_dyadic_bound_f 682560145 536870912 4 3 536870912 268435456 Ns540p729 Ns540p153 Ns540p730 Ns540p731 Ns540p156 Ns540p730 158363307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 682560145) qz19 0 3 Ns540p729 Ns540p153 Ns540p730 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 682560145) qz378 0 3 Ns540p731 Ns540p156 Ns540p730 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p733 := nat_lit 45763960312679876321253137794683639491543796300978096425443057678725152548602657980951086268941770424582144000000 

noncomputable def Ns540p734 := nat_lit 36410383075730083584754545537082010468263743170303964822402631037665961300189394352781771739136000000000000 

noncomputable def Ns540p735 := nat_lit 277196006018191844462751686783259996227232125753648598154883760472147690009655963694768125322755479604926873600000 

noncomputable def Ns540p736 := BSN.cos_dyadic_bound_f 758755940 536870912 4 3 536870912 268435456 Ns540p733 Ns540p153 Ns540p734 Ns540p735 Ns540p156 Ns540p734 84209737 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 758755940) qz19 0 3 Ns540p733 Ns540p153 Ns540p734 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 758755940) qz378 0 3 Ns540p735 Ns540p156 Ns540p734 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p737 := Ns540p666 216390 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 158363307 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 84209737 536870912) qz100 rfl rfl (Ns540p728 rfl) (Ns540p703 rfl) RS541to552.d35 RS541to552.d37 RS541to552.d39 RS541to552.d41 RS541to552.d17 (Ns540p732 rfl rfl) (Ns540p736 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p738 := nat_lit 16222058533939313956324747060443753804319228158311330914672831892817404160 

noncomputable def Ns540p739 := nat_lit 4167409653231385847008149825443673892969387310070897706491349940265216 

noncomputable def Ns540p740 := nat_lit 42479596544688209546622038630016255920247456644694323323094526105094676736 

noncomputable def Ns540p741 := BSN.sin_dyadic_bound_f 504061206 536870912 3 2 536870912 268435456 Ns540p738 Ns540p276 Ns540p739 Ns540p740 Ns540p279 Ns540p739 433201815 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 504061206) qz376 0 2 Ns540p738 Ns540p276 Ns540p739 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 504061206) qz377 0 2 Ns540p740 Ns540p279 Ns540p739 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p742 := nat_lit 694402519925411880260598904140928876183103996368693519466983689195421696 

noncomputable def Ns540p743 := nat_lit 24752214343733798343461654769693726070576453214248320050848679919616 

noncomputable def Ns540p744 := nat_lit 2083158055347548173185109789113247241097170836199652061760849370226425856 

noncomputable def Ns540p745 := BSN.cos_dyadic_bound_f 265583908 536870912 3 2 536870912 268435456 Ns540p742 Ns540p160 Ns540p743 Ns540p744 Ns540p163 Ns540p743 472509003 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 265583908) qz19 0 2 Ns540p742 Ns540p160 Ns540p743 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 265583908) qz378 0 2 Ns540p744 Ns540p163 Ns540p743 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p746 := Ns540p664 252073 BSN.abs_quadSignPos qz613 (BSN.sfrac_eq_quadSignPos_mul Bool.false 433201815 536870912) BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 472509003 536870912) qz100 rfl rfl (Ns540p737 rfl) (Ns540p703 rfl) RS541to552.d43 RS541to552.d45 RS541to552.d47 RS541to552.d49 RS541to552.d17 (Ns540p741 rfl rfl) (Ns540p745 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p747 := nat_lit 38956431730585656561871718560000 

noncomputable def Ns540p748 := BSN.cos_dyadic_bound_f 79003220 536870912 2 1 536870912 268435456 Ns540p747 Ns540p136 Ns540p747 Ns540p747 Ns540p137 Ns540p747 531068535 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 79003220) qz19 0 1 Ns540p747 Ns540p136 Ns540p747 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 79003220) qz378 0 1 Ns540p747 Ns540p137 Ns540p747 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p749 := Ns540p662 Bool.true 252154709 252073 Bool.true 79003220 28296951008113761 1 Bool.false 531068535 Bool.false Bool.true 98848424 268749 BSN.abs_quadSignPos qz380 (BSN.sfrac_eq_quadSignPos_mul Bool.false 531068535 536870912) qz100 rfl (Ns540p746 rfl) (Ns540p703 rfl) RS541to552.d51 RS541to552.d53 RS541to552.d17 (Ns540p748 rfl rfl) rfl 

noncomputable def Ns540p750 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz97) qz97 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz97) qz97 12) 98848424 536870912 268749 536870912 98848424 536870912 268749 536870912 106137687085285376 12356053 33554432 268749 268435456 (Ns540p749 rfl rfl rfl rfl) 

noncomputable def Ns540p751 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz98) (Zeta.RiemannSiegel.correction qz99) 19215469 67108864 1 67108864 615732072849 1099511627776 15194793168830409 676243631547351040000 11831580558135701181 73786976294838206464 

noncomputable def Ns540p752 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz98 1 1 0 1 19215469 67108864 1 67108864 19215469 67108864 1 67108864 

noncomputable abbrev qz106 := qz432

noncomputable def Ns540p753 := @Enclosure.Real.IsNear.sqrt_image qz106 39935163473 268435456 3739 268435456 409267883 409267922 33554432 (@Enclosure.Real.IsNear.of_eq qz106 (@HMul.hMul Real Real Real qz5 qz97 qz3) Bool.false 39935163473 268435456 3739 268435456 (BSN.t_div_two_pi_mk qz97 934750 1000 qz100) (@Enclosure.Real.IsNear.mulLit_ff qz97 qz3 934750 1000 0 1 10680707 67108864 1 67108864 39935163473 268435456 3739 268435456 (Enclosure.Real.IsNear.const Bool.false 934750 1000) RS541to552.d56 rfl)) 

noncomputable abbrev qz741 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 934750 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz631 := qz741

noncomputable abbrev qz439 := qz631

noncomputable abbrev qz107 := qz439

noncomputable def Ns540p754 := @Enclosure.Real.IsNear.sqrt_image qz107 818535805 67108864 39 67108864 117186822 117186829 33554432 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 818535805 67108864 39 67108864 818535805 67108864 39 67108864 (Ns540p753 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns540p755 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 234373651 67108864 7 67108864 9607734 9607735 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 234373651 67108864 7 67108864 234373651 67108864 7 67108864 (Ns540p754 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns540p756 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 19215469 67108864 1 67108864 19215469 67108864 1 67108864 (Ns540p755 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz108 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz433))

noncomputable abbrev qz632 := (@HMul.hMul Real Real Real qz717 qz740 qz740)

noncomputable abbrev qz440 := (@HSub.hSub Real Real Real qz582 (@HSub.hSub Real Real Real qz582 qz632 qz627) qz594)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz440))

noncomputable def Ns540p757 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz99) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz108) qz109) Bool.false 615732072849 

noncomputable def Ns540p758 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz108) qz109 12862319 4194304 595 

noncomputable def Ns540p759 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz108) Bool.false 205797104 67108864 2380 67108864 12862319 4194304 595 

noncomputable def Ns540p760 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 10941844 33554432 1215584432 322458091520000 2735461 8388608 75974027 20153630720000 

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz355 qz352 qz433)

noncomputable def Ns540p761 := @Enclosure.Real.IsNear.cos_image qz110 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20780751) qz616) Bool.false 20780751 16777216 123 33554432 Bool.false 10941844 33554432 1 

noncomputable def Ns540p762 := nat_lit 1052456941066357771270574417 

noncomputable def Ns540p763 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz99 884279719003555 140737488355328 1 500000000000000 13229437 67108864 39 67108864 11698522832935233648535 9444732965739290427392 Ns540p762 

noncomputable def Ns540p764 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz1 818535805 67108864 39 67108864 12 1 0 1 13229437 13229437 67108864 39 

noncomputable def Ns540p765 := @Ns540p764 67108864 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 818535805 67108864 39 67108864 818535805 67108864 39 67108864 (Ns540p753 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns540p766 := @Enclosure.Real.IsNear.recentre' qz110 Bool.false 11698522832935233648535 9444732965739290427392 Ns540p762 Ns540p333 20780751 16777216 123 33554432 (@Ns540p763 Ns540p333 RS541to552.d55 (Ns540p765 rfl rfl) rfl) 

noncomputable def Ns540p767 := nat_lit 23395805939380388871735942775530811717889234898101828155205229503109801161609196585445766742081 

noncomputable def Ns540p768 := nat_lit 6485371560768448104093529054388973720965313244378298427981997422008090293600388312744001 

noncomputable def Ns540p769 := nat_lit 141802136335707594821083847824995226688704105530174894747517897577495096347860626955579275100225 

noncomputable def Ns540p770 := BSN.cos_dyadic_bound_f 20780751 16777216 4 3 33554432 9610000 Ns540p767 Ns540p519 Ns540p768 Ns540p769 Ns540p522 Ns540p768 10941844 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 20780751) (BSN.cosEvenQ 16777216) 0 3 Ns540p767 Ns540p519 Ns540p768 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 20780751) (BSN.cosOddQ 16777216) 0 3 Ns540p769 Ns540p522 Ns540p768 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p771 := @Enclosure.Real.IsNear.inv_image qz108 2735461 8388608 75974027 20153630720000 102897362 102899742 33554432 (Ns540p760 (@Ns540p761 9610000 (Ns540p766 rfl) (Enclosure.sfrac_false_div 20780751 16777216) (Ns540p770 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns540p772 := @Enclosure.Real.IsNear.recentre' qz109 Bool.false 6127488 33554432 

noncomputable abbrev qz111 := (@HMul.hMul Real Real Real qz355 qz352 qz440)

noncomputable def Ns540p773 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 93090225)) qz374) Bool.true 93090225 67108864 

noncomputable def Ns540p774 := nat_lit 879212320297198192622055571525 

noncomputable def Ns540p775 := nat_lit 98476056361706773748470425484174961 

noncomputable def Ns540p776 := @Enclosure.Real.IsNear.recentre' qz111 Bool.true Ns540p774 Ns540p210 Ns540p775 

noncomputable abbrev qz112 := qz440

noncomputable def Ns540p777 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz112 884279719003555 140737488355328 1 500000000000000 994269461803255 

noncomputable abbrev qz441 := (@HSub.hSub Real Real Real qz582 qz632 qz627)

noncomputable abbrev qz113 := qz441

noncomputable def Ns540p778 := @Enclosure.Real.IsNear.subLit_tf qz113 qz30 712794485092599 4503599627370496 3649143303 4503599627370496 1 16 

noncomputable abbrev qz442 := qz632

noncomputable abbrev qz114 := qz442

noncomputable def Ns540p779 := @Enclosure.Real.IsNear.subLit_ff_n qz114 qz99 175018003336969 4503599627370496 1031897607 4503599627370496 13229437 67108864 39 67108864 

noncomputable def Ns540p780 := @Enclosure.Real.IsNear.mulLit_ff qz99 qz99 13229437 67108864 39 67108864 13229437 67108864 39 67108864 175018003336969 4503599627370496 

noncomputable def Ns540p781 := nat_lit 617927490854779946551354096289437644121271926726613029112208005327266448159177252892800099298837890625 

noncomputable def Ns540p782 := nat_lit 423495656067652611055534315243366013806753277721223111538198223246482528076486647129058837890625 

noncomputable def Ns540p783 := nat_lit 3743262208700093100855765287870812327745325128040790870407546914706630335515327578727495148514837890625 

noncomputable def Ns540p784 := BSN.cos_dyadic_bound_f 93090225 67108864 4 3 33554432 9610000 Ns540p781 Ns540p219 Ns540p782 Ns540p783 Ns540p222 Ns540p782 6127488 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 93090225) qz596 0 3 Ns540p781 Ns540p219 Ns540p782 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 93090225) (BSN.cosOddQ 67108864) 0 3 Ns540p783 Ns540p222 Ns540p782 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p785 := @Ns540p772 3363338864 644916183040000 47871 262144 210208679 40307261440000 (@Ns540p773 343 67108864 Bool.false 6127488 33554432 1 9610000 (@Ns540p776 Ns540p213 93090225 67108864 343 67108864 (@Ns540p777 4503599627370496 3649143303 4503599627370496 Ns540p774 Ns540p210 Ns540p775 Ns540p213 RS541to552.d55 (@Ns540p778 0 1 15908311388852080 994269461803255 4503599627370496 3649143303 4503599627370496 (@Ns540p779 47834828160029253697536 712794485092599 4503599627370496 3649143303 4503599627370496 (@Ns540p780 1031897607 4503599627370496 (Ns540p765 rfl rfl) (Ns540p765 rfl rfl) rfl) (Ns540p765 rfl rfl) rfl rfl) qz389 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 93090225 67108864) (BSN.cos_neg_of_bound 93090225 67108864 Bool.false 6127488 33554432 1 9610000 (Ns540p784 rfl rfl)) rfl rfl) 

noncomputable def Ns540p786 := @Ns540p751 29235379214595070818723 Ns540p659 (Ns540p752 qz32 (@Enclosure.Real.IsNear.of_eq qz98 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 19215469 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz106 (BSN.t_div_two_pi_nonneg qz97 934750 1000 qz100)) Ns540p756) rfl) (@Ns540p757 1099511627776 15194793168830409 676243631547351040000 (BSN.correction_mk qz99 (BSN.cos_two_pi_p_ne_zero_mk qz97 934750 1000 12 qz100 rfl rfl (@BSN.floor_sqrt_eq_dec qz97 934750 1000 12 qz100 rfl rfl rfl))) (@Ns540p758 16777216 47871 262144 210208679 40307261440000 615732072849 1099511627776 15194793168830409 676243631547351040000 (@Ns540p759 16777216 (Ns540p771 rfl rfl rfl rfl rfl) rfl) (Ns540p785 rfl) rfl)) 

noncomputable def Ns540p787 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz97) (hardyZApproximantRS₀ qz97) Bool.true 39002828451968757437 73786976294838206464 Ns540p658 Ns540p659 (@Eq.refl Real (hardyZApproximantRS₀ qz97)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz97) (@HSub.hSub Real Real Real qz33 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz97) qz97 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz98) (Zeta.RiemannSiegel.correction qz99))) Bool.true 39002828451968757437 73786976294838206464 Ns540p658 Ns540p659 (BSN.hardyZApproximantRS₀_eq qz97 12 (@BSN.floor_sqrt_eq_dec qz97 934750 1000 12 qz100 rfl rfl rfl)) (@Ns540p661 39002828451968757437 73786976294838206464 Ns540p658 Ns540p659 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz97) qz97 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz97) qz97 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz97) qz97 12)) Bool.true 12356053 33554432 268749 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz97) qz97 12) (Ns540p750 (Ns540p749 rfl rfl rfl rfl) rfl rfl)) (Ns540p786 rfl) rfl rfl)) 

theorem RS541to552.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz97) Bool.true 39002828451968757437 73786976294838206464 Ns540p658 Ns540p659 := Ns540p787 

noncomputable def Ns540p788 := nat_lit 11447589538487988525669079 

noncomputable def Ns540p789 := nat_lit 11345485475094322625904640000 

noncomputable def Ns540p790 := nat_lit 5981984105291630162213284610048 

noncomputable abbrev qz742 := (Enclosure.sfrac Bool.false 935378 1000)

noncomputable abbrev qz633 := qz742

noncomputable abbrev qz443 := qz633

noncomputable abbrev qz115 := qz443

noncomputable abbrev qz743 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 935378 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz634 := qz743

noncomputable abbrev qz444 := qz634

noncomputable abbrev qz116 := (@HPow.hPow Real Real Real qz356 qz444 qz358)

noncomputable abbrev qz744 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 935378 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz635 := qz744

noncomputable abbrev qz445 := qz635

noncomputable abbrev qz117 := qz445

noncomputable def Ns540p791 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz115) qz115 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz116) (Zeta.RiemannSiegel.correction qz117)) 359321645 268435456 268933 268435456 3000385561506117853497 18889465931478580854784 81075253305253698149079 Ns540p789 Ns540p790 

noncomputable def Ns540p792 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz115) qz115 Real.cos BSN.quadSignPos 11 12 935378 1000 288 536870912 268435456 9007199254740992 Bool.false 1004915424587 4454 1334074092 57 154981288 8 

noncomputable def Ns540p793 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz115) qz115 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 935378 1000 179 236 536870912 268435456 9007199254740992 Bool.false 1004915424587 4454 

noncomputable def Ns540p794 := Ns540p793 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 64805779 216540 Bool.true 437040135 Bool.true 230697134 28296951008113761 1 Bool.false 390344971 Bool.false Bool.false 488062848 Bool.false Bool.false 205788623 

noncomputable def Ns540p795 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz115) qz115 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 935378 1000 46 116 536870912 268435456 9007199254740992 Bool.false 1004915424587 4454 

noncomputable def Ns540p796 := Ns540p795 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 24386171 176839 Bool.true 540305126 Bool.true 656212043 28296951008113761 1 Bool.false 287176885 Bool.true Bool.false 183338271 Bool.false Bool.true 64805779 

noncomputable def Ns540p797 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz115) qz115 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 935378 1000 124 32 536870912 268435456 9007199254740992 Bool.false 1004915424587 4454 

noncomputable def Ns540p798 := Ns540p797 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 173202994 131399 Bool.false 563564366 Bool.false 737575782 28296951008113761 1 Bool.false 267261604 Bool.false Bool.false 105056778 Bool.false Bool.true 24386171 

noncomputable def Ns540p799 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz115) qz115 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 935378 1000 366 233 536870912 268435456 9007199254740992 Bool.false 1004915424587 4454 

noncomputable def Ns540p800 := Ns540p799 744261104 56 268435448 8 864060384 56 240095976 8 Bool.false 178271432 77544 Bool.false 96724158 Bool.false 199989149 28296951008113761 1 Bool.false 528181407 Bool.true Bool.false 195395956 Bool.true Bool.true 173202994 

noncomputable def Ns540p801 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz115) qz115 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 935378 1000 778 537 536870912 268435456 9007199254740992 Bool.false 1004915424587 4454 

noncomputable def Ns540p802 := Ns540p801 372130544 56 379625064 8 589812976 56 309962568 8 Bool.false 446591008 4520 Bool.false 733742218 Bool.false 357264764 28296951008113761 1 Bool.false 108813517 Bool.true Bool.false 331474337 Bool.true Bool.false 178271432 

noncomputable def Ns540p803 := nat_lit 1587944146678483648225479085609927996625541940014569575531 

noncomputable def Ns540p804 := nat_lit 848351016785262880158776019744189710361720948523008000 

noncomputable def Ns540p805 := nat_lit 7872512000000000000000000 

noncomputable def Ns540p806 := nat_lit 343698239341759257937627020016640000 

noncomputable def Ns540p807 := nat_lit 1928926887524682752334174483039964139520 

noncomputable abbrev qz636 := (@Eq.refl Real qz742)

noncomputable abbrev qz446 := qz636

noncomputable abbrev qz118 := qz446

noncomputable def Ns540p808 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz115 935378 1000 3499729011536 16000000 1870756 4000 2000 Ns540p806 Ns540p807 qz118 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns540p809 := nat_lit 32521096123975345115657811673291325370891098931498384906874880 

noncomputable abbrev qz637 := (@HSub.hSub Real Real Real qz721 qz722 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz723 (@Nat.cast Real Real.instNatCast 1870756))))

noncomputable abbrev qz447 := (@HSub.hSub Real Real Real qz582 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 935378 4000) (Real.log (Enclosure.sfrac Bool.false 3499729011536 16000000))) (@HMul.hMul Real Real Real qz579 qz583 qz637))

noncomputable abbrev qz638 := (Enclosure.sfrac Bool.false 935378 2000)

noncomputable abbrev qz119 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz447 qz638) (@HMul.hMul Real Real Real qz355 qz638 (Real.log Real.pi)))

noncomputable def Ns540p810 := @Enclosure.Real.IsNear.addLit_ft_p qz119 (Enclosure.sfrac Bool.true Ns540p806 Ns540p807) 16859684744955231978719 9007199254740992000 65298804819437923903 Ns540p805 Ns540p806 Ns540p807 0 1 Ns540p809 

noncomputable def Ns540p811 := nat_lit 565717145316037674474152132608000 

noncomputable abbrev qz120 := (@HSub.hSub Real Real Real qz361 qz447 qz638)

noncomputable def Ns540p812 := @Enclosure.Real.IsNear.subLit_ff_p qz120 (@HMul.hMul Real Real Real qz5 qz638 (Real.log Real.pi)) 21681937230552405099743 9007199254740992000 5896120140875443 1922000000000000000000 17964290401329 33554432000 1403067 268435456000 Ns540p811 16859684744955231978719 9007199254740992000 

noncomputable def Ns540p813 := nat_lit 43363874461104810199486000 

noncomputable abbrev qz121 := qz447

noncomputable def Ns540p814 := @Enclosure.Real.IsNear.subLit_ff_p qz121 qz638 25894505242802964907231 9007199254740992000 5896120140875443 1922000000000000000000 935378 2000 0 1 Ns540p813 21681937230552405099743 9007199254740992000 5896120140875443 1922000000000000000000 

noncomputable def Ns540p815 := nat_lit 58309242081215393902568574244553228288 

noncomputable def Ns540p816 := nat_lit 118915817780762207733153792 

noncomputable def Ns540p817 := nat_lit 127679370842436878230599594027514472530919344261797572822103306080706059092416495708275370671612792060298577316055151911237095257531157878903093541406202920960 

noncomputable def Ns540p818 := nat_lit 2778225280651458319994431506763497735212941476448468762943637001160200547587127982360387258576128887925685319100578781543460258290432461397361058283375296512 

noncomputable def Ns540p819 := nat_lit 602483408019996264262294035981289267059198337871640997024005250246480855377546579071890065952005955011608532562064009418898727215592104882476070993920 

noncomputable def Ns540p820 := BSN.log_dyadic_bound 1402577011536 5596881011536 7 6 Ns540p817 268435456 76880000 Ns540p818 Ns540p819 137467221 6999458023072 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1402577011536) (BSN.artanhQ 5596881011536) 0 6 Ns540p818 Ns540p817 Ns540p819 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz448 := (Real.log (Enclosure.sfrac Bool.false 3499729011536 16000000))

noncomputable def Ns540p821 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 935378 4000) qz448 935378 4000 0 1 55374492789042279 4503599627370496 12500016337 961000000000000000 25898041158014394423231 9007199254740992000 5846120140635193 1922000000000000000000 (Enclosure.Real.IsNear.const Bool.false 935378 4000) (BSN.isNear_log_sfrac 3499729011536 16000000 55374492789042279 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3499729011536) qz364)) Bool.false Ns540p816 Ns540p114 1000001306960000 76880000000000000000000 55374492789042279 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3499729011536 16000000 17 6999458023072 4194304000000 137467221 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns540p820 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p822 := BSN.arctan_dyadic_bound_f 1000 1870756 1 0 33554432 9610000 0 1 1 0 1 1 17936 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1870756) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1870756) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns540p823 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1870756))) 884279719003555 562949953421312 1 2000000000000000 17936 33554432 1 9610000 29661406629919329353728 883978802857379 562949953421312 200000000961 1922000000000000000 qz15 (Ns540p822 rfl) rfl rfl 

noncomputable abbrev qz449 := (@HMul.hMul Real Real Real qz579 qz583 qz637)

noncomputable abbrev qz122 := qz449

noncomputable abbrev qz450 := qz637

noncomputable abbrev qz123 := qz450

noncomputable def Ns540p824 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 935378 4000) qz448) qz122 25898041158014394423231 9007199254740992000 5846120140635193 1922000000000000000000 883978802857379 2251799813685248 200000000961 7688000000000000000 Ns540p815 25894505242802964907231 9007199254740992000 5896120140875443 1922000000000000000000 (Ns540p821 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz123 1 4 0 1 883978802857379 562949953421312 200000000961 1922000000000000000 883978802857379 2251799813685248 200000000961 7688000000000000000 qz372 Ns540p823 rfl) 

noncomputable def Ns540p825 := @Ns540p810 Ns540p803 Ns540p804 65298804819437923903 Ns540p805 (@Ns540p812 65298804819437923903 Ns540p805 (Ns540p814 (Ns540p824 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 935378 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz638 (Real.log Real.pi) 935378 2000 0 1 38410761 33554432 3 268435456 17964290401329 33554432000 1403067 268435456000 (Enclosure.Real.IsNear.const Bool.false 935378 2000) RS541to552.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns540p806 Ns540p807) 

noncomputable def Ns540p826 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz115) Bool.false Ns540p803 Ns540p804 65298804819437923903 Ns540p805 125614428073 67108864 279 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz115) (@HAdd.hAdd Real Real Real qz373 qz119 (Enclosure.sfrac Bool.true Ns540p806 Ns540p807)) Bool.false Ns540p803 Ns540p804 65298804819437923903 Ns540p805 Ns540p808 (Ns540p825 rfl rfl)) 

noncomputable def Ns540p827 := nat_lit 9501342377948407698292736 

noncomputable def Ns540p828 := nat_lit 358736504605372850116628578924993732060221572580897176093638060383942783059159130893382123520 

noncomputable def Ns540p829 := nat_lit 46199975943266144436568348213124696692647303168343434164427665391357367878632476496239452487680 

noncomputable def Ns540p830 := nat_lit 110469233333673917666222002629342487771328889435345860654488560119860875367348673068466176 

noncomputable def Ns540p831 := nat_lit 939369133302960087772091442513583696129902919509930615518468605241560847547202968773889949696 

noncomputable def Ns540p832 := nat_lit 846999558959879314670419717240619439365200558086296293014507198841551744441595402431056628940800 

noncomputable def Ns540p833 := BSN.sin_dyadic_bound_f 135022196132 137438953472 3 2 67108864 19238770 Ns540p828 Ns540p829 Ns540p830 Ns540p831 Ns540p832 Ns540p830 55823876 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 135022196132) (BSN.sinEvenQ 137438953472) 0 2 Ns540p828 Ns540p829 Ns540p830 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 135022196132) (BSN.sinOddQ 137438953472) 0 2 Ns540p831 Ns540p832 Ns540p830 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p834 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz115) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 125614428073) qz374) Bool.false 125614428073 67108864 279 33554432 Bool.false 55823876 67108864 1 9610000 (Ns540p826 rfl) (Enclosure.sfrac_false_div 125614428073 67108864) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 125614428073) qz374) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns540p827) qz375) 226375608064910080 72057594037927936 Bool.false 55823876 67108864 297 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q3 125614428073 67108864 226375608064910080 72057594037927936 297 Ns540p827 Ns540p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 55823876 67108864 Ns540p827 Ns540p114 135022196132 137438953472 19238770 19220000 (Ns540p833 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns540p835 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz115) Bool.false Ns540p803 Ns540p804 65298804819437923903 Ns540p805 1004915424587 536870912 4454 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz115) (@HAdd.hAdd Real Real Real qz373 qz119 (Enclosure.sfrac Bool.true Ns540p806 Ns540p807)) Bool.false Ns540p803 Ns540p804 65298804819437923903 Ns540p805 Ns540p808 (Ns540p825 rfl rfl)) 

noncomputable def Ns540p836 := Ns540p802 77544 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 778 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 108813517 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 537 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 331474337 536870912) qz118 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz115) qz115 1) Bool.false 13955969 16777216 169671527 20153630720000 446591008 536870912 4520 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz115) qz115 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz115)) Bool.false 13955969 16777216 169671527 20153630720000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz115) qz115) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz115)) Bool.false 55823876 67108864 2714744432 322458091520000 13955969 16777216 169671527 20153630720000 (Ns540p834 rfl rfl) rfl)) rfl) (Ns540p835 rfl) RS541to552.d7 

noncomputable def Ns540p837 := nat_lit 40009212337378591451364019154024816931503852177304091688149312149955942138141106089794359168871813059900767277056 

noncomputable def Ns540p838 := nat_lit 24351297042034329633168907074301570700499741451990739098170162576554454144226965582297481147460526879870976 

noncomputable def Ns540p839 := nat_lit 242387077940520804604265422142313324444871345706492655161157590178083925076795281556883529405614168021687493529600 

noncomputable def Ns540p840 := BSN.cos_dyadic_bound_f 733742218 536870912 4 3 536870912 268435456 Ns540p837 Ns540p153 Ns540p838 Ns540p839 Ns540p156 Ns540p838 108813517 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 733742218) qz19 0 3 Ns540p837 Ns540p153 Ns540p838 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 733742218) qz378 0 3 Ns540p839 Ns540p156 Ns540p838 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p841 := nat_lit 4093079562089816417364607294800364323921428969900719527347330608156180480 

noncomputable def Ns540p842 := nat_lit 265412565998362982814119126331941274294404789773591849479293129261056 

noncomputable def Ns540p843 := nat_lit 10719540566080759933982748626844035800588218265794631994343851784866430976 

noncomputable def Ns540p844 := BSN.sin_dyadic_bound_f 357264764 536870912 3 2 536870912 268435456 Ns540p841 Ns540p276 Ns540p842 Ns540p843 Ns540p279 Ns540p842 331474337 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 357264764) qz376 0 2 Ns540p841 Ns540p276 Ns540p842 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 357264764) qz377 0 2 Ns540p843 Ns540p279 Ns540p842 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p845 := nat_lit 87526554197212934513457142753296 

noncomputable def Ns540p846 := BSN.cos_dyadic_bound_f 96724158 536870912 2 1 536870912 268435456 Ns540p845 Ns540p136 Ns540p845 Ns540p845 Ns540p137 Ns540p845 528181407 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 96724158) qz19 0 1 Ns540p845 Ns540p136 Ns540p845 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 96724158) qz378 0 1 Ns540p845 Ns540p137 Ns540p845 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p847 := nat_lit 1599652796257586140003656069128401 

noncomputable def Ns540p848 := BSN.sin_dyadic_bound_f 199989149 536870912 2 1 536870912 268435456 Ns540p847 Ns540p282 Ns540p847 Ns540p847 Ns540p283 Ns540p847 195395956 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 199989149) qz376 0 1 Ns540p847 Ns540p282 Ns540p847 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 199989149) qz377 0 1 Ns540p847 Ns540p283 Ns540p847 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p849 := Ns540p800 131399 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 366 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 528181407 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 195395956 536870912) qz118 rfl rfl (Ns540p836 RS541to552.d9 RS541to552.d11 RS541to552.d13 RS541to552.d17 (Ns540p840 rfl rfl) (Ns540p844 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns540p835 rfl) RS541to552.d19 RS541to552.d21 RS541to552.d23 RS541to552.d25 RS541to552.d17 (Ns540p846 rfl rfl) (Ns540p848 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns540p850 := nat_lit 13905052067710491995398293634972921829849411865577322416494731745015958583523855993877636744948041439471815233536 

noncomputable def Ns540p851 := nat_lit 1026413368825746419895162359727672801125915294609718919258607493133612076838661690299985862672348768505856 

noncomputable def Ns540p852 := nat_lit 84316694128769323313365564820321031406074466143773531085058256646155828478132507559611524634774255515525767106560 

noncomputable def Ns540p853 := BSN.cos_dyadic_bound_f 563564366 536870912 4 3 536870912 268435456 Ns540p850 Ns540p153 Ns540p851 Ns540p852 Ns540p156 Ns540p851 267261604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 563564366) qz19 0 3 Ns540p850 Ns540p153 Ns540p851 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 563564366) qz378 0 3 Ns540p852 Ns540p156 Ns540p851 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p854 := nat_lit 40853712754666202723326499719027751643111522636457258632805812727475525624388402436005087026509508266558766125056 

noncomputable def Ns540p855 := nat_lit 25922672955943581141991306086781135898925031440375241291145970484319137069030009228815622852735555269758976 

noncomputable def Ns540p856 := nat_lit 247496096593169080657659431603552680494176504626311056676580261556815807169135712991710326945554180865945248665600 

noncomputable def Ns540p857 := BSN.cos_dyadic_bound_f 737575782 536870912 4 3 536870912 268435456 Ns540p854 Ns540p153 Ns540p855 Ns540p856 Ns540p156 Ns540p855 105056778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 737575782) qz19 0 3 Ns540p854 Ns540p153 Ns540p855 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 737575782) qz378 0 3 Ns540p856 Ns540p156 Ns540p855 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p858 := Ns540p798 176839 BSN.abs_quadSignPos (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267261604 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 105056778 536870912) qz118 rfl rfl (Ns540p849 rfl rfl) (Ns540p835 rfl) RS541to552.d27 RS541to552.d29 RS541to552.d31 RS541to552.d33 RS541to552.d17 (Ns540p853 rfl rfl) (Ns540p857 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p859 := nat_lit 11746438153200097269139813534730593312312122154527673891962514230867032172867224968140349100665122240282534547456 

noncomputable def Ns540p860 := nat_lit 618969221000475393999545072272475993081888357782777535036319620107846820921882595051529864844908911333376 

noncomputable def Ns540p861 := nat_lit 71232730371694774630089665669514062553747588719019637594882297546425870099758990726724154853109535732592210022400 

noncomputable def Ns540p862 := BSN.cos_dyadic_bound_f 540305126 536870912 4 3 536870912 268435456 Ns540p859 Ns540p153 Ns540p860 Ns540p861 Ns540p156 Ns540p860 287176885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 540305126) qz19 0 3 Ns540p859 Ns540p153 Ns540p860 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 540305126) qz378 0 3 Ns540p861 Ns540p156 Ns540p860 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p863 := nat_lit 25576329762927238258851515662615391116153785385516082532054146050081194327910494697159367620965894601643769966481 

noncomputable def Ns540p864 := nat_lit 6375736457620905472698899744802773585944120336851292796356543885685426679556180249877724775629059029184401 

noncomputable def Ns540p865 := nat_lit 155025786179276065555693459039865844262798101875854963160591693096682609572673250858359498124612787907716609191825 

noncomputable def Ns540p866 := BSN.cos_dyadic_bound_f 656212043 536870912 4 3 536870912 268435456 Ns540p863 Ns540p153 Ns540p864 Ns540p865 Ns540p156 Ns540p864 183338271 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 656212043) qz19 0 3 Ns540p863 Ns540p153 Ns540p864 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 656212043) qz378 0 3 Ns540p865 Ns540p156 Ns540p864 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p867 := Ns540p796 216540 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 287176885 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 183338271 536870912) qz118 rfl rfl (Ns540p858 rfl) (Ns540p835 rfl) RS541to552.d35 RS541to552.d37 RS541to552.d39 RS541to552.d41 RS541to552.d17 (Ns540p862 rfl rfl) (Ns540p866 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p868 := nat_lit 9166628561950776732201245993824428342775940427117174884260829201208530625 

noncomputable def Ns540p869 := nat_lit 1330977069171934381684837445558205972999410178595818022523487687890625 

noncomputable def Ns540p870 := nat_lit 24005681794616232119147202151771170469028321121208207658170467023099090625 

noncomputable def Ns540p871 := BSN.sin_dyadic_bound_f 437040135 536870912 3 2 536870912 268435456 Ns540p868 Ns540p276 Ns540p869 Ns540p870 Ns540p279 Ns540p869 390344971 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 437040135) qz376 0 2 Ns540p868 Ns540p276 Ns540p869 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 437040135) qz377 0 2 Ns540p870 Ns540p279 Ns540p869 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p872 := nat_lit 395336023297320970386548546748783929949994366269394880192146026402693376 

noncomputable def Ns540p873 := nat_lit 8023014807855978838610720470119141585215058822231479708294420644096 

noncomputable def Ns540p874 := nat_lit 1185992023862347199201968418805411551566812668690540177617021490366791936 

noncomputable def Ns540p875 := BSN.cos_dyadic_bound_f 230697134 536870912 3 2 536870912 268435456 Ns540p872 Ns540p160 Ns540p873 Ns540p874 Ns540p163 Ns540p873 488062848 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 230697134) qz19 0 2 Ns540p872 Ns540p160 Ns540p873 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 230697134) qz378 0 2 Ns540p874 Ns540p163 Ns540p873 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p876 := Ns540p794 252246 BSN.abs_quadSignPos qz613 (BSN.sfrac_eq_quadSignPos_mul Bool.false 390344971 536870912) BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 488062848 536870912) qz118 rfl rfl (Ns540p867 rfl) (Ns540p835 rfl) RS541to552.d43 RS541to552.d45 RS541to552.d47 RS541to552.d49 RS541to552.d17 (Ns540p871 rfl rfl) (Ns540p875 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p877 := nat_lit 29109344722386151499771641486096 

noncomputable def Ns540p878 := BSN.cos_dyadic_bound_f 73452758 536870912 2 1 536870912 268435456 Ns540p877 Ns540p136 Ns540p877 Ns540p877 Ns540p137 Ns540p877 531853973 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 73452758) qz19 0 1 Ns540p877 Ns540p136 Ns540p877 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 73452758) qz378 0 1 Ns540p877 Ns540p137 Ns540p877 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p879 := Ns540p792 Bool.false 205788623 252246 Bool.true 73452758 28296951008113761 1 Bool.false 531853973 Bool.false Bool.false 359321645 268933 BSN.abs_quadSignPos qz380 (BSN.sfrac_eq_quadSignPos_mul Bool.false 531853973 536870912) qz118 rfl (Ns540p876 rfl) (Ns540p835 rfl) RS541to552.d51 RS541to552.d53 RS541to552.d17 (Ns540p878 rfl rfl) rfl 

noncomputable def Ns540p880 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz115) qz115 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz115) qz115 12) 359321645 536870912 268933 536870912 359321645 536870912 268933 536870912 385818678504980480 359321645 268435456 268933 268435456 (Ns540p879 rfl rfl rfl rfl) 

noncomputable def Ns540p881 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz116) (Zeta.RiemannSiegel.correction qz117) 19212243 67108864 1 67108864 156170498234179 281474976710656 4215096029373341 169060907886837760000 3000385561506117853497 18889465931478580854784 

noncomputable def Ns540p882 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz116 1 1 0 1 19212243 67108864 1 67108864 19212243 67108864 1 67108864 

noncomputable abbrev qz124 := qz444

noncomputable def Ns540p883 := @Enclosure.Real.IsNear.sqrt_image qz124 4995249176123 33554432000 467689 33554432000 409405340 409405380 33554432 (@Enclosure.Real.IsNear.of_eq qz124 (@HMul.hMul Real Real Real qz5 qz115 qz3) Bool.false 4995249176123 33554432000 467689 33554432000 (BSN.t_div_two_pi_mk qz115 935378 1000 qz118) (@Enclosure.Real.IsNear.mulLit_ff qz115 qz3 935378 1000 0 1 10680707 67108864 1 67108864 4995249176123 33554432000 467689 33554432000 (Enclosure.Real.IsNear.const Bool.false 935378 1000) RS541to552.d56 rfl)) 

noncomputable abbrev qz745 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 935378 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz639 := qz745

noncomputable abbrev qz451 := qz639

noncomputable abbrev qz125 := qz451

noncomputable def Ns540p884 := @Enclosure.Real.IsNear.sqrt_image qz125 25587835 2097152 5 8388608 117206499 117206506 33554432 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 818810720 67108864 40 67108864 25587835 2097152 5 8388608 (Ns540p883 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns540p885 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz125) 234413005 67108864 7 67108864 9606121 9606122 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz125) Bool.false 234413005 67108864 7 67108864 234413005 67108864 7 67108864 (Ns540p884 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns540p886 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 19212243 67108864 1 67108864 19212243 67108864 1 67108864 (Ns540p885 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz126 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz445))

noncomputable abbrev qz640 := (@HMul.hMul Real Real Real qz717 qz744 qz744)

noncomputable abbrev qz452 := (@HSub.hSub Real Real Real qz582 (@HSub.hSub Real Real Real qz582 qz640 qz635) qz594)

noncomputable abbrev qz127 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz452))

noncomputable def Ns540p887 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz117) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz126) qz127) Bool.false 156170498234179 

noncomputable def Ns540p888 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz126) qz127 222469217 67108864 2847 

noncomputable def Ns540p889 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz126) Bool.false 222469217 67108864 2847 67108864 222469217 67108864 2847 

noncomputable def Ns540p890 := @Enclosure.Real.IsNear.recentre' qz126 Bool.false 10121849 33554432 622207216 161229045760000 10121849 33554432 38887951 10076815360000 

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz355 qz352 qz445)

noncomputable def Ns540p891 := @Enclosure.Real.IsNear.cos_image qz128 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42425173) qz384) Bool.false 42425173 33554432 63 16777216 Bool.false 10121849 33554432 1 

noncomputable def Ns540p892 := nat_lit 134930377059720414824262883 

noncomputable def Ns540p893 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns540p894 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz117 884279719003555 140737488355328 1 500000000000000 422011 2097152 5 8388608 373175768496409249105 295147905179352825856 Ns540p892 

noncomputable def Ns540p895 := @Enclosure.Real.IsNear.subLit_ff_p qz125 qz1 25587835 2097152 5 8388608 12 1 0 1 422011 422011 2097152 5 

noncomputable def Ns540p896 := @Ns540p895 8388608 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 818810720 67108864 40 67108864 25587835 2097152 5 8388608 (Ns540p883 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns540p897 := @Enclosure.Real.IsNear.recentre' qz128 Bool.false 373175768496409249105 295147905179352825856 Ns540p892 Ns540p893 42425173 33554432 63 16777216 (@Ns540p894 Ns540p893 RS541to552.d55 (Ns540p896 rfl rfl) rfl) 

noncomputable def Ns540p898 := nat_lit 104058995823272491340752489678589229860314217257020154893571543588207346517530219638428627988323601 

noncomputable def Ns540p899 := nat_lit 34000355922248362044489730754443266463925465292418605243055718939202835375736689867787803921 

noncomputable def Ns540p900 := nat_lit 630651829185991553044737243955665024170030737626086940571922101432222945616145857756030118724836625 

noncomputable def Ns540p901 := BSN.cos_dyadic_bound_f 42425173 33554432 4 3 33554432 9610000 Ns540p898 Ns540p354 Ns540p899 Ns540p900 Ns540p357 Ns540p899 10121849 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 42425173) qz595 0 3 Ns540p898 Ns540p354 Ns540p899 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 42425173) (BSN.cosOddQ 33554432) 0 3 Ns540p900 Ns540p357 Ns540p899 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p902 := @Enclosure.Real.IsNear.inv_image qz126 10121849 33554432 38887951 10076815360000 111233185 111236032 33554432 (Ns540p890 (@Ns540p891 9610000 (Ns540p897 rfl) (Enclosure.sfrac_false_div 42425173 33554432) (Ns540p901 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns540p903 := @Enclosure.Real.IsNear.recentre' qz127 Bool.false 5615896 33554432 

noncomputable abbrev qz129 := (@HMul.hMul Real Real Real qz355 qz352 qz452)

noncomputable def Ns540p904 := @Enclosure.Real.IsNear.cos_image qz129 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 94129455)) qz374) Bool.true 94129455 67108864 

noncomputable def Ns540p905 := nat_lit 868190988327569145650184725 

noncomputable def Ns540p906 := nat_lit 618970019642690137449562112 

noncomputable def Ns540p907 := nat_lit 63496621675568712783819775890319 

noncomputable def Ns540p908 := @Enclosure.Real.IsNear.recentre' qz129 Bool.true Ns540p905 Ns540p906 Ns540p907 

noncomputable def Ns540p909 := nat_lit 12089258196146291747061760000000000000 

noncomputable abbrev qz130 := qz452

noncomputable def Ns540p910 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz130 884279719003555 140737488355328 1 500000000000000 981805835495 

noncomputable abbrev qz453 := (@HSub.hSub Real Real Real qz582 qz640 qz635)

noncomputable abbrev qz131 := qz453

noncomputable def Ns540p911 := @Enclosure.Real.IsNear.subLit_tf qz131 qz30 706927928551 4398046511104 58823505 70368744177664 1 16 

noncomputable abbrev qz454 := qz640

noncomputable abbrev qz132 := qz454

noncomputable def Ns540p912 := @Enclosure.Real.IsNear.subLit_ff_n qz132 qz117 178093284121 4398046511104 16880465 70368744177664 422011 2097152 5 8388608 

noncomputable def Ns540p913 := @Enclosure.Real.IsNear.mulLit_ff qz117 qz117 422011 2097152 5 8388608 422011 2097152 5 8388608 178093284121 4398046511104 

noncomputable def Ns540p914 := nat_lit 646050943389769866205922988635204956148435599972897319179218022968802027149822921571822065634971890625 

noncomputable def Ns540p915 := nat_lit 483845303738662230802257133277034425607202419339736182280090647410139103961344172392402587890625 

noncomputable def Ns540p916 := nat_lit 3913367079663727440215458171596081286121420739107479638223105786422133427992381356719937201956917490625 

noncomputable def Ns540p917 := BSN.cos_dyadic_bound_f 94129455 67108864 4 3 33554432 9610000 Ns540p914 Ns540p219 Ns540p915 Ns540p916 Ns540p222 Ns540p915 5615896 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 94129455) qz596 0 3 Ns540p914 Ns540p219 Ns540p915 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 94129455) (BSN.cosOddQ 67108864) 0 3 Ns540p916 Ns540p222 Ns540p915 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p918 := @Ns540p903 1734524432 322458091520000 701987 4194304 108407777 20153630720000 (@Ns540p904 177 33554432 Bool.false 5615896 33554432 1 9610000 (@Ns540p908 Ns540p909 94129455 67108864 177 33554432 (@Ns540p910 4398046511104 58823505 70368744177664 Ns540p905 Ns540p906 Ns540p907 Ns540p909 RS541to552.d55 (@Ns540p911 0 1 15708893367920 981805835495 4398046511104 58823505 70368744177664 (@Ns540p912 1482535319216586752 706927928551 4398046511104 58823505 70368744177664 (@Ns540p913 16880465 70368744177664 (Ns540p896 rfl rfl) (Ns540p896 rfl rfl) rfl) (Ns540p896 rfl rfl) rfl rfl) qz389 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 94129455 67108864) (BSN.cos_neg_of_bound 94129455 67108864 Bool.false 5615896 33554432 1 9610000 (Ns540p917 rfl rfl)) rfl rfl) 

noncomputable def Ns540p919 := @Ns540p881 81075253305253698149079 Ns540p789 (Ns540p882 qz32 (@Enclosure.Real.IsNear.of_eq qz116 (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 19212243 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz124 (BSN.t_div_two_pi_nonneg qz115 935378 1000 qz118)) Ns540p886) rfl) (@Ns540p887 281474976710656 4215096029373341 169060907886837760000 (BSN.correction_mk qz117 (BSN.cos_two_pi_p_ne_zero_mk qz115 935378 1000 12 qz118 rfl rfl (@BSN.floor_sqrt_eq_dec qz115 935378 1000 12 qz118 rfl rfl rfl))) (@Ns540p888 67108864 701987 4194304 108407777 20153630720000 156170498234179 281474976710656 4215096029373341 169060907886837760000 (@Ns540p889 67108864 (Ns540p902 rfl rfl rfl rfl rfl) rfl) (Ns540p918 rfl) rfl)) 

noncomputable def Ns540p920 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz115) (hardyZApproximantRS₀ qz115) Bool.false 22284627352996282883783 18889465931478580854784 Ns540p788 Ns540p789 (@Eq.refl Real (hardyZApproximantRS₀ qz115)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz115) (@HSub.hSub Real Real Real qz33 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz115) qz115 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz116) (Zeta.RiemannSiegel.correction qz117))) Bool.false 22284627352996282883783 18889465931478580854784 Ns540p788 Ns540p789 (BSN.hardyZApproximantRS₀_eq qz115 12 (@BSN.floor_sqrt_eq_dec qz115 935378 1000 12 qz118 rfl rfl rfl)) (@Ns540p791 22284627352996282883783 18889465931478580854784 Ns540p788 Ns540p789 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz115) qz115 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz115) qz115 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz115) qz115 12)) Bool.false 359321645 268435456 268933 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz115) qz115 12) (Ns540p880 (Ns540p879 rfl rfl rfl rfl) rfl rfl)) (Ns540p919 rfl) rfl rfl)) 

theorem RS541to552.d64 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz115) Bool.false 22284627352996282883783 18889465931478580854784 Ns540p788 Ns540p789 := Ns540p920 

noncomputable def Ns540p921 := nat_lit 58557344387583600649830400 

noncomputable def Ns540p922 := nat_lit 39076093505298214454801888968704 

noncomputable abbrev qz746 := (Enclosure.sfrac Bool.false 936869 1000)

noncomputable abbrev qz641 := qz746

noncomputable abbrev qz455 := qz641

noncomputable abbrev qz133 := qz455

noncomputable abbrev qz747 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 936869 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz642 := qz747

noncomputable abbrev qz456 := qz642

noncomputable abbrev qz134 := (@HPow.hPow Real Real Real qz356 qz456 qz358)

noncomputable abbrev qz748 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 936869 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz643 := qz748

noncomputable abbrev qz457 := qz643

noncomputable abbrev qz135 := qz457

noncomputable def Ns540p923 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz133) qz133 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz134) (Zeta.RiemannSiegel.correction qz135)) 475462379 268435456 269363 268435456 11739029981259950592235 75557863725914323419136 507671172155334151217 Ns540p921 Ns540p922 

noncomputable def Ns540p924 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz133) qz133 Real.cos BSN.quadSignPos 11 12 936869 1000 288 536870912 268435456 9007199254740992 Bool.false 1006918159933 4461 1334074092 57 154981288 8 

noncomputable def Ns540p925 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz133) qz133 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 936869 1000 179 236 536870912 268435456 9007199254740992 Bool.false 1006918159933 4461 

noncomputable def Ns540p926 := Ns540p925 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 869179267 216886 Bool.true 277465504 Bool.true 147415876 28296951008113761 1 Bool.false 265277457 Bool.false Bool.false 516758772 Bool.false Bool.true 629482541 

noncomputable def Ns540p927 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz133) qz133 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 936869 1000 46 116 536870912 268435456 9007199254740992 Bool.false 1006918159933 4461 

noncomputable def Ns540p928 := Ns540p927 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 821387017 177121 Bool.true 202109768 Bool.true 412298986 28296951008113761 1 Bool.false 499275088 Bool.true Bool.false 386184471 Bool.false Bool.true 869179267 

noncomputable def Ns540p929 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz133) qz133 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 936869 1000 125 33 536870912 268435456 9007199254740992 Bool.false 1006918159933 4461 

noncomputable def Ns540p930 := Ns540p929 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 589226254 131609 Bool.false 288727048 Bool.false 339344783 28296951008113761 1 Bool.false 275009110 Bool.true Bool.false 317195845 Bool.true Bool.true 821387017 

noncomputable def Ns540p931 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz133) qz133 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 936869 1000 367 234 536870912 268435456 9007199254740992 Bool.false 1006918159933 4461 

noncomputable def Ns540p932 := Ns540p931 744261104 56 268435448 8 864060384 56 240095976 8 Bool.true 423553326 77668 Bool.false 146451342 Bool.false 71095606 28296951008113761 1 Bool.false 144641781 Bool.false Bool.false 532170338 Bool.true Bool.true 589226254 

noncomputable def Ns540p933 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz133) qz133 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 936869 1000 780 538 536870912 268435456 9007199254740992 Bool.false 1006918159933 4461 

noncomputable def Ns540p934 := Ns540p933 372130544 56 379625064 8 589812976 56 309962568 8 Bool.true 536870864 4528 Bool.false 495001210 Bool.false 637274106 28296951008113761 1 Bool.false 324387335 Bool.false Bool.false 201019990 Bool.true Bool.true 423553326 

noncomputable def Ns540p935 := nat_lit 205617539876879249064335826424379497705281366163407598875491 

noncomputable def Ns540p936 := nat_lit 109631627027332984474252201955665848709027775995969536000 

noncomputable def Ns540p937 := nat_lit 346446274059537721873009325767520000 

noncomputable def Ns540p938 := nat_lit 1947448904845802965621931725260400169280 

noncomputable abbrev qz644 := (@Eq.refl Real qz746)

noncomputable abbrev qz458 := qz644

noncomputable abbrev qz136 := qz458

noncomputable def Ns540p939 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz133 936869 1000 3510895092644 16000000 1873738 4000 2000 Ns540p937 Ns540p938 qz136 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns540p940 := nat_lit 65797612760601359700587464455801439265690037172290431640157120 

noncomputable abbrev qz645 := (@HSub.hSub Real Real Real qz721 qz722 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz723 (@Nat.cast Real Real.instNatCast 1873738))))

noncomputable abbrev qz459 := (@HSub.hSub Real Real Real qz582 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 936869 4000) (Real.log (Enclosure.sfrac Bool.false 3510895092644 16000000))) (@HMul.hMul Real Real Real qz579 qz583 qz645))

noncomputable abbrev qz646 := (Enclosure.sfrac Bool.false 936869 2000)

noncomputable abbrev qz137 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz459 qz646) (@HMul.hMul Real Real Real qz355 qz646 (Real.log Real.pi)))

noncomputable def Ns540p941 := @Enclosure.Real.IsNear.addLit_ft_p qz137 (Enclosure.sfrac Bool.true Ns540p937 Ns540p938) 33786570131775750825379 18014398509481984000 130805130365650081763 Ns540p543 Ns540p937 Ns540p938 0 1 Ns540p940 

noncomputable def Ns540p942 := nat_lit 2267378339999800940638247059456000 

noncomputable abbrev qz138 := (@HSub.hSub Real Real Real qz361 qz459 qz646)

noncomputable def Ns540p943 := @Enclosure.Real.IsNear.subLit_ff_p qz138 (@HMul.hMul Real Real Real qz5 qz646 (Real.log Real.pi)) 43446448520895311013283 18014398509481984000 11810877806109353 3844000000000000000000 35985851247309 67108864000 2810607 536870912000 Ns540p942 33786570131775750825379 18014398509481984000 

noncomputable def Ns540p944 := nat_lit 86892897041790622026566000 

noncomputable abbrev qz139 := qz459

noncomputable def Ns540p945 := @Enclosure.Real.IsNear.subLit_ff_p qz139 qz646 51885014279485249447331 18014398509481984000 11810877806109353 3844000000000000000000 936869 2000 0 1 Ns540p944 43446448520895311013283 18014398509481984000 11810877806109353 3844000000000000000000 

noncomputable def Ns540p946 := nat_lit 116834665487601316706747007362387673088 

noncomputable def Ns540p947 := nat_lit 118946625824949138727370752 

noncomputable def Ns540p948 := nat_lit 130769862969344212532408857048052654656739144170329233929731048062037277096902586959854807331633211349715061165769509521003996836341332211818246606689780367360 

noncomputable def Ns540p949 := nat_lit 2880826434304288140031043939107193627360217675924155048542457050976457857592229310725197560348921108286783217269943553917053660369157840487056132263842414592 

noncomputable def Ns540p950 := nat_lit 662629010987046913418806944763246852789798197036918410914594054196151394415698276834834184700330247373381827944139969992976922571160707544061281566720 

noncomputable def Ns540p951 := BSN.log_dyadic_bound 1413743092644 5608047092644 7 6 Ns540p948 268435456 76880000 Ns540p949 Ns540p950 138322316 7021790185288 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1413743092644) (BSN.artanhQ 5608047092644) 0 6 Ns540p949 Ns540p948 Ns540p950 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz460 := (Real.log (Enclosure.sfrac Bool.false 3510895092644 16000000))

noncomputable def Ns540p952 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 936869 4000) qz460 936869 4000 0 1 55388838902557799 4503599627370496 12500016337 961000000000000000 51892086113800422591331 18014398509481984000 11710877805628853 3844000000000000000000 (Enclosure.Real.IsNear.const Bool.false 936869 4000) (BSN.isNear_log_sfrac 3510895092644 16000000 55388838902557799 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3510895092644) qz364)) Bool.false Ns540p947 Ns540p114 1000001306960000 76880000000000000000000 55388838902557799 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3510895092644 16000000 17 7021790185288 4194304000000 138322316 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns540p951 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p953 := BSN.arctan_dyadic_bound_f 1000 1873738 1 0 33554432 9610000 0 1 1 0 1 1 17907 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1873738) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1873738) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns540p954 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1873738))) 884279719003555 562949953421312 1 2000000000000000 17907 33554432 1 9610000 29661422955467978571776 883979289396643 562949953421312 200000000961 1922000000000000000 qz15 (Ns540p953 rfl) rfl rfl 

noncomputable abbrev qz461 := (@HMul.hMul Real Real Real qz579 qz583 qz645)

noncomputable abbrev qz140 := qz461

noncomputable abbrev qz462 := qz645

noncomputable abbrev qz141 := qz462

noncomputable def Ns540p955 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 936869 4000) qz460) qz140 51892086113800422591331 18014398509481984000 11710877805628853 3844000000000000000000 883979289396643 2251799813685248 200000000961 7688000000000000000 Ns540p946 51885014279485249447331 18014398509481984000 11810877806109353 3844000000000000000000 (Ns540p952 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz141 1 4 0 1 883979289396643 562949953421312 200000000961 1922000000000000000 883979289396643 2251799813685248 200000000961 7688000000000000000 qz372 Ns540p954 rfl) 

noncomputable def Ns540p956 := @Ns540p941 Ns540p935 Ns540p936 130805130365650081763 Ns540p543 (@Ns540p943 130805130365650081763 Ns540p543 (Ns540p945 (Ns540p955 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 936869 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz646 (Real.log Real.pi) 936869 2000 0 1 38410761 33554432 3 268435456 35985851247309 67108864000 2810607 536870912000 (Enclosure.Real.IsNear.const Bool.false 936869 2000) RS541to552.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns540p937 Ns540p938) 

noncomputable def Ns540p957 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz133) Bool.false Ns540p935 Ns540p936 130805130365650081763 Ns540p543 125864769991 67108864 559 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz133) (@HAdd.hAdd Real Real Real qz373 qz137 (Enclosure.sfrac Bool.true Ns540p937 Ns540p938)) Bool.false Ns540p935 Ns540p936 130805130365650081763 Ns540p543 Ns540p939 (Ns540p956 rfl rfl)) 

noncomputable def Ns540p958 := BSN.cos_dyadic_bound_f 56634379 137438953472 1 0 67108864 19238770 0 1 1 0 1 1 67108858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 56634379) qz589 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 56634379) qz590 0 0 rfl) rfl rfl 

noncomputable def Ns540p959 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz133) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 125864769991) qz374) Bool.false 125864769991 67108864 559 67108864 Bool.true 67108858 67108864 1 9610000 (Ns540p957 rfl) (Enclosure.sfrac_false_div 125864769991 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 125864769991) qz374) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3985290152834993487872) qz375) 226375608064910080 72057594037927936 Bool.false 67108858 67108864 298 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q2 125864769991 67108864 226375608064910080 72057594037927936 298 3985290152834993487872 Ns540p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108858 67108864 3985290152834993487872 Ns540p114 56634379 137438953472 19238770 19220000 (Ns540p958 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns540p960 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz133) Bool.false Ns540p935 Ns540p936 130805130365650081763 Ns540p543 1006918159933 536870912 4461 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz133) (@HAdd.hAdd Real Real Real qz373 qz137 (Enclosure.sfrac Bool.true Ns540p937 Ns540p938)) Bool.false Ns540p935 Ns540p936 130805130365650081763 Ns540p543 Ns540p939 (Ns540p956 rfl rfl)) 

noncomputable def Ns540p961 := Ns540p934 77668 BSN.abs_quadSignPos (BSN.cos_quad_nat0 780 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 324387335 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 538 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 201019990 536870912) qz136 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz133) qz133 1) Bool.true 33554429 33554432 339943679 40307261440000 536870864 536870912 4528 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz133) qz133 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz133)) Bool.true 33554429 33554432 339943679 40307261440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz133) qz133) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz133)) Bool.true 67108858 67108864 5439098864 644916183040000 33554429 33554432 339943679 40307261440000 (Ns540p959 rfl rfl) rfl)) rfl) (Ns540p960 rfl) RS541to552.d7 

noncomputable def Ns540p962 := nat_lit 8383021877204642807408154395907895498827220977895493186562017684528800000 

noncomputable def Ns540p963 := nat_lit 3604541950654060530490182107934890624316091567769569329957216100000000 

noncomputable def Ns540p964 := nat_lit 25141856547712620301163482823507816715233030750550940421026138621386400000 

noncomputable def Ns540p965 := BSN.cos_dyadic_bound_f 495001210 536870912 3 2 536870912 268435456 Ns540p962 Ns540p160 Ns540p963 Ns540p964 Ns540p163 Ns540p963 324387335 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 495001210) qz19 0 2 Ns540p962 Ns540p160 Ns540p963 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 495001210) qz378 0 2 Ns540p964 Ns540p163 Ns540p963 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p966 := nat_lit 22745883223847369151098574528917425489182592939387225204320194458615776068251154608075916111517398284800419106816 

noncomputable def Ns540p967 := nat_lit 4486578478295445015591806794503166962960673780511265876738433552675110775423796827983994880616004086337536 

noncomputable def Ns540p968 := nat_lit 137883085037291455465054850987054610553930948525139283924103399856713471496078016083057603640473819129933211832320 

noncomputable def Ns540p969 := BSN.cos_dyadic_bound_f 637274106 536870912 4 3 536870912 268435456 Ns540p966 Ns540p153 Ns540p967 Ns540p968 Ns540p156 Ns540p967 201019990 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 637274106) qz19 0 3 Ns540p966 Ns540p153 Ns540p967 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 637274106) qz378 0 3 Ns540p968 Ns540p156 Ns540p967 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p970 := nat_lit 460016514125206544752425901729296 

noncomputable def Ns540p971 := BSN.sin_dyadic_bound_f 146451342 536870912 2 1 536870912 268435456 Ns540p970 Ns540p282 Ns540p970 Ns540p970 Ns540p283 Ns540p970 144641781 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 146451342) qz376 0 1 Ns540p970 Ns540p282 Ns540p970 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 146451342) qz377 0 1 Ns540p970 Ns540p283 Ns540p970 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p972 := nat_lit 25548831468313412013155912359696 

noncomputable def Ns540p973 := BSN.cos_dyadic_bound_f 71095606 536870912 2 1 536870912 268435456 Ns540p972 Ns540p136 Ns540p972 Ns540p972 Ns540p137 Ns540p972 532170338 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 71095606) qz19 0 1 Ns540p972 Ns540p136 Ns540p972 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 71095606) qz378 0 1 Ns540p972 Ns540p137 Ns540p972 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p974 := Ns540p932 131609 BSN.abs_quadSignPos (BSN.cos_quad_nat3 367 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 144641781 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 234 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 532170338 536870912) qz136 rfl rfl (Ns540p961 RS541to552.d9 RS541to552.d11 RS541to552.d13 RS541to552.d17 (Ns540p965 rfl rfl) (Ns540p969 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns540p960 rfl) RS541to552.d19 RS541to552.d21 RS541to552.d23 RS541to552.d25 RS541to552.d17 (Ns540p971 rfl rfl) (Ns540p973 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns540p975 := nat_lit 1745915334989385606271149066308071444291462298717781983578644728491540480 

noncomputable def Ns540p976 := nat_lit 48294732462015678534269653022806176149170565914991404153229390381056 

noncomputable def Ns540p977 := nat_lit 4572557209691071419611573022797197810763874030011280923289726203226750976 

noncomputable def Ns540p978 := BSN.sin_dyadic_bound_f 288727048 536870912 3 2 536870912 268435456 Ns540p975 Ns540p276 Ns540p976 Ns540p977 Ns540p279 Ns540p976 275009110 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 288727048) qz376 0 2 Ns540p975 Ns540p276 Ns540p976 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 288727048) qz377 0 2 Ns540p977 Ns540p279 Ns540p976 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p979 := nat_lit 3331569783515322545835923604740213764350855344252641751171382764755545985 

noncomputable def Ns540p980 := nat_lit 175844753307681045391404477797578433303596425860205017768721301434241 

noncomputable def Ns540p981 := nat_lit 8725255208177632326925356690879363779645939126448383302086757882728869761 

noncomputable def Ns540p982 := BSN.sin_dyadic_bound_f 339344783 536870912 3 2 536870912 268435456 Ns540p979 Ns540p276 Ns540p980 Ns540p981 Ns540p279 Ns540p980 317195845 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 339344783) qz376 0 2 Ns540p979 Ns540p276 Ns540p980 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 339344783) qz377 0 2 Ns540p981 Ns540p279 Ns540p980 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p983 := Ns540p930 177121 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 125 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 275009110 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 317195845 536870912) qz136 rfl rfl (Ns540p974 rfl rfl) (Ns540p960 rfl) RS541to552.d27 RS541to552.d29 RS541to552.d31 RS541to552.d33 RS541to552.d17 (Ns540p978 rfl rfl) (Ns540p982 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p984 := nat_lit 232885894595740257761507905228456817120580075600545985027359018693165056 

noncomputable def Ns540p985 := nat_lit 2784187173601297876459861419297985916432874153410910906763052056576 

noncomputable def Ns540p986 := nat_lit 698652115412873570688770795962531855389907361053331133260263529975382016 

noncomputable def Ns540p987 := BSN.cos_dyadic_bound_f 202109768 536870912 3 2 536870912 268435456 Ns540p984 Ns540p160 Ns540p985 Ns540p986 Ns540p163 Ns540p985 499275088 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 202109768) qz19 0 2 Ns540p984 Ns540p160 Ns540p985 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 202109768) qz378 0 2 Ns540p986 Ns540p163 Ns540p985 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p988 := nat_lit 4033924391006605887839344720878589624846142751774233151821339232832020736 

noncomputable def Ns540p989 := nat_lit 835022414991608922200863687036063669306686857450638257529837398221056 

noncomputable def Ns540p990 := nat_lit 12100103128189834445673632435261696747199814881607798178948958023699620096 

noncomputable def Ns540p991 := BSN.cos_dyadic_bound_f 412298986 536870912 3 2 536870912 268435456 Ns540p988 Ns540p160 Ns540p989 Ns540p990 Ns540p163 Ns540p989 386184471 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 412298986) qz19 0 2 Ns540p988 Ns540p160 Ns540p989 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 412298986) qz378 0 2 Ns540p990 Ns540p163 Ns540p989 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p992 := Ns540p928 216886 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 499275088 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 386184471 536870912) qz136 rfl rfl (Ns540p983 rfl) (Ns540p960 rfl) RS541to552.d35 RS541to552.d37 RS541to552.d39 RS541to552.d41 RS541to552.d17 (Ns540p987 rfl rfl) (Ns540p991 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p993 := nat_lit 1489043954881668518094322929927992927621401884764279333700807871399198720 

noncomputable def Ns540p994 := nat_lit 35129500603378779531472545963383899298323268048667681671883350081536 

noncomputable def Ns540p995 := nat_lit 3899820148355773981746842432356040760314331460520081364398456613954912256 

noncomputable def Ns540p996 := BSN.sin_dyadic_bound_f 277465504 536870912 3 2 536870912 268435456 Ns540p993 Ns540p276 Ns540p994 Ns540p995 Ns540p279 Ns540p994 265277457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 277465504) qz376 0 2 Ns540p993 Ns540p276 Ns540p994 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 277465504) qz377 0 2 Ns540p995 Ns540p279 Ns540p994 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p997 := nat_lit 472255506068018128260195038085376 

noncomputable def Ns540p998 := BSN.cos_dyadic_bound_f 147415876 536870912 2 1 536870912 268435456 Ns540p997 Ns540p136 Ns540p997 Ns540p997 Ns540p137 Ns540p997 516758772 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 147415876) qz19 0 1 Ns540p997 Ns540p136 Ns540p997 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 147415876) qz378 0 1 Ns540p997 Ns540p137 Ns540p997 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p999 := Ns540p926 252649 BSN.abs_quadSignPos qz613 (BSN.sfrac_eq_quadSignPos_mul Bool.false 265277457 536870912) BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 516758772 536870912) qz136 rfl rfl (Ns540p992 rfl) (Ns540p960 rfl) RS541to552.d43 RS541to552.d45 RS541to552.d47 RS541to552.d49 RS541to552.d17 (Ns540p996 rfl rfl) (Ns540p998 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1000 := nat_lit 12806790831174105336783071844721 

noncomputable def Ns540p1001 := BSN.cos_dyadic_bound_f 59821883 536870912 2 1 536870912 268435456 Ns540p1000 Ns540p136 Ns540p1000 Ns540p1000 Ns540p137 Ns540p1000 533541474 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 59821883) qz19 0 1 Ns540p1000 Ns540p136 Ns540p1000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 59821883) qz378 0 1 Ns540p1000 Ns540p137 Ns540p1000 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1002 := Ns540p924 Bool.true 629482541 252649 Bool.true 59821883 28296951008113761 1 Bool.false 533541474 Bool.false Bool.true 475462379 269363 BSN.abs_quadSignPos qz380 (BSN.sfrac_eq_quadSignPos_mul Bool.false 533541474 536870912) qz136 rfl (Ns540p999 rfl) (Ns540p960 rfl) RS541to552.d51 RS541to552.d53 RS541to552.d17 (Ns540p1001 rfl rfl) rfl 

noncomputable def Ns540p1003 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz133) qz133 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz133) qz133 12) 475462379 536870912 269363 536870912 475462379 536870912 269363 536870912 510523842070839296 475462379 268435456 269363 268435456 (Ns540p1002 rfl rfl rfl rfl) 

noncomputable def Ns540p1004 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz134) (Zeta.RiemannSiegel.correction qz135) 19204595 67108864 1 67108864 611261522633513 1125899906842624 52820423244029 1745144855606067200 11739029981259950592235 75557863725914323419136 

noncomputable def Ns540p1005 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz134 1 1 0 1 19204595 67108864 1 67108864 19204595 67108864 1 67108864 

noncomputable abbrev qz142 := qz456

noncomputable def Ns540p1006 := @Enclosure.Real.IsNear.sqrt_image qz142 10006423286383 67108864000 936869 67108864000 409731508 409731547 33554432 (@Enclosure.Real.IsNear.of_eq qz142 (@HMul.hMul Real Real Real qz5 qz133 qz3) Bool.false 10006423286383 67108864000 936869 67108864000 (BSN.t_div_two_pi_mk qz133 936869 1000 qz136) (@Enclosure.Real.IsNear.mulLit_ff qz133 qz3 936869 1000 0 1 10680707 67108864 1 67108864 10006423286383 67108864000 936869 67108864000 (Enclosure.Real.IsNear.const Bool.false 936869 1000) RS541to552.d56 rfl)) 

noncomputable abbrev qz749 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 936869 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz647 := qz749

noncomputable abbrev qz463 := qz647

noncomputable abbrev qz143 := qz463

noncomputable def Ns540p1007 := @Enclosure.Real.IsNear.sqrt_image qz143 819463055 67108864 39 67108864 117253179 117253185 33554432 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 819463055 67108864 39 67108864 819463055 67108864 39 67108864 (Ns540p1006 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns540p1008 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz143) 58626591 16777216 3 33554432 9602297 9602298 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz143) Bool.false 234506364 67108864 6 67108864 58626591 16777216 3 33554432 (Ns540p1007 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns540p1009 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 19204595 67108864 1 67108864 19204595 67108864 1 67108864 (Ns540p1008 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz144 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz457))

noncomputable abbrev qz648 := (@HMul.hMul Real Real Real qz717 qz748 qz748)

noncomputable abbrev qz464 := (@HSub.hSub Real Real Real qz582 (@HSub.hSub Real Real Real qz582 qz648 qz643) qz594)

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz464))

noncomputable def Ns540p1010 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz135) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz144) qz145) Bool.false 611261522633513 

noncomputable def Ns540p1011 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz144) qz145 276284761 67108864 4289 

noncomputable def Ns540p1012 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz144) Bool.false 276284761 67108864 4289 67108864 276284761 67108864 4289 

noncomputable def Ns540p1013 := @Enclosure.Real.IsNear.recentre' qz144 Bool.false 8150286 33554432 1215584432 322458091520000 4075143 16777216 75974027 20153630720000 

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz355 qz352 qz457)

noncomputable def Ns540p1014 := @Enclosure.Real.IsNear.cos_image qz146 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 88949087) qz374) Bool.false 88949087 67108864 123 33554432 Bool.false 8150286 33554432 1 

noncomputable def Ns540p1015 := nat_lit 1052456941074322788121006417 

noncomputable def Ns540p1016 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz135 884279719003555 140737488355328 1 500000000000000 14156687 67108864 39 67108864 12518471202381280022285 9444732965739290427392 Ns540p1015 

noncomputable def Ns540p1017 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz1 819463055 67108864 39 67108864 12 1 0 1 14156687 14156687 67108864 39 

noncomputable def Ns540p1018 := @Ns540p1017 67108864 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 819463055 67108864 39 67108864 819463055 67108864 39 67108864 (Ns540p1006 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns540p1019 := @Enclosure.Real.IsNear.recentre' qz146 Bool.false 12518471202381280022285 9444732965739290427392 Ns540p1015 Ns540p333 88949087 67108864 123 33554432 (@Ns540p1016 Ns540p333 RS541to552.d55 (Ns540p1018 rfl rfl) rfl) 

noncomputable def Ns540p1020 := nat_lit 514906204070003785255853169959305484163910222985964915868225023727544606851264336817555639150445836161 

noncomputable def Ns540p1021 := nat_lit 245300219359671106743878504286654942946638946221353963182119944768605259687240173565931994462081 

noncomputable def Ns540p1022 := nat_lit 3119944262648231737936588209400101966042813438280022253105361212483506587219819962587860530827698091905 

noncomputable def Ns540p1023 := BSN.cos_dyadic_bound_f 88949087 67108864 4 3 33554432 9610000 Ns540p1020 Ns540p219 Ns540p1021 Ns540p1022 Ns540p222 Ns540p1021 8150286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 88949087) qz596 0 3 Ns540p1020 Ns540p219 Ns540p1021 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 88949087) (BSN.cosOddQ 67108864) 0 3 Ns540p1022 Ns540p222 Ns540p1021 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1024 := @Enclosure.Real.IsNear.inv_image qz144 4075143 16777216 75974027 20153630720000 138140236 138144525 33554432 (Ns540p1013 (@Ns540p1014 9610000 (Ns540p1019 rfl) (Enclosure.sfrac_false_div 88949087 67108864) (Ns540p1023 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns540p1025 := @Enclosure.Real.IsNear.recentre' qz145 Bool.false 4424866 33554432 

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz355 qz352 qz464)

noncomputable def Ns540p1026 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 96538771)) qz374) Bool.true 96538771 67108864 

noncomputable def Ns540p1027 := nat_lit 911782916190127436754469646525 

noncomputable def Ns540p1028 := nat_lit 100427837759019981151483577830613461 

noncomputable def Ns540p1029 := @Enclosure.Real.IsNear.recentre' qz147 Bool.true Ns540p1027 Ns540p210 Ns540p1028 

noncomputable abbrev qz148 := qz464

noncomputable def Ns540p1030 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz148 884279719003555 140737488355328 1 500000000000000 1031102372468255 

noncomputable abbrev qz465 := (@HSub.hSub Real Real Real qz582 qz648 qz643)

noncomputable abbrev qz149 := qz465

noncomputable def Ns540p1031 := @Enclosure.Real.IsNear.subLit_tf qz149 qz30 749627395757599 4503599627370496 3721468803 4503599627370496 1 16 

noncomputable abbrev qz466 := qz648

noncomputable abbrev qz150 := qz466

noncomputable def Ns540p1032 := @Enclosure.Real.IsNear.subLit_ff_n qz150 qz135 200411786815969 4503599627370496 1104223107 4503599627370496 14156687 67108864 39 67108864 

noncomputable def Ns540p1033 := @Enclosure.Real.IsNear.mulLit_ff qz135 qz135 14156687 67108864 39 67108864 14156687 67108864 39 67108864 200411786815969 4503599627370496 

noncomputable def Ns540p1034 := nat_lit 714953687898218916833915643058983817123056221740931361176671439855628489730021234036562337223291087921 

noncomputable def Ns540p1035 := nat_lit 655271362182498202009716460142440271513624946163035890815039612189063655379029033927505196526641 

noncomputable def Ns540p1036 := nat_lit 4330030327444442637001909089515061076832019014571604394513567917871118189617331170909141411608910539825 

noncomputable def Ns540p1037 := BSN.cos_dyadic_bound_f 96538771 67108864 4 3 33554432 9610000 Ns540p1034 Ns540p219 Ns540p1035 Ns540p1036 Ns540p222 Ns540p1035 4424866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 96538771) qz596 0 3 Ns540p1034 Ns540p219 Ns540p1035 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 96538771) (BSN.cosOddQ 67108864) 0 3 Ns540p1036 Ns540p222 Ns540p1035 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1038 := @Ns540p1025 3420998864 644916183040000 2212433 16777216 213812429 40307261440000 (@Ns540p1026 349 67108864 Bool.false 4424866 33554432 1 9610000 (@Ns540p1029 Ns540p213 96538771 67108864 349 67108864 (@Ns540p1030 4503599627370496 3721468803 4503599627370496 Ns540p1027 Ns540p210 Ns540p1028 Ns540p213 RS541to552.d55 (@Ns540p1031 0 1 16497637959492080 1031102372468255 4503599627370496 3721468803 4503599627370496 (@Ns540p1032 50306642952570888257536 749627395757599 4503599627370496 3721468803 4503599627370496 (@Ns540p1033 1104223107 4503599627370496 (Ns540p1018 rfl rfl) (Ns540p1018 rfl rfl) rfl) (Ns540p1018 rfl rfl) rfl rfl) qz389 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 96538771 67108864) (BSN.cos_neg_of_bound 96538771 67108864 Bool.false 4424866 33554432 1 9610000 (Ns540p1037 rfl rfl)) rfl rfl) 

noncomputable def Ns540p1039 := @Ns540p1004 507671172155334151217 Ns540p921 (Ns540p1005 qz32 (@Enclosure.Real.IsNear.of_eq qz134 (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 19204595 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz142 (BSN.t_div_two_pi_nonneg qz133 936869 1000 qz136)) Ns540p1009) rfl) (@Ns540p1010 1125899906842624 52820423244029 1745144855606067200 (BSN.correction_mk qz135 (BSN.cos_two_pi_p_ne_zero_mk qz133 936869 1000 12 qz136 rfl rfl (@BSN.floor_sqrt_eq_dec qz133 936869 1000 12 qz136 rfl rfl rfl))) (@Ns540p1011 67108864 2212433 16777216 213812429 40307261440000 611261522633513 1125899906842624 52820423244029 1745144855606067200 (@Ns540p1012 67108864 (Ns540p1024 rfl rfl rfl rfl rfl) rfl) (Ns540p1038 rfl) rfl)) 

noncomputable def Ns540p1040 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz133) (hardyZApproximantRS₀ qz133) Bool.true 145569792037078047002859 75557863725914323419136 59267352889732469050417 Ns540p921 (@Eq.refl Real (hardyZApproximantRS₀ qz133)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz133) (@HSub.hSub Real Real Real qz33 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz133) qz133 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz134) (Zeta.RiemannSiegel.correction qz135))) Bool.true 145569792037078047002859 75557863725914323419136 59267352889732469050417 Ns540p921 (BSN.hardyZApproximantRS₀_eq qz133 12 (@BSN.floor_sqrt_eq_dec qz133 936869 1000 12 qz136 rfl rfl rfl)) (@Ns540p923 145569792037078047002859 75557863725914323419136 59267352889732469050417 Ns540p921 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz133) qz133 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz133) qz133 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz133) qz133 12)) Bool.true 475462379 268435456 269363 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz133) qz133 12) (Ns540p1003 (Ns540p1002 rfl rfl rfl rfl) rfl rfl)) (Ns540p1039 rfl) rfl rfl)) 

theorem RS541to552.d65 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz133) Bool.true 145569792037078047002859 75557863725914323419136 59267352889732469050417 Ns540p921 := Ns540p1040 

noncomputable def Ns540p1041 := nat_lit 9219675414305834484180791 

noncomputable def Ns540p1042 := nat_lit 9076388380075458100723712000 

noncomputable def Ns540p1043 := nat_lit 5067205247602017361865159475200 

noncomputable abbrev qz750 := (Enclosure.sfrac Bool.false 938124 1000)

noncomputable abbrev qz649 := qz750

noncomputable abbrev qz467 := qz649

noncomputable abbrev qz151 := qz467

noncomputable abbrev qz152 := qz356

noncomputable abbrev qz751 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 938124 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz650 := qz751

noncomputable abbrev qz468 := qz650

noncomputable abbrev qz153 := qz468

noncomputable abbrev qz154 := qz358

noncomputable abbrev qz752 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 938124 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz651 := qz752

noncomputable abbrev qz469 := qz651

noncomputable abbrev qz155 := qz469

noncomputable abbrev qz652 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz152 qz153 qz154))

noncomputable def Ns540p1044 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 12) (@HMul.hMul Real Real Real qz5 qz652 (Zeta.RiemannSiegel.correction qz155)) 577462705 268435456 269731 268435456 1440852130936330605735 9444732965739290427392 99481865260907315668791 Ns540p1042 Ns540p1043 

noncomputable def Ns540p1045 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.cos BSN.quadSignPos 11 12 938124 1000 288 536870912 268435456 9007199254740992 Bool.false 1008604390094 4468 1334074092 57 154981288 8 

noncomputable def Ns540p1046 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 938124 1000 179 236 536870912 268435456 9007199254740992 Bool.false 1008604390094 4468 

noncomputable def Ns540p1047 := Ns540p1046 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.false 218295946 217182 Bool.true 142654993 Bool.true 76822791 28296951008113761 1 Bool.false 140982221 Bool.false Bool.false 531383859 Bool.false Bool.false 423096695 

noncomputable def Ns540p1048 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 938124 1000 45 116 536870912 268435456 9007199254740992 Bool.false 1008604390094 4468 

noncomputable def Ns540p1049 := Ns540p1048 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.false 239960428 177363 Bool.true 760266017 Bool.true 206499389 28296951008113761 1 Bool.false 530460276 Bool.true Bool.false 497644663 Bool.false Bool.false 218295946 

noncomputable def Ns540p1050 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 938124 1000 125 33 536870912 268435456 9007199254740992 Bool.false 1008604390094 4468 

noncomputable def Ns540p1051 := Ns540p1050 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.false 654070549 131789 Bool.false 767718075 Bool.false 714473255 28296951008113761 1 Bool.false 531557309 Bool.true Bool.false 521484867 Bool.true Bool.false 239960428 

noncomputable def Ns540p1052 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 938124 1000 368 234 536870912 268435456 9007199254740992 Bool.false 1008604390094 4468 

noncomputable def Ns540p1053 := Ns540p1052 744261104 56 268435448 8 864060384 56 240095976 8 Bool.false 461984573 77775 Bool.false 55318961 Bool.false 672929985 28296951008113761 1 Bool.false 534023411 Bool.false Bool.false 167539003 Bool.true Bool.false 654070549 

noncomputable def Ns540p1054 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz151) qz151 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 938124 1000 782 539 536870912 268435456 9007199254740992 Bool.false 1008604390094 4468 

noncomputable def Ns540p1055 := Ns540p1054 372130544 56 379625064 8 589812976 56 309962568 8 Bool.false 536870880 4536 Bool.false 27577826 Bool.false 739974125 28296951008113761 1 Bool.false 536162762 Bool.true Bool.false 526955703 Bool.false Bool.false 461984573 

noncomputable def Ns540p1056 := nat_lit 35200810652903733472373473117628291847584913647004313 

noncomputable def Ns540p1057 := nat_lit 18737070256638536321649662388730547690237486694400 

noncomputable def Ns540p1058 := nat_lit 348772940708286475278491947499520000 

noncomputable def Ns540p1059 := nat_lit 1963153857618416972631203959446574202880 

noncomputable abbrev qz653 := (@Eq.refl Real qz750)

noncomputable abbrev qz470 := qz653

noncomputable abbrev qz156 := qz470

noncomputable def Ns540p1060 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz151 938124 1000 3520307557504 16000000 1876248 4000 2000 Ns540p1058 Ns540p1059 qz156 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns540p1061 := nat_lit 3321965270806126670657473825301118337713587857108907505745920 

noncomputable abbrev qz654 := (@HSub.hSub Real Real Real qz721 qz722 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz723 (@Nat.cast Real Real.instNatCast 1876248))))

noncomputable abbrev qz471 := (@HSub.hSub Real Real Real qz582 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 938124 4000) (Real.log (Enclosure.sfrac Bool.false 3520307557504 16000000))) (@HMul.hMul Real Real Real qz579 qz583 qz654))

noncomputable abbrev qz655 := (Enclosure.sfrac Bool.false 938124 2000)

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz471 qz655) (@HMul.hMul Real Real Real qz355 qz655 (Real.log Real.pi)))

noncomputable def Ns540p1062 := @Enclosure.Real.IsNear.addLit_ft_p qz157 (Enclosure.sfrac Bool.true Ns540p1058 Ns540p1059) 1692157531138632959009 900719925474099200 32744951020671686037 Ns540p413 Ns540p1058 Ns540p1059 0 1 Ns540p1061 

noncomputable def Ns540p1063 := nat_lit 141948462029697855490065694720000 

noncomputable abbrev qz158 := (@HSub.hSub Real Real Real qz361 qz471 qz655)

noncomputable def Ns540p1064 := @Enclosure.Real.IsNear.subLit_ff_p qz158 (@HMul.hMul Real Real Real qz5 qz655 (Real.log Real.pi)) 10878992269655842149541 4503599627370496000 184790083228317 60062500000000000000 9008514188091 16777216000 703593 134217728000 Ns540p1063 1692157531138632959009 900719925474099200 

noncomputable def Ns540p1065 := nat_lit 21757984539311684299082000 

noncomputable abbrev qz159 := qz471

noncomputable def Ns540p1066 := @Enclosure.Real.IsNear.subLit_ff_p qz159 qz655 12991459718069501744293 4503599627370496000 184790083228317 60062500000000000000 938124 2000 0 1 Ns540p1065 10878992269655842149541 4503599627370496000 184790083228317 60062500000000000000 

noncomputable def Ns540p1067 := nat_lit 29254166572648308537689841148482289664 

noncomputable def Ns540p1068 := nat_lit 118972519505193886017388544 

noncomputable def Ns540p1069 := nat_lit 133428099192860233276963346542781500314893579082451077235597398004321367026925138261246187048010551367511290278553389489903210464242918867343815806562766684160 

noncomputable def Ns540p1070 := nat_lit 2969875108533188028651590128106957036012817917548407578661104134706220992978433894832647389963675731507407053053042027990102086984835789470900069109755543552 

noncomputable def Ns540p1071 := nat_lit 717551324842519432950059700456427501550912571184840878000592570816832023302143019414611192032837968920027076921948032783103260377859807119006834360320 

noncomputable def Ns540p1072 := BSN.log_dyadic_bound 1423155557504 5617459557504 7 6 Ns540p1069 268435456 76880000 Ns540p1070 Ns540p1071 139041010 7040615115008 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1423155557504) (BSN.artanhQ 5617459557504) 0 6 Ns540p1070 Ns540p1069 Ns540p1071 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz472 := (Real.log (Enclosure.sfrac Bool.false 3520307557504 16000000))

noncomputable def Ns540p1073 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 938124 4000) qz472 938124 4000 0 1 55400896587033703 4503599627370496 12500016337 961000000000000000 12993227677453601398293 4503599627370496000 2931641331532947 961000000000000000000 (Enclosure.Real.IsNear.const Bool.false 938124 4000) (BSN.isNear_log_sfrac 3520307557504 16000000 55400896587033703 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3520307557504) qz364)) Bool.false Ns540p1068 Ns540p114 1000001306960000 76880000000000000000000 55400896587033703 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3520307557504 16000000 17 7040615115008 4194304000000 139041010 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns540p1072 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p1074 := BSN.arctan_dyadic_bound_f 1000 1876248 1 0 33554432 9610000 0 1 1 0 1 1 17883 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1876248) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1876248) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns540p1075 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1876248))) 884279719003555 562949953421312 1 2000000000000000 17883 33554432 1 9610000 29661436466266860683264 883979692049827 562949953421312 200000000961 1922000000000000000 qz15 (Ns540p1074 rfl) rfl rfl 

noncomputable abbrev qz473 := (@HMul.hMul Real Real Real qz579 qz583 qz654)

noncomputable abbrev qz160 := qz473

noncomputable abbrev qz474 := qz654

noncomputable abbrev qz161 := qz474

noncomputable def Ns540p1076 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 938124 4000) qz472) qz160 12993227677453601398293 4503599627370496000 2931641331532947 961000000000000000000 883979692049827 2251799813685248 200000000961 7688000000000000000 Ns540p1067 12991459718069501744293 4503599627370496000 184790083228317 60062500000000000000 (Ns540p1073 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz161 1 4 0 1 883979692049827 562949953421312 200000000961 1922000000000000000 883979692049827 2251799813685248 200000000961 7688000000000000000 qz372 Ns540p1075 rfl) 

noncomputable def Ns540p1077 := @Ns540p1062 Ns540p1056 Ns540p1057 32744951020671686037 Ns540p413 (@Ns540p1064 32744951020671686037 Ns540p413 (Ns540p1066 (Ns540p1076 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 938124 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz655 (Real.log Real.pi) 938124 2000 0 1 38410761 33554432 3 268435456 9008514188091 16777216000 703593 134217728000 (Enclosure.Real.IsNear.const Bool.false 938124 2000) RS541to552.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns540p1058 Ns540p1059) 

noncomputable def Ns540p1078 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz151) Bool.false Ns540p1056 Ns540p1057 32744951020671686037 Ns540p413 126075548761 67108864 35 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz151) (@HAdd.hAdd Real Real Real qz373 qz157 (Enclosure.sfrac Bool.true Ns540p1058 Ns540p1059)) Bool.false Ns540p1056 Ns540p1057 32744951020671686037 Ns540p413 Ns540p1060 (Ns540p1077 rfl rfl)) 

noncomputable def Ns540p1079 := nat_lit 15188597476555048659976192 

noncomputable def Ns540p1080 := nat_lit 14368198236056406428016015160127777494794205338549433293558784845571329600452657224285073031281006584299930375710619955652102769533451203774961 

noncomputable def Ns540p1081 := nat_lit 10224791626024072117922528750731155685907766643998486704850643122091014219423361108734308730356885589845208393048196735470851355381336561 

noncomputable def Ns540p1082 := nat_lit 71751795250987348086376285188105147027925689585403851409578437090873080440862744980110927564283147519769672203949394854007428981495316061620721 

noncomputable def Ns540p1083 := BSN.sin_dyadic_bound_f 215842952067 137438953472 4 3 67108864 19238770 Ns540p1080 Ns540p267 Ns540p1081 Ns540p1082 Ns540p270 Ns540p1081 67108860 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215842952067) (BSN.sinEvenQ 137438953472) 0 3 Ns540p1080 Ns540p267 Ns540p1081 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215842952067) (BSN.sinOddQ 137438953472) 0 3 Ns540p1082 Ns540p270 Ns540p1081 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1084 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz151) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 126075548761) qz374) Bool.false 126075548761 67108864 35 4194304 Bool.false 67108860 67108864 1 9610000 (Ns540p1078 rfl) (Enclosure.sfrac_false_div 126075548761 67108864) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 126075548761) qz374) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns540p1079) qz375) 226375608064910080 72057594037927936 Bool.false 67108860 67108864 298 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q3 126075548761 67108864 226375608064910080 72057594037927936 298 Ns540p1079 Ns540p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108860 67108864 Ns540p1079 Ns540p114 215842952067 137438953472 19238770 19220000 (Ns540p1083 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns540p1085 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz151) Bool.false Ns540p1056 Ns540p1057 32744951020671686037 Ns540p413 1008604390094 536870912 4468 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz151) (@HAdd.hAdd Real Real Real qz373 qz157 (Enclosure.sfrac Bool.true Ns540p1058 Ns540p1059)) Bool.false Ns540p1056 Ns540p1057 32744951020671686037 Ns540p413 Ns540p1060 (Ns540p1077 rfl rfl)) 

noncomputable def Ns540p1086 := Ns540p1055 77775 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 782 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536162762 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 539 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 526955703 536870912) qz156 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 1) Bool.false 16777215 16777216 21284019 2519203840000 536870880 536870912 4536 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz151)) Bool.false 16777215 16777216 21284019 2519203840000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz151) qz151) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz151)) Bool.false 67108860 67108864 340544304 40307261440000 16777215 16777216 21284019 2519203840000 (Ns540p1084 rfl rfl) rfl)) rfl) (Ns540p1085 rfl) RS541to552.d7 

noncomputable def Ns540p1087 := nat_lit 578415747885318666117757148176 

noncomputable def Ns540p1088 := BSN.cos_dyadic_bound_f 27577826 536870912 2 1 536870912 268435456 Ns540p1087 Ns540p136 Ns540p1087 Ns540p1087 Ns540p137 Ns540p1087 536162762 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 27577826) qz19 0 1 Ns540p1087 Ns540p136 Ns540p1087 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 27577826) qz378 0 1 Ns540p1087 Ns540p137 Ns540p1087 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1089 := nat_lit 107508377854807502549570311214844466805843245084612788360798744161282358802242590081540510144300378341617431640625 

noncomputable def Ns540p1090 := nat_lit 26952459738745615401750180588178668619087197171436213691222070318978202245025173775502480566501617431640625 

noncomputable def Ns540p1091 := nat_lit 537145671941638827246769904152021028552433004701990753056375674477721603974512918094619608711579625701617431640625 

noncomputable def Ns540p1092 := BSN.sin_dyadic_bound_f 739974125 536870912 4 3 536870912 268435456 Ns540p1089 Ns540p130 Ns540p1090 Ns540p1091 Ns540p133 Ns540p1090 526955703 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 739974125) qz376 0 3 Ns540p1089 Ns540p130 Ns540p1090 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 739974125) qz377 0 3 Ns540p1091 Ns540p133 Ns540p1090 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1093 := nat_lit 9364747205387516243481017269441 

noncomputable def Ns540p1094 := BSN.cos_dyadic_bound_f 55318961 536870912 2 1 536870912 268435456 Ns540p1093 Ns540p136 Ns540p1093 Ns540p1093 Ns540p137 Ns540p1093 534023411 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 55318961) qz19 0 1 Ns540p1093 Ns540p136 Ns540p1093 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 55318961) qz378 0 1 Ns540p1093 Ns540p137 Ns540p1093 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1095 := nat_lit 28287982978941422235043846115908765179756142630097084589248145247843485204305961394819316394138281381619336890625 

noncomputable def Ns540p1096 := nat_lit 8622606454535293955567281650977621356750300816790387132691704428219827696641364586773227683307480712890625 

noncomputable def Ns540p1097 := nat_lit 171445872612661806643182760645372554482670430626848501200407837995846030321102040706494035437883043644964898490625 

noncomputable def Ns540p1098 := BSN.cos_dyadic_bound_f 672929985 536870912 4 3 536870912 268435456 Ns540p1095 Ns540p153 Ns540p1096 Ns540p1097 Ns540p156 Ns540p1096 167539003 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 672929985) qz19 0 3 Ns540p1095 Ns540p153 Ns540p1096 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 672929985) qz378 0 3 Ns540p1097 Ns540p156 Ns540p1096 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1099 := Ns540p1053 131789 BSN.abs_quadSignPos (BSN.cos_quad_nat0 368 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 534023411 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 234 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 167539003 536870912) qz156 rfl rfl (Ns540p1086 RS541to552.d9 RS541to552.d11 RS541to552.d13 RS541to552.d17 (Ns540p1088 rfl rfl) (Ns540p1092 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns540p1085 rfl) RS541to552.d19 RS541to552.d21 RS541to552.d23 RS541to552.d25 RS541to552.d17 (Ns540p1094 rfl rfl) (Ns540p1098 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns540p1100 := nat_lit 124584892558675229157062397605464498741525923177224972090598498296759085077117776059244053785323881222291744140625 

noncomputable def Ns540p1101 := nat_lit 41919991704163955288337923601651465683693524720798212803665513094244539756755206863776392996311187744140625 

noncomputable def Ns540p1102 := nat_lit 622392557799021051659150373450462275169479950220932413938917930141857758113551558349247099012625020866707744140625 

noncomputable def Ns540p1103 := BSN.sin_dyadic_bound_f 767718075 536870912 4 3 536870912 268435456 Ns540p1100 Ns540p130 Ns540p1101 Ns540p1102 Ns540p133 Ns540p1101 531557309 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 767718075) qz376 0 3 Ns540p1100 Ns540p130 Ns540p1101 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 767718075) qz377 0 3 Ns540p1102 Ns540p133 Ns540p1101 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1104 := nat_lit 93422673172644862953090935434285529533941631622297430408772116794970150223590223464703304000425160719440305790625 

noncomputable def Ns540p1105 := nat_lit 17694231986169379631537688767667015857463617480615939021827000749302453647870033725777668953874707275390625 

noncomputable def Ns540p1106 := nat_lit 466814088724260958614385941875530654806378690679923036884539989383862412308307139375583321646733796583748427390625 

noncomputable def Ns540p1107 := BSN.sin_dyadic_bound_f 714473255 536870912 4 3 536870912 268435456 Ns540p1104 Ns540p130 Ns540p1105 Ns540p1106 Ns540p133 Ns540p1105 521484867 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 714473255) qz376 0 3 Ns540p1104 Ns540p130 Ns540p1105 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 714473255) qz377 0 3 Ns540p1106 Ns540p133 Ns540p1105 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1108 := Ns540p1051 177363 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 125 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 531557309 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 521484867 536870912) qz156 rfl rfl (Ns540p1099 rfl rfl) (Ns540p1085 rfl) RS541to552.d27 RS541to552.d29 RS541to552.d31 RS541to552.d33 RS541to552.d17 (Ns540p1103 rfl rfl) (Ns540p1107 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1109 := nat_lit 119811270654925644832513269674581986485435093602340781943827157391957772594831941343676714463790478063826227455361 

noncomputable def Ns540p1110 := nat_lit 37289532754337652456346752977988196988951947003471758518802061683497982521681951990019418528627952465765761 

noncomputable def Ns540p1111 := nat_lit 598564382469133649899552090071260089567127988921287422641042501558432837225292065950781015285632083369164247950721 

noncomputable def Ns540p1112 := BSN.sin_dyadic_bound_f 760266017 536870912 4 3 536870912 268435456 Ns540p1109 Ns540p130 Ns540p1110 Ns540p1111 Ns540p133 Ns540p1110 530460276 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 760266017) qz376 0 3 Ns540p1109 Ns540p130 Ns540p1110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 760266017) qz377 0 3 Ns540p1111 Ns540p133 Ns540p1110 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1113 := nat_lit 253787086920085048404691791635293668647563608603037337840491058428179361 

noncomputable def Ns540p1114 := nat_lit 3306360225448431064930758485767810517692785601034127122767091659681 

noncomputable def Ns540p1115 := nat_lit 761354648039804248351945513388909470321655440237909945267227641101218721 

noncomputable def Ns540p1116 := BSN.cos_dyadic_bound_f 206499389 536870912 3 2 536870912 268435456 Ns540p1113 Ns540p160 Ns540p1114 Ns540p1115 Ns540p163 Ns540p1114 497644663 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 206499389) qz19 0 2 Ns540p1113 Ns540p160 Ns540p1114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 206499389) qz378 0 2 Ns540p1115 Ns540p163 Ns540p1114 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1117 := Ns540p1049 217182 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 530460276 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 497644663 536870912) qz156 rfl rfl (Ns540p1108 rfl) (Ns540p1085 rfl) RS541to552.d35 RS541to552.d37 RS541to552.d39 RS541to552.d41 RS541to552.d17 (Ns540p1112 rfl rfl) (Ns540p1116 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1118 := nat_lit 414140694232516875138317627342401 

noncomputable def Ns540p1119 := BSN.sin_dyadic_bound_f 142654993 536870912 2 1 536870912 268435456 Ns540p1118 Ns540p282 Ns540p1118 Ns540p1118 Ns540p283 Ns540p1118 140982221 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 142654993) qz376 0 1 Ns540p1118 Ns540p282 Ns540p1118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 142654993) qz377 0 1 Ns540p1118 Ns540p283 Ns540p1118 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1120 := nat_lit 34830549392786980251124434961761 

noncomputable def Ns540p1121 := BSN.cos_dyadic_bound_f 76822791 536870912 2 1 536870912 268435456 Ns540p1120 Ns540p136 Ns540p1120 Ns540p1120 Ns540p137 Ns540p1120 531383859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 76822791) qz19 0 1 Ns540p1120 Ns540p136 Ns540p1120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 76822791) qz378 0 1 Ns540p1120 Ns540p137 Ns540p1120 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1122 := Ns540p1047 252994 BSN.abs_quadSignPos qz613 (BSN.sfrac_eq_quadSignPos_mul Bool.false 140982221 536870912) BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 531383859 536870912) qz156 rfl rfl (Ns540p1117 rfl) (Ns540p1085 rfl) RS541to552.d43 RS541to552.d45 RS541to552.d47 RS541to552.d49 RS541to552.d17 (Ns540p1119 rfl rfl) (Ns540p1121 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1123 := nat_lit 5244434701505268895980284989696 

noncomputable def Ns540p1124 := BSN.cos_dyadic_bound_f 47854708 536870912 2 1 536870912 268435456 Ns540p1123 Ns540p136 Ns540p1123 Ns540p1123 Ns540p137 Ns540p1123 534739527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 47854708) qz19 0 1 Ns540p1123 Ns540p136 Ns540p1123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 47854708) qz378 0 1 Ns540p1123 Ns540p137 Ns540p1123 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1125 := Ns540p1045 Bool.false 423096695 252994 Bool.true 47854708 28296951008113761 1 Bool.false 534739527 Bool.false Bool.false 577462705 269731 BSN.abs_quadSignPos qz380 (BSN.sfrac_eq_quadSignPos_mul Bool.false 534739527 536870912) qz156 rfl (Ns540p1122 rfl) (Ns540p1085 rfl) RS541to552.d51 RS541to552.d53 RS541to552.d17 (Ns540p1124 rfl rfl) rfl 

noncomputable def Ns540p1126 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 12) 577462705 536870912 269731 536870912 577462705 536870912 269731 536870912 620045858158673920 577462705 268435456 269731 268435456 (Ns540p1125 rfl rfl rfl rfl) 

noncomputable def Ns540p1127 := @Enclosure.Real.IsNear.mulLit_ff qz652 (Zeta.RiemannSiegel.correction qz155) 2399771 8388608 1 33554432 600412343901285 1125899906842624 51743273549137773 1352487263094702080000 1440852130936330605735 9444732965739290427392 

noncomputable abbrev qz656 := (@HPow.hPow Real Real Real qz152 qz153 qz154)

noncomputable def Ns540p1128 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz656 1 1 0 1 2399771 8388608 1 33554432 2399771 8388608 1 33554432 

noncomputable def Ns540p1129 := @Enclosure.Real.IsNear.sqrt_image qz153 2504956893417 16777216000 234531 16777216000 410005848 410005887 33554432 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz151 qz3) Bool.false 2504956893417 16777216000 234531 16777216000 (BSN.t_div_two_pi_mk qz151 938124 1000 qz156) (@Enclosure.Real.IsNear.mulLit_ff qz151 qz3 938124 1000 0 1 10680707 67108864 1 67108864 2504956893417 16777216000 234531 16777216000 (Enclosure.Real.IsNear.const Bool.false 938124 1000) RS541to552.d56 rfl)) 

noncomputable abbrev qz753 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 938124 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz657 := qz753

noncomputable abbrev qz475 := qz657

noncomputable abbrev qz162 := qz475

noncomputable def Ns540p1130 := @Enclosure.Real.IsNear.sqrt_image qz162 820011735 67108864 39 67108864 117292426 117292433 33554432 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 820011735 67108864 39 67108864 820011735 67108864 39 67108864 (Ns540p1129 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns540p1131 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz162) 234584859 67108864 7 67108864 9599083 9599085 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz162) Bool.false 234584859 67108864 7 67108864 234584859 67108864 7 67108864 (Ns540p1130 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns540p1132 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz162)) Bool.false 19198168 67108864 2 67108864 2399771 8388608 1 33554432 (Ns540p1131 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz163 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz469))

noncomputable abbrev qz658 := (@HMul.hMul Real Real Real qz717 qz752 qz752)

noncomputable abbrev qz476 := (@HSub.hSub Real Real Real qz582 (@HSub.hSub Real Real Real qz582 qz658 qz651) qz594)

noncomputable abbrev qz164 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz476))

noncomputable def Ns540p1133 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz155) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz163) qz164) Bool.false 600412343901285 

noncomputable def Ns540p1134 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz163) qz164 348135965 67108864 6809 

noncomputable def Ns540p1135 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz163) Bool.false 348135965 67108864 6809 67108864 348135965 67108864 6809 

noncomputable def Ns540p1136 := @Enclosure.Real.IsNear.recentre' qz163 Bool.false 6468162 33554432 1215584432 322458091520000 3234081 16777216 75974027 20153630720000 

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz355 qz352 qz469)

noncomputable def Ns540p1137 := @Enclosure.Real.IsNear.cos_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 92396545) qz374) Bool.false 92396545 67108864 123 33554432 Bool.false 6468162 33554432 1 

noncomputable def Ns540p1138 := nat_lit 1052456941079035913432944977 

noncomputable def Ns540p1139 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz155 884279719003555 140737488355328 1 500000000000000 14705367 67108864 39 67108864 13003657798604150579685 9444732965739290427392 Ns540p1138 

noncomputable def Ns540p1140 := @Enclosure.Real.IsNear.subLit_ff_p qz162 qz1 820011735 67108864 39 67108864 12 1 0 1 14705367 14705367 67108864 39 

noncomputable def Ns540p1141 := @Ns540p1140 67108864 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 820011735 67108864 39 67108864 820011735 67108864 39 67108864 (Ns540p1129 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns540p1142 := @Enclosure.Real.IsNear.recentre' qz165 Bool.false 13003657798604150579685 9444732965739290427392 Ns540p1138 Ns540p333 92396545 67108864 123 33554432 (@Ns540p1139 Ns540p333 RS541to552.d55 (Ns540p1141 rfl rfl) rfl) 

noncomputable def Ns540p1143 := nat_lit 599675017567459386424945429371364007045285598672348971902765187870509764668167081510817705011396890625 

noncomputable def Ns540p1144 := nat_lit 387140656780285433335129535520757759113215815912417346321733890368619602412669813720918212890625 

noncomputable def Ns540p1145 := nat_lit 3632849924752626552310191291248939022879835649996400199680830254858928904294347117557225717908062490625 

noncomputable def Ns540p1146 := BSN.cos_dyadic_bound_f 92396545 67108864 4 3 33554432 9610000 Ns540p1143 Ns540p219 Ns540p1144 Ns540p1145 Ns540p222 Ns540p1144 6468162 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 92396545) qz596 0 3 Ns540p1143 Ns540p219 Ns540p1144 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 92396545) (BSN.cosOddQ 67108864) 0 3 Ns540p1145 Ns540p222 Ns540p1144 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1147 := @Enclosure.Real.IsNear.inv_image qz163 3234081 16777216 75974027 20153630720000 174064578 174071387 33554432 (Ns540p1136 (@Ns540p1137 9610000 (Ns540p1142 rfl) (Enclosure.sfrac_false_div 92396545 67108864) (Ns540p1146 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns540p1148 := @Enclosure.Real.IsNear.recentre' qz164 Bool.false 3449298 33554432 

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz355 qz352 qz476)

noncomputable def Ns540p1149 := @Enclosure.Real.IsNear.cos_image qz166 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 98503553)) qz374) Bool.true 98503553 67108864 

noncomputable def Ns540p1150 := nat_lit 930339755750410284617941540525 

noncomputable def Ns540p1151 := nat_lit 101582761907924117534902167154064741 

noncomputable def Ns540p1152 := @Enclosure.Real.IsNear.recentre' qz166 Bool.true Ns540p1150 Ns540p210 Ns540p1151 

noncomputable abbrev qz167 := qz476

noncomputable def Ns540p1153 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz167 884279719003555 140737488355328 1 500000000000000 1052087632179055 

noncomputable abbrev qz477 := (@HSub.hSub Real Real Real qz582 qz658 qz651)

noncomputable abbrev qz168 := qz477

noncomputable def Ns540p1154 := @Enclosure.Real.IsNear.subLit_tf qz168 qz30 770612655468399 4503599627370496 3764265843 4503599627370496 1 16 

noncomputable abbrev qz478 := qz658

noncomputable abbrev qz169 := qz478

noncomputable def Ns540p1155 := @Enclosure.Real.IsNear.subLit_ff_n qz169 qz155 216247818604689 4503599627370496 1147020147 4503599627370496 14705367 67108864 39 67108864 

noncomputable def Ns540p1156 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz155 14705367 67108864 39 67108864 14705367 67108864 39 67108864 216247818604689 4503599627370496 

noncomputable def Ns540p1157 := nat_lit 775123967476884149706260677156527444503556777388497572461098957511147263485900271990120139969258129921 

noncomputable def Ns540p1158 := nat_lit 834493096331062675547334354919784009554251367135320939486225848566816075016717029675959543728641 

noncomputable def Ns540p1159 := nat_lit 4693776570985500538919962075611228068629267142895737667939867782623644612805431001135430725236001933825 

noncomputable def Ns540p1160 := BSN.cos_dyadic_bound_f 98503553 67108864 4 3 33554432 9610000 Ns540p1157 Ns540p219 Ns540p1158 Ns540p1159 Ns540p222 Ns540p1158 3449298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 98503553) qz596 0 3 Ns540p1157 Ns540p219 Ns540p1158 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 98503553) (BSN.cosOddQ 67108864) 0 3 Ns540p1159 Ns540p222 Ns540p1158 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1161 := @Ns540p1148 3459438864 644916183040000 1724649 16777216 216214929 40307261440000 (@Ns540p1149 353 67108864 Bool.false 3449298 33554432 1 9610000 (@Ns540p1152 Ns540p213 98503553 67108864 353 67108864 (@Ns540p1153 4503599627370496 3764265843 4503599627370496 Ns540p1150 Ns540p210 Ns540p1151 Ns540p213 RS541to552.d55 (@Ns540p1154 0 1 16833402114864880 1052087632179055 4503599627370496 3764265843 4503599627370496 (@Ns540p1155 51714939892507644788736 770612655468399 4503599627370496 3764265843 4503599627370496 (@Ns540p1156 1147020147 4503599627370496 (Ns540p1141 rfl rfl) (Ns540p1141 rfl rfl) rfl) (Ns540p1141 rfl rfl) rfl rfl) qz389 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 98503553 67108864) (BSN.cos_neg_of_bound 98503553 67108864 Bool.false 3449298 33554432 1 9610000 (Ns540p1160 rfl rfl)) rfl rfl) 

noncomputable def Ns540p1162 := @Ns540p1127 99481865260907315668791 Ns540p1042 (Ns540p1128 qz32 (@Enclosure.Real.IsNear.of_eq qz656 (@Inv.inv Real Real.instInv (Real.sqrt qz162)) Bool.false 2399771 8388608 1 33554432 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz151 938124 1000 qz156)) Ns540p1132) rfl) (@Ns540p1133 1125899906842624 51743273549137773 1352487263094702080000 (BSN.correction_mk qz155 (BSN.cos_two_pi_p_ne_zero_mk qz151 938124 1000 12 qz156 rfl rfl (@BSN.floor_sqrt_eq_dec qz151 938124 1000 12 qz156 rfl rfl rfl))) (@Ns540p1134 67108864 1724649 16777216 216214929 40307261440000 600412343901285 1125899906842624 51743273549137773 1352487263094702080000 (@Ns540p1135 67108864 (Ns540p1147 rfl rfl rfl rfl rfl) rfl) (Ns540p1161 rfl) rfl)) 

noncomputable def Ns540p1163 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz151) (hardyZApproximantRS₀ qz151) Bool.false 18876810549207096404825 9444732965739290427392 Ns540p1041 Ns540p1042 (@Eq.refl Real (hardyZApproximantRS₀ qz151)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz151) (@HSub.hSub Real Real Real qz33 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 12) (@HMul.hMul Real Real Real qz5 qz652 (Zeta.RiemannSiegel.correction qz155))) Bool.false 18876810549207096404825 9444732965739290427392 Ns540p1041 Ns540p1042 (BSN.hardyZApproximantRS₀_eq qz151 12 (@BSN.floor_sqrt_eq_dec qz151 938124 1000 12 qz156 rfl rfl rfl)) (@Ns540p1044 18876810549207096404825 9444732965739290427392 Ns540p1041 Ns540p1042 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz151) qz151 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz151) qz151 12)) Bool.false 577462705 268435456 269731 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz151) qz151 12) (Ns540p1126 (Ns540p1125 rfl rfl rfl rfl) rfl rfl)) (Ns540p1162 rfl) rfl rfl)) 

theorem RS541to552.d66 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz151) Bool.false 18876810549207096404825 9444732965739290427392 Ns540p1041 Ns540p1042 := Ns540p1163 

noncomputable def Ns540p1164 := nat_lit 92707755647903200809211203 

noncomputable def Ns540p1165 := nat_lit 1387477521933142692091203 

noncomputable def Ns540p1166 := nat_lit 17802189885979273355568678436864 

noncomputable abbrev qz754 := (Enclosure.sfrac Bool.false 939379 1000)

noncomputable abbrev qz659 := qz754

noncomputable abbrev qz479 := qz659

noncomputable abbrev qz170 := qz479

noncomputable abbrev qz755 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 939379 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz660 := qz755

noncomputable abbrev qz480 := qz660

noncomputable abbrev qz171 := qz480

noncomputable abbrev qz756 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 939379 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz661 := qz756

noncomputable abbrev qz481 := qz661

noncomputable abbrev qz172 := qz481

noncomputable abbrev qz662 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz152 qz171 qz154))

noncomputable def Ns540p1167 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HMul.hMul Real Real Real qz5 qz662 (Zeta.RiemannSiegel.correction qz172)) 77579591 268435456 270081 268435456 22644898133720959468827 151115727451828646838272 Ns540p1165 Ns540p228 Ns540p1166 

noncomputable def Ns540p1168 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos BSN.quadSignPos 11 12 939379 1000 288 536870912 268435456 9007199254740992 Bool.false 1010291070845 4473 1334074092 57 154981288 8 

noncomputable def Ns540p1169 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 939379 1000 179 236 536870912 268435456 9007199254740992 Bool.false 1010291070845 4473 

noncomputable def Ns540p1170 := Ns540p1169 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 396424751 217463 Bool.true 7393891 Bool.true 5779116 28296951008113761 1 Bool.false 7393657 Bool.false Bool.false 536839807 Bool.false Bool.true 232223386 

noncomputable def Ns540p1171 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 939379 1000 45 116 536870912 268435456 9007199254740992 Bool.false 1010291070845 4473 

noncomputable def Ns540p1172 := Ns540p1171 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 428589106 177592 Bool.true 474656820 Bool.true 249203 28296951008113761 1 Bool.false 415192143 Bool.true Bool.false 536870854 Bool.false Bool.true 396424751 

noncomputable def Ns540p1173 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 939379 1000 126 34 536870912 268435456 9007199254740992 Bool.false 1010291070845 4473 

noncomputable def Ns540p1174 := Ns540p1173 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 86689277 131958 Bool.false 403844835 Bool.false 246737460 28296951008113761 1 Bool.false 392009227 Bool.true Bool.false 481163551 Bool.true Bool.true 428589106 

noncomputable def Ns540p1175 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 939379 1000 368 235 536870912 268435456 9007199254740992 Bool.false 1010291070845 4473 

noncomputable def Ns540p1176 := Ns540p1175 744261104 56 268435448 8 864060384 56 240095976 8 Bool.true 277339324 77872 Bool.false 807952026 Bool.false 431900098 28296951008113761 1 Bool.false 35337264 Bool.false Bool.false 386798197 Bool.false Bool.true 86689277 

noncomputable def Ns540p1177 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 939379 1000 783 540 536870912 268435456 9007199254740992 Bool.false 1010291070845 4473 

noncomputable def Ns540p1178 := Ns540p1177 372130544 56 379625064 8 589812976 56 309962568 8 Bool.true 536870896 4536 Bool.false 403919887 Bool.false 843124735 28296951008113761 1 Bool.false 366877835 Bool.false Bool.false 190121 Bool.false Bool.true 277339324 

noncomputable def Ns540p1179 := nat_lit 209644931974932091238637037746014649198936487013378977914613 

noncomputable def Ns540p1180 := nat_lit 111405781040296570631320138700585907645533880556978176000 

noncomputable def Ns540p1181 := nat_lit 351112090958830593424263170991520000 

noncomputable def Ns540p1182 := nat_lit 1978964210996575634583652080433074396480 

noncomputable abbrev qz663 := (@Eq.refl Real qz754)

noncomputable abbrev qz482 := qz663

noncomputable abbrev qz173 := qz482

noncomputable def Ns540p1183 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz170 939379 1000 3529732622564 16000000 1878758 4000 2000 Ns540p1181 Ns540p1182 qz173 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns540p1184 := nat_lit 67086378231978269196363852078724687743659675844281272932676160 

noncomputable abbrev qz664 := (@HSub.hSub Real Real Real qz721 qz722 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz723 (@Nat.cast Real Real.instNatCast 1878758))))

noncomputable abbrev qz483 := (@HSub.hSub Real Real Real qz582 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 939379 4000) (Real.log (Enclosure.sfrac Bool.false 3529732622564 16000000))) (@HMul.hMul Real Real Real qz579 qz583 qz664))

noncomputable abbrev qz665 := (Enclosure.sfrac Bool.false 939379 2000)

noncomputable abbrev qz174 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz483 qz665) (@HMul.hMul Real Real Real qz355 qz665 (Real.log Real.pi)))

noncomputable def Ns540p1185 := @Enclosure.Real.IsNear.addLit_ft_p qz174 (Enclosure.sfrac Bool.true Ns540p1181 Ns540p1182) 33899746233039624355717 18014398509481984000 131154477799723406533 Ns540p543 Ns540p1181 Ns540p1182 0 1 Ns540p1184 

noncomputable def Ns540p1186 := nat_lit 2274973459587568457498899775488000 

noncomputable abbrev qz175 := (@HSub.hSub Real Real Real qz361 qz483 qz665)

noncomputable def Ns540p1187 := @Enclosure.Real.IsNear.subLit_ff_p qz175 (@HMul.hMul Real Real Real qz5 qz665 (Real.log Real.pi)) 43585504755621483003781 18014398509481984000 11842252847115223 3844000000000000000000 36082262257419 67108864000 2818137 536870912000 Ns540p1186 33899746233039624355717 18014398509481984000 

noncomputable def Ns540p1188 := nat_lit 87171009511242966007562000 

noncomputable abbrev qz176 := qz483

noncomputable def Ns540p1189 := @Enclosure.Real.IsNear.subLit_ff_p qz176 qz665 52046678584340821327749 18014398509481984000 11842252847115223 3844000000000000000000 939379 2000 0 1 Ns540p1188 43585504755621483003781 18014398509481984000 11842252847115223 3844000000000000000000 

noncomputable def Ns540p1190 := nat_lit 117198701139154648600653989044134346752 

noncomputable def Ns540p1191 := nat_lit 118998378561764698083033088 

noncomputable def Ns540p1192 := nat_lit 136139442596482043894079044193950523872054718837533583222418784042512540634563678045182827699037203664277884226520259672460710462306369172369956128976493608960 

noncomputable def Ns540p1193 := nat_lit 3061449252969752402045397286021292723783542620996616633154411654070647191467421702354722281819153140902283691327355810536633125875805888573739448579875930112 

noncomputable def Ns540p1194 := nat_lit 776700104407696611290460740986669381511892191519312951852285767522796497155403978372483866274619861633837672702599014599837990862338953436626597969920 

noncomputable def Ns540p1195 := BSN.log_dyadic_bound 1432580622564 5626884622564 7 6 Ns540p1192 268435456 76880000 Ns540p1193 Ns540p1194 139758743 7059465245128 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1432580622564) (BSN.artanhQ 5626884622564) 0 6 Ns540p1193 Ns540p1192 Ns540p1194 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz484 := (Real.log (Enclosure.sfrac Bool.false 3529732622564 16000000))

noncomputable def Ns540p1196 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 939379 4000) qz484 939379 4000 0 1 55412938148605031 4503599627370496 12500016337 961000000000000000 52053750425098445415749 18014398509481984000 11742252846634723 3844000000000000000000 (Enclosure.Real.IsNear.const Bool.false 939379 4000) (BSN.isNear_log_sfrac 3529732622564 16000000 55412938148605031 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3529732622564) qz364)) Bool.false Ns540p1191 Ns540p114 1000001306960000 76880000000000000000000 55412938148605031 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3529732622564 16000000 17 7059465245128 4194304000000 139758743 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns540p1195 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p1197 := BSN.arctan_dyadic_bound_f 1000 1878758 1 0 33554432 9610000 0 1 1 0 1 1 17859 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1878758) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1878758) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns540p1198 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1878758))) 884279719003555 562949953421312 1 2000000000000000 17859 33554432 1 9610000 29661449977065742794752 883980094703011 562949953421312 200000000961 1922000000000000000 qz15 (Ns540p1197 rfl) rfl rfl 

noncomputable abbrev qz485 := (@HMul.hMul Real Real Real qz579 qz583 qz664)

noncomputable abbrev qz177 := qz485

noncomputable abbrev qz486 := qz664

noncomputable abbrev qz178 := qz486

noncomputable def Ns540p1199 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 939379 4000) qz484) qz177 52053750425098445415749 18014398509481984000 11742252846634723 3844000000000000000000 883980094703011 2251799813685248 200000000961 7688000000000000000 Ns540p1190 52046678584340821327749 18014398509481984000 11842252847115223 3844000000000000000000 (Ns540p1196 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz178 1 4 0 1 883980094703011 562949953421312 200000000961 1922000000000000000 883980094703011 2251799813685248 200000000961 7688000000000000000 qz372 Ns540p1198 rfl) 

noncomputable def Ns540p1200 := @Ns540p1185 Ns540p1179 Ns540p1180 131154477799723406533 Ns540p543 (@Ns540p1187 131154477799723406533 Ns540p543 (Ns540p1189 (Ns540p1199 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 939379 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz665 (Real.log Real.pi) 939379 2000 0 1 38410761 33554432 3 268435456 36082262257419 67108864000 2818137 536870912000 (Enclosure.Real.IsNear.const Bool.false 939379 2000) RS541to552.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns540p1181 Ns540p1182) 

noncomputable def Ns540p1201 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns540p1179 Ns540p1180 131154477799723406533 Ns540p543 126286383855 67108864 35 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz373 qz174 (Enclosure.sfrac Bool.true Ns540p1181 Ns540p1182)) Bool.false Ns540p1179 Ns540p1180 131154477799723406533 Ns540p543 Ns540p1183 (Ns540p1200 rfl rfl)) 

noncomputable def Ns540p1202 := nat_lit 15189516912265093101649920 

noncomputable def Ns540p1203 := nat_lit 14371684636157554289196284385459210806618213906645027362813855717084581922496323016973279137114666530857224095129030966794599417126609971449856 

noncomputable def Ns540p1204 := nat_lit 10232221543605550717536891081277298874049728410667209295636475194617899202018632132906926133626573184304944108196880254615522933120045056 

noncomputable def Ns540p1205 := nat_lit 71769184036911156436996168266002570862932642677371009732032965854701750411906895212342375973499709628075022469239210422036257568916811413590016 

noncomputable def Ns540p1206 := BSN.sin_dyadic_bound_f 215856018034 137438953472 4 3 67108864 19238770 Ns540p1203 Ns540p267 Ns540p1204 Ns540p1205 Ns540p270 Ns540p1204 67108862 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215856018034) (BSN.sinEvenQ 137438953472) 0 3 Ns540p1203 Ns540p267 Ns540p1204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215856018034) (BSN.sinOddQ 137438953472) 0 3 Ns540p1205 Ns540p270 Ns540p1204 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1207 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz170) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 126286383855) qz374) Bool.false 126286383855 67108864 35 4194304 Bool.true 67108862 67108864 1 9610000 (Ns540p1201 rfl) (Enclosure.sfrac_false_div 126286383855 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 126286383855) qz374) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns540p1202) qz375) 226375608064910080 72057594037927936 Bool.false 67108862 67108864 299 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q1 126286383855 67108864 226375608064910080 72057594037927936 299 Ns540p1202 Ns540p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108862 67108864 Ns540p1202 Ns540p114 215856018034 137438953472 19238770 19220000 (Ns540p1206 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns540p1208 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns540p1179 Ns540p1180 131154477799723406533 Ns540p543 1010291070845 536870912 4473 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz373 qz174 (Enclosure.sfrac Bool.true Ns540p1181 Ns540p1182)) Bool.false Ns540p1179 Ns540p1180 131154477799723406533 Ns540p543 Ns540p1183 (Ns540p1200 rfl rfl)) 

noncomputable def Ns540p1209 := Ns540p1178 77872 BSN.abs_quadSignPos (BSN.cos_quad_nat3 783 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 366877835 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 540 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 190121 536870912) qz173 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) Bool.true 33554431 33554432 21284019 2519203840000 536870896 536870912 4536 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 33554431 33554432 21284019 2519203840000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz170) qz170) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 67108862 67108864 340544304 40307261440000 33554431 33554432 21284019 2519203840000 (Ns540p1207 rfl rfl) rfl)) rfl) (Ns540p1208 rfl) RS541to552.d7 

noncomputable def Ns540p1210 := nat_lit 6687876452879858824959980277380306391607619706708949476774723466793188225 

noncomputable def Ns540p1211 := nat_lit 708535948299252680355761016065089716024565883475173183768594867944321 

noncomputable def Ns540p1212 := nat_lit 17514719746959526703888896161017649451813059458521622158779126592767392641 

noncomputable def Ns540p1213 := BSN.sin_dyadic_bound_f 403919887 536870912 3 2 536870912 268435456 Ns540p1210 Ns540p276 Ns540p1211 Ns540p1212 Ns540p279 Ns540p1211 366877835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 403919887) qz376 0 2 Ns540p1210 Ns540p276 Ns540p1211 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 403919887) qz377 0 2 Ns540p1212 Ns540p279 Ns540p1211 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1214 := nat_lit 69859005745399864203907605459856169681009322200861163204063100143932993187569960235094141123554394777890436890625 

noncomputable def Ns540p1215 := nat_lit 129033348061446965324104341415063893995226435739735381568075648099977270994641296951858542833655918212890625 

noncomputable def Ns540p1216 := nat_lit 422791377250632316026120743119681640995750089303935382908972643147411588145345847532494102075598554625886238490625 

noncomputable def Ns540p1217 := BSN.cos_dyadic_bound_f 843124735 536870912 4 3 536870912 268435456 Ns540p1214 Ns540p153 Ns540p1215 Ns540p1216 Ns540p156 Ns540p1215 190121 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 843124735) qz19 0 3 Ns540p1214 Ns540p153 Ns540p1215 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 843124735) qz378 0 3 Ns540p1216 Ns540p156 Ns540p1215 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1218 := nat_lit 58877796329726895487401481773897447158517918391123806669057067687358922987548973085854570029097986087080390496256 

noncomputable def Ns540p1219 := nat_lit 77379673292769865178278615649323402122734245438702224658603222794022495964539276740703865244711167862706176 

noncomputable def Ns540p1220 := nat_lit 356466736925278659187232775565874326707778030276277390722979747349262974716465223960974806915310845883316079104000 

noncomputable def Ns540p1221 := BSN.cos_dyadic_bound_f 807952026 536870912 4 3 536870912 268435456 Ns540p1218 Ns540p153 Ns540p1219 Ns540p1220 Ns540p156 Ns540p1219 35337264 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 807952026) qz19 0 3 Ns540p1218 Ns540p153 Ns540p1219 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 807952026) qz378 0 3 Ns540p1220 Ns540p156 Ns540p1219 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1222 := nat_lit 8742882523702991376297534899670103486324310428164083905781389721046810880 

noncomputable def Ns540p1223 := nat_lit 1210783295830836649719505999931005660161600673444536863016156920217856 

noncomputable def Ns540p1224 := nat_lit 22896065341505060821441616965612287502637694244101309550696851682013675776 

noncomputable def Ns540p1225 := BSN.sin_dyadic_bound_f 431900098 536870912 3 2 536870912 268435456 Ns540p1222 Ns540p276 Ns540p1223 Ns540p1224 Ns540p279 Ns540p1223 386798197 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 431900098) qz376 0 2 Ns540p1222 Ns540p276 Ns540p1223 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 431900098) qz377 0 2 Ns540p1224 Ns540p279 Ns540p1223 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1226 := Ns540p1176 131958 BSN.abs_quadSignPos (BSN.cos_quad_nat0 368 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 35337264 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 235 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 386798197 536870912) qz173 rfl rfl (Ns540p1209 RS541to552.d9 RS541to552.d11 RS541to552.d13 RS541to552.d17 (Ns540p1213 rfl rfl) (Ns540p1217 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns540p1208 rfl) RS541to552.d19 RS541to552.d21 RS541to552.d23 RS541to552.d25 RS541to552.d17 (Ns540p1221 rfl rfl) (Ns540p1225 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns540p1227 := nat_lit 3713040347181082899675712823862301747165738252593392185303686756664190625 

noncomputable def Ns540p1228 := nat_lit 707483413441254930604817164520594406190989353071304254135200875390625 

noncomputable def Ns540p1229 := nat_lit 11137706074716366189165928837257864052684832779074033947402789868241790625 

noncomputable def Ns540p1230 := BSN.cos_dyadic_bound_f 403844835 536870912 3 2 536870912 268435456 Ns540p1227 Ns540p160 Ns540p1228 Ns540p1229 Ns540p163 Ns540p1228 392009227 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 403844835) qz19 0 2 Ns540p1227 Ns540p160 Ns540p1228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 403844835) qz378 0 2 Ns540p1229 Ns540p163 Ns540p1228 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1231 := nat_lit 517297845963803909282625641672523656146743759859135355833924071628800000 

noncomputable def Ns540p1232 := nat_lit 13736646339882634697594233205902846890253912946711166230553600000000 

noncomputable def Ns540p1233 := nat_lit 1551866064598731962578481736551159162746450771751512645169311107686400000 

noncomputable def Ns540p1234 := BSN.cos_dyadic_bound_f 246737460 536870912 3 2 536870912 268435456 Ns540p1231 Ns540p160 Ns540p1232 Ns540p1233 Ns540p163 Ns540p1232 481163551 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 246737460) qz19 0 2 Ns540p1231 Ns540p160 Ns540p1232 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 246737460) qz378 0 2 Ns540p1233 Ns540p163 Ns540p1232 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1235 := Ns540p1174 177592 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 126 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 392009227 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 481163551 536870912) qz173 rfl rfl (Ns540p1226 rfl rfl) (Ns540p1208 rfl) RS541to552.d27 RS541to552.d29 RS541to552.d31 RS541to552.d33 RS541to552.d17 (Ns540p1230 rfl rfl) (Ns540p1234 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1236 := nat_lit 12754631778499455777817186512180953383519491488487007891306750648688640000 

noncomputable def Ns540p1237 := nat_lit 2576545418921370665344971163435650467861312531600485107802137600000000 

noncomputable def Ns540p1238 := nat_lit 33400816441582225770348739483352172570364987963843381787057429190451200000 

noncomputable def Ns540p1239 := BSN.sin_dyadic_bound_f 474656820 536870912 3 2 536870912 268435456 Ns540p1236 Ns540p276 Ns540p1237 Ns540p1238 Ns540p279 Ns540p1237 415192143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 474656820) qz376 0 2 Ns540p1236 Ns540p276 Ns540p1237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 474656820) qz377 0 2 Ns540p1238 Ns540p279 Ns540p1237 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1240 := BSN.cos_dyadic_bound_f 249203 536870912 1 0 536870912 268435456 0 1 1 0 1 1 536870854 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 249203) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 249203) qz378 0 0 rfl) rfl rfl 

noncomputable def Ns540p1241 := Ns540p1172 217463 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 415192143 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536870854 536870912) qz173 rfl rfl (Ns540p1235 rfl) (Ns540p1208 rfl) RS541to552.d35 RS541to552.d37 RS541to552.d39 RS541to552.d41 RS541to552.d17 (Ns540p1239 rfl rfl) (Ns540p1240 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1242 := BSN.sin_dyadic_bound_f 7393891 536870912 1 0 536870912 268435456 0 1 1 0 1 1 7393657 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 7393891) qz376 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 7393891) qz377 0 0 rfl) rfl rfl 

noncomputable def Ns540p1243 := BSN.cos_dyadic_bound_f 5779116 536870912 1 0 536870912 268435456 0 1 1 0 1 1 536839807 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 5779116) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 5779116) qz378 0 0 rfl) rfl rfl 

noncomputable def Ns540p1244 := Ns540p1170 253322 BSN.abs_quadSignPos qz613 (BSN.sfrac_eq_quadSignPos_mul Bool.false 7393657 536870912) BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 536839807 536870912) qz173 rfl rfl (Ns540p1241 rfl) (Ns540p1208 rfl) RS541to552.d43 RS541to552.d45 RS541to552.d47 RS541to552.d49 RS541to552.d17 (Ns540p1242 rfl rfl) (Ns540p1243 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1245 := nat_lit 1576975517870359575325571540496 

noncomputable def Ns540p1246 := BSN.cos_dyadic_bound_f 35436942 536870912 2 1 536870912 268435456 Ns540p1245 Ns540p136 Ns540p1245 Ns540p1245 Ns540p137 Ns540p1245 535701803 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 35436942) qz19 0 1 Ns540p1245 Ns540p136 Ns540p1245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 35436942) qz378 0 1 Ns540p1245 Ns540p137 Ns540p1245 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1247 := Ns540p1168 Bool.true 232223386 253322 Bool.true 35436942 28296951008113761 1 Bool.false 535701803 Bool.false Bool.true 77579591 270081 BSN.abs_quadSignPos qz380 (BSN.sfrac_eq_quadSignPos_mul Bool.false 535701803 536870912) qz173 rfl (Ns540p1244 rfl) (Ns540p1208 rfl) RS541to552.d51 RS541to552.d53 RS541to552.d17 (Ns540p1246 rfl rfl) rfl 

noncomputable def Ns540p1248 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) 77579591 536870912 270081 536870912 77579591 536870912 270081 536870912 83300451545513984 77579591 268435456 270081 268435456 (Ns540p1247 rfl rfl rfl rfl) 

noncomputable def Ns540p1249 := @Enclosure.Real.IsNear.mulLit_ff qz662 (Zeta.RiemannSiegel.correction qz172) 19191753 67108864 1 67108864 1179928594001859 2251799813685248 9032322080366979 169060907886837760000 22644898133720959468827 151115727451828646838272 

noncomputable abbrev qz666 := (@HPow.hPow Real Real Real qz152 qz171 qz154)

noncomputable def Ns540p1250 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz666 1 1 0 1 19191753 67108864 1 67108864 19191753 67108864 1 67108864 

noncomputable def Ns540p1251 := @Enclosure.Real.IsNear.sqrt_image qz171 10033231860953 67108864000 939379 67108864000 410280004 410280044 33554432 (@Enclosure.Real.IsNear.of_eq qz171 (@HMul.hMul Real Real Real qz5 qz170 qz3) Bool.false 10033231860953 67108864000 939379 67108864000 (BSN.t_div_two_pi_mk qz170 939379 1000 qz173) (@Enclosure.Real.IsNear.mulLit_ff qz170 qz3 939379 1000 0 1 10680707 67108864 1 67108864 10033231860953 67108864000 939379 67108864000 (Enclosure.Real.IsNear.const Bool.false 939379 1000) RS541to552.d56 rfl)) 

noncomputable abbrev qz757 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 939379 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz667 := qz757

noncomputable abbrev qz487 := qz667

noncomputable abbrev qz179 := qz487

noncomputable def Ns540p1252 := @Enclosure.Real.IsNear.sqrt_image qz179 51285003 4194304 5 8388608 117331634 117331641 33554432 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 820560048 67108864 40 67108864 51285003 4194304 5 8388608 (Ns540p1251 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns540p1253 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz179) 234663275 67108864 7 67108864 9595876 9595877 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz179) Bool.false 234663275 67108864 7 67108864 234663275 67108864 7 67108864 (Ns540p1252 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns540p1254 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 19191753 67108864 1 67108864 19191753 67108864 1 67108864 (Ns540p1253 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz180 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz481))

noncomputable abbrev qz668 := (@HMul.hMul Real Real Real qz717 qz756 qz756)

noncomputable abbrev qz488 := (@HSub.hSub Real Real Real qz582 (@HSub.hSub Real Real Real qz582 qz668 qz661) qz594)

noncomputable abbrev qz181 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz488))

noncomputable def Ns540p1255 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz172) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz180) qz181) Bool.false 1179928594001859 

noncomputable def Ns540p1256 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz180) qz181 472064151 67108864 12815 

noncomputable def Ns540p1257 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz180) Bool.false 472064151 67108864 12815 67108864 472064151 67108864 12815 

noncomputable def Ns540p1258 := @Enclosure.Real.IsNear.recentre' qz180 Bool.false 4770114 33554432 622207216 161229045760000 2385057 16777216 38887951 10076815360000 

noncomputable abbrev qz182 := (@HMul.hMul Real Real Real qz355 qz352 qz481)

noncomputable def Ns540p1259 := @Enclosure.Real.IsNear.cos_image qz182 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47920849) qz384) Bool.false 47920849 33554432 63 16777216 Bool.false 4770114 33554432 1 

noncomputable def Ns540p1260 := nat_lit 26986075412319748292351431 

noncomputable def Ns540p1261 := nat_lit 7205759403792793600000000000000 

noncomputable def Ns540p1262 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz172 884279719003555 140737488355328 1 500000000000000 953355 4194304 5 8388608 843032491510634177025 590295810358705651712 Ns540p1260 

noncomputable def Ns540p1263 := @Enclosure.Real.IsNear.subLit_ff_p qz179 qz1 51285003 4194304 5 8388608 12 1 0 1 953355 953355 4194304 5 

noncomputable def Ns540p1264 := @Ns540p1263 8388608 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 820560048 67108864 40 67108864 51285003 4194304 5 8388608 (Ns540p1251 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns540p1265 := @Enclosure.Real.IsNear.recentre' qz182 Bool.false 843032491510634177025 590295810358705651712 Ns540p1260 Ns540p1261 47920849 33554432 63 16777216 (@Ns540p1262 Ns540p1261 RS541to552.d55 (Ns540p1264 rfl rfl) rfl) 

noncomputable def Ns540p1266 := nat_lit 169549816837392152006844186721417552405492855995466717414747281258900293729408322334056136869766081 

noncomputable def Ns540p1267 := nat_lit 146654044490790902473443799435594706836077026636531714232106764656892974822198977741982884801 

noncomputable def Ns540p1268 := nat_lit 1026907644846593562232973061433422927445576914465338565543364731980088338953120047315957233208091585 

noncomputable def Ns540p1269 := BSN.cos_dyadic_bound_f 47920849 33554432 4 3 33554432 9610000 Ns540p1266 Ns540p354 Ns540p1267 Ns540p1268 Ns540p357 Ns540p1267 4770114 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 47920849) qz595 0 3 Ns540p1266 Ns540p354 Ns540p1267 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 47920849) (BSN.cosOddQ 33554432) 0 3 Ns540p1268 Ns540p357 Ns540p1267 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1270 := @Enclosure.Real.IsNear.inv_image qz180 2385057 16777216 38887951 10076815360000 236025668 236038483 33554432 (Ns540p1258 (@Ns540p1259 9610000 (Ns540p1265 rfl) (Enclosure.sfrac_false_div 47920849 33554432) (Ns540p1269 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns540p1271 := @Enclosure.Real.IsNear.recentre' qz181 Bool.false 2499509 33554432 

noncomputable abbrev qz183 := (@HMul.hMul Real Real Real qz355 qz352 qz488)

noncomputable def Ns540p1272 := @Enclosure.Real.IsNear.cos_image qz183 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6275669)) (@Nat.cast Real Real.instNatCast 4194304)) Bool.true 6275669 4194304 

noncomputable def Ns540p1273 := nat_lit 3704501143579800964175740405 

noncomputable def Ns540p1274 := nat_lit 2475880078570760549798248448 

noncomputable def Ns540p1275 := nat_lit 1646424913552162495694952636442483 

noncomputable def Ns540p1276 := @Enclosure.Real.IsNear.recentre' qz183 Bool.true Ns540p1273 Ns540p1274 Ns540p1275 

noncomputable def Ns540p1277 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz184 := qz488

noncomputable def Ns540p1278 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz184 884279719003555 140737488355328 1 500000000000000 4189286561671 

noncomputable abbrev qz489 := (@HSub.hSub Real Real Real qz582 qz668 qz661)

noncomputable abbrev qz185 := qz489

noncomputable def Ns540p1279 := @Enclosure.Real.IsNear.subLit_tf qz185 qz30 3089774933895 17592186044416 61010165 70368744177664 1 16 

noncomputable abbrev qz490 := qz668

noncomputable abbrev qz186 := qz490

noncomputable def Ns540p1280 := @Enclosure.Real.IsNear.subLit_ff_n qz186 qz172 908885756025 17592186044416 19067125 70368744177664 953355 4194304 5 8388608 

noncomputable def Ns540p1281 := @Enclosure.Real.IsNear.mulLit_ff qz172 qz172 953355 4194304 5 8388608 953355 4194304 5 8388608 908885756025 17592186044416 

noncomputable def Ns540p1282 := nat_lit 2973988648927909380808618361248201881772874651280492898074977834706653161916973739860241 

noncomputable def Ns540p1283 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns540p1284 := nat_lit 3731817116472507673400486974644223301363082956747704937309457105452638069218009361 

noncomputable def Ns540p1285 := nat_lit 18006402616667920871731566609932559483134113383724615478063009987353385342836097324081425 

noncomputable def Ns540p1286 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns540p1287 := BSN.cos_dyadic_bound_f 6275669 4194304 4 3 33554432 9610000 Ns540p1282 Ns540p1283 Ns540p1284 Ns540p1285 Ns540p1286 Ns540p1284 2499509 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6275669) (BSN.cosEvenQ 4194304) 0 3 Ns540p1282 Ns540p1283 Ns540p1284 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6275669) (BSN.cosOddQ 4194304) 0 3 Ns540p1285 Ns540p1286 Ns540p1284 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1288 := @Ns540p1271 3593978864 644916183040000 2499509 33554432 224623679 40307261440000 (@Ns540p1272 367 67108864 Bool.false 2499509 33554432 1 9610000 (@Ns540p1276 Ns540p1277 6275669 4194304 367 67108864 (@Ns540p1278 17592186044416 61010165 70368744177664 Ns540p1273 Ns540p1274 Ns540p1275 Ns540p1277 RS541to552.d55 (@Ns540p1279 0 1 67028584986736 4189286561671 17592186044416 61010165 70368744177664 (@Ns540p1280 12959455364335534080 3089774933895 17592186044416 61010165 70368744177664 (@Ns540p1281 19067125 70368744177664 (Ns540p1264 rfl rfl) (Ns540p1264 rfl rfl) rfl) (Ns540p1264 rfl rfl) rfl rfl) qz389 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6275669 4194304) (BSN.cos_neg_of_bound 6275669 4194304 Bool.false 2499509 33554432 1 9610000 (Ns540p1287 rfl rfl)) rfl rfl) 

noncomputable def Ns540p1289 := @Ns540p1249 Ns540p1165 Ns540p228 (Ns540p1250 qz32 (@Enclosure.Real.IsNear.of_eq qz666 (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 19191753 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz171 (BSN.t_div_two_pi_nonneg qz170 939379 1000 qz173)) Ns540p1254) rfl) (@Ns540p1255 2251799813685248 9032322080366979 169060907886837760000 (BSN.correction_mk qz172 (BSN.cos_two_pi_p_ne_zero_mk qz170 939379 1000 12 qz173 rfl rfl (@BSN.floor_sqrt_eq_dec qz170 939379 1000 12 qz173 rfl rfl rfl))) (@Ns540p1256 67108864 2499509 33554432 224623679 40307261440000 1179928594001859 2251799813685248 9032322080366979 169060907886837760000 (@Ns540p1257 67108864 (Ns540p1270 rfl rfl rfl rfl rfl) rfl) (Ns540p1288 rfl) rfl)) 

noncomputable def Ns540p1290 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (hardyZApproximantRS₀ qz170) Bool.true 66318325273615395112219 151115727451828646838272 Ns540p1164 Ns540p228 (@Eq.refl Real (hardyZApproximantRS₀ qz170)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (@HSub.hSub Real Real Real qz33 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HMul.hMul Real Real Real qz5 qz662 (Zeta.RiemannSiegel.correction qz172))) Bool.true 66318325273615395112219 151115727451828646838272 Ns540p1164 Ns540p228 (BSN.hardyZApproximantRS₀_eq qz170 12 (@BSN.floor_sqrt_eq_dec qz170 939379 1000 12 qz173 rfl rfl rfl)) (@Ns540p1167 66318325273615395112219 151115727451828646838272 Ns540p1164 Ns540p228 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12)) Bool.true 77579591 268435456 270081 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (Ns540p1248 (Ns540p1247 rfl rfl rfl rfl) rfl rfl)) (Ns540p1289 rfl) rfl rfl)) 

theorem RS541to552.d67 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz170) Bool.true 66318325273615395112219 151115727451828646838272 Ns540p1164 Ns540p228 := Ns540p1290 

noncomputable def Ns540p1291 := nat_lit 1871073530638640758088403 

noncomputable def Ns540p1292 := nat_lit 1815277676015091620144742400 

noncomputable def Ns540p1293 := nat_lit 9680948216953506792231705509888 

noncomputable abbrev qz758 := (Enclosure.sfrac Bool.false 940634 1000)

noncomputable abbrev qz669 := qz758

noncomputable abbrev qz491 := qz669

noncomputable abbrev qz187 := qz491

noncomputable abbrev qz759 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 940634 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz670 := qz759

noncomputable abbrev qz492 := qz670

noncomputable abbrev qz188 := qz492

noncomputable abbrev qz760 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 940634 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz671 := qz760

noncomputable abbrev qz493 := qz671

noncomputable abbrev qz189 := qz493

noncomputable abbrev qz672 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz152 qz188 qz154))

noncomputable def Ns540p1294 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz187) qz187 12) (@HMul.hMul Real Real Real qz5 qz672 (Zeta.RiemannSiegel.correction qz189)) 552031859 268435456 270435 268435456 2781446191362220107453 18889465931478580854784 42274065663561973064403 Ns540p1292 Ns540p1293 

noncomputable def Ns540p1295 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz187) qz187 Real.cos BSN.quadSignPos 11 12 940634 1000 288 536870912 268435456 9007199254740992 Bool.false 1011978201320 4479 1334074092 57 154981288 8 

noncomputable def Ns540p1296 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz187) qz187 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 940634 1000 178 235 536870912 268435456 9007199254740992 Bool.false 1011978201320 4479 

noncomputable def Ns540p1297 := Ns540p1296 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.false 276718086 217747 Bool.true 714997923 Bool.true 777600574 28296951008113761 1 Bool.false 127098728 Bool.true Bool.false 532854138 Bool.false Bool.false 397187498 

noncomputable def Ns540p1298 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz187) qz187 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 940634 1000 45 115 536870912 268435456 9007199254740992 Bool.false 1011978201320 4479 

noncomputable def Ns540p1299 := Ns540p1298 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.false 176146879 177823 Bool.true 188597898 Bool.true 636864149 28296951008113761 1 Bool.false 184742764 Bool.true Bool.false 497662927 Bool.false Bool.false 276718086 

noncomputable def Ns540p1300 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz187) qz187 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 940634 1000 127 34 536870912 268435456 9007199254740992 Bool.false 1011978201320 4479 

noncomputable def Ns540p1301 := Ns540p1300 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.false 240695154 132128 Bool.false 40421320 Bool.false 622766246 28296951008113761 1 Bool.false 40383141 Bool.false Bool.false 214397455 Bool.true Bool.false 176146879 

noncomputable def Ns540p1302 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz187) qz187 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 940634 1000 369 236 536870912 268435456 9007199254740992 Bool.false 1011978201320 4479 

noncomputable def Ns540p1303 := Ns540p1302 744261104 56 268435448 8 864060384 56 240095976 8 Bool.false 276807317 77970 Bool.false 717719959 Bool.false 191319934 28296951008113761 1 Bool.false 522247033 Bool.true Bool.false 503140654 Bool.false Bool.false 240695154 

noncomputable def Ns540p1304 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz187) qz187 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 940634 1000 784 542 536870912 268435456 9007199254740992 Bool.false 1011978201320 4479 

noncomputable def Ns540p1305 := Ns540p1304 372130544 56 379625064 8 589812976 56 309962568 8 Bool.false 536870776 4536 Bool.false 780711673 Bool.false 103410212 28296951008113761 1 Bool.false 62461407 Bool.false Bool.false 526942407 Bool.true Bool.false 276807317 

noncomputable def Ns540p1306 := nat_lit 1653780980303259740107868023526268480334004496457009993999 

noncomputable def Ns540p1307 := nat_lit 877357735557310031270869994062177960978991737208832000 

noncomputable def Ns540p1308 := nat_lit 353463774978984167180867476843520000 

noncomputable def Ns540p1309 := nat_lit 1994880530122168309551102525033861550080 

noncomputable abbrev qz673 := (@Eq.refl Real qz758)

noncomputable abbrev qz494 := qz673

noncomputable abbrev qz190 := qz494

noncomputable def Ns540p1310 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz187 940634 1000 3539170287824 16000000 1881268 4000 2000 Ns540p1308 Ns540p1309 qz190 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns540p1311 := nat_lit 33869434476610759477409137121817978477240412087439564677099520 

noncomputable abbrev qz674 := (@HSub.hSub Real Real Real qz721 qz722 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz723 (@Nat.cast Real Real.instNatCast 1881268))))

noncomputable abbrev qz495 := (@HSub.hSub Real Real Real qz582 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 940634 4000) (Real.log (Enclosure.sfrac Bool.false 3539170287824 16000000))) (@HMul.hMul Real Real Real qz579 qz583 qz674))

noncomputable abbrev qz675 := (Enclosure.sfrac Bool.false 940634 2000)

noncomputable abbrev qz191 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz495 qz675) (@HMul.hMul Real Real Real qz355 qz675 (Real.log Real.pi)))

noncomputable def Ns540p1312 := @Enclosure.Real.IsNear.addLit_ft_p qz191 (Enclosure.sfrac Bool.true Ns540p1308 Ns540p1309) 16978178466785283970619 9007199254740992000 65664575758380034459 Ns540p805 Ns540p1308 Ns540p1309 0 1 Ns540p1311 

noncomputable def Ns540p1313 := nat_lit 569693134847611069592825233408000 

noncomputable abbrev qz192 := (@HSub.hSub Real Real Real qz361 qz495 qz675)

noncomputable def Ns540p1314 := @Enclosure.Real.IsNear.subLit_ff_p qz192 (@HMul.hMul Real Real Real qz5 qz675 (Real.log Real.pi)) 21827527761441787909691 9007199254740992000 5928970183809079 1922000000000000000000 18065233881237 33554432000 1410951 268435456000 Ns540p1313 16978178466785283970619 9007199254740992000 

noncomputable def Ns540p1315 := nat_lit 8731011104576715163876400 

noncomputable abbrev qz193 := qz495

noncomputable def Ns540p1316 := @Enclosure.Real.IsNear.subLit_ff_p qz193 qz675 5212753338666761408831 1801439850948198400 5928970183809079 1922000000000000000000 940634 2000 0 1 Ns540p1315 21827527761441787909691 9007199254740992000 5928970183809079 1922000000000000000000 

noncomputable def Ns540p1317 := nat_lit 11738076996796967809535983270481625088 

noncomputable def Ns540p1318 := nat_lit 119024203066719168962232320 

noncomputable def Ns540p1319 := nat_lit 138904931916493649016907705011272024405697018109660841245429736218555451939603152427992157676052491879968317910410439773750019406160837140074843717102217461760 

noncomputable def Ns540p1320 := nat_lit 3155615387300531299009691207303361632580120091690368617869832417551045840381960787058878038555351830138763100067393633792075283580747935624841024289764278272 

noncomputable def Ns540p1321 := nat_lit 840376137087901172685834473650547080843861389253614822859092868233908949352050839416971248519545378931000574656024870244059783802018569274210669035520 

noncomputable def Ns540p1322 := BSN.log_dyadic_bound 1442018287824 5636322287824 7 6 Ns540p1319 268435456 76880000 Ns540p1320 Ns540p1321 140475517 7078340575648 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1442018287824) (BSN.artanhQ 5636322287824) 0 6 Ns540p1320 Ns540p1319 Ns540p1321 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz496 := (Real.log (Enclosure.sfrac Bool.false 3539170287824 16000000))

noncomputable def Ns540p1323 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 940634 4000) qz496 940634 4000 0 1 55424963620826215 4503599627370496 12500016337 961000000000000000 5213460523051224592031 1801439850948198400 5878970183568829 1922000000000000000000 (Enclosure.Real.IsNear.const Bool.false 940634 4000) (BSN.isNear_log_sfrac 3539170287824 16000000 55424963620826215 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3539170287824) qz364)) Bool.false Ns540p1318 Ns540p114 1000001306960000 76880000000000000000000 55424963620826215 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3539170287824 16000000 17 7078340575648 4194304000000 140475517 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns540p1322 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p1324 := BSN.arctan_dyadic_bound_f 1000 1881268 1 0 33554432 9610000 0 1 1 0 1 1 17836 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1881268) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1881268) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns540p1325 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1881268))) 884279719003555 562949953421312 1 2000000000000000 17836 33554432 1 9610000 29661462924914671484928 883980480578979 562949953421312 200000000961 1922000000000000000 qz15 (Ns540p1324 rfl) rfl rfl 

noncomputable abbrev qz497 := (@HMul.hMul Real Real Real qz579 qz583 qz674)

noncomputable abbrev qz194 := qz497

noncomputable abbrev qz498 := qz674

noncomputable abbrev qz195 := qz498

noncomputable def Ns540p1326 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 940634 4000) qz496) qz194 5213460523051224592031 1801439850948198400 5878970183568829 1922000000000000000000 883980480578979 2251799813685248 200000000961 7688000000000000000 Ns540p1317 5212753338666761408831 1801439850948198400 5928970183809079 1922000000000000000000 (Ns540p1323 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz195 1 4 0 1 883980480578979 562949953421312 200000000961 1922000000000000000 883980480578979 2251799813685248 200000000961 7688000000000000000 qz372 Ns540p1325 rfl) 

noncomputable def Ns540p1327 := @Ns540p1312 Ns540p1306 Ns540p1307 65664575758380034459 Ns540p805 (@Ns540p1314 65664575758380034459 Ns540p805 (Ns540p1316 (Ns540p1326 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 940634 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz675 (Real.log Real.pi) 940634 2000 0 1 38410761 33554432 3 268435456 18065233881237 33554432000 1410951 268435456000 (Enclosure.Real.IsNear.const Bool.false 940634 2000) RS541to552.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns540p1308 Ns540p1309) 

noncomputable def Ns540p1328 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz187) Bool.false Ns540p1306 Ns540p1307 65664575758380034459 Ns540p805 126497275165 67108864 35 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz187) (@HAdd.hAdd Real Real Real qz373 qz191 (Enclosure.sfrac Bool.true Ns540p1308 Ns540p1309)) Bool.false Ns540p1306 Ns540p1307 65664575758380034459 Ns540p805 Ns540p1310 (Ns540p1327 rfl rfl)) 

noncomputable def Ns540p1329 := BSN.cos_dyadic_bound_f 95611097 137438953472 1 0 67108864 19238770 0 1 1 0 1 1 67108847 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 95611097) qz589 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 95611097) qz590 0 0 rfl) rfl rfl 

noncomputable def Ns540p1330 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz187) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 126497275165) qz374) Bool.false 126497275165 67108864 35 4194304 Bool.false 67108847 67108864 1 9610000 (Ns540p1328 rfl) (Enclosure.sfrac_false_div 126497275165 67108864) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 126497275165) qz374) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6728032842656126074880) qz375) 226375608064910080 72057594037927936 Bool.false 67108847 67108864 300 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q0 126497275165 67108864 226375608064910080 72057594037927936 300 6728032842656126074880 Ns540p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108847 67108864 6728032842656126074880 Ns540p114 95611097 137438953472 19238770 19220000 (Ns540p1329 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns540p1331 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz187) Bool.false Ns540p1306 Ns540p1307 65664575758380034459 Ns540p805 1011978201320 536870912 4479 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz187) (@HAdd.hAdd Real Real Real qz373 qz191 (Enclosure.sfrac Bool.true Ns540p1308 Ns540p1309)) Bool.false Ns540p1306 Ns540p1307 65664575758380034459 Ns540p805 Ns540p1310 (Ns540p1327 rfl rfl)) 

noncomputable def Ns540p1332 := Ns540p1305 77970 BSN.abs_quadSignPos (BSN.cos_quad_nat0 784 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 62461407 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 542 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 526942407 536870912) qz190 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz187) qz187 1) Bool.false 67108847 67108864 21284019 2519203840000 536870776 536870912 4536 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz187) qz187 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz187)) Bool.false 67108847 67108864 21284019 2519203840000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz187) qz187) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz187)) Bool.false 67108847 67108864 340544304 40307261440000 67108847 67108864 21284019 2519203840000 (Ns540p1330 rfl rfl) rfl)) rfl) (Ns540p1331 rfl) RS541to552.d7 

noncomputable def Ns540p1333 := nat_lit 51310034554813729610365552600048990624671800744005414796826196530139937759946650376620769775742255010098339642401 

noncomputable def Ns540p1334 := nat_lit 51272922738303141214524188810175623850714564300679552395002105091606212120692012134019951868394289934629921 

noncomputable def Ns540p1335 := nat_lit 310729707100937177466940764457949525256060767278706550610035047218081336538243731512286616128485482210709798648865 

noncomputable def Ns540p1336 := BSN.cos_dyadic_bound_f 780711673 536870912 4 3 536870912 268435456 Ns540p1333 Ns540p153 Ns540p1334 Ns540p1335 Ns540p156 Ns540p1334 62461407 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 780711673) qz19 0 3 Ns540p1333 Ns540p153 Ns540p1334 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 780711673) qz378 0 3 Ns540p1335 Ns540p156 Ns540p1334 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1337 := nat_lit 114354619686206684677175285883136 

noncomputable def Ns540p1338 := BSN.cos_dyadic_bound_f 103410212 536870912 2 1 536870912 268435456 Ns540p1337 Ns540p136 Ns540p1337 Ns540p1337 Ns540p137 Ns540p1337 526942407 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 103410212) qz19 0 1 Ns540p1337 Ns540p136 Ns540p1337 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 103410212) qz378 0 1 Ns540p1337 Ns540p137 Ns540p1337 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1339 := nat_lit 95134210276493996550448619864060567900283131656529192666098957079409256524900605059615424678005080353303420746081 

noncomputable def Ns540p1340 := nat_lit 18683588081869971304773659668131011660524755536132635820689097265972757034189768416926201713458781871946081 

noncomputable def Ns540p1341 := nat_lit 475360718495931526141616659152485165347466812849460310771938299788068754215301046326881243560639013955407185983841 

noncomputable def Ns540p1342 := BSN.sin_dyadic_bound_f 717719959 536870912 4 3 536870912 268435456 Ns540p1339 Ns540p130 Ns540p1340 Ns540p1341 Ns540p133 Ns540p1340 522247033 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 717719959) qz376 0 3 Ns540p1339 Ns540p130 Ns540p1340 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 717719959) qz377 0 3 Ns540p1341 Ns540p133 Ns540p1340 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1343 := nat_lit 186996654722707444193292287616370465950777136607663399985435403928862976 

noncomputable def Ns540p1344 := nat_lit 1795071612754287769724277013612921664662255358546065526827534909696 

noncomputable def Ns540p1345 := nat_lit 560986374024896824004337414295084172009002085312273107825252556716769536 

noncomputable def Ns540p1346 := BSN.cos_dyadic_bound_f 191319934 536870912 3 2 536870912 268435456 Ns540p1343 Ns540p160 Ns540p1344 Ns540p1345 Ns540p163 Ns540p1344 503140654 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 191319934) qz19 0 2 Ns540p1343 Ns540p160 Ns540p1344 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 191319934) qz378 0 2 Ns540p1345 Ns540p163 Ns540p1344 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1347 := Ns540p1303 132128 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 369 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 522247033 536870912) BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 503140654 536870912) qz190 rfl rfl (Ns540p1332 RS541to552.d9 RS541to552.d11 RS541to552.d13 RS541to552.d17 (Ns540p1336 rfl rfl) (Ns540p1338 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns540p1331 rfl) RS541to552.d19 RS541to552.d21 RS541to552.d23 RS541to552.d25 RS541to552.d17 (Ns540p1342 rfl rfl) (Ns540p1346 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns540p1348 := nat_lit 2669574018915708498022197760000 

noncomputable def Ns540p1349 := BSN.sin_dyadic_bound_f 40421320 536870912 2 1 536870912 268435456 Ns540p1348 Ns540p282 Ns540p1348 Ns540p1348 Ns540p283 Ns540p1348 40383141 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 40421320) qz376 0 1 Ns540p1348 Ns540p282 Ns540p1348 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 40421320) qz377 0 1 Ns540p1348 Ns540p283 Ns540p1348 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1350 := nat_lit 20742106143953489043306972126302583381168428933316355913933536024338453696092146234975502106547083761818656772096 

noncomputable def Ns540p1351 := nat_lit 3403304348944178600828991365239025648650445930086170663994242693148069342177829035189658093440941935497216 

noncomputable def Ns540p1352 := nat_lit 125745112642486255858096452193529012926275059651625846967628031188845737909929095715269778507033483631753692385280 

noncomputable def Ns540p1353 := BSN.cos_dyadic_bound_f 622766246 536870912 4 3 536870912 268435456 Ns540p1350 Ns540p153 Ns540p1351 Ns540p1352 Ns540p156 Ns540p1351 214397455 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 622766246) qz19 0 3 Ns540p1350 Ns540p153 Ns540p1351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 622766246) qz378 0 3 Ns540p1352 Ns540p156 Ns540p1351 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1354 := Ns540p1301 177823 BSN.abs_quadSignPos (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 40383141 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 214397455 536870912) qz190 rfl rfl (Ns540p1347 rfl rfl) (Ns540p1331 rfl) RS541to552.d27 RS541to552.d29 RS541to552.d31 RS541to552.d33 RS541to552.d17 (Ns540p1349 rfl rfl) (Ns540p1353 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1355 := nat_lit 1265165650323181666803721378707216 

noncomputable def Ns540p1356 := BSN.sin_dyadic_bound_f 188597898 536870912 2 1 536870912 268435456 Ns540p1355 Ns540p282 Ns540p1355 Ns540p1355 Ns540p283 Ns540p1355 184742764 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 188597898) qz376 0 1 Ns540p1355 Ns540p282 Ns540p1355 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 188597898) qz377 0 1 Ns540p1355 Ns540p283 Ns540p1355 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1357 := nat_lit 58956215650906167564738828478197910417382396663159065861662588281529689036394209932872233517169742888007033411601 

noncomputable def Ns540p1358 := nat_lit 4452066287220837345652106973307992585895719493803956962152932666848847025207956878953533801112796953565201 

noncomputable def Ns540p1359 := nat_lit 294661810710044637839201510845765877238868928806011456143544352543058847933094875184476055768404349399406571935761 

noncomputable def Ns540p1360 := BSN.sin_dyadic_bound_f 636864149 536870912 4 3 536870912 268435456 Ns540p1357 Ns540p130 Ns540p1358 Ns540p1359 Ns540p133 Ns540p1358 497662927 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 636864149) qz376 0 3 Ns540p1357 Ns540p130 Ns540p1358 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 636864149) qz377 0 3 Ns540p1359 Ns540p133 Ns540p1358 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1361 := Ns540p1299 217747 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 184742764 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 497662927 536870912) qz190 rfl rfl (Ns540p1354 rfl) (Ns540p1331 rfl) RS541to552.d35 RS541to552.d37 RS541to552.d39 RS541to552.d41 RS541to552.d17 (Ns540p1356 rfl rfl) (Ns540p1360 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1362 := nat_lit 36067540168847437468167835115634405533797684374887347923037064948069345885359353086387368948633112419435998412401 

noncomputable def Ns540p1363 := nat_lit 17850786782989982217985954412302719831267589137212805893073720235543146367114156753043473468491345378999921 

noncomputable def Ns540p1364 := nat_lit 218537011062007396281635080402194584954594929289147145849476517938091017776499697424534876075599079860848921738865 

noncomputable def Ns540p1365 := BSN.cos_dyadic_bound_f 714997923 536870912 4 3 536870912 268435456 Ns540p1362 Ns540p153 Ns540p1363 Ns540p1364 Ns540p156 Ns540p1363 127098728 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 714997923) qz19 0 3 Ns540p1362 Ns540p153 Ns540p1363 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 714997923) qz378 0 3 Ns540p1364 Ns540p156 Ns540p1363 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1366 := nat_lit 131134240027452513457809814472905167514405729966122191241474952789393483682321728302872073804780001259773852389376 

noncomputable def Ns540p1367 := nat_lit 48874110906693213502911748558106557531943144266470786869744827970556646189172251162379275994270197552254976 

noncomputable def Ns540p1368 := nat_lit 655081977112061128088104183672009283536342637568650394591114995981274360556769925011942357791952834196622281281536 

noncomputable def Ns540p1369 := BSN.sin_dyadic_bound_f 777600574 536870912 4 3 536870912 268435456 Ns540p1366 Ns540p130 Ns540p1367 Ns540p1368 Ns540p133 Ns540p1367 532854138 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 777600574) qz376 0 3 Ns540p1366 Ns540p130 Ns540p1367 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 777600574) qz377 0 3 Ns540p1368 Ns540p133 Ns540p1367 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1370 := Ns540p1297 253654 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 178 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127098728 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 235 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 532854138 536870912) qz190 rfl rfl (Ns540p1361 rfl) (Ns540p1331 rfl) RS541to552.d43 RS541to552.d45 RS541to552.d47 RS541to552.d49 RS541to552.d17 (Ns540p1365 rfl rfl) (Ns540p1369 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1371 := nat_lit 259468151049097261555856732416 

noncomputable def Ns540p1372 := BSN.cos_dyadic_bound_f 22569452 536870912 2 1 536870912 268435456 Ns540p1371 Ns540p136 Ns540p1371 Ns540p1371 Ns540p137 Ns540p1371 536396584 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 22569452) qz19 0 1 Ns540p1371 Ns540p136 Ns540p1371 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 22569452) qz378 0 1 Ns540p1371 Ns540p137 Ns540p1371 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1373 := Ns540p1295 Bool.false 397187498 253654 Bool.true 22569452 28296951008113761 1 Bool.false 536396584 Bool.false Bool.false 552031859 270435 BSN.abs_quadSignPos qz380 (BSN.sfrac_eq_quadSignPos_mul Bool.false 536396584 536870912) qz190 rfl (Ns540p1370 rfl) (Ns540p1331 rfl) RS541to552.d51 RS541to552.d53 RS541to552.d17 (Ns540p1372 rfl rfl) rfl 

noncomputable def Ns540p1374 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz187) qz187 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz187) qz187 12) 552031859 536870912 270435 536870912 552031859 536870912 270435 536870912 592739695188770816 552031859 268435456 270435 268435456 (Ns540p1373 rfl rfl rfl rfl) 

noncomputable def Ns540p1375 := @Enclosure.Real.IsNear.mulLit_ff qz672 (Zeta.RiemannSiegel.correction qz189) 4796337 16777216 1 33554432 579910500734669 1125899906842624 110100157057342379 1352487263094702080000 2781446191362220107453 18889465931478580854784 

noncomputable abbrev qz676 := (@HPow.hPow Real Real Real qz152 qz188 qz154)

noncomputable def Ns540p1376 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz676 1 1 0 1 4796337 16777216 1 33554432 4796337 16777216 1 33554432 

noncomputable def Ns540p1377 := @Enclosure.Real.IsNear.sqrt_image qz188 5023318074119 33554432000 470317 33554432000 410553978 410554017 33554432 (@Enclosure.Real.IsNear.of_eq qz188 (@HMul.hMul Real Real Real qz5 qz187 qz3) Bool.false 5023318074119 33554432000 470317 33554432000 (BSN.t_div_two_pi_mk qz187 940634 1000 qz190) (@Enclosure.Real.IsNear.mulLit_ff qz187 qz3 940634 1000 0 1 10680707 67108864 1 67108864 5023318074119 33554432000 470317 33554432000 (Enclosure.Real.IsNear.const Bool.false 940634 1000) RS541to552.d56 rfl)) 

noncomputable abbrev qz761 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 940634 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz677 := qz761

noncomputable abbrev qz499 := qz677

noncomputable abbrev qz196 := qz499

noncomputable def Ns540p1378 := @Enclosure.Real.IsNear.sqrt_image qz196 821107995 67108864 39 67108864 117370803 117370810 33554432 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 821107995 67108864 39 67108864 821107995 67108864 39 67108864 (Ns540p1377 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns540p1379 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz196) 234741613 67108864 7 67108864 9592673 9592675 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz196) Bool.false 234741613 67108864 7 67108864 234741613 67108864 7 67108864 (Ns540p1378 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns540p1380 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz196)) Bool.false 19185348 67108864 2 67108864 4796337 16777216 1 33554432 (Ns540p1379 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz197 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz493))

noncomputable abbrev qz678 := (@HMul.hMul Real Real Real qz717 qz760 qz760)

noncomputable abbrev qz500 := (@HSub.hSub Real Real Real qz582 (@HSub.hSub Real Real Real qz582 qz678 qz671) qz594)

noncomputable abbrev qz198 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz500))

noncomputable def Ns540p1381 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz189) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz197) qz198) Bool.false 579910500734669 

noncomputable def Ns540p1382 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz197) qz198 367863847 33554432 3801 

noncomputable def Ns540p1383 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz197) Bool.false 735727694 67108864 30408 67108864 367863847 33554432 3801 

noncomputable def Ns540p1384 := @Enclosure.Real.IsNear.recentre' qz197 Bool.false 3060643 33554432 1215584432 322458091520000 3060643 33554432 75974027 20153630720000 

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz355 qz352 qz493)

noncomputable def Ns540p1385 := @Enclosure.Real.IsNear.cos_image qz199 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49642275) qz384) Bool.false 49642275 33554432 123 33554432 Bool.false 3060643 33554432 1 

noncomputable def Ns540p1386 := nat_lit 1052456941088452715128770897 

noncomputable def Ns540p1387 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz189 884279719003555 140737488355328 1 500000000000000 15801627 67108864 39 67108864 13973058283358987783985 9444732965739290427392 Ns540p1386 

noncomputable def Ns540p1388 := @Enclosure.Real.IsNear.subLit_ff_p qz196 qz1 821107995 67108864 39 67108864 12 1 0 1 15801627 15801627 67108864 39 

noncomputable def Ns540p1389 := @Ns540p1388 67108864 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 821107995 67108864 39 67108864 821107995 67108864 39 67108864 (Ns540p1377 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns540p1390 := @Enclosure.Real.IsNear.recentre' qz199 Bool.false 13973058283358987783985 9444732965739290427392 Ns540p1386 Ns540p333 49642275 33554432 123 33554432 (@Ns540p1387 Ns540p333 RS541to552.d55 (Ns540p1389 rfl rfl) rfl) 

noncomputable def Ns540p1391 := nat_lit 195329912498878245328336717889930257370638139652283566033983386811905334924967757153786298056640625 

noncomputable def Ns540p1392 := nat_lit 223985607431325473126327019723080273901074236175421205071924696879839586072027683258056640625 

noncomputable def Ns540p1393 := nat_lit 1182753928095445111276057960339683470898931801887431184068209412882042733187041179179375034056640625 

noncomputable def Ns540p1394 := BSN.cos_dyadic_bound_f 49642275 33554432 4 3 33554432 9610000 Ns540p1391 Ns540p354 Ns540p1392 Ns540p1393 Ns540p357 Ns540p1392 3060643 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 49642275) qz595 0 3 Ns540p1391 Ns540p354 Ns540p1392 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 49642275) (BSN.cosOddQ 33554432) 0 3 Ns540p1393 Ns540p357 Ns540p1392 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1395 := @Enclosure.Real.IsNear.inv_image qz197 3060643 33554432 75974027 20153630720000 367848643 367879051 33554432 (Ns540p1384 (@Ns540p1385 9610000 (Ns540p1390 rfl) (Enclosure.sfrac_false_div 49642275 33554432) (Ns540p1394 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns540p1396 := @Enclosure.Real.IsNear.recentre' qz198 Bool.false 1576427 33554432 

noncomputable abbrev qz200 := (@HMul.hMul Real Real Real qz355 qz352 qz500)

noncomputable def Ns540p1397 := @Enclosure.Real.IsNear.cos_image qz200 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 51130171)) qz384) Bool.true 51130171 33554432 

noncomputable def Ns540p1398 := nat_lit 965821626271343817840893581525 

noncomputable def Ns540p1399 := nat_lit 103890294800446442857501882498081901 

noncomputable def Ns540p1400 := @Enclosure.Real.IsNear.recentre' qz200 Bool.true Ns540p1398 Ns540p210 Ns540p1399 

noncomputable abbrev qz201 := qz500

noncomputable def Ns540p1401 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz201 884279719003555 140737488355328 1 500000000000000 1092212798185255 

noncomputable abbrev qz501 := (@HSub.hSub Real Real Real qz582 qz678 qz671)

noncomputable abbrev qz202 := qz501

noncomputable def Ns540p1402 := @Enclosure.Real.IsNear.subLit_tf qz202 qz30 810737821474599 4503599627370496 3849774123 4503599627370496 1 16 

noncomputable abbrev qz502 := qz678

noncomputable abbrev qz203 := qz502

noncomputable def Ns540p1403 := @Enclosure.Real.IsNear.subLit_ff_n qz203 qz189 249691415847129 4503599627370496 1232528427 4503599627370496 15801627 67108864 39 67108864 

noncomputable def Ns540p1404 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz189 15801627 67108864 39 67108864 15801627 67108864 39 67108864 249691415847129 4503599627370496 

noncomputable def Ns540p1405 := nat_lit 219900381777480491526805277879119879119632892423687386812026877755649074223204010512066588640669521 

noncomputable def Ns540p1406 := nat_lit 319247086290263078630309602761472657379948148783868959294770505420374468577859807675792879441 

noncomputable def Ns540p1407 := nat_lit 1331215629341622314511012442628879668280159063879160215759900682398406827308013006752720957507235665 

noncomputable def Ns540p1408 := BSN.cos_dyadic_bound_f 51130171 33554432 4 3 33554432 9610000 Ns540p1405 Ns540p354 Ns540p1406 Ns540p1407 Ns540p357 Ns540p1406 1576427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 51130171) qz595 0 3 Ns540p1405 Ns540p354 Ns540p1406 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 51130171) (BSN.cosOddQ 33554432) 0 3 Ns540p1407 Ns540p357 Ns540p1406 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1409 := @Ns540p1396 3536318864 644916183040000 1576427 33554432 221019929 40307261440000 (@Ns540p1397 361 67108864 Bool.false 1576427 33554432 1 9610000 (@Ns540p1400 Ns540p213 51130171 33554432 361 67108864 (@Ns540p1401 4503599627370496 3849774123 4503599627370496 Ns540p1398 Ns540p210 Ns540p1399 Ns540p213 RS541to552.d55 (@Ns540p1402 0 1 17475404770964080 1092212798185255 4503599627370496 3849774123 4503599627370496 (@Ns540p1403 54407694200995143745536 810737821474599 4503599627370496 3849774123 4503599627370496 (@Ns540p1404 1232528427 4503599627370496 (Ns540p1389 rfl rfl) (Ns540p1389 rfl rfl) rfl) (Ns540p1389 rfl rfl) rfl rfl) qz389 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 51130171 33554432) (BSN.cos_neg_of_bound 51130171 33554432 Bool.false 1576427 33554432 1 9610000 (Ns540p1408 rfl rfl)) rfl rfl) 

noncomputable def Ns540p1410 := @Ns540p1375 42274065663561973064403 Ns540p1292 (Ns540p1376 qz32 (@Enclosure.Real.IsNear.of_eq qz676 (@Inv.inv Real Real.instInv (Real.sqrt qz196)) Bool.false 4796337 16777216 1 33554432 (BSN.rpow_neg_quarter_mk qz188 (BSN.t_div_two_pi_nonneg qz187 940634 1000 qz190)) Ns540p1380) rfl) (@Ns540p1381 1125899906842624 110100157057342379 1352487263094702080000 (BSN.correction_mk qz189 (BSN.cos_two_pi_p_ne_zero_mk qz187 940634 1000 12 qz190 rfl rfl (@BSN.floor_sqrt_eq_dec qz187 940634 1000 12 qz190 rfl rfl rfl))) (@Ns540p1382 8388608 1576427 33554432 221019929 40307261440000 579910500734669 1125899906842624 110100157057342379 1352487263094702080000 (@Ns540p1383 8388608 (Ns540p1395 rfl rfl rfl rfl rfl) rfl) (Ns540p1409 rfl) rfl)) 

noncomputable def Ns540p1411 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz187) (hardyZApproximantRS₀ qz187) Bool.false 36064342472529064089923 18889465931478580854784 Ns540p1291 Ns540p1292 (@Eq.refl Real (hardyZApproximantRS₀ qz187)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz187) (@HSub.hSub Real Real Real qz33 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz187) qz187 12) (@HMul.hMul Real Real Real qz5 qz672 (Zeta.RiemannSiegel.correction qz189))) Bool.false 36064342472529064089923 18889465931478580854784 Ns540p1291 Ns540p1292 (BSN.hardyZApproximantRS₀_eq qz187 12 (@BSN.floor_sqrt_eq_dec qz187 940634 1000 12 qz190 rfl rfl rfl)) (@Ns540p1294 36064342472529064089923 18889465931478580854784 Ns540p1291 Ns540p1292 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz187) qz187 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz187) qz187 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz187) qz187 12)) Bool.false 552031859 268435456 270435 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz187) qz187 12) (Ns540p1374 (Ns540p1373 rfl rfl rfl rfl) rfl rfl)) (Ns540p1410 rfl) rfl rfl)) 

theorem RS541to552.d68 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz187) Bool.false 36064342472529064089923 18889465931478580854784 Ns540p1291 Ns540p1292 := Ns540p1411 

noncomputable def Ns540p1412 := nat_lit 2412501579601893405061963 

noncomputable def Ns540p1413 := nat_lit 2269097095018864525180928000 

noncomputable def Ns540p1414 := nat_lit 4273825588983974457785721028608 

noncomputable abbrev qz762 := (Enclosure.sfrac Bool.false 941888 1000)

noncomputable abbrev qz679 := qz762

noncomputable abbrev qz503 := qz679

noncomputable abbrev qz204 := qz503

noncomputable abbrev qz763 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 941888 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz680 := qz763

noncomputable abbrev qz504 := qz680

noncomputable abbrev qz205 := qz504

noncomputable abbrev qz764 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 941888 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz681 := qz764

noncomputable abbrev qz505 := qz681

noncomputable abbrev qz206 := qz505

noncomputable abbrev qz682 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz152 qz205 qz154))

noncomputable def Ns540p1415 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 12) (@HMul.hMul Real Real Real qz5 qz682 (Zeta.RiemannSiegel.correction qz206)) 187399019 268435456 135399 134217728 2734207376804080553677 18889465931478580854784 123433792904898818437963 Ns540p1413 Ns540p1414 

noncomputable def Ns540p1416 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos BSN.quadSignPos 11 12 941888 1000 288 536870912 268435456 9007199254740992 Bool.false 1013664436722 4485 1334074092 57 154981288 8 

noncomputable def Ns540p1417 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 941888 1000 178 235 536870912 268435456 9007199254740992 Bool.false 1013664436722 4485 

noncomputable def Ns540p1418 := Ns540p1417 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 418679379 218040 Bool.true 578945980 Bool.true 705714888 28296951008113761 1 Bool.false 253813517 Bool.true Bool.false 519333798 Bool.false Bool.true 342357239 

noncomputable def Ns540p1419 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 941888 1000 44 115 536870912 268435456 9007199254740992 Bool.false 1013664436722 4485 

noncomputable def Ns540p1420 := Ns540p1419 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 581489841 178062 Bool.true 745632514 Bool.true 429879686 28296951008113761 1 Bool.false 97144273 Bool.false Bool.false 385394329 Bool.false Bool.true 418679379 

noncomputable def Ns540p1421 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 941888 1000 127 35 536870912 268435456 9007199254740992 Bool.false 1013664436722 4485 

noncomputable def Ns540p1422 := Ns540p1421 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 820198718 132306 Bool.false 520379532 Bool.false 155629805 28296951008113761 1 Bool.false 442639248 Bool.false Bool.false 153459291 Bool.false Bool.true 581489841 

noncomputable def Ns540p1423 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 941888 1000 370 236 536870912 268435456 9007199254740992 Bool.false 1013664436722 4485 

noncomputable def Ns540p1424 := Ns540p1423 744261104 56 268435448 8 864060384 56 240095976 8 Bool.true 737111881 78076 Bool.false 627337080 Bool.false 794023615 28296951008113761 1 Bool.false 210199194 Bool.true Bool.false 49222020 Bool.false Bool.true 820198718 

noncomputable def Ns540p1425 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 941888 1000 786 543 536870912 268435456 9007199254740992 Bool.false 1013664436722 4485 

noncomputable def Ns540p1426 := Ns540p1425 372130544 56 379625064 8 589812976 56 309962568 8 Bool.true 536870904 4544 Bool.false 313665660 Bool.false 206705286 28296951008113761 1 Bool.false 447818632 Bool.true Bool.false 201636029 Bool.false Bool.true 737111881 

noncomputable def Ns540p1427 := nat_lit 203836825961964118844373928770199286493118277838045773 

noncomputable def Ns540p1428 := nat_lit 107958865566171992503555815807053217040070344704000 

noncomputable def Ns540p1429 := nat_lit 355826154168879483308873956720640000 

noncomputable def Ns540p1430 := nat_lit 2010890572633072594246935393792637009920 

noncomputable abbrev qz765 := (@Eq.refl Real (Enclosure.sfrac Bool.false 941888 1000))

noncomputable abbrev qz683 := qz765

noncomputable abbrev qz506 := qz683

noncomputable abbrev qz207 := qz506

noncomputable def Ns540p1431 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz204 941888 1000 3548613018176 16000000 1883776 4000 2000 Ns540p1429 Ns540p1430 qz207 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns540p1432 := nat_lit 267173004524865609851697795917675608792259989127883355586560 

noncomputable abbrev qz684 := (@HSub.hSub Real Real Real qz721 qz722 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz723 (@Nat.cast Real Real.instNatCast 1883776))))

noncomputable abbrev qz507 := (@HSub.hSub Real Real Real qz582 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 941888 4000) (Real.log (Enclosure.sfrac Bool.false 3548613018176 16000000))) (@HMul.hMul Real Real Real qz579 qz583 qz684))

noncomputable abbrev qz685 := (Enclosure.sfrac Bool.false 941888 2000)

noncomputable abbrev qz208 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz507 qz685) (@HMul.hMul Real Real Real qz355 qz685 (Real.log Real.pi)))

noncomputable def Ns540p1433 := @Enclosure.Real.IsNear.addLit_ft_p qz208 (Enclosure.sfrac Bool.true Ns540p1429 Ns540p1430) 132863037501870229293 70368744177664000 2054745094555501259 246016000000000000000000 Ns540p1429 Ns540p1430 0 1 Ns540p1432 

noncomputable def Ns540p1434 := nat_lit 139316992411561077551136768000 

noncomputable abbrev qz209 := (@HSub.hSub Real Real Real qz361 qz507 qz685)

noncomputable def Ns540p1435 := @Enclosure.Real.IsNear.subLit_ff_p qz209 (@HMul.hMul Real Real Real qz5 qz685 (Real.log Real.pi)) 170799085725440591661 70368744177664000 2968403847026189 961000000000000000000 565291169637 1048576000 44151 8388608000 Ns540p1434 132863037501870229293 70368744177664000 

noncomputable abbrev qz210 := qz507

noncomputable def Ns540p1436 := @Enclosure.Real.IsNear.subLit_ff_p qz210 qz685 203938823583446386477 70368744177664000 2968403847026189 961000000000000000000 941888 2000 0 1 341598171450881183322000 170799085725440591661 70368744177664000 2968403847026189 961000000000000000000 

noncomputable def Ns540p1437 := nat_lit 1836917619793572935789375192966365184 

noncomputable def Ns540p1438 := nat_lit 119049972627758185921380352 

noncomputable def Ns540p1439 := nat_lit 141723355883032595842716602702472922801924029590171872016302873967521192448536908950524122418570180978559130144387685254595137038953238877137847663030184181760 

noncomputable def Ns540p1440 := nat_lit 3252363444905328775970798068118811338862536160012399713626982608623035365897525178842229687245855364095645972920274982939717271997572191369460373866279862272 

noncomputable def Ns540p1441 := nat_lit 908843303529650067673262119386034870908120900848083365807311320321550874456198691542917297533902863276199797035749366621162716894909959945208746475520 

noncomputable def Ns540p1442 := BSN.log_dyadic_bound 1451461018176 5645765018176 7 6 Ns540p1439 268435456 76880000 Ns540p1440 Ns540p1441 141190766 7097226036352 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1451461018176) (BSN.artanhQ 5645765018176) 0 6 Ns540p1440 Ns540p1439 Ns540p1441 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz508 := (Real.log (Enclosure.sfrac Bool.false 3548613018176 16000000))

noncomputable def Ns540p1443 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 941888 4000) qz508 941888 4000 0 1 55436963507792999 4503599627370496 12500016337 961000000000000000 815865791944189566283 281474976710656000 183962740431629 60062500000000000000 (Enclosure.Real.IsNear.const Bool.false 941888 4000) (BSN.isNear_log_sfrac 3548613018176 16000000 55436963507792999 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3548613018176) qz364)) Bool.false Ns540p1438 Ns540p114 1000001306960000 76880000000000000000000 55436963507792999 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3548613018176 16000000 17 7097226036352 4194304000000 141190766 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns540p1442 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p1444 := BSN.arctan_dyadic_bound_f 1000 1883776 1 0 33554432 9610000 0 1 1 0 1 1 17812 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1883776) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1883776) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns540p1445 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1883776))) 884279719003555 562949953421312 1 2000000000000000 17812 33554432 1 9610000 29661476435713553596416 883980883232163 562949953421312 200000000961 1922000000000000000 qz15 (Ns540p1444 rfl) rfl rfl 

noncomputable abbrev qz509 := (@HMul.hMul Real Real Real qz579 qz583 qz684)

noncomputable abbrev qz211 := qz509

noncomputable abbrev qz510 := qz684

noncomputable abbrev qz212 := qz510

noncomputable def Ns540p1446 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 941888 4000) qz508) qz211 815865791944189566283 281474976710656000 183962740431629 60062500000000000000 883980883232163 2251799813685248 200000000961 7688000000000000000 Ns540p1437 203938823583446386477 70368744177664000 2968403847026189 961000000000000000000 (Ns540p1443 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz212 1 4 0 1 883980883232163 562949953421312 200000000961 1922000000000000000 883980883232163 2251799813685248 200000000961 7688000000000000000 qz372 Ns540p1445 rfl) 

noncomputable def Ns540p1447 := @Ns540p1433 Ns540p1427 Ns540p1428 2054745094555501259 246016000000000000000000 (@Ns540p1435 2054745094555501259 246016000000000000000000 (Ns540p1436 (Ns540p1446 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 941888 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz685 (Real.log Real.pi) 941888 2000 0 1 38410761 33554432 3 268435456 565291169637 1048576000 44151 8388608000 (Enclosure.Real.IsNear.const Bool.false 941888 2000) RS541to552.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns540p1429 Ns540p1430) 

noncomputable def Ns540p1448 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz204) Bool.false Ns540p1427 Ns540p1428 2054745094555501259 246016000000000000000000 63354027295 33554432 561 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz204) (@HAdd.hAdd Real Real Real qz373 qz208 (Enclosure.sfrac Bool.true Ns540p1429 Ns540p1430)) Bool.false Ns540p1427 Ns540p1428 2054745094555501259 246016000000000000000000 Ns540p1431 (Ns540p1447 rfl rfl)) 

noncomputable def Ns540p1449 := nat_lit 7595717307346529739079680 

noncomputable def Ns540p1450 := nat_lit 4835703278458516698824704 

noncomputable def Ns540p1451 := nat_lit 14378958403488727448947541650178817369457051529641868815845731500962837647752471926639729800711144516467935333026418900204585989747587076325376 

noncomputable def Ns540p1452 := nat_lit 10247734337313363347972762123352253827338964178985259769769789476237152574836047711117414635657450948977173116218238853028357241544114176 

noncomputable def Ns540p1453 := nat_lit 71805462680283338674080208690702908155743786391076210053030189551812151051150957514197708729445203654623915119533103328828574456299721049767936 

noncomputable def Ns540p1454 := BSN.sin_dyadic_bound_f 215883270224 137438953472 4 3 67108864 19238770 Ns540p1451 Ns540p267 Ns540p1452 Ns540p1453 Ns540p270 Ns540p1452 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215883270224) (BSN.sinEvenQ 137438953472) 0 3 Ns540p1451 Ns540p267 Ns540p1452 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215883270224) (BSN.sinOddQ 137438953472) 0 3 Ns540p1453 Ns540p270 Ns540p1452 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1455 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz204) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 63354027295) qz384) Bool.false 63354027295 33554432 561 67108864 Bool.true 67108863 67108864 1 9610000 (Ns540p1448 rfl) (Enclosure.sfrac_false_div 63354027295 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 63354027295) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns540p1449) (@Nat.cast Real Real.instNatCast Ns540p1450)) 226375608064910080 72057594037927936 Bool.false 67108863 67108864 300 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q1 63354027295 33554432 226375608064910080 72057594037927936 300 Ns540p1449 Ns540p1450 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108863 67108864 Ns540p1449 Ns540p1450 215883270224 137438953472 19238770 19220000 (Ns540p1454 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns540p1456 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz204) Bool.false Ns540p1427 Ns540p1428 2054745094555501259 246016000000000000000000 1013664436722 536870912 4485 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz204) (@HAdd.hAdd Real Real Real qz373 qz208 (Enclosure.sfrac Bool.true Ns540p1429 Ns540p1430)) Bool.false Ns540p1427 Ns540p1428 2054745094555501259 246016000000000000000000 Ns540p1431 (Ns540p1447 rfl rfl)) 

noncomputable def Ns540p1457 := Ns540p1426 78076 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 786 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 447818632 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 543 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 201636029 536870912) qz207 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 1) Bool.true 67108863 67108864 341144929 40307261440000 536870904 536870912 4544 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz204)) Bool.true 67108863 67108864 341144929 40307261440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz204) qz204) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz204)) Bool.true 67108863 67108864 5458318864 644916183040000 67108863 67108864 341144929 40307261440000 (Ns540p1455 rfl rfl) rfl)) rfl) (Ns540p1456 rfl) RS541to552.d7 

noncomputable def Ns540p1458 := nat_lit 1351097834464402344110289624449980185160331485536848856451021385932800000 

noncomputable def Ns540p1459 := nat_lit 93699181941266305475433171961184112659372891248879235846169600000000 

noncomputable def Ns540p1460 := nat_lit 4053106105029324499719918007006018187255675710828048810881371818598400000 

noncomputable def Ns540p1461 := BSN.cos_dyadic_bound_f 313665660 536870912 3 2 536870912 268435456 Ns540p1458 Ns540p160 Ns540p1459 Ns540p1460 Ns540p163 Ns540p1459 447818632 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 313665660) qz19 0 2 Ns540p1458 Ns540p160 Ns540p1459 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 313665660) qz378 0 2 Ns540p1460 Ns540p163 Ns540p1459 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1462 := nat_lit 1825602960302911954431250744505616 

noncomputable def Ns540p1463 := BSN.sin_dyadic_bound_f 206705286 536870912 2 1 536870912 268435456 Ns540p1462 Ns540p282 Ns540p1462 Ns540p1462 Ns540p283 Ns540p1462 201636029 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 206705286) qz376 0 1 Ns540p1462 Ns540p282 Ns540p1462 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 206705286) qz377 0 1 Ns540p1462 Ns540p283 Ns540p1462 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1464 := nat_lit 21358478129101279096365678576544271760251213587715743343347445316610377853661213904867796107005820187705344000000 

noncomputable def Ns540p1465 := nat_lit 3715450653031512531293801017270000159611945762534280134640509596397181126535910945372594241536000000000000 

noncomputable def Ns540p1466 := nat_lit 129478993267516544849157724203905532174772961006871606715095853563782223220606703274170499147919360087660953600000 

noncomputable def Ns540p1467 := BSN.cos_dyadic_bound_f 627337080 536870912 4 3 536870912 268435456 Ns540p1464 Ns540p153 Ns540p1465 Ns540p1466 Ns540p156 Ns540p1465 210199194 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 627337080) qz19 0 3 Ns540p1464 Ns540p153 Ns540p1465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 627337080) qz378 0 3 Ns540p1466 Ns540p156 Ns540p1465 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1468 := nat_lit 54910325176190584927345583068766593846653586234949605642317980692743409145771139106762175518287581901911776890625 

noncomputable def Ns540p1469 := nat_lit 62805984443355158364206557476175731344567085002798060201283055965596739642945469188314928284121855712890625 

noncomputable def Ns540p1470 := nat_lit 332491622154738704623110619266540925106492354799834274635053885757532899437034927502170285680595038427943034490625 

noncomputable def Ns540p1471 := BSN.cos_dyadic_bound_f 794023615 536870912 4 3 536870912 268435456 Ns540p1468 Ns540p153 Ns540p1469 Ns540p1470 Ns540p156 Ns540p1469 49222020 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 794023615) qz19 0 3 Ns540p1468 Ns540p153 Ns540p1469 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 794023615) qz378 0 3 Ns540p1470 Ns540p156 Ns540p1469 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1472 := Ns540p1424 132306 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 370 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 210199194 536870912) BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 49222020 536870912) qz207 rfl rfl (Ns540p1457 RS541to552.d9 RS541to552.d11 RS541to552.d13 RS541to552.d17 (Ns540p1461 rfl rfl) (Ns540p1463 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns540p1456 rfl) RS541to552.d19 RS541to552.d21 RS541to552.d23 RS541to552.d25 RS541to552.d17 (Ns540p1467 rfl rfl) (Ns540p1471 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns540p1473 := nat_lit 18427603386099044354012683863921700006543943371571208373739186835270205440 

noncomputable def Ns540p1474 := nat_lit 5377267598157299243415852717092634886690030136302618469062314284875776 

noncomputable def Ns540p1475 := nat_lit 48254064720814766252210546358252969084465210686275341501319388440675024896 

noncomputable def Ns540p1476 := BSN.sin_dyadic_bound_f 520379532 536870912 3 2 536870912 268435456 Ns540p1473 Ns540p276 Ns540p1474 Ns540p1475 Ns540p279 Ns540p1474 442639248 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 520379532) qz376 0 2 Ns540p1473 Ns540p276 Ns540p1474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 520379532) qz377 0 2 Ns540p1475 Ns540p279 Ns540p1474 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1477 := nat_lit 586639218142889890721828460900625 

noncomputable def Ns540p1478 := BSN.sin_dyadic_bound_f 155629805 536870912 2 1 536870912 268435456 Ns540p1477 Ns540p282 Ns540p1477 Ns540p1477 Ns540p283 Ns540p1477 153459291 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 155629805) qz376 0 1 Ns540p1477 Ns540p282 Ns540p1477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 155629805) qz377 0 1 Ns540p1477 Ns540p283 Ns540p1477 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1479 := Ns540p1422 178062 BSN.abs_quadSignPos (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 442639248 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 153459291 536870912) qz207 rfl rfl (Ns540p1472 rfl rfl) (Ns540p1456 rfl) RS541to552.d27 RS541to552.d29 RS541to552.d31 RS541to552.d33 RS541to552.d17 (Ns540p1476 rfl rfl) (Ns540p1478 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1480 := nat_lit 42672209072029479506104306761474498208693168273263150103501383756188582539048502486320514011740277297002766667776 

noncomputable def Ns540p1481 := nat_lit 29532352999229101337911726933295311077428281493485022002593846964257523991414098822281952663134926222135296 

noncomputable def Ns540p1482 := nat_lit 258496542605313312060310663916893665940572921187690047965424734681097019133408622507471274583218227857087627530240 

noncomputable def Ns540p1483 := BSN.cos_dyadic_bound_f 745632514 536870912 4 3 536870912 268435456 Ns540p1480 Ns540p153 Ns540p1481 Ns540p1482 Ns540p156 Ns540p1481 97144273 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 745632514) qz19 0 3 Ns540p1480 Ns540p153 Ns540p1481 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 745632514) qz378 0 3 Ns540p1482 Ns540p156 Ns540p1481 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1484 := nat_lit 8580409339406444285499481736277239757658932352732773083417432952609153280 

noncomputable def Ns540p1485 := nat_lit 1166206301706309818316089430303599898213747970661713044066255366758656 

noncomputable def Ns540p1486 := nat_lit 22470612507290305769935654688315136394033429141395239111640979033858744576 

noncomputable def Ns540p1487 := BSN.sin_dyadic_bound_f 429879686 536870912 3 2 536870912 268435456 Ns540p1484 Ns540p276 Ns540p1485 Ns540p1486 Ns540p279 Ns540p1485 385394329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 429879686) qz376 0 2 Ns540p1484 Ns540p276 Ns540p1485 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 429879686) qz377 0 2 Ns540p1486 Ns540p279 Ns540p1485 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1488 := Ns540p1420 218040 BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 97144273 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 385394329 536870912) qz207 rfl rfl (Ns540p1479 rfl) (Ns540p1456 rfl) RS541to552.d35 RS541to552.d37 RS541to552.d39 RS541to552.d41 RS541to552.d17 (Ns540p1483 rfl rfl) (Ns540p1487 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1489 := nat_lit 15487680012973379793601620270891095660217546015867181694724051121981326723005303920306910779186729325953024000000 

noncomputable def Ns540p1490 := nat_lit 1417935618928536080563807993461073213884202332076408619955565653922837250056464454098011754496000000000000 

noncomputable def Ns540p1491 := nat_lit 93908204779629259525582896249420300271322201769034408129996933436171013487273856374391377413433908979931545600000 

noncomputable def Ns540p1492 := BSN.cos_dyadic_bound_f 578945980 536870912 4 3 536870912 268435456 Ns540p1489 Ns540p153 Ns540p1490 Ns540p1491 Ns540p156 Ns540p1490 253813517 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 578945980) qz19 0 3 Ns540p1489 Ns540p153 Ns540p1490 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 578945980) qz378 0 3 Ns540p1491 Ns540p156 Ns540p1490 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1493 := nat_lit 88920896202823517847441469871243419473652717150777949810832350180344051997889382238990549800538873893231427321856 

noncomputable def Ns540p1494 := nat_lit 15259888299516379341267226480654292716052034553893378172756737960552761297762751843321015884788907278073856 

noncomputable def Ns540p1495 := nat_lit 444333327632975172134378408101394963877796168110207836878683908822849367270849764786066790594128954868650911727616 

noncomputable def Ns540p1496 := BSN.sin_dyadic_bound_f 705714888 536870912 4 3 536870912 268435456 Ns540p1493 Ns540p130 Ns540p1494 Ns540p1495 Ns540p133 Ns540p1494 519333798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 705714888) qz376 0 3 Ns540p1493 Ns540p130 Ns540p1494 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 705714888) qz377 0 3 Ns540p1495 Ns540p133 Ns540p1494 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1497 := Ns540p1418 253995 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 178 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 253813517 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 235 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 519333798 536870912) qz207 rfl rfl (Ns540p1488 rfl) (Ns540p1456 rfl) RS541to552.d43 RS541to552.d45 RS541to552.d47 RS541to552.d49 RS541to552.d17 (Ns540p1492 rfl rfl) (Ns540p1496 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1498 := nat_lit 7362063002383281679100741136 

noncomputable def Ns540p1499 := BSN.cos_dyadic_bound_f 9262962 536870912 2 1 536870912 268435456 Ns540p1498 Ns540p136 Ns540p1498 Ns540p1498 Ns540p137 Ns540p1498 536791004 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 9262962) qz19 0 1 Ns540p1498 Ns540p136 Ns540p1498 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 9262962) qz378 0 1 Ns540p1498 Ns540p137 Ns540p1498 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1500 := Ns540p1416 Bool.true 342357239 253995 Bool.true 9262962 28296951008113761 1 Bool.false 536791004 Bool.false Bool.true 187399019 270798 BSN.abs_quadSignPos qz380 (BSN.sfrac_eq_quadSignPos_mul Bool.false 536791004 536870912) qz207 rfl (Ns540p1497 rfl) (Ns540p1456 rfl) RS541to552.d51 RS541to552.d53 RS541to552.d17 (Ns540p1499 rfl rfl) rfl 

noncomputable def Ns540p1501 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 12) 187399019 536870912 270798 536870912 187399019 536870912 270798 536870912 201218164476870656 187399019 268435456 135399 134217728 (Ns540p1500 rfl rfl rfl rfl) 

noncomputable def Ns540p1502 := @Enclosure.Real.IsNear.mulLit_ff qz682 (Zeta.RiemannSiegel.correction qz206) 19178959 67108864 1 67108864 142562866775203 281474976710656 128700062506546181 676243631547351040000 2734207376804080553677 18889465931478580854784 

noncomputable abbrev qz686 := (@HPow.hPow Real Real Real qz152 qz205 qz154)

noncomputable def Ns540p1503 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz686 1 1 0 1 19178959 67108864 1 67108864 19178959 67108864 1 67108864 

noncomputable def Ns540p1504 := @Enclosure.Real.IsNear.sqrt_image qz205 157187964919 1048576000 14717 1048576000 410827550 410827590 33554432 (@Enclosure.Real.IsNear.of_eq qz205 (@HMul.hMul Real Real Real qz5 qz204 qz3) Bool.false 157187964919 1048576000 14717 1048576000 (BSN.t_div_two_pi_mk qz204 941888 1000 qz207) (@Enclosure.Real.IsNear.mulLit_ff qz204 qz3 941888 1000 0 1 10680707 67108864 1 67108864 157187964919 1048576000 14717 1048576000 (Enclosure.Real.IsNear.const Bool.false 941888 1000) RS541to552.d56 rfl)) 

noncomputable abbrev qz766 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 941888 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz687 := qz766

noncomputable abbrev qz511 := qz687

noncomputable abbrev qz213 := qz511

noncomputable def Ns540p1505 := @Enclosure.Real.IsNear.sqrt_image qz213 205413785 16777216 5 8388608 117409902 117409908 33554432 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 821655140 67108864 40 67108864 205413785 16777216 5 8388608 (Ns540p1504 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns540p1506 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz213) 117409905 33554432 3 33554432 9589479 9589480 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz213) Bool.false 234819810 67108864 6 67108864 117409905 33554432 3 33554432 (Ns540p1505 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns540p1507 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz213)) Bool.false 19178959 67108864 1 67108864 19178959 67108864 1 67108864 (Ns540p1506 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz214 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz505))

noncomputable abbrev qz688 := (@HMul.hMul Real Real Real qz717 qz764 qz764)

noncomputable abbrev qz512 := (@HSub.hSub Real Real Real qz582 (@HSub.hSub Real Real Real qz582 qz688 qz681) qz594)

noncomputable abbrev qz215 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz512))

noncomputable def Ns540p1508 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz206) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz214) qz215) Bool.false 142562866775203 

noncomputable def Ns540p1509 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz214) qz215 1673410571 67108864 161035 

noncomputable def Ns540p1510 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz214) Bool.false 1673410571 67108864 161035 67108864 1673410571 67108864 161035 

noncomputable def Ns540p1511 := @Enclosure.Real.IsNear.recentre' qz214 Bool.false 1345635 33554432 622207216 161229045760000 1345635 33554432 38887951 10076815360000 

noncomputable abbrev qz216 := (@HMul.hMul Real Real Real qz355 qz352 qz505)

noncomputable def Ns540p1512 := @Enclosure.Real.IsNear.cos_image qz216 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 25680591) qz616) Bool.false 25680591 16777216 63 16777216 Bool.false 1345635 33554432 1 

noncomputable def Ns540p1513 := nat_lit 134930377062774587543284963 

noncomputable def Ns540p1514 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz206 884279719003555 140737488355328 1 500000000000000 4087193 16777216 5 8388608 3614221877553296971115 2361183241434822606848 Ns540p1513 

noncomputable def Ns540p1515 := @Enclosure.Real.IsNear.subLit_ff_p qz213 qz1 205413785 16777216 5 8388608 12 1 0 1 4087193 4087193 16777216 5 

noncomputable def Ns540p1516 := @Ns540p1515 8388608 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 821655140 67108864 40 67108864 205413785 16777216 5 8388608 (Ns540p1504 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns540p1517 := @Enclosure.Real.IsNear.recentre' qz216 Bool.false 3614221877553296971115 2361183241434822606848 Ns540p1513 Ns540p893 25680591 16777216 63 16777216 (@Ns540p1514 Ns540p893 RS541to552.d55 (Ns540p1516 rfl rfl) rfl) 

noncomputable def Ns540p1518 := nat_lit 54666641665374518965045091637098434117058460323401962112177422261358923736126659665514410807361 

noncomputable def Ns540p1519 := nat_lit 82273537259560135824198341737125915284475875262156193455397284950693745021034688434671681 

noncomputable def Ns540p1520 := nat_lit 330923772268177665949438346280708366866578517025397347599982178774478937246161274841866776350785 

noncomputable def Ns540p1521 := BSN.cos_dyadic_bound_f 25680591 16777216 4 3 33554432 9610000 Ns540p1518 Ns540p519 Ns540p1519 Ns540p1520 Ns540p522 Ns540p1519 1345635 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 25680591) (BSN.cosEvenQ 16777216) 0 3 Ns540p1518 Ns540p519 Ns540p1519 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 25680591) (BSN.cosOddQ 16777216) 0 3 Ns540p1520 Ns540p522 Ns540p1519 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1522 := @Enclosure.Real.IsNear.inv_image qz214 1345635 33554432 38887951 10076815360000 836624768 836785803 33554432 (Ns540p1511 (@Ns540p1512 9610000 (Ns540p1517 rfl) (Enclosure.sfrac_false_div 25680591 16777216) (Ns540p1521 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns540p1523 := @Enclosure.Real.IsNear.recentre' qz215 Bool.false 681544 33554432 

noncomputable abbrev qz217 := (@HMul.hMul Real Real Real qz355 qz352 qz512)

noncomputable def Ns540p1524 := @Enclosure.Real.IsNear.cos_image qz217 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 52025587)) qz384) Bool.true 52025587 33554432 

noncomputable def Ns540p1525 := nat_lit 61420972085268964509771584525 

noncomputable def Ns540p1526 := nat_lit 39614081257132168796771975168 

noncomputable def Ns540p1527 := nat_lit 33667304153443646648087129939861 

noncomputable def Ns540p1528 := @Enclosure.Real.IsNear.recentre' qz217 Bool.true Ns540p1525 Ns540p1526 Ns540p1527 

noncomputable def Ns540p1529 := nat_lit 6044629098073145873530880000000000000 

noncomputable abbrev qz218 := qz512

noncomputable def Ns540p1530 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz218 884279719003555 140737488355328 1 500000000000000 69458759219855 

noncomputable abbrev qz513 := (@HSub.hSub Real Real Real qz582 qz688 qz681)

noncomputable abbrev qz219 := qz513

noncomputable def Ns540p1531 := @Enclosure.Real.IsNear.subLit_tf qz219 qz30 51866573175439 281474976710656 31189515 35184372088832 1 16 

noncomputable abbrev qz514 := qz688

noncomputable abbrev qz220 := qz514

noncomputable def Ns540p1532 := @Enclosure.Real.IsNear.subLit_ff_n qz220 qz206 16705146619249 281474976710656 10217995 35184372088832 4087193 16777216 5 8388608 

noncomputable def Ns540p1533 := @Enclosure.Real.IsNear.mulLit_ff qz206 qz206 4087193 16777216 5 8388608 4087193 16777216 5 8388608 16705146619249 281474976710656 

noncomputable def Ns540p1534 := nat_lit 235768047570652512753596878880012316906804749325517451525412970700569128598744660712653799404950961 

noncomputable def Ns540p1535 := nat_lit 393191271399253162828553917149975764330620216438229015263613057130292201068574726993191196081 

noncomputable def Ns540p1536 := nat_lit 1427055194158709928982636058987846500453420299905904379768532250783793099304474610166461909319898545 

noncomputable def Ns540p1537 := BSN.cos_dyadic_bound_f 52025587 33554432 4 3 33554432 9610000 Ns540p1534 Ns540p354 Ns540p1535 Ns540p1536 Ns540p357 Ns540p1535 681544 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 52025587) qz595 0 3 Ns540p1534 Ns540p354 Ns540p1535 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 52025587) (BSN.cosOddQ 33554432) 0 3 Ns540p1536 Ns540p357 Ns540p1535 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1538 := @Ns540p1523 1830624432 322458091520000 85193 4194304 114414027 20153630720000 (@Ns540p1524 187 33554432 Bool.false 681544 33554432 1 9610000 (@Ns540p1528 Ns540p1529 52025587 33554432 187 33554432 (@Ns540p1530 281474976710656 31189515 35184372088832 Ns540p1525 Ns540p1526 Ns540p1527 Ns540p1529 RS541to552.d55 (@Ns540p1531 0 1 1111340147517680 69458759219855 281474976710656 31189515 35184372088832 (@Ns540p1532 870176701344145997824 51866573175439 281474976710656 31189515 35184372088832 (@Ns540p1533 10217995 35184372088832 (Ns540p1516 rfl rfl) (Ns540p1516 rfl rfl) rfl) (Ns540p1516 rfl rfl) rfl rfl) qz389 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 52025587 33554432) (BSN.cos_neg_of_bound 52025587 33554432 Bool.false 681544 33554432 1 9610000 (Ns540p1537 rfl rfl)) rfl rfl) 

noncomputable def Ns540p1539 := @Ns540p1502 123433792904898818437963 Ns540p1413 (Ns540p1503 qz32 (@Enclosure.Real.IsNear.of_eq qz686 (@Inv.inv Real Real.instInv (Real.sqrt qz213)) Bool.false 19178959 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz205 (BSN.t_div_two_pi_nonneg qz204 941888 1000 qz207)) Ns540p1507) rfl) (@Ns540p1508 281474976710656 128700062506546181 676243631547351040000 (BSN.correction_mk qz206 (BSN.cos_two_pi_p_ne_zero_mk qz204 941888 1000 12 qz207 rfl rfl (@BSN.floor_sqrt_eq_dec qz204 941888 1000 12 qz207 rfl rfl rfl))) (@Ns540p1509 67108864 85193 4194304 114414027 20153630720000 142562866775203 281474976710656 128700062506546181 676243631547351040000 (@Ns540p1510 67108864 (Ns540p1522 rfl rfl rfl rfl rfl) rfl) (Ns540p1538 rfl) rfl)) 

noncomputable def Ns540p1540 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz204) (hardyZApproximantRS₀ qz204) Bool.true 15921241003960275865293 18889465931478580854784 Ns540p1412 Ns540p1413 (@Eq.refl Real (hardyZApproximantRS₀ qz204)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz204) (@HSub.hSub Real Real Real qz33 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 12) (@HMul.hMul Real Real Real qz5 qz682 (Zeta.RiemannSiegel.correction qz206))) Bool.true 15921241003960275865293 18889465931478580854784 Ns540p1412 Ns540p1413 (BSN.hardyZApproximantRS₀_eq qz204 12 (@BSN.floor_sqrt_eq_dec qz204 941888 1000 12 qz207 rfl rfl rfl)) (@Ns540p1415 15921241003960275865293 18889465931478580854784 Ns540p1412 Ns540p1413 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 12)) Bool.true 187399019 268435456 135399 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz204) qz204 12) (Ns540p1501 (Ns540p1500 rfl rfl rfl rfl) rfl rfl)) (Ns540p1539 rfl) rfl rfl)) 

theorem RS541to552.d69 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz204) Bool.true 15921241003960275865293 18889465931478580854784 Ns540p1412 Ns540p1413 := Ns540p1540 

noncomputable def Ns540p1541 := nat_lit 6827301987602357628181061 

noncomputable def Ns540p1542 := nat_lit 5672742737547161312952320000 

noncomputable def Ns540p1543 := nat_lit 18021628190650606925751871602688 

noncomputable abbrev qz767 := (Enclosure.sfrac Bool.false 943142 1000)

noncomputable abbrev qz689 := qz767

noncomputable abbrev qz515 := qz689

noncomputable abbrev qz221 := qz515

noncomputable abbrev qz768 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 943142 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz690 := qz768

noncomputable abbrev qz516 := qz690

noncomputable abbrev qz222 := qz516

noncomputable abbrev qz769 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 943142 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz691 := qz769

noncomputable abbrev qz517 := qz691

noncomputable abbrev qz223 := qz517

noncomputable abbrev qz692 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz152 qz222 qz154))

noncomputable def Ns540p1544 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz221) qz221 12) (@HMul.hMul Real Real Real qz5 qz692 (Zeta.RiemannSiegel.correction qz223)) 1946324667 268435456 271169 268435456 1344414628281593040221 9444732965739290427392 1096792321256619060501061 Ns540p1542 Ns540p1543 

noncomputable def Ns540p1545 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.sin BSN.quadSignPos 11 12 943142 1000 287 536870912 268435456 9007199254740992 Bool.false 1015351120583 4491 1334074092 57 154981288 8 

noncomputable def Ns540p1546 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 943142 1000 178 235 536870912 268435456 9007199254740992 Bool.false 1015351120583 4491 

noncomputable def Ns540p1547 := Ns540p1546 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.false 1757005747 218340 Bool.true 442445577 Bool.true 633380743 28296951008113761 1 Bool.false 364644741 Bool.true Bool.false 496345707 Bool.false Bool.false 1791348805 

noncomputable def Ns540p1548 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 943142 1000 44 115 536870912 268435456 9007199254740992 Bool.false 1015351120583 4491 

noncomputable def Ns540p1549 := Ns540p1548 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.false 1560369575 178309 Bool.true 458903815 Bool.true 222446764 28296951008113761 1 Bool.false 352395784 Bool.false Bool.false 216136339 Bool.false Bool.false 1757005747 

noncomputable def Ns540p1550 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 943142 1000 128 35 536870912 268435456 9007199254740992 Bool.false 1015351120583 4491 

noncomputable def Ns540p1551 := Ns540p1550 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.false 1180752584 132492 Bool.false 157471346 Bool.false 532256680 28296951008113761 1 Bool.false 513941794 Bool.false Bool.false 449251560 Bool.false Bool.false 1560369575 

noncomputable def Ns540p1552 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 943142 1000 371 237 536870912 268435456 9007199254740992 Bool.false 1015351120583 4491 

noncomputable def Ns540p1553 := Ns540p1552 744261104 56 268435448 8 864060384 56 240095976 8 Bool.false 1160765655 78190 Bool.false 537402660 Bool.false 553860898 28296951008113761 1 Bool.false 452048377 Bool.false Bool.false 460713293 Bool.true Bool.false 1180752584 

noncomputable def Ns540p1554 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 943142 1000 787 544 536870912 268435456 9007199254740992 Bool.false 1015351120583 4491 

noncomputable def Ns540p1555 := Ns540p1554 372130544 56 379625064 8 589812976 56 309962568 8 Bool.false 536870904 4560 Bool.false 690382962 Bool.false 310448818 28296951008113761 1 Bool.false 515235878 Bool.false Bool.false 449584903 Bool.false Bool.false 1160765655 

noncomputable def Ns540p1556 := nat_lit 1686015495535455926024257660765559178605937240160474078321 

noncomputable def Ns540p1557 := nat_lit 891487346972113214051861705185588383215013423218688000 

noncomputable def Ns540p1558 := nat_lit 358201147700023068414057142031360000 

noncomputable def Ns540p1559 := nat_lit 2027007546921852767927388652391501598720 

noncomputable abbrev qz770 := (@Eq.refl Real (Enclosure.sfrac Bool.false 943142 1000))

noncomputable abbrev qz693 := qz770

noncomputable abbrev qz518 := qz693

noncomputable abbrev qz224 := qz518

noncomputable def Ns540p1560 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz221 943142 1000 3558068328656 16000000 1886284 4000 2000 Ns540p1558 Ns540p1559 qz224 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns540p1561 := nat_lit 34529597348566137364976796892478651977849594678486509124014080 

noncomputable abbrev qz694 := (@HSub.hSub Real Real Real qz721 qz722 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz723 (@Nat.cast Real Real.instNatCast 1886284))))

noncomputable abbrev qz519 := (@HSub.hSub Real Real Real qz582 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 943142 4000) (Real.log (Enclosure.sfrac Bool.false 3558068328656 16000000))) (@HMul.hMul Real Real Real qz579 qz583 qz694))

noncomputable abbrev qz695 := (Enclosure.sfrac Bool.false 943142 2000)

noncomputable abbrev qz225 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz519 qz695) (@HMul.hMul Real Real Real qz355 qz695 (Real.log Real.pi)))

noncomputable def Ns540p1562 := @Enclosure.Real.IsNear.addLit_ft_p qz225 (Enclosure.sfrac Bool.true Ns540p1558 Ns540p1559) 17034766657574002529989 9007199254740992000 2123842267521678907 253952000000000000000000 Ns540p1558 Ns540p1559 0 1 Ns540p1561 

noncomputable def Ns540p1563 := nat_lit 4572735355579473222882750889984 

noncomputable abbrev qz226 := (@HSub.hSub Real Real Real qz361 qz519 qz695)

noncomputable def Ns540p1564 := @Enclosure.Real.IsNear.subLit_ff_p qz226 (@HMul.hMul Real Real Real qz5 qz695 (Real.log Real.pi)) 175176365665212090857 72057594037927936 191762748525667 62000000000000000000 18113400975531 33554432000 1414713 268435456000 Ns540p1563 17034766657574002529989 9007199254740992000 

noncomputable def Ns540p1565 := nat_lit 43794091416303022714250000 

noncomputable abbrev qz227 := qz519

noncomputable def Ns540p1566 := @Enclosure.Real.IsNear.subLit_ff_p qz227 qz695 26144579667908975695557 9007199254740992000 191762748525667 62000000000000000000 943142 2000 0 1 Ns540p1565 175176365665212090857 72057594037927936 191762748525667 62000000000000000000 

noncomputable def Ns540p1567 := nat_lit 58872359625076554500552087308270043136 

noncomputable def Ns540p1568 := nat_lit 119075707925411237845794816 

noncomputable def Ns540p1569 := nat_lit 144597972537727925468243225151900573925785431172221340235296338858148593117757179269042929268720965262857723773200939378218654993780185398230466115814146703360 

noncomputable def Ns540p1570 := nat_lit 3351837095295367048744879576053330141032533812641347256313039230763438165304460316908890016975454165306192568033159936245641131139789604062142174516888993792 

noncomputable def Ns540p1571 := nat_lit 982491071222451851120083276540422973010938010459503879931356533053978576711528047944502328669933490771971151371887056916085147861243799622034097438720 

noncomputable def Ns540p1572 := BSN.log_dyadic_bound 1460916328656 5655220328656 7 6 Ns540p1569 268435456 76880000 Ns540p1570 Ns540p1571 141905064 7116136657312 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1460916328656) (BSN.artanhQ 5655220328656) 0 6 Ns540p1570 Ns540p1569 Ns540p1571 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz520 := (Real.log (Enclosure.sfrac Bool.false 3558068328656 16000000))

noncomputable def Ns540p1573 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 943142 4000) qz520 943142 4000 0 1 55448947439627367 4503599627370496 12500016337 961000000000000000 26148115593052517083557 9007199254740992000 5894645204055427 1922000000000000000000 (Enclosure.Real.IsNear.const Bool.false 943142 4000) (BSN.isNear_log_sfrac 3558068328656 16000000 55448947439627367 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3558068328656) qz364)) Bool.false Ns540p1568 Ns540p114 1000001306960000 76880000000000000000000 55448947439627367 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3558068328656 16000000 17 7116136657312 4194304000000 141905064 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns540p1572 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p1574 := BSN.arctan_dyadic_bound_f 1000 1886284 1 0 33554432 9610000 0 1 1 0 1 1 17788 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1886284) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1886284) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns540p1575 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1886284))) 884279719003555 562949953421312 1 2000000000000000 17788 33554432 1 9610000 29661489946512435707904 883981285885347 562949953421312 200000000961 1922000000000000000 qz15 (Ns540p1574 rfl) rfl rfl 

noncomputable abbrev qz521 := (@HMul.hMul Real Real Real qz579 qz583 qz694)

noncomputable abbrev qz228 := qz521

noncomputable abbrev qz522 := qz694

noncomputable abbrev qz229 := qz522

noncomputable def Ns540p1576 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 943142 4000) qz520) qz228 26148115593052517083557 9007199254740992000 5894645204055427 1922000000000000000000 883981285885347 2251799813685248 200000000961 7688000000000000000 Ns540p1567 26144579667908975695557 9007199254740992000 191762748525667 62000000000000000000 (Ns540p1573 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz229 1 4 0 1 883981285885347 562949953421312 200000000961 1922000000000000000 883981285885347 2251799813685248 200000000961 7688000000000000000 qz372 Ns540p1575 rfl) 

noncomputable def Ns540p1577 := @Ns540p1562 Ns540p1556 Ns540p1557 2123842267521678907 253952000000000000000000 (@Ns540p1564 2123842267521678907 253952000000000000000000 (Ns540p1566 (Ns540p1576 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 943142 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz695 (Real.log Real.pi) 943142 2000 0 1 38410761 33554432 3 268435456 18113400975531 33554432000 1414713 268435456000 (Enclosure.Real.IsNear.const Bool.false 943142 2000) RS541to552.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns540p1558 Ns540p1559) 

noncomputable def Ns540p1578 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz221) Bool.false Ns540p1556 Ns540p1557 2123842267521678907 253952000000000000000000 15864861259 8388608 563 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz221) (@HAdd.hAdd Real Real Real qz373 qz225 (Enclosure.sfrac Bool.true Ns540p1558 Ns540p1559)) Bool.false Ns540p1556 Ns540p1557 2123842267521678907 253952000000000000000000 Ns540p1560 (Ns540p1577 rfl rfl)) 

noncomputable def Ns540p1579 := BSN.cos_dyadic_bound_f 8527543 137438953472 1 0 67108864 19238770 0 1 1 0 1 1 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 8527543) qz589 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 8527543) qz590 0 0 rfl) rfl rfl 

noncomputable def Ns540p1580 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz221) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15864861259) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 15864861259 8388608 563 67108864 Bool.false 67108863 67108864 1 9610000 (Ns540p1578 rfl) (Enclosure.sfrac_false_div 15864861259 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15864861259) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 75009068840452620288) (@Nat.cast Real Real.instNatCast Ns540p64)) 226375608064910080 72057594037927936 Bool.false 67108863 67108864 301 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q0 15864861259 8388608 226375608064910080 72057594037927936 301 75009068840452620288 Ns540p64 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108863 67108864 75009068840452620288 Ns540p64 8527543 137438953472 19238770 19220000 (Ns540p1579 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns540p1581 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz221) Bool.false Ns540p1556 Ns540p1557 2123842267521678907 253952000000000000000000 1015351120583 536870912 4491 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz221) (@HAdd.hAdd Real Real Real qz373 qz225 (Enclosure.sfrac Bool.true Ns540p1558 Ns540p1559)) Bool.false Ns540p1556 Ns540p1557 2123842267521678907 253952000000000000000000 Ns540p1560 (Ns540p1577 rfl rfl)) 

noncomputable def Ns540p1582 := Ns540p1555 78190 BSN.abs_quadSignPos (BSN.cos_quad_nat3 787 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 515235878 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 544 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 449584903 536870912) qz224 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 1) Bool.false 67108863 67108864 342346179 40307261440000 536870904 536870912 4560 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz221)) Bool.false 67108863 67108864 342346179 40307261440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz221) qz221) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz221)) Bool.false 67108863 67108864 5477538864 644916183040000 67108863 67108864 342346179 40307261440000 (Ns540p1580 rfl rfl) rfl)) rfl) (Ns540p1581 rfl) RS541to552.d7 

noncomputable def Ns540p1583 := nat_lit 81434967828954702890748854468693031889650162105625303696563448812811112764155956810980748058470156566811706003456 

noncomputable def Ns540p1584 := nat_lit 11724134129856667693093841752676402787912349555226564285426269407569071698574768414904297604095263965843456 

noncomputable def Ns540p1585 := nat_lit 406947385404077654279590913407407892413455671097704909984468028690520836545681896216517911511113181434191621001216 

noncomputable def Ns540p1586 := BSN.sin_dyadic_bound_f 690382962 536870912 4 3 536870912 268435456 Ns540p1583 Ns540p130 Ns540p1584 Ns540p1585 Ns540p133 Ns540p1584 515235878 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 690382962) qz376 0 3 Ns540p1583 Ns540p130 Ns540p1584 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 690382962) qz377 0 3 Ns540p1585 Ns540p133 Ns540p1584 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1587 := nat_lit 1296515533058245040704713166884988411767955140358812238407700535128473856 

noncomputable def Ns540p1588 := nat_lit 86281976525253404078754572858484323511322734361361789006784070533376 

noncomputable def Ns540p1589 := nat_lit 3889374035221684615305981991509248266656842775607713991645088037244354816 

noncomputable def Ns540p1590 := BSN.cos_dyadic_bound_f 310448818 536870912 3 2 536870912 268435456 Ns540p1587 Ns540p160 Ns540p1588 Ns540p1589 Ns540p163 Ns540p1588 449584903 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 310448818) qz19 0 2 Ns540p1587 Ns540p160 Ns540p1588 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 310448818) qz378 0 2 Ns540p1589 Ns540p163 Ns540p1588 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1591 := nat_lit 20960647414158122872794085384637182745672018074791642671767396452311040000 

noncomputable def Ns540p1592 := nat_lit 6956623411095996256042294559504290828100131987678579359739929600000000 

noncomputable def Ns540p1593 := nat_lit 54885670599177118768141393244762947863038361410759965488046459393843200000 

noncomputable def Ns540p1594 := BSN.sin_dyadic_bound_f 537402660 536870912 3 2 536870912 268435456 Ns540p1591 Ns540p276 Ns540p1592 Ns540p1593 Ns540p279 Ns540p1592 452048377 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 537402660) qz376 0 2 Ns540p1591 Ns540p276 Ns540p1592 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 537402660) qz377 0 2 Ns540p1593 Ns540p279 Ns540p1592 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1595 := nat_lit 23649760784883753908166121220569160017622937325969748176455004479546753280 

noncomputable def Ns540p1596 := nat_lit 8855348225360686455255283135445645542088688508226909807842012345958656 

noncomputable def Ns540p1597 := nat_lit 61925512444235438171888475595461840429563358929478877846264696093109944576 

noncomputable def Ns540p1598 := BSN.sin_dyadic_bound_f 553860898 536870912 3 2 536870912 268435456 Ns540p1595 Ns540p276 Ns540p1596 Ns540p1597 Ns540p279 Ns540p1596 460713293 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 553860898) qz376 0 2 Ns540p1595 Ns540p276 Ns540p1596 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 553860898) qz377 0 2 Ns540p1597 Ns540p279 Ns540p1596 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1599 := Ns540p1553 132492 BSN.abs_quadSignPos (BSN.cos_quad_nat3 371 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 452048377 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 237 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 460713293 536870912) qz224 rfl rfl (Ns540p1582 RS541to552.d9 RS541to552.d11 RS541to552.d13 RS541to552.d17 (Ns540p1586 rfl rfl) (Ns540p1590 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns540p1581 rfl) RS541to552.d19 RS541to552.d21 RS541to552.d23 RS541to552.d25 RS541to552.d17 (Ns540p1594 rfl rfl) (Ns540p1598 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns540p1600 := nat_lit 85821648188360210115379623136056169760304027510766844898398671557673216 

noncomputable def Ns540p1601 := nat_lit 378104910279597490967691265345740625999799358433804538666762158336 

noncomputable def Ns540p1602 := nat_lit 257464188355260071151156934025637817799660082933583667086118681148702976 

noncomputable def Ns540p1603 := BSN.cos_dyadic_bound_f 157471346 536870912 3 2 536870912 268435456 Ns540p1600 Ns540p160 Ns540p1601 Ns540p1602 Ns540p163 Ns540p1601 513941794 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 157471346) qz19 0 2 Ns540p1600 Ns540p160 Ns540p1601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 157471346) qz378 0 2 Ns540p1602 Ns540p163 Ns540p1601 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1604 := nat_lit 20169005587920345016621512956815836711800898660735870329737863642480640000 

noncomputable def Ns540p1605 := nat_lit 6441232350798950574100271617397281754096531767301149393164697600000000 

noncomputable def Ns540p1606 := nat_lit 52813157401699610075936371589994262455686197345732601383629280981811200000 

noncomputable def Ns540p1607 := BSN.sin_dyadic_bound_f 532256680 536870912 3 2 536870912 268435456 Ns540p1604 Ns540p276 Ns540p1605 Ns540p1606 Ns540p279 Ns540p1605 449251560 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 532256680) qz376 0 2 Ns540p1604 Ns540p276 Ns540p1605 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 532256680) qz377 0 2 Ns540p1606 Ns540p279 Ns540p1605 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1608 := Ns540p1551 178309 BSN.abs_quadSignPos (BSN.cos_quad_nat0 128 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 513941794 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 449251560 536870912) qz224 rfl rfl (Ns540p1599 rfl rfl) (Ns540p1581 rfl) RS541to552.d27 RS541to552.d29 RS541to552.d31 RS541to552.d33 RS541to552.d17 (Ns540p1603 rfl rfl) (Ns540p1607 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1609 := nat_lit 6191750249455742231650083018506564655387046835804397065787392167668690625 

noncomputable def Ns540p1610 := nat_lit 1966859532718287258119855828850060939276195978271284508348891687890625 

noncomputable def Ns540p1611 := nat_lit 18571317029301790120434009343861993844282588115456648628345478719630290625 

noncomputable def Ns540p1612 := BSN.cos_dyadic_bound_f 458903815 536870912 3 2 536870912 268435456 Ns540p1609 Ns540p160 Ns540p1610 Ns540p1611 Ns540p163 Ns540p1610 352395784 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 458903815) qz19 0 2 Ns540p1609 Ns540p160 Ns540p1610 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 458903815) qz378 0 2 Ns540p1611 Ns540p163 Ns540p1610 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1613 := nat_lit 615134217649340281329647203044069622716949794111353065212086516076052480 

noncomputable def Ns540p1614 := nat_lit 5995269889487041901389089194720217386131168431573193289345815085056 

noncomputable def Ns540p1615 := nat_lit 1611056101501784424462188044685295655335290962685606909432996220308094976 

noncomputable def Ns540p1616 := BSN.sin_dyadic_bound_f 222446764 536870912 3 2 536870912 268435456 Ns540p1613 Ns540p276 Ns540p1614 Ns540p1615 Ns540p279 Ns540p1614 216136339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 222446764) qz376 0 2 Ns540p1613 Ns540p276 Ns540p1614 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 222446764) qz377 0 2 Ns540p1615 Ns540p279 Ns540p1614 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1617 := Ns540p1549 218340 BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 352395784 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 216136339 536870912) qz224 rfl rfl (Ns540p1608 rfl) (Ns540p1581 rfl) RS541to552.d35 RS541to552.d37 RS541to552.d39 RS541to552.d41 RS541to552.d17 (Ns540p1612 rfl rfl) (Ns540p1616 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1618 := nat_lit 5349921846270328707830756711297166203876679264680838148941072786270359361 

noncomputable def Ns540p1619 := nat_lit 1468516611615218044199891614275757666457939246887038136519227426639681 

noncomputable def Ns540p1620 := nat_lit 16046828505587755687403870350662947096297121915548740370550179903957798721 

noncomputable def Ns540p1621 := BSN.cos_dyadic_bound_f 442445577 536870912 3 2 536870912 268435456 Ns540p1618 Ns540p160 Ns540p1619 Ns540p1620 Ns540p163 Ns540p1619 364644741 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 442445577) qz19 0 2 Ns540p1618 Ns540p160 Ns540p1619 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 442445577) qz378 0 2 Ns540p1620 Ns540p163 Ns540p1619 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1622 := nat_lit 57676067782383193850310089343536048591222800838181823753035192428260998521137710375045257851090864877775847341601 

noncomputable def Ns540p1623 := nat_lit 4168485180867128139779078663267221524763286209905913499132167223964065115512542966087756586065435629895201 

noncomputable def Ns540p1624 := nat_lit 288266191702814938765100269290171325002522380493488614148521692249445757676694074653866559260508826937976819465761 

noncomputable def Ns540p1625 := BSN.sin_dyadic_bound_f 633380743 536870912 4 3 536870912 268435456 Ns540p1622 Ns540p130 Ns540p1623 Ns540p1624 Ns540p133 Ns540p1623 496345707 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 633380743) qz376 0 3 Ns540p1622 Ns540p130 Ns540p1623 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 633380743) qz377 0 3 Ns540p1624 Ns540p133 Ns540p1623 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1626 := Ns540p1547 254343 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 178 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 364644741 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 235 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 496345707 536870912) qz224 rfl rfl (Ns540p1617 rfl) (Ns540p1581 rfl) RS541to552.d43 RS541to552.d45 RS541to552.d47 RS541to552.d49 RS541to552.d17 (Ns540p1621 rfl rfl) (Ns540p1625 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1627 := nat_lit 177661952352408548241726300401836254422202529830930181423616878873726787170039946956435986755127027971228868684561 

noncomputable def Ns540p1628 := nat_lit 121350940500022889664894342870260825374028887947319851572778613986033389032467585501315514725547357046450961 

noncomputable def Ns540p1629 := nat_lit 887229223252414721869261505420029254273541534216125967171869181996674023439894363817911365635761622153955664603921 

noncomputable def Ns540p1630 := BSN.sin_dyadic_bound_f 838822869 536870912 4 3 536870912 268435456 Ns540p1627 Ns540p130 Ns540p1628 Ns540p1629 Ns540p133 Ns540p1628 536852119 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 838822869) qz376 0 3 Ns540p1627 Ns540p130 Ns540p1628 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 838822869) qz377 0 3 Ns540p1629 Ns540p133 Ns540p1628 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1631 := Ns540p1545 Bool.false 1791348805 254343 Bool.true 838822869 28296951008113761 1 Bool.false 536852119 Bool.false Bool.false 1946324667 271169 BSN.abs_quadSignPos (BSN.cos_quad_nat3 287 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536852119 536870912) qz224 rfl (Ns540p1626 rfl) (Ns540p1581 rfl) RS541to552.d51 RS541to552.d53 RS541to552.d17 (Ns540p1630 rfl rfl) rfl 

noncomputable def Ns540p1632 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 12) 1946324667 536870912 271169 536870912 1946324667 536870912 271169 536870912 2089850198040772608 1946324667 268435456 271169 268435456 (Ns540p1631 rfl rfl rfl rfl) 

noncomputable def Ns540p1633 := @Enclosure.Real.IsNear.mulLit_ff qz692 (Zeta.RiemannSiegel.correction qz223) 19172581 67108864 1 67108864 70121734172441 140737488355328 28602047559114149 42265226971709440000 1344414628281593040221 9444732965739290427392 

noncomputable abbrev qz696 := (@HPow.hPow Real Real Real qz152 qz222 qz154)

noncomputable def Ns540p1634 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz696 1 1 0 1 19172581 67108864 1 67108864 19172581 67108864 1 67108864 

noncomputable def Ns540p1635 := @Enclosure.Real.IsNear.sqrt_image qz222 5036711680697 33554432000 471571 33554432000 411100941 411100980 33554432 (@Enclosure.Real.IsNear.of_eq qz222 (@HMul.hMul Real Real Real qz5 qz221 qz3) Bool.false 5036711680697 33554432000 471571 33554432000 (BSN.t_div_two_pi_mk qz221 943142 1000 qz224) (@Enclosure.Real.IsNear.mulLit_ff qz221 qz3 943142 1000 0 1 10680707 67108864 1 67108864 5036711680697 33554432000 471571 33554432000 (Enclosure.Real.IsNear.const Bool.false 943142 1000) RS541to552.d56 rfl)) 

noncomputable abbrev qz771 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 943142 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz697 := qz771

noncomputable abbrev qz523 := qz697

noncomputable abbrev qz230 := qz523

noncomputable def Ns540p1636 := @Enclosure.Real.IsNear.sqrt_image qz230 822201921 67108864 39 67108864 117448961 117448968 33554432 (@Enclosure.Real.IsNear.recentre' qz230 Bool.false 822201921 67108864 39 67108864 822201921 67108864 39 67108864 (Ns540p1635 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns540p1637 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz230) 234897929 67108864 7 67108864 9586290 9586291 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz230) Bool.false 234897929 67108864 7 67108864 234897929 67108864 7 67108864 (Ns540p1636 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns540p1638 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz230)) Bool.false 19172581 67108864 1 67108864 19172581 67108864 1 67108864 (Ns540p1637 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz524 := (@HMul.hMul Real Real Real qz579 qz577 qz691)

noncomputable abbrev qz231 := (Real.cos qz524)

noncomputable abbrev qz698 := (@HMul.hMul Real Real Real qz717 qz769 qz769)

noncomputable abbrev qz525 := (@HSub.hSub Real Real Real qz582 (@HSub.hSub Real Real Real qz582 qz698 qz691) qz594)

noncomputable abbrev qz232 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz525))

noncomputable def Ns540p1639 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz223) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz231) qz232) Bool.false 70121734172441 

noncomputable def Ns540p1640 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz231) qz232 378571883 4194304 515239 

noncomputable abbrev qz233 := (@Neg.neg Real Real.instNeg (Real.cos qz524))

noncomputable def Ns540p1641 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz231) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz233)) Bool.true 378571883 4194304 515239 16777216 (BSN.inv_eq_neg_inv_neg qz231) 

noncomputable def Ns540p1642 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz233) Bool.false 6057150128 67108864 2060956 67108864 378571883 4194304 

noncomputable def Ns540p1643 := @Enclosure.Real.IsNear.recentre' qz231 Bool.true 371759 33554432 1215584432 322458091520000 371759 33554432 75974027 20153630720000 

noncomputable abbrev qz234 := qz524

noncomputable def Ns540p1644 := @Enclosure.Real.IsNear.cos_image qz234 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 53078945) qz384) Bool.false 53078945 33554432 123 33554432 Bool.true 371759 33554432 1 

noncomputable def Ns540p1645 := nat_lit 1052456941097849467917259089 

noncomputable def Ns540p1646 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz223 884279719003555 140737488355328 1 500000000000000 16895553 67108864 39 67108864 14940394859249670690915 9444732965739290427392 Ns540p1645 

noncomputable def Ns540p1647 := @Enclosure.Real.IsNear.subLit_ff_p qz230 qz1 822201921 67108864 39 67108864 12 1 0 1 16895553 16895553 67108864 39 

noncomputable def Ns540p1648 := @Ns540p1647 67108864 (@Enclosure.Real.IsNear.recentre' qz230 Bool.false 822201921 67108864 39 67108864 822201921 67108864 39 67108864 (Ns540p1635 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns540p1649 := @Enclosure.Real.IsNear.recentre' qz234 Bool.false 14940394859249670690915 9444732965739290427392 Ns540p1645 Ns540p333 53078945 33554432 123 33554432 (@Ns540p1646 Ns540p333 RS541to552.d55 (Ns540p1648 rfl rfl) rfl) 

noncomputable def Ns540p1650 := nat_lit 255523306307296361572344304826758110055567502074515483331478688370460641505504268487694987746890625 

noncomputable def Ns540p1651 := nat_lit 500112128055921504287259373287986859466482212644322782248938956677350588842056047636962890625 

noncomputable def Ns540p1652 := nat_lit 1546334649052962719832331768386933408188249820620725544340201298951662592927616131938312080252490625 

noncomputable def Ns540p1653 := BSN.cos_dyadic_bound_t 53078945 33554432 4 3 33554432 9610000 Ns540p1650 Ns540p354 Ns540p1651 Ns540p1652 Ns540p357 Ns540p1651 371759 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 53078945) qz595 0 3 Ns540p1650 Ns540p354 Ns540p1651 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 53078945) (BSN.cosOddQ 33554432) 0 3 Ns540p1652 Ns540p357 Ns540p1651 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1654 := @Enclosure.Real.IsNear.inv_image qz233 371759 33554432 75974027 20153630720000 3027544586 3029605542 33554432 (@Enclosure.Real.IsNear.neg qz231 Bool.true 371759 33554432 75974027 20153630720000 (Ns540p1643 (@Ns540p1644 9610000 (Ns540p1649 rfl) (Enclosure.sfrac_false_div 53078945 33554432) (Ns540p1653 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns540p1655 := Ns540p1641 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz233) Bool.false 378571883 4194304 515239 16777216 (@Ns540p1642 515239 16777216 (Ns540p1654 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p1656 := @Enclosure.Real.IsNear.recentre' qz232 Bool.true 185227 33554432 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz355 qz352 qz525)

noncomputable def Ns540p1657 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 26446203)) qz616) Bool.true 26446203 16777216 

noncomputable def Ns540p1658 := nat_lit 999109306842536016578370151645 

noncomputable def Ns540p1659 := nat_lit 21238582964789417285927113611136741 

noncomputable def Ns540p1660 := @Enclosure.Real.IsNear.recentre' qz235 Bool.true Ns540p1658 Ns540p210 Ns540p1659 

noncomputable abbrev qz236 := qz525

noncomputable def Ns540p1661 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz236 884279719003555 140737488355328 1 500000000000000 1129856634016639 

noncomputable abbrev qz526 := (@HSub.hSub Real Real Real qz582 qz698 qz691)

noncomputable abbrev qz237 := qz526

noncomputable def Ns540p1662 := @Enclosure.Real.IsNear.subLit_tf qz237 qz30 848381657305983 4503599627370496 3935100351 4503599627370496 1 16 

noncomputable abbrev qz527 := qz698

noncomputable abbrev qz238 := qz527

noncomputable def Ns540p1663 := @Enclosure.Real.IsNear.subLit_ff_n qz238 qz223 285459711175809 4503599627370496 1317854655 4503599627370496 16895553 67108864 39 67108864 

noncomputable def Ns540p1664 := @Enclosure.Real.IsNear.mulLit_ff qz223 qz223 16895553 67108864 39 67108864 16895553 67108864 39 67108864 285459711175809 4503599627370496 

noncomputable def Ns540p1665 := nat_lit 61508078212331618058963853698996215048836953382523579762628834006707207701363868746053369815121 

noncomputable def Ns540p1666 := nat_lit 117046902973251797019394797357542229956185518724150155192504578963962324343025046039388241 

noncomputable def Ns540p1667 := nat_lit 372237534049649871506348785356589722235496501620381516622211260608740822401166348386827533901905 

noncomputable def Ns540p1668 := BSN.cos_dyadic_bound_t 26446203 16777216 4 3 33554432 9610000 Ns540p1665 Ns540p519 Ns540p1666 Ns540p1667 Ns540p522 Ns540p1666 185227 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 26446203) (BSN.cosEvenQ 16777216) 0 3 Ns540p1665 Ns540p519 Ns540p1666 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 26446203) (BSN.cosOddQ 16777216) 0 3 Ns540p1667 Ns540p522 Ns540p1666 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1669 := @Ns540p1656 1811404432 322458091520000 185227 33554432 113212777 20153630720000 (@Ns540p1657 185 33554432 Bool.true 185227 33554432 1 9610000 (@Ns540p1660 Ns540p348 26446203 16777216 185 33554432 (@Ns540p1661 4503599627370496 3935100351 4503599627370496 Ns540p1658 Ns540p210 Ns540p1659 Ns540p348 RS541to552.d55 (@Ns540p1662 0 1 18077706144266224 1129856634016639 4503599627370496 3935100351 4503599627370496 (@Ns540p1663 56933929260241819533312 848381657305983 4503599627370496 3935100351 4503599627370496 (@Ns540p1664 1317854655 4503599627370496 (Ns540p1648 rfl rfl) (Ns540p1648 rfl rfl) rfl) (Ns540p1648 rfl rfl) rfl rfl) qz389 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 26446203 16777216) (BSN.cos_neg_of_bound 26446203 16777216 Bool.true 185227 33554432 1 9610000 (Ns540p1668 rfl rfl)) rfl rfl) 

noncomputable def Ns540p1670 := @Ns540p1633 1096792321256619060501061 Ns540p1542 (Ns540p1634 qz32 (@Enclosure.Real.IsNear.of_eq qz696 (@Inv.inv Real Real.instInv (Real.sqrt qz230)) Bool.false 19172581 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz222 (BSN.t_div_two_pi_nonneg qz221 943142 1000 qz224)) Ns540p1638) rfl) (@Ns540p1639 140737488355328 28602047559114149 42265226971709440000 (BSN.correction_mk qz223 (BSN.cos_two_pi_p_ne_zero_mk qz221 943142 1000 12 qz224 rfl rfl (@BSN.floor_sqrt_eq_dec qz221 943142 1000 12 qz224 rfl rfl rfl))) (@Ns540p1640 16777216 185227 33554432 113212777 20153630720000 70121734172441 140737488355328 28602047559114149 42265226971709440000 Ns540p1655 (Ns540p1669 rfl) rfl)) 

noncomputable def Ns540p1671 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz221) (hardyZApproximantRS₀ qz221) Bool.false 67135796661118443778723 9444732965739290427392 Ns540p1541 Ns540p1542 (@Eq.refl Real (hardyZApproximantRS₀ qz221)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz221) (@HSub.hSub Real Real Real qz33 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz221) qz221 12) (@HMul.hMul Real Real Real qz5 qz692 (Zeta.RiemannSiegel.correction qz223))) Bool.false 67135796661118443778723 9444732965739290427392 Ns540p1541 Ns540p1542 (BSN.hardyZApproximantRS₀_eq qz221 12 (@BSN.floor_sqrt_eq_dec qz221 943142 1000 12 qz224 rfl rfl rfl)) (@Ns540p1544 67135796661118443778723 9444732965739290427392 Ns540p1541 Ns540p1542 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz221) qz221 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 12)) Bool.false 1946324667 268435456 271169 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz221) qz221 12) (Ns540p1632 (Ns540p1631 rfl rfl rfl rfl) rfl rfl)) (Ns540p1670 rfl) rfl rfl)) 

theorem RS541to552.d70 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz221) Bool.false 67135796661118443778723 9444732965739290427392 Ns540p1541 Ns540p1542 := Ns540p1671 

noncomputable def Ns540p1672 := nat_lit 11877483121728884608592669 

noncomputable def Ns540p1673 := nat_lit 6510926019426839762088950235136 

noncomputable abbrev qz772 := (Enclosure.sfrac Bool.false 944396 1000)

noncomputable abbrev qz699 := qz772

noncomputable abbrev qz528 := qz699

noncomputable abbrev qz239 := qz528

noncomputable abbrev qz773 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 944396 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz700 := qz773

noncomputable abbrev qz529 := qz700

noncomputable abbrev qz240 := qz529

noncomputable abbrev qz774 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 944396 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz701 := qz774

noncomputable abbrev qz530 := qz701

noncomputable abbrev qz241 := qz530

noncomputable abbrev qz702 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz152 qz240 qz154))

noncomputable def Ns540p1674 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz239) qz239 12) (@HMul.hMul Real Real Real qz5 qz702 (Zeta.RiemannSiegel.correction qz241)) 307094083 268435456 271523 268435456 2645264569072738812669 18889465931478580854784 401501898689422331472669 Ns540p789 Ns540p1673 

noncomputable def Ns540p1675 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.sin BSN.quadSignPos 11 12 944396 1000 287 536870912 268435456 9007199254740992 Bool.false 1017038251589 4497 1334074092 57 154981288 8 

noncomputable def Ns540p1676 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 944396 1000 178 235 536870912 268435456 9007199254740992 Bool.false 1017038251589 4497 

noncomputable def Ns540p1677 := Ns540p1676 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 458902982 218624 Bool.true 305498030 Bool.true 560599452 28296951008113761 1 Bool.false 452271673 Bool.true Bool.false 464136531 Bool.false Bool.true 461981425 

noncomputable def Ns540p1678 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 944396 1000 44 115 536870912 268435456 9007199254740992 Bool.false 1017038251589 4497 

noncomputable def Ns540p1679 := Ns540p1678 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 643942597 178540 Bool.true 171727971 Bool.true 14566697 28296951008113761 1 Bool.false 509639126 Bool.false Bool.false 14564909 Bool.false Bool.true 458902982 

noncomputable def Ns540p1680 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 944396 1000 128 36 536870912 268435456 9007199254740992 Bool.false 1017038251589 4497 

noncomputable def Ns540p1681 := Ns540p1680 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 926996619 132662 Bool.false 638325161 Bool.false 66015843 28296951008113761 1 Bool.false 200045008 Bool.false Bool.false 532817234 Bool.false Bool.true 643942597 

noncomputable def Ns540p1682 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 944396 1000 372 238 536870912 268435456 9007199254740992 Bool.false 1017038251589 4497 

noncomputable def Ns540p1683 := Ns540p1682 744261104 56 268435448 8 864060384 56 240095976 8 Bool.true 907150088 78288 Bool.false 447915385 Bool.false 314145326 28296951008113761 1 Bool.false 360611321 Bool.false Bool.false 447553883 Bool.true Bool.true 926996619 

noncomputable def Ns540p1684 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz239) qz239 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 944396 1000 789 545 536870912 268435456 9007199254740992 Bool.false 1017038251589 4497 

noncomputable def Ns540p1685 := Ns540p1684 372130544 56 379625064 8 589812976 56 309962568 8 Bool.true 536870640 4560 Bool.false 224232553 Bool.false 414639496 28296951008113761 1 Bool.false 217769820 Bool.true Bool.false 374630342 Bool.true Bool.true 907150088 

noncomputable def Ns540p1686 := nat_lit 1662436099889779291033973740619078179481093101748477029 

noncomputable def Ns540p1687 := nat_lit 877561471945275987067840912319735815298516779008000 

noncomputable def Ns540p1688 := nat_lit 360588806022495212747470990868480000 

noncomputable def Ns540p1689 := nat_lit 2043232023588558628847452142088990228480 

noncomputable abbrev qz775 := (@Eq.refl Real (Enclosure.sfrac Bool.false 944396 1000))

noncomputable abbrev qz703 := qz775

noncomputable abbrev qz531 := qz703

noncomputable abbrev qz242 := qz531

noncomputable def Ns540p1690 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz239 944396 1000 3567536219264 16000000 1888792 4000 2000 Ns540p1688 Ns540p1689 qz242 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns540p1691 := nat_lit 17431905958780252098752400490433905211275666802590110491607040 

noncomputable abbrev qz704 := (@HSub.hSub Real Real Real qz721 qz722 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz723 (@Nat.cast Real Real.instNatCast 1888792))))

noncomputable abbrev qz532 := (@HSub.hSub Real Real Real qz582 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 944396 4000) (Real.log (Enclosure.sfrac Bool.false 3567536219264 16000000))) (@HMul.hMul Real Real Real qz579 qz583 qz704))

noncomputable abbrev qz705 := (Enclosure.sfrac Bool.false 944396 2000)

noncomputable abbrev qz243 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz532 qz705) (@HMul.hMul Real Real Real qz355 qz705 (Real.log Real.pi)))

noncomputable def Ns540p1692 := @Enclosure.Real.IsNear.addLit_ft_p qz243 (Enclosure.sfrac Bool.true Ns540p1688 Ns540p1689) 8531536008383398071173 4503599627370496000 32963188780284025973 Ns540p413 Ns540p1688 Ns540p1689 0 1 Ns540p1691 

noncomputable def Ns540p1693 := nat_lit 143135422424426080254052794368000 

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz361 qz532 qz705)

noncomputable def Ns540p1694 := @Enclosure.Real.IsNear.subLit_ff_p qz244 (@HMul.hMul Real Real Real qz5 qz705 (Real.log Real.pi)) 10965907972652403706757 4503599627370496000 186015084829343 60062500000000000000 9068742261339 16777216000 708297 134217728000 Ns540p1693 8531536008383398071173 4503599627370496000 

noncomputable def Ns540p1695 := nat_lit 4386363189060961482702800 

noncomputable abbrev qz245 := qz532

noncomputable def Ns540p1696 := @Enclosure.Real.IsNear.subLit_ff_p qz245 qz705 2618499741899499435393 900719925474099200 186015084829343 60062500000000000000 944396 2000 0 1 Ns540p1695 10965907972652403706757 4503599627370496000 186015084829343 60062500000000000000 

noncomputable def Ns540p1697 := nat_lit 5896337230944162804548711170613182464 

noncomputable def Ns540p1698 := nat_lit 119101408995707121754439680 

noncomputable def Ns540p1699 := nat_lit 71010613871926202724469514972229619758619770183908556441165235655807722660642055850463281644157485064171197302009021174946281093262928746768136761130058548069333722939609867356628582400 

noncomputable def Ns540p1700 := nat_lit 1662567049000434741980423933727546940456462808508030068581505240320445334656604861371437952466194746976999667238178473705247805407388092795362321892115723651466578486026140260960829440 

noncomputable def Ns540p1701 := nat_lit 29840047400238486897455460243780501339204937752196364249722247926622174452821424675546988593197595571228097494813342615983812923010615100568015305525321927971985821060468572160 

noncomputable def Ns540p1702 := BSN.log_dyadic_bound 1470384219264 5664688219264 8 7 Ns540p1699 268435456 76880000 Ns540p1700 Ns540p1701 142618412 7135072438528 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1470384219264) (BSN.artanhQ 5664688219264) 0 7 Ns540p1700 Ns540p1699 Ns540p1701 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz533 := (Real.log (Enclosure.sfrac Bool.false 3567536219264 16000000))

noncomputable def Ns540p1703 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 944396 4000) qz533 944396 4000 0 1 55460915433106535 4503599627370496 12500016337 961000000000000000 2618853334568203961393 900719925474099200 2951241357149363 961000000000000000000 (Enclosure.Real.IsNear.const Bool.false 944396 4000) (BSN.isNear_log_sfrac 3567536219264 16000000 55460915433106535 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3567536219264) qz364)) Bool.false Ns540p1698 Ns540p114 1000001306960000 76880000000000000000000 55460915433106535 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3567536219264 16000000 17 7135072438528 4194304000000 142618412 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns540p1702 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p1704 := BSN.arctan_dyadic_bound_f 1000 1888792 1 0 33554432 9610000 0 1 1 0 1 1 17765 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1888792) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1888792) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns540p1705 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1888792))) 884279719003555 562949953421312 1 2000000000000000 17765 33554432 1 9610000 29661502894361364398080 883981671761315 562949953421312 200000000961 1922000000000000000 qz15 (Ns540p1704 rfl) rfl rfl 

noncomputable abbrev qz534 := (@HMul.hMul Real Real Real qz579 qz583 qz704)

noncomputable abbrev qz246 := qz534

noncomputable abbrev qz535 := qz704

noncomputable abbrev qz247 := qz535

noncomputable def Ns540p1706 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 944396 4000) qz533) qz246 2618853334568203961393 900719925474099200 2951241357149363 961000000000000000000 883981671761315 2251799813685248 200000000961 7688000000000000000 Ns540p1697 2618499741899499435393 900719925474099200 186015084829343 60062500000000000000 (Ns540p1703 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz247 1 4 0 1 883981671761315 562949953421312 200000000961 1922000000000000000 883981671761315 2251799813685248 200000000961 7688000000000000000 qz372 Ns540p1705 rfl) 

noncomputable def Ns540p1707 := @Ns540p1692 Ns540p1686 Ns540p1687 32963188780284025973 Ns540p413 (@Ns540p1694 32963188780284025973 Ns540p413 (Ns540p1696 (Ns540p1706 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 944396 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz705 (Real.log Real.pi) 944396 2000 0 1 38410761 33554432 3 268435456 9068742261339 16777216000 708297 134217728000 (Enclosure.Real.IsNear.const Bool.false 944396 2000) RS541to552.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns540p1688 Ns540p1689) 

noncomputable def Ns540p1708 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz239) Bool.false Ns540p1686 Ns540p1687 32963188780284025973 Ns540p413 15891222681 8388608 563 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz239) (@HAdd.hAdd Real Real Real qz373 qz243 (Enclosure.sfrac Bool.true Ns540p1688 Ns540p1689)) Bool.false Ns540p1686 Ns540p1687 32963188780284025973 Ns540p413 Ns540p1690 (Ns540p1707 rfl rfl)) 

noncomputable def Ns540p1709 := BSN.cos_dyadic_bound_f 136859047 137438953472 1 0 67108864 19238770 0 1 1 0 1 1 67108830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 136859047) qz589 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 136859047) qz590 0 0 rfl) rfl rfl 

noncomputable def Ns540p1710 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz239) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15891222681) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 15891222681 8388608 563 67108864 Bool.true 67108830 67108864 1 9610000 (Ns540p1708 rfl) (Enclosure.sfrac_false_div 15891222681 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15891222681) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1203824909506672852992) (@Nat.cast Real Real.instNatCast Ns540p64)) 226375608064910080 72057594037927936 Bool.false 67108830 67108864 301 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q2 15891222681 8388608 226375608064910080 72057594037927936 301 1203824909506672852992 Ns540p64 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108830 67108864 1203824909506672852992 Ns540p64 136859047 137438953472 19238770 19220000 (Ns540p1709 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns540p1711 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz239) Bool.false Ns540p1686 Ns540p1687 32963188780284025973 Ns540p413 1017038251589 536870912 4497 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz239) (@HAdd.hAdd Real Real Real qz373 qz243 (Enclosure.sfrac Bool.true Ns540p1688 Ns540p1689)) Bool.false Ns540p1686 Ns540p1687 32963188780284025973 Ns540p413 Ns540p1690 (Ns540p1707 rfl rfl)) 

noncomputable def Ns540p1712 := Ns540p1685 78288 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 789 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 217769820 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 545 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 374630342 536870912) qz242 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 1) Bool.true 33554415 33554432 342346179 40307261440000 536870640 536870912 4560 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz239)) Bool.true 33554415 33554432 342346179 40307261440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz239) qz239) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz239)) Bool.true 67108830 67108864 5477538864 644916183040000 33554415 33554432 342346179 40307261440000 (Ns540p1710 rfl rfl) rfl)) rfl) (Ns540p1711 rfl) RS541to552.d7 

noncomputable def Ns540p1713 := nat_lit 635126598039239361360602070254218844702665865157467381567952078863290945 

noncomputable def Ns540p1714 := nat_lit 6391301318790713953530520289388863598335020568777197511563866231361 

noncomputable def Ns540p1715 := nat_lit 1663416456567301237645652086966295106537346628236255598167712912668054081 

noncomputable def Ns540p1716 := BSN.sin_dyadic_bound_f 224232553 536870912 3 2 536870912 268435456 Ns540p1713 Ns540p276 Ns540p1714 Ns540p1715 Ns540p279 Ns540p1714 217769820 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 224232553) qz376 0 2 Ns540p1713 Ns540p276 Ns540p1714 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 224232553) qz377 0 2 Ns540p1715 Ns540p279 Ns540p1714 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1717 := nat_lit 7426685802839117445275511123479322910980413366861464301919771604780318720 

noncomputable def Ns540p1718 := nat_lit 873706051049441103657655365971155568645699713003110803708261523521536 

noncomputable def Ns540p1719 := nat_lit 19449429197638846594887083405186654324504227685101830039917207493862752256 

noncomputable def Ns540p1720 := BSN.sin_dyadic_bound_f 414639496 536870912 3 2 536870912 268435456 Ns540p1717 Ns540p276 Ns540p1718 Ns540p1719 Ns540p279 Ns540p1718 374630342 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 414639496) qz376 0 2 Ns540p1717 Ns540p276 Ns540p1718 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 414639496) qz377 0 2 Ns540p1719 Ns540p279 Ns540p1718 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1721 := nat_lit 5619503299986999004706970222954151753694145712923467027084943555012690625 

noncomputable def Ns540p1722 := nat_lit 1620197056387915266697847447879570581167662146515389971725757687890625 

noncomputable def Ns540p1723 := nat_lit 16855269505848221183587514973966696119920101814477370301311379149662290625 

noncomputable def Ns540p1724 := BSN.cos_dyadic_bound_f 447915385 536870912 3 2 536870912 268435456 Ns540p1721 Ns540p160 Ns540p1722 Ns540p1723 Ns540p163 Ns540p1722 360611321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 447915385) qz19 0 2 Ns540p1721 Ns540p160 Ns540p1722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 447915385) qz378 0 2 Ns540p1723 Ns540p163 Ns540p1722 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1725 := nat_lit 1359381930542691498973774907964200558158282129925516757401461559499571456 

noncomputable def Ns540p1726 := nat_lit 94851634629517747195843204764887179769385232684611110835306491166976 

noncomputable def Ns540p1727 := nat_lit 4077956088358815461426933037483071900115307619311181049982714065516380416 

noncomputable def Ns540p1728 := BSN.cos_dyadic_bound_f 314145326 536870912 3 2 536870912 268435456 Ns540p1725 Ns540p160 Ns540p1726 Ns540p1727 Ns540p163 Ns540p1726 447553883 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 314145326) qz19 0 2 Ns540p1725 Ns540p160 Ns540p1726 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 314145326) qz378 0 2 Ns540p1727 Ns540p163 Ns540p1726 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1729 := Ns540p1683 132662 BSN.abs_quadSignPos (BSN.cos_quad_nat0 372 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 360611321 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 447553883 536870912) qz242 rfl rfl (Ns540p1712 RS541to552.d9 RS541to552.d11 RS541to552.d13 RS541to552.d17 (Ns540p1716 rfl rfl) (Ns540p1720 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns540p1711 rfl) RS541to552.d19 RS541to552.d21 RS541to552.d23 RS541to552.d25 RS541to552.d17 (Ns540p1724 rfl rfl) (Ns540p1728 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns540p1730 := nat_lit 22896492634018098944384683906937561057112826792298044137375029238464800731419750147974748844021034176057905916001 

noncomputable def Ns540p1731 := nat_lit 4576184874883066755249535503698956435489207218707120265757548760415682604933266805724000971320679163111521 

noncomputable def Ns540p1732 := nat_lit 138795340677686938225981764919165594763826599102252426479980270088540616879283123349843293047873460023269477460065 

noncomputable def Ns540p1733 := BSN.cos_dyadic_bound_f 638325161 536870912 4 3 536870912 268435456 Ns540p1730 Ns540p153 Ns540p1731 Ns540p1732 Ns540p156 Ns540p1731 200045008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 638325161) qz19 0 3 Ns540p1730 Ns540p153 Ns540p1731 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 638325161) qz378 0 3 Ns540p1732 Ns540p156 Ns540p1731 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1734 := nat_lit 18992961757714848531802046421201 

noncomputable def Ns540p1735 := BSN.cos_dyadic_bound_f 66015843 536870912 2 1 536870912 268435456 Ns540p1734 Ns540p136 Ns540p1734 Ns540p1734 Ns540p137 Ns540p1734 532817234 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 66015843) qz19 0 1 Ns540p1734 Ns540p136 Ns540p1734 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 66015843) qz378 0 1 Ns540p1734 Ns540p137 Ns540p1734 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1736 := Ns540p1681 178540 BSN.abs_quadSignPos (BSN.cos_quad_nat0 128 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 200045008 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 532817234 536870912) qz242 rfl rfl (Ns540p1729 rfl rfl) (Ns540p1711 rfl) RS541to552.d27 RS541to552.d29 RS541to552.d31 RS541to552.d33 RS541to552.d17 (Ns540p1733 rfl rfl) (Ns540p1735 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1737 := nat_lit 121382377482960409010385377309816753327401056967109553938297507300231841 

noncomputable def Ns540p1738 := nat_lit 756359575467275424049160969279103465452945744787838628422102796961 

noncomputable def Ns540p1739 := nat_lit 364145619729730292480308033607511701775272265009839086137635677695101601 

noncomputable def Ns540p1740 := BSN.cos_dyadic_bound_f 171727971 536870912 3 2 536870912 268435456 Ns540p1737 Ns540p160 Ns540p1738 Ns540p1739 Ns540p163 Ns540p1738 509639126 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 171727971) qz19 0 2 Ns540p1737 Ns540p160 Ns540p1738 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 171727971) qz378 0 2 Ns540p1739 Ns540p163 Ns540p1738 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1741 := BSN.sin_dyadic_bound_f 14566697 536870912 1 0 536870912 268435456 0 1 1 0 1 1 14564909 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 14566697) qz376 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 14566697) qz377 0 0 rfl) rfl rfl 

noncomputable def Ns540p1742 := Ns540p1679 218624 BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 509639126 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 14564909 536870912) qz242 rfl rfl (Ns540p1736 rfl) (Ns540p1711 rfl) RS541to552.d35 RS541to552.d37 RS541to552.d39 RS541to552.d41 RS541to552.d17 (Ns540p1740 rfl rfl) (Ns540p1741 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1743 := nat_lit 1215764723591519463929148126397030368949317460015779831952657746608800000 

noncomputable def Ns540p1744 := nat_lit 75869515793339540753574185625087385351560739121778181178736100000000 

noncomputable def Ns540p1745 := nat_lit 3647142431742971712705937230819840932077249258569095939495615767626400000 

noncomputable def Ns540p1746 := BSN.cos_dyadic_bound_f 305498030 536870912 3 2 536870912 268435456 Ns540p1743 Ns540p160 Ns540p1744 Ns540p1745 Ns540p163 Ns540p1744 452271673 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 305498030) qz19 0 2 Ns540p1743 Ns540p160 Ns540p1744 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 305498030) qz378 0 2 Ns540p1745 Ns540p163 Ns540p1744 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1747 := nat_lit 24822336870332610346560011093901132514163116379923368304047240276233748480 

noncomputable def Ns540p1748 := nat_lit 9754866969035803495597932892957101956106879669043993284109145231917056 

noncomputable def Ns540p1749 := nat_lit 64995088685302207225807156211723892705355417475573226711949452583570046976 

noncomputable def Ns540p1750 := BSN.sin_dyadic_bound_f 560599452 536870912 3 2 536870912 268435456 Ns540p1747 Ns540p276 Ns540p1748 Ns540p1749 Ns540p279 Ns540p1748 464136531 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 560599452) qz376 0 2 Ns540p1747 Ns540p276 Ns540p1748 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 560599452) qz377 0 2 Ns540p1749 Ns540p279 Ns540p1748 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1751 := Ns540p1677 254675 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 178 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 452271673 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 235 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 464136531 536870912) qz242 rfl rfl (Ns540p1742 rfl) (Ns540p1711 rfl) RS541to552.d43 RS541to552.d45 RS541to552.d47 RS541to552.d49 RS541to552.d17 (Ns540p1746 rfl rfl) (Ns540p1750 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns540p1752 := nat_lit 165910560278547063806370928443197471919344257683186194773619270010612139546399007007952196306069514101258253438976 

noncomputable def Ns540p1753 := nat_lit 98866977452099539377259931948880138035482451707483864241473845835350428313396407674883400184167487671832576 

noncomputable def Ns540p1754 := nat_lit 828610262147882852344741001578959282479407435777192875874745059082289412522168365160273264845721468044598543323136 

noncomputable def Ns540p1755 := BSN.sin_dyadic_bound_f 824620774 536870912 4 3 536870912 268435456 Ns540p1752 Ns540p130 Ns540p1753 Ns540p1754 Ns540p133 Ns540p1753 536545476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 824620774) qz376 0 3 Ns540p1752 Ns540p130 Ns540p1753 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 824620774) qz377 0 3 Ns540p1754 Ns540p133 Ns540p1753 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1756 := Ns540p1675 Bool.true 461981425 254675 Bool.true 824620774 28296951008113761 1 Bool.false 536545476 Bool.false Bool.true 307094083 271523 BSN.abs_quadSignPos (BSN.cos_quad_nat3 287 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536545476 536870912) qz242 rfl (Ns540p1751 rfl) (Ns540p1711 rfl) RS541to552.d51 RS541to552.d53 RS541to552.d17 (Ns540p1755 rfl rfl) rfl 

noncomputable def Ns540p1757 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 12) 307094083 536870912 271523 536870912 307094083 536870912 271523 536870912 329739760820027392 307094083 268435456 271523 268435456 (Ns540p1756 rfl rfl rfl rfl) 

noncomputable def Ns540p1758 := @Enclosure.Real.IsNear.mulLit_ff qz702 (Zeta.RiemannSiegel.correction qz241) 9583107 33554432 1 33554432 276034126413567 562949953421312 83759069749030311 676243631547351040000 2645264569072738812669 18889465931478580854784 

noncomputable abbrev qz706 := (@HPow.hPow Real Real Real qz152 qz240 qz154)

noncomputable def Ns540p1759 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz706 1 1 0 1 9583107 33554432 1 33554432 9583107 33554432 1 33554432 

noncomputable def Ns540p1760 := @Enclosure.Real.IsNear.sqrt_image qz240 2521704241993 16777216000 236099 16777216000 411374149 411374189 33554432 (@Enclosure.Real.IsNear.of_eq qz240 (@HMul.hMul Real Real Real qz5 qz239 qz3) Bool.false 2521704241993 16777216000 236099 16777216000 (BSN.t_div_two_pi_mk qz239 944396 1000 qz242) (@Enclosure.Real.IsNear.mulLit_ff qz239 qz3 944396 1000 0 1 10680707 67108864 1 67108864 2521704241993 16777216000 236099 16777216000 (Enclosure.Real.IsNear.const Bool.false 944396 1000) RS541to552.d56 rfl)) 

noncomputable abbrev qz776 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 944396 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz707 := qz776

noncomputable abbrev qz536 := qz707

noncomputable abbrev qz248 := qz536

noncomputable def Ns540p1761 := @Enclosure.Real.IsNear.sqrt_image qz248 411374169 33554432 5 8388608 117487981 117487988 33554432 (@Enclosure.Real.IsNear.recentre' qz248 Bool.false 822748338 67108864 40 67108864 411374169 33554432 5 8388608 (Ns540p1760 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns540p1762 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz248) 234975969 67108864 7 67108864 9583106 9583108 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz248) Bool.false 234975969 67108864 7 67108864 234975969 67108864 7 67108864 (Ns540p1761 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns540p1763 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz248)) Bool.false 19166214 67108864 2 67108864 9583107 33554432 1 33554432 (Ns540p1762 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz537 := (@HMul.hMul Real Real Real qz579 qz577 qz701)

noncomputable abbrev qz249 := (Real.cos qz537)

noncomputable abbrev qz708 := (@HMul.hMul Real Real Real qz717 qz774 qz774)

noncomputable abbrev qz538 := (@HSub.hSub Real Real Real qz582 (@HSub.hSub Real Real Real qz582 qz708 qz701) qz594)

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz538))

noncomputable def Ns540p1764 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz241) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz249) qz250) Bool.false 276034126413567 

noncomputable def Ns540p1765 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz249) qz250 1078945291 67108864 66945 

noncomputable abbrev qz251 := (@Neg.neg Real Real.instNeg (Real.cos qz537))

noncomputable def Ns540p1766 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz249) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz251)) Bool.true 1078945291 67108864 66945 67108864 (BSN.inv_eq_neg_inv_neg qz249) 

noncomputable def Ns540p1767 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz251) Bool.false 1078945291 67108864 66945 67108864 1078945291 67108864 

noncomputable def Ns540p1768 := @Enclosure.Real.IsNear.recentre' qz249 Bool.true 2087038 33554432 622207216 161229045760000 1043519 16777216 38887951 10076815360000 

noncomputable abbrev qz252 := qz537

noncomputable def Ns540p1769 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 109591129) qz374) Bool.false 109591129 67108864 63 16777216 Bool.true 2087038 33554432 1 

noncomputable def Ns540p1770 := nat_lit 26986075412789679991559623 

noncomputable def Ns540p1771 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz241 884279719003555 140737488355328 1 500000000000000 8720985 33554432 5 8388608 7711790165234218101675 4722366482869645213696 Ns540p1770 

noncomputable def Ns540p1772 := @Enclosure.Real.IsNear.subLit_ff_p qz248 qz1 411374169 33554432 5 8388608 12 1 0 1 8720985 8720985 33554432 5 

noncomputable def Ns540p1773 := @Ns540p1772 8388608 (@Enclosure.Real.IsNear.recentre' qz248 Bool.false 822748338 67108864 40 67108864 411374169 33554432 5 8388608 (Ns540p1760 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns540p1774 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 7711790165234218101675 4722366482869645213696 Ns540p1770 Ns540p1261 109591129 67108864 63 16777216 (@Ns540p1771 Ns540p1261 RS541to552.d55 (Ns540p1773 rfl rfl) rfl) 

noncomputable def Ns540p1775 := nat_lit 1189329284169715667436712322708891692078364575083455339570306111597892281500020069768394284610717737121 

noncomputable def Ns540p1776 := nat_lit 3001268238875823009376492768544807050240391687162991056306572107949660617391002441455782923591841 

noncomputable def Ns540p1777 := nat_lit 7194972380353163791524048998997877572459235455801959972380364813346438023244947643488005130905871704225 

noncomputable def Ns540p1778 := BSN.cos_dyadic_bound_t 109591129 67108864 4 3 33554432 9610000 Ns540p1775 Ns540p219 Ns540p1776 Ns540p1777 Ns540p222 Ns540p1776 2087038 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 109591129) qz596 0 3 Ns540p1775 Ns540p219 Ns540p1776 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 109591129) (BSN.cosOddQ 67108864) 0 3 Ns540p1777 Ns540p222 Ns540p1776 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1779 := @Enclosure.Real.IsNear.inv_image qz251 1043519 16777216 38887951 10076815360000 539439173 539506118 33554432 (@Enclosure.Real.IsNear.neg qz249 Bool.true 1043519 16777216 38887951 10076815360000 (Ns540p1768 (@Ns540p1769 9610000 (Ns540p1774 rfl) (Enclosure.sfrac_false_div 109591129 67108864) (Ns540p1778 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns540p1780 := Ns540p1766 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz251) Bool.false 1078945291 67108864 66945 67108864 (@Ns540p1767 66945 67108864 (Ns540p1779 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns540p1781 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true 1023348 33554432 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz355 qz352 qz538)

noncomputable def Ns540p1782 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 107461369)) qz374) Bool.true 107461369 67108864 

noncomputable def Ns540p1783 := nat_lit 253735985671522966696354319245 

noncomputable def Ns540p1784 := nat_lit 158456325028528675187087900672 

noncomputable def Ns540p1785 := nat_lit 3440483224516682302125428447187401 

noncomputable def Ns540p1786 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns540p1783 Ns540p1784 Ns540p1785 

noncomputable def Ns540p1787 := nat_lit 604462909807314587353088000000000000000 

noncomputable abbrev qz254 := qz538

noncomputable def Ns540p1788 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 286940862962959 

noncomputable abbrev qz539 := (@HSub.hSub Real Real Real qz582 qz708 qz701)

noncomputable abbrev qz255 := qz539

noncomputable def Ns540p1789 := @Enclosure.Real.IsNear.subLit_tf qz255 qz30 216572118785295 1125899906842624 127491055 140737488355328 1 16 

noncomputable abbrev qz540 := qz708

noncomputable abbrev qz256 := qz540

noncomputable def Ns540p1790 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz241 76055579370225 1125899906842624 43604975 140737488355328 8720985 33554432 5 8388608 

noncomputable def Ns540p1791 := @Enclosure.Real.IsNear.mulLit_ff qz241 qz241 8720985 33554432 5 8388608 8720985 33554432 5 8388608 76055579370225 1125899906842624 

noncomputable def Ns540p1792 := nat_lit 1099187009999796016510291896583407485431539517106718739647411551156000485013851547029485063023551556641 

noncomputable def Ns540p1793 := nat_lit 2371528932311152324427443677431388961185348665268024937087631386624446281180620713007220261628961 

noncomputable def Ns540p1794 := nat_lit 6651058569598329066063625622849497954448518135196809947054874702807942352816483491971920343707109010465 

noncomputable def Ns540p1795 := BSN.cos_dyadic_bound_t 107461369 67108864 4 3 33554432 9610000 Ns540p1792 Ns540p219 Ns540p1793 Ns540p1794 Ns540p222 Ns540p1793 1023348 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 107461369) qz596 0 3 Ns540p1792 Ns540p219 Ns540p1793 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 107461369) (BSN.cosOddQ 67108864) 0 3 Ns540p1794 Ns540p222 Ns540p1793 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns540p1796 := @Ns540p1781 3747738864 644916183040000 255837 8388608 234233679 40307261440000 (@Ns540p1782 383 67108864 Bool.true 1023348 33554432 1 9610000 (@Ns540p1786 Ns540p1787 107461369 67108864 383 67108864 (@Ns540p1788 1125899906842624 127491055 140737488355328 Ns540p1783 Ns540p1784 Ns540p1785 Ns540p1787 RS541to552.d55 (@Ns540p1789 0 1 4591053807407344 286940862962959 1125899906842624 127491055 140737488355328 (@Ns540p1790 7266954432877103677440 216572118785295 1125899906842624 127491055 140737488355328 (@Ns540p1791 43604975 140737488355328 (Ns540p1773 rfl rfl) (Ns540p1773 rfl rfl) rfl) (Ns540p1773 rfl rfl) rfl rfl) qz389 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 107461369 67108864) (BSN.cos_neg_of_bound 107461369 67108864 Bool.true 1023348 33554432 1 9610000 (Ns540p1795 rfl rfl)) rfl rfl) 

noncomputable def Ns540p1797 := @Ns540p1758 401501898689422331472669 Ns540p789 (Ns540p1759 qz32 (@Enclosure.Real.IsNear.of_eq qz706 (@Inv.inv Real Real.instInv (Real.sqrt qz248)) Bool.false 9583107 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz240 (BSN.t_div_two_pi_nonneg qz239 944396 1000 qz242)) Ns540p1763) rfl) (@Ns540p1764 562949953421312 83759069749030311 676243631547351040000 (BSN.correction_mk qz241 (BSN.cos_two_pi_p_ne_zero_mk qz239 944396 1000 12 qz242 rfl rfl (@BSN.floor_sqrt_eq_dec qz239 944396 1000 12 qz242 rfl rfl rfl))) (@Ns540p1765 67108864 255837 8388608 234233679 40307261440000 276034126413567 562949953421312 83759069749030311 676243631547351040000 Ns540p1780 (Ns540p1796 rfl) rfl)) 

noncomputable def Ns540p1798 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz239) (hardyZApproximantRS₀ qz239) Bool.true 24255089534174053974781 18889465931478580854784 Ns540p1672 Ns540p789 (@Eq.refl Real (hardyZApproximantRS₀ qz239)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz239) (@HSub.hSub Real Real Real qz33 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz239) qz239 12) (@HMul.hMul Real Real Real qz5 qz702 (Zeta.RiemannSiegel.correction qz241))) Bool.true 24255089534174053974781 18889465931478580854784 Ns540p1672 Ns540p789 (BSN.hardyZApproximantRS₀_eq qz239 12 (@BSN.floor_sqrt_eq_dec qz239 944396 1000 12 qz242 rfl rfl rfl)) (@Ns540p1674 24255089534174053974781 18889465931478580854784 Ns540p1672 Ns540p789 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz239) qz239 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz239) qz239 12)) Bool.true 307094083 268435456 271523 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz239) qz239 12) (Ns540p1757 (Ns540p1756 rfl rfl rfl rfl) rfl rfl)) (Ns540p1797 rfl) rfl rfl)) 

theorem RS541to552.d71 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz239) Bool.true 24255089534174053974781 18889465931478580854784 Ns540p1672 Ns540p789 := Ns540p1798 

noncomputable def RS541to552.d72 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz541 := (RS541to552.d3 qz578 qz597 (@Enclosure.dec_le_dec qz578 qz597 929330 1000 930587 1000 (@Eq.refl Real qz578) qz600 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz541)

noncomputable def Ns540p1799 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 170244875588074060131293 151115727451828646838272 Ns540p85 Ns540p86 

noncomputable abbrev qz542 := (@Enclosure.dec_le_dec qz578 qz597 929330 1000 930587 1000 (@Eq.refl Real qz578) qz600 rfl rfl rfl)

noncomputable abbrev qz258 := qz542

noncomputable def Ns540p1800 := @Enclosure.Real.IsNear.neg_val qz257 170244875588074060131293 151115727451828646838272 Ns540p85 Ns540p86 (Ns540p1799 (RS541to552.d4 qz4 qz34 qz258) RS541to552.d57) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz541)

noncomputable def Ns540p1801 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz34) Bool.false 161348760837839862005895 151115727451828646838272 Ns540p227 Ns540p228 

noncomputable def Ns540p1802 := @Enclosure.Real.IsNear.pos_val qz259 161348760837839862005895 151115727451828646838272 Ns540p227 Ns540p228 (Ns540p1801 (RS541to552.d58 qz4 qz34 qz258) RS541to552.d59) rfl 

noncomputable def Ns540p1803 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 929330 1000 929330 1000 

noncomputable def Ns540p1804 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 170244875588074060131293 151115727451828646838272 Ns540p85 

noncomputable def Ns540p1805 := @Ns540p1804 Ns540p86 91844473 2147483648 1213 10737418240 (Ns540p1799 (RS541to552.d4 qz4 qz34 qz258) RS541to552.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable def Ns540p1806 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz34 929330 1000 930587 1000 

noncomputable def Ns540p1807 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 161348760837839862005895 151115727451828646838272 Ns540p227 

noncomputable def Ns540p1808 := @Ns540p1807 Ns540p228 91844473 2147483648 1213 10737418240 (Ns540p1801 (RS541to552.d58 qz4 qz34 qz258) RS541to552.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz541

noncomputable def Ns540p1809 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 929330 1000 qz9 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns540p1800 rfl rfl) (Ns540p1802 rfl rfl)) (Ns540p1803 qz9 qz9 rfl rfl rfl rfl (Ns540p1805 rfl)) (Ns540p1806 qz9 qz37 rfl rfl rfl rfl (Ns540p1808 rfl)) 

noncomputable abbrev qz543 := (RS541to552.d3 qz597 qz607 (@Enclosure.dec_le_dec qz597 qz607 930587 1000 931844 1000 qz600 qz610 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz543)

noncomputable def Ns540p1810 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz34) Bool.false 161348760837839862005895 151115727451828646838272 Ns540p227 Ns540p228 

noncomputable abbrev qz544 := (@Enclosure.dec_le_dec qz597 qz607 930587 1000 931844 1000 qz600 qz610 rfl rfl rfl)

noncomputable abbrev qz262 := qz544

noncomputable def Ns540p1811 := @Enclosure.Real.IsNear.pos_val qz261 161348760837839862005895 151115727451828646838272 Ns540p227 Ns540p228 (Ns540p1810 (RS541to552.d4 qz34 qz61 qz262) RS541to552.d59) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz543)

noncomputable def Ns540p1812 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz61) Bool.true 54955096768538535491 1180591620717411303424 Ns540p396 Ns540p397 

noncomputable def Ns540p1813 := @Enclosure.Real.IsNear.neg_val qz263 54955096768538535491 1180591620717411303424 Ns540p396 Ns540p397 (Ns540p1812 (RS541to552.d58 qz34 qz61 qz262) RS541to552.d61) rfl 

noncomputable def Ns540p1814 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz34 929330 1000 930587 1000 

noncomputable def Ns540p1815 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 161348760837839862005895 151115727451828646838272 Ns540p227 

noncomputable def Ns540p1816 := @Ns540p1815 Ns540p228 91844473 2147483648 1213 10737418240 (Ns540p1810 (RS541to552.d4 qz34 qz61 qz262) RS541to552.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable def Ns540p1817 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz61 929330 1000 931844 1000 

noncomputable def Ns540p1818 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 54955096768538535491 1180591620717411303424 Ns540p396 

noncomputable def Ns540p1819 := @Ns540p1818 Ns540p397 91844473 2147483648 1213 10737418240 (Ns540p1812 (RS541to552.d58 qz34 qz61 qz262) RS541to552.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz543

noncomputable def Ns540p1820 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz34 930587 1000 qz37 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns540p1811 rfl rfl) (Ns540p1813 rfl rfl)) (Ns540p1814 qz9 qz37 rfl rfl rfl rfl (Ns540p1816 rfl)) (Ns540p1817 qz9 qz64 rfl rfl rfl rfl (Ns540p1819 rfl)) 

noncomputable abbrev qz545 := (RS541to552.d3 qz607 qz617 (@Enclosure.dec_le_dec qz607 qz617 931844 1000 933729 1000 qz610 qz620 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz545)

noncomputable def Ns540p1821 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz61) Bool.true 54955096768538535491 1180591620717411303424 Ns540p396 Ns540p397 

noncomputable abbrev qz546 := (@Enclosure.dec_le_dec qz607 qz617 931844 1000 933729 1000 qz610 qz620 rfl rfl rfl)

noncomputable abbrev qz266 := qz546

noncomputable def Ns540p1822 := @Enclosure.Real.IsNear.neg_val qz265 54955096768538535491 1180591620717411303424 Ns540p396 Ns540p397 (Ns540p1821 (RS541to552.d4 qz61 qz79 qz266) RS541to552.d61) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz545)

noncomputable def Ns540p1823 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz79) Bool.false 2984780444121419696865 590295810358705651712 713233165624754110463851 Ns540p527 

noncomputable def Ns540p1824 := @Enclosure.Real.IsNear.pos_val qz267 2984780444121419696865 590295810358705651712 713233165624754110463851 Ns540p527 (Ns540p1823 (RS541to552.d58 qz61 qz79 qz266) RS541to552.d62) rfl 

noncomputable def Ns540p1825 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz61 929330 1000 931844 1000 

noncomputable def Ns540p1826 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 54955096768538535491 1180591620717411303424 Ns540p396 

noncomputable def Ns540p1827 := @Ns540p1826 Ns540p397 91844473 2147483648 1213 10737418240 (Ns540p1821 (RS541to552.d4 qz61 qz79 qz266) RS541to552.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable def Ns540p1828 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz79 929330 1000 933729 1000 

noncomputable def Ns540p1829 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2984780444121419696865 590295810358705651712 713233165624754110463851 

noncomputable def Ns540p1830 := @Ns540p1829 Ns540p527 91844473 2147483648 1213 10737418240 (Ns540p1823 (RS541to552.d58 qz61 qz79 qz266) RS541to552.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz545

noncomputable def Ns540p1831 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz61 931844 1000 qz64 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns540p1822 rfl rfl) (Ns540p1824 rfl rfl)) (Ns540p1825 qz9 qz64 rfl rfl rfl rfl (Ns540p1827 rfl)) (Ns540p1828 qz9 qz82 rfl rfl rfl rfl (Ns540p1830 rfl)) 

noncomputable abbrev qz547 := (RS541to552.d3 qz617 qz625 (@Enclosure.dec_le_dec qz617 qz625 933729 1000 934750 1000 qz620 qz628 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz547)

noncomputable def Ns540p1832 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz79) Bool.false 2984780444121419696865 590295810358705651712 713233165624754110463851 Ns540p527 

noncomputable abbrev qz548 := (@Enclosure.dec_le_dec qz617 qz625 933729 1000 934750 1000 qz620 qz628 rfl rfl rfl)

noncomputable abbrev qz270 := qz548

noncomputable def Ns540p1833 := @Enclosure.Real.IsNear.pos_val qz269 2984780444121419696865 590295810358705651712 713233165624754110463851 Ns540p527 (Ns540p1832 (RS541to552.d4 qz79 qz97 qz270) RS541to552.d62) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz547)

noncomputable def Ns540p1834 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz97) Bool.true 39002828451968757437 73786976294838206464 Ns540p658 Ns540p659 

noncomputable def Ns540p1835 := @Enclosure.Real.IsNear.neg_val qz271 39002828451968757437 73786976294838206464 Ns540p658 Ns540p659 (Ns540p1834 (RS541to552.d58 qz79 qz97 qz270) RS541to552.d63) rfl 

noncomputable def Ns540p1836 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz79 929330 1000 933729 1000 

noncomputable def Ns540p1837 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2984780444121419696865 590295810358705651712 713233165624754110463851 

noncomputable def Ns540p1838 := @Ns540p1837 Ns540p527 91844473 2147483648 1213 10737418240 (Ns540p1832 (RS541to552.d4 qz79 qz97 qz270) RS541to552.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable def Ns540p1839 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz97 929330 1000 934750 1000 

noncomputable def Ns540p1840 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 39002828451968757437 73786976294838206464 Ns540p658 

noncomputable def Ns540p1841 := @Ns540p1840 Ns540p659 91844473 2147483648 1213 10737418240 (Ns540p1834 (RS541to552.d58 qz79 qz97 qz270) RS541to552.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz547

noncomputable def Ns540p1842 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz79 933729 1000 qz82 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns540p1833 rfl rfl) (Ns540p1835 rfl rfl)) (Ns540p1836 qz9 qz82 rfl rfl rfl rfl (Ns540p1838 rfl)) (Ns540p1839 qz9 qz100 rfl rfl rfl rfl (Ns540p1841 rfl)) 

noncomputable abbrev qz549 := (RS541to552.d3 qz625 qz633 (@Enclosure.dec_le_dec qz625 qz633 934750 1000 935378 1000 qz628 qz636 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz549)

noncomputable def Ns540p1843 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz97) Bool.true 39002828451968757437 73786976294838206464 Ns540p658 Ns540p659 

noncomputable abbrev qz550 := (@Enclosure.dec_le_dec qz625 qz633 934750 1000 935378 1000 qz628 qz636 rfl rfl rfl)

noncomputable abbrev qz274 := qz550

noncomputable def Ns540p1844 := @Enclosure.Real.IsNear.neg_val qz273 39002828451968757437 73786976294838206464 Ns540p658 Ns540p659 (Ns540p1843 (RS541to552.d4 qz97 qz115 qz274) RS541to552.d63) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz549)

noncomputable def Ns540p1845 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz115) Bool.false 22284627352996282883783 18889465931478580854784 Ns540p788 Ns540p789 

noncomputable def Ns540p1846 := @Enclosure.Real.IsNear.pos_val qz275 22284627352996282883783 18889465931478580854784 Ns540p788 Ns540p789 (Ns540p1845 (RS541to552.d58 qz97 qz115 qz274) RS541to552.d64) rfl 

noncomputable def Ns540p1847 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz97 929330 1000 934750 1000 

noncomputable def Ns540p1848 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 39002828451968757437 73786976294838206464 Ns540p658 

noncomputable def Ns540p1849 := @Ns540p1848 Ns540p659 91844473 2147483648 1213 10737418240 (Ns540p1843 (RS541to552.d4 qz97 qz115 qz274) RS541to552.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable def Ns540p1850 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz115 929330 1000 935378 1000 

noncomputable def Ns540p1851 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 22284627352996282883783 18889465931478580854784 Ns540p788 

noncomputable def Ns540p1852 := @Ns540p1851 Ns540p789 91844473 2147483648 1213 10737418240 (Ns540p1845 (RS541to552.d58 qz97 qz115 qz274) RS541to552.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz549

noncomputable def Ns540p1853 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz97 934750 1000 qz100 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns540p1844 rfl rfl) (Ns540p1846 rfl rfl)) (Ns540p1847 qz9 qz100 rfl rfl rfl rfl (Ns540p1849 rfl)) (Ns540p1850 qz9 qz118 rfl rfl rfl rfl (Ns540p1852 rfl)) 

noncomputable abbrev qz551 := (RS541to552.d3 qz633 qz641 (@Enclosure.dec_le_dec qz633 qz641 935378 1000 936869 1000 qz636 qz644 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns540p1854 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz115) Bool.false 22284627352996282883783 18889465931478580854784 Ns540p788 Ns540p789 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz633 qz641 935378 1000 936869 1000 qz636 qz644 rfl rfl rfl)

noncomputable abbrev qz278 := qz552

noncomputable def Ns540p1855 := @Enclosure.Real.IsNear.pos_val qz277 22284627352996282883783 18889465931478580854784 Ns540p788 Ns540p789 (Ns540p1854 (RS541to552.d4 qz115 qz133 qz278) RS541to552.d64) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns540p1856 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz133) Bool.true 145569792037078047002859 75557863725914323419136 59267352889732469050417 Ns540p921 

noncomputable def Ns540p1857 := @Enclosure.Real.IsNear.neg_val qz279 145569792037078047002859 75557863725914323419136 59267352889732469050417 Ns540p921 (Ns540p1856 (RS541to552.d58 qz115 qz133 qz278) RS541to552.d65) rfl 

noncomputable def Ns540p1858 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz115 929330 1000 935378 1000 

noncomputable def Ns540p1859 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 22284627352996282883783 18889465931478580854784 Ns540p788 

noncomputable def Ns540p1860 := @Ns540p1859 Ns540p789 91844473 2147483648 1213 10737418240 (Ns540p1854 (RS541to552.d4 qz115 qz133 qz278) RS541to552.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable def Ns540p1861 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz133 929330 1000 936869 1000 

noncomputable def Ns540p1862 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 145569792037078047002859 75557863725914323419136 59267352889732469050417 

noncomputable def Ns540p1863 := @Ns540p1862 Ns540p921 91844473 2147483648 1213 10737418240 (Ns540p1856 (RS541to552.d58 qz115 qz133 qz278) RS541to552.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz551

noncomputable def Ns540p1864 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz115 935378 1000 qz118 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns540p1855 rfl rfl) (Ns540p1857 rfl rfl)) (Ns540p1858 qz9 qz118 rfl rfl rfl rfl (Ns540p1860 rfl)) (Ns540p1861 qz9 qz136 rfl rfl rfl rfl (Ns540p1863 rfl)) 

noncomputable abbrev qz553 := (RS541to552.d3 qz641 qz649 (@Enclosure.dec_le_dec qz641 qz649 936869 1000 938124 1000 qz644 qz653 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns540p1865 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz133) Bool.true 145569792037078047002859 75557863725914323419136 59267352889732469050417 Ns540p921 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz641 qz649 936869 1000 938124 1000 qz644 qz653 rfl rfl rfl)

noncomputable abbrev qz282 := qz554

noncomputable def Ns540p1866 := @Enclosure.Real.IsNear.neg_val qz281 145569792037078047002859 75557863725914323419136 59267352889732469050417 Ns540p921 (Ns540p1865 (RS541to552.d4 qz133 qz151 qz282) RS541to552.d65) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns540p1867 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz151) Bool.false 18876810549207096404825 9444732965739290427392 Ns540p1041 Ns540p1042 

noncomputable def Ns540p1868 := @Enclosure.Real.IsNear.pos_val qz283 18876810549207096404825 9444732965739290427392 Ns540p1041 Ns540p1042 (Ns540p1867 (RS541to552.d58 qz133 qz151 qz282) RS541to552.d66) rfl 

noncomputable def Ns540p1869 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz133 929330 1000 936869 1000 

noncomputable def Ns540p1870 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 145569792037078047002859 75557863725914323419136 59267352889732469050417 

noncomputable def Ns540p1871 := @Ns540p1870 Ns540p921 91844473 2147483648 1213 10737418240 (Ns540p1865 (RS541to552.d4 qz133 qz151 qz282) RS541to552.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable def Ns540p1872 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz151 929330 1000 938124 1000 

noncomputable def Ns540p1873 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 18876810549207096404825 9444732965739290427392 Ns540p1041 

noncomputable def Ns540p1874 := @Ns540p1873 Ns540p1042 91844473 2147483648 1213 10737418240 (Ns540p1867 (RS541to552.d58 qz133 qz151 qz282) RS541to552.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz553

noncomputable def Ns540p1875 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz133 936869 1000 qz136 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns540p1866 rfl rfl) (Ns540p1868 rfl rfl)) (Ns540p1869 qz9 qz136 rfl rfl rfl rfl (Ns540p1871 rfl)) (Ns540p1872 qz9 qz156 rfl rfl rfl rfl (Ns540p1874 rfl)) 

noncomputable abbrev qz555 := (RS541to552.d3 qz649 qz659 (@Enclosure.dec_le_dec qz649 qz659 938124 1000 939379 1000 qz653 qz663 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns540p1876 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz151) Bool.false 18876810549207096404825 9444732965739290427392 Ns540p1041 Ns540p1042 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz649 qz659 938124 1000 939379 1000 qz653 qz663 rfl rfl rfl)

noncomputable abbrev qz286 := qz556

noncomputable def Ns540p1877 := @Enclosure.Real.IsNear.pos_val qz285 18876810549207096404825 9444732965739290427392 Ns540p1041 Ns540p1042 (Ns540p1876 (RS541to552.d4 qz151 qz170 qz286) RS541to552.d66) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns540p1878 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz170) Bool.true 66318325273615395112219 151115727451828646838272 Ns540p1164 Ns540p228 

noncomputable def Ns540p1879 := @Enclosure.Real.IsNear.neg_val qz287 66318325273615395112219 151115727451828646838272 Ns540p1164 Ns540p228 (Ns540p1878 (RS541to552.d58 qz151 qz170 qz286) RS541to552.d67) rfl 

noncomputable def Ns540p1880 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz151 929330 1000 938124 1000 

noncomputable def Ns540p1881 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 18876810549207096404825 9444732965739290427392 Ns540p1041 

noncomputable def Ns540p1882 := @Ns540p1881 Ns540p1042 91844473 2147483648 1213 10737418240 (Ns540p1876 (RS541to552.d4 qz151 qz170 qz286) RS541to552.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable def Ns540p1883 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz170 929330 1000 939379 1000 

noncomputable def Ns540p1884 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 66318325273615395112219 151115727451828646838272 Ns540p1164 

noncomputable def Ns540p1885 := @Ns540p1884 Ns540p228 91844473 2147483648 1213 10737418240 (Ns540p1878 (RS541to552.d58 qz151 qz170 qz286) RS541to552.d67) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz555

noncomputable def Ns540p1886 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz151 938124 1000 qz156 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns540p1877 rfl rfl) (Ns540p1879 rfl rfl)) (Ns540p1880 qz9 qz156 rfl rfl rfl rfl (Ns540p1882 rfl)) (Ns540p1883 qz9 qz173 rfl rfl rfl rfl (Ns540p1885 rfl)) 

noncomputable abbrev qz709 := (@Enclosure.dec_le_dec qz754 qz758 939379 1000 940634 1000 (@Eq.refl Real qz754) (@Eq.refl Real qz758) rfl rfl rfl)

noncomputable abbrev qz557 := (RS541to552.d3 qz659 qz669 qz709)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns540p1887 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz170) Bool.true 66318325273615395112219 151115727451828646838272 Ns540p1164 Ns540p228 

noncomputable abbrev qz558 := qz709

noncomputable abbrev qz290 := qz558

noncomputable def Ns540p1888 := @Enclosure.Real.IsNear.neg_val qz289 66318325273615395112219 151115727451828646838272 Ns540p1164 Ns540p228 (Ns540p1887 (RS541to552.d4 qz170 qz187 qz290) RS541to552.d67) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns540p1889 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz187) Bool.false 36064342472529064089923 18889465931478580854784 Ns540p1291 Ns540p1292 

noncomputable def Ns540p1890 := @Enclosure.Real.IsNear.pos_val qz291 36064342472529064089923 18889465931478580854784 Ns540p1291 Ns540p1292 (Ns540p1889 (RS541to552.d58 qz170 qz187 qz290) RS541to552.d68) rfl 

noncomputable def Ns540p1891 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz170 929330 1000 939379 1000 

noncomputable def Ns540p1892 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 66318325273615395112219 151115727451828646838272 Ns540p1164 

noncomputable def Ns540p1893 := @Ns540p1892 Ns540p228 91844473 2147483648 1213 10737418240 (Ns540p1887 (RS541to552.d4 qz170 qz187 qz290) RS541to552.d67) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable def Ns540p1894 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz187 929330 1000 940634 1000 

noncomputable def Ns540p1895 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 36064342472529064089923 18889465931478580854784 Ns540p1291 

noncomputable def Ns540p1896 := @Ns540p1895 Ns540p1292 91844473 2147483648 1213 10737418240 (Ns540p1889 (RS541to552.d58 qz170 qz187 qz290) RS541to552.d68) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz557

noncomputable def Ns540p1897 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz170 939379 1000 qz173 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns540p1888 rfl rfl) (Ns540p1890 rfl rfl)) (Ns540p1891 qz9 qz173 rfl rfl rfl rfl (Ns540p1893 rfl)) (Ns540p1894 qz9 qz190 rfl rfl rfl rfl (Ns540p1896 rfl)) 

noncomputable abbrev qz710 := (@Enclosure.dec_le_dec qz758 qz762 940634 1000 941888 1000 (@Eq.refl Real qz758) qz765 rfl rfl rfl)

noncomputable abbrev qz559 := (RS541to552.d3 qz669 qz679 qz710)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns540p1898 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz187) Bool.false 36064342472529064089923 18889465931478580854784 Ns540p1291 Ns540p1292 

noncomputable abbrev qz560 := qz710

noncomputable abbrev qz294 := qz560

noncomputable def Ns540p1899 := @Enclosure.Real.IsNear.pos_val qz293 36064342472529064089923 18889465931478580854784 Ns540p1291 Ns540p1292 (Ns540p1898 (RS541to552.d4 qz187 qz204 qz294) RS541to552.d68) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns540p1900 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz204) Bool.true 15921241003960275865293 18889465931478580854784 Ns540p1412 Ns540p1413 

noncomputable def Ns540p1901 := @Enclosure.Real.IsNear.neg_val qz295 15921241003960275865293 18889465931478580854784 Ns540p1412 Ns540p1413 (Ns540p1900 (RS541to552.d58 qz187 qz204 qz294) RS541to552.d69) rfl 

noncomputable def Ns540p1902 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz187 929330 1000 940634 1000 

noncomputable def Ns540p1903 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 36064342472529064089923 18889465931478580854784 Ns540p1291 

noncomputable def Ns540p1904 := @Ns540p1903 Ns540p1292 91844473 2147483648 1213 10737418240 (Ns540p1898 (RS541to552.d4 qz187 qz204 qz294) RS541to552.d68) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable def Ns540p1905 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz204 929330 1000 941888 1000 

noncomputable def Ns540p1906 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 15921241003960275865293 18889465931478580854784 Ns540p1412 

noncomputable def Ns540p1907 := @Ns540p1906 Ns540p1413 91844473 2147483648 1213 10737418240 (Ns540p1900 (RS541to552.d58 qz187 qz204 qz294) RS541to552.d69) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz559

noncomputable def Ns540p1908 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz187 940634 1000 qz190 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns540p1899 rfl rfl) (Ns540p1901 rfl rfl)) (Ns540p1902 qz9 qz190 rfl rfl rfl rfl (Ns540p1904 rfl)) (Ns540p1905 qz9 qz207 rfl rfl rfl rfl (Ns540p1907 rfl)) 

noncomputable abbrev qz711 := (@Enclosure.dec_le_dec qz762 qz767 941888 1000 943142 1000 qz765 qz770 rfl rfl rfl)

noncomputable abbrev qz561 := (RS541to552.d3 qz679 qz689 qz711)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns540p1909 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz204) Bool.true 15921241003960275865293 18889465931478580854784 Ns540p1412 Ns540p1413 

noncomputable abbrev qz562 := qz711

noncomputable abbrev qz298 := qz562

noncomputable def Ns540p1910 := @Enclosure.Real.IsNear.neg_val qz297 15921241003960275865293 18889465931478580854784 Ns540p1412 Ns540p1413 (Ns540p1909 (RS541to552.d4 qz204 qz221 qz298) RS541to552.d69) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns540p1911 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz221) Bool.false 67135796661118443778723 9444732965739290427392 Ns540p1541 Ns540p1542 

noncomputable def Ns540p1912 := @Enclosure.Real.IsNear.pos_val qz299 67135796661118443778723 9444732965739290427392 Ns540p1541 Ns540p1542 (Ns540p1911 (RS541to552.d58 qz204 qz221 qz298) RS541to552.d70) rfl 

noncomputable def Ns540p1913 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz204 929330 1000 941888 1000 

noncomputable def Ns540p1914 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 15921241003960275865293 18889465931478580854784 Ns540p1412 

noncomputable def Ns540p1915 := @Ns540p1914 Ns540p1413 91844473 2147483648 1213 10737418240 (Ns540p1909 (RS541to552.d4 qz204 qz221 qz298) RS541to552.d69) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable def Ns540p1916 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz221 929330 1000 943142 1000 

noncomputable def Ns540p1917 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 67135796661118443778723 9444732965739290427392 Ns540p1541 

noncomputable def Ns540p1918 := @Ns540p1917 Ns540p1542 91844473 2147483648 1213 10737418240 (Ns540p1911 (RS541to552.d58 qz204 qz221 qz298) RS541to552.d70) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz561

noncomputable def Ns540p1919 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz204 941888 1000 qz207 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns540p1910 rfl rfl) (Ns540p1912 rfl rfl)) (Ns540p1913 qz9 qz207 rfl rfl rfl rfl (Ns540p1915 rfl)) (Ns540p1916 qz9 qz224 rfl rfl rfl rfl (Ns540p1918 rfl)) 

noncomputable abbrev qz777 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 943142 1000) (Enclosure.sfrac Bool.false 944396 1000) 943142 1000 944396 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 943142 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 944396 1000)) rfl rfl rfl)

noncomputable abbrev qz712 := qz777

noncomputable abbrev qz563 := (RS541to552.d3 qz689 qz699 qz712)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns540p1920 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz221) Bool.false 67135796661118443778723 9444732965739290427392 Ns540p1541 Ns540p1542 

noncomputable abbrev qz564 := qz712

noncomputable abbrev qz302 := qz564

noncomputable def Ns540p1921 := @Enclosure.Real.IsNear.pos_val qz301 67135796661118443778723 9444732965739290427392 Ns540p1541 Ns540p1542 (Ns540p1920 (RS541to552.d4 qz221 qz239 qz302) RS541to552.d70) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns540p1922 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz239) Bool.true 24255089534174053974781 18889465931478580854784 Ns540p1672 Ns540p789 

noncomputable def Ns540p1923 := @Enclosure.Real.IsNear.neg_val qz303 24255089534174053974781 18889465931478580854784 Ns540p1672 Ns540p789 (Ns540p1922 (RS541to552.d58 qz221 qz239 qz302) RS541to552.d71) rfl 

noncomputable def Ns540p1924 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz221 929330 1000 943142 1000 

noncomputable def Ns540p1925 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 67135796661118443778723 9444732965739290427392 Ns540p1541 

noncomputable def Ns540p1926 := @Ns540p1925 Ns540p1542 91844473 2147483648 1213 10737418240 (Ns540p1920 (RS541to552.d4 qz221 qz239 qz302) RS541to552.d70) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable def Ns540p1927 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz239 929330 1000 944396 1000 

noncomputable def Ns540p1928 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 24255089534174053974781 18889465931478580854784 Ns540p1672 

noncomputable def Ns540p1929 := @Ns540p1928 Ns540p789 91844473 2147483648 1213 10737418240 (Ns540p1922 (RS541to552.d58 qz221 qz239 qz302) RS541to552.d71) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 91844473 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS541to552.d60) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz563

noncomputable def Ns540p1930 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz221 943142 1000 qz224 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns540p1921 rfl rfl) (Ns540p1923 rfl rfl)) (Ns540p1924 qz9 qz224 rfl rfl rfl rfl (Ns540p1926 rfl)) (Ns540p1927 qz9 qz242 rfl rfl rfl rfl (Ns540p1929 rfl)) 

noncomputable def Ns540p1931 := @List.cons RS541to552.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns540p1919)) (@List.cons RS541to552.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns540p1930)) (@List.nil RS541to552.d0)) 

noncomputable def Ns540p1932 := @List.cons RS541to552.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns540p1897)) (@List.cons RS541to552.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns540p1908)) Ns540p1931) 

noncomputable def Ns540p1933 := @List.cons RS541to552.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns540p1875)) (@List.cons RS541to552.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns540p1886)) Ns540p1932) 

noncomputable def Ns540p1934 := @List.cons RS541to552.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns540p1853)) (@List.cons RS541to552.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns540p1864)) Ns540p1933) 

noncomputable def Ns540p1935 := @List.cons RS541to552.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns540p1831)) (@List.cons RS541to552.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns540p1842)) Ns540p1934) 

noncomputable def Ns540p1936 := @List.cons RS541to552.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns540p1809)) (@List.cons RS541to552.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns540p1820)) Ns540p1935) 

noncomputable abbrev qz565 := (RS541to552.d2 qz659 qz669 qz709)

noncomputable abbrev qz713 := (RS541to552.d2 qz762 qz767 (@Enclosure.dec_le_dec qz762 qz767 941888 1000 943142 1000 qz765 qz770 rfl rfl rfl))

noncomputable abbrev qz714 := (@List.cons RS541to552.d1 (RS541to552.d2 qz767 qz772 qz777) (@List.nil RS541to552.d1))

noncomputable abbrev qz566 := (@List.cons RS541to552.d1 (RS541to552.d2 qz669 qz679 qz710) (@List.cons RS541to552.d1 qz713 qz714))

noncomputable abbrev qz305 := (@List.cons RS541to552.d1 (RS541to552.d2 qz467 qz479 qz556) (@List.cons RS541to552.d1 qz565 qz566))

noncomputable def Ns540p1937 := @List.cons RS541to552.d1 (RS541to552.d2 qz115 qz133 qz278) (@List.cons RS541to552.d1 (RS541to552.d2 qz133 qz151 qz282) qz305) 

noncomputable abbrev qz306 := (RS541to552.d2 qz431 qz443 qz550)

noncomputable def Ns540p1938 := @List.IsChain.cons_cons RS541to552.d1 RS541to552.d72 qz306 (RS541to552.d2 qz115 qz133 qz278) (@List.cons RS541to552.d1 (RS541to552.d2 qz133 qz151 qz282) qz305) 

noncomputable def Ns540p1939 := @List.IsChain.cons_cons RS541to552.d1 RS541to552.d72 (RS541to552.d2 qz115 qz133 qz278) (RS541to552.d2 qz133 qz151 qz282) qz305 (@Enclosure.dec_le_dec qz133 qz133 936869 1000 936869 1000 qz136 qz136 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS541to552.d2 qz467 qz479 qz556)

noncomputable abbrev qz308 := qz565

noncomputable abbrev qz309 := qz566

noncomputable abbrev qz567 := (RS541to552.d2 qz669 qz679 qz710)

noncomputable abbrev qz310 := qz567

noncomputable abbrev qz568 := (@List.cons RS541to552.d1 qz713 qz714)

noncomputable abbrev qz311 := qz568

noncomputable abbrev qz569 := qz713

noncomputable abbrev qz312 := qz569

noncomputable abbrev qz570 := qz714

noncomputable abbrev qz313 := qz570

noncomputable abbrev qz715 := (RS541to552.d2 qz767 qz772 qz777)

noncomputable abbrev qz571 := qz715

noncomputable abbrev qz314 := qz571

noncomputable def Ns540p1940 := @List.IsChain.cons_cons RS541to552.d1 RS541to552.d72 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz170 qz170 939379 1000 939379 1000 qz173 qz173 rfl rfl rfl) (@List.IsChain.cons_cons RS541to552.d1 RS541to552.d72 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz187 qz187 940634 1000 940634 1000 qz190 qz190 rfl rfl rfl) (@List.IsChain.cons_cons RS541to552.d1 RS541to552.d72 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz204 qz204 941888 1000 941888 1000 qz207 qz207 rfl rfl rfl) (@List.IsChain.cons_cons RS541to552.d1 RS541to552.d72 qz312 qz314 (@List.nil RS541to552.d1) (@Enclosure.dec_le_dec qz221 qz221 943142 1000 943142 1000 qz224 qz224 rfl rfl rfl) (@List.IsChain.singleton RS541to552.d1 RS541to552.d72 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS541to552.d1 qz565 qz566)

noncomputable def Ns540p1941 := @List.IsChain.cons_cons RS541to552.d1 RS541to552.d72 (RS541to552.d2 qz133 qz151 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz151 qz151 938124 1000 938124 1000 qz156 qz156 rfl rfl rfl) Ns540p1940 

noncomputable def Ns540p1942 := @List.IsChain.cons_cons RS541to552.d1 RS541to552.d72 (RS541to552.d2 qz4 qz34 qz258) (RS541to552.d2 qz34 qz61 qz262) (@List.cons RS541to552.d1 (RS541to552.d2 qz61 qz79 qz266) (@List.cons RS541to552.d1 (RS541to552.d2 qz79 qz97 qz270) (@List.cons RS541to552.d1 qz306 Ns540p1937))) (@Enclosure.dec_le_dec qz34 qz34 930587 1000 930587 1000 qz37 qz37 rfl rfl rfl) (@List.IsChain.cons_cons RS541to552.d1 RS541to552.d72 (RS541to552.d2 qz34 qz61 qz262) (RS541to552.d2 qz61 qz79 qz266) (@List.cons RS541to552.d1 (RS541to552.d2 qz79 qz97 qz270) (@List.cons RS541to552.d1 qz306 Ns540p1937)) (@Enclosure.dec_le_dec qz61 qz61 931844 1000 931844 1000 qz64 qz64 rfl rfl rfl) (@List.IsChain.cons_cons RS541to552.d1 RS541to552.d72 (RS541to552.d2 qz61 qz79 qz266) (RS541to552.d2 qz79 qz97 qz270) (@List.cons RS541to552.d1 qz306 Ns540p1937) (@Enclosure.dec_le_dec qz79 qz79 933729 1000 933729 1000 qz82 qz82 rfl rfl rfl) (@List.IsChain.cons_cons RS541to552.d1 RS541to552.d72 (RS541to552.d2 qz79 qz97 qz270) qz306 Ns540p1937 (@Enclosure.dec_le_dec qz97 qz97 934750 1000 934750 1000 qz100 qz100 rfl rfl rfl) (Ns540p1938 (@Enclosure.dec_le_dec qz115 qz115 935378 1000 935378 1000 qz118 qz118 rfl rfl rfl) (Ns540p1939 Ns540p1941))))) 

noncomputable abbrev qz572 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz573 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns540p1936 Ns540p1942)

noncomputable abbrev qz574 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns540p1936 Ns540p1942))

theorem RS541to552.d73 : Zeta.Certificates.BatchSpec 12 929330 1000 944396 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz572 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz572 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz572 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz572 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz572 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz239)))) qz573 (@And.intro (@Eq Nat (@List.length qz572 qz574) 12) (And (@Eq (Option Real) (@Option.map qz572 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz572 qz574)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz572 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz572 qz574)) (@Option.some Real qz239))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz572 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz572 qz574)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz572 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz572 qz574)) (@Option.some Real qz239)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz239))))

theorem solution : Zeta.Certificates.BatchSpec 12 929330 1000 944396 1000 := RS541to552.d73
#print axioms solution
#check solution
