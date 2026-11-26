-- Prove2me | solution 1 for RHHeight1000.rs_main_0565_0576
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:21:45.89666+00:00
-- url     : https://prove2.me/submissions/43761bc3-f456-4402-a081-c53c84d4bc6d

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

noncomputable def RS565to576.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS565to576.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS565to576.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS565to576.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS565to576.d2 a b h 

theorem RS565to576.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS565to576.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS565to576.d3 a b h)) 

noncomputable def Ns564p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns564p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns564p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns564p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns564p0 Ns564p1 Ns564p2 Ns564p1 614572177 536870912 1 163840000 614572177 536870912 1 163840000 307286088 268435456 3 268435456 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns564p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns564p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns564p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns564p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns564p8 := nat_lit 6573389678388862351155759458724141871788046104702795740939545775355827438482086890337971184306503456724674701876007739166027855002689342487126242201873902293161938510715598861337724155978462934346539722102807352693564004597780440630880721700532830491857281958381906437104026277614553345439647264822859384496062743250358046048880947907642984145065307980413206151384068885350206914057384338280179177725692904928360597982006748935836093248417685721122261418062303135764477585928239149568275027355236134745000697766005167655784166499502223346815249842007858448160935771607172549259242715110048115445292136446613946552506617916138661398090061483392335970316672263498462800198746102072055363920390651513279180731193678641632192805423820381724597815072905552156968003637925334143020171520625 

noncomputable def Ns564p9 := nat_lit 702614123509571190207434367497643053726389003684617183996726348470791223755418688598787599501240412886827946200799073391711533512528899996899108221816773619593298708861540359234024488137706935294538610329535191474811214152768697527793266408685885408431698677504366547635987768499962038530066773279961750661013789994039311989768445302208965109624014234440840481147386361324656837522786906307734587964680180646868573806366973424595907336814393861048013934514934272026683624090151873353554279683010347128413433843775162422864773798490322287367830744467164676975854073090397461536167654230134598982106570951920409048997311342333559851528447946435833392322432321465286801524775001800171249769824525762984779161997185015423416919065587459911326773695449510414365759468097615398764501522575 

noncomputable def Ns564p10 := nat_lit 541392566138474909591412279139378993255101875047003589935782329109463644892392322173295519240510467068363239080443023466297029982601757003829684821059136286585994161974307047499333049696728682047261006046816072264069316416942594393775486731411634963656291648112663555457379375292741727868294229136381639619442405391741167595634732196900940186574903289828257139713673376723681752760045249773972946001592268830432998579610986951410273979009689762628244990479410235165324966379611071762421902787196495466840333515349387051622842182127210560393625584510287605139387730811840242457253978115925211125629993337408355023684205061830608267784338105681114876710224147942516826039256450164994945245879666660679160980454641866547806615379410050641833332584350523565507268843323231339375 

noncomputable def Ns564p11 := BSN.log_dyadic_bound Ns564p6 Ns564p7 16 15 Ns564p8 536870912 163840000 Ns564p9 Ns564p10 614572177 Ns564p4 Ns564p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns564p6) (BSN.artanhQ Ns564p7) 0 15 Ns564p9 Ns564p8 Ns564p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns564p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns564p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns564p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns564p15 := nat_lit 6573389678388957581038003304946500209472262679236338533996718496177406624059139082449994147026037314666926693076053053862592074936423388863596813530408382584499373597031431853921413941298322255656576695489433951602693567143885654771592106690789036275646003378131729522606930818530515414843848039000889531334935427389830473690579523667466182538201372727149023132371319359578146651783732835416323469915494090659780509855937937675396353734377829186029766969614606089327824892671842834136516654569045504808111725705550748907924941183733134599012581542910476929082687043869700761244349471219210833189555347464155979117619898077496880661665775336657207488512148128426326823595335945176245554694022845325705851563290369414226074229552025260849280553835909109839168582914725334143020171520625 

noncomputable def Ns564p16 := nat_lit 702614123509582134195699383225799303120857312948289364169564431944606347230839067212220070086773571232938822231607515388838247088164426860334641427891924556959013106220289292017417932077264689683982462259236603120411894481357554273197237433243865910367073588753830073256225145709268648257922640132615276470163987114280905050307903018021985933333474523803420109333064989110261463867307642914581311357336787925252212965840242792007601256472655504246146516404729632839909377990937267835233434162343951883521915890115762575574377037535717851480622294463860980162526686236248764915916362237196611189536095144270945605478817014333998082847306947436470576941659846222535334992451365706225994338058508887942119777908276510373758951874822816373072605980596581754554466975502415398764501522575 

noncomputable def Ns564p17 := nat_lit 541392566138490077533790984620311058177654278555980714203107761719673916425133183846751239616284470803704371181920004286935467360846628369375164068764590875438310007353955324186636582299553928814156491749519256774653872128089233575343481607925575468185460509172779152955629338248076232826253005811067688706928164570779608774451502836676056177667078421728722179008027603013170304530594440809888606240685402729798990208830923560422594844623819537735750113690675240496626214395332044296593456069970973486809806367897564108502902289348063943342100923856630472249952347312756547637419241376870243223562839253667975765230153074010838184467350558565952691487980795548332122966513692688198426849374346091985539852378055886379210372820263137502377721028428076000707268843323231339375 

noncomputable def Ns564p18 := BSN.log_dyadic_bound Ns564p13 Ns564p14 16 15 Ns564p15 536870912 163840000 Ns564p16 Ns564p17 614572177 Ns564p12 Ns564p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns564p13) (BSN.artanhQ Ns564p14) 0 15 Ns564p16 Ns564p15 Ns564p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns564p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 307286088 268435456 3 268435456 38410761 33554432 3 268435456 (Ns564p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns564p0 Ns564p1 614572177 536870912 1 163840000 Bool.false (BSN.logfrac_isNear Ns564p4 Ns564p5 1 Ns564p0 Ns564p1 614572177 536870912 163840000 rfl rfl rfl (Ns564p11 rfl))) (BSN.isNear_log_sfrac Ns564p2 Ns564p1 614572177 536870912 1 163840000 Bool.false (BSN.logfrac_isNear Ns564p12 Ns564p5 1 Ns564p2 Ns564p1 614572177 536870912 163840000 rfl rfl rfl (Ns564p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS565to576.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 3 268435456 := Ns564p19 

noncomputable def Ns564p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 33554432 10240000 385100712855 135135 23258159 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz583 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz316 := qz583

noncomputable abbrev qz0 := qz316

theorem RS565to576.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 23258159 33554432 1 10240000 := BSN.isNear_log_sfrac 2 1 23258159 33554432 1 10240000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 23258159 33554432 10240000 rfl rfl rfl (Ns564p20 rfl)) 

theorem RS565to576.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 372130544 536870912 53 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 23258159 33554432 1 10240000 372130544 536870912 53 536870912 RS565to576.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz584 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz584

noncomputable def Ns564p21 := @Enclosure.Real.IsNear.inv_image qz317 94906265 67108864 1 67108864 23726566 23726567 33554432 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 94906265 67108864 1 67108864 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 94906265 67108864 1 67108864 94906265 67108864 1 67108864 (BSN.sqrt_enclosure 2 1 47453132 47453133 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS565to576.d8 : Enclosure.Real.IsNear qz320 Bool.false 47453133 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 47453133 67108864 1 67108864 47453133 67108864 1 67108864 (Ns564p21 rfl rfl) rfl 

theorem RS565to576.d9 : Enclosure.Real.IsNear qz320 Bool.false 379625064 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 47453133 67108864 1 67108864 379625064 536870912 8 536870912 RS565to576.d8 rfl 

noncomputable def Ns564p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 33554432 10240000 13079757671720842725 316234143225 36863311 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS565to576.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 36863311 33554432 1 10240000 := BSN.isNear_log_sfrac 3 1 36863311 33554432 1 10240000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 36863311 33554432 10240000 rfl rfl rfl (Ns564p22 rfl)) 

theorem RS565to576.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 589812976 536870912 53 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 36863311 33554432 1 10240000 589812976 536870912 53 536870912 RS565to576.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns564p23 := @Enclosure.Real.IsNear.inv_image qz321 116235963 67108864 1 67108864 19372660 19372661 33554432 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 116235963 67108864 1 67108864 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 116235963 67108864 1 67108864 116235963 67108864 1 67108864 (BSN.sqrt_enclosure 3 1 58117981 58117982 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS565to576.d12 : Enclosure.Real.IsNear qz323 Bool.false 38745321 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 38745321 67108864 1 67108864 38745321 67108864 1 67108864 (Ns564p23 rfl rfl) rfl 

theorem RS565to576.d13 : Enclosure.Real.IsNear qz323 Bool.false 309962568 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 38745321 67108864 1 67108864 309962568 536870912 8 536870912 RS565to576.d12 rfl 

noncomputable def Ns564p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns564p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns564p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns564p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns564p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns564p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns564p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns564p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns564p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns564p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns564p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns564p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns564p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns564p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns564p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns564p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns564p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns564p25 Ns564p26 Ns564p27 Ns564p28 200200021673987500790625 Ns564p29 Ns564p30 Ns564p31 Ns564p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns564p32 Ns564p33 151412625 Ns564p34 Ns564p35 1322214852783825 Ns564p27 Ns564p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns564p32 Ns564p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns564p34 Ns564p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns564p36 Ns564p37 1267389585 Ns564p38 Ns564p39 1927077560082675 Ns564p29 Ns564p30 Ns564p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns564p36 Ns564p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns564p38 Ns564p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS565to576.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns564p24 Ns564p25 1 Ns564p26 := Ns564p40 rfl rfl rfl 

noncomputable def Ns564p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns564p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns564p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns564p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns564p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns564p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns564p25 Ns564p26 Ns564p42 Ns564p43 9945 Ns564p44 Ns564p45 65835 Ns564p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns564p42 Ns564p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns564p44 Ns564p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS565to576.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns564p41 Ns564p25 1 Ns564p26 := Ns564p46 rfl 

noncomputable def Ns564p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns564p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS565to576.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns564p47 Ns564p25 1 Ns564p48 := BSN.pi_combine Ns564p24 Ns564p41 Ns564p25 Ns564p26 Ns564p48 Ns564p47 rfl rfl rfl rfl RS565to576.d14 RS565to576.d15 

theorem RS565to576.d17 : Enclosure.Real.IsNear Real.pi Bool.false 28296951008113761 9007199254740992 1 9007199254740992 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns564p47 Ns564p25 1 Ns564p48 28296951008113761 9007199254740992 1 9007199254740992 RS565to576.d16 rfl 

noncomputable def Ns564p49 := nat_lit 129013261453190219981479458510875701904296875 

noncomputable def Ns564p50 := nat_lit 20028702544022979302942508184499384445755625 

noncomputable def Ns564p51 := nat_lit 105610919306899072369715234453255625 

noncomputable def Ns564p52 := nat_lit 11743816085855617508865225 

noncomputable def Ns564p53 := nat_lit 24536140990734100341796875 

noncomputable def Ns564p54 := BSN.log_dyadic_bound 3 5 18 17 Ns564p49 33554432 10240000 Ns564p50 Ns564p51 46516319 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 3) (BSN.artanhQ 5) 0 17 8 816252149187356400 5258090972900390625 87256779635025 Ns564p52 Ns564p53 1210346287688420415225 Ns564p50 Ns564p49 Ns564p51 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 3) (BSN.artanhQ 5) 0 8 816252149187356400 5258090972900390625 87256779635025 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 3) (BSN.artanhQ 5) 8 17 Ns564p52 Ns564p53 1210346287688420415225 rfl rfl rfl rfl)) rfl rfl 

theorem RS565to576.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 46516319 33554432 1 10240000 := BSN.isNear_log_sfrac 4 1 46516319 33554432 1 10240000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 46516319 33554432 10240000 rfl rfl rfl (Ns564p54 rfl rfl)) 

theorem RS565to576.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 744261104 536870912 53 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 46516319 33554432 1 10240000 744261104 536870912 53 536870912 RS565to576.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns564p55 := @Enclosure.Real.IsNear.inv_image qz325 134217729 67108864 1 67108864 16777215 16777216 33554432 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 134217729 67108864 1 67108864 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 134217729 67108864 1 67108864 134217729 67108864 1 67108864 (BSN.sqrt_enclosure 4 1 67108864 67108865 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS565to576.d20 : Enclosure.Real.IsNear qz327 Bool.false 33554431 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 33554431 67108864 1 67108864 33554431 67108864 1 67108864 (Ns564p55 rfl rfl) rfl 

theorem RS565to576.d21 : Enclosure.Real.IsNear qz327 Bool.false 268435448 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 33554431 67108864 1 67108864 268435448 536870912 8 536870912 RS565to576.d20 rfl 

noncomputable def Ns564p56 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns564p57 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns564p58 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns564p59 := nat_lit 885951608314392539099884620 

noncomputable def Ns564p60 := nat_lit 1286943652057122751813246125 

noncomputable def Ns564p61 := BSN.log_dyadic_bound 2 3 22 21 Ns564p56 33554432 10240000 Ns564p57 Ns564p58 54003774 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns564p59 Ns564p60 84004523356416638976000 Ns564p57 Ns564p56 Ns564p58 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns564p59 Ns564p60 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS565to576.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 54003774 33554432 1 10240000 := BSN.isNear_log_sfrac 5 1 54003774 33554432 1 10240000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 54003774 33554432 10240000 rfl rfl rfl (Ns564p61 rfl rfl)) 

theorem RS565to576.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 864060384 536870912 53 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 54003774 33554432 1 10240000 864060384 536870912 53 536870912 RS565to576.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns564p62 := @Enclosure.Real.IsNear.inv_image qz328 150059981 67108864 1 67108864 15005998 15005999 33554432 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 150059981 67108864 1 67108864 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 150059981 67108864 1 67108864 150059981 67108864 1 67108864 (BSN.sqrt_enclosure 5 1 75029990 75029991 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS565to576.d24 : Enclosure.Real.IsNear qz329 Bool.false 30011997 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 30011997 67108864 1 67108864 30011997 67108864 1 67108864 (Ns564p62 rfl rfl) rfl 

theorem RS565to576.d25 : Enclosure.Real.IsNear qz329 Bool.false 240095976 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 30011997 67108864 1 67108864 240095976 536870912 8 536870912 RS565to576.d24 rfl 

noncomputable def Ns564p63 := nat_lit 2166104270535356806332416 

noncomputable def Ns564p64 := nat_lit 1208925819614629174706176 

noncomputable def Ns564p65 := BSN.log_dyadic_bound 2 10 6 5 103950000000000 33554432 10240000 1420244935680 967680 13605151 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 2) (BSN.artanhQ 10) 0 5 1420244935680 103950000000000 967680 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz584)

theorem RS565to576.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683612241143 2251799813685248 24414063 250000000000000 := BSN.isNear_log_sfrac 6 1 4034683612241143 2251799813685248 24414063 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false Ns564p63 Ns564p64 1000000020480000 10240000000000000000000 4034683612241143 2251799813685248 24414063 250000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 13605151 33554432 24973259072661432 36028797018963968 10240000 1000000000000000 rfl rfl rfl rfl (Ns564p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS565to576.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 961943533 536870912 54 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683612241143 2251799813685248 24414063 250000000000000 961943533 536870912 54 536870912 RS565to576.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns564p66 := @Enclosure.Real.IsNear.inv_image qz331 164382475 67108864 1 67108864 13698539 13698540 33554432 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 164382475 67108864 1 67108864 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 164382475 67108864 1 67108864 164382475 67108864 1 67108864 (BSN.sqrt_enclosure 6 1 82191237 82191238 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS565to576.d28 : Enclosure.Real.IsNear qz332 Bool.false 27397079 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 27397079 67108864 1 67108864 27397079 67108864 1 67108864 (Ns564p66 rfl rfl) rfl 

theorem RS565to576.d29 : Enclosure.Real.IsNear qz332 Bool.false 219176632 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 27397079 67108864 1 67108864 219176632 536870912 8 536870912 RS565to576.d28 rfl 

noncomputable def Ns564p67 := nat_lit 2352460989330532755046400 

noncomputable def Ns564p68 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 33554432 10240000 11010900719820672 5524329195 18777589 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz584)

theorem RS565to576.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381800050531575 2251799813685248 24414063 250000000000000 := BSN.isNear_log_sfrac 7 1 4381800050531575 2251799813685248 24414063 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false Ns564p67 Ns564p64 1000000020480000 10240000000000000000000 4381800050531575 2251799813685248 24414063 250000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 18777589 33554432 24973259072661432 36028797018963968 10240000 1000000000000000 rfl rfl rfl rfl (Ns564p68 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS565to576.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 1044702541 536870912 54 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381800050531575 2251799813685248 24414063 250000000000000 1044702541 536870912 54 536870912 RS565to576.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns564p69 := @Enclosure.Real.IsNear.inv_image qz334 177553365 67108864 1 67108864 12682383 12682384 33554432 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 177553365 67108864 1 67108864 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 177553365 67108864 1 67108864 177553365 67108864 1 67108864 (BSN.sqrt_enclosure 7 1 88776682 88776683 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS565to576.d32 : Enclosure.Real.IsNear qz335 Bool.false 25364767 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 25364767 67108864 1 67108864 25364767 67108864 1 67108864 (Ns564p69 rfl rfl) rfl 

theorem RS565to576.d33 : Enclosure.Real.IsNear qz335 Bool.false 202918136 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 25364767 67108864 1 67108864 202918136 536870912 8 536870912 RS565to576.d32 rfl 

noncomputable def Ns564p70 := nat_lit 2513890570116003237199872 

noncomputable def Ns564p71 := BSN.log_dyadic_bound 0 16 1 0 1 33554432 10240000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz584)

theorem RS565to576.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 97656253 1000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 97656253 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false Ns564p70 Ns564p64 1000000030720000 10240000000000000000000 9364972152248037 4503599627370496 97656253 1000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 33554432 24973259072661432 36028797018963968 10240000 1000000000000000 rfl rfl rfl rfl (Ns564p71 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS565to576.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 1116391676 536870912 54 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 97656253 1000000000000000 1116391676 536870912 54 536870912 RS565to576.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns564p72 := @Enclosure.Real.IsNear.inv_image qz337 189812531 67108864 1 67108864 11863283 11863284 33554432 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 189812531 67108864 1 67108864 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 189812531 67108864 1 67108864 189812531 67108864 1 67108864 (BSN.sqrt_enclosure 8 1 94906265 94906266 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS565to576.d36 : Enclosure.Real.IsNear qz338 Bool.false 23726567 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 23726567 67108864 1 67108864 23726567 67108864 1 67108864 (Ns564p72 rfl rfl) rfl 

theorem RS565to576.d37 : Enclosure.Real.IsNear qz338 Bool.false 189812536 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 23726567 67108864 1 67108864 189812536 536870912 8 536870912 RS565to576.d36 rfl 

noncomputable def Ns564p73 := nat_lit 2656281492024125531619328 

noncomputable def Ns564p74 := BSN.log_dyadic_bound 1 17 3 2 1252815 33554432 10240000 1448 3 3952142 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz584)

theorem RS565to576.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 97656253 1000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 97656253 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false Ns564p73 Ns564p64 1000000030720000 10240000000000000000000 9895419672221413 4503599627370496 97656253 1000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 3952142 33554432 24973259072661432 36028797018963968 10240000 1000000000000000 rfl rfl rfl rfl (Ns564p74 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS565to576.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 1179625948 536870912 54 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 97656253 1000000000000000 1179625948 536870912 54 536870912 RS565to576.d38 rfl 

noncomputable abbrev qz340 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns564p75 := @Enclosure.Real.IsNear.inv_image qz340 201326593 67108864 1 67108864 11184810 11184811 33554432 (@Enclosure.Real.IsNear.of_eq qz340 (Real.sqrt qz339) Bool.false 201326593 67108864 1 67108864 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 201326593 67108864 1 67108864 201326593 67108864 1 67108864 (BSN.sqrt_enclosure 9 1 100663296 100663297 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS565to576.d40 : Enclosure.Real.IsNear qz341 Bool.false 22369621 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 22369621 67108864 1 67108864 22369621 67108864 1 67108864 (Ns564p75 rfl rfl) rfl 

theorem RS565to576.d41 : Enclosure.Real.IsNear qz341 Bool.false 178956968 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 22369621 67108864 1 67108864 178956968 536870912 8 536870912 RS565to576.d40 rfl 

noncomputable def Ns564p76 := nat_lit 2783654566499630094221312 

noncomputable def Ns564p77 := BSN.log_dyadic_bound 2 18 4 3 3571283520 33554432 10240000 14806464 960 7487455 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz584)

theorem RS565to576.d42 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921350850277 4503599627370496 97656253 1000000000000000 := BSN.isNear_log_sfrac 10 1 10369921350850277 4503599627370496 97656253 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false Ns564p76 Ns564p64 1000000030720000 10240000000000000000000 10369921350850277 4503599627370496 97656253 1000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 7487455 33554432 24973259072661432 36028797018963968 10240000 1000000000000000 rfl rfl rfl rfl (Ns564p77 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS565to576.d43 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 1236190956 536870912 54 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921350850277 4503599627370496 97656253 1000000000000000 1236190956 536870912 54 536870912 RS565to576.d42 rfl 

noncomputable abbrev qz343 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns564p78 := @Enclosure.Real.IsNear.inv_image qz343 212216861 67108864 1 67108864 10610843 10610844 33554432 (@Enclosure.Real.IsNear.of_eq qz343 (Real.sqrt qz342) Bool.false 212216861 67108864 1 67108864 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz342) Bool.false 212216861 67108864 1 67108864 212216861 67108864 1 67108864 (BSN.sqrt_enclosure 10 1 106108430 106108431 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz344 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS565to576.d44 : Enclosure.Real.IsNear qz344 Bool.false 21221687 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz344 Bool.false 21221687 67108864 1 67108864 21221687 67108864 1 67108864 (Ns564p78 rfl rfl) rfl 

theorem RS565to576.d45 : Enclosure.Real.IsNear qz344 Bool.false 169773496 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz344 Bool.false 21221687 67108864 1 67108864 169773496 536870912 8 536870912 RS565to576.d44 rfl 

noncomputable def Ns564p79 := nat_lit 2898877505641241362038784 

noncomputable def Ns564p80 := BSN.log_dyadic_bound 3 19 5 4 16049467073745 33554432 10240000 135406373544 688905 10685534 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 19) 0 4 135406373544 16049467073745 688905 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11) qz584)

theorem RS565to576.d46 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 10799160248194789 4503599627370496 97656253 1000000000000000 := BSN.isNear_log_sfrac 11 1 10799160248194789 4503599627370496 97656253 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false Ns564p79 Ns564p64 1000000030720000 10240000000000000000000 10799160248194789 4503599627370496 97656253 1000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 10685534 33554432 24973259072661432 36028797018963968 10240000 1000000000000000 rfl rfl rfl rfl (Ns564p80 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS565to576.d47 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 1287360220 536870912 54 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 10799160248194789 4503599627370496 97656253 1000000000000000 1287360220 536870912 54 536870912 RS565to576.d46 rfl 

noncomputable abbrev qz346 := (Real.sqrt (@Nat.cast Real Real.instNatCast 11))

noncomputable def Ns564p81 := @Enclosure.Real.IsNear.inv_image qz346 222574921 67108864 1 67108864 10117041 10117042 33554432 (@Enclosure.Real.IsNear.of_eq qz346 (Real.sqrt qz345) Bool.false 222574921 67108864 1 67108864 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz345) Bool.false 222574921 67108864 1 67108864 222574921 67108864 1 67108864 (BSN.sqrt_enclosure 11 1 111287460 111287461 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz347 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

theorem RS565to576.d48 : Enclosure.Real.IsNear qz347 Bool.false 20234083 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz347 Bool.false 20234083 67108864 1 67108864 20234083 67108864 1 67108864 (Ns564p81 rfl rfl) rfl 

theorem RS565to576.d49 : Enclosure.Real.IsNear qz347 Bool.false 161872664 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz347 Bool.false 20234083 67108864 1 67108864 161872664 536870912 8 536870912 RS565to576.d48 rfl 

noncomputable def Ns564p82 := nat_lit 3004067793907357885399040 

noncomputable def Ns564p83 := BSN.log_dyadic_bound 4 20 6 5 106444800000000000 33554432 10240000 1454330814136320 990904320 13605151 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 4) (BSN.artanhQ 20) 0 5 1454330814136320 106444800000000000 990904320 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz740 := (Enclosure.sfrac Bool.false 12 1)

noncomputable abbrev qz585 := qz740

noncomputable abbrev qz348 := qz585

noncomputable abbrev qz1 := qz348

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12) qz584)

theorem RS565to576.d50 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 11191024608564965 4503599627370496 97656253 1000000000000000 := BSN.isNear_log_sfrac 12 1 11191024608564965 4503599627370496 97656253 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz349) Bool.false Ns564p82 Ns564p64 1000000030720000 10240000000000000000000 11191024608564965 4503599627370496 97656253 1000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 13605151 33554432 24973259072661432 36028797018963968 10240000 1000000000000000 rfl rfl rfl rfl (Ns564p83 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS565to576.d51 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 1334074092 536870912 54 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 11191024608564965 4503599627370496 97656253 1000000000000000 1334074092 536870912 54 536870912 RS565to576.d50 rfl 

noncomputable abbrev qz350 := (Real.sqrt (@Nat.cast Real Real.instNatCast 12))

noncomputable def Ns564p84 := @Enclosure.Real.IsNear.inv_image qz350 232471925 67108864 1 67108864 9686330 9686331 33554432 (@Enclosure.Real.IsNear.of_eq qz350 (Real.sqrt qz349) Bool.false 232471925 67108864 1 67108864 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz349) Bool.false 232471925 67108864 1 67108864 232471925 67108864 1 67108864 (BSN.sqrt_enclosure 12 1 116235962 116235963 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz351 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))

theorem RS565to576.d52 : Enclosure.Real.IsNear qz351 Bool.false 19372661 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz351 Bool.false 19372661 67108864 1 67108864 19372661 67108864 1 67108864 (Ns564p84 rfl rfl) rfl 

theorem RS565to576.d53 : Enclosure.Real.IsNear qz351 Bool.false 154981288 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz351 Bool.false 19372661 67108864 1 67108864 154981288 536870912 8 536870912 RS565to576.d52 rfl 

theorem RS565to576.d54 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz741 := (@instHMul Real Real.instMul)

noncomputable abbrev qz586 := (@HMul.hMul Real Real Real qz741 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz352 := qz586

noncomputable abbrev qz2 := qz352

theorem RS565to576.d55 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS565to576.d54 rfl 

noncomputable abbrev qz353 := (@Inv.inv Real Real.instInv qz586)

noncomputable abbrev qz3 := qz353

theorem RS565to576.d56 : Enclosure.Real.IsNear qz3 Bool.false 10680707 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 10680707 67108864 1 67108864 10680707 67108864 1 67108864 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 5340353 5340354 33554432 RS565to576.d55 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns564p85 := nat_lit 5902958103587056517120000 

noncomputable def Ns564p86 := nat_lit 176240642139187505338846806016 

noncomputable abbrev qz742 := (Enclosure.sfrac Bool.false 959413 1000)

noncomputable abbrev qz587 := qz742

noncomputable abbrev qz354 := qz587

noncomputable abbrev qz4 := qz354

noncomputable abbrev qz588 := qz741

noncomputable abbrev qz355 := qz588

noncomputable abbrev qz5 := qz355

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 12)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz743 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 959413 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz589 := qz743

noncomputable abbrev qz356 := qz589

noncomputable abbrev qz8 := qz356

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz744 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 959413 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz590 := qz744

noncomputable abbrev qz357 := qz590

noncomputable abbrev qz10 := qz357

noncomputable abbrev qz591 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns564p87 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HMul.hMul Real Real Real qz5 qz591 (Zeta.RiemannSiegel.correction qz10)) 10654901 67108864 16373 16777216 1126646212008580178391 9444732965739290427392 22023170360761415607 Ns564p85 Ns564p86 

noncomputable def Ns564p88 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin BSN.quadSignPos 11 12 959413 1000 287 536870912 268435456 9007199254740992 Bool.false 1037276676864 4464 1334074092 54 154981288 8 

noncomputable def Ns564p89 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 959413 1000 176 234 536870912 268435456 9007199254740992 Bool.false 1037276676864 4464 

noncomputable def Ns564p90 := Ns564p89 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.true 228171731 210932 Bool.true 317582055 Bool.true 497777458 28296951008113761 1 Bool.false 445646561 Bool.false Bool.false 322170841 Bool.true Bool.true 184384069 

noncomputable def Ns564p91 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 959413 1000 40 112 536870912 268435456 9007199254740992 Bool.false 1037276676864 4464 

noncomputable def Ns564p92 := Ns564p91 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 595133529 172260 Bool.true 71415920 Bool.true 20528852 28296951008113761 1 Bool.false 532127949 Bool.false Bool.false 536478469 Bool.false Bool.true 228171731 

noncomputable def Ns564p93 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 959413 1000 135 41 536870912 268435456 9007199254740992 Bool.false 1037276676864 4464 

noncomputable def Ns564p94 := Ns564p93 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.true 640130046 127998 Bool.false 528040405 Bool.false 399568777 28296951008113761 1 Bool.false 446929258 Bool.false Bool.false 363689169 Bool.true Bool.true 595133529 

noncomputable def Ns564p95 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 959413 1000 383 246 536870912 268435456 9007199254740992 Bool.false 1037276676864 4464 

noncomputable def Ns564p96 := Ns564p95 744261104 53 268435448 8 864060384 53 240095976 8 Bool.true 747397284 75585 Bool.false 233308240 Bool.false 830456962 28296951008113761 1 Bool.false 226033835 Bool.false Bool.false 12856665 Bool.true Bool.true 640130046 

noncomputable def Ns564p97 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 959413 1000 806 558 536870912 268435456 9007199254740992 Bool.false 1037276676864 4464 

noncomputable def Ns564p98 := Ns564p97 372130544 53 379625064 8 589812976 53 309962568 8 Bool.true 536870576 4517 Bool.false 538020888 Bool.false 832750175 28296951008113761 1 Bool.false 289104255 Bool.true Bool.false 10563999 Bool.true Bool.true 747397284 

noncomputable def Ns564p99 := nat_lit 244298590251336276529943595432517322416154273719564811276659 

noncomputable def Ns564p100 := nat_lit 126443416567543311239777211519860618100831122519752704000 

noncomputable def Ns564p101 := nat_lit 390184066278932616886880698380640000 

noncomputable def Ns564p102 := nat_lit 2246086278168905025860930129508485785920 

noncomputable abbrev qz358 := (@Eq.refl Real qz587)

noncomputable abbrev qz11 := qz358

noncomputable def Ns564p103 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 959413 1000 3681894218276 16000000 1918826 4000 2000 Ns564p101 Ns564p102 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns564p104 := nat_lit 78175548880427608489581950538405543173169367590260739608530880 

noncomputable abbrev qz745 := (@instHSub Real Real.instSub)

noncomputable abbrev qz592 := qz745

noncomputable abbrev qz359 := qz592

noncomputable abbrev qz593 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz746 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz747 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz594 := (@HSub.hSub Real Real Real qz745 qz746 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz747 (@Nat.cast Real Real.instNatCast 1918826))))

noncomputable abbrev qz360 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 959413 4000) (Real.log (Enclosure.sfrac Bool.false 3681894218276 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz594))

noncomputable abbrev qz595 := (Enclosure.sfrac Bool.false 959413 2000)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz360 qz595) (@HMul.hMul Real Real Real qz355 qz595 (Real.log Real.pi)))

noncomputable def Ns564p105 := @Enclosure.Real.IsNear.addLit_ft_p qz12 (Enclosure.sfrac Bool.true Ns564p101 Ns564p102) 34805232848441849451539 18014398509481984000 136207600352815891 16384000000000000000000 Ns564p101 Ns564p102 0 1 Ns564p104 

noncomputable def Ns564p106 := nat_lit 2335739637714416686751805341696000 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz359 qz360 qz595)

noncomputable def Ns564p107 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (@HMul.hMul Real Real Real qz5 qz595 (Real.log Real.pi)) 44697558141455456048147 18014398509481984000 47237028132709 16000000000000000000 36851783443293 67108864000 2878239 536870912000 Ns564p106 34805232848441849451539 18014398509481984000 

noncomputable def Ns564p108 := nat_lit 89395116282910912096294000 

noncomputable abbrev qz14 := qz360

noncomputable def Ns564p109 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz595 53339182200044275405843 18014398509481984000 47237028132709 16000000000000000000 959413 2000 0 1 Ns564p108 44697558141455456048147 18014398509481984000 47237028132709 16000000000000000000 

noncomputable def Ns564p110 := nat_lit 120109160540183195874813706140662104064 

noncomputable def Ns564p111 := nat_lit 119406562494135408082812928 

noncomputable def Ns564p112 := nat_lit 9671406556917033397649408 

noncomputable def Ns564p113 := nat_lit 93938896432268646782334682914642160057818925709173213411004818747273072023611960961668266677865781739838178542366340177873245313485380005718413445115073775794716745637906280293492326400 

noncomputable def Ns564p114 := nat_lit 2466966349340719298058110494539281904292773077365638605710456838335139897135869523397584758054161918786970011856728789562839493905529460029303394038573137566952691638668286804979875840 

noncomputable def Ns564p115 := nat_lit 85150781148230799419744172821302758098821139532114575626286480406387690240998663726334228346178889435976588408672699364164610444428076127958267719652422436345876685499672821760 

noncomputable def Ns564p116 := BSN.log_dyadic_bound 1584742218276 5779046218276 8 7 Ns564p113 268435456 81920000 Ns564p114 Ns564p115 151088123 7363788436552 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1584742218276) (BSN.artanhQ 5779046218276) 0 7 Ns564p114 Ns564p113 Ns564p115 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz361 := (Real.log (Enclosure.sfrac Bool.false 3681894218276 16000000))

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns564p117 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 959413 4000) qz361 959413 4000 0 1 55603013604011111 4503599627370496 48828193 4000000000000000 53346254090865112037843 18014398509481984000 46846403130709 16000000000000000000 (Enclosure.Real.IsNear.const Bool.false 959413 4000) (BSN.isNear_log_sfrac 3681894218276 16000000 55603013604011111 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3681894218276) qz362)) Bool.false Ns564p111 Ns564p112 1000001392640000 81920000000000000000000 55603013604011111 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3681894218276 16000000 17 7363788436552 4194304000000 151088123 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns564p116 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p118 := BSN.arctan_dyadic_bound_f 1000 1918826 1 0 33554432 10240000 0 1 1 0 1 1 17486 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1918826) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1918826) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz596 := qz746

noncomputable abbrev qz363 := qz596

noncomputable abbrev qz15 := qz363

noncomputable abbrev qz597 := qz747

noncomputable abbrev qz364 := qz597

noncomputable abbrev qz16 := qz364

noncomputable abbrev qz748 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz598 := qz748

noncomputable abbrev qz365 := qz598

noncomputable abbrev qz17 := (@Enclosure.Real.IsNear.mulLit_ff qz365 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def Ns564p119 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1918826))) 884279719003555 562949953421312 1 2000000000000000 17486 33554432 1 10240000 29661659957398368944128 883986352604579 562949953421312 195312501 2000000000000000 qz17 (Ns564p118 rfl) rfl rfl 

noncomputable abbrev qz366 := (@HMul.hMul Real Real Real qz588 qz593 qz594)

noncomputable abbrev qz18 := qz366

noncomputable abbrev qz367 := qz593

noncomputable abbrev qz19 := qz367

noncomputable abbrev qz368 := qz594

noncomputable abbrev qz20 := qz368

noncomputable abbrev qz369 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns564p120 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 959413 4000) qz361) qz18 53346254090865112037843 18014398509481984000 46846403130709 16000000000000000000 883986352604579 2251799813685248 195312501 8000000000000000 Ns564p110 53339182200044275405843 18014398509481984000 47237028132709 16000000000000000000 (Ns564p117 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz20 1 4 0 1 883986352604579 562949953421312 195312501 2000000000000000 883986352604579 2251799813685248 195312501 8000000000000000 qz369 Ns564p119 rfl) 

noncomputable def Ns564p121 := @Ns564p105 Ns564p99 Ns564p100 136207600352815891 16384000000000000000000 (@Ns564p107 136207600352815891 16384000000000000000000 (Ns564p109 (Ns564p120 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 959413 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz595 (Real.log Real.pi) 959413 2000 0 1 38410761 33554432 3 268435456 36851783443293 67108864000 2878239 536870912000 (Enclosure.Real.IsNear.const Bool.false 959413 2000) RS565to576.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns564p101 Ns564p102) 

noncomputable abbrev qz370 := (@instHAdd Real Real.instAdd)

noncomputable def Ns564p122 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns564p99 Ns564p100 136207600352815891 16384000000000000000000 4051862019 2097152 279 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz370 qz12 (Enclosure.sfrac Bool.true Ns564p101 Ns564p102)) Bool.false Ns564p99 Ns564p100 136207600352815891 16384000000000000000000 Ns564p103 (Ns564p121 rfl rfl)) 

noncomputable def Ns564p123 := nat_lit 14339645564434808976720949102368567046583825529163944266362970891231219443196111757028660139525406781594399825422504225316963440825272138034081 

noncomputable def Ns564p124 := nat_lit 282877490902138091004622673603363019119652456796264491099280832830873987773707601701812303598028785564314492868916806270538811366318583631052800 

noncomputable def Ns564p125 := nat_lit 10164077646254256925687554113803996313638384904851784431785840877441296268612799765320847635354978023018972399384807435839037786008677281 

noncomputable def Ns564p126 := nat_lit 71609385416142981215742411210998239838554402730712082133571362524878358588928395473874480276252591970864511200782838477026400440695384377486241 

noncomputable def Ns564p127 := nat_lit 9900712181574833185161793576117705669187835987869257188474829149080589572079766059563430625931007494751007250412088219468858397821150427086848000 

noncomputable abbrev qz371 := (BSN.sinEvenQ 137438953472)

noncomputable abbrev qz372 := (BSN.sinOddQ 137438953472)

noncomputable def Ns564p128 := BSN.sin_dyadic_bound_f 215735855463 137438953472 4 3 67108864 20500001 Ns564p123 Ns564p124 Ns564p125 Ns564p126 Ns564p127 Ns564p125 67108822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215735855463) qz371 0 3 Ns564p123 Ns564p124 Ns564p125 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215735855463) qz372 0 3 Ns564p126 Ns564p127 Ns564p125 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p129 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4051862019) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 4051862019 2097152 279 33554432 Bool.true 67108822 67108864 1 10240000 (Ns564p122 rfl) (Enclosure.sfrac_false_div 4051862019 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4051862019) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474408163219606945660928) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 67108822 67108864 307 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 4051862019 2097152 226375608064910080 72057594037927936 307 474408163219606945660928 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108822 67108864 474408163219606945660928 302231454903657293676544 215735855463 137438953472 20500001 20480000 (Ns564p128 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p130 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns564p99 Ns564p100 136207600352815891 16384000000000000000000 1037276676864 536870912 4464 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz370 qz12 (Enclosure.sfrac Bool.true Ns564p101 Ns564p102)) Bool.false Ns564p99 Ns564p100 136207600352815891 16384000000000000000000 Ns564p103 (Ns564p121 rfl rfl)) 

noncomputable def Ns564p131 := Ns564p98 75585 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 806 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 289104255 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 558 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 10563999 536870912) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 33554411 33554432 176423 20971520000 536870576 536870912 4517 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554411 33554432 176423 20971520000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 67108822 67108864 2890514432 343597383680000 33554411 33554432 176423 20971520000 (Ns564p129 rfl rfl) rfl)) rfl) (Ns564p130 rfl) RS565to576.d7 

noncomputable def Ns564p132 := nat_lit 11548935044567762791643623876441329409933983789276949404694651257612307005850375648958378240480015997557104705536 

noncomputable def Ns564p133 := nat_lit 274647376664257459544000446540783031995164976078897331880025758552119769180746491160307949742358795015190845849600 

noncomputable def Ns564p134 := nat_lit 588287530849602829897781428315920999278902019491599172989759965047926674834895365241111096534156082937856 

noncomputable def Ns564p135 := nat_lit 70035511142194956860739291624069690454077018074723353637461443633312006222718618857467492293337932592671421890560 

noncomputable def Ns564p136 := nat_lit 24992911276447428818504040635211255911560012823179657201082344028242898995447930695588023426554650346382366972313600 

noncomputable abbrev qz373 := (BSN.cosEvenQ 536870912)

noncomputable abbrev qz374 := (BSN.cosOddQ 536870912)

noncomputable def Ns564p137 := BSN.cos_dyadic_bound_f 538020888 536870912 4 3 536870912 268435456 Ns564p132 Ns564p133 Ns564p134 Ns564p135 Ns564p136 Ns564p134 289104255 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 538020888) qz373 0 3 Ns564p132 Ns564p133 Ns564p134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 538020888) qz374 0 3 Ns564p135 Ns564p136 Ns564p134 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p138 := nat_lit 66471920220096929802587710395082825578194852045270720829540411536462194159126311575909946814660540226576962890625 

noncomputable def Ns564p139 := nat_lit 111218438047021254130420379439986705381127239292076907141777841796184276583665430960252714216709136962890625 

noncomputable def Ns564p140 := nat_lit 402339268313959238314438316018978598760564067834452549700189670328413290320184487461727887140490766048272962890625 

noncomputable def Ns564p141 := BSN.cos_dyadic_bound_f 832750175 536870912 4 3 536870912 268435456 Ns564p138 Ns564p133 Ns564p139 Ns564p140 Ns564p136 Ns564p139 10563999 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 832750175) qz373 0 3 Ns564p138 Ns564p133 Ns564p139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 832750175) qz374 0 3 Ns564p140 Ns564p136 Ns564p139 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p142 := nat_lit 744366322294297238931141626910225897813355568642760908969815457136640000 

noncomputable def Ns564p143 := nat_lit 2504505714323359787184324207303086996185458423821189873137376790332288532480 

noncomputable def Ns564p144 := nat_lit 8778910472593238150184194190739206219104572069052790970777600000000 

noncomputable def Ns564p145 := nat_lit 1949516630630013331957889677021901868891576510471500104687944938291200000 

noncomputable def Ns564p146 := nat_lit 45915938095928262765045943800556594930066737770055147674185241156091956428800 

noncomputable abbrev qz375 := (BSN.sinEvenQ 536870912)

noncomputable abbrev qz376 := (BSN.sinOddQ 536870912)

noncomputable def Ns564p147 := BSN.sin_dyadic_bound_f 233308240 536870912 3 2 536870912 268435456 Ns564p142 Ns564p143 Ns564p144 Ns564p145 Ns564p146 Ns564p144 226033835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 233308240) qz375 0 2 Ns564p142 Ns564p143 Ns564p144 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 233308240) qz376 0 2 Ns564p145 Ns564p146 Ns564p144 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p148 := nat_lit 65740263462286777246037508806710968817472486375521113292973454097015806231205822243338447971084746668787016667136 

noncomputable def Ns564p149 := nat_lit 107598338073403970454450407628437576772814459596705503138956020937806602950456673085694287484304142615187456 

noncomputable def Ns564p150 := nat_lit 397920711306734409101740455191944561138263526179868064326537608412416592194761278456286211456292278186257666805760 

noncomputable def Ns564p151 := BSN.cos_dyadic_bound_f 830456962 536870912 4 3 536870912 268435456 Ns564p148 Ns564p133 Ns564p149 Ns564p150 Ns564p136 Ns564p149 12856665 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 830456962) qz373 0 3 Ns564p148 Ns564p133 Ns564p149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 830456962) qz374 0 3 Ns564p150 Ns564p136 Ns564p149 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p152 := Ns564p96 127998 BSN.abs_quadSignPos (BSN.cos_quad_nat3 383 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 226033835 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 246 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12856665 536870912) qz11 rfl rfl (Ns564p131 RS565to576.d9 RS565to576.d11 RS565to576.d13 RS565to576.d17 (Ns564p137 rfl rfl) (Ns564p141 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns564p130 rfl) RS565to576.d19 RS565to576.d21 RS565to576.d23 RS565to576.d25 RS565to576.d17 (Ns564p147 rfl rfl) (Ns564p151 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns564p153 := nat_lit 19537288185800180518778899285518957411896739870669289950977919553462230625 

noncomputable def Ns564p154 := nat_lit 6044177973709153994560431731149625686540154845296417401215295250390625 

noncomputable def Ns564p155 := nat_lit 51159302293709705585572590763080170018141825124860517576768774066757590625 

noncomputable def Ns564p156 := BSN.sin_dyadic_bound_f 528040405 536870912 3 2 536870912 268435456 Ns564p153 Ns564p143 Ns564p154 Ns564p155 Ns564p146 Ns564p154 446929258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 528040405) qz375 0 2 Ns564p153 Ns564p143 Ns564p154 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 528040405) qz376 0 2 Ns564p155 Ns564p146 Ns564p154 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p157 := nat_lit 6404297875834086491535033557532438444042341077622101874154280855085085505 

noncomputable def Ns564p158 := nat_lit 649729154582976100946151495190896157433469990836536330094212385436481 

noncomputable def Ns564p159 := nat_lit 16772109160934235040333079833973696378713143870929864802060106848027374401 

noncomputable def Ns564p160 := BSN.sin_dyadic_bound_f 399568777 536870912 3 2 536870912 268435456 Ns564p157 Ns564p143 Ns564p158 Ns564p159 Ns564p146 Ns564p158 363689169 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 399568777) qz375 0 2 Ns564p157 Ns564p143 Ns564p158 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 399568777) qz376 0 2 Ns564p159 Ns564p146 Ns564p158 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p161 := Ns564p94 172260 BSN.abs_quadSignPos (BSN.cos_quad_nat3 135 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 446929258 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 363689169 536870912) qz11 rfl rfl (Ns564p152 rfl rfl) (Ns564p130 rfl) RS565to576.d27 RS565to576.d29 RS565to576.d31 RS565to576.d33 RS565to576.d17 (Ns564p156 rfl rfl) (Ns564p160 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p162 := nat_lit 26012383074935998225170472960000 

noncomputable def Ns564p163 := nat_lit 1993841993677373809355710590420516864 

noncomputable def Ns564p164 := nat_lit 29907629905160607140335658856307752960 

noncomputable def Ns564p165 := BSN.cos_dyadic_bound_f 71415920 536870912 2 1 536870912 268435456 Ns564p162 Ns564p163 Ns564p162 Ns564p162 Ns564p164 Ns564p162 532127949 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 71415920) qz373 0 1 Ns564p162 Ns564p163 Ns564p162 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 71415920) qz374 0 1 Ns564p162 Ns564p164 Ns564p162 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p166 := nat_lit 177606417808302758173071913216 

noncomputable def Ns564p167 := BSN.cos_dyadic_bound_f 20528852 536870912 2 1 536870912 268435456 Ns564p166 Ns564p163 Ns564p166 Ns564p166 Ns564p164 Ns564p166 536478469 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20528852) qz373 0 1 Ns564p166 Ns564p163 Ns564p166 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20528852) qz374 0 1 Ns564p166 Ns564p164 Ns564p166 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p168 := Ns564p92 210932 BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 532127949 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536478469 536870912) qz11 rfl rfl (Ns564p161 rfl) (Ns564p130 rfl) RS565to576.d35 RS565to576.d37 RS565to576.d39 RS565to576.d41 RS565to576.d17 (Ns564p165 rfl rfl) (Ns564p167 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p169 := nat_lit 1419855831019076287075634133935513266395906316544320470261560721272690625 

noncomputable def Ns564p170 := nat_lit 278278412702595531909369356367009666242828713757909985904152976703587614720 

noncomputable def Ns564p171 := nat_lit 103477907230208716599529217247346748196214927587234198268310187890625 

noncomputable def Ns564p172 := nat_lit 4259360537242768443793703343372045105691326519777786942388145543442290625 

noncomputable def Ns564p173 := nat_lit 12522528571616798935921621036515434980927292119105949365686883951661442662400 

noncomputable def Ns564p174 := BSN.cos_dyadic_bound_f 317582055 536870912 3 2 536870912 268435456 Ns564p169 Ns564p170 Ns564p171 Ns564p172 Ns564p173 Ns564p171 445646561 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 317582055) qz373 0 2 Ns564p169 Ns564p170 Ns564p171 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 317582055) qz374 0 2 Ns564p172 Ns564p173 Ns564p171 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p175 := nat_lit 8572760370841885055447432338550299696951504740600066118322093697969930496 

noncomputable def Ns564p176 := nat_lit 3769483134354420428962032906527360513714341666736839582794255001436416 

noncomputable def Ns564p177 := nat_lit 25710742146256946325484372949837844369827085538466724675800692583906918656 

noncomputable def Ns564p178 := BSN.cos_dyadic_bound_f 497777458 536870912 3 2 536870912 268435456 Ns564p175 Ns564p170 Ns564p176 Ns564p177 Ns564p173 Ns564p176 322170841 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 497777458) qz373 0 2 Ns564p175 Ns564p170 Ns564p176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 497777458) qz374 0 2 Ns564p177 Ns564p173 Ns564p176 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz599 := (BSN.cos_quad_nat2 234 rfl)

noncomputable def Ns564p179 := Ns564p90 245713 BSN.abs_quadSignPos (BSN.cos_quad_nat0 176 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 445646561 536870912) BSN.abs_quadSignNeg qz599 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 322170841 536870912) qz11 rfl rfl (Ns564p168 rfl) (Ns564p130 rfl) RS565to576.d43 RS565to576.d45 RS565to576.d47 RS565to576.d49 RS565to576.d17 (Ns564p174 rfl rfl) (Ns564p178 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p180 := nat_lit 52946999516729111599821937734518966337375692707827780580494758359944947503911117877051691483314082950838385504721 

noncomputable def Ns564p181 := nat_lit 3570415896635346974072005805030179415937144689025665314440334861177556999349704385084003346650664335197480996044800 

noncomputable def Ns564p182 := nat_lit 3225401334295346284251273721609044284238122656386305196148927046484528326847969597616814400257675341459921 

noncomputable def Ns564p183 := nat_lit 264638792704477861113324791647439410027297534250615596702349780986560585652476678574562138682449199117781397795281 

noncomputable def Ns564p184 := nat_lit 124964556382237144092520203176056279557800064115898286005411720141214494977239653477940117132773251731911834861568000 

noncomputable def Ns564p185 := BSN.sin_dyadic_bound_f 619986139 536870912 4 3 536870912 268435456 Ns564p180 Ns564p181 Ns564p182 Ns564p183 Ns564p184 Ns564p182 491086499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 619986139) qz375 0 3 Ns564p180 Ns564p181 Ns564p182 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 619986139) qz376 0 3 Ns564p183 Ns564p184 Ns564p182 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz377 := (BSN.cos_quad_nat3 287 rfl)

noncomputable def Ns564p186 := Ns564p88 Bool.true 184384069 245713 Bool.true 619986139 28296951008113761 1 Bool.false 491086499 Bool.false Bool.true 42619604 261968 BSN.abs_quadSignPos qz377 (BSN.sfrac_eq_quadSignPos_mul Bool.false 491086499 536870912) qz11 rfl (Ns564p179 rfl) (Ns564p130 rfl) RS565to576.d51 RS565to576.d53 RS565to576.d17 (Ns564p185 rfl rfl) rfl 

noncomputable def Ns564p187 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) 42619604 536870912 261968 536870912 42619604 536870912 261968 536870912 45762451337117696 10654901 67108864 16373 16777216 (Ns564p186 rfl rfl rfl rfl) 

noncomputable def Ns564p188 := @Enclosure.Real.IsNear.mulLit_ff qz591 (Zeta.RiemannSiegel.correction qz10) 19090771 67108864 1 67108864 59015228458221 140737488355328 2303341723737 175921860444160000 1126646212008580178391 9444732965739290427392 

noncomputable abbrev qz600 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns564p189 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz600 1 1 0 1 19090771 67108864 1 67108864 19090771 67108864 1 67108864 

noncomputable abbrev qz21 := (@Enclosure.Real.IsNear.of_eq qz356 (@HMul.hMul Real Real Real qz355 qz354 qz353) Bool.false 10247209144991 67108864000 959413 67108864000 (BSN.t_div_two_pi_mk qz354 959413 1000 qz358) (@Enclosure.Real.IsNear.mulLit_ff qz354 qz353 959413 1000 0 1 10680707 67108864 1 67108864 10247209144991 67108864000 959413 67108864000 (Enclosure.Real.IsNear.const Bool.false 959413 1000) RS565to576.d56 rfl))

noncomputable def Ns564p190 := @Enclosure.Real.IsNear.sqrt_image qz8 10247209144991 67108864000 959413 67108864000 414631915 414631955 33554432 qz21 

noncomputable abbrev qz749 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 959413 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz601 := qz749

noncomputable abbrev qz378 := qz601

noncomputable abbrev qz22 := qz378

noncomputable def Ns564p191 := @Enclosure.Real.IsNear.sqrt_image qz22 414631935 33554432 5 8388608 117952271 117952278 33554432 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 829263870 67108864 40 67108864 414631935 33554432 5 8388608 (Ns564p190 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz602 := (Real.sqrt qz749)

noncomputable abbrev qz379 := qz602

noncomputable abbrev qz23 := qz379

noncomputable def Ns564p192 := @Enclosure.Real.IsNear.inv_image qz23 235904549 67108864 7 67108864 9545385 9545386 33554432 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 235904549 67108864 7 67108864 235904549 67108864 7 67108864 (Ns564p191 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns564p193 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 19090771 67108864 1 67108864 19090771 67108864 1 67108864 (Ns564p192 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz380 := (@HMul.hMul Real Real Real qz588 qz586 qz590)

noncomputable abbrev qz24 := (Real.cos qz380)

noncomputable abbrev qz603 := (@HMul.hMul Real Real Real qz741 qz744 qz744)

noncomputable abbrev qz604 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz381 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz603 qz590) qz604)

noncomputable abbrev qz25 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz381))

noncomputable def Ns564p194 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz24) qz25) Bool.false 59015228458221 

noncomputable def Ns564p195 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz24) qz25 13470023 8388608 167 

noncomputable abbrev qz26 := (@Neg.neg Real Real.instNeg (Real.cos qz380))

noncomputable def Ns564p196 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz24) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz26)) Bool.true 13470023 8388608 167 16777216 (BSN.inv_eq_neg_inv_neg qz24) 

noncomputable def Ns564p197 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz26) Bool.false 107760184 67108864 668 67108864 13470023 8388608 

noncomputable def Ns564p198 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true 41792798 67108864 661897216 171798691840000 20896399 33554432 40399 10485760000 

noncomputable abbrev qz27 := qz380

noncomputable abbrev qz605 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns564p199 := @Enclosure.Real.IsNear.cos_image qz27 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9408089) qz605) Bool.false 9408089 4194304 63 16777216 Bool.true 41792798 67108864 1 

noncomputable def Ns564p200 := nat_lit 134930377070944399171808483 

noncomputable def Ns564p201 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns564p202 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 11978751 33554432 5 8388608 10592566568293553459805 4722366482869645213696 Ns564p200 

noncomputable def Ns564p203 := @Enclosure.Real.IsNear.subLit_ff_p qz22 qz1 414631935 33554432 5 8388608 12 1 0 1 11978751 11978751 33554432 5 

noncomputable abbrev qz382 := (Enclosure.Real.IsNear.const Bool.false 12 1)

noncomputable def Ns564p204 := @Ns564p203 8388608 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 829263870 67108864 40 67108864 414631935 33554432 5 8388608 (Ns564p190 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns564p205 := @Enclosure.Real.IsNear.recentre' qz27 Bool.false 10592566568293553459805 4722366482869645213696 Ns564p200 Ns564p201 9408089 4194304 63 16777216 (@Ns564p202 Ns564p201 RS565to576.d55 (Ns564p204 rfl rfl) rfl) 

noncomputable def Ns564p206 := nat_lit 78642391403620755889092525668037481208890391285551712415776091850202771385083005080224725825 

noncomputable def Ns564p207 := nat_lit 46199975943266144436568348213124696692647303168343434164427665391357367878632476496239452487680 

noncomputable def Ns564p208 := nat_lit 5311442284064872075454300963516654650932836419709000799786964676247277751846014113610561 

noncomputable def Ns564p209 := nat_lit 205959568483880160392834450738538185725278085917479717944785347379150477082666786425357007681 

noncomputable def Ns564p210 := nat_lit 846999558959879314670419717240619439365200558086296293014507198841551744441595402431056628940800 

noncomputable def Ns564p211 := BSN.sin_dyadic_bound_f 92395657079 137438953472 3 2 67108864 20500001 Ns564p206 Ns564p207 Ns564p208 Ns564p209 Ns564p210 Ns564p208 41792798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 92395657079) qz371 0 2 Ns564p206 Ns564p207 Ns564p208 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 92395657079) qz372 0 2 Ns564p209 Ns564p210 Ns564p208 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p212 := @Ns564p199 10240000 (Ns564p205 rfl) (Enclosure.sfrac_false_div 9408089 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9408089) qz605) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 406360397260306186764288) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 41792798 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 9408089 4194304 226375608064910080 72057594037927936 0 406360397260306186764288 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 41792798 67108864 406360397260306186764288 604462909807314587353088 92395657079 137438953472 20500001 20480000 (Ns564p211 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p213 := @Enclosure.Real.IsNear.inv_image qz26 20896399 33554432 40399 10485760000 53879758 53880426 33554432 (@Enclosure.Real.IsNear.neg qz24 Bool.true 20896399 33554432 40399 10485760000 (Ns564p198 (Ns564p212 rfl rfl) rfl)) 

noncomputable def Ns564p214 := Ns564p196 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz26) Bool.false 13470023 8388608 167 16777216 (@Ns564p197 167 16777216 (Ns564p213 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p215 := @Enclosure.Real.IsNear.recentre' qz25 Bool.true 8762454 33554432 

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz355 qz352 qz381)

noncomputable abbrev qz383 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable def Ns564p216 := @Enclosure.Real.IsNear.cos_image qz28 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 61572411)) qz383) Bool.true 61572411 33554432 

noncomputable def Ns564p217 := nat_lit 290767490576824192687166597725 

noncomputable def Ns564p218 := nat_lit 158456325028528675187087900672 

noncomputable def Ns564p219 := nat_lit 155202192770669877704524779306803 

noncomputable def Ns564p220 := @Enclosure.Real.IsNear.recentre' qz28 Bool.true Ns564p217 Ns564p218 Ns564p219 

noncomputable def Ns564p221 := nat_lit 24178516392292583494123520000000000000 

noncomputable abbrev qz29 := qz381

noncomputable def Ns564p222 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz29 884279719003555 140737488355328 1 500000000000000 328818454532095 

noncomputable abbrev qz384 := (@HSub.hSub Real Real Real qz592 qz603 qz590)

noncomputable abbrev qz30 := qz384

noncomputable abbrev qz385 := qz604

noncomputable abbrev qz31 := qz385

noncomputable def Ns564p223 := @Enclosure.Real.IsNear.subLit_tf qz30 qz31 258449710354431 1125899906842624 143779885 140737488355328 1 16 

noncomputable abbrev qz386 := qz603

noncomputable abbrev qz32 := qz386

noncomputable def Ns564p224 := @Enclosure.Real.IsNear.subLit_ff_n qz32 qz10 143490475520001 1125899906842624 59893805 140737488355328 11978751 33554432 5 8388608 

noncomputable def Ns564p225 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 11978751 33554432 5 8388608 11978751 33554432 5 8388608 143490475520001 1125899906842624 

noncomputable def Ns564p226 := nat_lit 464080643768838313658033817186217429303247549994786927595398152902497873933834837454534972196325201 

noncomputable def Ns564p227 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600 

noncomputable def Ns564p228 := nat_lit 2969162151596886451816247010838699596437442869624001072487815483582299646860022709671945373521 

noncomputable def Ns564p229 := nat_lit 2802825109001463325655831188644949555124698331671294596039907512239860709925174247609473051129087825 

noncomputable def Ns564p230 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600 

noncomputable def Ns564p231 := BSN.cos_dyadic_bound_t 61572411 33554432 4 3 33554432 10240000 Ns564p226 Ns564p227 Ns564p228 Ns564p229 Ns564p230 Ns564p228 8762454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 61572411) (BSN.cosEvenQ 33554432) 0 3 Ns564p226 Ns564p227 Ns564p228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 61572411) (BSN.cosOddQ 33554432) 0 3 Ns564p229 Ns564p230 Ns564p228 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz387 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns564p232 := @Ns564p215 280674304 42949672960000 4381227 16777216 17131 2621440000 (@Ns564p216 27 4194304 Bool.true 8762454 33554432 1 10240000 (@Ns564p220 Ns564p221 61572411 33554432 27 4194304 (@Ns564p222 1125899906842624 143779885 140737488355328 Ns564p217 Ns564p218 Ns564p219 Ns564p221 RS565to576.d55 (@Ns564p223 0 1 5261095272513520 328818454532095 1125899906842624 143779885 140737488355328 (@Ns564p224 8672133231507450888192 258449710354431 1125899906842624 143779885 140737488355328 (@Ns564p225 59893805 140737488355328 (Ns564p204 rfl rfl) (Ns564p204 rfl rfl) rfl) (Ns564p204 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 61572411 33554432) (BSN.cos_neg_of_bound 61572411 33554432 Bool.true 8762454 33554432 1 10240000 (Ns564p231 rfl rfl)) rfl rfl) 

noncomputable abbrev qz33 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 12) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 12 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns564p233 := @Ns564p188 22023170360761415607 Ns564p85 (Ns564p189 qz33 (@Enclosure.Real.IsNear.of_eq qz600 (@Inv.inv Real Real.instInv qz23) Bool.false 19090771 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 959413 1000 qz11)) Ns564p193) rfl) (@Ns564p194 140737488355328 2303341723737 175921860444160000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 959413 1000 12 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 959413 1000 12 qz11 rfl rfl rfl))) (@Ns564p195 16777216 4381227 16777216 17131 2621440000 59015228458221 140737488355328 2303341723737 175921860444160000 Ns564p214 (Ns564p232 rfl) rfl)) 

noncomputable abbrev qz34 := qz359

noncomputable def Ns564p234 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 2626190217423252840919 9444732965739290427392 5782760412465224775607 Ns564p85 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HMul.hMul Real Real Real qz5 qz591 (Zeta.RiemannSiegel.correction qz10))) Bool.true 2626190217423252840919 9444732965739290427392 5782760412465224775607 Ns564p85 (BSN.hardyZApproximantRS₀_eq qz4 12 (@BSN.floor_sqrt_eq_dec qz4 959413 1000 12 qz11 rfl rfl rfl)) (@Ns564p87 2626190217423252840919 9444732965739290427392 5782760412465224775607 Ns564p85 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12)) Bool.true 10654901 67108864 16373 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (Ns564p187 (Ns564p186 rfl rfl rfl rfl) rfl rfl)) (Ns564p233 rfl) rfl rfl)) 

theorem RS565to576.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 2626190217423252840919 9444732965739290427392 5782760412465224775607 Ns564p85 := Ns564p234 

theorem RS565to576.d58 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS565to576.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS565to576.d3 a b h)) 

noncomputable def Ns564p235 := nat_lit 47223664828696452136960000 

noncomputable def Ns564p236 := nat_lit 165696793982068032674917836128256 

noncomputable abbrev qz750 := (Enclosure.sfrac Bool.false 960663 1000)

noncomputable abbrev qz606 := qz750

noncomputable abbrev qz388 := qz606

noncomputable abbrev qz35 := qz388

noncomputable abbrev qz751 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 960663 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz607 := qz751

noncomputable abbrev qz389 := qz607

noncomputable abbrev qz36 := qz389

noncomputable abbrev qz752 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 960663 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz608 := qz752

noncomputable abbrev qz390 := qz608

noncomputable abbrev qz37 := qz390

noncomputable abbrev qz609 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz36 qz9))

noncomputable def Ns564p237 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HMul.hMul Real Real Real qz5 qz609 (Zeta.RiemannSiegel.correction qz37)) 2224677153 268435456 262321 268435456 8922290721762987491067 75557863725914323419136 162670845253379109591 Ns564p235 Ns564p236 

noncomputable def Ns564p238 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin BSN.quadSignPos 11 12 960663 1000 287 536870912 268435456 9007199254740992 Bool.false 1038964160924 4470 1334074092 54 154981288 8 

noncomputable def Ns564p239 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 960663 1000 176 234 536870912 268435456 9007199254740992 Bool.false 1038964160924 4470 

noncomputable def Ns564p240 := Ns564p239 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.false 2039451858 211219 Bool.true 175336690 Bool.true 419493673 28296951008113761 1 Bool.false 508492890 Bool.false Bool.false 381151981 Bool.true Bool.false 2085329793 

noncomputable def Ns564p241 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 960663 1000 39 111 536870912 268435456 9007199254740992 Bool.false 1038964160924 4470 

noncomputable def Ns564p242 := Ns564p241 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.false 1697850981 172496 Bool.true 622736312 Bool.true 650892084 28296951008113761 1 Bool.false 492191364 Bool.false Bool.false 502754849 Bool.false Bool.false 2039451858 

noncomputable def Ns564p243 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 960663 1000 136 41 536870912 268435456 9007199254740992 Bool.false 1038964160924 4470 

noncomputable def Ns564p244 := Ns564p243 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.false 1691103425 128176 Bool.false 169780193 Bool.false 781174661 28296951008113761 1 Bool.false 510248233 Bool.false Bool.false 533278712 Bool.true Bool.false 1697850981 

noncomputable def Ns564p245 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 960663 1000 384 247 536870912 268435456 9007199254740992 Bool.false 1038964160924 4470 

noncomputable def Ns564p246 := Ns564p245 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 1217908868 75694 Bool.false 147151063 Bool.false 594550685 28296951008113761 1 Bool.false 516830513 Bool.false Bool.false 480261124 Bool.false Bool.false 1691103425 

noncomputable def Ns564p247 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 960663 1000 808 560 536870912 268435456 9007199254740992 Bool.false 1038964160924 4470 

noncomputable def Ns564p248 := Ns564p247 372130544 53 379625064 8 589812976 53 309962568 8 Bool.false 536870848 4533 Bool.false 73712054 Bool.false 96338302 28296951008113761 1 Bool.false 531818545 Bool.false Bool.false 528250412 Bool.false Bool.false 1217908868 

noncomputable def Ns564p249 := nat_lit 5480336074995977902928027656941041329983852976584799878957 

noncomputable def Ns564p250 := nat_lit 2831890778629377496150633805088858740535964342629171200 

noncomputable def Ns564p251 := nat_lit 392732512633381873139345481380640000 

noncomputable def Ns564p252 := nat_lit 2263701848873757912748390474693114585920 

noncomputable abbrev qz610 := (@Eq.refl Real qz750)

noncomputable abbrev qz391 := qz610

noncomputable abbrev qz38 := qz391

noncomputable def Ns564p253 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz35 960663 1000 3691494598276 16000000 1921326 4000 2000 Ns564p251 Ns564p252 qz38 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns564p254 := nat_lit 15783367895988416360432719651990199030353496572564223651396160 

noncomputable abbrev qz611 := (@HSub.hSub Real Real Real qz745 qz746 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz747 (@Nat.cast Real Real.instNatCast 1921326))))

noncomputable abbrev qz392 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 960663 4000) (Real.log (Enclosure.sfrac Bool.false 3691494598276 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz611))

noncomputable abbrev qz612 := (Enclosure.sfrac Bool.false 960663 2000)

noncomputable abbrev qz39 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz392 qz612) (@HMul.hMul Real Real Real qz355 qz612 (Real.log Real.pi)))

noncomputable def Ns564p255 := @Enclosure.Real.IsNear.addLit_ft_p qz39 (Enclosure.sfrac Bool.true Ns564p251 Ns564p252) 6972371082706405069773 3602879701896396800 136384541357824641 16384000000000000000000 Ns564p251 Ns564p252 0 1 Ns564p254 

noncomputable def Ns564p256 := nat_lit 2339539513734384448781533839360000 

noncomputable abbrev qz40 := (@HSub.hSub Real Real Real qz359 qz392 qz612)

noncomputable def Ns564p257 := @Enclosure.Real.IsNear.subLit_ff_p qz40 (@HMul.hMul Real Real Real qz5 qz612 (Real.log Real.pi)) 44767069219226059465473 18014398509481984000 47298063373959 16000000000000000000 36899796894543 67108864000 2881989 536870912000 Ns564p256 6972371082706405069773 3602879701896396800 

noncomputable def Ns564p258 := nat_lit 89534138438452118930946000 

noncomputable abbrev qz41 := qz392

noncomputable def Ns564p259 := @Enclosure.Real.IsNear.subLit_ff_p qz41 qz612 53419952276883305063169 18014398509481984000 47298063373959 16000000000000000000 960663 2000 0 1 Ns564p258 44767069219226059465473 18014398509481984000 47298063373959 16000000000000000000 

noncomputable def Ns564p260 := nat_lit 120291038584160666021895638415323430912 

noncomputable def Ns564p261 := nat_lit 119431747415885198313652224 

noncomputable def Ns564p262 := nat_lit 96147415294677785686375274506375880650099649637408371360251589780064888605083714530082626936776290642923528816113628131484245845765474352723313456209461177282554093767090589082740326400 

noncomputable def Ns564p263 := nat_lit 2548259569376733235173551362044894719493505084141820742494395480042357668621831585405914348248044827749217258988181672468398644906305853855076674863467833189029320359030677672128675840 

noncomputable def Ns564p264 := nat_lit 92663978940178959895043856536028396800800925865913885380985339574914240239705517275002267313601939143693050770325853919951971435914388663045534341027479592067126993018956021760 

noncomputable def Ns564p265 := BSN.log_dyadic_bound 1594342598276 5788646598276 8 7 Ns564p262 268435456 81920000 Ns564p263 Ns564p264 151787145 7382989196552 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1594342598276) (BSN.artanhQ 5788646598276) 0 7 Ns564p263 Ns564p262 Ns564p264 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz393 := (Real.log (Enclosure.sfrac Bool.false 3691494598276 16000000))

noncomputable def Ns564p266 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 960663 4000) qz393 960663 4000 0 1 55614741247093863 4503599627370496 48828193 4000000000000000 53427024170656931711169 18014398509481984000 46907438371959 16000000000000000000 (Enclosure.Real.IsNear.const Bool.false 960663 4000) (BSN.isNear_log_sfrac 3691494598276 16000000 55614741247093863 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3691494598276) qz362)) Bool.false Ns564p261 Ns564p112 1000001392640000 81920000000000000000000 55614741247093863 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3691494598276 16000000 17 7382989196552 4194304000000 151787145 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns564p265 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p267 := BSN.arctan_dyadic_bound_f 1000 1921326 1 0 33554432 10240000 0 1 1 0 1 1 17464 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1921326) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1921326) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns564p268 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1921326))) 884279719003555 562949953421312 1 2000000000000000 17464 33554432 1 10240000 29661672342297344212992 883986721703331 562949953421312 195312501 2000000000000000 qz17 (Ns564p267 rfl) rfl rfl 

noncomputable abbrev qz394 := (@HMul.hMul Real Real Real qz588 qz593 qz611)

noncomputable abbrev qz42 := qz394

noncomputable abbrev qz395 := qz611

noncomputable abbrev qz43 := qz395

noncomputable def Ns564p269 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 960663 4000) qz393) qz42 53427024170656931711169 18014398509481984000 46907438371959 16000000000000000000 883986721703331 2251799813685248 195312501 8000000000000000 Ns564p260 53419952276883305063169 18014398509481984000 47298063373959 16000000000000000000 (Ns564p266 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz43 1 4 0 1 883986721703331 562949953421312 195312501 2000000000000000 883986721703331 2251799813685248 195312501 8000000000000000 qz369 Ns564p268 rfl) 

noncomputable def Ns564p270 := @Ns564p255 Ns564p249 Ns564p250 136384541357824641 16384000000000000000000 (@Ns564p257 136384541357824641 16384000000000000000000 (Ns564p259 (Ns564p269 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 960663 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz612 (Real.log Real.pi) 960663 2000 0 1 38410761 33554432 3 268435456 36899796894543 67108864000 2881989 536870912000 (Enclosure.Real.IsNear.const Bool.false 960663 2000) RS565to576.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns564p251 Ns564p252) 

noncomputable def Ns564p271 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns564p249 Ns564p250 136384541357824641 16384000000000000000000 129870520115 67108864 35 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz370 qz39 (Enclosure.sfrac Bool.true Ns564p251 Ns564p252)) Bool.false Ns564p249 Ns564p250 136384541357824641 16384000000000000000000 Ns564p253 (Ns564p270 rfl rfl)) 

noncomputable def Ns564p272 := BSN.cos_dyadic_bound_f 65963981 137438953472 1 0 67108864 20500001 0 1 1 0 1 1 67108856 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 65963981) (BSN.cosEvenQ 137438953472) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 65963981) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl 

noncomputable abbrev qz396 := (@Nat.cast Real Real.instNatCast 67108864)

noncomputable abbrev qz397 := (@Nat.cast Real Real.instNatCast Ns564p112)

noncomputable def Ns564p273 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz35) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 129870520115) qz396) Bool.false 129870520115 67108864 35 4194304 Bool.false 67108856 67108864 1 10240000 (Ns564p271 rfl) (Enclosure.sfrac_false_div 129870520115 67108864) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 129870520115) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4641802572373887549440) qz397) 226375608064910080 72057594037927936 Bool.false 67108856 67108864 308 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q0 129870520115 67108864 226375608064910080 72057594037927936 308 4641802572373887549440 Ns564p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108856 67108864 4641802572373887549440 Ns564p112 65963981 137438953472 20500001 20480000 (Ns564p272 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p274 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns564p249 Ns564p250 136384541357824641 16384000000000000000000 1038964160924 536870912 4470 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz370 qz39 (Enclosure.sfrac Bool.true Ns564p251 Ns564p252)) Bool.false Ns564p249 Ns564p250 136384541357824641 16384000000000000000000 Ns564p253 (Ns564p270 rfl rfl)) 

noncomputable def Ns564p275 := Ns564p248 75694 BSN.abs_quadSignPos (BSN.cos_quad_nat0 808 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 531818545 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 560 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 528250412 536870912) qz38 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) Bool.false 8388607 8388608 22131 2621440000 536870848 536870912 4533 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 8388607 8388608 22131 2621440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz35) qz35) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 67108856 67108864 362594304 42949672960000 8388607 8388608 22131 2621440000 (Ns564p273 rfl rfl) rfl)) rfl) (Ns564p274 rfl) RS565to576.d7 

noncomputable def Ns564p276 := nat_lit 29522562606631805887760177975056 

noncomputable def Ns564p277 := BSN.cos_dyadic_bound_f 73712054 536870912 2 1 536870912 268435456 Ns564p276 Ns564p163 Ns564p276 Ns564p276 Ns564p164 Ns564p276 531818545 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 73712054) qz373 0 1 Ns564p276 Ns564p163 Ns564p276 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 73712054) qz374 0 1 Ns564p276 Ns564p164 Ns564p276 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p278 := nat_lit 86138231243981324557931404185616 

noncomputable def Ns564p279 := BSN.cos_dyadic_bound_f 96338302 536870912 2 1 536870912 268435456 Ns564p278 Ns564p163 Ns564p278 Ns564p278 Ns564p164 Ns564p278 528250412 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 96338302) qz373 0 1 Ns564p278 Ns564p163 Ns564p278 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 96338302) qz374 0 1 Ns564p278 Ns564p164 Ns564p278 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p280 := nat_lit 468871262111472520571529694140961 

noncomputable def Ns564p281 := BSN.cos_dyadic_bound_f 147151063 536870912 2 1 536870912 268435456 Ns564p280 Ns564p163 Ns564p280 Ns564p280 Ns564p164 Ns564p280 516830513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 147151063) qz373 0 1 Ns564p280 Ns564p163 Ns564p280 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 147151063) qz374 0 1 Ns564p280 Ns564p164 Ns564p280 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p282 := nat_lit 31407457280839120609197176644409281011287465183178159222477498300472830625 

noncomputable def Ns564p283 := nat_lit 15613888384426472152508041859781231018379954535816334015356218875390625 

noncomputable def Ns564p284 := nat_lit 82232346582908625402507592477108471131723126981932428660940014051630590625 

noncomputable def Ns564p285 := BSN.sin_dyadic_bound_f 594550685 536870912 3 2 536870912 268435456 Ns564p282 Ns564p143 Ns564p283 Ns564p284 Ns564p146 Ns564p283 480261124 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 594550685) qz375 0 2 Ns564p282 Ns564p143 Ns564p283 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 594550685) qz376 0 2 Ns564p284 Ns564p146 Ns564p283 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p286 := Ns564p246 128176 BSN.abs_quadSignPos (BSN.cos_quad_nat0 384 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 516830513 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 247 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 480261124 536870912) qz38 rfl rfl (Ns564p275 RS565to576.d9 RS565to576.d11 RS565to576.d13 RS565to576.d17 (Ns564p277 rfl rfl) (Ns564p279 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns564p274 rfl) RS565to576.d19 RS565to576.d21 RS565to576.d23 RS565to576.d25 RS565to576.d17 (Ns564p281 rfl rfl) (Ns564p285 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns564p287 := nat_lit 115968344105341521515195134409712744806929249428235575614773783932276481 

noncomputable def Ns564p288 := nat_lit 690392688644241415774478583916753454947086937180335568706338656001 

noncomputable def Ns564p289 := nat_lit 347903651530647276062753854271970400913877854110832366173183939119517441 

noncomputable def Ns564p290 := BSN.cos_dyadic_bound_f 169780193 536870912 3 2 536870912 268435456 Ns564p287 Ns564p170 Ns564p288 Ns564p289 Ns564p173 Ns564p288 510248233 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 169780193) qz373 0 2 Ns564p287 Ns564p170 Ns564p288 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 169780193) qz374 0 2 Ns564p289 Ns564p173 Ns564p288 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p291 := nat_lit 133565438319357272518458538641412035009286779594996467035457419795607957922602059278667515030674642753158134922321 

noncomputable def Ns564p292 := nat_lit 51638993803617605805521261427563249839948123732988001483206612730695903569104390853704426395825085837245521 

noncomputable def Ns564p293 := nat_lit 667215947077686405688069376824343828707852458591501963522971415792816999228446122961526926392346115332536611404881 

noncomputable def Ns564p294 := BSN.sin_dyadic_bound_f 781174661 536870912 4 3 536870912 268435456 Ns564p291 Ns564p181 Ns564p292 Ns564p293 Ns564p184 Ns564p292 533278712 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 781174661) qz375 0 3 Ns564p291 Ns564p181 Ns564p292 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 781174661) qz376 0 3 Ns564p293 Ns564p184 Ns564p292 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p295 := Ns564p244 172496 BSN.abs_quadSignPos (BSN.cos_quad_nat0 136 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 510248233 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 533278712 536870912) qz38 rfl rfl (Ns564p286 rfl rfl) (Ns564p274 rfl) RS565to576.d27 RS565to576.d29 RS565to576.d31 RS565to576.d33 RS565to576.d17 (Ns564p290 rfl rfl) (Ns564p294 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p296 := nat_lit 53893297284301475332710659056712818029600760224214544893583601614944279143999623840774419630436613055974322733056 

noncomputable def Ns564p297 := nat_lit 3401341861374066913367020033452190487188606692217660529213411265787599303888508741960610947453520032301056 

noncomputable def Ns564p298 := nat_lit 269366813813821101482994127297823716611484843022344277051448681364932399615411510184787572315239681104790805282816 

noncomputable def Ns564p299 := BSN.sin_dyadic_bound_f 622736312 536870912 4 3 536870912 268435456 Ns564p296 Ns564p181 Ns564p297 Ns564p298 Ns564p184 Ns564p297 492191364 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 622736312) qz375 0 3 Ns564p296 Ns564p181 Ns564p297 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 622736312) qz376 0 3 Ns564p298 Ns564p184 Ns564p297 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p300 := nat_lit 64328620092710704351173748441908726542935255124632465811732916513927165686912448764738040105198152428827187347456 

noncomputable def Ns564p301 := nat_lit 5782396625189693817040677342706973990808098658178921477549494389689432920227515038633710627576109865107456 

noncomputable def Ns564p302 := nat_lit 321501120949152635881797494886607419256588626846141777903789636200618895467252496259699135234266815498811359625216 

noncomputable def Ns564p303 := BSN.sin_dyadic_bound_f 650892084 536870912 4 3 536870912 268435456 Ns564p300 Ns564p181 Ns564p301 Ns564p302 Ns564p184 Ns564p301 502754849 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 650892084) qz375 0 3 Ns564p300 Ns564p181 Ns564p301 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 650892084) qz376 0 3 Ns564p302 Ns564p184 Ns564p301 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p304 := Ns564p242 211219 BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 492191364 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 111 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 502754849 536870912) qz38 rfl rfl (Ns564p295 rfl) (Ns564p274 rfl) RS565to576.d35 RS565to576.d37 RS565to576.d39 RS565to576.d41 RS565to576.d17 (Ns564p299 rfl rfl) (Ns564p303 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p305 := nat_lit 131911583721098741363521080973800942272672960543414331478214698160800000 

noncomputable def Ns564p306 := nat_lit 893269343690142115787821132682528652935015322071151563184100000000 

noncomputable def Ns564p307 := nat_lit 395732964624608843806331667279137461760713011599598852131517726282400000 

noncomputable def Ns564p308 := BSN.cos_dyadic_bound_f 175336690 536870912 3 2 536870912 268435456 Ns564p305 Ns564p170 Ns564p306 Ns564p307 Ns564p173 Ns564p306 508492890 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 175336690) qz373 0 2 Ns564p305 Ns564p170 Ns564p306 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 175336690) qz374 0 2 Ns564p307 Ns564p173 Ns564p306 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p309 := nat_lit 4323015454128770156937362175017132448352386987754900971883702035295287361 

noncomputable def Ns564p310 := nat_lit 958966243454464905566292563257053055621625791075391224112958622447681 

noncomputable def Ns564p311 := nat_lit 12967128429899401541000953939924883238945917711682552133202880188640966721 

noncomputable def Ns564p312 := BSN.cos_dyadic_bound_f 419493673 536870912 3 2 536870912 268435456 Ns564p309 Ns564p170 Ns564p310 Ns564p311 Ns564p173 Ns564p310 381151981 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 419493673) qz373 0 2 Ns564p309 Ns564p170 Ns564p310 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 419493673) qz374 0 2 Ns564p311 Ns564p173 Ns564p310 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p313 := Ns564p240 246045 BSN.abs_quadSignPos (BSN.cos_quad_nat0 176 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 508492890 536870912) BSN.abs_quadSignNeg qz599 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 381151981 536870912) qz38 rfl rfl (Ns564p304 rfl) (Ns564p274 rfl) RS565to576.d43 RS565to576.d45 RS565to576.d47 RS565to576.d49 RS565to576.d17 (Ns564p308 rfl rfl) (Ns564p312 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p314 := nat_lit 32596018518431297691530330586052884024442187761610313728565052625740898560 

noncomputable def Ns564p315 := nat_lit 16817378325506746742001035203906994255435118738163658010037823831286016 

noncomputable def Ns564p316 := nat_lit 85343296554793054459282864144570275406649311088165223366606505162165985536 

noncomputable def Ns564p317 := BSN.sin_dyadic_bound_f 600094694 536870912 3 2 536870912 268435456 Ns564p314 Ns564p143 Ns564p315 Ns564p316 Ns564p146 Ns564p315 482713400 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 600094694) qz375 0 2 Ns564p314 Ns564p143 Ns564p315 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 600094694) qz376 0 2 Ns564p316 Ns564p146 Ns564p315 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p318 := Ns564p238 Bool.false 2085329793 246045 Bool.true 600094694 28296951008113761 1 Bool.false 482713400 Bool.false Bool.false 2224677153 262321 BSN.abs_quadSignPos qz377 (BSN.sfrac_eq_quadSignPos_mul Bool.false 482713400 536870912) qz38 rfl (Ns564p313 rfl) (Ns564p274 rfl) RS565to576.d51 RS565to576.d53 RS565to576.d17 (Ns564p317 rfl rfl) rfl 

noncomputable def Ns564p319 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) 2224677153 536870912 262321 536870912 2224677153 536870912 262321 536870912 2388728904073347072 2224677153 268435456 262321 268435456 (Ns564p318 rfl rfl rfl rfl) 

noncomputable def Ns564p320 := @Enclosure.Real.IsNear.mulLit_ff qz609 (Zeta.RiemannSiegel.correction qz37) 19084557 67108864 1 67108864 467513640571431 1125899906842624 531773676747 43980465111040000 8922290721762987491067 75557863725914323419136 

noncomputable abbrev qz613 := (@HPow.hPow Real Real Real qz7 qz36 qz9)

noncomputable def Ns564p321 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz613 1 1 0 1 19084557 67108864 1 67108864 19084557 67108864 1 67108864 

noncomputable def Ns564p322 := @Enclosure.Real.IsNear.sqrt_image qz36 10260560028741 67108864000 960663 67108864000 414901935 414901974 33554432 (@Enclosure.Real.IsNear.of_eq qz36 (@HMul.hMul Real Real Real qz5 qz35 qz3) Bool.false 10260560028741 67108864000 960663 67108864000 (BSN.t_div_two_pi_mk qz35 960663 1000 qz38) (@Enclosure.Real.IsNear.mulLit_ff qz35 qz3 960663 1000 0 1 10680707 67108864 1 67108864 10260560028741 67108864000 960663 67108864000 (Enclosure.Real.IsNear.const Bool.false 960663 1000) RS565to576.d56 rfl)) 

noncomputable abbrev qz753 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 960663 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz614 := qz753

noncomputable abbrev qz398 := qz614

noncomputable abbrev qz44 := qz398

noncomputable def Ns564p323 := @Enclosure.Real.IsNear.sqrt_image qz44 829803909 67108864 39 67108864 117990672 117990678 33554432 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 829803909 67108864 39 67108864 829803909 67108864 39 67108864 (Ns564p322 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns564p324 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz44) 117990675 33554432 3 33554432 9542278 9542279 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz44) Bool.false 235981350 67108864 6 67108864 117990675 33554432 3 33554432 (Ns564p323 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns564p325 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 19084557 67108864 1 67108864 19084557 67108864 1 67108864 (Ns564p324 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz588 qz586 qz608)

noncomputable abbrev qz45 := (Real.cos qz399)

noncomputable abbrev qz615 := (@HMul.hMul Real Real Real qz741 qz752 qz752)

noncomputable abbrev qz400 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz615 qz608) qz604)

noncomputable abbrev qz46 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz400))

noncomputable def Ns564p326 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz37) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz45) qz46) Bool.false 467513640571431 

noncomputable def Ns564p327 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz45) qz46 101448169 67108864 579 

noncomputable abbrev qz47 := (@Neg.neg Real Real.instNeg (Real.cos qz399))

noncomputable def Ns564p328 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz45) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz47)) Bool.true 101448169 67108864 579 67108864 (BSN.inv_eq_neg_inv_neg qz45) 

noncomputable def Ns564p329 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz47) Bool.false 101448169 67108864 579 67108864 101448169 67108864 

noncomputable def Ns564p330 := @Enclosure.Real.IsNear.recentre' qz45 Bool.true 44393109 67108864 1293074432 343597383680000 44393109 67108864 78923 20971520000 

noncomputable abbrev qz48 := qz399

noncomputable def Ns564p331 := @Enclosure.Real.IsNear.cos_image qz48 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 153922589) qz396) Bool.false 153922589 67108864 123 33554432 Bool.true 44393109 67108864 1 

noncomputable def Ns564p332 := nat_lit 210491388232630009521285597 

noncomputable def Ns564p333 := nat_lit 57646075230342348800000000000000 

noncomputable def Ns564p334 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz37 884279719003555 140737488355328 1 500000000000000 24497541 67108864 39 67108864 21662678671758067758255 9444732965739290427392 Ns564p332 

noncomputable def Ns564p335 := @Enclosure.Real.IsNear.subLit_ff_p qz44 qz1 829803909 67108864 39 67108864 12 1 0 1 24497541 24497541 67108864 39 

noncomputable def Ns564p336 := @Ns564p335 67108864 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 829803909 67108864 39 67108864 829803909 67108864 39 67108864 (Ns564p322 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns564p337 := @Enclosure.Real.IsNear.recentre' qz48 Bool.false 21662678671758067758255 9444732965739290427392 Ns564p332 Ns564p333 153922589 67108864 123 33554432 (@Ns564p334 Ns564p333 RS565to576.d55 (Ns564p336 rfl rfl) rfl) 

noncomputable def Ns564p338 := nat_lit 6990772968312310478143488 

noncomputable def Ns564p339 := nat_lit 105109492562499029165952000933449906789217018341063921746030877581571594232176450375857191745 

noncomputable def Ns564p340 := nat_lit 9487748886463685027872895679167849166680176073625707116218437912934976937762017909128001 

noncomputable def Ns564p341 := nat_lit 275271405117871754230305351089840626977869946798667258189987944766542756835896231526820723521 

noncomputable def Ns564p342 := BSN.sin_dyadic_bound_f 99344858999 137438953472 3 2 67108864 20500001 Ns564p339 Ns564p207 Ns564p340 Ns564p341 Ns564p210 Ns564p340 44393109 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 99344858999) qz371 0 2 Ns564p339 Ns564p207 Ns564p340 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 99344858999) qz372 0 2 Ns564p341 Ns564p210 Ns564p340 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p343 := @Ns564p331 10240000 (Ns564p337 rfl) (Enclosure.sfrac_false_div 153922589 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 153922589) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p338) qz397) 226375608064910080 72057594037927936 Bool.false 44393109 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 153922589 67108864 226375608064910080 72057594037927936 0 Ns564p338 Ns564p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 44393109 67108864 Ns564p338 Ns564p112 99344858999 137438953472 20500001 20480000 (Ns564p342 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p344 := @Enclosure.Real.IsNear.inv_image qz47 44393109 67108864 78923 20971520000 50723795 50724374 33554432 (@Enclosure.Real.IsNear.neg qz45 Bool.true 44393109 67108864 78923 20971520000 (Ns564p330 (Ns564p343 rfl rfl) rfl)) 

noncomputable def Ns564p345 := Ns564p328 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz47) Bool.false 101448169 67108864 579 67108864 (@Ns564p329 579 67108864 (Ns564p344 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p346 := @Enclosure.Real.IsNear.recentre' qz46 Bool.true 9216798 33554432 

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz355 qz352 qz400)

noncomputable def Ns564p347 := @Enclosure.Real.IsNear.cos_image qz49 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 62043999)) qz383) Bool.true 62043999 33554432 

noncomputable def Ns564p348 := nat_lit 1171978011239725078630760103445 

noncomputable def Ns564p349 := nat_lit 633825300114114700748351602688 

noncomputable def Ns564p350 := nat_lit 122194444896904879269477530834672513 

noncomputable def Ns564p351 := @Enclosure.Real.IsNear.recentre' qz49 Bool.true Ns564p348 Ns564p349 Ns564p350 

noncomputable def Ns564p352 := nat_lit 19342813113834066795298816000000000000000 

noncomputable abbrev qz50 := qz400

noncomputable def Ns564p353 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz50 884279719003555 140737488355328 1 500000000000000 1325347608967399 

noncomputable abbrev qz401 := (@HSub.hSub Real Real Real qz592 qz615 qz608)

noncomputable abbrev qz51 := qz401

noncomputable def Ns564p354 := @Enclosure.Real.IsNear.subLit_tf qz51 qz31 1043872632256743 4503599627370496 4528055415 4503599627370496 1 16 

noncomputable abbrev qz402 := qz615

noncomputable abbrev qz52 := qz402

noncomputable def Ns564p355 := @Enclosure.Real.IsNear.subLit_ff_n qz52 qz37 600129515046681 4503599627370496 1910809719 4503599627370496 24497541 67108864 39 67108864 

noncomputable def Ns564p356 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz37 24497541 67108864 39 67108864 24497541 67108864 39 67108864 600129515046681 4503599627370496 

noncomputable def Ns564p357 := nat_lit 478562135660675029645942102889698205432863161040610519126862135770243109822175325750811247233937281 

noncomputable def Ns564p358 := nat_lit 3253848933521129908912517293535018631900581251694772459443526793656023691028993723743031472001 

noncomputable def Ns564p359 := nat_lit 2889886106181347625518433525191981403991255046455555335418948372882842120778201808596975141667417985 

noncomputable def Ns564p360 := BSN.cos_dyadic_bound_t 62043999 33554432 4 3 33554432 10240000 Ns564p357 Ns564p227 Ns564p358 Ns564p359 Ns564p230 Ns564p358 9216798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 62043999) (BSN.cosEvenQ 33554432) 0 3 Ns564p357 Ns564p227 Ns564p358 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 62043999) (BSN.cosOddQ 33554432) 0 3 Ns564p359 Ns564p230 Ns564p358 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p361 := @Ns564p346 4419108864 687194767360000 4608399 16777216 269721 41943040000 (@Ns564p347 425 67108864 Bool.true 9216798 33554432 1 10240000 (@Ns564p351 Ns564p352 62043999 33554432 425 67108864 (@Ns564p353 4503599627370496 4528055415 4503599627370496 Ns564p348 Ns564p349 Ns564p350 Ns564p352 RS565to576.d55 (@Ns564p354 0 1 21205561743478384 1325347608967399 4503599627370496 4528055415 4503599627370496 (@Ns564p355 70053106511439779069952 1043872632256743 4503599627370496 4528055415 4503599627370496 (@Ns564p356 1910809719 4503599627370496 (Ns564p336 rfl rfl) (Ns564p336 rfl rfl) rfl) (Ns564p336 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 62043999 33554432) (BSN.cos_neg_of_bound 62043999 33554432 Bool.true 9216798 33554432 1 10240000 (Ns564p360 rfl rfl)) rfl rfl) 

noncomputable def Ns564p362 := @Ns564p320 162670845253379109591 Ns564p235 (Ns564p321 qz33 (@Enclosure.Real.IsNear.of_eq qz613 (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 19084557 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz36 (BSN.t_div_two_pi_nonneg qz35 960663 1000 qz38)) Ns564p325) rfl) (@Ns564p326 1125899906842624 531773676747 43980465111040000 (BSN.correction_mk qz37 (BSN.cos_two_pi_p_ne_zero_mk qz35 960663 1000 12 qz38 rfl rfl (@BSN.floor_sqrt_eq_dec qz35 960663 1000 12 qz38 rfl rfl rfl))) (@Ns564p327 67108864 4608399 16777216 269721 41943040000 467513640571431 1125899906842624 531773676747 43980465111040000 Ns564p345 (Ns564p361 rfl) rfl)) 

noncomputable def Ns564p363 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (hardyZApproximantRS₀ qz35) Bool.false 617268659107640507351301 75557863725914323419136 46310669198825874469591 Ns564p235 (@Eq.refl Real (hardyZApproximantRS₀ qz35)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HMul.hMul Real Real Real qz5 qz609 (Zeta.RiemannSiegel.correction qz37))) Bool.false 617268659107640507351301 75557863725914323419136 46310669198825874469591 Ns564p235 (BSN.hardyZApproximantRS₀_eq qz35 12 (@BSN.floor_sqrt_eq_dec qz35 960663 1000 12 qz38 rfl rfl rfl)) (@Ns564p237 617268659107640507351301 75557863725914323419136 46310669198825874469591 Ns564p235 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12)) Bool.false 2224677153 268435456 262321 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (Ns564p319 (Ns564p318 rfl rfl rfl rfl) rfl rfl)) (Ns564p362 rfl) rfl rfl)) 

theorem RS565to576.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz35) Bool.false 617268659107640507351301 75557863725914323419136 46310669198825874469591 Ns564p235 := Ns564p363 

noncomputable abbrev qz616 := (@HMul.hMul Real Real Real qz741 (Real.sqrt qz749) qz743)

noncomputable abbrev qz403 := qz616

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv qz403)

noncomputable abbrev qz404 := (@HMul.hMul Real Real Real qz588 (@HMul.hMul Real Real Real qz588 qz616 qz616) qz616)

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz355 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz404))

noncomputable abbrev qz405 := (@HMul.hMul Real Real Real qz588 qz602 qz602)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz355 qz405 qz379))

noncomputable abbrev qz617 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz53)

noncomputable def Ns564p364 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz370 (@HAdd.hAdd Real Real Real qz370 qz617 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55)) Bool.false 

noncomputable def Ns564p365 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz370 qz617 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55) 25005001 2147483648 

noncomputable def Ns564p366 := @Enclosure.Real.IsNear.addLit_ff qz617 qz54 3125625 268435456 25 268435456 

noncomputable def Ns564p367 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz53 25 4 0 1 125025 67108864 1 67108864 3125625 

noncomputable def Ns564p368 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 125025 67108864 1 67108864 125025 67108864 1 67108864 

noncomputable def Ns564p369 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz8 235904549 67108864 7 67108864 10247209144991 67108864000 959413 67108864000 2417363251857777464059 4503599627370496000 59612072360113 

noncomputable def Ns564p370 := @Enclosure.Real.IsNear.sqrt_image qz8 10247209144991 67108864000 959413 67108864000 414631915 414631955 33554432 qz21 

noncomputable def Ns564p371 := @Enclosure.Real.IsNear.sqrt_image qz22 414631935 33554432 5 8388608 117952271 117952278 33554432 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 829263870 67108864 40 67108864 414631935 33554432 5 8388608 (Ns564p370 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz406 := (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 235904549 67108864 7 67108864 235904549 67108864 7 67108864 (Ns564p371 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns564p372 := @Ns564p369 900719925474099200 qz406 

noncomputable def Ns564p373 := Ns564p372 qz21 

noncomputable abbrev qz56 := qz403

noncomputable def Ns564p374 := @Enclosure.Real.IsNear.inv_image qz56 2417363251857777464059 4503599627370496000 59612072360113 900719925474099200 62512 62513 33554432 (Ns564p373 rfl) rfl rfl 

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv qz404)

noncomputable def Ns564p375 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz57 1 32 0 1 1 

noncomputable def Ns564p376 := @Enclosure.Real.IsNear.recentre' qz57 Bool.false 1 67108864 1 67108864 

noncomputable def Ns564p377 := nat_lit 14126212900927786180765087355843052756025091399895114133448757379 

noncomputable def Ns564p378 := nat_lit 91343852333181432387730302044767688728495783936000000000 

noncomputable def Ns564p379 := nat_lit 1045055510966969655108531446636698540893597122817576801049 

noncomputable def Ns564p380 := nat_lit 18268770466636286477546060408953537745699156787200000000 

noncomputable abbrev qz58 := qz404

noncomputable def Ns564p381 := @Enclosure.Real.IsNear.inv_image qz58 Ns564p377 Ns564p378 Ns564p379 Ns564p380 0 1 

noncomputable def Ns564p382 := nat_lit 5843645091432408440040181969465489036755481 

noncomputable def Ns564p383 := nat_lit 20282409603651670423947251286016000000 

noncomputable def Ns564p384 := nat_lit 288208083948843648664186162092221179 

noncomputable def Ns564p385 := nat_lit 4056481920730334084789450257203200000 

noncomputable abbrev qz407 := (@HMul.hMul Real Real Real qz588 qz616 qz616)

noncomputable abbrev qz59 := qz407

noncomputable def Ns564p386 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz56 Ns564p382 Ns564p383 Ns564p384 Ns564p385 2417363251857777464059 4503599627370496000 59612072360113 

noncomputable def Ns564p387 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 2417363251857777464059 4503599627370496000 59612072360113 900719925474099200 2417363251857777464059 4503599627370496000 59612072360113 900719925474099200 Ns564p382 

noncomputable def Ns564p388 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz55 13 10 0 1 1544937 67108864 1 

noncomputable def Ns564p389 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 1544937 67108864 1 67108864 1544937 67108864 

noncomputable def Ns564p390 := nat_lit 13128313732954884021981149 

noncomputable abbrev qz60 := qz405

noncomputable def Ns564p391 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz23 55650956238893401 4503599627370496 3302663735 4503599627370496 235904549 67108864 7 67108864 Ns564p390 

noncomputable def Ns564p392 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz23 235904549 67108864 7 67108864 235904549 67108864 7 67108864 55650956238893401 4503599627370496 3302663735 

noncomputable def Ns564p393 := @Ns564p392 4503599627370496 qz406 

noncomputable def Ns564p394 := Ns564p393 qz406 

noncomputable def Ns564p395 := @Ns564p391 302231454903657293676544 1168670115694730467 302231454903657293676544 (Ns564p394 rfl) qz406 

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz355 qz405 qz379)

noncomputable def Ns564p396 := @Enclosure.Real.IsNear.inv_image qz61 Ns564p390 302231454903657293676544 1168670115694730467 302231454903657293676544 772468 772469 33554432 (Ns564p395 rfl) 

noncomputable def Ns564p397 := @Ns564p365 201 2147483648 20084181 671088640 13 671088640 59911022395260928 446371901 10737418240 1213 10737418240 (@Ns564p366 1 2147483648 1 2147483648 6712228845715456 25005001 2147483648 201 2147483648 (@Ns564p367 268435456 25 268435456 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns564p368 (Ns564p374 rfl rfl rfl rfl) rfl) rfl) (@Ns564p375 67108864 1 67108864 1 2147483648 1 2147483648 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns564p376 1 67108864 1 67108864 (@Ns564p381 33554432 (@Ns564p386 900719925474099200 Ns564p377 Ns564p378 Ns564p379 Ns564p380 (@Ns564p387 Ns564p383 Ns564p384 Ns564p385 (Ns564p373 rfl) (Ns564p373 rfl) rfl) (Ns564p373 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns564p388 67108864 20084181 671088640 13 671088640 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns564p389 1 67108864 (Ns564p396 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS565to576.d60 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 := @Ns564p364 446371901 10737418240 1213 10737418240 (BSN.hardyZErrorBoundRS₀_mk qz4 959413 1000 qz11 rfl rfl) (Ns564p397 rfl rfl) 

noncomputable def Ns564p398 := nat_lit 11271337261772721574391498932224 

noncomputable abbrev qz754 := (Enclosure.sfrac Bool.false 962536 1000)

noncomputable abbrev qz618 := qz754

noncomputable abbrev qz408 := qz618

noncomputable abbrev qz62 := qz408

noncomputable abbrev qz755 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 962536 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz619 := qz755

noncomputable abbrev qz409 := qz619

noncomputable abbrev qz63 := qz409

noncomputable abbrev qz756 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 962536 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz620 := qz756

noncomputable abbrev qz410 := qz620

noncomputable abbrev qz64 := qz410

noncomputable abbrev qz621 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz63 qz9))

noncomputable def Ns564p399 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HMul.hMul Real Real Real qz5 qz621 (Zeta.RiemannSiegel.correction qz64)) 565447857 268435456 262831 268435456 2199147756932859080481 18889465931478580854784 777012660207254269 236118324143482260684800 Ns564p398 

noncomputable def Ns564p400 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin BSN.quadSignPos 11 12 962536 1000 287 536870912 268435456 9007199254740992 Bool.false 1041493505109 4479 1334074092 54 154981288 8 

noncomputable def Ns564p401 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 962536 1000 175 234 536870912 268435456 9007199254740992 Bool.false 1041493505109 4479 

noncomputable def Ns564p402 := Ns564p401 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.true 733004945 211629 Bool.true 804693022 Bool.true 301375180 28296951008113761 1 Bool.false 535482307 Bool.false Bool.false 454479785 Bool.true Bool.true 700701370 

noncomputable def Ns564p403 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 962536 1000 39 111 536870912 268435456 9007199254740992 Bool.false 1041493505109 4479 

noncomputable def Ns564p404 := Ns564p403 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 900395386 172831 Bool.true 184393736 Bool.true 330987300 28296951008113761 1 Bool.false 180789729 Bool.false Bool.false 310414859 Bool.false Bool.true 733004945 

noncomputable def Ns564p405 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 962536 1000 137 42 536870912 268435456 9007199254740992 Bool.false 1041493505109 4479 

noncomputable def Ns564p406 := Ns564p405 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.true 760454828 128425 Bool.false 54089284 Bool.false 510476130 28296951008113761 1 Bool.false 53997825 Bool.true Bool.false 311923590 Bool.true Bool.true 900395386 

noncomputable def Ns564p407 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 962536 1000 385 248 536870912 268435456 9007199254740992 Bool.false 1041493505109 4479 

noncomputable def Ns564p408 := Ns564p407 744261104 53 268435448 8 864060384 53 240095976 8 Bool.true 644021109 75841 Bool.false 439179344 Bool.false 662194915 28296951008113761 1 Bool.false 391810561 Bool.true Bool.false 177703798 Bool.false Bool.true 760454828 

noncomputable def Ns564p409 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 962536 1000 810 561 536870912 268435456 9007199254740992 Bool.false 1041493505109 4479 

noncomputable def Ns564p410 := Ns564p409 372130544 53 379625064 8 589812976 53 309962568 8 Bool.true 342712 4541 Bool.false 219426017 Bool.false 677647927 28296951008113761 1 Bool.false 492650546 Bool.true Bool.false 511512451 Bool.true Bool.true 644021109 

noncomputable def Ns564p411 := nat_lit 7633105647021881940070077495780749625490653992147732903 

noncomputable def Ns564p412 := nat_lit 3934726784184924816787100351492103527927289741312000 

noncomputable def Ns564p413 := nat_lit 396576013087858003442925407764480000 

noncomputable def Ns564p414 := nat_lit 2290312424409741545554192475678925127680 

noncomputable abbrev qz622 := (@Eq.refl Real qz754)

noncomputable abbrev qz411 := qz622

noncomputable abbrev qz65 := qz411

noncomputable def Ns564p415 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz62 962536 1000 3705903205184 16000000 1925072 4000 2000 Ns564p413 Ns564p414 qz65 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns564p416 := nat_lit 10004864233664521096488651975269744149123110000587876470620160 

noncomputable abbrev qz623 := (@HSub.hSub Real Real Real qz745 qz746 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz747 (@Nat.cast Real Real.instNatCast 1925072))))

noncomputable abbrev qz412 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 962536 4000) (Real.log (Enclosure.sfrac Bool.false 3705903205184 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz623))

noncomputable abbrev qz624 := (Enclosure.sfrac Bool.false 962536 2000)

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz412 qz624) (@HMul.hMul Real Real Real qz355 qz624 (Real.log Real.pi)))

noncomputable def Ns564p417 := @Enclosure.Real.IsNear.addLit_ft_p qz66 (Enclosure.sfrac Bool.true Ns564p413 Ns564p414) 4368340764362208595987 2251799813685248000 17081208719966219 2048000000000000000000 Ns564p413 Ns564p414 0 1 Ns564p416 

noncomputable def Ns564p418 := nat_lit 36644298282654937925965316096000 

noncomputable abbrev qz67 := (@HSub.hSub Real Real Real qz359 qz412 qz624)

noncomputable def Ns564p419 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (@HMul.hMul Real Real Real qz5 qz624 (Real.log Real.pi)) 5608906508499006935059 2251799813685248000 5923689822431 2000000000000000000 4621467531237 8388608000 360951 67108864000 Ns564p418 4368340764362208595987 2251799813685248000 

noncomputable def Ns564p420 := nat_lit 11217813016998013870118000 

noncomputable abbrev qz68 := qz412

noncomputable def Ns564p421 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz624 6692625701231678869523 2251799813685248000 5923689822431 2000000000000000000 962536 2000 0 1 Ns564p420 5608906508499006935059 2251799813685248000 5923689822431 2000000000000000000 

noncomputable def Ns564p422 := nat_lit 15070453307098596724585548281181896704 

noncomputable def Ns564p423 := nat_lit 119469423305388681238413312 

noncomputable def Ns564p424 := nat_lit 99552675016482077859137978934908470761983477706789484287173108065050862534987862648286854496568598860022347689593382205985455534959160996373809250840978790986270186781467046545090150400 

noncomputable def Ns564p425 := nat_lit 2674796826427005957859587940281958554709384810986281874660390185796115343530801135912229731660967179673314414007617907159738298914815982875995016830190870072711533614078392598255370240 

noncomputable def Ns564p426 := nat_lit 105102304752771947133237460405811485725702535567266599362322908847875392031100051466520055925506865061011583139049022519084733592187601748180426288088006331159948313002099343360 

noncomputable def Ns564p427 := BSN.log_dyadic_bound 1608751205184 5803055205184 8 7 Ns564p424 268435456 81920000 Ns564p425 Ns564p426 152832861 7411806410368 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1608751205184) (BSN.artanhQ 5803055205184) 0 7 Ns564p425 Ns564p424 Ns564p426 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz413 := (Real.log (Enclosure.sfrac Bool.false 3705903205184 16000000))

noncomputable def Ns564p428 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 962536 4000) qz413 962536 4000 0 1 55632285450300519 4503599627370496 48828193 4000000000000000 6693509688523807544523 2251799813685248000 5874861697181 2000000000000000000 (Enclosure.Real.IsNear.const Bool.false 962536 4000) (BSN.isNear_log_sfrac 3705903205184 16000000 55632285450300519 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3705903205184) qz362)) Bool.false Ns564p423 Ns564p112 1000001392640000 81920000000000000000000 55632285450300519 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3705903205184 16000000 17 7411806410368 4194304000000 152832861 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns564p427 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p429 := BSN.arctan_dyadic_bound_f 1000 1925072 1 0 33554432 10240000 0 1 1 0 1 1 17430 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1925072) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1925072) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns564p430 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1925072))) 884279719003555 562949953421312 1 2000000000000000 17430 33554432 1 10240000 29661691482595760537600 883987292128675 562949953421312 195312501 2000000000000000 qz17 (Ns564p429 rfl) rfl rfl 

noncomputable abbrev qz414 := (@HMul.hMul Real Real Real qz588 qz593 qz623)

noncomputable abbrev qz69 := qz414

noncomputable abbrev qz415 := qz623

noncomputable abbrev qz70 := qz415

noncomputable def Ns564p431 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 962536 4000) qz413) qz69 6693509688523807544523 2251799813685248000 5874861697181 2000000000000000000 883987292128675 2251799813685248 195312501 8000000000000000 Ns564p422 6692625701231678869523 2251799813685248000 5923689822431 2000000000000000000 (Ns564p428 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz70 1 4 0 1 883987292128675 562949953421312 195312501 2000000000000000 883987292128675 2251799813685248 195312501 8000000000000000 qz369 Ns564p430 rfl) 

noncomputable def Ns564p432 := @Ns564p417 Ns564p411 Ns564p412 17081208719966219 2048000000000000000000 (@Ns564p419 17081208719966219 2048000000000000000000 (Ns564p421 (Ns564p431 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 962536 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz624 (Real.log Real.pi) 962536 2000 0 1 38410761 33554432 3 268435456 4621467531237 8388608000 360951 67108864000 (Enclosure.Real.IsNear.const Bool.false 962536 2000) RS565to576.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns564p413 Ns564p414) 

noncomputable def Ns564p433 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns564p411 Ns564p412 17081208719966219 2048000000000000000000 65093344069 33554432 561 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz370 qz66 (Enclosure.sfrac Bool.true Ns564p413 Ns564p414)) Bool.false Ns564p411 Ns564p412 17081208719966219 2048000000000000000000 Ns564p415 (Ns564p432 rfl rfl)) 

noncomputable def Ns564p434 := nat_lit 7592818055849095754416128 

noncomputable def Ns564p435 := nat_lit 4835703278458516698824704 

noncomputable def Ns564p436 := nat_lit 5530780446718663680220486650742315004586954162612055595584236303316873211215455932282748435354893823179646440160753089618292949682634320261361 

noncomputable def Ns564p437 := nat_lit 21759806992472160846509436431027924547665573599712653161483140986990306751823661669370177199848368120331884066839754328502985489716814125465600 

noncomputable def Ns564p438 := nat_lit 10200894575748024791337524881323781246801002621598243861510045023689689727043257717649289299635273782370378819171439614010039250906788081 

noncomputable def Ns564p439 := nat_lit 33472711612106593665649879563858948807746205142695171131321341766620341649447326191049409140007783306628564112956677305257622005618960569217265 

noncomputable def Ns564p440 := nat_lit 1980142436314966637032358715223541133837567197573851437694965829816117914415953211912686125186201498950201450082417643893771679564230085417369600 

noncomputable def Ns564p441 := BSN.cos_dyadic_bound_f 215800868541 137438953472 4 3 67108864 20500001 Ns564p436 Ns564p437 Ns564p438 Ns564p439 Ns564p440 Ns564p438 42839 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 215800868541) (BSN.cosEvenQ 137438953472) 0 3 Ns564p436 Ns564p437 Ns564p438 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 215800868541) (BSN.cosOddQ 137438953472) 0 3 Ns564p439 Ns564p440 Ns564p438 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz416 := (@Nat.cast Real Real.instNatCast Ns564p435)

noncomputable def Ns564p442 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz62) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 65093344069) qz383) Bool.false 65093344069 33554432 561 67108864 Bool.true 42839 67108864 1 10240000 (Ns564p433 rfl) (Enclosure.sfrac_false_div 65093344069 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 65093344069) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p434) qz416) 226375608064910080 72057594037927936 Bool.false 42839 67108864 308 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q2 65093344069 33554432 226375608064910080 72057594037927936 308 Ns564p434 Ns564p435 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 42839 67108864 Ns564p434 Ns564p435 215800868541 137438953472 20500001 20480000 (Ns564p441 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p443 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns564p411 Ns564p412 17081208719966219 2048000000000000000000 1041493505109 536870912 4479 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz370 qz66 (Enclosure.sfrac Bool.true Ns564p413 Ns564p414)) Bool.false Ns564p411 Ns564p412 17081208719966219 2048000000000000000000 Ns564p415 (Ns564p432 rfl rfl)) 

noncomputable def Ns564p444 := Ns564p410 75841 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 810 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 492650546 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 561 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 511512451 536870912) qz65 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) Bool.true 42839 67108864 354721 41943040000 342712 536870912 4541 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 42839 67108864 354721 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz62) qz62) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 42839 67108864 5811748864 687194767360000 42839 67108864 354721 41943040000 (Ns564p442 rfl rfl) rfl)) rfl) (Ns564p443 rfl) RS565to576.d7 

noncomputable def Ns564p445 := nat_lit 323555265490640663941388541868251815291432484685553449817169143492171521 

noncomputable def Ns564p446 := nat_lit 5374090296758911600344556097089522971557205166879477862815901341441 

noncomputable def Ns564p447 := nat_lit 970655048291328474000964936492561266828354339646326590495781798673831681 

noncomputable def Ns564p448 := BSN.cos_dyadic_bound_f 219426017 536870912 3 2 536870912 268435456 Ns564p445 Ns564p170 Ns564p446 Ns564p447 Ns564p173 Ns564p446 492650546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 219426017) qz373 0 2 Ns564p445 Ns564p170 Ns564p446 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 219426017) qz374 0 2 Ns564p447 Ns564p173 Ns564p446 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p449 := nat_lit 75585581228975784762650817955157110340951072412514908991195729102920054107534417458957169920896079663406682916321 

noncomputable def Ns564p450 := nat_lit 9376685922940248001141905248523207933676654120521184672996519688005503272384622504753888634097367107159521 

noncomputable def Ns564p451 := nat_lit 377731931876780646032185795899624984113219209514752903260372535106862503980161528257488494849366469417322907878881 

noncomputable def Ns564p452 := BSN.sin_dyadic_bound_f 677647927 536870912 4 3 536870912 268435456 Ns564p449 Ns564p181 Ns564p450 Ns564p451 Ns564p184 Ns564p450 511512451 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 677647927) qz375 0 3 Ns564p449 Ns564p181 Ns564p450 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 677647927) qz376 0 3 Ns564p451 Ns564p184 Ns564p450 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p453 := nat_lit 9347451351896098335629535556343233387866455059915260628897203655498792960 

noncomputable def Ns564p454 := nat_lit 1383997308013382553942943415903694869817877860210307681500150749986816 

noncomputable def Ns564p455 := nat_lit 24479179449800616831085256929654148128908629545147246863246437901282574336 

noncomputable def Ns564p456 := BSN.sin_dyadic_bound_f 439179344 536870912 3 2 536870912 268435456 Ns564p453 Ns564p143 Ns564p454 Ns564p455 Ns564p146 Ns564p454 391810561 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 439179344) qz375 0 2 Ns564p453 Ns564p143 Ns564p454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 439179344) qz376 0 2 Ns564p455 Ns564p146 Ns564p454 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p457 := nat_lit 26523211862471626995634341290979437751190508552768041336536651802956359218853702659453336830527913849499940640625 

noncomputable def Ns564p458 := nat_lit 7109353310905887842879738553232299614957215322425841578115489172575892691639003343570234635885195556640625 

noncomputable def Ns564p459 := nat_lit 160759864507968399100494646114254682456413174461825337299758082549466824557454334359132937201409091669674686240625 

noncomputable def Ns564p460 := BSN.cos_dyadic_bound_f 662194915 536870912 4 3 536870912 268435456 Ns564p457 Ns564p133 Ns564p458 Ns564p459 Ns564p136 Ns564p458 177703798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 662194915) qz373 0 3 Ns564p457 Ns564p133 Ns564p458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 662194915) qz374 0 3 Ns564p459 Ns564p136 Ns564p458 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p461 := Ns564p408 128425 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 385 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 391810561 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 248 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 177703798 536870912) qz65 rfl rfl (Ns564p444 RS565to576.d9 RS565to576.d11 RS565to576.d13 RS565to576.d17 (Ns564p448 rfl rfl) (Ns564p452 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns564p443 rfl) RS565to576.d19 RS565to576.d21 RS565to576.d23 RS565to576.d25 RS565to576.d17 (Ns564p456 rfl rfl) (Ns564p460 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns564p462 := nat_lit 8559431688588174315795869614336 

noncomputable def Ns564p463 := nat_lit 9969209968386869046778552952102584320 

noncomputable def Ns564p464 := nat_lit 69784469778708083327449870664718090240 

noncomputable def Ns564p465 := BSN.sin_dyadic_bound_f 54089284 536870912 2 1 536870912 268435456 Ns564p462 Ns564p463 Ns564p462 Ns564p462 Ns564p464 Ns564p462 53997825 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 54089284) qz375 0 1 Ns564p462 Ns564p463 Ns564p462 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 54089284) qz376 0 1 Ns564p462 Ns564p464 Ns564p462 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p466 := nat_lit 9358316632503160222290855676577071310635496765862063819742575420041177268201001039410522517522204071779904000000 

noncomputable def Ns564p467 := nat_lit 313116007026983435212648194468340985309647264652881782836613497652641009842096624115318896881000000000000 

noncomputable def Ns564p468 := nat_lit 56755380030363736673272823569326949678639119342475724924173057742339631222570375436292114703393996773062617600000 

noncomputable def Ns564p469 := BSN.cos_dyadic_bound_f 510476130 536870912 4 3 536870912 268435456 Ns564p466 Ns564p133 Ns564p467 Ns564p468 Ns564p136 Ns564p467 311923590 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 510476130) qz373 0 3 Ns564p466 Ns564p133 Ns564p467 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 510476130) qz374 0 3 Ns564p468 Ns564p136 Ns564p467 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p470 := Ns564p406 172831 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 137 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 53997825 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 311923590 536870912) qz65 rfl rfl (Ns564p461 rfl rfl) (Ns564p443 rfl) RS565to576.d27 RS565to576.d29 RS565to576.d31 RS565to576.d33 RS565to576.d17 (Ns564p465 rfl rfl) (Ns564p469 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p471 := nat_lit 1156071392672803022528252812988416 

noncomputable def Ns564p472 := BSN.sin_dyadic_bound_f 184393736 536870912 2 1 536870912 268435456 Ns564p471 Ns564p463 Ns564p471 Ns564p471 Ns564p464 Ns564p471 180789729 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 184393736) qz375 0 1 Ns564p471 Ns564p463 Ns564p471 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 184393736) qz376 0 1 Ns564p471 Ns564p464 Ns564p471 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p473 := nat_lit 3015277949469809444711269107973184462749997075245070293915057382400000000 

noncomputable def Ns564p474 := nat_lit 144042497072261292320455681209665252911023329215788810000000000000000 

noncomputable def Ns564p475 := nat_lit 7896923322663764884532424068826857944411945921204072825989912192000000000 

noncomputable def Ns564p476 := BSN.sin_dyadic_bound_f 330987300 536870912 3 2 536870912 268435456 Ns564p473 Ns564p143 Ns564p474 Ns564p475 Ns564p146 Ns564p474 310414859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 330987300) qz375 0 2 Ns564p473 Ns564p143 Ns564p474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 330987300) qz376 0 2 Ns564p475 Ns564p146 Ns564p474 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p477 := Ns564p404 211629 BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 180789729 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 111 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 310414859 536870912) qz65 rfl rfl (Ns564p470 rfl) (Ns564p443 rfl) RS565to576.d35 RS565to576.d37 RS565to576.d39 RS565to576.d41 RS565to576.d17 (Ns564p472 rfl rfl) (Ns564p476 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p478 := nat_lit 150419263272763979368342680019945995322741615158112362849112565654883078643328875429561123113914215486167031484416 

noncomputable def Ns564p479 := nat_lit 73716180305514683745412851578483857606106033848317488667789842557099796761854830997881794027894789794697216 

noncomputable def Ns564p480 := nat_lit 751321336948777591014379886273188235304431801394876059444806387470601483381867567934551387050591537307657501413376 

noncomputable def Ns564p481 := BSN.sin_dyadic_bound_f 804693022 536870912 4 3 536870912 268435456 Ns564p478 Ns564p181 Ns564p479 Ns564p480 Ns564p184 Ns564p479 535482307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 804693022) qz375 0 3 Ns564p478 Ns564p181 Ns564p479 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 804693022) qz376 0 3 Ns564p480 Ns564p184 Ns564p479 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p482 := nat_lit 1151448130665205756961582028478472946809776877514970198026749358284800000 

noncomputable def Ns564p483 := nat_lit 68054972399127633162488555227720653719498968162134073516057600000000 

noncomputable def Ns564p484 := nat_lit 3454208282050819015618421108324963399121891634608586325933215959654400000 

noncomputable def Ns564p485 := BSN.cos_dyadic_bound_f 301375180 536870912 3 2 536870912 268435456 Ns564p482 Ns564p170 Ns564p483 Ns564p484 Ns564p173 Ns564p483 454479785 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 301375180) qz373 0 2 Ns564p482 Ns564p170 Ns564p483 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 301375180) qz374 0 2 Ns564p484 Ns564p173 Ns564p483 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz625 := (BSN.cos_quad_nat3 175 rfl)

noncomputable def Ns564p486 := Ns564p402 246523 BSN.abs_quadSignPos qz625 (BSN.sfrac_eq_quadSignPos_mul Bool.false 535482307 536870912) BSN.abs_quadSignNeg qz599 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 454479785 536870912) qz65 rfl rfl (Ns564p477 rfl) (Ns564p443 rfl) RS565to576.d43 RS565to576.d45 RS565to576.d47 RS565to576.d49 RS565to576.d17 (Ns564p481 rfl rfl) (Ns564p485 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p487 := nat_lit 26432020779957638314862406969675335146740698958130339147303271979039677985 

noncomputable def Ns564p488 := nat_lit 11060496654749350638769500907127480266517957306628565894694240592158241 

noncomputable def Ns564p489 := nat_lit 69208813619590887114081629538157195178175087245178251517202874031764233761 

noncomputable def Ns564p490 := BSN.sin_dyadic_bound_f 569471283 536870912 3 2 536870912 268435456 Ns564p487 Ns564p143 Ns564p488 Ns564p489 Ns564p146 Ns564p488 468531900 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 569471283) qz375 0 2 Ns564p487 Ns564p143 Ns564p488 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 569471283) qz376 0 2 Ns564p489 Ns564p146 Ns564p488 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p491 := Ns564p400 Bool.true 700701370 246523 Bool.true 569471283 28296951008113761 1 Bool.false 468531900 Bool.false Bool.true 565447857 262831 BSN.abs_quadSignPos qz377 (BSN.sfrac_eq_quadSignPos_mul Bool.false 468531900 536870912) qz65 rfl (Ns564p486 rfl) (Ns564p443 rfl) RS565to576.d51 RS565to576.d53 RS565to576.d17 (Ns564p490 rfl rfl) rfl 

noncomputable def Ns564p492 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) 565447857 536870912 262831 536870912 565447857 536870912 262831 536870912 607145013352071168 565447857 268435456 262831 268435456 (Ns564p491 rfl rfl rfl rfl) 

noncomputable def Ns564p493 := @Enclosure.Real.IsNear.mulLit_ff qz621 (Zeta.RiemannSiegel.correction qz64) 9537633 33554432 1 33554432 230575841713857 562949953421312 324663522289 28147497671065600 2199147756932859080481 18889465931478580854784 

noncomputable abbrev qz626 := (@HPow.hPow Real Real Real qz7 qz63 qz9)

noncomputable def Ns564p494 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz626 1 1 0 1 9537633 33554432 1 33554432 9537633 33554432 1 33554432 

noncomputable def Ns564p495 := @Enclosure.Real.IsNear.sqrt_image qz63 1285070624119 8388608000 120317 8388608000 415306204 415306244 33554432 (@Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz5 qz62 qz3) Bool.false 1285070624119 8388608000 120317 8388608000 (BSN.t_div_two_pi_mk qz62 962536 1000 qz65) (@Enclosure.Real.IsNear.mulLit_ff qz62 qz3 962536 1000 0 1 10680707 67108864 1 67108864 1285070624119 8388608000 120317 8388608000 (Enclosure.Real.IsNear.const Bool.false 962536 1000) RS565to576.d56 rfl)) 

noncomputable abbrev qz757 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 962536 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz627 := qz757

noncomputable abbrev qz417 := qz627

noncomputable abbrev qz71 := qz417

noncomputable def Ns564p496 := @Enclosure.Real.IsNear.sqrt_image qz71 25956639 2097152 5 8388608 118048141 118048148 33554432 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 830612448 67108864 40 67108864 25956639 2097152 5 8388608 (Ns564p495 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns564p497 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz71) 236096289 67108864 7 67108864 9537632 9537634 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz71) Bool.false 236096289 67108864 7 67108864 236096289 67108864 7 67108864 (Ns564p496 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns564p498 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 19075266 67108864 2 67108864 9537633 33554432 1 33554432 (Ns564p497 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz418 := (@HMul.hMul Real Real Real qz588 qz586 qz620)

noncomputable abbrev qz72 := (Real.cos qz418)

noncomputable abbrev qz628 := (@HMul.hMul Real Real Real qz741 qz756 qz756)

noncomputable abbrev qz419 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz628 qz620) qz604)

noncomputable abbrev qz73 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz419))

noncomputable def Ns564p499 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz72) qz73) Bool.false 230575841713857 

noncomputable def Ns564p500 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz72) qz73 46842073 33554432 63 

noncomputable abbrev qz74 := (@Neg.neg Real Real.instNeg (Real.cos qz418))

noncomputable def Ns564p501 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz72) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz74)) Bool.true 46842073 33554432 63 8388608 (BSN.inv_eq_neg_inv_neg qz72) 

noncomputable def Ns564p502 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz74) Bool.false 93684146 67108864 504 67108864 46842073 33554432 

noncomputable def Ns564p503 := @Enclosure.Real.IsNear.recentre' qz72 Bool.true 48072164 67108864 661897216 171798691840000 12018041 16777216 40399 10485760000 

noncomputable abbrev qz75 := qz418

noncomputable def Ns564p504 := @Enclosure.Real.IsNear.cos_image qz75 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 79501395) qz383) Bool.false 79501395 33554432 63 16777216 Bool.true 48072164 67108864 1 

noncomputable def Ns564p505 := nat_lit 26986075414478484754666951 

noncomputable def Ns564p506 := nat_lit 7205759403792793600000000000000 

noncomputable def Ns564p507 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz64 884279719003555 140737488355328 1 500000000000000 790815 2097152 5 8388608 699301665983796347325 295147905179352825856 Ns564p505 

noncomputable def Ns564p508 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz1 25956639 2097152 5 8388608 12 1 0 1 790815 790815 2097152 5 

noncomputable def Ns564p509 := @Ns564p508 8388608 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 830612448 67108864 40 67108864 25956639 2097152 5 8388608 (Ns564p495 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns564p510 := @Enclosure.Real.IsNear.recentre' qz75 Bool.false 699301665983796347325 295147905179352825856 Ns564p505 Ns564p506 79501395 33554432 63 16777216 (@Ns564p507 Ns564p506 RS565to576.d55 (Ns564p509 rfl rfl) rfl) 

noncomputable def Ns564p511 := nat_lit 3861453545445230777466880 

noncomputable def Ns564p512 := nat_lit 156560995273467429022945029727967998227715437468482683078745916250769012757001389149429922625 

noncomputable def Ns564p513 := nat_lit 21047866328309822147098773013327008610175610079459480726266162821090989575275902140644161 

noncomputable def Ns564p514 := nat_lit 410006624408835526776617870321704132582457290001135521285063444964589457523310334406945897281 

noncomputable def Ns564p515 := BSN.sin_dyadic_bound_f 109749110647 137438953472 3 2 67108864 20500001 Ns564p512 Ns564p207 Ns564p513 Ns564p514 Ns564p210 Ns564p513 48072164 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 109749110647) qz371 0 2 Ns564p512 Ns564p207 Ns564p513 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 109749110647) qz372 0 2 Ns564p514 Ns564p210 Ns564p513 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p516 := @Ns564p504 10240000 (Ns564p510 rfl) (Enclosure.sfrac_false_div 79501395 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 79501395) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p511) qz416) 226375608064910080 72057594037927936 Bool.false 48072164 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 79501395 33554432 226375608064910080 72057594037927936 0 Ns564p511 Ns564p435 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 48072164 67108864 Ns564p511 Ns564p435 109749110647 137438953472 20500001 20480000 (Ns564p515 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p517 := @Enclosure.Real.IsNear.inv_image qz74 12018041 16777216 40399 10485760000 46841821 46842325 33554432 (@Enclosure.Real.IsNear.neg qz72 Bool.true 12018041 16777216 40399 10485760000 (Ns564p503 (Ns564p516 rfl rfl) rfl)) 

noncomputable def Ns564p518 := Ns564p501 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz74) Bool.false 46842073 33554432 63 8388608 (@Ns564p502 63 8388608 (Ns564p517 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p519 := @Enclosure.Real.IsNear.recentre' qz73 Bool.true 9844818 33554432 

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz355 qz352 qz419)

noncomputable abbrev qz629 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns564p520 := @Enclosure.Real.IsNear.cos_image qz76 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31349505)) qz629) Bool.true 31349505 16777216 

noncomputable def Ns564p521 := nat_lit 1156592598749000228670684445 

noncomputable def Ns564p522 := nat_lit 618970019642690137449562112 

noncomputable def Ns564p523 := nat_lit 1985518444140325773141007554589783 

noncomputable def Ns564p524 := @Enclosure.Real.IsNear.recentre' qz76 Bool.true Ns564p521 Ns564p522 Ns564p523 

noncomputable def Ns564p525 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz77 := qz419

noncomputable def Ns564p526 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz77 884279719003555 140737488355328 1 500000000000000 1307948801599 

noncomputable abbrev qz420 := (@HSub.hSub Real Real Real qz592 qz628 qz620)

noncomputable abbrev qz78 := qz420

noncomputable def Ns564p527 := @Enclosure.Real.IsNear.subLit_tf qz78 qz31 1033070894655 4398046511104 73575665 70368744177664 1 16 

noncomputable abbrev qz421 := qz628

noncomputable abbrev qz79 := qz421

noncomputable def Ns564p528 := @Enclosure.Real.IsNear.subLit_ff_n qz79 qz64 625388364225 4398046511104 31632625 70368744177664 790815 2097152 5 8388608 

noncomputable def Ns564p529 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 790815 2097152 5 8388608 790815 2097152 5 8388608 625388364225 4398046511104 

noncomputable def Ns564p530 := nat_lit 121885201243147572489400313353044103217164170093193635488608435914778776128916916878839316890625 

noncomputable def Ns564p531 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns564p532 := nat_lit 901090174112617211365080158452065287702549543232305376160178877142772480466772168212890625 

noncomputable def Ns564p533 := nat_lit 735880915387217747512838279520292083892858905467744327297348945547731231369310666491144110490625 

noncomputable def Ns564p534 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns564p535 := BSN.cos_dyadic_bound_t 31349505 16777216 4 3 33554432 10240000 Ns564p530 Ns564p531 Ns564p532 Ns564p533 Ns564p534 Ns564p532 9844818 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 31349505) (BSN.cosEvenQ 16777216) 0 3 Ns564p530 Ns564p531 Ns564p532 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 31349505) (BSN.cosOddQ 16777216) 0 3 Ns564p533 Ns564p534 Ns564p532 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p536 := @Ns564p519 2296594432 343597383680000 4922409 16777216 140173 20971520000 (@Ns564p520 221 33554432 Bool.true 9844818 33554432 1 10240000 (@Ns564p524 Ns564p525 31349505 16777216 221 33554432 (@Ns564p526 4398046511104 73575665 70368744177664 Ns564p521 Ns564p522 Ns564p523 Ns564p525 RS565to576.d55 (@Ns564p527 0 1 20927180825584 1307948801599 4398046511104 73575665 70368744177664 (@Ns564p528 2166506692867522560 1033070894655 4398046511104 73575665 70368744177664 (@Ns564p529 31632625 70368744177664 (Ns564p509 rfl rfl) (Ns564p509 rfl rfl) rfl) (Ns564p509 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 31349505 16777216) (BSN.cos_neg_of_bound 31349505 16777216 Bool.true 9844818 33554432 1 10240000 (Ns564p535 rfl rfl)) rfl rfl) 

noncomputable def Ns564p537 := @Ns564p493 777012660207254269 236118324143482260684800 (Ns564p494 qz33 (@Enclosure.Real.IsNear.of_eq qz626 (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 9537633 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz63 (BSN.t_div_two_pi_nonneg qz62 962536 1000 qz65)) Ns564p498) rfl) (@Ns564p499 562949953421312 324663522289 28147497671065600 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz62 962536 1000 12 qz65 rfl rfl (@BSN.floor_sqrt_eq_dec qz62 962536 1000 12 qz65 rfl rfl rfl))) (@Ns564p500 8388608 4922409 16777216 140173 20971520000 230575841713857 562949953421312 324663522289 28147497671065600 Ns564p518 (Ns564p536 rfl) rfl)) 

noncomputable def Ns564p538 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (hardyZApproximantRS₀ qz62) Bool.true 41989003351974195146529 18889465931478580854784 231965605172202339069 236118324143482260684800 (@Eq.refl Real (hardyZApproximantRS₀ qz62)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HMul.hMul Real Real Real qz5 qz621 (Zeta.RiemannSiegel.correction qz64))) Bool.true 41989003351974195146529 18889465931478580854784 231965605172202339069 236118324143482260684800 (BSN.hardyZApproximantRS₀_eq qz62 12 (@BSN.floor_sqrt_eq_dec qz62 962536 1000 12 qz65 rfl rfl rfl)) (@Ns564p399 41989003351974195146529 18889465931478580854784 231965605172202339069 236118324143482260684800 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12)) Bool.true 565447857 268435456 262831 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (Ns564p492 (Ns564p491 rfl rfl rfl rfl) rfl rfl)) (Ns564p537 rfl) rfl rfl)) 

theorem RS565to576.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz62) Bool.true 41989003351974195146529 18889465931478580854784 231965605172202339069 236118324143482260684800 := Ns564p538 

noncomputable def Ns564p539 := nat_lit 94447329657392904273920000 

noncomputable def Ns564p540 := nat_lit 6688586538717420342425948258304 

noncomputable abbrev qz758 := (Enclosure.sfrac Bool.false 963395 1000)

noncomputable abbrev qz630 := qz758

noncomputable abbrev qz422 := qz630

noncomputable abbrev qz80 := qz422

noncomputable abbrev qz759 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 963395 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz631 := qz759

noncomputable abbrev qz423 := qz631

noncomputable abbrev qz81 := qz423

noncomputable abbrev qz760 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 963395 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz632 := qz760

noncomputable abbrev qz424 := qz632

noncomputable abbrev qz82 := qz424

noncomputable abbrev qz633 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz81 qz9))

noncomputable def Ns564p541 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HMul.hMul Real Real Real qz5 qz633 (Zeta.RiemannSiegel.correction qz82)) 75322997 268435456 263063 268435456 17486151109596663966355 151115727451828646838272 301601362243442655941 Ns564p539 Ns564p540 

noncomputable def Ns564p542 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin BSN.quadSignPos 11 12 963395 1000 287 536870912 268435456 9007199254740992 Bool.false 1042653846460 4483 1334074092 54 154981288 8 

noncomputable def Ns564p543 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 963395 1000 175 234 536870912 268435456 9007199254740992 Bool.false 1042653846460 4483 

noncomputable def Ns564p544 := Ns564p543 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.true 77068777 211815 Bool.true 706239702 Bool.true 246876258 28296951008113761 1 Bool.false 519466592 Bool.false Bool.false 481101967 Bool.true Bool.true 57856706 

noncomputable def Ns564p545 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 963395 1000 38 111 536870912 268435456 9007199254740992 Bool.false 1042653846460 4483 

noncomputable def Ns564p546 := Ns564p545 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 131193241 172982 Bool.true 826347691 Bool.true 183944638 28296951008113761 1 Bool.false 16964341 Bool.true Bool.false 180366797 Bool.false Bool.true 77068777 

noncomputable def Ns564p547 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 963395 1000 137 42 536870912 268435456 9007199254740992 Bool.false 1042653846460 4483 

noncomputable def Ns564p548 := Ns564p547 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.false 40154931 128536 Bool.false 388121140 Bool.false 773417998 28296951008113761 1 Bool.false 355186331 Bool.true Bool.false 69699564 Bool.true Bool.true 131193241 

noncomputable def Ns564p549 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 963395 1000 386 249 536870912 268435456 9007199254740992 Bool.false 1042653846460 4483 

noncomputable def Ns564p550 := Ns564p549 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 404831435 75905 Bool.false 116885550 Bool.false 236993539 28296951008113761 1 Bool.false 524197147 Bool.true Bool.false 229371237 Bool.true Bool.false 40154931 

noncomputable def Ns564p551 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 963395 1000 811 562 536870912 268435456 9007199254740992 Bool.false 1042653846460 4483 

noncomputable def Ns564p552 := Ns564p551 372130544 53 379625064 8 589812976 53 309962568 8 Bool.false 446146848 4541 Bool.false 216792375 Bool.false 488025075 28296951008113761 1 Bool.false 210948518 Bool.false Bool.false 329918508 Bool.true Bool.false 404831435 

noncomputable def Ns564p553 := nat_lit 3222323951235957286896362719813333584135645278786825209 

noncomputable def Ns564p554 := nat_lit 1659200706286545146520891895737451263417159725875200 

noncomputable def Ns564p555 := nat_lit 398348763799306985960071098500000000 

noncomputable def Ns564p556 := nat_lit 2302603533242055170616863068646445000000 

noncomputable abbrev qz634 := (@Eq.refl Real qz758)

noncomputable abbrev qz425 := qz634

noncomputable abbrev qz83 := qz425

noncomputable def Ns564p557 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz80 963395 1000 3712520704100 16000000 1926790 4000 2000 Ns564p555 Ns564p556 qz83 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns564p558 := nat_lit 16111619756179786434481813599066667920678226393934126045000000 

noncomputable abbrev qz635 := (@HSub.hSub Real Real Real qz745 qz746 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz747 (@Nat.cast Real Real.instNatCast 1926790))))

noncomputable abbrev qz426 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 963395 4000) (Real.log (Enclosure.sfrac Bool.false 3712520704100 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz635))

noncomputable abbrev qz636 := (Enclosure.sfrac Bool.false 963395 2000)

noncomputable abbrev qz84 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz426 qz636) (@HMul.hMul Real Real Real qz355 qz636 (Real.log Real.pi)))

noncomputable def Ns564p559 := @Enclosure.Real.IsNear.addLit_ft_p qz84 (Enclosure.sfrac Bool.true Ns564p555 Ns564p556) 6997132141414450695281 3602879701896396800 27354252723674353 3276800000000000000000 Ns564p555 Ns564p556 0 1 Ns564p558 

noncomputable def Ns564p560 := nat_lit 18782783570728445573772722831360 

noncomputable abbrev qz85 := (@HSub.hSub Real Real Real qz359 qz426 qz636)

noncomputable def Ns564p561 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (@HMul.hMul Real Real Real qz5 qz636 (Real.log Real.pi)) 1796761745843225199229 720575940379279360 9486292399447 3200000000000000000 7400947018719 13421772800 578037 107374182400 Ns564p560 6997132141414450695281 3602879701896396800 

noncomputable def Ns564p562 := nat_lit 17967617458432251992290000 

noncomputable abbrev qz86 := qz426

noncomputable def Ns564p563 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz636 10719306874420365593713 3602879701896396800 9486292399447 3200000000000000000 963395 2000 0 1 Ns564p562 1796761745843225199229 720575940379279360 9486292399447 3200000000000000000 

noncomputable def Ns564p564 := nat_lit 24137733222654777324397374058029645824 

noncomputable def Ns564p565 := nat_lit 119486677784511439234400256 

noncomputable def Ns564p566 := nat_lit 101153854433714279280909725274680755010161139504360950654906570851636505675382062565373420390504132649415439602756034755946527688318072284562699588824798510250000000000000000000000000000 

noncomputable def Ns564p567 := nat_lit 2734785223192467646982642118538711905052201302109371422778824775680043966403442319570732887208594974848586843559240677844019040774059010788307995428391656150000000000000000000000000000 

noncomputable def Ns564p568 := nat_lit 111319475496901523153127158301269332684935882230338216833524254726322892999822629722023149081961798601859988192818170273760763057889368368049610567350000000000000000000000000000 

noncomputable def Ns564p569 := BSN.log_dyadic_bound 1615368704100 5809672704100 8 7 Ns564p566 268435456 81920000 Ns564p567 Ns564p568 153311769 7425041408200 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1615368704100) (BSN.artanhQ 5809672704100) 0 7 Ns564p567 Ns564p566 Ns564p568 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz427 := (Real.log (Enclosure.sfrac Bool.false 3712520704100 16000000))

noncomputable def Ns564p570 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 963395 4000) qz427 963395 4000 0 1 55640320193260647 4503599627370496 48828193 4000000000000000 10720721254517268203313 3602879701896396800 9408167399047 3200000000000000000 (Enclosure.Real.IsNear.const Bool.false 963395 4000) (BSN.isNear_log_sfrac 3712520704100 16000000 55640320193260647 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3712520704100) qz362)) Bool.false Ns564p565 Ns564p112 1000001392640000 81920000000000000000000 55640320193260647 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3712520704100 16000000 17 7425041408200 4194304000000 153311769 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns564p569 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p571 := BSN.arctan_dyadic_bound_f 1000 1926790 1 0 33554432 10240000 0 1 1 0 1 1 17414 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1926790) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1926790) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns564p572 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1926790))) 884279719003555 562949953421312 1 2000000000000000 17414 33554432 1 10240000 29661700489795015278592 883987560564131 562949953421312 195312501 2000000000000000 qz17 (Ns564p571 rfl) rfl rfl 

noncomputable abbrev qz428 := (@HMul.hMul Real Real Real qz588 qz593 qz635)

noncomputable abbrev qz87 := qz428

noncomputable abbrev qz429 := qz635

noncomputable abbrev qz88 := qz429

noncomputable def Ns564p573 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 963395 4000) qz427) qz87 10720721254517268203313 3602879701896396800 9408167399047 3200000000000000000 883987560564131 2251799813685248 195312501 8000000000000000 Ns564p564 10719306874420365593713 3602879701896396800 9486292399447 3200000000000000000 (Ns564p570 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz88 1 4 0 1 883987560564131 562949953421312 195312501 2000000000000000 883987560564131 2251799813685248 195312501 8000000000000000 qz369 Ns564p572 rfl) 

noncomputable def Ns564p574 := @Ns564p559 Ns564p553 Ns564p554 27354252723674353 3276800000000000000000 (@Ns564p561 27354252723674353 3276800000000000000000 (Ns564p563 (Ns564p573 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 963395 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz636 (Real.log Real.pi) 963395 2000 0 1 38410761 33554432 3 268435456 7400947018719 13421772800 578037 107374182400 (Enclosure.Real.IsNear.const Bool.false 963395 2000) RS565to576.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns564p555 Ns564p556) 

noncomputable def Ns564p575 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns564p553 Ns564p554 27354252723674353 3276800000000000000000 130331730807 67108864 561 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz370 qz84 (Enclosure.sfrac Bool.true Ns564p555 Ns564p556)) Bool.false Ns564p553 Ns564p554 27354252723674353 3276800000000000000000 Ns564p557 (Ns564p574 rfl rfl)) 

noncomputable def Ns564p576 := nat_lit 5704867844566594181136384 

noncomputable def Ns564p577 := nat_lit 25896620142147837778932829278697206820011749506140468324809406973170313711297849811754090496 

noncomputable def Ns564p578 := nat_lit 5133330660362904937396483134791632965849700352038159351603073932373040875403608499582161387520 

noncomputable def Ns564p579 := nat_lit 1866062999929681918406525082266271440580792763740670653671296106760655473659807300386816 

noncomputable def Ns564p580 := nat_lit 77686128300443653972961674785927087917154086932893923633120878327297419822946229820661497856 

noncomputable def Ns564p581 := nat_lit 230999879716330722182841741065623483463236515841717170822138326956786839393162382481197262438400 

noncomputable def Ns564p582 := BSN.cos_dyadic_bound_f 81071048108 137438953472 3 2 67108864 20500001 Ns564p577 Ns564p578 Ns564p579 Ns564p580 Ns564p581 Ns564p579 55768356 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 81071048108) (BSN.cosEvenQ 137438953472) 0 2 Ns564p577 Ns564p578 Ns564p579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 81071048108) (BSN.cosOddQ 137438953472) 0 2 Ns564p580 Ns564p581 Ns564p579 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p583 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz80) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 130331730807) qz396) Bool.false 130331730807 67108864 561 67108864 Bool.false 55768356 67108864 1 10240000 (Ns564p575 rfl) (Enclosure.sfrac_false_div 130331730807 67108864) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 130331730807) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p576) qz397) 226375608064910080 72057594037927936 Bool.false 55768356 67108864 309 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q0 130331730807 67108864 226375608064910080 72057594037927936 309 Ns564p576 Ns564p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 55768356 67108864 Ns564p576 Ns564p112 81071048108 137438953472 20500001 20480000 (Ns564p582 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p584 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns564p553 Ns564p554 27354252723674353 3276800000000000000000 1042653846460 536870912 4483 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz370 qz84 (Enclosure.sfrac Bool.true Ns564p555 Ns564p556)) Bool.false Ns564p553 Ns564p554 27354252723674353 3276800000000000000000 Ns564p557 (Ns564p574 rfl rfl)) 

noncomputable def Ns564p585 := Ns564p552 75905 BSN.abs_quadSignPos (BSN.cos_quad_nat3 811 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 210948518 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 562 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 329918508 536870912) qz83 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) Bool.false 13942089 16777216 354721 41943040000 446146848 536870912 4541 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 13942089 16777216 354721 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz80) qz80) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 55768356 67108864 5811748864 687194767360000 13942089 16777216 354721 41943040000 (Ns564p583 rfl rfl) rfl)) rfl) (Ns564p584 rfl) RS565to576.d7 

noncomputable def Ns564p586 := nat_lit 2208899783801877214311582275390625 

noncomputable def Ns564p587 := BSN.sin_dyadic_bound_f 216792375 536870912 2 1 536870912 268435456 Ns564p586 Ns564p463 Ns564p586 Ns564p586 Ns564p464 Ns564p586 210948518 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 216792375) qz375 0 1 Ns564p586 Ns564p463 Ns564p586 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 216792375) qz376 0 1 Ns564p586 Ns564p464 Ns564p586 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p588 := nat_lit 7920157138773102223532169801026652829485028386530127773866287949025390625 

noncomputable def Ns564p589 := nat_lit 3217637353100870467950956090727629068270583445962407138452301025390625 

noncomputable def Ns564p590 := nat_lit 23754036141613104929660607490898503230318543992698458507321959245025390625 

noncomputable def Ns564p591 := BSN.cos_dyadic_bound_f 488025075 536870912 3 2 536870912 268435456 Ns564p588 Ns564p170 Ns564p589 Ns564p590 Ns564p173 Ns564p589 329918508 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 488025075) qz373 0 2 Ns564p588 Ns564p170 Ns564p589 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 488025075) qz374 0 2 Ns564p590 Ns564p173 Ns564p589 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p592 := nat_lit 186656577724210194840434006250000 

noncomputable def Ns564p593 := BSN.cos_dyadic_bound_f 116885550 536870912 2 1 536870912 268435456 Ns564p592 Ns564p163 Ns564p592 Ns564p592 Ns564p164 Ns564p592 524197147 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 116885550) qz373 0 1 Ns564p592 Ns564p163 Ns564p592 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 116885550) qz374 0 1 Ns564p592 Ns564p164 Ns564p592 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p594 := nat_lit 792524619631086427851942300863090263201338785141423682135441941033433505 

noncomputable def Ns564p595 := nat_lit 9951580267244371326470202125648022037569325277843340331878308952481 

noncomputable def Ns564p596 := nat_lit 2075643605999079391582463169552271068729731229796135992565620137825450401 

noncomputable def Ns564p597 := BSN.sin_dyadic_bound_f 236993539 536870912 3 2 536870912 268435456 Ns564p594 Ns564p143 Ns564p595 Ns564p596 Ns564p146 Ns564p595 229371237 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 236993539) qz375 0 2 Ns564p594 Ns564p143 Ns564p595 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 236993539) qz376 0 2 Ns564p596 Ns564p146 Ns564p595 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p598 := Ns564p550 128536 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 386 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 524197147 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 249 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 229371237 536870912) qz83 rfl rfl (Ns564p585 RS565to576.d9 RS565to576.d11 RS565to576.d13 RS565to576.d17 (Ns564p587 rfl rfl) (Ns564p591 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns564p584 rfl) RS565to576.d19 RS565to576.d21 RS565to576.d23 RS565to576.d25 RS565to576.d17 (Ns564p593 rfl rfl) (Ns564p597 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns564p599 := nat_lit 5701244982663815248111101062604092381121167997379777903203691346698240000 

noncomputable def Ns564p600 := nat_lit 514918371014679705244213115315669292753120169624396184985625600000000 

noncomputable def Ns564p601 := nat_lit 14930998420090254263625345485585921343129077798577169295519691085619200000 

noncomputable def Ns564p602 := BSN.sin_dyadic_bound_f 388121140 536870912 3 2 536870912 268435456 Ns564p599 Ns564p143 Ns564p600 Ns564p601 Ns564p146 Ns564p600 355186331 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 388121140) qz375 0 2 Ns564p599 Ns564p143 Ns564p600 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 388121140) qz376 0 2 Ns564p601 Ns564p146 Ns564p600 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p603 := nat_lit 49414476034296239472906333036090178744532738393073182015379190594670260125114029285239637013549780345454128664576 

noncomputable def Ns564p604 := nat_lit 45811160169595392923136615084057119034486680813301861691564279917296684196814525906069355916330211295236096 

noncomputable def Ns564p605 := nat_lit 299269865893263232381537273685295784952529707530499710957003289913532863888394821670994070040294031426897336995840 

noncomputable def Ns564p606 := BSN.cos_dyadic_bound_f 773417998 536870912 4 3 536870912 268435456 Ns564p603 Ns564p133 Ns564p604 Ns564p605 Ns564p136 Ns564p604 69699564 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 773417998) qz373 0 3 Ns564p603 Ns564p133 Ns564p604 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 773417998) qz374 0 3 Ns564p605 Ns564p136 Ns564p604 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p607 := Ns564p548 172982 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 137 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 355186331 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 69699564 536870912) qz83 rfl rfl (Ns564p598 rfl rfl) (Ns564p584 rfl) RS565to576.d27 RS565to576.d29 RS565to576.d31 RS565to576.d33 RS565to576.d17 (Ns564p602 rfl rfl) (Ns564p606 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p608 := nat_lit 64444399926341898424658125168830237024781402522589727215921400483747592949551098796379681690495895175907314060561 

noncomputable def Ns564p609 := nat_lit 101380356712357212771468307728394041502829075313685916978345395115390663412622829171406918426771257174084881 

noncomputable def Ns564p610 := nat_lit 390094303872427973916207712922558337359654864413090998689791243904997244635974407205397100419432293188870276467985 

noncomputable def Ns564p611 := BSN.cos_dyadic_bound_f 826347691 536870912 4 3 536870912 268435456 Ns564p608 Ns564p133 Ns564p609 Ns564p610 Ns564p136 Ns564p609 16964341 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 826347691) qz373 0 3 Ns564p608 Ns564p133 Ns564p609 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 826347691) qz374 0 3 Ns564p610 Ns564p136 Ns564p609 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p612 := nat_lit 1144849847275226848611227108689936 

noncomputable def Ns564p613 := BSN.sin_dyadic_bound_f 183944638 536870912 2 1 536870912 268435456 Ns564p612 Ns564p463 Ns564p612 Ns564p612 Ns564p464 Ns564p612 180366797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 183944638) qz375 0 1 Ns564p612 Ns564p463 Ns564p612 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 183944638) qz376 0 1 Ns564p612 Ns564p464 Ns564p612 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p614 := Ns564p546 211815 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 16964341 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 111 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 180366797 536870912) qz83 rfl rfl (Ns564p607 rfl) (Ns564p584 rfl) RS565to576.d35 RS565to576.d37 RS565to576.d39 RS565to576.d41 RS565to576.d17 (Ns564p611 rfl rfl) (Ns564p613 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p615 := nat_lit 89185962159356057446584038416834189768283698470425507652641431928429612352833460414810647587551924905003098116096 

noncomputable def Ns564p616 := nat_lit 15396625231320130486200451917088570413217505794102281756056735885527220740864166085457181176001389253431296 

noncomputable def Ns564p617 := nat_lit 445657039853988467968410182648935578831952329700402702295684272430811922418751884617048745862373092579641890246656 

noncomputable def Ns564p618 := BSN.sin_dyadic_bound_f 706239702 536870912 4 3 536870912 268435456 Ns564p615 Ns564p181 Ns564p616 Ns564p617 Ns564p184 Ns564p616 519466592 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 706239702) qz375 0 3 Ns564p615 Ns564p181 Ns564p616 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 706239702) qz376 0 3 Ns564p617 Ns564p184 Ns564p616 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p619 := nat_lit 518462848252710820875963941512602525684820326120150566388893396112343296 

noncomputable def Ns564p620 := nat_lit 13798586740580503839764699501037367737520900584798115452427488297216 

noncomputable def Ns564p621 := nat_lit 1555360947584651301620212295138805502318985936559282102935775333360435456 

noncomputable def Ns564p622 := BSN.cos_dyadic_bound_f 246876258 536870912 3 2 536870912 268435456 Ns564p619 Ns564p170 Ns564p620 Ns564p621 Ns564p173 Ns564p620 481101967 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 246876258) qz373 0 2 Ns564p619 Ns564p170 Ns564p620 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 246876258) qz374 0 2 Ns564p621 Ns564p173 Ns564p620 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p623 := Ns564p544 246741 BSN.abs_quadSignPos qz625 (BSN.sfrac_eq_quadSignPos_mul Bool.false 519466592 536870912) BSN.abs_quadSignNeg qz599 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 481101967 536870912) qz83 rfl rfl (Ns564p614 rfl) (Ns564p584 rfl) RS565to576.d43 RS565to576.d45 RS565to576.d47 RS565to576.d49 RS565to576.d17 (Ns564p618 rfl rfl) (Ns564p622 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p624 := nat_lit 23862117255369949208208146523716156906836656370954633763168213890739623105 

noncomputable def Ns564p625 := nat_lit 9015029892324432893769201504619005551812919021360525848776031449535681 

noncomputable def Ns564p626 := nat_lit 62481425620428960749193328854915789699393069578846599956923494234352145601 

noncomputable def Ns564p627 := BSN.sin_dyadic_bound_f 555099577 536870912 3 2 536870912 268435456 Ns564p624 Ns564p143 Ns564p625 Ns564p626 Ns564p146 Ns564p625 461348012 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 555099577) qz375 0 2 Ns564p624 Ns564p143 Ns564p625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 555099577) qz376 0 2 Ns564p626 Ns564p146 Ns564p625 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p628 := Ns564p542 Bool.true 57856706 246741 Bool.true 555099577 28296951008113761 1 Bool.false 461348012 Bool.false Bool.false 75322997 263063 BSN.abs_quadSignPos qz377 (BSN.sfrac_eq_quadSignPos_mul Bool.false 461348012 536870912) qz83 rfl (Ns564p623 rfl) (Ns564p584 rfl) RS565to576.d51 RS565to576.d53 RS565to576.d17 (Ns564p627 rfl rfl) rfl 

noncomputable def Ns564p629 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) 75322997 536870912 263063 536870912 75322997 536870912 263063 536870912 80877452187926528 75322997 268435456 263063 268435456 (Ns564p628 rfl rfl rfl rfl) 

noncomputable def Ns564p630 := @Enclosure.Real.IsNear.mulLit_ff qz633 (Zeta.RiemannSiegel.correction qz82) 19071013 67108864 1 67108864 916896816629335 2251799813685248 15784598644469 1407374883553280000 17486151109596663966355 151115727451828646838272 

noncomputable abbrev qz637 := (@HPow.hPow Real Real Real qz7 qz81 qz9)

noncomputable def Ns564p631 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz637 1 1 0 1 19071013 67108864 1 67108864 19071013 67108864 1 67108864 

noncomputable def Ns564p632 := @Enclosure.Real.IsNear.sqrt_image qz81 2057947944053 13421772800 192679 13421772800 415491479 415491519 33554432 (@Enclosure.Real.IsNear.of_eq qz81 (@HMul.hMul Real Real Real qz5 qz80 qz3) Bool.false 2057947944053 13421772800 192679 13421772800 (BSN.t_div_two_pi_mk qz80 963395 1000 qz83) (@Enclosure.Real.IsNear.mulLit_ff qz80 qz3 963395 1000 0 1 10680707 67108864 1 67108864 2057947944053 13421772800 192679 13421772800 (Enclosure.Real.IsNear.const Bool.false 963395 1000) RS565to576.d56 rfl)) 

noncomputable abbrev qz761 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 963395 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz638 := qz761

noncomputable abbrev qz430 := qz638

noncomputable abbrev qz89 := qz430

noncomputable def Ns564p633 := @Enclosure.Real.IsNear.sqrt_image qz89 415491499 33554432 5 8388608 118074470 118074477 33554432 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 830982998 67108864 40 67108864 415491499 33554432 5 8388608 (Ns564p632 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns564p634 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz89) 236148947 67108864 7 67108864 9535506 9535507 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz89) Bool.false 236148947 67108864 7 67108864 236148947 67108864 7 67108864 (Ns564p633 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns564p635 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 19071013 67108864 1 67108864 19071013 67108864 1 67108864 (Ns564p634 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz431 := (@HMul.hMul Real Real Real qz588 qz586 qz632)

noncomputable abbrev qz90 := (Real.cos qz431)

noncomputable abbrev qz639 := (@HMul.hMul Real Real Real qz741 qz760 qz760)

noncomputable abbrev qz432 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz639 qz632) qz604)

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz432))

noncomputable def Ns564p636 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz82) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz90) qz91) Bool.false 916896816629335 

noncomputable def Ns564p637 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz90) qz91 90675055 67108864 473 

noncomputable abbrev qz92 := (@Neg.neg Real Real.instNeg (Real.cos qz431))

noncomputable def Ns564p638 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz90) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz92)) Bool.true 90675055 67108864 473 67108864 (BSN.inv_eq_neg_inv_neg qz90) 

noncomputable def Ns564p639 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz92) Bool.false 90675055 67108864 473 67108864 90675055 67108864 

noncomputable def Ns564p640 := @Enclosure.Real.IsNear.recentre' qz90 Bool.true 49667460 67108864 661897216 171798691840000 12416865 16777216 40399 10485760000 

noncomputable abbrev qz93 := qz431

noncomputable def Ns564p641 := @Enclosure.Real.IsNear.cos_image qz93 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10083189) qz605) Bool.false 10083189 4194304 63 16777216 Bool.true 49667460 67108864 1 

noncomputable def Ns564p642 := nat_lit 26986075414558059761243591 

noncomputable def Ns564p643 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz82 884279719003555 140737488355328 1 500000000000000 12838315 33554432 5 8388608 11352661580679125209825 4722366482869645213696 Ns564p642 

noncomputable def Ns564p644 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz1 415491499 33554432 5 8388608 12 1 0 1 12838315 12838315 33554432 5 

noncomputable def Ns564p645 := @Ns564p644 8388608 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 830982998 67108864 40 67108864 415491499 33554432 5 8388608 (Ns564p632 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns564p646 := @Enclosure.Real.IsNear.recentre' qz93 Bool.false 11352661580679125209825 4722366482869645213696 Ns564p642 Ns564p506 10083189 4194304 63 16777216 (@Ns564p643 Ns564p506 RS565to576.d55 (Ns564p645 rfl rfl) rfl) 

noncomputable def Ns564p647 := nat_lit 185598847971964350425464709818128317793916654732060556891617749581924228919739116173365410625 

noncomputable def Ns564p648 := nat_lit 29578069696252440059191913957394033708181635909166026599657522227391423716729083195620161 

noncomputable def Ns564p649 := nat_lit 486044332575636509068502214996309813405682754030591380196885136726195299151394409557449833281 

noncomputable def Ns564p650 := BSN.sin_dyadic_bound_f 114517333879 137438953472 3 2 67108864 20500001 Ns564p647 Ns564p207 Ns564p648 Ns564p649 Ns564p210 Ns564p648 49667460 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 114517333879) qz371 0 2 Ns564p647 Ns564p207 Ns564p648 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 114517333879) qz372 0 2 Ns564p649 Ns564p210 Ns564p648 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p651 := @Ns564p641 10240000 (Ns564p646 rfl) (Enclosure.sfrac_false_div 10083189 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10083189) qz605) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 503652560730316485951488) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 49667460 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 10083189 4194304 226375608064910080 72057594037927936 0 503652560730316485951488 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 49667460 67108864 503652560730316485951488 604462909807314587353088 114517333879 137438953472 20500001 20480000 (Ns564p650 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p652 := @Enclosure.Real.IsNear.inv_image qz92 12416865 16777216 40399 10485760000 45337291 45337764 33554432 (@Enclosure.Real.IsNear.neg qz90 Bool.true 12416865 16777216 40399 10485760000 (Ns564p640 (Ns564p651 rfl rfl) rfl)) 

noncomputable def Ns564p653 := Ns564p638 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz92) Bool.false 90675055 67108864 473 67108864 (@Ns564p639 473 67108864 (Ns564p652 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p654 := @Enclosure.Real.IsNear.recentre' qz91 Bool.true 10111897 33554432 

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz355 qz352 qz432)

noncomputable def Ns564p655 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 125957491)) qz396) Bool.true 125957491 67108864 

noncomputable def Ns564p656 := nat_lit 297408718894811466186351845045 

noncomputable def Ns564p657 := nat_lit 3996036113889308772403804647787391 

noncomputable def Ns564p658 := @Enclosure.Real.IsNear.recentre' qz94 Bool.true Ns564p656 Ns564p218 Ns564p657 

noncomputable def Ns564p659 := nat_lit 604462909807314587353088000000000000000 

noncomputable abbrev qz95 := qz432

noncomputable def Ns564p660 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz95 884279719003555 140737488355328 1 500000000000000 336328779800519 

noncomputable abbrev qz433 := (@HSub.hSub Real Real Real qz592 qz639 qz632)

noncomputable abbrev qz96 := qz433

noncomputable def Ns564p661 := @Enclosure.Real.IsNear.subLit_tf qz96 qz31 265960035622855 1125899906842624 148077705 140737488355328 1 16 

noncomputable abbrev qz434 := qz639

noncomputable abbrev qz97 := qz434

noncomputable def Ns564p662 := @Enclosure.Real.IsNear.subLit_ff_n qz97 qz82 164822332039225 1125899906842624 64191625 140737488355328 12838315 33554432 5 8388608 

noncomputable def Ns564p663 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz82 12838315 33554432 5 8388608 12838315 33554432 5 8388608 164822332039225 1125899906842624 

noncomputable def Ns564p664 := nat_lit 2081902981539827900425973508015604013776776288033263357751183756896474547294426851656793331794244208561 

noncomputable def Ns564p665 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600 

noncomputable def Ns564p666 := nat_lit 15947331199145349711029195335135189943315940816920576843750232568359186962689352858184913234626481 

noncomputable def Ns564p667 := nat_lit 12568387742972223804557046168497970746939558353858927744623562210232738238065700824706868152307446646705 

noncomputable def Ns564p668 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600 

noncomputable def Ns564p669 := BSN.cos_dyadic_bound_t 125957491 67108864 4 3 33554432 10240000 Ns564p664 Ns564p665 Ns564p666 Ns564p667 Ns564p668 Ns564p666 10111897 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 125957491) (BSN.cosEvenQ 67108864) 0 3 Ns564p664 Ns564p665 Ns564p666 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 125957491) (BSN.cosOddQ 67108864) 0 3 Ns564p667 Ns564p668 Ns564p666 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p670 := @Ns564p654 4623908864 687194767360000 10111897 33554432 282221 41943040000 (@Ns564p655 445 67108864 Bool.true 10111897 33554432 1 10240000 (@Ns564p658 Ns564p659 125957491 67108864 445 67108864 (@Ns564p660 1125899906842624 148077705 140737488355328 Ns564p656 Ns564p218 Ns564p657 Ns564p659 RS565to576.d55 (@Ns564p661 0 1 5381260476808304 336328779800519 1125899906842624 148077705 140737488355328 (@Ns564p662 8924137930024665743360 265960035622855 1125899906842624 148077705 140737488355328 (@Ns564p663 64191625 140737488355328 (Ns564p645 rfl rfl) (Ns564p645 rfl rfl) rfl) (Ns564p645 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 125957491 67108864) (BSN.cos_neg_of_bound 125957491 67108864 Bool.true 10111897 33554432 1 10240000 (Ns564p669 rfl rfl)) rfl rfl) 

noncomputable def Ns564p671 := @Ns564p630 301601362243442655941 Ns564p539 (Ns564p631 qz33 (@Enclosure.Real.IsNear.of_eq qz637 (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 19071013 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz81 (BSN.t_div_two_pi_nonneg qz80 963395 1000 qz83)) Ns564p635) rfl) (@Ns564p636 2251799813685248 15784598644469 1407374883553280000 (BSN.correction_mk qz82 (BSN.cos_two_pi_p_ne_zero_mk qz80 963395 1000 12 qz83 rfl rfl (@BSN.floor_sqrt_eq_dec qz80 963395 1000 12 qz83 rfl rfl rfl))) (@Ns564p637 67108864 10111897 33554432 282221 41943040000 916896816629335 2251799813685248 15784598644469 1407374883553280000 Ns564p653 (Ns564p670 rfl) rfl)) 

noncomputable def Ns564p672 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (hardyZApproximantRS₀ qz80) Bool.false 24916926543106959545709 151115727451828646838272 92858666110287566815941 Ns564p539 (@Eq.refl Real (hardyZApproximantRS₀ qz80)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HMul.hMul Real Real Real qz5 qz633 (Zeta.RiemannSiegel.correction qz82))) Bool.false 24916926543106959545709 151115727451828646838272 92858666110287566815941 Ns564p539 (BSN.hardyZApproximantRS₀_eq qz80 12 (@BSN.floor_sqrt_eq_dec qz80 963395 1000 12 qz83 rfl rfl rfl)) (@Ns564p541 24916926543106959545709 151115727451828646838272 92858666110287566815941 Ns564p539 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12)) Bool.false 75322997 268435456 263063 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (Ns564p629 (Ns564p628 rfl rfl rfl rfl) rfl rfl)) (Ns564p671 rfl) rfl rfl)) 

theorem RS565to576.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz80) Bool.false 24916926543106959545709 151115727451828646838272 92858666110287566815941 Ns564p539 := Ns564p672 

noncomputable def Ns564p673 := nat_lit 11805916207174113034240000 

noncomputable def Ns564p674 := nat_lit 5585450853989506184392562704384 

noncomputable abbrev qz762 := (Enclosure.sfrac Bool.false 964019 1000)

noncomputable abbrev qz640 := qz762

noncomputable abbrev qz435 := qz640

noncomputable abbrev qz98 := qz435

noncomputable abbrev qz763 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 964019 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz641 := qz763

noncomputable abbrev qz436 := qz641

noncomputable abbrev qz99 := qz436

noncomputable abbrev qz764 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 964019 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz642 := qz764

noncomputable abbrev qz437 := qz642

noncomputable abbrev qz100 := qz437

noncomputable abbrev qz643 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz99 qz9))

noncomputable def Ns564p675 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HMul.hMul Real Real Real qz5 qz643 (Zeta.RiemannSiegel.correction qz100)) 264762063 268435456 263231 268435456 2176451999705361116557 18889465931478580854784 37032836391750866963 Ns564p673 Ns564p674 

noncomputable def Ns564p676 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin BSN.quadSignPos 11 12 964019 1000 287 536870912 268435456 9007199254740992 Bool.false 1043496877817 4486 1334074092 54 154981288 8 

noncomputable def Ns564p677 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 964019 1000 175 234 536870912 268435456 9007199254740992 Bool.false 1043496877817 4486 

noncomputable def Ns564p678 := Ns564p677 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.true 403488592 211950 Bool.true 634591501 Bool.true 207157678 28296951008113761 1 Bool.false 496805917 Bool.false Bool.false 497397285 Bool.true Bool.true 396355679 

noncomputable def Ns564p679 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 964019 1000 38 111 536870912 268435456 9007199254740992 Bool.false 1043496877817 4486 

noncomputable def Ns564p680 := Ns564p679 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 372194552 173092 Bool.true 679944740 Bool.true 76999872 28296951008113761 1 Bool.false 160860450 Bool.true Bool.false 76736158 Bool.false Bool.true 403488592 

noncomputable def Ns564p681 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 964019 1000 137 43 536870912 268435456 9007199254740992 Bool.false 1043496877817 4486 

noncomputable def Ns564p682 := Ns564p681 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.true 215386432 128617 Bool.false 630899732 Bool.false 121240113 28296951008113761 1 Bool.false 495394789 Bool.true Bool.false 120212237 Bool.false Bool.true 372194552 

noncomputable def Ns564p683 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 964019 1000 386 249 536870912 268435456 9007199254740992 Bool.false 1043496877817 4486 

noncomputable def Ns564p684 := Ns564p683 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 149599244 75951 Bool.false 495497978 Bool.false 540851217 28296951008113761 1 Bool.false 323991362 Bool.true Bool.false 453899427 Bool.true Bool.true 215386432 

noncomputable def Ns564p685 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 964019 1000 811 563 536870912 268435456 9007199254740992 Bool.false 1043496877817 4486 

noncomputable def Ns564p686 := Ns564p685 372130544 53 379625064 8 589812976 53 309962568 8 Bool.true 298400200 4541 Bool.false 827614272 Bool.false 119698278 28296951008113761 1 Bool.false 536641349 Bool.false Bool.false 118709057 Bool.false Bool.false 149599244 

noncomputable def Ns564p687 := nat_lit 252928324386470738251042398896070645485114794104126096664373 

noncomputable def Ns564p688 := nat_lit 130129627668805928208485119205666520594748146645467136000 

noncomputable def Ns564p689 := nat_lit 399640506910970468310512190127520000 

noncomputable def Ns564p690 := nat_lit 2311566541180914814796756204019106217280 

noncomputable abbrev qz644 := (@Eq.refl Real qz762)

noncomputable abbrev qz438 := qz644

noncomputable abbrev qz101 := qz438

noncomputable def Ns564p691 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz98 964019 1000 3717331529444 16000000 1928038 4000 2000 Ns564p689 Ns564p690 qz101 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns564p692 := nat_lit 80937063803670636240333567646742606555236734113320350932599360 

noncomputable abbrev qz645 := (@HSub.hSub Real Real Real qz745 qz746 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz747 (@Nat.cast Real Real.instNatCast 1928038))))

noncomputable abbrev qz439 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 964019 4000) (Real.log (Enclosure.sfrac Bool.false 3717331529444 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz645))

noncomputable abbrev qz646 := (Enclosure.sfrac Bool.false 964019 2000)

noncomputable abbrev qz102 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz439 qz646) (@HMul.hMul Real Real Real qz355 qz646 (Real.log Real.pi)))

noncomputable def Ns564p693 := @Enclosure.Real.IsNear.addLit_ft_p qz102 (Enclosure.sfrac Bool.true Ns564p689 Ns564p690) 35013948143411652852037 18014398509481984000 136859592568072133 16384000000000000000000 Ns564p689 Ns564p690 0 1 Ns564p692 

noncomputable def Ns564p694 := nat_lit 2349746284059265107262563155968000 

noncomputable abbrev qz103 := (@HSub.hSub Real Real Real qz359 qz439 qz646)

noncomputable def Ns564p695 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (@HMul.hMul Real Real Real qz5 qz646 (Real.log Real.pi)) 44953765027950098774341 18014398509481984000 47461930789667 16000000000000000000 37028703408459 67108864000 2892057 536870912000 Ns564p694 35013948143411652852037 18014398509481984000 

noncomputable def Ns564p696 := nat_lit 89907530055900197548682000 

noncomputable abbrev qz104 := qz439

noncomputable def Ns564p697 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz646 53636876246306255141189 18014398509481984000 47461930789667 16000000000000000000 964019 2000 0 1 Ns564p696 44953765027950098774341 18014398509481984000 47461930789667 16000000000000000000 

noncomputable def Ns564p698 := nat_lit 120779507938091129441688547520646479872 

noncomputable def Ns564p699 := nat_lit 119499202259046359564812288 

noncomputable def Ns564p700 := nat_lit 102332864249902113871058900490962798544671625376702138296289159549629102362416445371937587871983064251913435470509960577781146395898963201812057059750570306346569341734164416371779174400 

noncomputable def Ns564p701 := nat_lit 2779153546343579106619908712515746309458821237389928654496721758355650236428773534046828495252580770075661251757917120197130498249452787050567367031730241375178265642907332820745584640 

noncomputable def Ns564p702 := nat_lit 116051782489361465617009032710350680926527004668388847259053060703250351212180106165021590707288661344510195781893261135141513303633901827999501450764873814116622590188411944960 

noncomputable def Ns564p703 := BSN.log_dyadic_bound 1620179529444 5814483529444 8 7 Ns564p700 268435456 81920000 Ns564p701 Ns564p702 153659393 7434663058888 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1620179529444) (BSN.artanhQ 5814483529444) 0 7 Ns564p701 Ns564p700 Ns564p702 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz440 := (Real.log (Enclosure.sfrac Bool.false 3717331529444 16000000))

noncomputable def Ns564p704 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 964019 4000) qz440 964019 4000 0 1 55646152356195431 4503599627370496 48828193 4000000000000000 53643948148267163197189 18014398509481984000 47071305787667 16000000000000000000 (Enclosure.Real.IsNear.const Bool.false 964019 4000) (BSN.isNear_log_sfrac 3717331529444 16000000 55646152356195431 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3717331529444) qz362)) Bool.false Ns564p699 Ns564p112 1000001392640000 81920000000000000000000 55646152356195431 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3717331529444 16000000 17 7434663058888 4194304000000 153659393 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns564p703 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p705 := BSN.arctan_dyadic_bound_f 1000 1928038 1 0 33554432 10240000 0 1 1 0 1 1 17403 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1928038) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1928038) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns564p706 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1928038))) 884279719003555 562949953421312 1 2000000000000000 17403 33554432 1 10240000 29661706682244502913024 883987745113507 562949953421312 195312501 2000000000000000 qz17 (Ns564p705 rfl) rfl rfl 

noncomputable abbrev qz441 := (@HMul.hMul Real Real Real qz588 qz593 qz645)

noncomputable abbrev qz105 := qz441

noncomputable abbrev qz442 := qz645

noncomputable abbrev qz106 := qz442

noncomputable def Ns564p707 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 964019 4000) qz440) qz105 53643948148267163197189 18014398509481984000 47071305787667 16000000000000000000 883987745113507 2251799813685248 195312501 8000000000000000 Ns564p698 53636876246306255141189 18014398509481984000 47461930789667 16000000000000000000 (Ns564p704 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz106 1 4 0 1 883987745113507 562949953421312 195312501 2000000000000000 883987745113507 2251799813685248 195312501 8000000000000000 qz369 Ns564p706 rfl) 

noncomputable def Ns564p708 := @Ns564p693 Ns564p687 Ns564p688 136859592568072133 16384000000000000000000 (@Ns564p695 136859592568072133 16384000000000000000000 (Ns564p697 (Ns564p707 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 964019 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz646 (Real.log Real.pi) 964019 2000 0 1 38410761 33554432 3 268435456 37028703408459 67108864000 2892057 536870912000 (Enclosure.Real.IsNear.const Bool.false 964019 2000) RS565to576.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns564p689 Ns564p690) 

noncomputable def Ns564p709 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns564p687 Ns564p688 136859592568072133 16384000000000000000000 130437109727 67108864 561 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz370 qz102 (Enclosure.sfrac Bool.true Ns564p689 Ns564p690)) Bool.false Ns564p687 Ns564p688 136859592568072133 16384000000000000000000 Ns564p691 (Ns564p708 rfl rfl)) 

noncomputable def Ns564p710 := nat_lit 5699760825051810317205504 

noncomputable def Ns564p711 := nat_lit 46445730272820095970867805882200293364186800812257802011432733957205144687068024435548160000 

noncomputable def Ns564p712 := nat_lit 1852740743661931159342976258048206502319063979485154539064361527728018319906655699009536 

noncomputable def Ns564p713 := nat_lit 121640579610467655844681507729916309333771199833279838827355818064492390722184024650542022656 

noncomputable def Ns564p714 := BSN.sin_dyadic_bound_f 80998472996 137438953472 3 2 67108864 20500001 Ns564p711 Ns564p207 Ns564p712 Ns564p713 Ns564p210 Ns564p712 37300025 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 80998472996) qz371 0 2 Ns564p711 Ns564p207 Ns564p712 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 80998472996) qz372 0 2 Ns564p713 Ns564p210 Ns564p712 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p715 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz98) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 130437109727) qz396) Bool.false 130437109727 67108864 561 67108864 Bool.true 37300025 67108864 1 10240000 (Ns564p709 rfl) (Enclosure.sfrac_false_div 130437109727 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 130437109727) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p710) qz397) 226375608064910080 72057594037927936 Bool.false 37300025 67108864 309 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 130437109727 67108864 226375608064910080 72057594037927936 309 Ns564p710 Ns564p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 37300025 67108864 Ns564p710 Ns564p112 80998472996 137438953472 20500001 20480000 (Ns564p714 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p716 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns564p687 Ns564p688 136859592568072133 16384000000000000000000 1043496877817 536870912 4486 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz370 qz102 (Enclosure.sfrac Bool.true Ns564p689 Ns564p690)) Bool.false Ns564p687 Ns564p688 136859592568072133 16384000000000000000000 Ns564p691 (Ns564p708 rfl rfl)) 

noncomputable def Ns564p717 := Ns564p686 75951 BSN.abs_quadSignPos (BSN.cos_quad_nat3 811 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536641349 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 563 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 118709057 536870912) qz101 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) Bool.true 37300025 67108864 354721 41943040000 298400200 536870912 4541 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 37300025 67108864 354721 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz98) qz98) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 37300025 67108864 5811748864 687194767360000 37300025 67108864 354721 41943040000 (Ns564p715 rfl rfl) rfl)) rfl) (Ns564p716 rfl) RS565to576.d7 

noncomputable def Ns564p718 := nat_lit 168337349996668200410502680293682340131723775936718263925401650992237954567153222100012814538411708627610203324416 

noncomputable def Ns564p719 := nat_lit 103260840639809150106390285543960340196051535514988887844804818365670368170370003373401081204412472377737216 

noncomputable def Ns564p720 := nat_lit 840716481997653663850059262268604478956838724759328982394003716700124952032682458178869043771789703288669262053376 

noncomputable def Ns564p721 := BSN.sin_dyadic_bound_f 827614272 536870912 4 3 536870912 268435456 Ns564p718 Ns564p181 Ns564p719 Ns564p720 Ns564p184 Ns564p719 536641349 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 827614272) qz375 0 3 Ns564p718 Ns564p181 Ns564p719 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 827614272) qz376 0 3 Ns564p720 Ns564p184 Ns564p719 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p722 := nat_lit 205282349884513467316472726800656 

noncomputable def Ns564p723 := BSN.sin_dyadic_bound_f 119698278 536870912 2 1 536870912 268435456 Ns564p722 Ns564p463 Ns564p722 Ns564p722 Ns564p464 Ns564p722 118709057 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 119698278) qz375 0 1 Ns564p722 Ns564p463 Ns564p722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 119698278) qz376 0 1 Ns564p722 Ns564p464 Ns564p722 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p724 := nat_lit 8416738891000693561926739419458724015525767839634958029229848972120924416 

noncomputable def Ns564p725 := nat_lit 3633583063965419919401622629453057977105463154279287226234597818081536 

noncomputable def Ns564p726 := nat_lit 25242949506874149845941415013117265930623092592596315513237077720726610176 

noncomputable def Ns564p727 := BSN.cos_dyadic_bound_f 495497978 536870912 3 2 536870912 268435456 Ns564p724 Ns564p170 Ns564p725 Ns564p726 Ns564p173 Ns564p725 323991362 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 495497978) qz373 0 2 Ns564p724 Ns564p170 Ns564p725 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 495497978) qz374 0 2 Ns564p726 Ns564p173 Ns564p725 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p728 := nat_lit 21504058175244284113121660545475304601973504009927144575933646063666297985 

noncomputable def Ns564p729 := nat_lit 7321878033419847850854342302848055289586969600276508104847324801498241 

noncomputable def Ns564p730 := nat_lit 56308297894538064352131537255373567582318893503789692876227891640875973761 

noncomputable def Ns564p731 := BSN.sin_dyadic_bound_f 540851217 536870912 3 2 536870912 268435456 Ns564p728 Ns564p143 Ns564p729 Ns564p730 Ns564p146 Ns564p729 453899427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 540851217) qz375 0 2 Ns564p728 Ns564p143 Ns564p729 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 540851217) qz376 0 2 Ns564p730 Ns564p146 Ns564p729 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p732 := Ns564p684 128617 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 386 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 323991362 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 249 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 453899427 536870912) qz101 rfl rfl (Ns564p717 RS565to576.d9 RS565to576.d11 RS565to576.d13 RS565to576.d17 (Ns564p721 rfl rfl) (Ns564p723 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns564p716 rfl) RS565to576.d19 RS565to576.d21 RS565to576.d23 RS565to576.d25 RS565to576.d17 (Ns564p727 rfl rfl) (Ns564p731 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns564p733 := nat_lit 56777107375168447612171899991260242425531936010789424845775623967783775240241637102439981840570767163681801240576 

noncomputable def Ns564p734 := nat_lit 3976711773437543888122441059608605028109528686257015196231923348306151422970525474095773765136509017522176 

noncomputable def Ns564p735 := nat_lit 283774918262162400883853410088041071795124241389846640733728413250362278725031839283408624179548303297552618356736 

noncomputable def Ns564p736 := BSN.sin_dyadic_bound_f 630899732 536870912 4 3 536870912 268435456 Ns564p733 Ns564p181 Ns564p734 Ns564p735 Ns564p184 Ns564p734 495394789 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 630899732) qz375 0 3 Ns564p733 Ns564p181 Ns564p734 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 630899732) qz376 0 3 Ns564p735 Ns564p184 Ns564p734 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p737 := nat_lit 216065451704655986475833892167361 

noncomputable def Ns564p738 := BSN.sin_dyadic_bound_f 121240113 536870912 2 1 536870912 268435456 Ns564p737 Ns564p463 Ns564p737 Ns564p737 Ns564p464 Ns564p737 120212237 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 121240113) qz375 0 1 Ns564p737 Ns564p463 Ns564p737 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 121240113) qz376 0 1 Ns564p737 Ns564p464 Ns564p737 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p739 := Ns564p682 173092 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 137 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 495394789 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 120212237 536870912) qz101 rfl rfl (Ns564p732 rfl rfl) (Ns564p716 rfl) RS565to576.d27 RS565to576.d29 RS565to576.d31 RS565to576.d33 RS565to576.d17 (Ns564p736 rfl rfl) (Ns564p738 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p740 := nat_lit 29487905764262129156122378818151764952738688256148088985665988104955033261485452689555122321941618093195264000000 

noncomputable def Ns564p741 := nat_lit 9765251245093288281523921155514184176830970240681126304386528873773106113033732291709822898176000000000000 

noncomputable def Ns564p742 := nat_lit 178710879539985458266506512703640221747848636099696983195362880290528351845205872782108863496294319509051801600000 

noncomputable def Ns564p743 := BSN.cos_dyadic_bound_f 679944740 536870912 4 3 536870912 268435456 Ns564p740 Ns564p133 Ns564p741 Ns564p742 Ns564p136 Ns564p741 160860450 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 679944740) qz373 0 3 Ns564p740 Ns564p133 Ns564p741 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 679944740) qz374 0 3 Ns564p742 Ns564p136 Ns564p741 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p744 := nat_lit 35152807255686843770077452435456 

noncomputable def Ns564p745 := BSN.sin_dyadic_bound_f 76999872 536870912 2 1 536870912 268435456 Ns564p744 Ns564p463 Ns564p744 Ns564p744 Ns564p464 Ns564p744 76736158 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 76999872) qz375 0 1 Ns564p744 Ns564p463 Ns564p744 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 76999872) qz376 0 1 Ns564p744 Ns564p464 Ns564p744 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p746 := Ns564p680 211950 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 160860450 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 111 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 76736158 536870912) qz101 rfl rfl (Ns564p739 rfl) (Ns564p716 rfl) RS565to576.d35 RS565to576.d37 RS565to576.d39 RS565to576.d41 RS565to576.d17 (Ns564p743 rfl rfl) (Ns564p745 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p747 := nat_lit 58118629001284778522249835708468284517881686899794859100998076123441567078638672255714247318639065166010331860401 

noncomputable def Ns564p748 := nat_lit 4265117658924449745612237054255611003592871537319442112162742159668416258063028297013061526967381183598001 

noncomputable def Ns564p749 := nat_lit 290477240331432431594078287610564697900885694273686193344987044105834668236954637097892307645123122607265792560561 

noncomputable def Ns564p750 := BSN.sin_dyadic_bound_f 634591501 536870912 4 3 536870912 268435456 Ns564p747 Ns564p181 Ns564p748 Ns564p749 Ns564p184 Ns564p748 496805917 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 634591501) qz375 0 3 Ns564p747 Ns564p181 Ns564p748 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 634591501) qz376 0 3 Ns564p749 Ns564p184 Ns564p748 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p751 := nat_lit 257038777512117266348364688110186228229161792561656628420358694464143616 

noncomputable def Ns564p752 := nat_lit 3391628495603598315768449307554865686462975158872665060277048852736 

noncomputable def Ns564p753 := nat_lit 771109549279360591848462527431943574956112451734652139930955529294725376 

noncomputable def Ns564p754 := BSN.cos_dyadic_bound_f 207157678 536870912 3 2 536870912 268435456 Ns564p751 Ns564p170 Ns564p752 Ns564p753 Ns564p173 Ns564p752 497397285 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 207157678) qz373 0 2 Ns564p751 Ns564p170 Ns564p752 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 207157678) qz374 0 2 Ns564p753 Ns564p173 Ns564p752 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p755 := Ns564p678 246898 BSN.abs_quadSignPos qz625 (BSN.sfrac_eq_quadSignPos_mul Bool.false 496805917 536870912) BSN.abs_quadSignNeg qz599 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 497397285 536870912) qz101 rfl rfl (Ns564p746 rfl) (Ns564p716 rfl) RS565to576.d43 RS565to576.d45 RS565to576.d47 RS565to576.d49 RS565to576.d17 (Ns564p750 rfl rfl) (Ns564p754 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p756 := nat_lit 22095403518457606096721320388562207101528041942209182817295783458619394145 

noncomputable def Ns564p757 := nat_lit 7729962416797435182442464172180417069704698421918986288465987528689761 

noncomputable def Ns564p758 := nat_lit 57856398799666534405879503694717488400174873670245705210355249840385296481 

noncomputable def Ns564p759 := BSN.sin_dyadic_bound_f 544530453 536870912 3 2 536870912 268435456 Ns564p756 Ns564p143 Ns564p757 Ns564p758 Ns564p146 Ns564p757 455853645 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 544530453) qz375 0 2 Ns564p756 Ns564p143 Ns564p757 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 544530453) qz376 0 2 Ns564p758 Ns564p146 Ns564p757 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p760 := Ns564p676 Bool.true 396355679 246898 Bool.true 544530453 28296951008113761 1 Bool.false 455853645 Bool.false Bool.true 264762063 263231 BSN.abs_quadSignPos qz377 (BSN.sfrac_eq_quadSignPos_mul Bool.false 455853645 536870912) qz101 rfl (Ns564p755 rfl) (Ns564p716 rfl) RS565to576.d51 RS565to576.d53 RS565to576.d17 (Ns564p759 rfl rfl) rfl 

noncomputable def Ns564p761 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) 264762063 536870912 263231 536870912 264762063 536870912 263231 536870912 284286100451622912 264762063 268435456 263231 268435456 (Ns564p760 rfl rfl rfl rfl) 

noncomputable def Ns564p762 := @Enclosure.Real.IsNear.mulLit_ff qz643 (Zeta.RiemannSiegel.correction qz100) 9533963 33554432 1 33554432 228284082884039 562949953421312 3869341109317 351843720888320000 2176451999705361116557 18889465931478580854784 

noncomputable abbrev qz647 := (@HPow.hPow Real Real Real qz7 qz99 qz9)

noncomputable def Ns564p763 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz647 1 1 0 1 9533963 33554432 1 33554432 9533963 33554432 1 33554432 

noncomputable def Ns564p764 := @Enclosure.Real.IsNear.sqrt_image qz99 10296404481433 67108864000 964019 67108864000 415626016 415626056 33554432 (@Enclosure.Real.IsNear.of_eq qz99 (@HMul.hMul Real Real Real qz5 qz98 qz3) Bool.false 10296404481433 67108864000 964019 67108864000 (BSN.t_div_two_pi_mk qz98 964019 1000 qz101) (@Enclosure.Real.IsNear.mulLit_ff qz98 qz3 964019 1000 0 1 10680707 67108864 1 67108864 10296404481433 67108864000 964019 67108864000 (Enclosure.Real.IsNear.const Bool.false 964019 1000) RS565to576.d56 rfl)) 

noncomputable abbrev qz765 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 964019 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz648 := qz765

noncomputable abbrev qz443 := qz648

noncomputable abbrev qz107 := qz443

noncomputable def Ns564p765 := @Enclosure.Real.IsNear.sqrt_image qz107 103906509 8388608 5 8388608 118093585 118093591 33554432 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 831252072 67108864 40 67108864 103906509 8388608 5 8388608 (Ns564p764 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns564p766 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 29523397 8388608 3 33554432 9533962 9533964 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 236187176 67108864 6 67108864 29523397 8388608 3 33554432 (Ns564p765 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns564p767 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 19067926 67108864 2 67108864 9533963 33554432 1 33554432 (Ns564p766 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz444 := (@HMul.hMul Real Real Real qz588 qz586 qz642)

noncomputable abbrev qz108 := (Real.cos qz444)

noncomputable abbrev qz649 := (@HMul.hMul Real Real Real qz741 qz764 qz764)

noncomputable abbrev qz445 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz649 qz642) qz604)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz445))

noncomputable def Ns564p768 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz100) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz108) qz109) Bool.false 228284082884039 

noncomputable def Ns564p769 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz108) qz109 22168391 16777216 113 

noncomputable abbrev qz110 := (@Neg.neg Real Real.instNeg (Real.cos qz444))

noncomputable def Ns564p770 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz108) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz110)) Bool.true 22168391 16777216 113 16777216 (BSN.inv_eq_neg_inv_neg qz108) 

noncomputable def Ns564p771 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz110) Bool.false 88673564 67108864 452 67108864 22168391 16777216 

noncomputable def Ns564p772 := @Enclosure.Real.IsNear.recentre' qz108 Bool.true 50788526 67108864 661897216 171798691840000 25394263 33554432 40399 10485760000 

noncomputable abbrev qz111 := qz444

noncomputable def Ns564p773 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 81510833) qz383) Bool.false 81510833 33554432 63 16777216 Bool.true 50788526 67108864 1 

noncomputable def Ns564p774 := nat_lit 134930377073079214813768931 

noncomputable def Ns564p775 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz100 884279719003555 140737488355328 1 500000000000000 3243213 8388608 5 8388608 2867907480308676622215 1180591620717411303424 Ns564p774 

noncomputable def Ns564p776 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz1 103906509 8388608 5 8388608 12 1 0 1 3243213 3243213 8388608 5 

noncomputable def Ns564p777 := @Ns564p776 8388608 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 831252072 67108864 40 67108864 103906509 8388608 5 8388608 (Ns564p764 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns564p778 := @Enclosure.Real.IsNear.recentre' qz111 Bool.false 2867907480308676622215 1180591620717411303424 Ns564p774 Ns564p201 81510833 33554432 63 16777216 (@Ns564p775 Ns564p201 RS565to576.d55 (Ns564p777 rfl rfl) rfl) 

noncomputable def Ns564p779 := nat_lit 4151044080742002449186816 

noncomputable def Ns564p780 := nat_lit 209088083273659754834110034017460336059605055732731756852385521241505834673168816995975330625 

noncomputable def Ns564p781 := nat_lit 37537065919259429663268685637142430357937760130266980924932688157586811487635108937890625 

noncomputable def Ns564p782 := nat_lit 547550872371906271203214320745174078126005151497896073787131236042164902639700254336893090625 

noncomputable def Ns564p783 := BSN.sin_dyadic_bound_f 117979768695 137438953472 3 2 67108864 20500001 Ns564p780 Ns564p207 Ns564p781 Ns564p782 Ns564p210 Ns564p781 50788526 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 117979768695) qz371 0 2 Ns564p780 Ns564p207 Ns564p781 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 117979768695) qz372 0 2 Ns564p782 Ns564p210 Ns564p781 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p784 := @Ns564p773 10240000 (Ns564p778 rfl) (Enclosure.sfrac_false_div 81510833 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 81510833) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p779) qz416) 226375608064910080 72057594037927936 Bool.false 50788526 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 81510833 33554432 226375608064910080 72057594037927936 0 Ns564p779 Ns564p435 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 50788526 67108864 Ns564p779 Ns564p435 117979768695 137438953472 20500001 20480000 (Ns564p783 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p785 := @Enclosure.Real.IsNear.inv_image qz110 25394263 33554432 40399 10485760000 44336556 44337008 33554432 (@Enclosure.Real.IsNear.neg qz108 Bool.true 25394263 33554432 40399 10485760000 (Ns564p772 (Ns564p784 rfl rfl) rfl)) 

noncomputable def Ns564p786 := Ns564p770 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz110) Bool.false 22168391 16777216 113 16777216 (@Ns564p771 113 16777216 (Ns564p785 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p787 := @Enclosure.Real.IsNear.recentre' qz109 Bool.true 10297729 33554432 

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz355 qz352 qz445)

noncomputable def Ns564p788 := @Enclosure.Real.IsNear.cos_image qz112 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31586909)) qz629) Bool.true 31586909 16777216 

noncomputable def Ns564p789 := nat_lit 18645620142646473703684924645 

noncomputable def Ns564p790 := nat_lit 9903520314283042199192993792 

noncomputable def Ns564p791 := nat_lit 2007094621013480071362709794221053 

noncomputable def Ns564p792 := @Enclosure.Real.IsNear.recentre' qz112 Bool.true Ns564p789 Ns564p790 Ns564p791 

noncomputable abbrev qz113 := qz445

noncomputable def Ns564p793 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz113 884279719003555 140737488355328 1 500000000000000 21085658465239 

noncomputable abbrev qz446 := (@HSub.hSub Real Real Real qz592 qz649 qz642)

noncomputable abbrev qz114 := qz446

noncomputable def Ns564p794 := @Enclosure.Real.IsNear.subLit_tf qz114 qz31 16687611954135 70368744177664 74375195 70368744177664 1 16 

noncomputable abbrev qz447 := qz649

noncomputable abbrev qz115 := qz447

noncomputable def Ns564p795 := @Enclosure.Real.IsNear.subLit_ff_n qz115 qz100 10518430563369 70368744177664 32432155 70368744177664 3243213 8388608 5 8388608 

noncomputable def Ns564p796 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz100 3243213 8388608 5 8388608 3243213 8388608 5 8388608 10518430563369 70368744177664 

noncomputable def Ns564p797 := nat_lit 125647192814338823297474711624337327751898425358814357475889468686884475385343704575516058997361 

noncomputable def Ns564p798 := nat_lit 986473789936250795632035605308151774123831797846996321522044505385816715415015682262061681 

noncomputable def Ns564p799 := nat_lit 758482288685587515887488887418064879384432410913736238831817482743450360075155586719237906780785 

noncomputable def Ns564p800 := BSN.cos_dyadic_bound_t 31586909 16777216 4 3 33554432 10240000 Ns564p797 Ns564p531 Ns564p798 Ns564p799 Ns564p534 Ns564p798 10297729 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 31586909) (BSN.cosEvenQ 16777216) 0 3 Ns564p797 Ns564p531 Ns564p798 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 31586909) (BSN.cosOddQ 16777216) 0 3 Ns564p799 Ns564p534 Ns564p798 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p801 := @Ns564p787 4644388864 687194767360000 10297729 33554432 283471 41943040000 (@Ns564p788 447 67108864 Bool.true 10297729 33554432 1 10240000 (@Ns564p792 Ns564p525 31586909 16777216 447 67108864 (@Ns564p793 70368744177664 74375195 70368744177664 Ns564p789 Ns564p790 Ns564p791 Ns564p525 RS565to576.d55 (@Ns564p794 0 1 337370535443824 21085658465239 70368744177664 74375195 70368744177664 (@Ns564p795 139985835139352494080 16687611954135 70368744177664 74375195 70368744177664 (@Ns564p796 32432155 70368744177664 (Ns564p777 rfl rfl) (Ns564p777 rfl rfl) rfl) (Ns564p777 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 31586909 16777216) (BSN.cos_neg_of_bound 31586909 16777216 Bool.true 10297729 33554432 1 10240000 (Ns564p800 rfl rfl)) rfl rfl) 

noncomputable def Ns564p802 := @Ns564p762 37032836391750866963 Ns564p673 (Ns564p763 qz33 (@Enclosure.Real.IsNear.of_eq qz647 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 9533963 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz99 (BSN.t_div_two_pi_nonneg qz98 964019 1000 qz101)) Ns564p767) rfl) (@Ns564p768 562949953421312 3869341109317 351843720888320000 (BSN.correction_mk qz100 (BSN.cos_two_pi_p_ne_zero_mk qz98 964019 1000 12 qz101 rfl rfl (@BSN.floor_sqrt_eq_dec qz98 964019 1000 12 qz101 rfl rfl rfl))) (@Ns564p769 16777216 10297729 33554432 283471 41943040000 228284082884039 562949953421312 3869341109317 351843720888320000 Ns564p786 (Ns564p801 rfl) rfl)) 

noncomputable def Ns564p803 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (hardyZApproximantRS₀ qz98) Bool.true 20807425878902920277389 18889465931478580854784 11614054648035921106963 Ns564p673 (@Eq.refl Real (hardyZApproximantRS₀ qz98)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HMul.hMul Real Real Real qz5 qz643 (Zeta.RiemannSiegel.correction qz100))) Bool.true 20807425878902920277389 18889465931478580854784 11614054648035921106963 Ns564p673 (BSN.hardyZApproximantRS₀_eq qz98 12 (@BSN.floor_sqrt_eq_dec qz98 964019 1000 12 qz101 rfl rfl rfl)) (@Ns564p675 20807425878902920277389 18889465931478580854784 11614054648035921106963 Ns564p673 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12)) Bool.true 264762063 268435456 263231 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (Ns564p761 (Ns564p760 rfl rfl rfl rfl) rfl rfl)) (Ns564p802 rfl) rfl rfl)) 

theorem RS565to576.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz98) Bool.true 20807425878902920277389 18889465931478580854784 11614054648035921106963 Ns564p673 := Ns564p803 

noncomputable def Ns564p804 := nat_lit 11713689545315266204076211175424 

noncomputable abbrev qz766 := (Enclosure.sfrac Bool.false 965657 1000)

noncomputable abbrev qz650 := qz766

noncomputable abbrev qz448 := qz650

noncomputable abbrev qz116 := qz448

noncomputable abbrev qz767 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 965657 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz651 := qz767

noncomputable abbrev qz449 := qz651

noncomputable abbrev qz117 := qz449

noncomputable abbrev qz768 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 965657 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz652 := qz768

noncomputable abbrev qz450 := qz652

noncomputable abbrev qz118 := qz450

noncomputable abbrev qz653 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz117 qz9))

noncomputable def Ns564p805 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HMul.hMul Real Real Real qz5 qz653 (Zeta.RiemannSiegel.correction qz118)) 85165767 67108864 263683 268435456 17228682173530400640925 151115727451828646838272 282294295615613009091 Ns564p539 Ns564p804 

noncomputable def Ns564p806 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin BSN.quadSignPos 11 12 965657 1000 287 536870912 268435456 9007199254740992 Bool.false 1045710350069 4493 1334074092 54 154981288 8 

noncomputable def Ns564p807 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 965657 1000 175 234 536870912 268435456 9007199254740992 Bool.false 1045710350069 4493 

noncomputable def Ns564p808 := Ns564p807 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.false 247131201 212316 Bool.true 446000035 Bool.true 102381466 28296951008113761 1 Bool.false 396441825 Bool.false Bool.false 527138370 Bool.true Bool.false 213558926 

noncomputable def Ns564p809 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 965657 1000 38 110 536870912 268435456 9007199254740992 Bool.false 1045710350069 4493 

noncomputable def Ns564p810 := Ns564p809 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.false 475431312 173392 Bool.true 295122053 Bool.true 639069780 28296951008113761 1 Bool.false 457777633 Bool.true Bool.false 199353819 Bool.true Bool.false 247131201 

noncomputable def Ns564p811 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 965657 1000 138 43 536870912 268435456 9007199254740992 Bool.false 1045710350069 4493 

noncomputable def Ns564p812 := Ns564p811 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.false 443185919 128842 Bool.false 425393621 Bool.false 623489603 28296951008113761 1 Bool.false 376974003 Bool.true Bool.false 492491742 Bool.false Bool.false 475431312 

noncomputable def Ns564p813 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 965657 1000 387 250 536870912 268435456 9007199254740992 Bool.false 1045710350069 4493 

noncomputable def Ns564p814 := Ns564p813 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 337406526 76088 Bool.false 646555685 Bool.false 495677703 28296951008113761 1 Bool.false 501217297 Bool.false Bool.false 323848035 Bool.true Bool.false 443185919 

noncomputable def Ns564p815 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 965657 1000 813 564 536870912 268435456 9007199254740992 Bool.false 1045710350069 4493 

noncomputable def Ns564p816 := Ns564p815 372130544 53 379625064 8 589812976 53 309962568 8 Bool.false 536870904 4557 Bool.false 744906980 Bool.false 523742019 28296951008113761 1 Bool.false 527877105 Bool.true Bool.false 301032342 Bool.false Bool.false 337406526 

noncomputable def Ns564p817 := nat_lit 51211973331055236334549107201148265815769459845069345631323 

noncomputable def Ns564p818 := nat_lit 26292384717954363247992972868984673708074412706417868800 

noncomputable def Ns564p819 := nat_lit 403047282614608219609207145627360000 

noncomputable def Ns564p820 := nat_lit 2335232870894042922315578613722013453120 

noncomputable abbrev qz654 := (@Eq.refl Real qz766)

noncomputable abbrev qz451 := qz654

noncomputable abbrev qz119 := qz451

noncomputable def Ns564p821 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz116 965657 1000 3729974766596 16000000 1931314 4000 2000 Ns564p819 Ns564p820 qz119 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns564p822 := nat_lit 16387831465937675627055714304367445061046227150422190602023360 

noncomputable abbrev qz655 := (@HSub.hSub Real Real Real qz745 qz746 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz747 (@Nat.cast Real Real.instNatCast 1931314))))

noncomputable abbrev qz452 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 965657 4000) (Real.log (Enclosure.sfrac Bool.false 3729974766596 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz655))

noncomputable abbrev qz656 := (Enclosure.sfrac Bool.false 965657 2000)

noncomputable abbrev qz120 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz452 qz656) (@HMul.hMul Real Real Real qz355 qz656 (Real.log Real.pi)))

noncomputable def Ns564p823 := @Enclosure.Real.IsNear.addLit_ft_p qz120 (Enclosure.sfrac Bool.true Ns564p819 Ns564p820) 7017643988453483067203 3602879701896396800 137091456061035599 16384000000000000000000 Ns564p819 Ns564p820 0 1 Ns564p822 

noncomputable def Ns564p824 := nat_lit 2354730580107711827416144936960000 

noncomputable abbrev qz121 := (@HSub.hSub Real Real Real qz359 qz452 qz656)

noncomputable def Ns564p825 := @Enclosure.Real.IsNear.subLit_ff_p qz121 (@HMul.hMul Real Real Real qz5 qz656 (Real.log Real.pi)) 45044925933822293480527 18014398509481984000 47541911369801 16000000000000000000 37091620234977 67108864000 2896971 536870912000 Ns564p824 7017643988453483067203 3602879701896396800 

noncomputable def Ns564p826 := nat_lit 90089851867644586961054000 

noncomputable abbrev qz122 := qz452

noncomputable def Ns564p827 := @Enclosure.Real.IsNear.subLit_ff_p qz122 qz656 53742790944557715592271 18014398509481984000 47541911369801 16000000000000000000 965657 2000 0 1 Ns564p826 45044925933822293480527 18014398509481984000 47541911369801 16000000000000000000 

noncomputable def Ns564p828 := nat_lit 121018006635880297347559307539495518208 

noncomputable def Ns564p829 := nat_lit 119532040417858918121734144 

noncomputable def Ns564p830 := nat_lit 105492511082052207533423472653973898032221397931365952427740830253483345659334850152383100844463651406050601237378895416171804164178805045027943568551629142228967509876062147186157158400 

noncomputable def Ns564p831 := nat_lit 2898864997995294775339164232770971838379565929100362303853428836623565177212672109127879961609066328925958386169202112192671119373408047568178178993146361356617907732858293932041175040 

noncomputable def Ns564p832 := nat_lit 129394109528115589128315196584626221915686468506989333838914005552377283275538097939009338079084792589357558686643008027034559328318201370075733805416342804417185226957583810560 

noncomputable def Ns564p833 := BSN.log_dyadic_bound 1632822766596 5827126766596 8 7 Ns564p830 268435456 81920000 Ns564p831 Ns564p832 154570835 7459949533192 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1632822766596) (BSN.artanhQ 5827126766596) 0 7 Ns564p831 Ns564p830 Ns564p832 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz453 := (Real.log (Enclosure.sfrac Bool.false 3729974766596 16000000))

noncomputable def Ns564p834 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 965657 4000) qz453 965657 4000 0 1 55661443815500903 4503599627370496 48828193 4000000000000000 53749862850545155488271 18014398509481984000 47151286367801 16000000000000000000 (Enclosure.Real.IsNear.const Bool.false 965657 4000) (BSN.isNear_log_sfrac 3729974766596 16000000 55661443815500903 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3729974766596) qz362)) Bool.false Ns564p829 Ns564p112 1000001392640000 81920000000000000000000 55661443815500903 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3729974766596 16000000 17 7459949533192 4194304000000 154570835 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns564p833 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p835 := BSN.arctan_dyadic_bound_f 1000 1931314 1 0 33554432 10240000 0 1 1 0 1 1 17373 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1931314) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1931314) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns564p836 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1931314))) 884279719003555 562949953421312 1 2000000000000000 17373 33554432 1 10240000 29661723570743105552384 883988248429987 562949953421312 195312501 2000000000000000 qz17 (Ns564p835 rfl) rfl rfl 

noncomputable abbrev qz454 := (@HMul.hMul Real Real Real qz588 qz593 qz655)

noncomputable abbrev qz123 := qz454

noncomputable abbrev qz455 := qz655

noncomputable abbrev qz124 := qz455

noncomputable def Ns564p837 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 965657 4000) qz453) qz123 53749862850545155488271 18014398509481984000 47151286367801 16000000000000000000 883988248429987 2251799813685248 195312501 8000000000000000 Ns564p828 53742790944557715592271 18014398509481984000 47541911369801 16000000000000000000 (Ns564p834 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz124 1 4 0 1 883988248429987 562949953421312 195312501 2000000000000000 883988248429987 2251799813685248 195312501 8000000000000000 qz369 Ns564p836 rfl) 

noncomputable def Ns564p838 := @Ns564p823 Ns564p817 Ns564p818 137091456061035599 16384000000000000000000 (@Ns564p825 137091456061035599 16384000000000000000000 (Ns564p827 (Ns564p837 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 965657 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz656 (Real.log Real.pi) 965657 2000 0 1 38410761 33554432 3 268435456 37091620234977 67108864000 2896971 536870912000 (Enclosure.Real.IsNear.const Bool.false 965657 2000) RS565to576.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns564p819 Ns564p820) 

noncomputable def Ns564p839 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns564p817 Ns564p818 137091456061035599 16384000000000000000000 65356896879 33554432 563 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz370 qz120 (Enclosure.sfrac Bool.true Ns564p819 Ns564p820)) Bool.false Ns564p817 Ns564p818 137091456061035599 16384000000000000000000 Ns564p821 (Ns564p838 rfl rfl)) 

noncomputable def Ns564p840 := nat_lit 7595256100556019647643648 

noncomputable def Ns564p841 := nat_lit 14375459380617276783067999320723847549033948406004349913575402104697747662937310939880617792770901131531108393088281595304321572189588516239921 

noncomputable def Ns564p842 := nat_lit 10240270005084961835472551293299627701014047729757951447326297090077388121282390183092815671484391802577351834239220630971900268893174321 

noncomputable def Ns564p843 := nat_lit 71788010958787289872893437927735684934632732324861884587959244344064797425986429362320251772489103535821081240957317655525676237541448141240881 

noncomputable def Ns564p844 := BSN.sin_dyadic_bound_f 215870161939 137438953472 4 3 67108864 20500001 Ns564p841 Ns564p124 Ns564p842 Ns564p843 Ns564p127 Ns564p842 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215870161939) qz371 0 3 Ns564p841 Ns564p124 Ns564p842 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215870161939) qz372 0 3 Ns564p843 Ns564p127 Ns564p842 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p845 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz116) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 65356896879) qz383) Bool.false 65356896879 33554432 563 67108864 Bool.false 67108863 67108864 1 10240000 (Ns564p839 rfl) (Enclosure.sfrac_false_div 65356896879 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 65356896879) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p840) qz416) 226375608064910080 72057594037927936 Bool.false 67108863 67108864 309 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q3 65356896879 33554432 226375608064910080 72057594037927936 309 Ns564p840 Ns564p435 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108863 67108864 Ns564p840 Ns564p435 215870161939 137438953472 20500001 20480000 (Ns564p844 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p846 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns564p817 Ns564p818 137091456061035599 16384000000000000000000 1045710350069 536870912 4493 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz370 qz120 (Enclosure.sfrac Bool.true Ns564p819 Ns564p820)) Bool.false Ns564p817 Ns564p818 137091456061035599 16384000000000000000000 Ns564p821 (Ns564p838 rfl rfl)) 

noncomputable def Ns564p847 := Ns564p816 76088 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 813 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 527877105 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 564 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 301032342 536870912) qz119 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) Bool.false 67108863 67108864 355971 41943040000 536870904 536870912 4557 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 67108863 67108864 355971 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz116) qz116) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 67108863 67108864 5832228864 687194767360000 67108863 67108864 355971 41943040000 (Ns564p845 rfl rfl) rfl)) rfl) (Ns564p846 rfl) RS565to576.d7 

noncomputable def Ns564p848 := nat_lit 110407429145058704440539745619652481673774148768842528633607474659832095979263654892447055877692209609991782400000 

noncomputable def Ns564p849 := nat_lit 29189356794165080242785005135684637312659178086889411258546929987880961584482414908790336720896000000000000 

noncomputable def Ns564p850 := nat_lit 551619295412319850321613257459745354854914912108957788240004132828480687186178756149587286847779389747494912000000 

noncomputable def Ns564p851 := BSN.sin_dyadic_bound_f 744906980 536870912 4 3 536870912 268435456 Ns564p848 Ns564p181 Ns564p849 Ns564p850 Ns564p184 Ns564p849 527877105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 744906980) qz375 0 3 Ns564p848 Ns564p181 Ns564p849 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 744906980) qz376 0 3 Ns564p850 Ns564p184 Ns564p849 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p852 := nat_lit 10370232128777282070966766387423977638359756717144790448467822438104809320552366425196032307306402896371479091441 

noncomputable def Ns564p853 := nat_lit 425999428784783292925034911369829835033072650144434656401662624336960067724270326020779807766203529042161 

noncomputable def Ns564p854 := nat_lit 62890140166091853273131956979783310797546555516996893828181389115529179600926044325386365146087513731024467400945 

noncomputable def Ns564p855 := BSN.cos_dyadic_bound_f 523742019 536870912 4 3 536870912 268435456 Ns564p852 Ns564p133 Ns564p853 Ns564p854 Ns564p136 Ns564p853 301032342 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 523742019) qz373 0 3 Ns564p852 Ns564p133 Ns564p853 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 523742019) qz374 0 3 Ns564p854 Ns564p136 Ns564p853 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p856 := nat_lit 62630204884364270818432359439909805288770386307120135248179116660199198607041307264084865390501732749647928540625 

noncomputable def Ns564p857 := nat_lit 5336680665699863329172263506594987254777122678596331583049550062957185957129077596762527008541718994140625 

noncomputable def Ns564p858 := nat_lit 313016438578814305529066730062530269122283635840055546391782277241191168692322452215517729046495086519859666140625 

noncomputable def Ns564p859 := BSN.sin_dyadic_bound_f 646555685 536870912 4 3 536870912 268435456 Ns564p856 Ns564p181 Ns564p857 Ns564p858 Ns564p184 Ns564p857 501217297 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 646555685) qz375 0 3 Ns564p856 Ns564p181 Ns564p857 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 646555685) qz376 0 3 Ns564p858 Ns564p184 Ns564p857 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p860 := nat_lit 8428962359371744003226172589963529842016335639414802713062873168271912641 

noncomputable def Ns564p861 := nat_lit 3644140126026472716225414986857855640029546606874411648061847684525761 

noncomputable def Ns564p862 := nat_lit 25279598797863179064246066939916873814768947825030659315892495809446686401 

noncomputable def Ns564p863 := BSN.cos_dyadic_bound_f 495677703 536870912 3 2 536870912 268435456 Ns564p860 Ns564p170 Ns564p861 Ns564p862 Ns564p173 Ns564p861 323848035 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 495677703) qz373 0 2 Ns564p860 Ns564p170 Ns564p861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 495677703) qz374 0 2 Ns564p862 Ns564p173 Ns564p861 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p864 := Ns564p814 128842 BSN.abs_quadSignPos (BSN.cos_quad_nat3 387 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 501217297 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 250 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 323848035 536870912) qz119 rfl rfl (Ns564p847 RS565to576.d9 RS565to576.d11 RS565to576.d13 RS565to576.d17 (Ns564p851 rfl rfl) (Ns564p855 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns564p846 rfl) RS565to576.d19 RS565to576.d21 RS565to576.d23 RS565to576.d25 RS565to576.d17 (Ns564p859 rfl rfl) (Ns564p863 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns564p865 := nat_lit 4571456124609617335243313970677543474529062547244735924025677780422803041 

noncomputable def Ns564p866 := nat_lit 1072328343110492500203554910843854715911569271671630473074128649240161 

noncomputable def Ns564p867 := nat_lit 13712223717142631020729534802210942714155364503190864511130885083969928801 

noncomputable def Ns564p868 := BSN.cos_dyadic_bound_f 425393621 536870912 3 2 536870912 268435456 Ns564p865 Ns564p170 Ns564p866 Ns564p867 Ns564p173 Ns564p866 376974003 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 425393621) qz373 0 2 Ns564p865 Ns564p170 Ns564p866 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 425393621) qz374 0 2 Ns564p867 Ns564p173 Ns564p866 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p869 := nat_lit 54154695326442692430696538292181295555735746474888849309468709048603013891284773363983075433149601799337508173041 

noncomputable def Ns564p870 := nat_lit 3451044739768267875311459688202667125474051488014001424741705917316451310570107565182746502665564736025841 

noncomputable def Ns564p871 := nat_lit 270672835315143687785040847404350485158087041662154042379670906395342981469908471360218379233552079682094553462001 

noncomputable def Ns564p872 := BSN.sin_dyadic_bound_f 623489603 536870912 4 3 536870912 268435456 Ns564p869 Ns564p181 Ns564p870 Ns564p871 Ns564p184 Ns564p870 492491742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 623489603) qz375 0 3 Ns564p869 Ns564p181 Ns564p870 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 623489603) qz376 0 3 Ns564p871 Ns564p184 Ns564p870 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p873 := Ns564p812 173392 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 138 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 376974003 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 492491742 536870912) qz119 rfl rfl (Ns564p864 rfl rfl) (Ns564p846 rfl) RS565to576.d27 RS565to576.d29 RS565to576.d31 RS565to576.d33 RS565to576.d17 (Ns564p868 rfl rfl) (Ns564p872 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p874 := nat_lit 1058812443205517128287391933060096078913060932807786211466319273997814241 

noncomputable def Ns564p875 := nat_lit 57545756936872285781520898457826319163732154042310521162924499323361 

noncomputable def Ns564p876 := nat_lit 3176322238102677640290612757383372584100855334115274013356631972994796001 

noncomputable def Ns564p877 := BSN.cos_dyadic_bound_f 295122053 536870912 3 2 536870912 268435456 Ns564p874 Ns564p170 Ns564p875 Ns564p876 Ns564p173 Ns564p875 457777633 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 295122053) qz373 0 2 Ns564p874 Ns564p170 Ns564p875 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 295122053) qz374 0 2 Ns564p876 Ns564p173 Ns564p875 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p878 := nat_lit 23003644372615950996753079290629029167438423659476062743725282864099272568024491808172796501212352783581184000000 

noncomputable def Ns564p879 := nat_lit 4640655996109427649438070612145480836623259683412816288817421635626189676464089177349385097216000000000000 

noncomputable def Ns564p880 := nat_lit 139444363261169971020131848184827442663068149344797718259413576507158963947500956307219579417178793454705049600000 

noncomputable def Ns564p881 := BSN.cos_dyadic_bound_f 639069780 536870912 4 3 536870912 268435456 Ns564p878 Ns564p133 Ns564p879 Ns564p880 Ns564p136 Ns564p879 199353819 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 639069780) qz373 0 3 Ns564p878 Ns564p133 Ns564p879 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 639069780) qz374 0 3 Ns564p880 Ns564p136 Ns564p879 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p882 := Ns564p810 212316 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 457777633 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 199353819 536870912) qz119 rfl rfl (Ns564p873 rfl) (Ns564p846 rfl) RS565to576.d35 RS565to576.d37 RS565to576.d39 RS565to576.d41 RS565to576.d17 (Ns564p877 rfl rfl) (Ns564p881 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p883 := nat_lit 9941896798825326511595279942023240153676597676822014592893209300874430625 

noncomputable def Ns564p884 := nat_lit 1565593978695958494304617751487544099224003835092691312613501875390625 

noncomputable def Ns564p885 := nat_lit 26035766368577014073758763800367982473944726480705602433547507261158590625 

noncomputable def Ns564p886 := BSN.sin_dyadic_bound_f 446000035 536870912 3 2 536870912 268435456 Ns564p883 Ns564p143 Ns564p884 Ns564p885 Ns564p146 Ns564p884 396441825 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 446000035) qz375 0 2 Ns564p883 Ns564p143 Ns564p884 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 446000035) qz376 0 2 Ns564p885 Ns564p146 Ns564p884 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p887 := nat_lit 109871581462855700883484537432336 

noncomputable def Ns564p888 := BSN.cos_dyadic_bound_f 102381466 536870912 2 1 536870912 268435456 Ns564p887 Ns564p163 Ns564p887 Ns564p887 Ns564p164 Ns564p887 527138370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 102381466) qz373 0 1 Ns564p887 Ns564p163 Ns564p887 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 102381466) qz374 0 1 Ns564p887 Ns564p164 Ns564p887 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p889 := Ns564p808 247323 BSN.abs_quadSignPos qz625 (BSN.sfrac_eq_quadSignPos_mul Bool.false 396441825 536870912) BSN.abs_quadSignNeg qz599 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 527138370 536870912) qz119 rfl rfl (Ns564p882 rfl) (Ns564p846 rfl) RS565to576.d43 RS565to576.d45 RS565to576.d47 RS565to576.d49 RS565to576.d17 (Ns564p886 rfl rfl) (Ns564p888 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p890 := nat_lit 17852411834347642584713560727750802688457122819098155019382257231272673280 

noncomputable def Ns564p891 := nat_lit 5046910924619328313596630213937558319903425557085910249080944454598656 

noncomputable def Ns564p892 := nat_lit 46748145519889680237932550219000965280107858980069409767502637886120984576 

noncomputable def Ns564p893 := BSN.sin_dyadic_bound_f 516271564 536870912 3 2 536870912 268435456 Ns564p890 Ns564p143 Ns564p891 Ns564p892 Ns564p146 Ns564p891 440301649 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 516271564) qz375 0 2 Ns564p890 Ns564p143 Ns564p891 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 516271564) qz376 0 2 Ns564p892 Ns564p146 Ns564p891 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p894 := Ns564p806 Bool.false 213558926 247323 Bool.true 516271564 28296951008113761 1 Bool.false 440301649 Bool.false Bool.false 340663068 263683 BSN.abs_quadSignPos qz377 (BSN.sfrac_eq_quadSignPos_mul Bool.false 440301649 536870912) qz119 rfl (Ns564p889 rfl) (Ns564p846 rfl) RS565to576.d51 RS565to576.d53 RS565to576.d17 (Ns564p893 rfl rfl) rfl 

noncomputable def Ns564p895 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) 340663068 536870912 263683 536870912 340663068 536870912 263683 536870912 365784184003756032 85165767 67108864 263683 268435456 (Ns564p894 rfl rfl rfl rfl) 

noncomputable def Ns564p896 := @Enclosure.Real.IsNear.mulLit_ff qz653 (Zeta.RiemannSiegel.correction qz118) 19059835 67108864 1 67108864 903926092410055 2251799813685248 14781309860581 1407374883553280000 17228682173530400640925 151115727451828646838272 

noncomputable abbrev qz657 := (@HPow.hPow Real Real Real qz7 qz117 qz9)

noncomputable def Ns564p897 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz657 1 1 0 1 19059835 67108864 1 67108864 19059835 67108864 1 67108864 

noncomputable def Ns564p898 := @Enclosure.Real.IsNear.sqrt_image qz117 10313899479499 67108864000 965657 67108864000 415978969 415979009 33554432 (@Enclosure.Real.IsNear.of_eq qz117 (@HMul.hMul Real Real Real qz5 qz116 qz3) Bool.false 10313899479499 67108864000 965657 67108864000 (BSN.t_div_two_pi_mk qz116 965657 1000 qz119) (@Enclosure.Real.IsNear.mulLit_ff qz116 qz3 965657 1000 0 1 10680707 67108864 1 67108864 10313899479499 67108864000 965657 67108864000 (Enclosure.Real.IsNear.const Bool.false 965657 1000) RS565to576.d56 rfl)) 

noncomputable abbrev qz769 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 965657 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz658 := qz769

noncomputable abbrev qz456 := qz658

noncomputable abbrev qz125 := qz456

noncomputable def Ns564p899 := @Enclosure.Real.IsNear.sqrt_image qz125 415978989 33554432 5 8388608 118143717 118143724 33554432 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 831957978 67108864 40 67108864 415978989 33554432 5 8388608 (Ns564p898 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns564p900 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz125) 236287441 67108864 7 67108864 9529917 9529918 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz125) Bool.false 236287441 67108864 7 67108864 236287441 67108864 7 67108864 (Ns564p899 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns564p901 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 19059835 67108864 1 67108864 19059835 67108864 1 67108864 (Ns564p900 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz457 := (@HMul.hMul Real Real Real qz588 qz586 qz652)

noncomputable abbrev qz126 := (Real.cos qz457)

noncomputable abbrev qz659 := (@HMul.hMul Real Real Real qz741 qz768 qz768)

noncomputable abbrev qz458 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz659 qz652) qz604)

noncomputable abbrev qz127 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz458))

noncomputable def Ns564p902 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz118) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz126) qz127) Bool.false 903926092410055 

noncomputable def Ns564p903 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz126) qz127 84062165 67108864 407 

noncomputable abbrev qz128 := (@Neg.neg Real Real.instNeg (Real.cos qz457))

noncomputable def Ns564p904 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz126) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz128)) Bool.true 84062165 67108864 407 67108864 (BSN.inv_eq_neg_inv_neg qz126) 

noncomputable def Ns564p905 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz128) Bool.false 84062165 67108864 407 67108864 84062165 67108864 

noncomputable def Ns564p906 := @Enclosure.Real.IsNear.recentre' qz126 Bool.true 53574633 67108864 661897216 171798691840000 53574633 67108864 40399 10485760000 

noncomputable abbrev qz129 := qz457

noncomputable def Ns564p907 := @Enclosure.Real.IsNear.cos_image qz129 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41864251) qz629) Bool.false 41864251 16777216 63 16777216 Bool.true 53574633 67108864 1 

noncomputable def Ns564p908 := nat_lit 5397215082953487024391259 

noncomputable def Ns564p909 := nat_lit 1441151880758558720000000000000 

noncomputable def Ns564p910 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz118 884279719003555 140737488355328 1 500000000000000 13325805 33554432 5 8388608 11783739100896168236775 4722366482869645213696 Ns564p908 

noncomputable def Ns564p911 := @Enclosure.Real.IsNear.subLit_ff_p qz125 qz1 415978989 33554432 5 8388608 12 1 0 1 13325805 13325805 33554432 5 

noncomputable def Ns564p912 := @Ns564p911 8388608 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 831957978 67108864 40 67108864 415978989 33554432 5 8388608 (Ns564p898 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns564p913 := @Enclosure.Real.IsNear.recentre' qz129 Bool.false 11783739100896168236775 4722366482869645213696 Ns564p908 Ns564p909 41864251 16777216 63 16777216 (@Ns564p910 Ns564p909 RS565to576.d55 (Ns564p912 rfl rfl) rfl) 

noncomputable def Ns564p914 := nat_lit 2235321932883498832494592 

noncomputable def Ns564p915 := nat_lit 2417851639229258349412352 

noncomputable def Ns564p916 := nat_lit 281324224156963810547079050694554923663278796557514950201963033814497625823215552963964435265 

noncomputable def Ns564p917 := nat_lit 67945728841094649099481731798274945534157348081052620220902086846785904098136559219243841 

noncomputable def Ns564p918 := nat_lit 736691532088210112477141209967589497777722498134693641524783628040218033311310417619266173761 

noncomputable def Ns564p919 := BSN.sin_dyadic_bound_f 127063340919 137438953472 3 2 67108864 20500001 Ns564p916 Ns564p207 Ns564p917 Ns564p918 Ns564p210 Ns564p917 53574633 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 127063340919) qz371 0 2 Ns564p916 Ns564p207 Ns564p917 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 127063340919) qz372 0 2 Ns564p918 Ns564p210 Ns564p917 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p920 := @Ns564p907 10240000 (Ns564p913 rfl) (Enclosure.sfrac_false_div 41864251 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 41864251) qz629) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p914) (@Nat.cast Real Real.instNatCast Ns564p915)) 226375608064910080 72057594037927936 Bool.false 53574633 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 41864251 16777216 226375608064910080 72057594037927936 0 Ns564p914 Ns564p915 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 53574633 67108864 Ns564p914 Ns564p915 127063340919 137438953472 20500001 20480000 (Ns564p919 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p921 := @Enclosure.Real.IsNear.inv_image qz128 53574633 67108864 40399 10485760000 42030879 42031286 33554432 (@Enclosure.Real.IsNear.neg qz126 Bool.true 53574633 67108864 40399 10485760000 (Ns564p906 (Ns564p920 rfl rfl) rfl)) 

noncomputable def Ns564p922 := Ns564p904 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz128) Bool.false 84062165 67108864 407 67108864 (@Ns564p905 407 67108864 (Ns564p921 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p923 := @Enclosure.Real.IsNear.recentre' qz127 Bool.true 10753067 33554432 

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz355 qz352 qz458)

noncomputable def Ns564p924 := @Enclosure.Real.IsNear.cos_image qz130 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 127306729)) qz396) Bool.true 127306729 67108864 

noncomputable def Ns564p925 := nat_lit 300594516265401721872936753445 

noncomputable def Ns564p926 := nat_lit 4061813323398951554100454808710661 

noncomputable def Ns564p927 := @Enclosure.Real.IsNear.recentre' qz130 Bool.true Ns564p925 Ns564p218 Ns564p926 

noncomputable abbrev qz131 := qz458

noncomputable def Ns564p928 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz131 884279719003555 140737488355328 1 500000000000000 339931482997399 

noncomputable abbrev qz459 := (@HSub.hSub Real Real Real qz592 qz659 qz652)

noncomputable abbrev qz132 := qz459

noncomputable def Ns564p929 := @Enclosure.Real.IsNear.subLit_tf qz132 qz31 269562738819735 1125899906842624 150515155 140737488355328 1 16 

noncomputable abbrev qz460 := qz659

noncomputable abbrev qz133 := qz460

noncomputable def Ns564p930 := @Enclosure.Real.IsNear.subLit_ff_n qz133 qz118 177577078898025 1125899906842624 66629075 140737488355328 13325805 33554432 5 8388608 

noncomputable def Ns564p931 := @Enclosure.Real.IsNear.mulLit_ff qz118 qz118 13325805 33554432 5 8388608 13325805 33554432 5 8388608 177577078898025 1125899906842624 

noncomputable def Ns564p932 := nat_lit 2173245823601378367760595247415062538602453674416206109471271462678817177032802726800207414268173101921 

noncomputable def Ns564p933 := nat_lit 18122425164985750945572407579283030448913303767815040278404342527589667197824351096196675805260641 

noncomputable def Ns564p934 := nat_lit 13117029576760850177381299853891913583789928314455446133758096374475037981930280964382654206031447337825 

noncomputable def Ns564p935 := BSN.cos_dyadic_bound_t 127306729 67108864 4 3 33554432 10240000 Ns564p932 Ns564p665 Ns564p933 Ns564p934 Ns564p668 Ns564p933 10753067 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 127306729) (BSN.cosEvenQ 67108864) 0 3 Ns564p932 Ns564p665 Ns564p933 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 127306729) (BSN.cosOddQ 67108864) 0 3 Ns564p934 Ns564p668 Ns564p933 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p936 := @Ns564p923 1173897216 171798691840000 10753067 33554432 71649 10485760000 (@Ns564p924 113 16777216 Bool.true 10753067 33554432 1 10240000 (@Ns564p927 Ns564p659 127306729 67108864 113 16777216 (@Ns564p928 1125899906842624 150515155 140737488355328 Ns564p925 Ns564p218 Ns564p926 Ns564p659 RS565to576.d55 (@Ns564p929 0 1 5438903727958384 339931482997399 1125899906842624 150515155 140737488355328 (@Ns564p930 9045024589460558315520 269562738819735 1125899906842624 150515155 140737488355328 (@Ns564p931 66629075 140737488355328 (Ns564p912 rfl rfl) (Ns564p912 rfl rfl) rfl) (Ns564p912 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 127306729 67108864) (BSN.cos_neg_of_bound 127306729 67108864 Bool.true 10753067 33554432 1 10240000 (Ns564p935 rfl rfl)) rfl rfl) 

noncomputable def Ns564p937 := @Ns564p896 282294295615613009091 Ns564p539 (Ns564p897 qz33 (@Enclosure.Real.IsNear.of_eq qz657 (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 19059835 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz117 (BSN.t_div_two_pi_nonneg qz116 965657 1000 qz119)) Ns564p901) rfl) (@Ns564p902 2251799813685248 14781309860581 1407374883553280000 (BSN.correction_mk qz118 (BSN.cos_two_pi_p_ne_zero_mk qz116 965657 1000 12 qz119 rfl rfl (@BSN.floor_sqrt_eq_dec qz116 965657 1000 12 qz119 rfl rfl rfl))) (@Ns564p903 67108864 10753067 33554432 71649 10485760000 903926092410055 2251799813685248 14781309860581 1407374883553280000 Ns564p922 (Ns564p936 rfl) rfl)) 

noncomputable def Ns564p938 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (hardyZApproximantRS₀ qz116) Bool.false 174547576089430841864291 151115727451828646838272 93057502150610495569091 Ns564p539 (@Eq.refl Real (hardyZApproximantRS₀ qz116)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HMul.hMul Real Real Real qz5 qz653 (Zeta.RiemannSiegel.correction qz118))) Bool.false 174547576089430841864291 151115727451828646838272 93057502150610495569091 Ns564p539 (BSN.hardyZApproximantRS₀_eq qz116 12 (@BSN.floor_sqrt_eq_dec qz116 965657 1000 12 qz119 rfl rfl rfl)) (@Ns564p805 174547576089430841864291 151115727451828646838272 93057502150610495569091 Ns564p539 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12)) Bool.false 85165767 67108864 263683 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (Ns564p895 (Ns564p894 rfl rfl rfl rfl) rfl rfl)) (Ns564p937 rfl) rfl rfl)) 

theorem RS565to576.d64 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz116) Bool.false 174547576089430841864291 151115727451828646838272 93057502150610495569091 Ns564p539 := Ns564p938 

noncomputable def Ns564p939 := nat_lit 17343646700659524069241311461376 

noncomputable abbrev qz770 := (Enclosure.sfrac Bool.false 966905 1000)

noncomputable abbrev qz660 := qz770

noncomputable abbrev qz461 := qz660

noncomputable abbrev qz134 := qz461

noncomputable abbrev qz771 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 966905 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz661 := qz771

noncomputable abbrev qz462 := qz661

noncomputable abbrev qz135 := qz462

noncomputable abbrev qz772 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 966905 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz662 := qz772

noncomputable abbrev qz463 := qz662

noncomputable abbrev qz136 := qz463

noncomputable abbrev qz663 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz135 qz9))

noncomputable def Ns564p940 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HMul.hMul Real Real Real qz5 qz663 (Zeta.RiemannSiegel.correction qz136)) 214352063 134217728 132009 134217728 8550753706223683678361 75557863725914323419136 137205323073002626363 Ns564p235 Ns564p939 

noncomputable def Ns564p941 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin BSN.quadSignPos 11 12 966905 1000 287 536870912 268435456 9007199254740992 Bool.false 1047397306329 4499 1334074092 54 154981288 8 

noncomputable def Ns564p942 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 966905 1000 175 234 536870912 268435456 9007199254740992 Bool.false 1047397306329 4499 

noncomputable def Ns564p943 := Ns564p942 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.true 480819584 212584 Bool.true 301810088 Bool.true 22050761 28296951008113761 1 Bool.false 286162579 Bool.false Bool.false 536418133 Bool.true Bool.true 552063174 

noncomputable def Ns564p944 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 966905 1000 38 110 536870912 268435456 9007199254740992 Bool.false 1047397306329 4499 

noncomputable def Ns564p945 := Ns564p944 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 165087269 173610 Bool.true 1422605 Bool.true 424286703 28296951008113761 1 Bool.false 536869027 Bool.true Bool.false 377761339 Bool.true Bool.true 480819584 

noncomputable def Ns564p946 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 966905 1000 139 44 536870912 268435456 9007199254740992 Bool.false 1047397306329 4499 

noncomputable def Ns564p947 := Ns564p946 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.true 386586981 129003 Bool.false 68529495 Bool.false 163342235 28296951008113761 1 Bool.false 68343548 Bool.false Bool.false 512213674 Bool.false Bool.true 165087269 

noncomputable def Ns564p948 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 966905 1000 388 251 536870912 268435456 9007199254740992 Bool.false 1047397306329 4499 

noncomputable def Ns564p949 := Ns564p948 744261104 53 268435448 8 864060384 53 240095976 8 Bool.true 633340743 76180 Bool.false 561359231 Bool.false 260971747 28296951008113761 1 Bool.false 269171823 Bool.false Bool.false 250814943 Bool.false Bool.true 386586981 

noncomputable def Ns564p950 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 966905 1000 815 565 536870912 268435456 9007199254740992 Bool.false 1047397306329 4499 

noncomputable def Ns564p951 := Ns564p950 372130544 53 379625064 8 589812976 53 309962568 8 Bool.true 536870848 4557 Bool.false 280814608 Bool.false 631296828 28296951008113761 1 Bool.false 268183971 Bool.false Bool.false 495547699 Bool.true Bool.true 633340743 

noncomputable def Ns564p952 := nat_lit 3308392350151546591402850325919194333509798443993338019 

noncomputable def Ns564p953 := nat_lit 1695803118402534511554183695608380698309130662707200 

noncomputable def Ns564p954 := nat_lit 405658482550224540589254351500000000 

noncomputable def Ns564p955 := nat_lit 2353399584102042906777729335832645000000 

noncomputable abbrev qz664 := (@Eq.refl Real qz770)

noncomputable abbrev qz464 := qz664

noncomputable abbrev qz137 := qz464

noncomputable def Ns564p956 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz134 966905 1000 3739622116100 16000000 1933810 4000 2000 Ns564p954 Ns564p955 qz137 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns564p957 := nat_lit 16541961750757732957014251629595971667548992219966690095000000 

noncomputable abbrev qz665 := (@HSub.hSub Real Real Real qz745 qz746 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz747 (@Nat.cast Real Real.instNatCast 1933810))))

noncomputable abbrev qz465 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 966905 4000) (Real.log (Enclosure.sfrac Bool.false 3739622116100 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz665))

noncomputable abbrev qz666 := (Enclosure.sfrac Bool.false 966905 2000)

noncomputable abbrev qz138 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz465 qz666) (@HMul.hMul Real Real Real qz355 qz666 (Real.log Real.pi)))

noncomputable def Ns564p958 := @Enclosure.Real.IsNear.addLit_ft_p qz138 (Enclosure.sfrac Bool.true Ns564p954 Ns564p955) 7028964959475062787811 3602879701896396800 27453622792087267 3276800000000000000000 Ns564p954 Ns564p955 0 1 Ns564p957 

noncomputable def Ns564p959 := nat_lit 94341170705235500003733851340800 

noncomputable abbrev qz139 := (@HSub.hSub Real Real Real qz359 qz465 qz666)

noncomputable def Ns564p960 := @Enclosure.Real.IsNear.subLit_ff_p qz139 (@HMul.hMul Real Real Real qz5 qz666 (Real.log Real.pi)) 9022879735998066183907 3602879701896396800 9520569790933 3200000000000000000 7427911372941 13421772800 580143 107374182400 Ns564p959 7028964959475062787811 3602879701896396800 

noncomputable def Ns564p961 := nat_lit 18045759471996132367814000 

noncomputable abbrev qz140 := qz465

noncomputable def Ns564p962 := @Enclosure.Real.IsNear.subLit_ff_p qz140 qz666 10764700935079133957859 3602879701896396800 9520569790933 3200000000000000000 966905 2000 0 1 Ns564p961 9022879735998066183907 3602879701896396800 9520569790933 3200000000000000000 

noncomputable def Ns564p963 := nat_lit 24239951559988608772869952466721964032 

noncomputable def Ns564p964 := nat_lit 119557022641596679661289472 

noncomputable def Ns564p965 := nat_lit 107964136199903228507283931100588202156142617227414819316939039311758938101308931061610597836120021353099311970153593341085478477800531519748777873854959530250000000000000000000000000000 

noncomputable def Ns564p966 := nat_lit 2993313734022569858160637655103317762436172663169600275103333314693877524357909898090418802218927604639650893819289505926348972143748579795293033529212268150000000000000000000000000000 

noncomputable def Ns564p967 := nat_lit 140518180442724921584586077216492446257110208492633082301713696530263094889254480728712412891959282152077827967506577424351499664164054132017594635350000000000000000000000000000 

noncomputable def Ns564p968 := BSN.log_dyadic_bound 1642470116100 5836774116100 8 7 Ns564p965 268435456 81920000 Ns564p966 Ns564p967 155264231 7479244232200 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1642470116100) (BSN.artanhQ 5836774116100) 0 7 Ns564p966 Ns564p965 Ns564p967 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz466 := (Real.log (Enclosure.sfrac Bool.false 3739622116100 16000000))

noncomputable def Ns564p969 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 966905 4000) qz466 966905 4000 0 1 55673077069966439 4503599627370496 48828193 4000000000000000 10766115316867179940259 3602879701896396800 9442444790533 3200000000000000000 (Enclosure.Real.IsNear.const Bool.false 966905 4000) (BSN.isNear_log_sfrac 3739622116100 16000000 55673077069966439 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3739622116100) qz362)) Bool.false Ns564p964 Ns564p112 1000001392640000 81920000000000000000000 55673077069966439 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3739622116100 16000000 17 7479244232200 4194304000000 155264231 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns564p968 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p970 := BSN.arctan_dyadic_bound_f 1000 1933810 1 0 33554432 10240000 0 1 1 0 1 1 17351 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1933810) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1933810) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns564p971 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1933810))) 884279719003555 562949953421312 1 2000000000000000 17351 33554432 1 10240000 29661735955642080821248 883988617528739 562949953421312 195312501 2000000000000000 qz17 (Ns564p970 rfl) rfl rfl 

noncomputable abbrev qz467 := (@HMul.hMul Real Real Real qz588 qz593 qz665)

noncomputable abbrev qz141 := qz467

noncomputable abbrev qz468 := qz665

noncomputable abbrev qz142 := qz468

noncomputable def Ns564p972 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 966905 4000) qz466) qz141 10766115316867179940259 3602879701896396800 9442444790533 3200000000000000000 883988617528739 2251799813685248 195312501 8000000000000000 Ns564p963 10764700935079133957859 3602879701896396800 9520569790933 3200000000000000000 (Ns564p969 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz142 1 4 0 1 883988617528739 562949953421312 195312501 2000000000000000 883988617528739 2251799813685248 195312501 8000000000000000 qz369 Ns564p971 rfl) 

noncomputable def Ns564p973 := @Ns564p958 Ns564p952 Ns564p953 27453622792087267 3276800000000000000000 (@Ns564p960 27453622792087267 3276800000000000000000 (Ns564p962 (Ns564p972 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 966905 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz666 (Real.log Real.pi) 966905 2000 0 1 38410761 33554432 3 268435456 7427911372941 13421772800 580143 107374182400 (Enclosure.Real.IsNear.const Bool.false 966905 2000) RS565to576.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns564p954 Ns564p955) 

noncomputable def Ns564p974 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns564p952 Ns564p953 27453622792087267 3276800000000000000000 130924663291 67108864 563 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz370 qz138 (Enclosure.sfrac Bool.true Ns564p954 Ns564p955)) Bool.false Ns564p952 Ns564p953 27453622792087267 3276800000000000000000 Ns564p956 (Ns564p973 rfl rfl)) 

noncomputable def Ns564p975 := BSN.cos_dyadic_bound_f 65155706 137438953472 1 0 67108864 20500001 0 1 1 0 1 1 67108856 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 65155706) (BSN.cosEvenQ 137438953472) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 65155706) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl 

noncomputable def Ns564p976 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz134) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 130924663291) qz396) Bool.false 130924663291 67108864 563 67108864 Bool.true 67108856 67108864 1 10240000 (Ns564p974 rfl) (Enclosure.sfrac_false_div 130924663291 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 130924663291) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4584925238874406387712) qz397) 226375608064910080 72057594037927936 Bool.false 67108856 67108864 310 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q2 130924663291 67108864 226375608064910080 72057594037927936 310 4584925238874406387712 Ns564p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108856 67108864 4584925238874406387712 Ns564p112 65155706 137438953472 20500001 20480000 (Ns564p975 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p977 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns564p952 Ns564p953 27453622792087267 3276800000000000000000 1047397306329 536870912 4499 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz370 qz138 (Enclosure.sfrac Bool.true Ns564p954 Ns564p955)) Bool.false Ns564p952 Ns564p953 27453622792087267 3276800000000000000000 Ns564p956 (Ns564p973 rfl rfl)) 

noncomputable def Ns564p978 := Ns564p951 76180 BSN.abs_quadSignPos (BSN.cos_quad_nat3 815 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268183971 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 565 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 495547699 536870912) qz137 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) Bool.true 8388607 8388608 355971 41943040000 536870848 536870912 4557 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 8388607 8388608 355971 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz134) qz134) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 67108856 67108864 5832228864 687194767360000 8388607 8388608 355971 41943040000 (Ns564p976 rfl rfl) rfl)) rfl) (Ns564p977 rfl) RS565to576.d7 

noncomputable def Ns564p979 := nat_lit 1562251023552556641048891851395026747921080753197539734591128692808744960 

noncomputable def Ns564p980 := nat_lit 38668521643698976065816607421012328090229448873028407485429046050816 

noncomputable def Ns564p981 := nat_lit 4091547217412129975833467336289245557928779696409666782697979691281678336 

noncomputable def Ns564p982 := BSN.sin_dyadic_bound_f 280814608 536870912 3 2 536870912 268435456 Ns564p979 Ns564p143 Ns564p980 Ns564p981 Ns564p146 Ns564p980 268183971 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 280814608) qz375 0 2 Ns564p979 Ns564p143 Ns564p980 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 280814608) qz376 0 2 Ns564p981 Ns564p146 Ns564p980 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p983 := nat_lit 56920277631152042763612418844247356253000305292563677736335832035810439607097951314046956085602176267993078562816 

noncomputable def Ns564p984 := nat_lit 4006851860918485158669104158941069385697854218779530415328143955039995472559934982148218784978284488687616 

noncomputable def Ns564p985 := nat_lit 284490211275556221003536954997825058893739378277183314819592476693546730199241008499003816734224153039025551179776 

noncomputable def Ns564p986 := BSN.sin_dyadic_bound_f 631296828 536870912 4 3 536870912 268435456 Ns564p983 Ns564p181 Ns564p984 Ns564p985 Ns564p184 Ns564p984 495547699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 631296828) qz375 0 3 Ns564p983 Ns564p181 Ns564p984 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 631296828) qz376 0 3 Ns564p985 Ns564p184 Ns564p984 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p987 := nat_lit 13688539462533287169716152510968462143644729572276992518954698507671521110359944357838413323894977172933693181441 

noncomputable def Ns564p988 := nat_lit 979242881172966870391766001723782648659952433718337805649123390123604006174514571074246660092374242332161 

noncomputable def Ns564p989 := nat_lit 83004438693962187636936443221876734597029000175943183399430173390351691435533486312758849176035925452409475730945 

noncomputable def Ns564p990 := BSN.cos_dyadic_bound_f 561359231 536870912 4 3 536870912 268435456 Ns564p987 Ns564p133 Ns564p988 Ns564p989 Ns564p136 Ns564p988 269171823 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 561359231) qz373 0 3 Ns564p987 Ns564p133 Ns564p988 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 561359231) qz374 0 3 Ns564p989 Ns564p136 Ns564p988 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p991 := nat_lit 1165314830749827274889090326172720640974052910281196143044246678879696545 

noncomputable def Ns564p992 := nat_lit 21515326582669586277763021093305052369597683034787047058101652518561 

noncomputable def Ns564p993 := nat_lit 3051980198577937588236501142703926803894873511630600243230171042009413281 

noncomputable def Ns564p994 := BSN.sin_dyadic_bound_f 260971747 536870912 3 2 536870912 268435456 Ns564p991 Ns564p143 Ns564p992 Ns564p993 Ns564p146 Ns564p992 250814943 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 260971747) qz375 0 2 Ns564p991 Ns564p143 Ns564p992 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 260971747) qz376 0 2 Ns564p993 Ns564p146 Ns564p992 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p995 := Ns564p949 129003 BSN.abs_quadSignPos (BSN.cos_quad_nat0 388 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 269171823 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 251 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 250814943 536870912) qz137 rfl rfl (Ns564p978 RS565to576.d9 RS565to576.d11 RS565to576.d13 RS565to576.d17 (Ns564p982 rfl rfl) (Ns564p986 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns564p977 rfl) RS565to576.d19 RS565to576.d21 RS565to576.d23 RS565to576.d25 RS565to576.d17 (Ns564p990 rfl rfl) (Ns564p994 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns564p996 := nat_lit 22055155590177707787936272750625 

noncomputable def Ns564p997 := BSN.sin_dyadic_bound_f 68529495 536870912 2 1 536870912 268435456 Ns564p996 Ns564p463 Ns564p996 Ns564p996 Ns564p464 Ns564p996 68343548 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 68529495) qz375 0 1 Ns564p996 Ns564p463 Ns564p996 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 68529495) qz376 0 1 Ns564p996 Ns564p464 Ns564p996 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p998 := nat_lit 99353911270432256644505475027032425614750520525738003199062182857190625 

noncomputable def Ns564p999 := nat_lit 506743223464620736234709253260190000964225759784337256693500390625 

noncomputable def Ns564p1000 := nat_lit 298060720324849840692043955662590756464249633125694440922673161570790625 

noncomputable def Ns564p1001 := BSN.cos_dyadic_bound_f 163342235 536870912 3 2 536870912 268435456 Ns564p998 Ns564p170 Ns564p999 Ns564p1000 Ns564p173 Ns564p999 512213674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 163342235) qz373 0 2 Ns564p998 Ns564p170 Ns564p999 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 163342235) qz374 0 2 Ns564p1000 Ns564p173 Ns564p999 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1002 := Ns564p947 173610 BSN.abs_quadSignPos (BSN.cos_quad_nat3 139 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 68343548 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 512213674 536870912) qz137 rfl rfl (Ns564p995 rfl rfl) (Ns564p977 rfl) RS565to576.d27 RS565to576.d29 RS565to576.d31 RS565to576.d33 RS565to576.d17 (Ns564p997 rfl rfl) (Ns564p1001 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1003 := BSN.cos_dyadic_bound_f 1422605 536870912 1 0 536870912 268435456 0 1 1 0 1 1 536869027 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1422605) qz373 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1422605) qz374 0 0 rfl) rfl rfl 

noncomputable def Ns564p1004 := nat_lit 4524048920455770644309395627340986152657224681336023963073255883612736641 

noncomputable def Ns564p1005 := nat_lit 1050208117276483375003568983108287927480720496447033850507136142789761 

noncomputable def Ns564p1006 := nat_lit 13570046345132758966178179744056741882116712603015177821518753378552630401 

noncomputable def Ns564p1007 := BSN.cos_dyadic_bound_f 424286703 536870912 3 2 536870912 268435456 Ns564p1004 Ns564p170 Ns564p1005 Ns564p1006 Ns564p173 Ns564p1005 377761339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 424286703) qz373 0 2 Ns564p1004 Ns564p170 Ns564p1005 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 424286703) qz374 0 2 Ns564p1006 Ns564p173 Ns564p1005 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1008 := Ns564p945 212584 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536869027 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 377761339 536870912) qz137 rfl rfl (Ns564p1002 rfl) (Ns564p977 rfl) RS565to576.d35 RS565to576.d37 RS565to576.d39 RS565to576.d41 RS565to576.d17 (Ns564p1003 rfl rfl) (Ns564p1007 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1009 := nat_lit 2084541929190492754634218531557195527592733013401103477527027120498278400 

noncomputable def Ns564p1010 := nat_lit 68844621373627623645615214593370327231828461946924268154416892215296 

noncomputable def Ns564p1011 := nat_lit 5459403113730971341222765158016646639355925408064499801850916259669999616 

noncomputable def Ns564p1012 := BSN.sin_dyadic_bound_f 301810088 536870912 3 2 536870912 268435456 Ns564p1009 Ns564p143 Ns564p1010 Ns564p1011 Ns564p146 Ns564p1010 286162579 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 301810088) qz375 0 2 Ns564p1009 Ns564p143 Ns564p1010 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 301810088) qz376 0 2 Ns564p1011 Ns564p146 Ns564p1010 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1013 := nat_lit 236425506704749839067725332641 

noncomputable def Ns564p1014 := BSN.cos_dyadic_bound_f 22050761 536870912 2 1 536870912 268435456 Ns564p1013 Ns564p163 Ns564p1013 Ns564p1013 Ns564p164 Ns564p1013 536418133 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 22050761) qz373 0 1 Ns564p1013 Ns564p163 Ns564p1013 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 22050761) qz374 0 1 Ns564p1013 Ns564p164 Ns564p1013 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1015 := Ns564p943 247636 BSN.abs_quadSignPos qz625 (BSN.sfrac_eq_quadSignPos_mul Bool.false 286162579 536870912) BSN.abs_quadSignNeg qz599 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536418133 536870912) qz137 rfl rfl (Ns564p1008 rfl) (Ns564p977 rfl) RS565to576.d43 RS565to576.d45 RS565to576.d47 RS565to576.d49 RS565to576.d17 (Ns564p1012 rfl rfl) (Ns564p1014 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1016 := nat_lit 14993919733269321587916385334375147659921310228266738169239658874185758945 

noncomputable def Ns564p1017 := nat_lit 3560422344010146604461694504269816906770665684785308682291479190747361 

noncomputable def Ns564p1018 := nat_lit 39264025284291254397659499798927997500992469520066090419665872751796730081 

noncomputable def Ns564p1019 := BSN.sin_dyadic_bound_f 494239771 536870912 3 2 536870912 268435456 Ns564p1016 Ns564p143 Ns564p1017 Ns564p1018 Ns564p146 Ns564p1017 427328265 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 494239771) qz375 0 2 Ns564p1016 Ns564p143 Ns564p1017 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 494239771) qz376 0 2 Ns564p1018 Ns564p146 Ns564p1017 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1020 := Ns564p941 Bool.true 552063174 247636 Bool.true 494239771 28296951008113761 1 Bool.false 427328265 Bool.false Bool.true 428704126 264018 BSN.abs_quadSignPos qz377 (BSN.sfrac_eq_quadSignPos_mul Bool.false 427328265 536870912) qz137 rfl (Ns564p1015 rfl) (Ns564p977 rfl) RS565to576.d51 RS565to576.d53 RS565to576.d17 (Ns564p1019 rfl rfl) rfl 

noncomputable def Ns564p1021 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) 428704126 536870912 264018 536870912 428704126 536870912 264018 536870912 460317550207565824 214352063 134217728 132009 134217728 (Ns564p1020 rfl rfl rfl rfl) 

noncomputable def Ns564p1022 := @Enclosure.Real.IsNear.mulLit_ff qz663 (Zeta.RiemannSiegel.correction qz136) 9526841 33554432 1 33554432 897543446586721 2251799813685248 14343090650489 1407374883553280000 8550753706223683678361 75557863725914323419136 

noncomputable abbrev qz667 := (@HPow.hPow Real Real Real qz7 qz135 qz9)

noncomputable def Ns564p1023 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz667 1 1 0 1 9526841 33554432 1 33554432 9526841 33554432 1 33554432 

noncomputable def Ns564p1024 := @Enclosure.Real.IsNear.sqrt_image qz135 2065445800367 13421772800 193381 13421772800 416247685 416247725 33554432 (@Enclosure.Real.IsNear.of_eq qz135 (@HMul.hMul Real Real Real qz5 qz134 qz3) Bool.false 2065445800367 13421772800 193381 13421772800 (BSN.t_div_two_pi_mk qz134 966905 1000 qz137) (@Enclosure.Real.IsNear.mulLit_ff qz134 qz3 966905 1000 0 1 10680707 67108864 1 67108864 2065445800367 13421772800 193381 13421772800 (Enclosure.Real.IsNear.const Bool.false 966905 1000) RS565to576.d56 rfl)) 

noncomputable abbrev qz773 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 966905 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz668 := qz773

noncomputable abbrev qz469 := qz668

noncomputable abbrev qz143 := qz469

noncomputable def Ns564p1025 := @Enclosure.Real.IsNear.sqrt_image qz143 416247705 33554432 5 8388608 118181871 118181877 33554432 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 832495410 67108864 40 67108864 416247705 33554432 5 8388608 (Ns564p1024 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns564p1026 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz143) 59090937 16777216 3 33554432 9526840 9526842 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz143) Bool.false 236363748 67108864 6 67108864 59090937 16777216 3 33554432 (Ns564p1025 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns564p1027 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 19053682 67108864 2 67108864 9526841 33554432 1 33554432 (Ns564p1026 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz470 := (@HMul.hMul Real Real Real qz588 qz586 qz662)

noncomputable abbrev qz144 := (Real.cos qz470)

noncomputable abbrev qz669 := (@HMul.hMul Real Real Real qz741 qz772 qz772)

noncomputable abbrev qz471 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz669 qz662) qz604)

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz471))

noncomputable def Ns564p1028 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz136) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz144) qz145) Bool.false 897543446586721 

noncomputable def Ns564p1029 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz144) qz145 81088139 67108864 379 

noncomputable abbrev qz146 := (@Neg.neg Real Real.instNeg (Real.cos qz470))

noncomputable def Ns564p1030 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz144) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz146)) Bool.true 81088139 67108864 379 67108864 (BSN.inv_eq_neg_inv_neg qz144) 

noncomputable def Ns564p1031 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz146) Bool.false 81088139 67108864 379 67108864 81088139 67108864 

noncomputable def Ns564p1032 := @Enclosure.Real.IsNear.recentre' qz144 Bool.true 55539561 67108864 661897216 171798691840000 55539561 67108864 40399 10485760000 

noncomputable abbrev qz147 := qz470

noncomputable def Ns564p1033 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 170833789) qz396) Bool.false 170833789 67108864 63 16777216 Bool.true 55539561 67108864 1 

noncomputable def Ns564p1034 := nat_lit 134930377074414238825737443 

noncomputable def Ns564p1035 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz136 884279719003555 140737488355328 1 500000000000000 13594521 33554432 5 8388608 12021359209867927522155 4722366482869645213696 Ns564p1034 

noncomputable def Ns564p1036 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz1 416247705 33554432 5 8388608 12 1 0 1 13594521 13594521 33554432 5 

noncomputable def Ns564p1037 := @Ns564p1036 8388608 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 832495410 67108864 40 67108864 416247705 33554432 5 8388608 (Ns564p1024 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns564p1038 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 12021359209867927522155 4722366482869645213696 Ns564p1034 Ns564p201 170833789 67108864 63 16777216 (@Ns564p1035 Ns564p201 RS565to576.d55 (Ns564p1037 rfl rfl) rfl) 

noncomputable def Ns564p1039 := nat_lit 9427933736900724300709888 

noncomputable def Ns564p1040 := nat_lit 347774472476015411690815078410637598862962762732589237004209094331616220371562143653285313345 

noncomputable def Ns564p1041 := nat_lit 103823046292430112170150465094596577804594179268385187412746936014776030071662999915707201 

noncomputable def Ns564p1042 := nat_lit 910669809647947858056240199846278650181790273723680139945688894876875701686356255187312294721 

noncomputable def Ns564p1043 := BSN.sin_dyadic_bound_f 133978996599 137438953472 3 2 67108864 20500001 Ns564p1040 Ns564p207 Ns564p1041 Ns564p1042 Ns564p210 Ns564p1041 55539561 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 133978996599) qz371 0 2 Ns564p1040 Ns564p207 Ns564p1041 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 133978996599) qz372 0 2 Ns564p1042 Ns564p210 Ns564p1041 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1044 := @Ns564p1033 10240000 (Ns564p1038 rfl) (Enclosure.sfrac_false_div 170833789 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 170833789) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p1039) qz397) 226375608064910080 72057594037927936 Bool.false 55539561 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 170833789 67108864 226375608064910080 72057594037927936 0 Ns564p1039 Ns564p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 55539561 67108864 Ns564p1039 Ns564p112 133978996599 137438953472 20500001 20480000 (Ns564p1043 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p1045 := @Enclosure.Real.IsNear.inv_image qz146 55539561 67108864 40399 10485760000 40543880 40544259 33554432 (@Enclosure.Real.IsNear.neg qz144 Bool.true 55539561 67108864 40399 10485760000 (Ns564p1032 (Ns564p1044 rfl rfl) rfl)) 

noncomputable def Ns564p1046 := Ns564p1030 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz146) Bool.false 81088139 67108864 379 67108864 (@Ns564p1031 379 67108864 (Ns564p1045 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p1047 := @Enclosure.Real.IsNear.recentre' qz145 Bool.true 11068739 33554432 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz355 qz352 qz471)

noncomputable def Ns564p1048 := @Enclosure.Real.IsNear.cos_image qz148 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 127974359)) qz396) Bool.true 127974359 67108864 

noncomputable def Ns564p1049 := nat_lit 302170913256051923978631923725 

noncomputable def Ns564p1050 := nat_lit 163922850983957964078591484836593 

noncomputable def Ns564p1051 := @Enclosure.Real.IsNear.recentre' qz148 Bool.true Ns564p1049 Ns564p218 Ns564p1050 

noncomputable abbrev qz149 := qz471

noncomputable def Ns564p1052 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz149 884279719003555 140737488355328 1 500000000000000 341714173425295 

noncomputable abbrev qz472 := (@HSub.hSub Real Real Real qz592 qz669 qz662)

noncomputable abbrev qz150 := qz472

noncomputable def Ns564p1053 := @Enclosure.Real.IsNear.subLit_tf qz150 qz31 271345429247631 1125899906842624 151858735 140737488355328 1 16 

noncomputable abbrev qz473 := qz669

noncomputable abbrev qz151 := qz473

noncomputable def Ns564p1054 := @Enclosure.Real.IsNear.subLit_ff_n qz151 qz136 184811001219441 1125899906842624 67972655 140737488355328 13594521 33554432 5 8388608 

noncomputable def Ns564p1055 := @Enclosure.Real.IsNear.mulLit_ff qz136 qz136 13594521 33554432 5 8388608 13594521 33554432 5 8388608 184811001219441 1125899906842624 

noncomputable def Ns564p1056 := nat_lit 2219553693932372774659454729831975141704827415992590079629094617295633190208445023606785779358692939361 

noncomputable def Ns564p1057 := nat_lit 19296367207956456665748860900664811888156302166114523393144827852189581859653663156315143909021281 

noncomputable def Ns564p1058 := nat_lit 13395084867569518852953335371215243721298156197688558809529636162262597276985770639387656208843097118305 

noncomputable def Ns564p1059 := BSN.cos_dyadic_bound_t 127974359 67108864 4 3 33554432 10240000 Ns564p1056 Ns564p665 Ns564p1057 Ns564p1058 Ns564p668 Ns564p1057 11068739 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 127974359) (BSN.cosEvenQ 67108864) 0 3 Ns564p1056 Ns564p665 Ns564p1057 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 127974359) (BSN.cosOddQ 67108864) 0 3 Ns564p1058 Ns564p668 Ns564p1057 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1060 := @Ns564p1047 592068608 85899345920000 11068739 33554432 36137 5242880000 (@Ns564p1048 57 8388608 Bool.true 11068739 33554432 1 10240000 (@Ns564p1051 Ns564p221 127974359 67108864 57 8388608 (@Ns564p1052 1125899906842624 151858735 140737488355328 Ns564p1049 Ns564p218 Ns564p1050 Ns564p221 RS565to576.d55 (@Ns564p1053 0 1 5467426774804720 341714173425295 1125899906842624 151858735 140737488355328 (@Ns564p1054 9104841754200445550592 271345429247631 1125899906842624 151858735 140737488355328 (@Ns564p1055 67972655 140737488355328 (Ns564p1037 rfl rfl) (Ns564p1037 rfl rfl) rfl) (Ns564p1037 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 127974359 67108864) (BSN.cos_neg_of_bound 127974359 67108864 Bool.true 11068739 33554432 1 10240000 (Ns564p1059 rfl rfl)) rfl rfl) 

noncomputable def Ns564p1061 := @Ns564p1022 137205323073002626363 Ns564p235 (Ns564p1023 qz33 (@Enclosure.Real.IsNear.of_eq qz667 (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 9526841 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz135 (BSN.t_div_two_pi_nonneg qz134 966905 1000 qz137)) Ns564p1027) rfl) (@Ns564p1028 2251799813685248 14343090650489 1407374883553280000 (BSN.correction_mk qz136 (BSN.cos_two_pi_p_ne_zero_mk qz134 966905 1000 12 qz137 rfl rfl (@BSN.floor_sqrt_eq_dec qz134 966905 1000 12 qz137 rfl rfl rfl))) (@Ns564p1029 67108864 11068739 33554432 36137 5242880000 897543446586721 2251799813685248 14343090650489 1407374883553280000 Ns564p1046 (Ns564p1060 rfl) rfl)) 

noncomputable def Ns564p1062 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (hardyZApproximantRS₀ qz134) Bool.true 129220237587835819045017 75557863725914323419136 46583743073819237506363 Ns564p235 (@Eq.refl Real (hardyZApproximantRS₀ qz134)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HMul.hMul Real Real Real qz5 qz663 (Zeta.RiemannSiegel.correction qz136))) Bool.true 129220237587835819045017 75557863725914323419136 46583743073819237506363 Ns564p235 (BSN.hardyZApproximantRS₀_eq qz134 12 (@BSN.floor_sqrt_eq_dec qz134 966905 1000 12 qz137 rfl rfl rfl)) (@Ns564p940 129220237587835819045017 75557863725914323419136 46583743073819237506363 Ns564p235 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12)) Bool.true 214352063 134217728 132009 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (Ns564p1021 (Ns564p1020 rfl rfl rfl rfl) rfl rfl)) (Ns564p1061 rfl) rfl rfl)) 

theorem RS565to576.d65 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz134) Bool.true 129220237587835819045017 75557863725914323419136 46583743073819237506363 Ns564p235 := Ns564p1062 

noncomputable def Ns564p1063 := nat_lit 1370101594093615274739856572416 

noncomputable abbrev qz774 := (Enclosure.sfrac Bool.false 968152 1000)

noncomputable abbrev qz670 := qz774

noncomputable abbrev qz474 := qz670

noncomputable abbrev qz152 := qz474

noncomputable abbrev qz775 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 968152 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz671 := qz775

noncomputable abbrev qz475 := qz671

noncomputable abbrev qz153 := qz475

noncomputable abbrev qz776 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 968152 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz672 := qz776

noncomputable abbrev qz476 := qz672

noncomputable abbrev qz154 := qz476

noncomputable abbrev qz673 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz153 qz9))

noncomputable def Ns564p1064 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (@HMul.hMul Real Real Real qz5 qz673 (Zeta.RiemannSiegel.correction qz154)) 305215853 134217728 132179 134217728 530775786593954093499 4722366482869645213696 261022331590555203 92233720368547758080000 Ns564p1063 

noncomputable def Ns564p1065 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin BSN.quadSignPos 11 12 968152 1000 287 536870912 268435456 9007199254740992 Bool.false 1049083342225 4504 1334074092 54 154981288 8 

noncomputable def Ns564p1066 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 9 10 11 968152 1000 175 233 536870912 268435456 9007199254740992 Bool.false 1049083342225 4504 

noncomputable def Ns564p1067 := Ns564p1066 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.false 602974158 212858 Bool.true 157304315 Bool.true 784667916 28296951008113761 1 Bool.false 155063187 Bool.false Bool.false 533670845 Bool.true Bool.false 491101637 

noncomputable def Ns564p1068 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 968152 1000 37 110 536870912 268435456 9007199254740992 Bool.false 1049083342225 4504 

noncomputable def Ns564p1069 := Ns564p1068 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.false 930846415 173834 Bool.true 550841986 Bool.true 209244364 28296951008113761 1 Bool.false 459156087 Bool.true Bool.false 496608191 Bool.true Bool.false 602974158 

noncomputable def Ns564p1070 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 968152 1000 139 44 536870912 268435456 9007199254740992 Bool.false 1049083342225 4504 

noncomputable def Ns564p1071 := Ns564p1070 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.false 636004071 129170 Bool.false 555021805 Bool.false 546634063 28296951008113761 1 Bool.false 461308233 Bool.false Bool.false 281809673 Bool.false Bool.false 930846415 

noncomputable def Ns564p1072 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 968152 1000 389 252 536870912 268435456 9007199254740992 Bool.false 1049083342225 4504 

noncomputable def Ns564p1073 := Ns564p1072 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 604211122 76280 Bool.false 475986674 Bool.false 26209488 28296951008113761 1 Bool.false 416033959 Bool.true Bool.false 536231278 Bool.false Bool.false 636004071 

noncomputable def Ns564p1074 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 968152 1000 816 566 536870912 268435456 9007199254740992 Bool.false 1049083342225 4504 

noncomputable def Ns564p1075 := Ns564p1074 372130544 53 379625064 8 589812976 53 309962568 8 Bool.false 536870800 4565 Bool.false 659488859 Bool.false 738521087 28296951008113761 1 Bool.false 180255048 Bool.false Bool.false 104129586 Bool.true Bool.false 604211122 

noncomputable def Ns564p1076 := nat_lit 7961851745489040985386339860905708288846212667789144913 

noncomputable def Ns564p1077 := nat_lit 4074496692268193148885779077316009226394914521088000 

noncomputable def Ns564p1078 := nat_lit 408281090050472628474997432975360000 

noncomputable def Ns564p1079 := nat_lit 2371669218565915448641043084973940408320 

noncomputable abbrev qz674 := (@Eq.refl Real qz774)

noncomputable abbrev qz477 := qz674

noncomputable abbrev qz155 := qz477

noncomputable def Ns564p1080 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz152 968152 1000 3749274180416 16000000 1936304 4000 2000 Ns564p1078 Ns564p1079 qz155 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns564p1081 := nat_lit 10435758319847395800365583382486329968356507867924588020367360 

noncomputable abbrev qz675 := (@HSub.hSub Real Real Real qz745 qz746 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz747 (@Nat.cast Real Real.instNatCast 1936304))))

noncomputable abbrev qz478 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 968152 4000) (Real.log (Enclosure.sfrac Bool.false 3749274180416 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz675))

noncomputable abbrev qz676 := (Enclosure.sfrac Bool.false 968152 2000)

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz478 qz676) (@HMul.hMul Real Real Real qz355 qz676 (Real.log Real.pi)))

noncomputable def Ns564p1082 := @Enclosure.Real.IsNear.addLit_ft_p qz156 (Enclosure.sfrac Bool.true Ns564p1078 Ns564p1079) 4400174846273419645573 2251799813685248000 17180578788379133 2048000000000000000000 Ns564p1078 Ns564p1079 0 1 Ns564p1081 

noncomputable def Ns564p1083 := nat_lit 36911341916847978226210832384000 

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz359 qz478 qz676)

noncomputable def Ns564p1084 := @Enclosure.Real.IsNear.subLit_ff_p qz157 (@HMul.hMul Real Real Real qz5 qz676 (Real.log Real.pi)) 5647978779131546079877 2251799813685248000 5957967213917 2000000000000000000 4648431885459 8388608000 363057 67108864000 Ns564p1083 4400174846273419645573 2251799813685248000 

noncomputable abbrev qz158 := qz478

noncomputable def Ns564p1085 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz676 269520841029641847629 90071992547409920 5957967213917 2000000000000000000 968152 2000 0 1 451838302330523686390160 5647978779131546079877 2251799813685248000 5957967213917 2000000000000000000 

noncomputable def Ns564p1086 := nat_lit 606906979614838857221836710181076992 

noncomputable def Ns564p1087 := nat_lit 119581952623578763703091200 

noncomputable def Ns564p1088 := nat_lit 110490691456149819347122120304899398817152211232780435592126098921195606418422330171477976490241048170788929713190843493985833118030810875047846346963112762350941635577996272657131110400 

noncomputable def Ns564p1089 := nat_lit 3090575353986115536449117580846102834912467477997080410530680220298085162994216159624046151412765031774593054263215251563016709502992000209755043267954764598257024580831681643271946240 

noncomputable def Ns564p1090 := nat_lit 152530997873901394137932267052798039829377659479561766360547062561987763591525682334559910330220713753949596652718655869781038901525200615898424821984696971677898147936715407360 

noncomputable def Ns564p1091 := BSN.log_dyadic_bound 1652122180416 5846426180416 8 7 Ns564p1088 268435456 81920000 Ns564p1089 Ns564p1090 155956177 7498548360832 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1652122180416) (BSN.artanhQ 5846426180416) 0 7 Ns564p1089 Ns564p1088 Ns564p1090 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz479 := (Real.log (Enclosure.sfrac Bool.false 3749274180416 16000000))

noncomputable def Ns564p1092 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 968152 4000) qz479 968152 4000 0 1 55684685997468775 4503599627370496 48828193 4000000000000000 269556200589106947269 90071992547409920 5909139088667 2000000000000000000 (Enclosure.Real.IsNear.const Bool.false 968152 4000) (BSN.isNear_log_sfrac 3749274180416 16000000 55684685997468775 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3749274180416) qz362)) Bool.false Ns564p1087 Ns564p112 1000001392640000 81920000000000000000000 55684685997468775 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3749274180416 16000000 17 7498548360832 4194304000000 155956177 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns564p1091 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p1093 := BSN.arctan_dyadic_bound_f 1000 1936304 1 0 33554432 10240000 0 1 1 0 1 1 17329 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1936304) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1936304) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns564p1094 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1936304))) 884279719003555 562949953421312 1 2000000000000000 17329 33554432 1 10240000 29661748340541056090112 883988986627491 562949953421312 195312501 2000000000000000 qz17 (Ns564p1093 rfl) rfl rfl 

noncomputable abbrev qz480 := (@HMul.hMul Real Real Real qz588 qz593 qz675)

noncomputable abbrev qz159 := qz480

noncomputable abbrev qz481 := qz675

noncomputable abbrev qz160 := qz481

noncomputable def Ns564p1095 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 968152 4000) qz479) qz159 269556200589106947269 90071992547409920 5909139088667 2000000000000000000 883988986627491 2251799813685248 195312501 8000000000000000 Ns564p1086 269520841029641847629 90071992547409920 5957967213917 2000000000000000000 (Ns564p1092 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz160 1 4 0 1 883988986627491 562949953421312 195312501 2000000000000000 883988986627491 2251799813685248 195312501 8000000000000000 qz369 Ns564p1094 rfl) 

noncomputable def Ns564p1096 := @Ns564p1082 Ns564p1076 Ns564p1077 17180578788379133 2048000000000000000000 (@Ns564p1084 17180578788379133 2048000000000000000000 (Ns564p1085 (Ns564p1095 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 968152 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz676 (Real.log Real.pi) 968152 2000 0 1 38410761 33554432 3 268435456 4648431885459 8388608000 363057 67108864000 (Enclosure.Real.IsNear.const Bool.false 968152 2000) RS565to576.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns564p1078 Ns564p1079) 

noncomputable def Ns564p1097 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns564p1076 Ns564p1077 17180578788379133 2048000000000000000000 65567708889 33554432 141 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz370 qz156 (Enclosure.sfrac Bool.true Ns564p1078 Ns564p1079)) Bool.false Ns564p1076 Ns564p1077 17180578788379133 2048000000000000000000 Ns564p1080 (Ns564p1096 rfl rfl)) 

noncomputable def Ns564p1098 := nat_lit 7592848781264521032368128 

noncomputable def Ns564p1099 := nat_lit 14357206246651226800260377289119841615849757554616818318157939063103200171472597020115909275560400512641358302345965252012438655695944870400000 

noncomputable def Ns564p1100 := nat_lit 10201389939274529409891966917782018064969517344767020053510741907633541037588196448201093646420223193227310286605230686308561000000000000 

noncomputable def Ns564p1101 := nat_lit 71696971483455004333437012975419272680942152733842783871538215248809418205428083372249349715815189622398482374975455205747640859732940352000000 

noncomputable def Ns564p1102 := BSN.sin_dyadic_bound_f 215801741810 137438953472 4 3 67108864 20500001 Ns564p1099 Ns564p124 Ns564p1100 Ns564p1101 Ns564p127 Ns564p1100 67108850 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215801741810) qz371 0 3 Ns564p1099 Ns564p124 Ns564p1100 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215801741810) qz372 0 3 Ns564p1101 Ns564p127 Ns564p1100 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1103 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz152) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 65567708889) qz383) Bool.false 65567708889 33554432 141 16777216 Bool.false 67108850 67108864 1 10240000 (Ns564p1097 rfl) (Enclosure.sfrac_false_div 65567708889 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 65567708889) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p1098) qz416) 226375608064910080 72057594037927936 Bool.false 67108850 67108864 310 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q3 65567708889 33554432 226375608064910080 72057594037927936 310 Ns564p1098 Ns564p435 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108850 67108864 Ns564p1098 Ns564p435 215801741810 137438953472 20500001 20480000 (Ns564p1102 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p1104 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns564p1076 Ns564p1077 17180578788379133 2048000000000000000000 1049083342225 536870912 4504 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz370 qz156 (Enclosure.sfrac Bool.true Ns564p1078 Ns564p1079)) Bool.false Ns564p1076 Ns564p1077 17180578788379133 2048000000000000000000 Ns564p1080 (Ns564p1096 rfl rfl)) 

noncomputable def Ns564p1105 := Ns564p1075 76280 BSN.abs_quadSignPos (BSN.cos_quad_nat0 816 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 180255048 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 566 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 104129586 536870912) qz155 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) Bool.false 33554425 33554432 89149 10485760000 536870800 536870912 4565 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 33554425 33554432 89149 10485760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz152) qz152) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 67108850 67108864 1460617216 171798691840000 33554425 33554432 89149 10485760000 (Ns564p1103 rfl rfl) rfl)) rfl) (Ns564p1104 rfl) RS565to576.d7 

noncomputable def Ns564p1106 := nat_lit 26091730884453731247079602229184308161394107214135367694692189438641222971498479997766204310475373528062037290961 

noncomputable def Ns564p1107 := nat_lit 6768455202959135971833359762596362898765177441532692963872685857075073955841028770357036378729482300387281 

noncomputable def Ns564p1108 := nat_lit 158146971356391114148908285351607444616740406675227822119850579719698097329746684630049191967808491931675881336785 

noncomputable def Ns564p1109 := BSN.cos_dyadic_bound_f 659488859 536870912 4 3 536870912 268435456 Ns564p1106 Ns564p133 Ns564p1107 Ns564p1108 Ns564p136 Ns564p1107 180255048 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 659488859) qz373 0 3 Ns564p1106 Ns564p133 Ns564p1107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 659488859) qz374 0 3 Ns564p1108 Ns564p136 Ns564p1107 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1110 := nat_lit 41064000961034169217379294294339459842875220047839653248628515626884166712393427660144888398864710826974159093761 

noncomputable def Ns564p1111 := nat_lit 26324177036651759293548166143451986111618816542876026742550925244533558002772236260698417531505604018094081 

noncomputable def Ns564p1112 := nat_lit 248768242102692896335274856032741776694674874233609227716975901642027441891929534287071213051219484677122281488385 

noncomputable def Ns564p1113 := BSN.cos_dyadic_bound_f 738521087 536870912 4 3 536870912 268435456 Ns564p1110 Ns564p133 Ns564p1111 Ns564p1112 Ns564p136 Ns564p1111 104129586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 738521087) qz373 0 3 Ns564p1110 Ns564p133 Ns564p1111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 738521087) qz374 0 3 Ns564p1112 Ns564p136 Ns564p1111 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1114 := nat_lit 12898202404016188556966114694371805480700413673044494860515970464675447040 

noncomputable def Ns564p1115 := nat_lit 2634864905594007952468268900082435148706928380981077555066112359710976 

noncomputable def Ns564p1116 := nat_lit 33776740324480960683940589859421261840165081735833040985309815606519972096 

noncomputable def Ns564p1117 := BSN.sin_dyadic_bound_f 475986674 536870912 3 2 536870912 268435456 Ns564p1114 Ns564p143 Ns564p1115 Ns564p1116 Ns564p146 Ns564p1115 416033959 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 475986674) qz375 0 2 Ns564p1114 Ns564p143 Ns564p1115 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 475986674) qz376 0 2 Ns564p1116 Ns564p146 Ns564p1115 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1118 := nat_lit 471882800855380102864515956736 

noncomputable def Ns564p1119 := BSN.cos_dyadic_bound_f 26209488 536870912 2 1 536870912 268435456 Ns564p1118 Ns564p163 Ns564p1118 Ns564p1118 Ns564p164 Ns564p1118 536231278 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 26209488) qz373 0 1 Ns564p1118 Ns564p163 Ns564p1118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 26209488) qz374 0 1 Ns564p1118 Ns564p164 Ns564p1118 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1120 := Ns564p1073 129170 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 389 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 416033959 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 252 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536231278 536870912) qz155 rfl rfl (Ns564p1105 RS565to576.d9 RS565to576.d11 RS565to576.d13 RS565to576.d17 (Ns564p1109 rfl rfl) (Ns564p1113 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns564p1104 rfl) RS565to576.d19 RS565to576.d21 RS565to576.d23 RS565to576.d25 RS565to576.d17 (Ns564p1117 rfl rfl) (Ns564p1119 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns564p1121 := nat_lit 23848742248338987973480653143042820878109903669140861190542337833310030625 

noncomputable def Ns564p1122 := nat_lit 9004930469068524874285182364729721601138017825450720018550406125390625 

noncomputable def Ns564p1123 := nat_lit 62446412191556952795033820317474016083886000437937240047580850810656590625 

noncomputable def Ns564p1124 := BSN.sin_dyadic_bound_f 555021805 536870912 3 2 536870912 268435456 Ns564p1121 Ns564p143 Ns564p1122 Ns564p1123 Ns564p146 Ns564p1122 461308233 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 555021805) qz375 0 2 Ns564p1121 Ns564p143 Ns564p1122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 555021805) qz376 0 2 Ns564p1123 Ns564p146 Ns564p1122 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1125 := nat_lit 12306916334640134690345471251645405121838629038868175699337244638037003868923459707735883633807795576182302327361 

noncomputable def Ns564p1126 := nat_lit 711803780605630463525295471496943412326995518405092711063693338342127508375118584449591202664281244975681 

noncomputable def Ns564p1127 := nat_lit 74630133426789638067211792695853775176192238890716352625623177237774331415793922568625313891288583139321261867585 

noncomputable def Ns564p1128 := BSN.cos_dyadic_bound_f 546634063 536870912 4 3 536870912 268435456 Ns564p1125 Ns564p133 Ns564p1126 Ns564p1127 Ns564p136 Ns564p1126 281809673 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 546634063) qz373 0 3 Ns564p1125 Ns564p133 Ns564p1126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 546634063) qz374 0 3 Ns564p1127 Ns564p136 Ns564p1126 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1129 := Ns564p1071 173834 BSN.abs_quadSignPos (BSN.cos_quad_nat3 139 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 461308233 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 281809673 536870912) qz155 rfl rfl (Ns564p1120 rfl rfl) (Ns564p1104 rfl) RS565to576.d27 RS565to576.d29 RS565to576.d31 RS565to576.d33 RS565to576.d17 (Ns564p1124 rfl rfl) (Ns564p1128 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1130 := nat_lit 23138145907055429292198973661034331169810056221888053985910758522161332480 

noncomputable def Ns564p1131 := nat_lit 8476494476797787952523758055678196500324076594724391116507946224845056 

noncomputable def Ns564p1132 := nat_lit 60586182098849404108597987789666435983740098742839159044149068978439454976 

noncomputable def Ns564p1133 := BSN.sin_dyadic_bound_f 550841986 536870912 3 2 536870912 268435456 Ns564p1130 Ns564p143 Ns564p1131 Ns564p1132 Ns564p146 Ns564p1131 459156087 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 550841986) qz375 0 2 Ns564p1130 Ns564p143 Ns564p1131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 550841986) qz376 0 2 Ns564p1132 Ns564p146 Ns564p1131 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1134 := nat_lit 267552996995053490051519882052537951381755589123553827658052698531495936 

noncomputable def Ns564p1135 := nat_lit 3674769919804375581507128287399002407907308580141718908363048288256 

noncomputable def Ns564p1136 := nat_lit 802651641445320861403396631901039056140450952753501199536341369497911296 

noncomputable def Ns564p1137 := BSN.cos_dyadic_bound_f 209244364 536870912 3 2 536870912 268435456 Ns564p1134 Ns564p170 Ns564p1135 Ns564p1136 Ns564p173 Ns564p1135 496608191 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 209244364) qz373 0 2 Ns564p1134 Ns564p170 Ns564p1135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 209244364) qz374 0 2 Ns564p1136 Ns564p173 Ns564p1135 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1138 := Ns564p1069 212858 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 459156087 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 496608191 536870912) qz155 rfl rfl (Ns564p1129 rfl) (Ns564p1104 rfl) RS565to576.d35 RS565to576.d37 RS565to576.d39 RS565to576.d41 RS565to576.d17 (Ns564p1133 rfl rfl) (Ns564p1137 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1139 := nat_lit 612297580771219274006812089600625 

noncomputable def Ns564p1140 := BSN.sin_dyadic_bound_f 157304315 536870912 2 1 536870912 268435456 Ns564p1139 Ns564p463 Ns564p1139 Ns564p1139 Ns564p464 Ns564p1139 155063187 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 157304315) qz375 0 1 Ns564p1139 Ns564p463 Ns564p1139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 157304315) qz376 0 1 Ns564p1139 Ns564p464 Ns564p1139 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1141 := nat_lit 135974247920399026285711490289438064006516436205449528790770030476245328944525164395354647911255217378355845267456 

noncomputable def Ns564p1142 := nat_lit 54479202711059910898239005870709647613611260278224224388350269722433373146221760436171368381619940628627456 

noncomputable def Ns564p1143 := nat_lit 679237779010600858015234117062652067888963531400537230946287633795333993123721017884894799470542005013649047945216 

noncomputable def Ns564p1144 := BSN.sin_dyadic_bound_f 784667916 536870912 4 3 536870912 268435456 Ns564p1141 Ns564p181 Ns564p1142 Ns564p1143 Ns564p184 Ns564p1142 533670845 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 784667916) qz375 0 3 Ns564p1141 Ns564p181 Ns564p1142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 784667916) qz376 0 3 Ns564p1143 Ns564p184 Ns564p1142 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1145 := Ns564p1067 247955 BSN.abs_quadSignPos qz625 (BSN.sfrac_eq_quadSignPos_mul Bool.false 155063187 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 533670845 536870912) qz155 rfl rfl (Ns564p1138 rfl) (Ns564p1104 rfl) RS565to576.d43 RS565to576.d45 RS565to576.d47 RS565to576.d49 RS565to576.d17 (Ns564p1140 rfl rfl) (Ns564p1144 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1146 := nat_lit 12449662188692462380813521800489469481183500268489758751270050199507107840 

noncomputable def Ns564p1147 := nat_lit 2454829205087070746761480830980979278433922952571316433822907147288576 

noncomputable def Ns564p1148 := nat_lit 32602283627862498597112086127555593722363131494597586026719180101423005696 

noncomputable def Ns564p1149 := BSN.sin_dyadic_bound_f 471794268 536870912 3 2 536870912 268435456 Ns564p1146 Ns564p143 Ns564p1147 Ns564p1148 Ns564p146 Ns564p1147 413371471 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 471794268) qz375 0 2 Ns564p1146 Ns564p143 Ns564p1147 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 471794268) qz376 0 2 Ns564p1148 Ns564p146 Ns564p1147 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1150 := Ns564p1065 Bool.false 491101637 247955 Bool.true 471794268 28296951008113761 1 Bool.false 413371471 Bool.false Bool.false 610431706 264358 BSN.abs_quadSignPos qz377 (BSN.sfrac_eq_quadSignPos_mul Bool.false 413371471 536870912) qz155 rfl (Ns564p1145 rfl) (Ns564p1104 rfl) RS565to576.d51 RS565to576.d53 RS565to576.d17 (Ns564p1149 rfl rfl) rfl 

noncomputable def Ns564p1151 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) 610431706 536870912 264358 536870912 610431706 536870912 264358 536870912 655446053427871744 305215853 134217728 132179 134217728 (Ns564p1150 rfl rfl rfl rfl) 

noncomputable def Ns564p1152 := @Enclosure.Real.IsNear.mulLit_ff qz673 (Zeta.RiemannSiegel.correction qz154) 2380943 8388608 1 33554432 222926708700693 562949953421312 3493523968983 351843720888320000 530775786593954093499 4722366482869645213696 

noncomputable abbrev qz677 := (@HPow.hPow Real Real Real qz7 qz153 qz9)

noncomputable def Ns564p1153 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz677 1 1 0 1 2380943 8388608 1 33554432 2380943 8388608 1 33554432 

noncomputable def Ns564p1154 := @Enclosure.Real.IsNear.sqrt_image qz153 1292568480433 8388608000 121019 8388608000 416516012 416516052 33554432 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz152 qz3) Bool.false 1292568480433 8388608000 121019 8388608000 (BSN.t_div_two_pi_mk qz152 968152 1000 qz155) (@Enclosure.Real.IsNear.mulLit_ff qz152 qz3 968152 1000 0 1 10680707 67108864 1 67108864 1292568480433 8388608000 121019 8388608000 (Enclosure.Real.IsNear.const Bool.false 968152 1000) RS565to576.d56 rfl)) 

noncomputable abbrev qz777 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 968152 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz678 := qz777

noncomputable abbrev qz482 := qz678

noncomputable abbrev qz161 := qz482

noncomputable def Ns564p1155 := @Enclosure.Real.IsNear.sqrt_image qz161 6508063 524288 5 8388608 118219956 118219963 33554432 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 833032064 67108864 40 67108864 6508063 524288 5 8388608 (Ns564p1154 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns564p1156 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz161) 236439919 67108864 7 67108864 9523771 9523773 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz161) Bool.false 236439919 67108864 7 67108864 236439919 67108864 7 67108864 (Ns564p1155 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns564p1157 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 19047544 67108864 2 67108864 2380943 8388608 1 33554432 (Ns564p1156 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz483 := (@HMul.hMul Real Real Real qz588 qz586 qz672)

noncomputable abbrev qz162 := (Real.cos qz483)

noncomputable abbrev qz679 := (@HMul.hMul Real Real Real qz741 qz776 qz776)

noncomputable abbrev qz484 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz679 qz672) qz604)

noncomputable abbrev qz163 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz484))

noncomputable def Ns564p1158 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz162) qz163) Bool.false 222926708700693 

noncomputable def Ns564p1159 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz162) qz163 39256389 33554432 89 

noncomputable abbrev qz164 := (@Neg.neg Real Real.instNeg (Real.cos qz483))

noncomputable def Ns564p1160 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz162) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz164)) Bool.true 39256389 33554432 89 16777216 (BSN.inv_eq_neg_inv_neg qz162) 

noncomputable def Ns564p1161 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz164) Bool.false 78512778 67108864 356 67108864 39256389 33554432 

noncomputable def Ns564p1162 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true 57361359 67108864 2657828864 687194767360000 57361359 67108864 162221 41943040000 

noncomputable abbrev qz165 := qz483

noncomputable def Ns564p1163 := @Enclosure.Real.IsNear.cos_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 174205685) qz396) Bool.false 174205685 67108864 253 67108864 Bool.true 57361359 67108864 1 

noncomputable def Ns564p1164 := nat_lit 134930377074990466670554339 

noncomputable def Ns564p1165 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 216607 524288 5 8388608 191541177094203037885 73786976294838206464 Ns564p1164 

noncomputable def Ns564p1166 := @Enclosure.Real.IsNear.subLit_ff_p qz161 qz1 6508063 524288 5 8388608 12 1 0 1 216607 216607 524288 5 

noncomputable def Ns564p1167 := @Ns564p1166 8388608 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 833032064 67108864 40 67108864 6508063 524288 5 8388608 (Ns564p1154 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns564p1168 := @Enclosure.Real.IsNear.recentre' qz165 Bool.false 191541177094203037885 73786976294838206464 Ns564p1164 Ns564p201 174205685 67108864 253 67108864 (@Ns564p1165 Ns564p201 RS565to576.d55 (Ns564p1167 rfl rfl) rfl) 

noncomputable def Ns564p1169 := nat_lit 9913875163112950412083200 

noncomputable def Ns564p1170 := nat_lit 425240153659145012836446400678681873681158465359906530959376039598185209342802043263192513345 

noncomputable def Ns564p1171 := nat_lit 155206234640213368405790865129219553406483397420075239245123478790726153238381651922107201 

noncomputable def Ns564p1172 := nat_lit 1113472925679771831022797864186338551792756912346789364030064189505776277364000352538582694721 

noncomputable def Ns564p1173 := BSN.sin_dyadic_bound_f 140884639607 137438953472 3 2 67108864 20500001 Ns564p1170 Ns564p207 Ns564p1171 Ns564p1172 Ns564p210 Ns564p1171 57361359 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 140884639607) qz371 0 2 Ns564p1170 Ns564p207 Ns564p1171 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 140884639607) qz372 0 2 Ns564p1172 Ns564p210 Ns564p1171 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1174 := @Ns564p1163 10240000 (Ns564p1168 rfl) (Enclosure.sfrac_false_div 174205685 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 174205685) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p1169) qz397) 226375608064910080 72057594037927936 Bool.false 57361359 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 174205685 67108864 226375608064910080 72057594037927936 0 Ns564p1169 Ns564p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 57361359 67108864 Ns564p1169 Ns564p112 140884639607 137438953472 20500001 20480000 (Ns564p1173 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p1175 := @Enclosure.Real.IsNear.inv_image qz164 57361359 67108864 162221 41943040000 39256211 39256567 33554432 (@Enclosure.Real.IsNear.neg qz162 Bool.true 57361359 67108864 162221 41943040000 (Ns564p1162 (Ns564p1174 rfl rfl) rfl)) 

noncomputable def Ns564p1176 := Ns564p1160 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz164) Bool.false 39256389 33554432 89 16777216 (@Ns564p1161 89 16777216 (Ns564p1175 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p1177 := @Enclosure.Real.IsNear.recentre' qz163 Bool.true 11357474 33554432 

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz355 qz352 qz484)

noncomputable def Ns564p1178 := @Enclosure.Real.IsNear.cos_image qz166 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 128587055)) qz396) Bool.true 128587055 67108864 

noncomputable def Ns564p1179 := nat_lit 74125390804066838630443805 

noncomputable def Ns564p1180 := nat_lit 38685626227668133590597632 

noncomputable def Ns564p1181 := nat_lit 2067138368941059279312567078572047 

noncomputable def Ns564p1182 := @Enclosure.Real.IsNear.recentre' qz166 Bool.true Ns564p1179 Ns564p1180 Ns564p1181 

noncomputable abbrev qz167 := qz484

noncomputable def Ns564p1183 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz167 884279719003555 140737488355328 1 500000000000000 83825727551 

noncomputable abbrev qz485 := (@HSub.hSub Real Real Real qz592 qz679 qz672)

noncomputable abbrev qz168 := qz485

noncomputable def Ns564p1184 := @Enclosure.Real.IsNear.subLit_tf qz168 qz31 66645858367 274877906944 76600185 70368744177664 1 16 

noncomputable abbrev qz486 := qz679

noncomputable abbrev qz169 := qz486

noncomputable def Ns564p1185 := @Enclosure.Real.IsNear.subLit_ff_n qz169 qz154 46918592449 274877906944 34657145 70368744177664 216607 524288 5 8388608 

noncomputable def Ns564p1186 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 216607 524288 5 8388608 216607 524288 5 8388608 46918592449 274877906944 

noncomputable def Ns564p1187 := nat_lit 2262707257021826989414122436467834639777839077418641411409424237391850851701818877073217627102491890625 

noncomputable def Ns564p1188 := nat_lit 20434640355303470379888952605956289602158054438348314186888746802387758943495141856082402587890625 

noncomputable def Ns564p1189 := nat_lit 13654146666357189034327728941012112316427030710047902899499614955950036319746552237408739828545205490625 

noncomputable def Ns564p1190 := BSN.cos_dyadic_bound_t 128587055 67108864 4 3 33554432 10240000 Ns564p1187 Ns564p665 Ns564p1188 Ns564p1189 Ns564p668 Ns564p1188 11357474 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 128587055) (BSN.cosEvenQ 67108864) 0 3 Ns564p1187 Ns564p665 Ns564p1188 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 128587055) (BSN.cosOddQ 67108864) 0 3 Ns564p1189 Ns564p668 Ns564p1188 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1191 := @Ns564p1177 1194377216 171798691840000 5678737 16777216 72899 10485760000 (@Ns564p1178 115 16777216 Bool.true 11357474 33554432 1 10240000 (@Ns564p1182 Ns564p525 128587055 67108864 115 16777216 (@Ns564p1183 274877906944 76600185 70368744177664 Ns564p1179 Ns564p1180 Ns564p1181 Ns564p525 RS565to576.d55 (@Ns564p1184 0 1 1341211640816 83825727551 274877906944 76600185 70368744177664 (@Ns564p1185 34941623791517696 66645858367 274877906944 76600185 70368744177664 (@Ns564p1186 34657145 70368744177664 (Ns564p1167 rfl rfl) (Ns564p1167 rfl rfl) rfl) (Ns564p1167 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 128587055 67108864) (BSN.cos_neg_of_bound 128587055 67108864 Bool.true 11357474 33554432 1 10240000 (Ns564p1190 rfl rfl)) rfl rfl) 

noncomputable def Ns564p1192 := @Ns564p1152 261022331590555203 92233720368547758080000 (Ns564p1153 qz33 (@Enclosure.Real.IsNear.of_eq qz677 (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 2380943 8388608 1 33554432 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz152 968152 1000 qz155)) Ns564p1157) rfl) (@Ns564p1158 562949953421312 3493523968983 351843720888320000 (BSN.correction_mk qz154 (BSN.cos_two_pi_p_ne_zero_mk qz152 968152 1000 12 qz155 rfl rfl (@BSN.floor_sqrt_eq_dec qz152 968152 1000 12 qz155 rfl rfl rfl))) (@Ns564p1159 16777216 5678737 16777216 72899 10485760000 222926708700693 562949953421312 3493523968983 351843720888320000 Ns564p1176 (Ns564p1191 rfl) rfl)) 

noncomputable def Ns564p1193 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (hardyZApproximantRS₀ qz152) Bool.false 10208052352768296560197 4722366482869645213696 91093739486467995203 92233720368547758080000 (@Eq.refl Real (hardyZApproximantRS₀ qz152)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (@HMul.hMul Real Real Real qz5 qz673 (Zeta.RiemannSiegel.correction qz154))) Bool.false 10208052352768296560197 4722366482869645213696 91093739486467995203 92233720368547758080000 (BSN.hardyZApproximantRS₀_eq qz152 12 (@BSN.floor_sqrt_eq_dec qz152 968152 1000 12 qz155 rfl rfl rfl)) (@Ns564p1064 10208052352768296560197 4722366482869645213696 91093739486467995203 92233720368547758080000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12)) Bool.false 305215853 134217728 132179 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (Ns564p1151 (Ns564p1150 rfl rfl rfl rfl) rfl rfl)) (Ns564p1192 rfl) rfl rfl)) 

theorem RS565to576.d66 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz152) Bool.false 10208052352768296560197 4722366482869645213696 91093739486467995203 92233720368547758080000 := Ns564p1193 

noncomputable def Ns564p1194 := nat_lit 128958294426025674783067436220416 

noncomputable abbrev qz778 := (Enclosure.sfrac Bool.false 969399 1000)

noncomputable abbrev qz680 := qz778

noncomputable abbrev qz487 := qz680

noncomputable abbrev qz170 := qz487

noncomputable abbrev qz779 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 969399 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz681 := qz779

noncomputable abbrev qz488 := qz681

noncomputable abbrev qz171 := qz488

noncomputable abbrev qz780 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 969399 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz682 := qz780

noncomputable abbrev qz489 := qz682

noncomputable abbrev qz172 := qz489

noncomputable abbrev qz683 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz171 qz9))

noncomputable def Ns564p1195 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HMul.hMul Real Real Real qz5 qz683 (Zeta.RiemannSiegel.correction qz172)) 823392353 268435456 132353 134217728 16878396362654086612525 151115727451828646838272 2083807037068178607 755578637259143234191360 Ns564p1194 

noncomputable def Ns564p1196 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin BSN.quadSignPos 11 12 969399 1000 287 536870912 268435456 9007199254740992 Bool.false 1050769809590 4511 1334074092 54 154981288 8 

noncomputable def Ns564p1197 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 9 10 11 969399 1000 175 233 536870912 268435456 9007199254740992 Bool.false 1050769809590 4511 

noncomputable def Ns564p1198 := Ns564p1197 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.true 785894499 213139 Bool.true 12367072 Bool.true 703538745 28296951008113761 1 Bool.false 12365978 Bool.false Bool.false 518777874 Bool.true Bool.true 938401442 

noncomputable def Ns564p1199 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 969399 1000 37 109 536870912 268435456 9007199254740992 Bool.false 1050769809590 4511 

noncomputable def Ns564p1200 := Ns564p1199 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 519669302 174064 Bool.true 256515041 Bool.true 837085413 28296951008113761 1 Bool.false 246865893 Bool.true Bool.false 536834771 Bool.true Bool.true 785894499 

noncomputable def Ns564p1201 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 969399 1000 140 45 536870912 268435456 9007199254740992 Bool.false 1050769809590 4511 

noncomputable def Ns564p1202 := Ns564p1201 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.true 691260334 129341 Bool.false 198630728 Bool.false 87042503 28296951008113761 1 Bool.false 500543594 Bool.false Bool.false 86661671 Bool.true Bool.true 519669302 

noncomputable def Ns564p1203 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 969399 1000 390 252 536870912 268435456 9007199254740992 Bool.false 1050769809590 4511 

noncomputable def Ns564p1204 := Ns564p1203 744261104 53 268435448 8 864060384 53 240095976 8 Bool.true 581700187 76382 Bool.false 391045585 Bool.false 635193554 28296951008113761 1 Bool.false 400642232 Bool.true Bool.false 202947679 Bool.false Bool.true 691260334 

noncomputable def Ns564p1205 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 969399 1000 818 568 536870912 268435456 9007199254740992 Bool.false 1050769809590 4511 

noncomputable def Ns564p1206 := Ns564p1205 372130544 53 379625064 8 589812976 53 309962568 8 Bool.true 536870672 4573 Bool.false 195279723 Bool.false 2861958 28296951008113761 1 Bool.false 501745544 Bool.true Bool.false 536863283 Bool.false Bool.true 581700187 

noncomputable def Ns564p1207 := nat_lit 29259926360046129629379988116633255627023797612044496577537 

noncomputable def Ns564p1208 := nat_lit 14949804616191444877865253773165021172313255139344384000 

noncomputable def Ns564p1209 := nat_lit 410917244304245555374643494559520000 

noncomputable def Ns564p1210 := nat_lit 2390056890990219853790451124781760770880 

noncomputable abbrev qz684 := (@Eq.refl Real qz778)

noncomputable abbrev qz490 := qz684

noncomputable abbrev qz173 := qz490

noncomputable def Ns564p1211 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz170 969399 1000 3758938684804 16000000 1938798 4000 2000 Ns564p1209 Ns564p1210 qz173 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns564p1212 := nat_lit 84268587916932853332614365775903776205828537122688150143306560 

noncomputable abbrev qz685 := (@HSub.hSub Real Real Real qz745 qz746 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz747 (@Nat.cast Real Real.instNatCast 1938798))))

noncomputable abbrev qz491 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 969399 4000) (Real.log (Enclosure.sfrac Bool.false 3758938684804 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz685))

noncomputable abbrev qz686 := (Enclosure.sfrac Bool.false 969399 2000)

noncomputable abbrev qz174 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz491 qz686) (@HMul.hMul Real Real Real qz355 qz686 (Real.log Real.pi)))

noncomputable def Ns564p1213 := @Enclosure.Real.IsNear.addLit_ft_p qz174 (Enclosure.sfrac Bool.true Ns564p1209 Ns564p1210) 35257987220733765754337 18014398509481984000 137621146653629793 16384000000000000000000 Ns564p1209 Ns564p1210 0 1 Ns564p1212 

noncomputable def Ns564p1214 := nat_lit 2366123469309960266215659143168000 

noncomputable abbrev qz175 := (@HSub.hSub Real Real Real qz359 qz491 qz686)

noncomputable def Ns564p1215 := @Enclosure.Real.IsNear.subLit_ff_p qz175 (@HMul.hMul Real Real Real qz5 qz686 (Real.log Real.pi)) 45253276263848771722721 18014398509481984000 47724626468007 16000000000000000000 37235353302639 67108864000 2908197 536870912000 Ns564p1214 35257987220733765754337 18014398509481984000 

noncomputable def Ns564p1216 := nat_lit 90506552527697543445442000 

noncomputable abbrev qz176 := qz491

noncomputable def Ns564p1217 := @Enclosure.Real.IsNear.subLit_ff_p qz176 qz686 53984846214195434626529 18014398509481984000 47724626468007 16000000000000000000 969399 2000 0 1 Ns564p1216 45253276263848771722721 18014398509481984000 47724626468007 16000000000000000000 

noncomputable def Ns564p1218 := nat_lit 121563066646952045536056720226036744192 

noncomputable def Ns564p1219 := nat_lit 119606850539931500866961408 

noncomputable def Ns564p1220 := nat_lit 113075420779003326746128278592681756902570581124893951021804131964721174571422442450904265145227199811606049636480693132461904126431619007211024891010377446816919478860309097127241318400 

noncomputable def Ns564p1221 := nat_lit 3190808035410092352944435755712196712988285319290799455768659607926738016605616921364040427984219556844869899451349815977626536487581968697522536288252546502017507283576457530483671040 

noncomputable def Ns564p1222 := nat_lit 165509030059947931830953780949625477998062237626686338822206697592368791864666014986599775958089859085296952774419223941134830990997124327964998172857904680963388136124642754560 

noncomputable def Ns564p1223 := BSN.log_dyadic_bound 1661786684804 5856090684804 8 7 Ns564p1220 268435456 81920000 Ns564p1221 Ns564p1222 156647233 7517877369608 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1661786684804) (BSN.artanhQ 5856090684804) 0 7 Ns564p1221 Ns564p1220 Ns564p1222 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz492 := (Real.log (Enclosure.sfrac Bool.false 3758938684804 16000000))

noncomputable def Ns564p1224 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 969399 4000) qz492 969399 4000 0 1 55696279993248871 4503599627370496 48828193 4000000000000000 53991918129175462298529 18014398509481984000 47334001466007 16000000000000000000 (Enclosure.Real.IsNear.const Bool.false 969399 4000) (BSN.isNear_log_sfrac 3758938684804 16000000 55696279993248871 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3758938684804) qz362)) Bool.false Ns564p1219 Ns564p112 1000001392640000 81920000000000000000000 55696279993248871 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3758938684804 16000000 17 7517877369608 4194304000000 156647233 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns564p1223 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p1225 := BSN.arctan_dyadic_bound_f 1000 1938798 1 0 33554432 10240000 0 1 1 0 1 1 17306 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1938798) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1938798) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns564p1226 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1938798))) 884279719003555 562949953421312 1 2000000000000000 17306 33554432 1 10240000 29661761288389984780288 883989372503459 562949953421312 195312501 2000000000000000 qz17 (Ns564p1225 rfl) rfl rfl 

noncomputable abbrev qz493 := (@HMul.hMul Real Real Real qz588 qz593 qz685)

noncomputable abbrev qz177 := qz493

noncomputable abbrev qz494 := qz685

noncomputable abbrev qz178 := qz494

noncomputable def Ns564p1227 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 969399 4000) qz492) qz177 53991918129175462298529 18014398509481984000 47334001466007 16000000000000000000 883989372503459 2251799813685248 195312501 8000000000000000 Ns564p1218 53984846214195434626529 18014398509481984000 47724626468007 16000000000000000000 (Ns564p1224 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz178 1 4 0 1 883989372503459 562949953421312 195312501 2000000000000000 883989372503459 2251799813685248 195312501 8000000000000000 qz369 Ns564p1226 rfl) 

noncomputable def Ns564p1228 := @Ns564p1213 Ns564p1207 Ns564p1208 137621146653629793 16384000000000000000000 (@Ns564p1215 137621146653629793 16384000000000000000000 (Ns564p1217 (Ns564p1227 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 969399 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz686 (Real.log Real.pi) 969399 2000 0 1 38410761 33554432 3 268435456 37235353302639 67108864000 2908197 536870912000 (Enclosure.Real.IsNear.const Bool.false 969399 2000) RS565to576.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns564p1209 Ns564p1210) 

noncomputable def Ns564p1229 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns564p1207 Ns564p1208 137621146653629793 16384000000000000000000 65673113099 33554432 565 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz370 qz174 (Enclosure.sfrac Bool.true Ns564p1209 Ns564p1210)) Bool.false Ns564p1207 Ns564p1208 137621146653629793 16384000000000000000000 Ns564p1211 (Ns564p1228 rfl rfl)) 

noncomputable def Ns564p1230 := nat_lit 7591386434856175563440128 

noncomputable def Ns564p1231 := nat_lit 14346126744717024388231682090856444384344718958706431331378641100617372295723491537822685592898512776321271744676208651159999057631838462890625 

noncomputable def Ns564p1232 := nat_lit 10177838029728212622614670539900860896474553021685803875905005654074613407296661036309806512744123089099376765697818250715732574462890625 

noncomputable def Ns564p1233 := nat_lit 71641711132560700739036943096855506127373350371801965583282353866368470492618464933863201282046241692227917188507597302599722025228894462890625 

noncomputable def Ns564p1234 := BSN.sin_dyadic_bound_f 215760179425 137438953472 4 3 67108864 20500001 Ns564p1231 Ns564p124 Ns564p1232 Ns564p1233 Ns564p127 Ns564p1232 67108834 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215760179425) qz371 0 3 Ns564p1231 Ns564p124 Ns564p1232 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215760179425) qz372 0 3 Ns564p1233 Ns564p127 Ns564p1232 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1235 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz170) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 65673113099) qz383) Bool.false 65673113099 33554432 565 67108864 Bool.true 67108834 67108864 1 10240000 (Ns564p1229 rfl) (Enclosure.sfrac_false_div 65673113099 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 65673113099) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p1230) qz416) 226375608064910080 72057594037927936 Bool.false 67108834 67108864 311 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 65673113099 33554432 226375608064910080 72057594037927936 311 Ns564p1230 Ns564p435 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108834 67108864 Ns564p1230 Ns564p435 215760179425 137438953472 20500001 20480000 (Ns564p1234 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p1236 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns564p1207 Ns564p1208 137621146653629793 16384000000000000000000 1050769809590 536870912 4511 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz370 qz174 (Enclosure.sfrac Bool.true Ns564p1209 Ns564p1210)) Bool.false Ns564p1207 Ns564p1208 137621146653629793 16384000000000000000000 Ns564p1211 (Ns564p1228 rfl rfl)) 

noncomputable def Ns564p1237 := Ns564p1206 76382 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 818 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 501745544 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 568 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536863283 536870912) qz173 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) Bool.true 33554417 33554432 357221 41943040000 536870672 536870912 4573 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 33554417 33554432 357221 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz170) qz170) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 67108834 67108864 5852708864 687194767360000 33554417 33554432 357221 41943040000 (Ns564p1235 rfl rfl) rfl)) rfl) (Ns564p1236 rfl) RS565to576.d7 

noncomputable def Ns564p1238 := nat_lit 202965351523967765179223288537073290967893780425643112417209309536984161 

noncomputable def Ns564p1239 := nat_lit 2114741085853752528258737731912701813903785221576238550591619472481 

noncomputable def Ns564p1240 := nat_lit 608891825089731588032613348135756047500053533706486184774526745372007521 

noncomputable def Ns564p1241 := BSN.cos_dyadic_bound_f 195279723 536870912 3 2 536870912 268435456 Ns564p1238 Ns564p170 Ns564p1239 Ns564p1240 Ns564p173 Ns564p1239 501745544 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 195279723) qz373 0 2 Ns564p1238 Ns564p170 Ns564p1239 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 195279723) qz374 0 2 Ns564p1240 Ns564p173 Ns564p1239 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1242 := BSN.cos_dyadic_bound_f 2861958 536870912 1 0 536870912 268435456 0 1 1 0 1 1 536863283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 2861958) qz373 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 2861958) qz374 0 0 rfl) rfl rfl 

noncomputable def Ns564p1243 := nat_lit 3264157324814025699658426185770925396455035070064072398976994763691690625 

noncomputable def Ns564p1244 := nat_lit 546788152174032897208625122958647563243177578393242575805028062890625 

noncomputable def Ns564p1245 := nat_lit 9791378398137729033180861307066858894238618855035430711779374234949290625 

noncomputable def Ns564p1246 := BSN.cos_dyadic_bound_f 391045585 536870912 3 2 536870912 268435456 Ns564p1243 Ns564p170 Ns564p1244 Ns564p1245 Ns564p173 Ns564p1244 400642232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 391045585) qz373 0 2 Ns564p1243 Ns564p170 Ns564p1244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 391045585) qz374 0 2 Ns564p1245 Ns564p173 Ns564p1244 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1247 := nat_lit 22449950127215908076706877067413852550598581955851411091589547733232851419750992585349661667195080600380778090496 

noncomputable def Ns564p1248 := nat_lit 4313928931698080177570179845281197036291354493546489163387480977115354961548448239681880919904274747887616 

noncomputable def Ns564p1249 := nat_lit 136090562270605365118628452989541258392481170082909135073767060321514535692237410925097421114726635232202371502080 

noncomputable def Ns564p1250 := BSN.cos_dyadic_bound_f 635193554 536870912 4 3 536870912 268435456 Ns564p1247 Ns564p133 Ns564p1248 Ns564p1249 Ns564p136 Ns564p1248 202947679 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 635193554) qz373 0 3 Ns564p1247 Ns564p133 Ns564p1248 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 635193554) qz374 0 3 Ns564p1249 Ns564p136 Ns564p1248 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1251 := Ns564p1204 129341 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 390 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 400642232 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 252 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 202947679 536870912) qz173 rfl rfl (Ns564p1237 RS565to576.d9 RS565to576.d11 RS565to576.d13 RS565to576.d17 (Ns564p1241 rfl rfl) (Ns564p1242 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns564p1236 rfl) RS565to576.d19 RS565to576.d21 RS565to576.d23 RS565to576.d25 RS565to576.d17 (Ns564p1246 rfl rfl) (Ns564p1250 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns564p1252 := nat_lit 217259792191471706482131165944347081688959710372449144278859184829628416 

noncomputable def Ns564p1253 := nat_lit 2423100764744886843409846573174074293403571919361102519892009025536 

noncomputable def Ns564p1254 := nat_lit 651774530372885629672706678139894896918292323973508710631537770470834176 

noncomputable def Ns564p1255 := BSN.cos_dyadic_bound_f 198630728 536870912 3 2 536870912 268435456 Ns564p1252 Ns564p170 Ns564p1253 Ns564p1254 Ns564p173 Ns564p1253 500543594 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 198630728) qz373 0 2 Ns564p1252 Ns564p170 Ns564p1253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 198630728) qz374 0 2 Ns564p1254 Ns564p173 Ns564p1253 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1256 := nat_lit 57401796479377837260686938090081 

noncomputable def Ns564p1257 := BSN.sin_dyadic_bound_f 87042503 536870912 2 1 536870912 268435456 Ns564p1256 Ns564p463 Ns564p1256 Ns564p1256 Ns564p464 Ns564p1256 86661671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 87042503) qz375 0 1 Ns564p1256 Ns564p463 Ns564p1256 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 87042503) qz376 0 1 Ns564p1256 Ns564p464 Ns564p1256 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1258 := Ns564p1202 174064 BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 500543594 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 86661671 536870912) qz173 rfl rfl (Ns564p1251 rfl rfl) (Ns564p1236 rfl) RS565to576.d27 RS565to576.d29 RS565to576.d31 RS565to576.d33 RS565to576.d17 (Ns564p1255 rfl rfl) (Ns564p1257 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1259 := nat_lit 1087727504475442718599535280055397359100961499289904749932875252172410625 

noncomputable def Ns564p1260 := nat_lit 18745744079957520109185425009779479043436214672255414113079902949121 

noncomputable def Ns564p1261 := nat_lit 2848779780516696712728129909456977249917400268078376407725156864418205441 

noncomputable def Ns564p1262 := BSN.sin_dyadic_bound_f 256515041 536870912 3 2 536870912 268435456 Ns564p1259 Ns564p143 Ns564p1260 Ns564p1261 Ns564p146 Ns564p1260 246865893 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 256515041) qz375 0 2 Ns564p1259 Ns564p143 Ns564p1260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 256515041) qz376 0 2 Ns564p1261 Ns564p146 Ns564p1260 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1263 := nat_lit 176191688457048563103970351303105449573521434177125048872545572677719553544748639313937920851533151962557538960081 

noncomputable def Ns564p1264 := nat_lit 118368811780369069148432666723144796929771677745101952738169868149760839892008917884196198280364683649680081 

noncomputable def Ns564p1265 := nat_lit 879895683429895345899704463280075860692962955887744290818060973706361421100105089482977333596587963961339775877841 

noncomputable def Ns564p1266 := BSN.sin_dyadic_bound_f 837085413 536870912 4 3 536870912 268435456 Ns564p1263 Ns564p181 Ns564p1264 Ns564p1265 Ns564p184 Ns564p1264 536834771 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 837085413) qz375 0 3 Ns564p1263 Ns564p181 Ns564p1264 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 837085413) qz376 0 3 Ns564p1265 Ns564p184 Ns564p1264 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1267 := Ns564p1200 213139 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 246865893 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536834771 536870912) qz173 rfl rfl (Ns564p1258 rfl) (Ns564p1236 rfl) RS565to576.d35 RS565to576.d37 RS565to576.d39 RS565to576.d41 RS565to576.d17 (Ns564p1262 rfl rfl) (Ns564p1266 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1268 := BSN.sin_dyadic_bound_f 12367072 536870912 1 0 536870912 268435456 0 1 1 0 1 1 12365978 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 12367072) qz375 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 12367072) qz376 0 0 rfl) rfl rfl 

noncomputable def Ns564p1269 := nat_lit 87828108708812077556033488832520979371001788485815605805476936905523771616056590401341646583175670902549715790625 

noncomputable def Ns564p1270 := nat_lit 14704702302753397351167265379457708343448919802261533056201979261942370928891810161275205787812988525390625 

noncomputable def Ns564p1271 := nat_lit 438876008175789202152741294018283956422944619631322893619757653092136515110660231908271407795424082286970477390625 

noncomputable def Ns564p1272 := BSN.sin_dyadic_bound_f 703538745 536870912 4 3 536870912 268435456 Ns564p1269 Ns564p181 Ns564p1270 Ns564p1271 Ns564p184 Ns564p1270 518777874 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 703538745) qz375 0 3 Ns564p1269 Ns564p181 Ns564p1270 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 703538745) qz376 0 3 Ns564p1271 Ns564p184 Ns564p1270 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1273 := Ns564p1198 248282 BSN.abs_quadSignPos qz625 (BSN.sfrac_eq_quadSignPos_mul Bool.false 12365978 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 518777874 536870912) qz173 rfl rfl (Ns564p1267 rfl) (Ns564p1236 rfl) RS565to576.d43 RS565to576.d45 RS565to576.d47 RS565to576.d49 RS565to576.d17 (Ns564p1268 rfl rfl) (Ns564p1272 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1274 := nat_lit 10204619972836791304721100207657981384752572750701206454328965675516330625 

noncomputable def Ns564p1275 := nat_lit 1649417883167611505440973942753207141313128524168610645668016062890625 

noncomputable def Ns564p1276 := nat_lit 26723715157047420141355977062244541291361278805654505820292399981298090625 

noncomputable def Ns564p1277 := BSN.sin_dyadic_bound_f 448917295 536870912 3 2 536870912 268435456 Ns564p1274 Ns564p143 Ns564p1275 Ns564p1276 Ns564p146 Ns564p1275 398403158 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 448917295) qz375 0 2 Ns564p1274 Ns564p143 Ns564p1275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 448917295) qz376 0 2 Ns564p1276 Ns564p146 Ns564p1275 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1278 := Ns564p1196 Bool.true 938401442 248282 Bool.true 448917295 28296951008113761 1 Bool.false 398403158 Bool.false Bool.true 823392353 264706 BSN.abs_quadSignPos qz377 (BSN.sfrac_eq_quadSignPos_mul Bool.false 398403158 536870912) qz173 rfl (Ns564p1273 rfl) (Ns564p1236 rfl) RS565to576.d51 RS565to576.d53 RS565to576.d17 (Ns564p1277 rfl rfl) rfl 

noncomputable def Ns564p1279 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) 823392353 536870912 264706 536870912 823392353 536870912 264706 536870912 884110806977871872 823392353 268435456 132353 134217728 (Ns564p1278 rfl rfl rfl rfl) 

noncomputable def Ns564p1280 := @Enclosure.Real.IsNear.mulLit_ff qz683 (Zeta.RiemannSiegel.correction qz172) 19041415 67108864 1 67108864 886404522072235 2251799813685248 109202751227 11258999068426240 16878396362654086612525 151115727451828646838272 

noncomputable abbrev qz687 := (@HPow.hPow Real Real Real qz7 qz171 qz9)

noncomputable def Ns564p1281 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz687 1 1 0 1 19041415 67108864 1 67108864 19041415 67108864 1 67108864 

noncomputable def Ns564p1282 := @Enclosure.Real.IsNear.sqrt_image qz171 10353866685093 67108864000 969399 67108864000 416784166 416784206 33554432 (@Enclosure.Real.IsNear.of_eq qz171 (@HMul.hMul Real Real Real qz5 qz170 qz3) Bool.false 10353866685093 67108864000 969399 67108864000 (BSN.t_div_two_pi_mk qz170 969399 1000 qz173) (@Enclosure.Real.IsNear.mulLit_ff qz170 qz3 969399 1000 0 1 10680707 67108864 1 67108864 10353866685093 67108864000 969399 67108864000 (Enclosure.Real.IsNear.const Bool.false 969399 1000) RS565to576.d56 rfl)) 

noncomputable abbrev qz781 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 969399 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz688 := qz781

noncomputable abbrev qz495 := qz688

noncomputable abbrev qz179 := qz495

noncomputable def Ns564p1283 := @Enclosure.Real.IsNear.sqrt_image qz179 208392093 16777216 5 8388608 118258005 118258012 33554432 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 833568372 67108864 40 67108864 208392093 16777216 5 8388608 (Ns564p1282 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns564p1284 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz179) 236516017 67108864 7 67108864 9520707 9520708 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz179) Bool.false 236516017 67108864 7 67108864 236516017 67108864 7 67108864 (Ns564p1283 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns564p1285 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 19041415 67108864 1 67108864 19041415 67108864 1 67108864 (Ns564p1284 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz496 := (@HMul.hMul Real Real Real qz588 qz586 qz682)

noncomputable abbrev qz180 := (Real.cos qz496)

noncomputable abbrev qz689 := (@HMul.hMul Real Real Real qz741 qz780 qz780)

noncomputable abbrev qz497 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz689 qz682) qz604)

noncomputable abbrev qz181 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz497))

noncomputable def Ns564p1286 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz172) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz180) qz181) Bool.false 886404522072235 

noncomputable def Ns564p1287 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz180) qz181 76283915 67108864 335 

noncomputable abbrev qz182 := (@Neg.neg Real Real.instNeg (Real.cos qz496))

noncomputable def Ns564p1288 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz180) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz182)) Bool.true 76283915 67108864 335 67108864 (BSN.inv_eq_neg_inv_neg qz180) 

noncomputable def Ns564p1289 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz182) Bool.false 76283915 67108864 335 67108864 76283915 67108864 

noncomputable def Ns564p1290 := @Enclosure.Real.IsNear.recentre' qz180 Bool.true 59037342 67108864 661897216 171798691840000 29518671 33554432 40399 10485760000 

noncomputable abbrev qz183 := qz496

noncomputable def Ns564p1291 := @Enclosure.Real.IsNear.cos_image qz183 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11098463) qz605) Bool.false 11098463 4194304 63 16777216 Bool.true 59037342 67108864 1 

noncomputable def Ns564p1292 := nat_lit 134930377075566323000700131 

noncomputable def Ns564p1293 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz172 884279719003555 140737488355328 1 500000000000000 7065501 16777216 5 8388608 6247879238899336856055 2361183241434822606848 Ns564p1292 

noncomputable def Ns564p1294 := @Enclosure.Real.IsNear.subLit_ff_p qz179 qz1 208392093 16777216 5 8388608 12 1 0 1 7065501 7065501 16777216 5 

noncomputable def Ns564p1295 := @Ns564p1294 8388608 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 833568372 67108864 40 67108864 208392093 16777216 5 8388608 (Ns564p1282 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns564p1296 := @Enclosure.Real.IsNear.recentre' qz183 Bool.false 6247879238899336856055 2361183241434822606848 Ns564p1292 Ns564p201 11098463 4194304 63 16777216 (@Ns564p1293 Ns564p201 RS565to576.d55 (Ns564p1295 rfl rfl) rfl) 

noncomputable def Ns564p1297 := nat_lit 514925390409516779776656724897080961901777347849318705517476299151337653123430279603573553985 

noncomputable def Ns564p1298 := nat_lit 227542441975368611288419587439224223596405344423479634030986548307947456912119618985065281 

noncomputable def Ns564p1299 := nat_lit 1348245715690298112139633981112691394333117921428672880757340138603861938488269205292907297601 

noncomputable def Ns564p1300 := BSN.sin_dyadic_bound_f 147785832311 137438953472 3 2 67108864 20500001 Ns564p1297 Ns564p207 Ns564p1298 Ns564p1299 Ns564p210 Ns564p1298 59037342 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 147785832311) qz371 0 2 Ns564p1297 Ns564p207 Ns564p1298 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 147785832311) qz372 0 2 Ns564p1299 Ns564p210 Ns564p1298 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1301 := @Ns564p1291 10240000 (Ns564p1296 rfl) (Enclosure.sfrac_false_div 11098463 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11098463) qz605) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 649968964188842980540416) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 59037342 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 11098463 4194304 226375608064910080 72057594037927936 0 649968964188842980540416 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 59037342 67108864 649968964188842980540416 604462909807314587353088 147785832311 137438953472 20500001 20480000 (Ns564p1300 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p1302 := @Enclosure.Real.IsNear.inv_image qz182 29518671 33554432 40399 10485760000 38141790 38142125 33554432 (@Enclosure.Real.IsNear.neg qz180 Bool.true 29518671 33554432 40399 10485760000 (Ns564p1290 (Ns564p1301 rfl rfl) rfl)) 

noncomputable def Ns564p1303 := Ns564p1288 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz182) Bool.false 76283915 67108864 335 67108864 (@Ns564p1289 335 67108864 (Ns564p1302 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p1304 := @Enclosure.Real.IsNear.recentre' qz181 Bool.true 11619809 33554432 

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz355 qz352 qz497)

noncomputable def Ns564p1305 := @Enclosure.Real.IsNear.cos_image qz184 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16143185)) (@Nat.cast Real Real.instNatCast 8388608)) Bool.true 16143185 8388608 

noncomputable def Ns564p1306 := nat_lit 76234035854621715455494083205 

noncomputable def Ns564p1307 := nat_lit 39614081257132168796771975168 

noncomputable def Ns564p1308 := nat_lit 1042614714552475897905514606803539 

noncomputable def Ns564p1309 := @Enclosure.Real.IsNear.recentre' qz184 Bool.true Ns564p1306 Ns564p1307 Ns564p1308 

noncomputable def Ns564p1310 := nat_lit 151115727451828646838272000000000000000 

noncomputable abbrev qz185 := qz497

noncomputable def Ns564p1311 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz185 884279719003555 140737488355328 1 500000000000000 86210318088631 

noncomputable abbrev qz498 := (@HSub.hSub Real Real Real qz592 qz689 qz682)

noncomputable abbrev qz186 := qz498

noncomputable def Ns564p1312 := @Enclosure.Real.IsNear.subLit_tf qz186 qz31 68618132044215 281474976710656 38635285 35184372088832 1 16 

noncomputable abbrev qz499 := qz689

noncomputable abbrev qz187 := qz499

noncomputable def Ns564p1313 := @Enclosure.Real.IsNear.subLit_ff_n qz187 qz172 49921304381001 281474976710656 17663765 35184372088832 7065501 16777216 5 8388608 

noncomputable def Ns564p1314 := @Enclosure.Real.IsNear.mulLit_ff qz172 qz172 7065501 16777216 5 8388608 7065501 16777216 5 8388608 49921304381001 281474976710656 

noncomputable def Ns564p1315 := nat_lit 33507107861345460847992772068542236906271435733519221396676558845518497885966568490611890625 

noncomputable def Ns564p1316 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns564p1317 := nat_lit 313235290287922768189496474708799684115229064422058526562967329074978809476777587890625 

noncomputable def Ns564p1318 := nat_lit 202177508359764190562528053775890547753985917323359152494152197572797156778534297477133490625 

noncomputable def Ns564p1319 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns564p1320 := BSN.cos_dyadic_bound_t 16143185 8388608 4 3 33554432 10240000 Ns564p1315 Ns564p1316 Ns564p1317 Ns564p1318 Ns564p1319 Ns564p1317 11619809 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16143185) (BSN.cosEvenQ 8388608) 0 3 Ns564p1315 Ns564p1316 Ns564p1317 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16143185) (BSN.cosOddQ 8388608) 0 3 Ns564p1318 Ns564p1319 Ns564p1317 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1321 := @Ns564p1304 301154304 42949672960000 11619809 33554432 18381 2621440000 (@Ns564p1305 29 4194304 Bool.true 11619809 33554432 1 10240000 (@Ns564p1309 Ns564p1310 16143185 8388608 29 4194304 (@Ns564p1311 281474976710656 38635285 35184372088832 Ns564p1306 Ns564p1307 Ns564p1308 Ns564p1310 RS565to576.d55 (@Ns564p1312 0 1 1379365089418096 86210318088631 281474976710656 38635285 35184372088832 (@Ns564p1313 1151221222822316605440 68618132044215 281474976710656 38635285 35184372088832 (@Ns564p1314 17663765 35184372088832 (Ns564p1295 rfl rfl) (Ns564p1295 rfl rfl) rfl) (Ns564p1295 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16143185 8388608) (BSN.cos_neg_of_bound 16143185 8388608 Bool.true 11619809 33554432 1 10240000 (Ns564p1320 rfl rfl)) rfl rfl) 

noncomputable def Ns564p1322 := @Ns564p1280 2083807037068178607 755578637259143234191360 (Ns564p1281 qz33 (@Enclosure.Real.IsNear.of_eq qz687 (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 19041415 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz171 (BSN.t_div_two_pi_nonneg qz170 969399 1000 qz173)) Ns564p1285) rfl) (@Ns564p1286 2251799813685248 109202751227 11258999068426240 (BSN.correction_mk qz172 (BSN.cos_two_pi_p_ne_zero_mk qz170 969399 1000 12 qz173 rfl rfl (@BSN.floor_sqrt_eq_dec qz170 969399 1000 12 qz173 rfl rfl rfl))) (@Ns564p1287 67108864 11619809 33554432 18381 2621440000 886404522072235 2251799813685248 109202751227 11258999068426240 Ns564p1303 (Ns564p1321 rfl) rfl)) 

noncomputable def Ns564p1323 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (hardyZApproximantRS₀ qz170) Bool.true 480407083131468574639661 151115727451828646838272 747164958888777249967 755578637259143234191360 (@Eq.refl Real (hardyZApproximantRS₀ qz170)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HMul.hMul Real Real Real qz5 qz683 (Zeta.RiemannSiegel.correction qz172))) Bool.true 480407083131468574639661 151115727451828646838272 747164958888777249967 755578637259143234191360 (BSN.hardyZApproximantRS₀_eq qz170 12 (@BSN.floor_sqrt_eq_dec qz170 969399 1000 12 qz173 rfl rfl rfl)) (@Ns564p1195 480407083131468574639661 151115727451828646838272 747164958888777249967 755578637259143234191360 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12)) Bool.true 823392353 268435456 132353 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (Ns564p1279 (Ns564p1278 rfl rfl rfl rfl) rfl rfl)) (Ns564p1322 rfl) rfl rfl)) 

theorem RS565to576.d67 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz170) Bool.true 480407083131468574639661 151115727451828646838272 747164958888777249967 755578637259143234191360 := Ns564p1323 

noncomputable def Ns564p1324 := nat_lit 32154582382839178721214070784 

noncomputable abbrev qz782 := (Enclosure.sfrac Bool.false 970646 1000)

noncomputable abbrev qz690 := qz782

noncomputable abbrev qz500 := qz690

noncomputable abbrev qz188 := qz500

noncomputable abbrev qz783 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 970646 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz691 := qz783

noncomputable abbrev qz501 := qz691

noncomputable abbrev qz189 := qz501

noncomputable abbrev qz784 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 970646 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz692 := qz784

noncomputable abbrev qz502 := qz692

noncomputable abbrev qz190 := qz502

noncomputable abbrev qz693 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz189 qz9))

noncomputable def Ns564p1325 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (@HMul.hMul Real Real Real qz5 qz693 (Zeta.RiemannSiegel.correction qz190)) 58198357 33554432 132523 134217728 65555093408258880825 590295810358705651712 16000832141119590661 Ns564p85 Ns564p1324 

noncomputable def Ns564p1326 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin BSN.quadSignPos 11 12 970646 1000 287 536870912 268435456 9007199254740992 Bool.false 1052456707254 4516 1334074092 54 154981288 8 

noncomputable def Ns564p1327 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 970646 1000 174 233 536870912 268435456 9007199254740992 Bool.false 1052456707254 4516 

noncomputable def Ns564p1328 := Ns564p1327 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.false 545134219 213413 Bool.true 710314386 Bool.true 621979276 28296951008113761 1 Bool.false 131644232 Bool.true Bool.false 491888516 Bool.true Bool.false 355194694 

noncomputable def Ns564p1329 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 970646 1000 36 109 536870912 268435456 9007199254740992 Bool.false 1052456707254 4516 

noncomputable def Ns564p1330 := Ns564p1329 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.false 695481066 174288 Bool.true 805072653 Bool.true 621181306 28296951008113761 1 Bool.false 38209871 Bool.false Bool.false 491568235 Bool.true Bool.false 545134219 

noncomputable def Ns564p1331 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 970646 1000 140 45 536870912 268435456 9007199254740992 Bool.false 1052456707254 4516 

noncomputable def Ns564p1332 := Ns564p1331 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.false 788262101 129508 Bool.false 685984807 Bool.false 471196098 28296951008113761 1 Bool.false 155087825 Bool.false Bool.false 412989530 Bool.true Bool.false 695481066 

noncomputable def Ns564p1333 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 970646 1000 391 253 536870912 268435456 9007199254740992 Bool.false 1052456707254 4516 

noncomputable def Ns564p1334 := Ns564p1333 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 806400726 76481 Bool.false 306534796 Bool.false 401293063 28296951008113761 1 Bool.false 290149036 Bool.false Bool.false 364955664 Bool.true Bool.false 788262101 

noncomputable def Ns564p1335 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 970646 1000 819 569 536870912 268435456 9007199254740992 Bool.false 1052456707254 4516 

noncomputable def Ns564p1336 := Ns564p1335 372130544 53 379625064 8 589812976 53 309962568 8 Bool.false 536870856 4581 Bool.false 574815742 Bool.false 110947984 28296951008113761 1 Bool.false 471118027 Bool.false Bool.false 110159959 Bool.true Bool.false 806400726 

noncomputable def Ns564p1337 := nat_lit 415319409612992546220339154362344034440593622780081283701 

noncomputable def Ns564p1338 := nat_lit 211859460511125551826974467161458158476648312628838400 

noncomputable def Ns564p1339 := nat_lit 413566997724462847048093918868480000 

noncomputable def Ns564p1340 := nat_lit 2408563210691745005385365256659703828480 

noncomputable abbrev qz694 := (@Eq.refl Real qz782)

noncomputable abbrev qz503 := qz694

noncomputable abbrev qz191 := qz503

noncomputable def Ns564p1341 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz188 970646 1000 3768615629264 16000000 1941292 4000 2000 Ns564p1339 Ns564p1340 qz191 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns564p1342 := nat_lit 8505741508874087346592545881340805825343357394536064690196480 

noncomputable abbrev qz695 := (@HSub.hSub Real Real Real qz745 qz746 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz747 (@Nat.cast Real Real.instNatCast 1941292))))

noncomputable abbrev qz504 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 970646 4000) (Real.log (Enclosure.sfrac Bool.false 3768615629264 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz695))

noncomputable abbrev qz696 := (Enclosure.sfrac Bool.false 970646 2000)

noncomputable abbrev qz192 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz504 qz696) (@HMul.hMul Real Real Real qz355 qz696 (Real.log Real.pi)))

noncomputable def Ns564p1343 := @Enclosure.Real.IsNear.addLit_ft_p qz192 (Enclosure.sfrac Bool.true Ns564p1339 Ns564p1340) 3531459010970813986601 1801439850948198400 68898831500113261 8192000000000000000000 Ns564p1339 Ns564p1340 0 1 Ns564p1342 

noncomputable def Ns564p1344 := nat_lit 592480506222037159490260828160000 

noncomputable abbrev qz193 := (@HSub.hSub Real Real Real qz359 qz504 qz696)

noncomputable def Ns564p1345 := @Enclosure.Real.IsNear.subLit_ff_p qz193 (@HMul.hMul Real Real Real qz5 qz696 (Real.log Real.pi)) 22661368366536570164173 9007199254740992000 23892757612339 8000000000000000000 18641625760803 33554432000 1455969 268435456000 Ns564p1344 3531459010970813986601 1801439850948198400 

noncomputable def Ns564p1346 := nat_lit 45322736733073140328346000 

noncomputable abbrev qz194 := qz504

noncomputable def Ns564p1347 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz696 27032769330445232624589 9007199254740992000 23892757612339 8000000000000000000 970646 2000 0 1 Ns564p1346 22661368366536570164173 9007199254740992000 23892757612339 8000000000000000000 

noncomputable def Ns564p1348 := nat_lit 60872384941692861148939944167391363072 

noncomputable def Ns564p1349 := nat_lit 119631716426683688171864064 

noncomputable def Ns564p1350 := nat_lit 115719638552697520104954134739877034786919618685221781786044858466956529422723736864227586473775676432522621174795535920272834775117819137878824692711759992584458255996111141997012582400 

noncomputable def Ns564p1351 := nat_lit 3294097717485371589196690963826722867685546194683093175755223963396306839545114937453196546555994315208468355135247075122845306367011468688694107943660370535258224807742739873991229440 

noncomputable def Ns564p1352 := nat_lit 179524976305874925029297730973572094226769546954150125311748062741637283488426555048943864870178982828718831148213628882023048702628670084925382477741357537005365765236494172160 

noncomputable def Ns564p1353 := BSN.log_dyadic_bound 1671463629264 5865767629264 8 7 Ns564p1350 268435456 81920000 Ns564p1351 Ns564p1352 157337400 7537231258528 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1671463629264) (BSN.artanhQ 5865767629264) 0 7 Ns564p1351 Ns564p1350 Ns564p1352 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz505 := (Real.log (Enclosure.sfrac Bool.false 3768615629264 16000000))

noncomputable def Ns564p1354 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 970646 4000) qz505 970646 4000 0 1 55707859074083943 4503599627370496 48828193 4000000000000000 27036305289411641468589 9007199254740992000 23697445111339 8000000000000000000 (Enclosure.Real.IsNear.const Bool.false 970646 4000) (BSN.isNear_log_sfrac 3768615629264 16000000 55707859074083943 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3768615629264) qz362)) Bool.false Ns564p1349 Ns564p112 1000001392640000 81920000000000000000000 55707859074083943 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3768615629264 16000000 17 7537231258528 4194304000000 157337400 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns564p1353 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p1355 := BSN.arctan_dyadic_bound_f 1000 1941292 1 0 33554432 10240000 0 1 1 0 1 1 17284 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1941292) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1941292) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns564p1356 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1941292))) 884279719003555 562949953421312 1 2000000000000000 17284 33554432 1 10240000 29661773673288960049152 883989741602211 562949953421312 195312501 2000000000000000 qz17 (Ns564p1355 rfl) rfl rfl 

noncomputable abbrev qz506 := (@HMul.hMul Real Real Real qz588 qz593 qz695)

noncomputable abbrev qz195 := qz506

noncomputable abbrev qz507 := qz695

noncomputable abbrev qz196 := qz507

noncomputable def Ns564p1357 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 970646 4000) qz505) qz195 27036305289411641468589 9007199254740992000 23697445111339 8000000000000000000 883989741602211 2251799813685248 195312501 8000000000000000 Ns564p1348 27032769330445232624589 9007199254740992000 23892757612339 8000000000000000000 (Ns564p1354 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz196 1 4 0 1 883989741602211 562949953421312 195312501 2000000000000000 883989741602211 2251799813685248 195312501 8000000000000000 qz369 Ns564p1356 rfl) 

noncomputable def Ns564p1358 := @Ns564p1343 Ns564p1337 Ns564p1338 68898831500113261 8192000000000000000000 (@Ns564p1345 68898831500113261 8192000000000000000000 (Ns564p1347 (Ns564p1357 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 970646 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz696 (Real.log Real.pi) 970646 2000 0 1 38410761 33554432 3 268435456 18641625760803 33554432000 1455969 268435456000 (Enclosure.Real.IsNear.const Bool.false 970646 2000) RS565to576.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns564p1339 Ns564p1340) 

noncomputable def Ns564p1359 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns564p1337 Ns564p1338 68898831500113261 8192000000000000000000 65778544203 33554432 283 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz370 qz192 (Enclosure.sfrac Bool.true Ns564p1339 Ns564p1340)) Bool.false Ns564p1337 Ns564p1338 68898831500113261 8192000000000000000000 Ns564p1341 (Ns564p1358 rfl rfl)) 

noncomputable def Ns564p1360 := nat_lit 7593799922315942162333696 

noncomputable def Ns564p1361 := nat_lit 14364416044129312806728834194463553705197051825062103492319566831504537678028051861978514197942668520055678214897862755821640494427689971613696 

noncomputable def Ns564p1362 := nat_lit 10216735402407884045913412414060344769689776231423272036255693045608026501971340127509921315345175357926222042642331140562310992385540096 

noncomputable def Ns564p1363 := nat_lit 71732931160535309568089097409606888882989783023854574277381121693470270269256345861475169879732321084206433467641443284027915771108558064582656 

noncomputable def Ns564p1364 := BSN.sin_dyadic_bound_f 215828774864 137438953472 4 3 67108864 20500001 Ns564p1361 Ns564p124 Ns564p1362 Ns564p1363 Ns564p127 Ns564p1362 67108857 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215828774864) qz371 0 3 Ns564p1361 Ns564p124 Ns564p1362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215828774864) qz372 0 3 Ns564p1363 Ns564p127 Ns564p1362 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1365 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz188) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 65778544203) qz383) Bool.false 65778544203 33554432 283 33554432 Bool.false 67108857 67108864 1 10240000 (Ns564p1359 rfl) (Enclosure.sfrac_false_div 65778544203 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 65778544203) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p1360) qz416) 226375608064910080 72057594037927936 Bool.false 67108857 67108864 311 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q3 65778544203 33554432 226375608064910080 72057594037927936 311 Ns564p1360 Ns564p435 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108857 67108864 Ns564p1360 Ns564p435 215828774864 137438953472 20500001 20480000 (Ns564p1364 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p1366 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns564p1337 Ns564p1338 68898831500113261 8192000000000000000000 1052456707254 536870912 4516 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz370 qz192 (Enclosure.sfrac Bool.true Ns564p1339 Ns564p1340)) Bool.false Ns564p1337 Ns564p1338 68898831500113261 8192000000000000000000 Ns564p1341 (Ns564p1358 rfl rfl)) 

noncomputable def Ns564p1367 := Ns564p1336 76481 BSN.abs_quadSignPos (BSN.cos_quad_nat3 819 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 471118027 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 569 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 110159959 536870912) qz191 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) Bool.false 67108857 67108864 178923 20971520000 536870856 536870912 4581 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 67108857 67108864 178923 20971520000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz188) qz188) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 67108857 67108864 2931474432 343597383680000 67108857 67108864 178923 20971520000 (Ns564p1365 rfl rfl) rfl)) rfl) (Ns564p1366 rfl) RS565to576.d7 

noncomputable def Ns564p1368 := nat_lit 27438766540925180070169261176665211485099710662140550061155308905343484160 

noncomputable def Ns564p1369 := nat_lit 11918709270539964478077042012229964351293084405627011553700335606825216 

noncomputable def Ns564p1370 := nat_lit 71844139220746978336526416442293848232978101026092330236700770399202836736 

noncomputable def Ns564p1371 := BSN.sin_dyadic_bound_f 574815742 536870912 3 2 536870912 268435456 Ns564p1368 Ns564p143 Ns564p1369 Ns564p1370 Ns564p146 Ns564p1369 471118027 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 574815742) qz375 0 2 Ns564p1368 Ns564p143 Ns564p1369 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 574815742) qz376 0 2 Ns564p1370 Ns564p146 Ns564p1369 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1372 := nat_lit 151522686180071512293663572033536 

noncomputable def Ns564p1373 := BSN.sin_dyadic_bound_f 110947984 536870912 2 1 536870912 268435456 Ns564p1372 Ns564p463 Ns564p1372 Ns564p1372 Ns564p464 Ns564p1372 110159959 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 110947984) qz375 0 1 Ns564p1372 Ns564p463 Ns564p1372 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 110947984) qz376 0 1 Ns564p1372 Ns564p464 Ns564p1372 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1374 := nat_lit 2218174290474969686961136050738260432370842616672206110496889084139601920 

noncomputable def Ns564p1375 := nat_lit 77953970671332245749712539734955931421228158544287755897290778279936 

noncomputable def Ns564p1376 := nat_lit 5809377882910500356500332979250158822796572483789563347315637701962694656 

noncomputable def Ns564p1377 := BSN.sin_dyadic_bound_f 306534796 536870912 3 2 536870912 268435456 Ns564p1374 Ns564p143 Ns564p1375 Ns564p1376 Ns564p146 Ns564p1375 290149036 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 306534796) qz375 0 2 Ns564p1374 Ns564p143 Ns564p1375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 306534796) qz376 0 2 Ns564p1376 Ns564p146 Ns564p1375 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1378 := nat_lit 6515574589400777215802978407261659865344529734784328154389555647179013825 

noncomputable def Ns564p1379 := nat_lit 672501439866527761211525315851276540051775975955720086068082071715521 

noncomputable def Ns564p1380 := nat_lit 17063511303242251663108696216126302342456541668093121619452345038305115841 

noncomputable def Ns564p1381 := BSN.sin_dyadic_bound_f 401293063 536870912 3 2 536870912 268435456 Ns564p1378 Ns564p143 Ns564p1379 Ns564p1380 Ns564p146 Ns564p1379 364955664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 401293063) qz375 0 2 Ns564p1378 Ns564p143 Ns564p1379 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 401293063) qz376 0 2 Ns564p1380 Ns564p146 Ns564p1379 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1382 := Ns564p1334 129508 BSN.abs_quadSignPos (BSN.cos_quad_nat3 391 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 290149036 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 253 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 364955664 536870912) qz191 rfl rfl (Ns564p1367 RS565to576.d9 RS565to576.d11 RS565to576.d13 RS565to576.d17 (Ns564p1371 rfl rfl) (Ns564p1373 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns564p1366 rfl) RS565to576.d19 RS565to576.d21 RS565to576.d23 RS565to576.d25 RS565to576.d17 (Ns564p1377 rfl rfl) (Ns564p1381 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns564p1383 := nat_lit 30551417694744080279677617557539812155780034054492411125038827515117808965489950580293324394078951440040513938081 

noncomputable def Ns564p1384 := nat_lit 10858603273307196952624459022932411884950289782527542030788957740893379594207629999174766299027020810724001 

noncomputable def Ns564p1385 := nat_lit 185149476294975968514150504608635964430428004159619018153196561903870111857389999500385803600459783236120813413025 

noncomputable def Ns564p1386 := BSN.cos_dyadic_bound_f 685984807 536870912 4 3 536870912 268435456 Ns564p1383 Ns564p133 Ns564p1384 Ns564p1385 Ns564p136 Ns564p1384 155087825 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 685984807) qz373 0 3 Ns564p1383 Ns564p133 Ns564p1384 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 685984807) qz374 0 3 Ns564p1385 Ns564p136 Ns564p1384 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1387 := nat_lit 12386631987440159056289692445841070862263567016188905998937660008009498880 

noncomputable def Ns564p1388 := nat_lit 2430040339111302071733983287006370394743398029835114662563039279513856 

noncomputable def Ns564p1389 := nat_lit 32437244663698998277404482337595270515765471921779782668716388433572331776 

noncomputable def Ns564p1390 := BSN.sin_dyadic_bound_f 471196098 536870912 3 2 536870912 268435456 Ns564p1387 Ns564p143 Ns564p1388 Ns564p1389 Ns564p146 Ns564p1388 412989530 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 471196098) qz375 0 2 Ns564p1387 Ns564p143 Ns564p1388 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 471196098) qz376 0 2 Ns564p1389 Ns564p146 Ns564p1388 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1391 := Ns564p1332 174288 BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 155087825 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 412989530 536870912) qz191 rfl rfl (Ns564p1382 rfl rfl) (Ns564p1366 rfl) RS565to576.d27 RS565to576.d29 RS565to576.d31 RS565to576.d33 RS565to576.d17 (Ns564p1386 rfl rfl) (Ns564p1390 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1392 := nat_lit 58040452228229091091149080032633219583614080670564283852347883886740255434648132505881653626064434613633457599921 

noncomputable def Ns564p1393 := nat_lit 74134590921710016294334419506885897503395667203206434867636816022080062478868297887578211272829980543301041 

noncomputable def Ns564p1394 := nat_lit 351407275184638223738005162909852094153160328169502502312759049737583073832573557194062353650935100709755811280305 

noncomputable def Ns564p1395 := BSN.cos_dyadic_bound_f 805072653 536870912 4 3 536870912 268435456 Ns564p1392 Ns564p133 Ns564p1393 Ns564p1394 Ns564p136 Ns564p1393 38209871 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 805072653) qz373 0 3 Ns564p1392 Ns564p133 Ns564p1393 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 805072653) qz374 0 3 Ns564p1394 Ns564p136 Ns564p1393 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1396 := nat_lit 53356694626426498932105494928987419048390699997817130149595591850665391013426640098002355681756305163214547521536 

noncomputable def Ns564p1397 := nat_lit 3300810025568558160838170107520787146757178134369401463995795684834082787574179867753208985539086962855936 

noncomputable def Ns564p1398 := nat_lit 266685774444983207137288011228577494640602308766118199896114634293793513872136939188733470620968877452751023312896 

noncomputable def Ns564p1399 := BSN.sin_dyadic_bound_f 621181306 536870912 4 3 536870912 268435456 Ns564p1396 Ns564p181 Ns564p1397 Ns564p1398 Ns564p184 Ns564p1397 491568235 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 621181306) qz375 0 3 Ns564p1396 Ns564p181 Ns564p1397 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 621181306) qz376 0 3 Ns564p1398 Ns564p184 Ns564p1397 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1400 := Ns564p1330 213413 BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 38209871 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 491568235 536870912) qz191 rfl rfl (Ns564p1391 rfl) (Ns564p1366 rfl) RS565to576.d35 RS565to576.d37 RS565to576.d39 RS565to576.d41 RS565to576.d17 (Ns564p1395 rfl rfl) (Ns564p1399 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1401 := nat_lit 35130050468335453764149357762669786572105887985581187221649197007294092648579965541363326331648220823394086424576 

noncomputable def Ns564p1402 := nat_lit 16497089340657860377664860398322687248011036179432280997654920224518716617174611329764307956776762785796096 

noncomputable def Ns564p1403 := nat_lit 212863544469225120505932277640924602434331954656372307000498471725222567438492809305420034401593914012102154915840 

noncomputable def Ns564p1404 := BSN.cos_dyadic_bound_f 710314386 536870912 4 3 536870912 268435456 Ns564p1401 Ns564p133 Ns564p1402 Ns564p1403 Ns564p136 Ns564p1402 131644232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 710314386) qz373 0 3 Ns564p1401 Ns564p133 Ns564p1402 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 710314386) qz374 0 3 Ns564p1403 Ns564p136 Ns564p1402 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1405 := nat_lit 53631555163415140558905215997204045493940504168757028991315157299470285700123613688015621383054042918087427096576 

noncomputable def Ns564p1406 := nat_lit 3352053749249148436139285195367906533448218829235275732664572926196998442304098700371776815207231233458176 

noncomputable def Ns564p1407 := nat_lit 268059068504919363281835975592226372970249094608228105463609015137830558563376144389698464400180772697246569332736 

noncomputable def Ns564p1408 := BSN.sin_dyadic_bound_f 621979276 536870912 4 3 536870912 268435456 Ns564p1405 Ns564p181 Ns564p1406 Ns564p1407 Ns564p184 Ns564p1406 491888516 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 621979276) qz375 0 3 Ns564p1405 Ns564p181 Ns564p1406 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 621979276) qz376 0 3 Ns564p1407 Ns564p184 Ns564p1406 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1409 := Ns564p1328 248601 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 174 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131644232 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 491888516 536870912) qz191 rfl rfl (Ns564p1400 rfl) (Ns564p1366 rfl) RS565to576.d43 RS565to576.d45 RS565to576.d47 RS565to576.d49 RS565to576.d17 (Ns564p1404 rfl rfl) (Ns564p1408 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1410 := nat_lit 8244520389401193454500221513997153745871779928883870888636282584055152640 

noncomputable def Ns564p1411 := nat_lit 1076700174790139896707454806348239573864216499448550621703281024434176 

noncomputable def Ns564p1412 := nat_lit 21591048267196322630524958562210838851306500606077697531136077646104887296 

noncomputable def Ns564p1413 := BSN.sin_dyadic_bound_f 425610024 536870912 3 2 536870912 268435456 Ns564p1410 Ns564p143 Ns564p1411 Ns564p1412 Ns564p146 Ns564p1411 382409656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 425610024) qz375 0 2 Ns564p1410 Ns564p143 Ns564p1411 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 425610024) qz376 0 2 Ns564p1412 Ns564p146 Ns564p1411 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1414 := Ns564p1326 Bool.false 355194694 248601 Bool.true 425610024 28296951008113761 1 Bool.false 382409656 Bool.false Bool.false 465586856 265046 BSN.abs_quadSignPos qz377 (BSN.sfrac_eq_quadSignPos_mul Bool.false 382409656 536870912) qz191 rfl (Ns564p1409 rfl) (Ns564p1366 rfl) RS565to576.d51 RS565to576.d53 RS565to576.d17 (Ns564p1413 rfl rfl) rfl 

noncomputable def Ns564p1415 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) 465586856 536870912 265046 536870912 465586856 536870912 265046 536870912 499920079991865344 58198357 33554432 132523 134217728 (Ns564p1414 rfl rfl rfl rfl) 

noncomputable def Ns564p1416 := @Enclosure.Real.IsNear.mulLit_ff qz693 (Zeta.RiemannSiegel.correction qz190) 594853 2097152 1 33554432 110203854411525 281474976710656 104621127629 10995116277760000 65555093408258880825 590295810358705651712 

noncomputable abbrev qz697 := (@HPow.hPow Real Real Real qz7 qz189 qz9)

noncomputable def Ns564p1417 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz697 1 1 0 1 594853 2097152 1 33554432 594853 2097152 1 33554432 

noncomputable def Ns564p1418 := @Enclosure.Real.IsNear.sqrt_image qz189 5183592763361 33554432000 485323 33554432000 417052148 417052188 33554432 (@Enclosure.Real.IsNear.of_eq qz189 (@HMul.hMul Real Real Real qz5 qz188 qz3) Bool.false 5183592763361 33554432000 485323 33554432000 (BSN.t_div_two_pi_mk qz188 970646 1000 qz191) (@Enclosure.Real.IsNear.mulLit_ff qz188 qz3 970646 1000 0 1 10680707 67108864 1 67108864 5183592763361 33554432000 485323 33554432000 (Enclosure.Real.IsNear.const Bool.false 970646 1000) RS565to576.d56 rfl)) 

noncomputable abbrev qz785 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 970646 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz698 := qz785

noncomputable abbrev qz508 := qz698

noncomputable abbrev qz197 := qz508

noncomputable def Ns564p1419 := @Enclosure.Real.IsNear.sqrt_image qz197 52131521 4194304 5 8388608 118296018 118296024 33554432 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 834104336 67108864 40 67108864 52131521 4194304 5 8388608 (Ns564p1418 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns564p1420 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz197) 118296021 33554432 3 33554432 9517647 9517649 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz197) Bool.false 236592042 67108864 6 67108864 118296021 33554432 3 33554432 (Ns564p1419 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns564p1421 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 19035296 67108864 2 67108864 594853 2097152 1 33554432 (Ns564p1420 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz509 := (@HMul.hMul Real Real Real qz588 qz586 qz692)

noncomputable abbrev qz198 := (Real.cos qz509)

noncomputable abbrev qz699 := (@HMul.hMul Real Real Real qz741 qz784 qz784)

noncomputable abbrev qz510 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz699 qz692) qz604)

noncomputable abbrev qz199 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz510))

noncomputable def Ns564p1422 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz190) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz198) qz199) Bool.false 110203854411525 

noncomputable def Ns564p1423 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz198) qz199 74361525 67108864 319 

noncomputable abbrev qz200 := (@Neg.neg Real Real.instNeg (Real.cos qz509))

noncomputable def Ns564p1424 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz198) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz200)) Bool.true 74361525 67108864 319 67108864 (BSN.inv_eq_neg_inv_neg qz198) 

noncomputable def Ns564p1425 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz200) Bool.false 74361525 67108864 319 67108864 74361525 67108864 

noncomputable def Ns564p1426 := @Enclosure.Real.IsNear.recentre' qz198 Bool.true 60563573 67108864 661897216 171798691840000 60563573 67108864 40399 10485760000 

noncomputable abbrev qz201 := qz509

noncomputable def Ns564p1427 := @Enclosure.Real.IsNear.cos_image qz201 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 180942969) qz396) Bool.false 180942969 67108864 63 16777216 Bool.true 60563573 67108864 1 

noncomputable def Ns564p1428 := nat_lit 134930377076141809963658467 

noncomputable def Ns564p1429 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz190 884279719003555 140737488355328 1 500000000000000 1799873 4194304 5 8388608 1591591190682085548515 590295810358705651712 Ns564p1428 

noncomputable def Ns564p1430 := @Enclosure.Real.IsNear.subLit_ff_p qz197 qz1 52131521 4194304 5 8388608 12 1 0 1 1799873 1799873 4194304 5 

noncomputable def Ns564p1431 := @Ns564p1430 8388608 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 834104336 67108864 40 67108864 52131521 4194304 5 8388608 (Ns564p1418 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns564p1432 := @Enclosure.Real.IsNear.recentre' qz201 Bool.false 1591591190682085548515 590295810358705651712 Ns564p1428 Ns564p201 180942969 67108864 63 16777216 (@Ns564p1429 Ns564p201 RS565to576.d55 (Ns564p1431 rfl rfl) rfl) 

noncomputable def Ns564p1433 := nat_lit 10884820113893404964814848 

noncomputable def Ns564p1434 := nat_lit 618041063345714253583779908260055443567810816112365264373476956018538929639322588447799294785 

noncomputable def Ns564p1435 := nat_lit 327741656770693577143733589080867672771938020995392187431081708956575352426110658989570881 

noncomputable def Ns564p1436 := nat_lit 1618148346080194303118333714870204756921683285403154581246122657281672265151440695343967419201 

noncomputable def Ns564p1437 := BSN.sin_dyadic_bound_f 154682597239 137438953472 3 2 67108864 20500001 Ns564p1434 Ns564p207 Ns564p1435 Ns564p1436 Ns564p210 Ns564p1435 60563573 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 154682597239) qz371 0 2 Ns564p1434 Ns564p207 Ns564p1435 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 154682597239) qz372 0 2 Ns564p1436 Ns564p210 Ns564p1435 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1438 := @Ns564p1427 10240000 (Ns564p1432 rfl) (Enclosure.sfrac_false_div 180942969 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 180942969) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p1433) qz397) 226375608064910080 72057594037927936 Bool.false 60563573 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 180942969 67108864 226375608064910080 72057594037927936 0 Ns564p1433 Ns564p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 60563573 67108864 Ns564p1433 Ns564p112 154682597239 137438953472 20500001 20480000 (Ns564p1437 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p1439 := @Enclosure.Real.IsNear.inv_image qz200 60563573 67108864 40399 10485760000 37180603 37180922 33554432 (@Enclosure.Real.IsNear.neg qz198 Bool.true 60563573 67108864 40399 10485760000 (Ns564p1426 (Ns564p1438 rfl rfl) rfl)) 

noncomputable def Ns564p1440 := Ns564p1424 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz200) Bool.false 74361525 67108864 319 67108864 (@Ns564p1425 319 67108864 (Ns564p1439 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p1441 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true 11856008 33554432 

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz355 qz352 qz510)

noncomputable def Ns564p1442 := @Enclosure.Real.IsNear.cos_image qz202 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 129649739)) qz396) Bool.true 129649739 67108864 

noncomputable def Ns564p1443 := nat_lit 4783231119546999420797063645 

noncomputable def Ns564p1444 := nat_lit 2475880078570760549798248448 

noncomputable def Ns564p1445 := nat_lit 2103308885256340775076218978764027 

noncomputable def Ns564p1446 := @Enclosure.Real.IsNear.recentre' qz202 Bool.true Ns564p1443 Ns564p1444 Ns564p1445 

noncomputable abbrev qz203 := qz510

noncomputable def Ns564p1447 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz203 884279719003555 140737488355328 1 500000000000000 5409183335039 

noncomputable abbrev qz511 := (@HSub.hSub Real Real Real qz592 qz699 qz692)

noncomputable abbrev qz204 := qz511

noncomputable def Ns564p1448 := @Enclosure.Real.IsNear.subLit_tf qz204 qz31 4309671707263 17592186044416 77940525 70368744177664 1 16 

noncomputable abbrev qz512 := qz699

noncomputable abbrev qz205 := qz512

noncomputable def Ns564p1449 := @Enclosure.Real.IsNear.subLit_ff_n qz205 qz190 3239542816129 17592186044416 35997485 70368744177664 1799873 4194304 5 8388608 

noncomputable def Ns564p1450 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz190 1799873 4194304 5 8388608 1799873 4194304 5 8388608 3239542816129 17592186044416 

noncomputable def Ns564p1451 := nat_lit 2339062920964733141670759106898150488578223215497090290488350201201645254197350478859176000272095731601 

noncomputable def Ns564p1452 := nat_lit 22555879295115156426238214268317792494872804516304214185021532888099143611415905483103371281784721 

noncomputable def Ns564p1453 := nat_lit 14112402841308377154401698971256602024799321287354502876384640219662442813656660720418948159895954743185 

noncomputable def Ns564p1454 := BSN.cos_dyadic_bound_t 129649739 67108864 4 3 33554432 10240000 Ns564p1451 Ns564p665 Ns564p1452 Ns564p1453 Ns564p668 Ns564p1452 11856008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 129649739) (BSN.cosEvenQ 67108864) 0 3 Ns564p1451 Ns564p665 Ns564p1452 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 129649739) (BSN.cosOddQ 67108864) 0 3 Ns564p1453 Ns564p668 Ns564p1452 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1455 := @Ns564p1441 1214857216 171798691840000 1482001 4194304 74149 10485760000 (@Ns564p1442 117 16777216 Bool.true 11856008 33554432 1 10240000 (@Ns564p1446 Ns564p525 129649739 67108864 117 16777216 (@Ns564p1447 17592186044416 77940525 70368744177664 Ns564p1443 Ns564p1444 Ns564p1445 Ns564p525 RS565to576.d55 (@Ns564p1448 0 1 86546933360624 5409183335039 17592186044416 77940525 70368744177664 (@Ns564p1449 18076073280460029952 4309671707263 17592186044416 77940525 70368744177664 (@Ns564p1450 35997485 70368744177664 (Ns564p1431 rfl rfl) (Ns564p1431 rfl rfl) rfl) (Ns564p1431 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 129649739 67108864) (BSN.cos_neg_of_bound 129649739 67108864 Bool.true 11856008 33554432 1 10240000 (Ns564p1454 rfl rfl)) rfl rfl) 

noncomputable def Ns564p1456 := @Ns564p1416 16000832141119590661 Ns564p85 (Ns564p1417 qz33 (@Enclosure.Real.IsNear.of_eq qz697 (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 594853 2097152 1 33554432 (BSN.rpow_neg_quarter_mk qz189 (BSN.t_div_two_pi_nonneg qz188 970646 1000 qz191)) Ns564p1421) rfl) (@Ns564p1422 281474976710656 104621127629 10995116277760000 (BSN.correction_mk qz190 (BSN.cos_two_pi_p_ne_zero_mk qz188 970646 1000 12 qz191 rfl rfl (@BSN.floor_sqrt_eq_dec qz188 970646 1000 12 qz191 rfl rfl rfl))) (@Ns564p1423 67108864 1482001 4194304 74149 10485760000 110203854411525 281474976710656 104621127629 10995116277760000 Ns564p1440 (Ns564p1455 rfl) rfl)) 

noncomputable def Ns564p1457 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (hardyZApproximantRS₀ qz188) Bool.false 958281230415081343687 590295810358705651712 5844424010051473510661 Ns564p85 (@Eq.refl Real (hardyZApproximantRS₀ qz188)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (@HMul.hMul Real Real Real qz5 qz693 (Zeta.RiemannSiegel.correction qz190))) Bool.false 958281230415081343687 590295810358705651712 5844424010051473510661 Ns564p85 (BSN.hardyZApproximantRS₀_eq qz188 12 (@BSN.floor_sqrt_eq_dec qz188 970646 1000 12 qz191 rfl rfl rfl)) (@Ns564p1325 958281230415081343687 590295810358705651712 5844424010051473510661 Ns564p85 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 12)) Bool.false 58198357 33554432 132523 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (Ns564p1415 (Ns564p1414 rfl rfl rfl rfl) rfl rfl)) (Ns564p1456 rfl) rfl rfl)) 

theorem RS565to576.d68 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz188) Bool.false 958281230415081343687 590295810358705651712 5844424010051473510661 Ns564p85 := Ns564p1457 

noncomputable def Ns564p1458 := nat_lit 36894114797941788998132419264512 

noncomputable abbrev qz786 := (Enclosure.sfrac Bool.false 972516 1000)

noncomputable abbrev qz700 := qz786

noncomputable abbrev qz513 := qz700

noncomputable abbrev qz206 := qz513

noncomputable abbrev qz787 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 972516 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz701 := qz787

noncomputable abbrev qz514 := qz701

noncomputable abbrev qz207 := qz514

noncomputable abbrev qz788 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 972516 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz702 := qz788

noncomputable abbrev qz515 := qz702

noncomputable abbrev qz208 := qz515

noncomputable abbrev qz703 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz207 qz9))

noncomputable def Ns564p1459 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (@HMul.hMul Real Real Real qz5 qz703 (Zeta.RiemannSiegel.correction qz208)) 473495637 134217728 66387 67108864 8328229059880919928585 75557863725914323419136 997271884252862771 377789318629571617095680 Ns564p1458 

noncomputable def Ns564p1460 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin BSN.quadSignPos 11 12 972516 1000 287 536870912 268435456 9007199254740992 Bool.false 1054987183784 4525 1334074092 54 154981288 8 

noncomputable def Ns564p1461 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 972516 1000 174 233 536870912 268435456 9007199254740992 Bool.false 1054987183784 4525 

noncomputable def Ns564p1462 := Ns564p1461 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.true 816758357 213815 Bool.true 491514944 Bool.true 498866357 28296951008113761 1 Bool.false 327158398 Bool.true Bool.false 430113057 Bool.true Bool.true 1049898892 

noncomputable def Ns564p1463 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 972516 1000 36 109 536870912 268435456 9007199254740992 Bool.false 1054987183784 4525 

noncomputable def Ns564p1464 := Ns564p1463 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 871061960 174615 Bool.true 362248557 Bool.true 296605299 28296951008113761 1 Bool.false 419225892 Bool.false Bool.false 281745412 Bool.true Bool.true 816758357 

noncomputable def Ns564p1465 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 972516 1000 141 46 536870912 268435456 9007199254740992 Bool.false 1054987183784 4525 

noncomputable def Ns564p1466 := Ns564p1465 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.true 490490383 129749 Bool.false 574312073 Bool.false 204764020 28296951008113761 1 Bool.false 470876295 Bool.true Bool.false 498293209 Bool.true Bool.true 871061960 

noncomputable def Ns564p1467 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 972516 1000 392 254 536870912 268435456 9007199254740992 Bool.false 1054987183784 4525 

noncomputable def Ns564p1468 := Ns564p1467 744261104 53 268435448 8 864060384 53 240095976 8 Bool.true 454254967 76620 Bool.false 601928205 Bool.false 472661818 28296951008113761 1 Bool.false 233335501 Bool.false Bool.false 341901859 Bool.true Bool.true 490490383 

noncomputable def Ns564p1469 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 972516 1000 821 570 536870912 268435456 9007199254740992 Bool.false 1054987183784 4525 

noncomputable def Ns564p1470 := Ns564p1469 372130544 53 379625064 8 589812976 53 309962568 8 Bool.false 298256 4581 Bool.false 722778442 Bool.false 695159392 28296951008113761 1 Bool.false 523396445 Bool.true Bool.false 146282160 Bool.true Bool.true 454254967 

noncomputable def Ns564p1471 := nat_lit 9139617396834645095498202334921183564680367844242227 

noncomputable def Ns564p1472 := nat_lit 4651046763970770831313320504242480406878832558080 

noncomputable def Ns564p1473 := nat_lit 417566167859411701242206711316480000 

noncomputable def Ns564p1474 := nat_lit 2436538976369014561747892558236043182080 

noncomputable abbrev qz789 := (@Eq.refl Real (Enclosure.sfrac Bool.false 972516 1000))

noncomputable abbrev qz704 := qz789

noncomputable abbrev qz516 := qz704

noncomputable abbrev qz209 := qz516

noncomputable def Ns564p1475 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz206 972516 1000 3783150481024 16000000 1945032 4000 2000 Ns564p1473 Ns564p1474 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns564p1476 := nat_lit 862522510635295633409141071038808347976645325337972367687680 

noncomputable abbrev qz705 := (@HSub.hSub Real Real Real qz745 qz746 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz747 (@Nat.cast Real Real.instNatCast 1945032))))

noncomputable abbrev qz517 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 972516 4000) (Real.log (Enclosure.sfrac Bool.false 3783150481024 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz705))

noncomputable abbrev qz706 := (Enclosure.sfrac Bool.false 972516 2000)

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz517 qz706) (@HMul.hMul Real Real Real qz355 qz706 (Real.log Real.pi)))

noncomputable def Ns564p1477 := @Enclosure.Real.IsNear.addLit_ft_p qz210 (Enclosure.sfrac Bool.true Ns564p1473 Ns564p1474) 353994988064044762071 180143985094819840 34515591685929903 4096000000000000000000 Ns564p1473 Ns564p1474 0 1 Ns564p1476 

noncomputable def Ns564p1478 := nat_lit 148476259441697520173344358400000 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz359 qz517 qz706)

noncomputable def Ns564p1479 := @Enclosure.Real.IsNear.subLit_ff_p qz211 (@HMul.hMul Real Real Real qz5 qz706 (Real.log Real.pi)) 11356731661184849059839 4503599627370496000 11969205986397 4000000000000000000 9338769911169 16777216000 729387 134217728000 Ns564p1478 353994988064044762071 180143985094819840 

noncomputable def Ns564p1480 := nat_lit 22713463322369698119678000 

noncomputable abbrev qz212 := qz517

noncomputable def Ns564p1481 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz706 13546643008790771703807 4503599627370496000 11969205986397 4000000000000000000 972516 2000 0 1 Ns564p1480 11356731661184849059839 4503599627370496000 11969205986397 4000000000000000000 

noncomputable def Ns564p1482 := nat_lit 30504328203255627107246152716581339136 

noncomputable def Ns564p1483 := nat_lit 119668945523075338924457984 

noncomputable def Ns564p1484 := nat_lit 119799343426163150051002460244218486940982006947502512330643134065743097965603088667437569629751818242521892287073931584560814822992171547087780285647925662584797363206739571419539046400 

noncomputable def Ns564p1485 := nat_lit 3454913976122031282188098690405283978754123431389943342473656081024316702019240547806768349844966126057864284737743185365403904704520768917002321052453968949087931682648769093791907840 

noncomputable def Ns564p1486 := nat_lit 202660146481124071614206250042889089440295391695600958799693398122480757577586206978332100834539578059529173063576426203471985508874517669874172220234182110919144995110529269760 

noncomputable def Ns564p1487 := BSN.log_dyadic_bound 1685998481024 5880302481024 8 7 Ns564p1484 268435456 81920000 Ns564p1485 Ns564p1486 158370715 7566300962048 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1685998481024) (BSN.artanhQ 5880302481024) 0 7 Ns564p1485 Ns564p1484 Ns564p1486 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz518 := (Real.log (Enclosure.sfrac Bool.false 3783150481024 16000000))

noncomputable def Ns564p1488 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 972516 4000) qz518 972516 4000 0 1 55725195223034983 4503599627370496 48828193 4000000000000000 13548410989381272381807 4503599627370496000 11871549735897 4000000000000000000 (Enclosure.Real.IsNear.const Bool.false 972516 4000) (BSN.isNear_log_sfrac 3783150481024 16000000 55725195223034983 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3783150481024) qz362)) Bool.false Ns564p1483 Ns564p112 1000001392640000 81920000000000000000000 55725195223034983 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3783150481024 16000000 17 7566300962048 4194304000000 158370715 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns564p1487 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p1489 := BSN.arctan_dyadic_bound_f 1000 1945032 1 0 33554432 10240000 0 1 1 0 1 1 17251 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1945032) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1945032) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns564p1490 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1945032))) 884279719003555 562949953421312 1 2000000000000000 17251 33554432 1 10240000 29661792250637422952448 883990295250339 562949953421312 195312501 2000000000000000 qz17 (Ns564p1489 rfl) rfl rfl 

noncomputable abbrev qz519 := (@HMul.hMul Real Real Real qz588 qz593 qz705)

noncomputable abbrev qz213 := qz519

noncomputable abbrev qz520 := qz705

noncomputable abbrev qz214 := qz520

noncomputable def Ns564p1491 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 972516 4000) qz518) qz213 13548410989381272381807 4503599627370496000 11871549735897 4000000000000000000 883990295250339 2251799813685248 195312501 8000000000000000 Ns564p1482 13546643008790771703807 4503599627370496000 11969205986397 4000000000000000000 (Ns564p1488 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz214 1 4 0 1 883990295250339 562949953421312 195312501 2000000000000000 883990295250339 2251799813685248 195312501 8000000000000000 qz369 Ns564p1490 rfl) 

noncomputable def Ns564p1492 := @Ns564p1477 Ns564p1471 Ns564p1472 34515591685929903 4096000000000000000000 (@Ns564p1479 34515591685929903 4096000000000000000000 (Ns564p1481 (Ns564p1491 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 972516 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz706 (Real.log Real.pi) 972516 2000 0 1 38410761 33554432 3 268435456 9338769911169 16777216000 729387 134217728000 (Enclosure.Real.IsNear.const Bool.false 972516 2000) RS565to576.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns564p1473 Ns564p1474) 

noncomputable def Ns564p1493 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns564p1471 Ns564p1472 34515591685929903 4096000000000000000000 131873397973 67108864 283 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz370 qz210 (Enclosure.sfrac Bool.true Ns564p1473 Ns564p1474)) Bool.false Ns564p1471 Ns564p1472 34515591685929903 4096000000000000000000 Ns564p1475 (Ns564p1492 rfl rfl)) 

noncomputable def Ns564p1494 := BSN.sin_dyadic_bound_f 76354991 137438953472 1 0 67108864 20500001 0 1 1 0 1 1 37282 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 76354991) qz371 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 76354991) qz372 0 0 rfl) rfl rfl 

noncomputable def Ns564p1495 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz206) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 131873397973) qz396) Bool.false 131873397973 67108864 283 33554432 Bool.false 37282 67108864 1 10240000 (Ns564p1493 rfl) (Enclosure.sfrac_false_div 131873397973 67108864) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 131873397973) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5373004848003427598336) qz397) 226375608064910080 72057594037927936 Bool.false 37282 67108864 312 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q3 131873397973 67108864 226375608064910080 72057594037927936 312 5373004848003427598336 Ns564p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 37282 67108864 5373004848003427598336 Ns564p112 76354991 137438953472 20500001 20480000 (Ns564p1494 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p1496 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns564p1471 Ns564p1472 34515591685929903 4096000000000000000000 1054987183784 536870912 4525 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz370 qz210 (Enclosure.sfrac Bool.true Ns564p1473 Ns564p1474)) Bool.false Ns564p1471 Ns564p1472 34515591685929903 4096000000000000000000 Ns564p1475 (Ns564p1492 rfl rfl)) 

noncomputable def Ns564p1497 := Ns564p1470 76620 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 821 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 523396445 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 570 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 146282160 536870912) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) Bool.false 18641 33554432 178923 20971520000 298256 536870912 4581 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.false 18641 33554432 178923 20971520000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz206) qz206) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.false 37282 67108864 2931474432 343597383680000 18641 33554432 178923 20971520000 (Ns564p1495 rfl rfl) rfl)) rfl) (Ns564p1496 rfl) RS565to576.d7 

noncomputable def Ns564p1498 := nat_lit 97847660305210903802476663835355694483030043315591213533121492065818501591309606569013112839619566563126880833536 

noncomputable def Ns564p1499 := nat_lit 20326485139140081791927432321247828845977990640616351981596626920446802194239197289968684423543433564327936 

noncomputable def Ns564p1500 := nat_lit 488910030829900975398490763260924090691897184329592733872583938434741111399768094718445268971539524614012333264896 

noncomputable def Ns564p1501 := BSN.sin_dyadic_bound_f 722778442 536870912 4 3 536870912 268435456 Ns564p1498 Ns564p181 Ns564p1499 Ns564p1500 Ns564p184 Ns564p1499 523396445 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 722778442) qz375 0 3 Ns564p1498 Ns564p181 Ns564p1499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 722778442) qz376 0 3 Ns564p1500 Ns564p184 Ns564p1499 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1502 := nat_lit 32221705408968065023493460245888485338259752359031748121953703251876182916504254141460035848319058447091070140416 

noncomputable def Ns564p1503 := nat_lit 12735404292916338567605901276297352275951032412272789473849782826743731552542297958249121146169089522139136 

noncomputable def Ns564p1504 := nat_lit 195260595887210912043468138411215519705716027177731349905999777851392549135181617264433467119994723472571388395520 

noncomputable def Ns564p1505 := BSN.cos_dyadic_bound_f 695159392 536870912 4 3 536870912 268435456 Ns564p1502 Ns564p133 Ns564p1503 Ns564p1504 Ns564p136 Ns564p1503 146282160 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 695159392) qz373 0 3 Ns564p1502 Ns564p133 Ns564p1503 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 695159392) qz374 0 3 Ns564p1504 Ns564p136 Ns564p1503 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1506 := nat_lit 18099719208858822721679634650034098876959121177932649172129590346445132671417244225790856982975807831265125640625 

noncomputable def Ns564p1507 := nat_lit 2262227754815852105901006277864614019449641255878056219611169609931020384661078485010525903843086181640625 

noncomputable def Ns564p1508 := nat_lit 109736163789111228227991300874619163204508757693529505930357118034514624223205187111652404457988784764446975240625 

noncomputable def Ns564p1509 := BSN.cos_dyadic_bound_f 601928205 536870912 4 3 536870912 268435456 Ns564p1506 Ns564p133 Ns564p1507 Ns564p1508 Ns564p136 Ns564p1507 233335501 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 601928205) qz373 0 3 Ns564p1506 Ns564p133 Ns564p1507 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 601928205) qz374 0 3 Ns564p1508 Ns564p136 Ns564p1507 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1510 := nat_lit 6968609756011873613765018653683434397108574387780773936458655209127321856 

noncomputable def Ns564p1511 := nat_lit 2491174607622065898247414142030266283560704728859841488530268278661376 

noncomputable def Ns564p1512 := nat_lit 20900846918820376709498561132766242658758601753884602126398905090824642816 

noncomputable def Ns564p1513 := BSN.cos_dyadic_bound_f 472661818 536870912 3 2 536870912 268435456 Ns564p1510 Ns564p170 Ns564p1511 Ns564p1512 Ns564p173 Ns564p1511 341901859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 472661818) qz373 0 2 Ns564p1510 Ns564p170 Ns564p1511 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 472661818) qz374 0 2 Ns564p1512 Ns564p173 Ns564p1511 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1514 := Ns564p1468 129749 BSN.abs_quadSignPos (BSN.cos_quad_nat0 392 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 233335501 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 254 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 341901859 536870912) qz209 rfl rfl (Ns564p1497 RS565to576.d9 RS565to576.d11 RS565to576.d13 RS565to576.d17 (Ns564p1501 rfl rfl) (Ns564p1505 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns564p1496 rfl) RS565to576.d19 RS565to576.d21 RS565to576.d23 RS565to576.d25 RS565to576.d17 (Ns564p1509 rfl rfl) (Ns564p1513 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns564p1515 := nat_lit 27342680956196613014447011522271035531120750787047097045566030511087594305 

noncomputable def Ns564p1516 := nat_lit 11835417099549250548507361019968686071999240935926659426913812830006081 

noncomputable def Ns564p1517 := nat_lit 71592621352829954346473161116677524708818729480750896718362695641599880001 

noncomputable def Ns564p1518 := BSN.sin_dyadic_bound_f 574312073 536870912 3 2 536870912 268435456 Ns564p1515 Ns564p143 Ns564p1516 Ns564p1517 Ns564p146 Ns564p1516 470876295 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 574312073) qz375 0 2 Ns564p1515 Ns564p143 Ns564p1516 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 574312073) qz376 0 2 Ns564p1517 Ns564p146 Ns564p1516 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1519 := nat_lit 245362867069175479938969590454695388526199476112429531625002381516800000 

noncomputable def Ns564p1520 := nat_lit 3090503056782445591109925165891557655376247106636508815385600000000 

noncomputable def Ns564p1521 := nat_lit 736082420201412874925726551513754382463287675843075321857376373350400000 

noncomputable def Ns564p1522 := BSN.cos_dyadic_bound_f 204764020 536870912 3 2 536870912 268435456 Ns564p1519 Ns564p170 Ns564p1520 Ns564p1521 Ns564p173 Ns564p1520 498293209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 204764020) qz373 0 2 Ns564p1519 Ns564p170 Ns564p1520 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 204764020) qz374 0 2 Ns564p1521 Ns564p173 Ns564p1520 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1523 := Ns564p1466 174615 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 141 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 470876295 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 498293209 536870912) qz209 rfl rfl (Ns564p1514 rfl rfl) (Ns564p1496 rfl) RS565to576.d27 RS565to576.d29 RS565to576.d31 RS565to576.d33 RS565to576.d17 (Ns564p1518 rfl rfl) (Ns564p1522 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1524 := nat_lit 2403637740700222778205795114640330600552940937928689620479882659907016481 

noncomputable def Ns564p1525 := nat_lit 296519536944854701044242530579221596690457671161482947154140239796001 

noncomputable def Ns564p1526 := nat_lit 7210320183026778625215296858859833358465441898443745895545339699241457441 

noncomputable def Ns564p1527 := BSN.cos_dyadic_bound_f 362248557 536870912 3 2 536870912 268435456 Ns564p1524 Ns564p170 Ns564p1525 Ns564p1526 Ns564p173 Ns564p1525 419225892 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 362248557) qz373 0 2 Ns564p1524 Ns564p170 Ns564p1525 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 362248557) qz374 0 2 Ns564p1526 Ns564p173 Ns564p1525 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1528 := nat_lit 1944420923124402853193601829855025572578916659689829156531347005576645665 

noncomputable def Ns564p1529 := nat_lit 59900610015124006911353135889716409154434501927960208633667181677601 

noncomputable def Ns564p1530 := nat_lit 5092434007195316319495862601686007434949007881422621569625263839168498721 

noncomputable def Ns564p1531 := BSN.sin_dyadic_bound_f 296605299 536870912 3 2 536870912 268435456 Ns564p1528 Ns564p143 Ns564p1529 Ns564p1530 Ns564p146 Ns564p1529 281745412 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 296605299) qz375 0 2 Ns564p1528 Ns564p143 Ns564p1529 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 296605299) qz376 0 2 Ns564p1530 Ns564p146 Ns564p1529 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1532 := Ns564p1464 213815 BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 419225892 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 281745412 536870912) qz209 rfl rfl (Ns564p1523 rfl) (Ns564p1496 rfl) RS565to576.d35 RS565to576.d37 RS565to576.d39 RS565to576.d41 RS565to576.d17 (Ns564p1527 rfl rfl) (Ns564p1531 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1533 := nat_lit 8149242819206354764692334597736377960844002836034360508022684562380292096 

noncomputable def Ns564p1534 := nat_lit 3406385638757114616427468705588554171260590213731612646895692615254016 

noncomputable def Ns564p1535 := nat_lit 24440915686341550064844148855797956774189487327675618298774262301910368256 

noncomputable def Ns564p1536 := BSN.cos_dyadic_bound_f 491514944 536870912 3 2 536870912 268435456 Ns564p1533 Ns564p170 Ns564p1534 Ns564p1535 Ns564p173 Ns564p1534 327158398 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 491514944) qz373 0 2 Ns564p1533 Ns564p170 Ns564p1534 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 491514944) qz374 0 2 Ns564p1535 Ns564p173 Ns564p1534 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1537 := nat_lit 15563425999042539714013165482865149300199606717561206666405067032072538465 

noncomputable def Ns564p1538 := nat_lit 3835957021714935978468142439310484447235624824937867252276394468559201 

noncomputable def Ns564p1539 := nat_lit 40755143209933398878450294510221269287608207534372308531700061397717076321 

noncomputable def Ns564p1540 := BSN.sin_dyadic_bound_f 498866357 536870912 3 2 536870912 268435456 Ns564p1537 Ns564p143 Ns564p1538 Ns564p1539 Ns564p146 Ns564p1538 430113057 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 498866357) qz375 0 2 Ns564p1537 Ns564p143 Ns564p1538 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 498866357) qz376 0 2 Ns564p1539 Ns564p146 Ns564p1538 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1541 := Ns564p1462 249071 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 174 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 327158398 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 430113057 536870912) qz209 rfl rfl (Ns564p1532 rfl) (Ns564p1496 rfl) RS565to576.d43 RS565to576.d45 RS565to576.d47 RS565to576.d49 RS565to576.d17 (Ns564p1536 rfl rfl) (Ns564p1540 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1542 := nat_lit 5803640267832859926611387010602583983128058633406699898805616490105585920 

noncomputable def Ns564p1543 := nat_lit 533578771049962492600992566798634431320119820913963199794062940487936 

noncomputable def Ns564p1544 := nat_lit 15199146335837695106613231039803379309589444798259877127881709943610982656 

noncomputable def Ns564p1545 := BSN.sin_dyadic_bound_f 389852046 536870912 3 2 536870912 268435456 Ns564p1542 Ns564p143 Ns564p1543 Ns564p1544 Ns564p146 Ns564p1543 356482436 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 389852046) qz375 0 2 Ns564p1542 Ns564p143 Ns564p1543 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 389852046) qz376 0 2 Ns564p1544 Ns564p146 Ns564p1543 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1546 := Ns564p1460 Bool.true 1049898892 249071 Bool.true 389852046 28296951008113761 1 Bool.false 356482436 Bool.false Bool.true 946991274 265548 BSN.abs_quadSignPos qz377 (BSN.sfrac_eq_quadSignPos_mul Bool.false 356482436 536870912) qz209 rfl (Ns564p1541 rfl) (Ns564p1496 rfl) RS565to576.d51 RS565to576.d53 RS565to576.d17 (Ns564p1545 rfl rfl) rfl 

noncomputable def Ns564p1547 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) 946991274 536870912 265548 536870912 946991274 536870912 265548 536870912 1016824137856843776 473495637 134217728 66387 67108864 (Ns564p1546 rfl rfl rfl rfl) 

noncomputable def Ns564p1548 := @Enclosure.Real.IsNear.mulLit_ff qz703 (Zeta.RiemannSiegel.correction qz208) 19026139 67108864 1 67108864 437725649953515 1125899906842624 261504239957 28147497671065600 8328229059880919928585 75557863725914323419136 

noncomputable abbrev qz707 := (@HPow.hPow Real Real Real qz7 qz207 qz9)

noncomputable def Ns564p1549 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz707 1 1 0 1 19026139 67108864 1 67108864 19026139 67108864 1 67108864 

noncomputable def Ns564p1550 := @Enclosure.Real.IsNear.sqrt_image qz207 2596789612203 16777216000 243129 16777216000 417453691 417453731 33554432 (@Enclosure.Real.IsNear.of_eq qz207 (@HMul.hMul Real Real Real qz5 qz206 qz3) Bool.false 2596789612203 16777216000 243129 16777216000 (BSN.t_div_two_pi_mk qz206 972516 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz206 qz3 972516 1000 0 1 10680707 67108864 1 67108864 2596789612203 16777216000 243129 16777216000 (Enclosure.Real.IsNear.const Bool.false 972516 1000) RS565to576.d56 rfl)) 

noncomputable abbrev qz790 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 972516 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz708 := qz790

noncomputable abbrev qz521 := qz708

noncomputable abbrev qz215 := qz521

noncomputable def Ns564p1551 := @Enclosure.Real.IsNear.sqrt_image qz215 417453711 33554432 5 8388608 118352953 118352959 33554432 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 834907422 67108864 40 67108864 417453711 33554432 5 8388608 (Ns564p1550 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns564p1552 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz215) 29588239 8388608 3 33554432 9513069 9513070 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz215) Bool.false 236705912 67108864 6 67108864 29588239 8388608 3 33554432 (Ns564p1551 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns564p1553 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 19026139 67108864 1 67108864 19026139 67108864 1 67108864 (Ns564p1552 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz216 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz515))

noncomputable abbrev qz709 := (@HMul.hMul Real Real Real qz741 qz788 qz788)

noncomputable abbrev qz522 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz709 qz702) qz604)

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz522))

noncomputable def Ns564p1554 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz216) qz217) Bool.false 437725649953515 

noncomputable def Ns564p1555 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz216) qz217 35991951 33554432 149 

noncomputable abbrev qz710 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz216))

noncomputable def Ns564p1556 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz216) (@Neg.neg Real Real.instNeg qz710) Bool.true 35991951 33554432 149 33554432 (BSN.inv_eq_neg_inv_neg qz216) 

noncomputable def Ns564p1557 := @Enclosure.Real.IsNear.recentre' qz710 Bool.false 71983902 67108864 298 67108864 35991951 33554432 

noncomputable def Ns564p1558 := @Enclosure.Real.IsNear.recentre' qz216 Bool.true 62563983 67108864 661897216 171798691840000 62563983 67108864 40399 10485760000 

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz355 qz352 qz515)

noncomputable def Ns564p1559 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 185988907) qz396) Bool.false 185988907 67108864 63 16777216 Bool.true 62563983 67108864 1 

noncomputable def Ns564p1560 := nat_lit 134930377077004116990127331 

noncomputable def Ns564p1561 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 14800527 33554432 5 8388608 13087805856664528873485 4722366482869645213696 Ns564p1560 

noncomputable def Ns564p1562 := @Enclosure.Real.IsNear.subLit_ff_p qz215 qz1 417453711 33554432 5 8388608 12 1 0 1 14800527 14800527 33554432 5 

noncomputable def Ns564p1563 := @Ns564p1562 8388608 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 834907422 67108864 40 67108864 417453711 33554432 5 8388608 (Ns564p1550 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns564p1564 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 13087805856664528873485 4722366482869645213696 Ns564p1560 Ns564p201 185988907 67108864 63 16777216 (@Ns564p1561 Ns564p201 RS565to576.d55 (Ns564p1563 rfl rfl) rfl) 

noncomputable def Ns564p1565 := nat_lit 11612016417782512991862784 

noncomputable def Ns564p1566 := nat_lit 800628152626314573683988366571070508030562499548173476827325891474478578360989218458519223105 

noncomputable def Ns564p1567 := nat_lit 549822774700268450941929435123109827287542113185707406932212544664011387051496018669222721 

noncomputable def Ns564p1568 := nat_lit 2095993067624166305966063550505461533693007668728629865412725181170368829652126483361133509441 

noncomputable def Ns564p1569 := BSN.sin_dyadic_bound_f 165016678263 137438953472 3 2 67108864 20500001 Ns564p1566 Ns564p207 Ns564p1567 Ns564p1568 Ns564p210 Ns564p1567 62563983 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 165016678263) qz371 0 2 Ns564p1566 Ns564p207 Ns564p1567 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 165016678263) qz372 0 2 Ns564p1568 Ns564p210 Ns564p1567 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1570 := @Ns564p1559 10240000 (Ns564p1564 rfl) (Enclosure.sfrac_false_div 185988907 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 185988907) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p1565) qz397) 226375608064910080 72057594037927936 Bool.false 62563983 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 185988907 67108864 226375608064910080 72057594037927936 0 Ns564p1565 Ns564p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 62563983 67108864 Ns564p1565 Ns564p112 165016678263 137438953472 20500001 20480000 (Ns564p1569 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p1571 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz216) 62563983 67108864 40399 10485760000 35991802 35992100 33554432 (@Enclosure.Real.IsNear.neg qz216 Bool.true 62563983 67108864 40399 10485760000 (Ns564p1558 (Ns564p1570 rfl rfl) rfl)) 

noncomputable def Ns564p1572 := Ns564p1556 (@Enclosure.Real.IsNear.neg qz710 Bool.false 35991951 33554432 149 33554432 (@Ns564p1557 149 33554432 (Ns564p1571 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p1573 := @Enclosure.Real.IsNear.recentre' qz217 Bool.true 12161765 33554432 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz355 qz352 qz522)

noncomputable def Ns564p1574 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 130304635)) qz396) Bool.true 130304635 67108864 

noncomputable def Ns564p1575 := nat_lit 307673121022387960245062304445 

noncomputable def Ns564p1576 := nat_lit 4260798118904428055362470925948331 

noncomputable def Ns564p1577 := @Enclosure.Real.IsNear.recentre' qz219 Bool.true Ns564p1575 Ns564p218 Ns564p1576 

noncomputable abbrev qz220 := qz522

noncomputable def Ns564p1578 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz220 884279719003555 140737488355328 1 500000000000000 347936421485599 

noncomputable abbrev qz523 := (@HSub.hSub Real Real Real qz592 qz709 qz702)

noncomputable abbrev qz221 := qz523

noncomputable def Ns564p1579 := @Enclosure.Real.IsNear.subLit_tf qz221 qz31 277567677307935 1125899906842624 157888765 140737488355328 1 16 

noncomputable abbrev qz524 := qz709

noncomputable abbrev qz222 := qz524

noncomputable def Ns564p1580 := @Enclosure.Real.IsNear.subLit_ff_n qz222 qz208 219055599477729 1125899906842624 74002685 140737488355328 14800527 33554432 5 8388608 

noncomputable def Ns564p1581 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 14800527 33554432 5 8388608 14800527 33554432 5 8388608 219055599477729 1125899906842624 

noncomputable def Ns564p1582 := nat_lit 2387083719685937627860407805154642776141441560155343820800767329260037237828271594916692309397148140625 

noncomputable def Ns564p1583 := nat_lit 23961740948042492919236669721556171520876767110181488642529190587045900998846617533385625244140625 

noncomputable def Ns564p1584 := nat_lit 14400521923416253922344748187515066301659712902204241511287549736627224467069228760041184920004661740625 

noncomputable def Ns564p1585 := BSN.cos_dyadic_bound_t 130304635 67108864 4 3 33554432 10240000 Ns564p1582 Ns564p665 Ns564p1583 Ns564p1584 Ns564p668 Ns564p1583 12161765 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 130304635) (BSN.cosEvenQ 67108864) 0 3 Ns564p1582 Ns564p665 Ns564p1583 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 130304635) (BSN.cosOddQ 67108864) 0 3 Ns564p1584 Ns564p668 Ns564p1583 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1586 := @Ns564p1573 2460434432 343597383680000 12161765 33554432 150173 20971520000 (@Ns564p1574 237 33554432 Bool.true 12161765 33554432 1 10240000 (@Ns564p1577 Ns564p659 130304635 67108864 237 33554432 (@Ns564p1578 1125899906842624 157888765 140737488355328 Ns564p1575 Ns564p218 Ns564p1576 Ns564p659 RS565to576.d55 (@Ns564p1579 0 1 5566982743769584 347936421485599 1125899906842624 157888765 140737488355328 (@Ns564p1580 9313625753627048017920 277567677307935 1125899906842624 157888765 140737488355328 (@Ns564p1581 74002685 140737488355328 (Ns564p1563 rfl rfl) (Ns564p1563 rfl rfl) rfl) (Ns564p1563 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 130304635 67108864) (BSN.cos_neg_of_bound 130304635 67108864 Bool.true 12161765 33554432 1 10240000 (Ns564p1585 rfl rfl)) rfl rfl) 

noncomputable def Ns564p1587 := @Ns564p1548 997271884252862771 377789318629571617095680 (Ns564p1549 qz33 (@Enclosure.Real.IsNear.of_eq qz707 (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 19026139 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz207 (BSN.t_div_two_pi_nonneg qz206 972516 1000 qz209)) Ns564p1553) rfl) (@Ns564p1554 1125899906842624 261504239957 28147497671065600 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz206 972516 1000 12 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz206 972516 1000 12 qz209 rfl rfl rfl))) (@Ns564p1555 33554432 12161765 33554432 150173 20971520000 437725649953515 1125899906842624 261504239957 28147497671065600 Ns564p1572 (Ns564p1586 rfl) rfl)) 

noncomputable def Ns564p1588 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (hardyZApproximantRS₀ qz206) Bool.true 274882575854225374744329 75557863725914323419136 374722857462059260211 377789318629571617095680 (@Eq.refl Real (hardyZApproximantRS₀ qz206)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (@HMul.hMul Real Real Real qz5 qz703 (Zeta.RiemannSiegel.correction qz208))) Bool.true 274882575854225374744329 75557863725914323419136 374722857462059260211 377789318629571617095680 (BSN.hardyZApproximantRS₀_eq qz206 12 (@BSN.floor_sqrt_eq_dec qz206 972516 1000 12 qz209 rfl rfl rfl)) (@Ns564p1459 274882575854225374744329 75557863725914323419136 374722857462059260211 377789318629571617095680 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12)) Bool.true 473495637 134217728 66387 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (Ns564p1547 (Ns564p1546 rfl rfl rfl rfl) rfl rfl)) (Ns564p1587 rfl) rfl rfl)) 

theorem RS565to576.d69 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz206) Bool.true 274882575854225374744329 75557863725914323419136 374722857462059260211 377789318629571617095680 := Ns564p1588 

noncomputable def Ns564p1589 := nat_lit 23611832414348226068480000 

noncomputable def Ns564p1590 := nat_lit 9423730909087059772430593556480 

noncomputable abbrev qz791 := (Enclosure.sfrac Bool.false 973528 1000)

noncomputable abbrev qz711 := qz791

noncomputable abbrev qz525 := qz711

noncomputable abbrev qz223 := qz525

noncomputable abbrev qz792 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 973528 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz712 := qz792

noncomputable abbrev qz526 := qz712

noncomputable abbrev qz224 := qz526

noncomputable abbrev qz793 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 973528 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz713 := qz793

noncomputable abbrev qz527 := qz713

noncomputable abbrev qz225 := qz527

noncomputable abbrev qz714 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz224 qz9))

noncomputable def Ns564p1591 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (@HMul.hMul Real Real Real qz5 qz714 (Zeta.RiemannSiegel.correction qz225)) 154205555 268435456 8307 8388608 8298871671341085258375 75557863725914323419136 61668237176975122767 Ns564p1589 Ns564p1590 

noncomputable def Ns564p1592 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin BSN.quadSignPos 11 12 973528 1000 287 536870912 268435456 9007199254740992 Bool.false 1056357020543 4529 1334074092 54 154981288 8 

noncomputable def Ns564p1593 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 973528 1000 174 233 536870912 268435456 9007199254740992 Bool.false 1056357020543 4529 

noncomputable def Ns564p1594 := Ns564p1593 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.false 302722147 214038 Bool.true 372703433 Bool.true 431838141 28296951008113761 1 Bool.false 412615711 Bool.true Bool.false 386755228 Bool.true Bool.false 55630513 

noncomputable def Ns564p1595 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 973528 1000 36 109 536870912 268435456 9007199254740992 Bool.false 1056357020543 4529 

noncomputable def Ns564p1596 := Ns564p1595 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.false 157651918 174798 Bool.true 122200174 Bool.true 120549999 28296951008113761 1 Bool.false 523023521 Bool.false Bool.false 119539546 Bool.true Bool.false 302722147 

noncomputable def Ns564p1597 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 973528 1000 142 46 536870912 268435456 9007199254740992 Bool.false 1056357020543 4529 

noncomputable def Ns564p1598 := Ns564p1597 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.false 486459605 129886 Bool.false 127347120 Bool.false 517361807 28296951008113761 1 Bool.false 521838068 Bool.true Bool.false 306293826 Bool.true Bool.false 157651918 

noncomputable def Ns564p1599 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 973528 1000 393 255 536870912 268435456 9007199254740992 Bool.false 1056357020543 4529 

noncomputable def Ns564p1600 := Ns564p1599 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 603888160 76702 Bool.false 375257870 Bool.false 124754612 28296951008113761 1 Bool.false 345439538 Bool.true Bool.false 123634900 Bool.false Bool.false 486459605 

noncomputable def Ns564p1601 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 973528 1000 823 571 536870912 268435456 9007199254740992 Bool.false 1056357020543 4529 

noncomputable def Ns564p1602 := Ns564p1601 372130544 53 379625064 8 589812976 53 309962568 8 Bool.false 298478680 4589 Bool.false 29389377 Bool.false 624790563 28296951008113761 1 Bool.false 29374700 Bool.false Bool.false 493008221 Bool.false Bool.false 603888160 

noncomputable def Ns564p1603 := nat_lit 8287894504774761149432920284214862123799086668347712817 

noncomputable def Ns564p1604 := nat_lit 4212145510284194869770216960208798616888769773568000 

noncomputable def Ns564p1605 := nat_lit 419743290040252346721253547376640000 

noncomputable def Ns564p1606 := nat_lit 2451791375808065564936386048915329515520 

noncomputable abbrev qz794 := (@Eq.refl Real (Enclosure.sfrac Bool.false 973528 1000))

noncomputable abbrev qz715 := qz794

noncomputable abbrev qz528 := qz715

noncomputable abbrev qz226 := qz528

noncomputable def Ns564p1607 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz223 973528 1000 3791028067136 16000000 1947056 4000 2000 Ns564p1605 Ns564p1606 qz226 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns564p1608 := nat_lit 10863109085298374933784717274926104082905938877936714143498240 

noncomputable abbrev qz716 := (@HSub.hSub Real Real Real qz745 qz746 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz747 (@Nat.cast Real Real.instNatCast 1947056))))

noncomputable abbrev qz529 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 973528 4000) (Real.log (Enclosure.sfrac Bool.false 3791028067136 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz716))

noncomputable abbrev qz717 := (Enclosure.sfrac Bool.false 973528 2000)

noncomputable abbrev qz227 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz529 qz717) (@HMul.hMul Real Real Real qz355 qz717 (Real.log Real.pi)))

noncomputable def Ns564p1609 := @Enclosure.Real.IsNear.addLit_ft_p qz227 (Enclosure.sfrac Bool.true Ns564p1605 Ns564p1606) 4430682862197422891237 2251799813685248000 17275702272671837 2048000000000000000000 Ns564p1605 Ns564p1606 0 1 Ns564p1608 

noncomputable def Ns564p1610 := nat_lit 37167261703292199244813828096000 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz359 qz529 qz717)

noncomputable def Ns564p1611 := @Enclosure.Real.IsNear.subLit_ff_p qz228 (@HMul.hMul Real Real Real qz5 qz717 (Real.log Real.pi)) 5685415659472547160293 2251799813685248000 5990779759613 2000000000000000000 4674243916851 8388608000 365073 67108864000 Ns564p1610 4430682862197422891237 2251799813685248000 

noncomputable def Ns564p1612 := nat_lit 2274166263789018864117200 

noncomputable abbrev qz229 := qz529

noncomputable def Ns564p1613 := @Enclosure.Real.IsNear.subLit_ff_p qz229 qz717 1356302148796246643553 450359962737049600 5990779759613 2000000000000000000 973528 2000 0 1 Ns564p1612 5685415659472547160293 2251799813685248000 5990779759613 2000000000000000000 

noncomputable def Ns564p1614 := nat_lit 3054120925960289701912853475590406144 

noncomputable def Ns564p1615 := nat_lit 119689063174668396968017920 

noncomputable def Ns564p1616 := nat_lit 122065873548290090573248771672136777150174975094784815035454075560142464675483823388956646469981823562268009481298972374188048972673265324559779751121363047872817268765157743544133222400 

noncomputable def Ns564p1617 := nat_lit 3545002188071628977206796333259364920749914620896001022546666649035356087996901651319773891757640807861758888376851232770606554362602842690573423779807875878869494112706667862231613440 

noncomputable def Ns564p1618 := nat_lit 216326982519714695199511423593038663246501167603691781138726032676411304357255836153287184338093077683175332071378623952270749994903513621504809051637294770602085823100915548160 

noncomputable def Ns564p1619 := BSN.log_dyadic_bound 1693876067136 5888180067136 8 7 Ns564p1616 268435456 81920000 Ns564p1617 Ns564p1618 158929092 7582056134272 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1693876067136) (BSN.artanhQ 5888180067136) 0 7 Ns564p1617 Ns564p1616 Ns564p1618 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz530 := (Real.log (Enclosure.sfrac Bool.false 3791028067136 16000000))

noncomputable def Ns564p1620 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 973528 4000) qz530 973528 4000 0 1 55734563234573415 4503599627370496 48828193 4000000000000000 1356478946915694688953 450359962737049600 5941951634363 2000000000000000000 (Enclosure.Real.IsNear.const Bool.false 973528 4000) (BSN.isNear_log_sfrac 3791028067136 16000000 55734563234573415 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3791028067136) qz362)) Bool.false Ns564p1615 Ns564p112 1000001392640000 81920000000000000000000 55734563234573415 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3791028067136 16000000 17 7582056134272 4194304000000 158929092 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns564p1619 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p1621 := BSN.arctan_dyadic_bound_f 1000 1947056 1 0 33554432 10240000 0 1 1 0 1 1 17233 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1947056) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1947056) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns564p1622 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1947056))) 884279719003555 562949953421312 1 2000000000000000 17233 33554432 1 10240000 29661802383736584536064 883990597240227 562949953421312 195312501 2000000000000000 qz17 (Ns564p1621 rfl) rfl rfl 

noncomputable abbrev qz531 := (@HMul.hMul Real Real Real qz588 qz593 qz716)

noncomputable abbrev qz230 := qz531

noncomputable abbrev qz532 := qz716

noncomputable abbrev qz231 := qz532

noncomputable def Ns564p1623 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 973528 4000) qz530) qz230 1356478946915694688953 450359962737049600 5941951634363 2000000000000000000 883990597240227 2251799813685248 195312501 8000000000000000 Ns564p1614 1356302148796246643553 450359962737049600 5990779759613 2000000000000000000 (Ns564p1620 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz231 1 4 0 1 883990597240227 562949953421312 195312501 2000000000000000 883990597240227 2251799813685248 195312501 8000000000000000 qz369 Ns564p1622 rfl) 

noncomputable def Ns564p1624 := @Ns564p1609 Ns564p1603 Ns564p1604 17275702272671837 2048000000000000000000 (@Ns564p1611 17275702272671837 2048000000000000000000 (Ns564p1613 (Ns564p1623 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 973528 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz717 (Real.log Real.pi) 973528 2000 0 1 38410761 33554432 3 268435456 4674243916851 8388608000 365073 67108864000 (Enclosure.Real.IsNear.const Bool.false 973528 2000) RS565to576.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns564p1605 Ns564p1606) 

noncomputable def Ns564p1625 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns564p1603 Ns564p1604 17275702272671837 2048000000000000000000 132044627567 67108864 567 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz370 qz227 (Enclosure.sfrac Bool.true Ns564p1605 Ns564p1606)) Bool.false Ns564p1603 Ns564p1604 17275702272671837 2048000000000000000000 Ns564p1607 (Ns564p1624 rfl rfl)) 

noncomputable def Ns564p1626 := nat_lit 9490348253765091861725184 

noncomputable def Ns564p1627 := nat_lit 198425579181392163123603468314307240797486804121747570196678033724156030668265395218992800000 

noncomputable def Ns564p1628 := nat_lit 109450762347563731244685469059591531191638148829851067356219872611867922065028128100000000 

noncomputable def Ns564p1629 := nat_lit 595057836019481361908321034004802539330077136067583008455321661427244356160666129400778400000 

noncomputable def Ns564p1630 := BSN.cos_dyadic_bound_f 134865960230 137438953472 3 2 67108864 20500001 Ns564p1627 Ns564p578 Ns564p1628 Ns564p1629 Ns564p581 Ns564p1628 37309835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 134865960230) (BSN.cosEvenQ 137438953472) 0 2 Ns564p1627 Ns564p578 Ns564p1628 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 134865960230) (BSN.cosOddQ 137438953472) 0 2 Ns564p1629 Ns564p581 Ns564p1628 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1631 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz223) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 132044627567) qz396) Bool.false 132044627567 67108864 567 67108864 Bool.false 37309835 67108864 1 10240000 (Ns564p1625 rfl) (Enclosure.sfrac_false_div 132044627567 67108864) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 132044627567) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p1626) qz397) 226375608064910080 72057594037927936 Bool.false 37309835 67108864 313 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q0 132044627567 67108864 226375608064910080 72057594037927936 313 Ns564p1626 Ns564p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 37309835 67108864 Ns564p1626 Ns564p112 134865960230 137438953472 20500001 20480000 (Ns564p1630 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p1632 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns564p1603 Ns564p1604 17275702272671837 2048000000000000000000 1056357020543 536870912 4529 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz370 qz227 (Enclosure.sfrac Bool.true Ns564p1605 Ns564p1606)) Bool.false Ns564p1603 Ns564p1604 17275702272671837 2048000000000000000000 Ns564p1607 (Ns564p1624 rfl rfl)) 

noncomputable def Ns564p1633 := Ns564p1602 76702 BSN.abs_quadSignPos (BSN.cos_quad_nat3 823 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 29374700 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 571 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 493008221 536870912) qz226 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) Bool.false 37309835 67108864 358471 41943040000 298478680 536870912 4589 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 37309835 67108864 358471 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz223) qz223) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 37309835 67108864 5873188864 687194767360000 37309835 67108864 358471 41943040000 (Ns564p1631 rfl rfl) rfl)) rfl) (Ns564p1632 rfl) RS565to576.d7 

noncomputable def Ns564p1634 := nat_lit 746038980184960234034659600641 

noncomputable def Ns564p1635 := BSN.sin_dyadic_bound_f 29389377 536870912 2 1 536870912 268435456 Ns564p1634 Ns564p463 Ns564p1634 Ns564p1634 Ns564p464 Ns564p1634 29374700 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 29389377) qz375 0 1 Ns564p1634 Ns564p463 Ns564p1634 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 29389377) qz376 0 1 Ns564p1634 Ns564p464 Ns564p1634 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1636 := nat_lit 54608378976925989860424093942930275226905603656844120929588418622102100660586209227334597779805911007279606893681 

noncomputable def Ns564p1637 := nat_lit 3538453841277016588160947867894899510467716413805997965460195785145867626552428280892978165205684350061681 

noncomputable def Ns564p1638 := nat_lit 272939561161793188520745746817504241270329014538092351379874796750233025854378130660323387096333700853848511843441 

noncomputable def Ns564p1639 := BSN.sin_dyadic_bound_f 624790563 536870912 4 3 536870912 268435456 Ns564p1636 Ns564p181 Ns564p1637 Ns564p1638 Ns564p184 Ns564p1637 493008221 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 624790563) qz375 0 3 Ns564p1636 Ns564p181 Ns564p1637 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 624790563) qz376 0 3 Ns564p1638 Ns564p184 Ns564p1637 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1640 := nat_lit 4982127059452514427617763091743492776362255092130401146474003512251040000 

noncomputable def Ns564p1641 := nat_lit 393222602439247181427547659337912945787421315082372952310192100000000 

noncomputable def Ns564p1642 := nat_lit 13047791366733588529276592067879743507607964654402822017890078411543200000 

noncomputable def Ns564p1643 := BSN.sin_dyadic_bound_f 375257870 536870912 3 2 536870912 268435456 Ns564p1640 Ns564p143 Ns564p1641 Ns564p1642 Ns564p146 Ns564p1641 345439538 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 375257870) qz375 0 2 Ns564p1640 Ns564p143 Ns564p1641 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 375257870) qz376 0 2 Ns564p1642 Ns564p146 Ns564p1641 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1644 := nat_lit 242229169047186974681151114055936 

noncomputable def Ns564p1645 := BSN.sin_dyadic_bound_f 124754612 536870912 2 1 536870912 268435456 Ns564p1644 Ns564p463 Ns564p1644 Ns564p1644 Ns564p464 Ns564p1644 123634900 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 124754612) qz375 0 1 Ns564p1644 Ns564p463 Ns564p1644 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 124754612) qz376 0 1 Ns564p1644 Ns564p464 Ns564p1644 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1646 := Ns564p1600 129886 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 393 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 345439538 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 255 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 123634900 536870912) qz226 rfl rfl (Ns564p1633 RS565to576.d9 RS565to576.d11 RS565to576.d13 RS565to576.d17 (Ns564p1635 rfl rfl) (Ns564p1639 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns564p1632 rfl) RS565to576.d19 RS565to576.d21 RS565to576.d23 RS565to576.d25 RS565to576.d17 (Ns564p1643 rfl rfl) (Ns564p1645 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns564p1647 := nat_lit 263000461610901556530800271360000 

noncomputable def Ns564p1648 := BSN.cos_dyadic_bound_f 127347120 536870912 2 1 536870912 268435456 Ns564p1647 Ns564p163 Ns564p1647 Ns564p1647 Ns564p164 Ns564p1647 521838068 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 127347120) qz373 0 1 Ns564p1647 Ns564p163 Ns564p1647 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 127347120) qz374 0 1 Ns564p1647 Ns564p164 Ns564p1647 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1649 := nat_lit 9873816843788932389600209817665671438145548557444959321676893176414039486403445456080340003338444334816691510081 

noncomputable def Ns564p1650 := nat_lit 367732807748084625905108124009013932873038960506834257181520068065284894987103332513059125638147390856001 

noncomputable def Ns564p1651 := nat_lit 59880665176268041187041921153625607854489807702495186801436239250930269023293336518076747826794802286248612617025 

noncomputable def Ns564p1652 := BSN.cos_dyadic_bound_f 517361807 536870912 4 3 536870912 268435456 Ns564p1649 Ns564p133 Ns564p1650 Ns564p1651 Ns564p136 Ns564p1650 306293826 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 517361807) qz373 0 3 Ns564p1649 Ns564p133 Ns564p1650 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 517361807) qz374 0 3 Ns564p1651 Ns564p136 Ns564p1650 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1653 := Ns564p1598 174798 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 142 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 521838068 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 306293826 536870912) qz226 rfl rfl (Ns564p1646 rfl rfl) (Ns564p1632 rfl) RS565to576.d27 RS565to576.d29 RS565to576.d31 RS565to576.d33 RS565to576.d17 (Ns564p1648 rfl rfl) (Ns564p1652 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1654 := nat_lit 222990980524274050558051047836176 

noncomputable def Ns564p1655 := BSN.cos_dyadic_bound_f 122200174 536870912 2 1 536870912 268435456 Ns564p1654 Ns564p163 Ns564p1654 Ns564p1654 Ns564p164 Ns564p1654 523023521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 122200174) qz373 0 1 Ns564p1654 Ns564p163 Ns564p1654 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 122200174) qz374 0 1 Ns564p1654 Ns564p164 Ns564p1654 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1656 := nat_lit 211187808944030071693814517800001 

noncomputable def Ns564p1657 := BSN.sin_dyadic_bound_f 120549999 536870912 2 1 536870912 268435456 Ns564p1656 Ns564p463 Ns564p1656 Ns564p1656 Ns564p464 Ns564p1656 119539546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 120549999) qz375 0 1 Ns564p1656 Ns564p463 Ns564p1656 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 120549999) qz376 0 1 Ns564p1656 Ns564p464 Ns564p1656 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1658 := Ns564p1596 214038 BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 523023521 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 119539546 536870912) qz226 rfl rfl (Ns564p1653 rfl) (Ns564p1632 rfl) RS565to576.d35 RS565to576.d37 RS565to576.d39 RS565to576.d41 RS565to576.d17 (Ns564p1655 rfl rfl) (Ns564p1657 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1659 := nat_lit 2693409503289205270361084073983007968627386753439429970739366284509670721 

noncomputable def Ns564p1660 := nat_lit 372312094758516166728453840217133888938029280662434330727058438712641 

noncomputable def Ns564p1661 := nat_lit 8079483885678098778749795314268589638104284201756965043556644736651586881 

noncomputable def Ns564p1662 := BSN.cos_dyadic_bound_f 372703433 536870912 3 2 536870912 268435456 Ns564p1659 Ns564p170 Ns564p1660 Ns564p1661 Ns564p173 Ns564p1660 412615711 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 372703433) qz373 0 2 Ns564p1659 Ns564p170 Ns564p1660 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 372703433) qz374 0 2 Ns564p1661 Ns564p173 Ns564p1660 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1663 := nat_lit 8737866167511662607548550848339400191332136485232357774366681042359685025 

noncomputable def Ns564p1664 := nat_lit 1209394477493713633543908978387158048502213646104436913289970890837921 

noncomputable def Ns564p1665 := nat_lit 22882929514328888435791895416828659388077068163038672701672171348547342241 

noncomputable def Ns564p1666 := BSN.sin_dyadic_bound_f 431838141 536870912 3 2 536870912 268435456 Ns564p1663 Ns564p143 Ns564p1664 Ns564p1665 Ns564p146 Ns564p1664 386755228 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 431838141) qz375 0 2 Ns564p1663 Ns564p143 Ns564p1664 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 431838141) qz376 0 2 Ns564p1665 Ns564p146 Ns564p1664 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1667 := Ns564p1594 249330 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 174 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 412615711 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 386755228 536870912) qz226 rfl rfl (Ns564p1658 rfl) (Ns564p1632 rfl) RS565to576.d43 RS565to576.d45 RS565to576.d47 RS565to576.d49 RS565to576.d17 (Ns564p1662 rfl rfl) (Ns564p1666 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1668 := nat_lit 4713699868921106625071026869078513651341385307568987350945362178216099840 

noncomputable def Ns564p1669 := nat_lit 351994940750296308937562374374410791275877484317065796761935193112576 

noncomputable def Ns564p1670 := nat_lit 12344834522032159728781076222789977183660610099134644003090714952634269696 

noncomputable def Ns564p1671 := BSN.sin_dyadic_bound_f 370098268 536870912 3 2 536870912 268435456 Ns564p1668 Ns564p143 Ns564p1669 Ns564p1670 Ns564p146 Ns564p1669 341473951 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 370098268) qz375 0 2 Ns564p1668 Ns564p143 Ns564p1669 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 370098268) qz376 0 2 Ns564p1670 Ns564p146 Ns564p1669 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1672 := Ns564p1592 Bool.false 55630513 249330 Bool.true 370098268 28296951008113761 1 Bool.false 341473951 Bool.false Bool.false 154205555 265824 BSN.abs_quadSignPos qz377 (BSN.sfrac_eq_quadSignPos_mul Bool.false 341473951 536870912) qz226 rfl (Ns564p1667 rfl) (Ns564p1632 rfl) RS565to576.d51 RS565to576.d53 RS565to576.d17 (Ns564p1671 rfl rfl) rfl 

noncomputable def Ns564p1673 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) 154205555 536870912 265824 536870912 154205555 536870912 265824 536870912 165576953896632320 154205555 268435456 8307 8388608 (Ns564p1672 rfl rfl rfl rfl) 

noncomputable def Ns564p1674 := @Enclosure.Real.IsNear.mulLit_ff qz714 (Zeta.RiemannSiegel.correction qz225) 19021193 67108864 1 67108864 436296065727375 1125899906842624 12939649247347 1407374883553280000 8298871671341085258375 75557863725914323419136 

noncomputable abbrev qz718 := (@HPow.hPow Real Real Real qz7 qz224 qz9)

noncomputable def Ns564p1675 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz718 1 1 0 1 19021193 67108864 1 67108864 19021193 67108864 1 67108864 

noncomputable def Ns564p1676 := @Enclosure.Real.IsNear.sqrt_image qz224 1299745915537 8388608000 121691 8388608000 417670836 417670876 33554432 (@Enclosure.Real.IsNear.of_eq qz224 (@HMul.hMul Real Real Real qz5 qz223 qz3) Bool.false 1299745915537 8388608000 121691 8388608000 (BSN.t_div_two_pi_mk qz223 973528 1000 qz226) (@Enclosure.Real.IsNear.mulLit_ff qz223 qz3 973528 1000 0 1 10680707 67108864 1 67108864 1299745915537 8388608000 121691 8388608000 (Enclosure.Real.IsNear.const Bool.false 973528 1000) RS565to576.d56 rfl)) 

noncomputable abbrev qz795 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 973528 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz719 := qz795

noncomputable abbrev qz533 := qz719

noncomputable abbrev qz232 := qz533

noncomputable def Ns564p1677 := @Enclosure.Real.IsNear.sqrt_image qz232 52208857 4194304 5 8388608 118383730 118383737 33554432 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 835341712 67108864 40 67108864 52208857 4194304 5 8388608 (Ns564p1676 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns564p1678 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz232) 236767467 67108864 7 67108864 9510596 9510597 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz232) Bool.false 236767467 67108864 7 67108864 236767467 67108864 7 67108864 (Ns564p1677 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns564p1679 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 19021193 67108864 1 67108864 19021193 67108864 1 67108864 (Ns564p1678 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz233 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz527))

noncomputable abbrev qz720 := (@HMul.hMul Real Real Real qz741 qz793 qz793)

noncomputable abbrev qz534 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz720 qz713) qz604)

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz534))

noncomputable def Ns564p1680 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz225) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz233) qz234) Bool.false 436296065727375 

noncomputable def Ns564p1681 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz233) qz234 70923825 67108864 289 

noncomputable abbrev qz721 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz233))

noncomputable def Ns564p1682 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz233) (@Neg.neg Real Real.instNeg qz721) Bool.true 70923825 67108864 289 67108864 (BSN.inv_eq_neg_inv_neg qz233) 

noncomputable def Ns564p1683 := @Enclosure.Real.IsNear.recentre' qz721 Bool.false 70923825 67108864 289 67108864 70923825 67108864 

noncomputable def Ns564p1684 := @Enclosure.Real.IsNear.recentre' qz233 Bool.true 63499108 67108864 661897216 171798691840000 15874777 16777216 40399 10485760000 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz355 qz352 qz527)

noncomputable def Ns564p1685 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2948713) (@Nat.cast Real Real.instNatCast 1048576)) Bool.false 2948713 1048576 63 16777216 Bool.true 63499108 67108864 1 

noncomputable def Ns564p1686 := nat_lit 134930377077470432326872291 

noncomputable def Ns564p1687 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz225 884279719003555 140737488355328 1 500000000000000 1877209 4194304 5 8388608 1659977847030944477995 590295810358705651712 Ns564p1686 

noncomputable def Ns564p1688 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz1 52208857 4194304 5 8388608 12 1 0 1 1877209 1877209 4194304 5 

noncomputable def Ns564p1689 := @Ns564p1688 8388608 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 835341712 67108864 40 67108864 52208857 4194304 5 8388608 (Ns564p1676 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns564p1690 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 1659977847030944477995 590295810358705651712 Ns564p1686 Ns564p201 2948713 1048576 63 16777216 (@Ns564p1687 Ns564p201 RS565to576.d55 (Ns564p1689 rfl rfl) rfl) 

noncomputable def Ns564p1691 := nat_lit 914808315602102363966405606154650064371585970212179989800018151188263395771006538696107293505 

noncomputable def Ns564p1692 := nat_lit 717688886255482566769482275950754241345927143122625108373213274373275753817510398735219521 

noncomputable def Ns564p1693 := nat_lit 2394764568380140171946768854339210852201498420895415723110300431620275971036931632129947794241 

noncomputable def Ns564p1694 := BSN.sin_dyadic_bound_f 170605107063 137438953472 3 2 67108864 20500001 Ns564p1691 Ns564p207 Ns564p1692 Ns564p1693 Ns564p210 Ns564p1692 63499108 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 170605107063) qz371 0 2 Ns564p1691 Ns564p207 Ns564p1692 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 170605107063) qz372 0 2 Ns564p1693 Ns564p210 Ns564p1692 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1695 := @Ns564p1685 10240000 (Ns564p1690 rfl) (Enclosure.sfrac_false_div 2948713 1048576) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2948713) (@Nat.cast Real Real.instNatCast 1048576)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 187582298974450043846656) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 63499108 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 2948713 1048576 226375608064910080 72057594037927936 0 187582298974450043846656 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 63499108 67108864 187582298974450043846656 151115727451828646838272 170605107063 137438953472 20500001 20480000 (Ns564p1694 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p1696 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz233) 15874777 16777216 40399 10485760000 35461768 35462057 33554432 (@Enclosure.Real.IsNear.neg qz233 Bool.true 15874777 16777216 40399 10485760000 (Ns564p1684 (Ns564p1695 rfl rfl) rfl)) 

noncomputable def Ns564p1697 := Ns564p1682 (@Enclosure.Real.IsNear.neg qz721 Bool.false 70923825 67108864 289 67108864 (@Ns564p1683 289 67108864 (Ns564p1696 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p1698 := @Enclosure.Real.IsNear.recentre' qz234 Bool.true 12303230 33554432 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz355 qz352 qz534)

noncomputable def Ns564p1699 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65304237)) qz383) Bool.true 65304237 33554432 

noncomputable def Ns564p1700 := nat_lit 4818602202717068934020568205 

noncomputable def Ns564p1701 := nat_lit 2145048787814391766494530284356123 

noncomputable def Ns564p1702 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true Ns564p1700 Ns564p1444 Ns564p1701 

noncomputable abbrev qz237 := qz534

noncomputable def Ns564p1703 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz237 884279719003555 140737488355328 1 500000000000000 5449183215631 

noncomputable abbrev qz535 := (@HSub.hSub Real Real Real qz592 qz720 qz713)

noncomputable abbrev qz238 := qz535

noncomputable def Ns564p1704 := @Enclosure.Real.IsNear.subLit_tf qz238 qz31 4349671587855 17592186044416 79487245 70368744177664 1 16 

noncomputable abbrev qz536 := qz720

noncomputable abbrev qz239 := qz536

noncomputable def Ns564p1705 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz225 3523913629681 17592186044416 37544205 70368744177664 1877209 4194304 5 8388608 

noncomputable def Ns564p1706 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 1877209 4194304 5 8388608 1877209 4194304 5 8388608 3523913629681 17592186044416 

noncomputable def Ns564p1707 := nat_lit 588285103724435564432727277722590589817660908752554649737737032783444018581642840577241315478253361 

noncomputable def Ns564p1708 := nat_lit 6015840532106299773844206961622892453109658248992951005444158286031841650279786314899191410481 

noncomputable def Ns564p1709 := nat_lit 3548752363705231843118762394587917390115983275539125170412485859846141878322069466677086059887767345 

noncomputable def Ns564p1710 := BSN.cos_dyadic_bound_t 65304237 33554432 4 3 33554432 10240000 Ns564p1707 Ns564p227 Ns564p1708 Ns564p1709 Ns564p230 Ns564p1708 12303230 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65304237) (BSN.cosEvenQ 33554432) 0 3 Ns564p1707 Ns564p227 Ns564p1708 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65304237) (BSN.cosOddQ 33554432) 0 3 Ns564p1709 Ns564p230 Ns564p1708 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1711 := @Ns564p1698 4951588864 687194767360000 6151615 16777216 302221 41943040000 (@Ns564p1699 477 67108864 Bool.true 12303230 33554432 1 10240000 (@Ns564p1702 Ns564p525 65304237 33554432 477 67108864 (@Ns564p1703 17592186044416 79487245 70368744177664 Ns564p1700 Ns564p1444 Ns564p1701 Ns564p525 RS565to576.d55 (@Ns564p1704 0 1 87186931450096 5449183215631 17592186044416 79487245 70368744177664 (@Ns564p1705 18243844939626577920 4349671587855 17592186044416 79487245 70368744177664 (@Ns564p1706 37544205 70368744177664 (Ns564p1689 rfl rfl) (Ns564p1689 rfl rfl) rfl) (Ns564p1689 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65304237 33554432) (BSN.cos_neg_of_bound 65304237 33554432 Bool.true 12303230 33554432 1 10240000 (Ns564p1710 rfl rfl)) rfl rfl) 

noncomputable def Ns564p1712 := @Ns564p1674 61668237176975122767 Ns564p1589 (Ns564p1675 qz33 (@Enclosure.Real.IsNear.of_eq qz718 (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 19021193 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz224 (BSN.t_div_two_pi_nonneg qz223 973528 1000 qz226)) Ns564p1679) rfl) (@Ns564p1680 1125899906842624 12939649247347 1407374883553280000 (BSN.correction_mk qz225 (BSN.cos_two_pi_p_ne_zero_mk qz223 973528 1000 12 qz226 rfl rfl (@BSN.floor_sqrt_eq_dec qz223 973528 1000 12 qz226 rfl rfl rfl))) (@Ns564p1681 67108864 6151615 16777216 302221 41943040000 436296065727375 1125899906842624 12939649247347 1407374883553280000 Ns564p1697 (Ns564p1711 rfl) rfl)) 

noncomputable def Ns564p1713 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (hardyZApproximantRS₀ qz223) Bool.false 35106133330937697635705 75557863725914323419136 23443794552531169042767 Ns564p1589 (@Eq.refl Real (hardyZApproximantRS₀ qz223)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (@HMul.hMul Real Real Real qz5 qz714 (Zeta.RiemannSiegel.correction qz225))) Bool.false 35106133330937697635705 75557863725914323419136 23443794552531169042767 Ns564p1589 (BSN.hardyZApproximantRS₀_eq qz223 12 (@BSN.floor_sqrt_eq_dec qz223 973528 1000 12 qz226 rfl rfl rfl)) (@Ns564p1591 35106133330937697635705 75557863725914323419136 23443794552531169042767 Ns564p1589 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12)) Bool.false 154205555 268435456 8307 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (Ns564p1673 (Ns564p1672 rfl rfl rfl rfl) rfl rfl)) (Ns564p1712 rfl) rfl rfl)) 

theorem RS565to576.d70 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz223) Bool.false 35106133330937697635705 75557863725914323419136 23443794552531169042767 Ns564p1589 := Ns564p1713 

noncomputable def Ns564p1714 := nat_lit 9444732965739290427392000 

noncomputable def Ns564p1715 := nat_lit 2439488822412954881595013070848 

noncomputable abbrev qz796 := (Enclosure.sfrac Bool.false 974151 1000)

noncomputable abbrev qz722 := qz796

noncomputable abbrev qz537 := qz722

noncomputable abbrev qz240 := qz537

noncomputable abbrev qz797 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 974151 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz723 := qz797

noncomputable abbrev qz538 := qz723

noncomputable abbrev qz241 := qz538

noncomputable abbrev qz798 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 974151 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz724 := qz798

noncomputable abbrev qz539 := qz724

noncomputable abbrev qz242 := qz539

noncomputable abbrev qz725 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz241 qz9))

noncomputable def Ns564p1716 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (@HMul.hMul Real Real Real qz5 qz725 (Zeta.RiemannSiegel.correction qz242)) 24930113 67108864 265995 268435456 8282404269088950312695 75557863725914323419136 24590249107132795589 Ns564p1714 Ns564p1715 

noncomputable def Ns564p1717 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin BSN.quadSignPos 11 12 974151 1000 287 536870912 268435456 9007199254740992 Bool.false 1057200449651 4533 1334074092 54 154981288 8 

noncomputable def Ns564p1718 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 974151 1000 174 233 536870912 268435456 9007199254740992 Bool.false 1057200449651 4533 

noncomputable def Ns564p1719 := Ns564p1718 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.false 56132090 214176 Bool.true 299421290 Bool.true 390434450 28296951008113761 1 Bool.false 455516894 Bool.true Bool.false 356917709 Bool.true Bool.true 195529740 

noncomputable def Ns564p1720 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 974151 1000 35 109 536870912 268435456 9007199254740992 Bool.false 1057200449651 4533 

noncomputable def Ns564p1721 := Ns564p1720 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 129453770 174910 Bool.true 817597937 Bool.true 12027857 28296951008113761 1 Bool.false 536255090 Bool.false Bool.false 12026850 Bool.true Bool.false 56132090 

noncomputable def Ns564p1722 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 974151 1000 142 46 536870912 268435456 9007199254740992 Bool.false 1057200449651 4533 

noncomputable def Ns564p1723 := Ns564p1722 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.false 89207157 129968 Bool.false 371485407 Bool.false 709941232 28296951008113761 1 Bool.false 413393919 Bool.true Bool.false 132005963 Bool.true Bool.true 129453770 

noncomputable def Ns564p1724 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 974151 1000 393 255 536870912 268435456 9007199254740992 Bool.false 1057200449651 4533 

noncomputable def Ns564p1725 := Ns564p1724 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 181668016 76749 Bool.false 755012310 Bool.false 429874101 28296951008113761 1 Bool.false 529625429 Bool.true Bool.false 385390440 Bool.false Bool.false 89207157 

noncomputable def Ns564p1726 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 974151 1000 823 572 536870912 268435456 9007199254740992 Bool.false 1057200449651 4533 

noncomputable def Ns564p1727 := Ns564p1726 372130544 53 379625064 8 589812976 53 309962568 8 Bool.true 446315512 4589 Bool.false 640981156 Bool.false 257451330 28296951008113761 1 Bool.false 499192720 Bool.false Bool.false 476315647 Bool.false Bool.false 181668016 

noncomputable def Ns564p1728 := nat_lit 30315536476664749269011591474552404706171461325131246907537 

noncomputable def Ns564p1729 := nat_lit 15394932646273224523269618380862106155994873367363584000 

noncomputable def Ns564p1730 := nat_lit 421088063394808951730612109960480000 

noncomputable def Ns564p1731 := nat_lit 2461220450848227527086226114998605314880 

noncomputable abbrev qz799 := (@Eq.refl Real (Enclosure.sfrac Bool.false 974151 1000))

noncomputable abbrev qz726 := qz799

noncomputable abbrev qz540 := qz726

noncomputable abbrev qz243 := qz540

noncomputable def Ns564p1732 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz240 974151 1000 3795881683204 16000000 1948302 4000 2000 Ns564p1730 Ns564p1731 qz243 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns564p1733 := nat_lit 87308745052794477894753383446710925553773808616377991093706560 

noncomputable abbrev qz727 := (@HSub.hSub Real Real Real qz745 qz746 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz747 (@Nat.cast Real Real.instNatCast 1948302))))

noncomputable abbrev qz541 := (@HSub.hSub Real Real Real qz592 (@HMul.hMul Real Real Real qz588 (Enclosure.sfrac Bool.false 974151 4000) (Real.log (Enclosure.sfrac Bool.false 3795881683204 16000000))) (@HMul.hMul Real Real Real qz588 qz593 qz727))

noncomputable abbrev qz728 := (Enclosure.sfrac Bool.false 974151 2000)

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz541 qz728) (@HMul.hMul Real Real Real qz355 qz728 (Real.log Real.pi)))

noncomputable def Ns564p1734 := @Enclosure.Real.IsNear.addLit_ft_p qz244 (Enclosure.sfrac Bool.true Ns564p1730 Ns564p1731) 35473763680272052278737 18014398509481984000 138293805578271057 16384000000000000000000 Ns564p1730 Ns564p1731 0 1 Ns564p1733 

noncomputable def Ns564p1735 := nat_lit 2380603982387516639374651424768000 

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz359 qz541 qz728)

noncomputable def Ns564p1736 := @Enclosure.Real.IsNear.subLit_ff_p qz245 (@HMul.hMul Real Real Real qz5 qz728 (Real.log Real.pi)) 45518049693192971507153 18014398509481984000 47956658041143 16000000000000000000 37417881238911 67108864000 2922453 536870912000 Ns564p1735 35473763680272052278737 18014398509481984000 

noncomputable def Ns564p1737 := nat_lit 18207219877277188602861200 

noncomputable abbrev qz246 := qz541

noncomputable def Ns564p1738 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz728 10858484370879632720989 3602879701896396800 47956658041143 16000000000000000000 974151 2000 0 1 Ns564p1737 45518049693192971507153 18014398509481984000 47956658041143 16000000000000000000 

noncomputable def Ns564p1739 := nat_lit 24451133083250934304808237937849270272 

noncomputable def Ns564p1740 := nat_lit 119701437445148545237647360 

noncomputable def Ns564p1741 := nat_lit 123482107482084049846393145377089992305257063202781244305651104858603000197165969709743097132627779262451848220879713786744641849145165908399317246672386823316543041652705473853810278400 

noncomputable def Ns564p1742 := nat_lit 3601558435803044545999049313256694756152121468316146496737051269533053132506250903079561708799916872797906170241400694940779937093291517388170152623292523922934304565921497931097047040 

noncomputable def Ns564p1743 := nat_lit 225168536213962669064475128740893040266684271054324460259175279165235339490694668579192342906708927532530865985337807547862417892747292155586147433885739991063224659074414018560 

noncomputable def Ns564p1744 := BSN.log_dyadic_bound 1698729683204 5893033683204 8 7 Ns564p1741 268435456 81920000 Ns564p1742 Ns564p1743 159272547 7591763366408 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1698729683204) (BSN.artanhQ 5893033683204) 0 7 Ns564p1742 Ns564p1741 Ns564p1743 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz542 := (Real.log (Enclosure.sfrac Bool.false 3795881683204 16000000))

noncomputable def Ns564p1745 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 974151 4000) qz542 974151 4000 0 1 55740325453294695 4503599627370496 48828193 4000000000000000 10859898756130496085789 3602879701896396800 47566033039143 16000000000000000000 (Enclosure.Real.IsNear.const Bool.false 974151 4000) (BSN.isNear_log_sfrac 3795881683204 16000000 55740325453294695 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3795881683204) qz362)) Bool.false Ns564p1740 Ns564p112 1000001392640000 81920000000000000000000 55740325453294695 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3795881683204 16000000 17 7591763366408 4194304000000 159272547 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns564p1744 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p1746 := BSN.arctan_dyadic_bound_f 1000 1948302 1 0 33554432 10240000 0 1 1 0 1 1 17222 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1948302) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1948302) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns564p1747 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1948302))) 884279719003555 562949953421312 1 2000000000000000 17222 33554432 1 10240000 29661808576186072170496 883990781789603 562949953421312 195312501 2000000000000000 qz17 (Ns564p1746 rfl) rfl rfl 

noncomputable abbrev qz543 := (@HMul.hMul Real Real Real qz588 qz593 qz727)

noncomputable abbrev qz247 := qz543

noncomputable abbrev qz544 := qz727

noncomputable abbrev qz248 := qz544

noncomputable def Ns564p1748 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 974151 4000) qz542) qz247 10859898756130496085789 3602879701896396800 47566033039143 16000000000000000000 883990781789603 2251799813685248 195312501 8000000000000000 Ns564p1739 10858484370879632720989 3602879701896396800 47956658041143 16000000000000000000 (Ns564p1745 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz248 1 4 0 1 883990781789603 562949953421312 195312501 2000000000000000 883990781789603 2251799813685248 195312501 8000000000000000 qz369 Ns564p1747 rfl) 

noncomputable def Ns564p1749 := @Ns564p1734 Ns564p1728 Ns564p1729 138293805578271057 16384000000000000000000 (@Ns564p1736 138293805578271057 16384000000000000000000 (Ns564p1738 (Ns564p1748 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 974151 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz728 (Real.log Real.pi) 974151 2000 0 1 38410761 33554432 3 268435456 37417881238911 67108864000 2922453 536870912000 (Enclosure.Real.IsNear.const Bool.false 974151 2000) RS565to576.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns564p1730 Ns564p1731) 

noncomputable def Ns564p1750 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns564p1728 Ns564p1729 138293805578271057 16384000000000000000000 66075028103 33554432 567 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz370 qz244 (Enclosure.sfrac Bool.true Ns564p1730 Ns564p1731)) Bool.false Ns564p1728 Ns564p1729 138293805578271057 16384000000000000000000 Ns564p1732 (Ns564p1749 rfl rfl)) 

noncomputable def Ns564p1751 := nat_lit 4746203248643125737947136 

noncomputable def Ns564p1752 := nat_lit 357388447002667415875384369020755343162584622036388197035524631066856032972818353056647840000 

noncomputable def Ns564p1753 := nat_lit 109640805868997409281962729756650725622093641249352841507696824090189512662510992100000000 

noncomputable def Ns564p1754 := nat_lit 935839847511769617201454931587134178536714429914232040016313953174191208098784954494487200000 

noncomputable def Ns564p1755 := BSN.sin_dyadic_bound_f 134895209630 137438953472 3 2 67108864 20500001 Ns564p1752 Ns564p207 Ns564p1753 Ns564p1754 Ns564p210 Ns564p1753 55789439 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 134895209630) qz371 0 2 Ns564p1752 Ns564p207 Ns564p1753 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 134895209630) qz372 0 2 Ns564p1754 Ns564p210 Ns564p1753 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1756 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz240) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66075028103) qz383) Bool.false 66075028103 33554432 567 67108864 Bool.true 55789439 67108864 1 10240000 (Ns564p1750 rfl) (Enclosure.sfrac_false_div 66075028103 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66075028103) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p1751) qz416) 226375608064910080 72057594037927936 Bool.false 55789439 67108864 313 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 66075028103 33554432 226375608064910080 72057594037927936 313 Ns564p1751 Ns564p435 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 55789439 67108864 Ns564p1751 Ns564p435 134895209630 137438953472 20500001 20480000 (Ns564p1755 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p1757 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns564p1728 Ns564p1729 138293805578271057 16384000000000000000000 1057200449651 536870912 4533 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz370 qz244 (Enclosure.sfrac Bool.true Ns564p1730 Ns564p1731)) Bool.false Ns564p1728 Ns564p1729 138293805578271057 16384000000000000000000 Ns564p1732 (Ns564p1749 rfl rfl)) 

noncomputable def Ns564p1758 := Ns564p1727 76749 BSN.abs_quadSignPos (BSN.cos_quad_nat3 823 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 499192720 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 572 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 476315647 536870912) qz243 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) Bool.true 55789439 67108864 358471 41943040000 446315512 536870912 4589 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 55789439 67108864 358471 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz240) qz240) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 55789439 67108864 5873188864 687194767360000 55789439 67108864 358471 41943040000 (Ns564p1756 rfl rfl) rfl)) rfl) (Ns564p1757 rfl) RS565to576.d7 

noncomputable def Ns564p1759 := nat_lit 60496585275921246325950265005476376872126659191126025139678001095693039772022553496791793536520723606854472564736 

noncomputable def Ns564p1760 := nat_lit 4809978601081122175716081329133613860090881687657197232822374449029352763893813461858891372886946150875136 

noncomputable def Ns564p1761 := nat_lit 302357348931724348873609782408811144246268341687094471437884943269105610055605823624856564567223198284342253060096 

noncomputable def Ns564p1762 := BSN.sin_dyadic_bound_f 640981156 536870912 4 3 536870912 268435456 Ns564p1759 Ns564p181 Ns564p1760 Ns564p1761 Ns564p184 Ns564p1760 499192720 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 640981156) qz375 0 3 Ns564p1759 Ns564p181 Ns564p1760 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 640981156) qz376 0 3 Ns564p1761 Ns564p184 Ns564p1760 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1763 := nat_lit 613172978180649381971278734056045165210408890167436307123708413360800000 

noncomputable def Ns564p1764 := nat_lit 19300169270235693011173551719109659691916598550978051323984100000000 

noncomputable def Ns564p1765 := nat_lit 1839480334203407674527813855064697276311842837305206965268477271882400000 

noncomputable def Ns564p1766 := BSN.cos_dyadic_bound_f 257451330 536870912 3 2 536870912 268435456 Ns564p1763 Ns564p170 Ns564p1764 Ns564p1765 Ns564p173 Ns564p1764 476315647 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 257451330) qz373 0 2 Ns564p1763 Ns564p170 Ns564p1764 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 257451330) qz374 0 2 Ns564p1765 Ns564p173 Ns564p1764 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1767 := nat_lit 116529452115110219876495522764768046254103668160120158028699392940105190680903385139349599031469761749424294400000 

noncomputable def Ns564p1768 := nat_lit 34312186280501853937543392622450008240556960099401605016928684515980579005098462023582791156161000000000000 

noncomputable def Ns564p1769 := nat_lit 582181842375176894822978820397090778277164703636679116427184886492603974172717912450520069805862779486417472000000 

noncomputable def Ns564p1770 := BSN.sin_dyadic_bound_f 755012310 536870912 4 3 536870912 268435456 Ns564p1767 Ns564p181 Ns564p1768 Ns564p1769 Ns564p184 Ns564p1768 529625429 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 755012310) qz375 0 3 Ns564p1767 Ns564p181 Ns564p1768 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 755012310) qz376 0 3 Ns564p1769 Ns564p184 Ns564p1768 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1771 := nat_lit 8579963380533485785825665760171845753240882008443960585682192625836327265 

noncomputable def Ns564p1772 := nat_lit 1166085096331994896635617365746025154360386825205151694345111437672801 

noncomputable def Ns564p1773 := nat_lit 22469444716003163352091714562810292932047631300588612240710136220577005921 

noncomputable def Ns564p1774 := BSN.sin_dyadic_bound_f 429874101 536870912 3 2 536870912 268435456 Ns564p1771 Ns564p143 Ns564p1772 Ns564p1773 Ns564p146 Ns564p1772 385390440 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 429874101) qz375 0 2 Ns564p1771 Ns564p143 Ns564p1772 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 429874101) qz376 0 2 Ns564p1773 Ns564p146 Ns564p1772 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1775 := Ns564p1725 129968 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 393 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 529625429 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 255 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 385390440 536870912) qz243 rfl rfl (Ns564p1758 RS565to576.d9 RS565to576.d11 RS565to576.d13 RS565to576.d17 (Ns564p1762 rfl rfl) (Ns564p1766 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns564p1757 rfl) RS565to576.d19 RS565to576.d21 RS565to576.d23 RS565to576.d25 RS565to576.d17 (Ns564p1770 rfl rfl) (Ns564p1774 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns564p1776 := nat_lit 2658367796677080405066222273261508009260117451045801513626955288981018881 

noncomputable def Ns564p1777 := nat_lit 362688733469696208082977651343477392542242091846338585275283603462401 

noncomputable def Ns564p1778 := nat_lit 7974378012564301822782500864481837072995267868953711863710315299736131841 

noncomputable def Ns564p1779 := BSN.cos_dyadic_bound_f 371485407 536870912 3 2 536870912 268435456 Ns564p1776 Ns564p170 Ns564p1777 Ns564p1778 Ns564p173 Ns564p1777 413393919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 371485407) qz373 0 2 Ns564p1776 Ns564p170 Ns564p1777 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 371485407) qz374 0 2 Ns564p1778 Ns564p173 Ns564p1777 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1780 := nat_lit 35056154161343388832785828606635486419617598084572187951658140052990747953993047476136898104296093462907905376256 

noncomputable def Ns564p1781 := nat_lit 16393391044849080246660362535260215041928543967265566284900694960947099208121838829838622851235710999986176 

noncomputable def Ns564p1782 := nat_lit 212416325879654475408781480602182177316003091724661277894573647593521824355594913180057787222426377806900363264000 

noncomputable def Ns564p1783 := BSN.cos_dyadic_bound_f 709941232 536870912 4 3 536870912 268435456 Ns564p1780 Ns564p133 Ns564p1781 Ns564p1782 Ns564p136 Ns564p1781 132005963 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 709941232) qz373 0 3 Ns564p1780 Ns564p133 Ns564p1781 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 709941232) qz374 0 3 Ns564p1782 Ns564p136 Ns564p1781 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1784 := Ns564p1723 174910 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 142 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 413393919 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132005963 536870912) qz243 rfl rfl (Ns564p1775 rfl rfl) (Ns564p1757 rfl) RS565to576.d27 RS565to576.d29 RS565to576.d31 RS565to576.d33 RS565to576.d17 (Ns564p1779 rfl rfl) (Ns564p1783 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1785 := nat_lit 160320566479625799752549457207639170186818773068084347955289862400526204323074621967690081554575145324576914319681 

noncomputable def Ns564p1786 := nat_lit 89223127749936824767566533792623361226895417846770123402053141015777116805352226655494519496383461473167681 

noncomputable def Ns564p1787 := nat_lit 800722640356099880555437596800730652196636798294316045395657882738189696295701754625684029801390375813188576389441 

noncomputable def Ns564p1788 := BSN.sin_dyadic_bound_f 817597937 536870912 4 3 536870912 268435456 Ns564p1785 Ns564p181 Ns564p1786 Ns564p1787 Ns564p184 Ns564p1786 536255090 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 817597937) qz375 0 3 Ns564p1785 Ns564p181 Ns564p1786 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 817597937) qz376 0 3 Ns564p1787 Ns564p184 Ns564p1786 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1789 := BSN.sin_dyadic_bound_f 12027857 536870912 1 0 536870912 268435456 0 1 1 0 1 1 12026850 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 12027857) qz375 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 12027857) qz376 0 0 rfl) rfl rfl 

noncomputable def Ns564p1790 := Ns564p1721 214176 BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536255090 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12026850 536870912) qz243 rfl rfl (Ns564p1784 rfl) (Ns564p1757 rfl) RS565to576.d35 RS565to576.d37 RS565to576.d39 RS565to576.d41 RS565to576.d17 (Ns564p1788 rfl rfl) (Ns564p1789 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1791 := nat_lit 1121875069521117190100322312190722523021040731041977386329193921328800000 

noncomputable def Ns564p1792 := nat_lit 64604298759671857558553999193734251522371330169801678516416100000000 

noncomputable def Ns564p1793 := nat_lit 3365495999965832226585849828573780100560077450465592555630548931786400000 

noncomputable def Ns564p1794 := BSN.cos_dyadic_bound_f 299421290 536870912 3 2 536870912 268435456 Ns564p1791 Ns564p170 Ns564p1792 Ns564p1793 Ns564p173 Ns564p1792 455516894 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 299421290) qz373 0 2 Ns564p1791 Ns564p170 Ns564p1792 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 299421290) qz374 0 2 Ns564p1793 Ns564p173 Ns564p1792 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1795 := nat_lit 5838401746970269458975910542972295070156563512895759222187325628900000000 

noncomputable def Ns564p1796 := nat_lit 539989164651204396683490940720194498712674238175288175039062500000000 

noncomputable def Ns564p1797 := nat_lit 15290177926274603775913706722451987725983560108817561782016741974500000000 

noncomputable def Ns564p1798 := BSN.sin_dyadic_bound_f 390434450 536870912 3 2 536870912 268435456 Ns564p1795 Ns564p143 Ns564p1796 Ns564p1797 Ns564p146 Ns564p1796 356917709 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 390434450) qz375 0 2 Ns564p1795 Ns564p143 Ns564p1796 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 390434450) qz376 0 2 Ns564p1797 Ns564p146 Ns564p1796 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1799 := Ns564p1719 249491 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 174 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 455516894 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 356917709 536870912) qz243 rfl rfl (Ns564p1790 rfl) (Ns564p1757 rfl) RS565to576.d43 RS565to576.d45 RS565to576.d47 RS565to576.d49 RS565to576.d17 (Ns564p1794 rfl rfl) (Ns564p1798 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns564p1800 := nat_lit 4117541144795525941278850897178079363684552209851157895158411705712640000 

noncomputable def Ns564p1801 := nat_lit 268594222112618077567460964592188453492329608806817311234457600000000 

noncomputable def Ns564p1802 := nat_lit 10783601464771528464557119317714201456915792015957821545006222488371200000 

noncomputable def Ns564p1803 := BSN.sin_dyadic_bound_f 357797320 536870912 3 2 536870912 268435456 Ns564p1800 Ns564p143 Ns564p1801 Ns564p1802 Ns564p146 Ns564p1801 331893101 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 357797320) qz375 0 2 Ns564p1800 Ns564p143 Ns564p1801 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 357797320) qz376 0 2 Ns564p1802 Ns564p146 Ns564p1801 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1804 := Ns564p1717 Bool.true 195529740 249491 Bool.true 357797320 28296951008113761 1 Bool.false 331893101 Bool.false Bool.true 99720452 265995 BSN.abs_quadSignPos qz377 (BSN.sfrac_eq_quadSignPos_mul Bool.false 331893101 536870912) qz243 rfl (Ns564p1799 rfl) (Ns564p1757 rfl) RS565to576.d51 RS565to576.d53 RS565to576.d17 (Ns564p1803 rfl rfl) rfl 

noncomputable def Ns564p1805 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) 99720452 536870912 265995 536870912 99720452 536870912 265995 536870912 107074020020584448 24930113 67108864 265995 268435456 (Ns564p1804 rfl rfl rfl rfl) 

noncomputable def Ns564p1806 := @Enclosure.Real.IsNear.mulLit_ff qz725 (Zeta.RiemannSiegel.correction qz242) 19018151 67108864 1 67108864 435499974160945 1125899906842624 1290125960207 140737488355328000 8282404269088950312695 75557863725914323419136 

noncomputable abbrev qz729 := (@HPow.hPow Real Real Real qz7 qz241 qz9)

noncomputable def Ns564p1807 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz729 1 1 0 1 19018151 67108864 1 67108864 19018151 67108864 1 67108864 

noncomputable def Ns564p1808 := @Enclosure.Real.IsNear.sqrt_image qz241 10404621404757 67108864000 974151 67108864000 417804457 417804497 33554432 (@Enclosure.Real.IsNear.of_eq qz241 (@HMul.hMul Real Real Real qz5 qz240 qz3) Bool.false 10404621404757 67108864000 974151 67108864000 (BSN.t_div_two_pi_mk qz240 974151 1000 qz243) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz3 974151 1000 0 1 10680707 67108864 1 67108864 10404621404757 67108864000 974151 67108864000 (Enclosure.Real.IsNear.const Bool.false 974151 1000) RS565to576.d56 rfl)) 

noncomputable abbrev qz800 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 974151 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz730 := qz800

noncomputable abbrev qz545 := qz730

noncomputable abbrev qz249 := qz545

noncomputable def Ns564p1809 := @Enclosure.Real.IsNear.sqrt_image qz249 417804477 33554432 5 8388608 118402665 118402672 33554432 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 835608954 67108864 40 67108864 417804477 33554432 5 8388608 (Ns564p1808 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns564p1810 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 236805337 67108864 7 67108864 9509075 9509076 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 236805337 67108864 7 67108864 236805337 67108864 7 67108864 (Ns564p1809 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns564p1811 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 19018151 67108864 1 67108864 19018151 67108864 1 67108864 (Ns564p1810 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz539))

noncomputable abbrev qz731 := (@HMul.hMul Real Real Real qz741 qz798 qz798)

noncomputable abbrev qz546 := (@HSub.hSub Real Real Real qz592 (@HSub.hSub Real Real Real qz592 qz731 qz724) qz604)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz546))

noncomputable def Ns564p1812 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz242) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 435499974160945 

noncomputable def Ns564p1813 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz250) qz251 70344055 67108864 285 

noncomputable abbrev qz732 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz250))

noncomputable def Ns564p1814 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz250) (@Neg.neg Real Real.instNeg qz732) Bool.true 70344055 67108864 285 67108864 (BSN.inv_eq_neg_inv_neg qz250) 

noncomputable def Ns564p1815 := @Enclosure.Real.IsNear.recentre' qz732 Bool.false 70344055 67108864 285 67108864 70344055 67108864 

noncomputable def Ns564p1816 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true 64022462 67108864 661897216 171798691840000 32011231 33554432 40399 10485760000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz355 qz352 qz539)

noncomputable def Ns564p1817 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 190396763) qz396) Bool.false 190396763 67108864 63 16777216 Bool.true 64022462 67108864 1 

noncomputable def Ns564p1818 := nat_lit 134930377077757381239401699 

noncomputable def Ns564p1819 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz242 884279719003555 140737488355328 1 500000000000000 15151293 33554432 5 8388608 13397981116580529846615 4722366482869645213696 Ns564p1818 

noncomputable def Ns564p1820 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 417804477 33554432 5 8388608 12 1 0 1 15151293 15151293 33554432 5 

noncomputable def Ns564p1821 := @Ns564p1820 8388608 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 835608954 67108864 40 67108864 417804477 33554432 5 8388608 (Ns564p1808 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns564p1822 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 13397981116580529846615 4722366482869645213696 Ns564p1818 Ns564p201 190396763 67108864 63 16777216 (@Ns564p1819 Ns564p201 RS565to576.d55 (Ns564p1821 rfl rfl) rfl) 

noncomputable def Ns564p1823 := nat_lit 12247255414233802752393216 

noncomputable def Ns564p1824 := nat_lit 990891728295034352407101252904938110391549556656837416999682567005167109425317211333749390145 

noncomputable def Ns564p1825 := nat_lit 841921880007965887768450634406154743028775352135827126587933886750017154302647634998868801 

noncomputable def Ns564p1826 := nat_lit 2593829510109838978200306742295323181441535583531116181556121496815937639768864600179345472321 

noncomputable def Ns564p1827 := BSN.sin_dyadic_bound_f 174043967351 137438953472 3 2 67108864 20500001 Ns564p1824 Ns564p207 Ns564p1825 Ns564p1826 Ns564p210 Ns564p1825 64022462 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 174043967351) qz371 0 2 Ns564p1824 Ns564p207 Ns564p1825 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 174043967351) qz372 0 2 Ns564p1826 Ns564p210 Ns564p1825 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1828 := @Ns564p1817 10240000 (Ns564p1822 rfl) (Enclosure.sfrac_false_div 190396763 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 190396763) qz396) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns564p1823) qz397) 226375608064910080 72057594037927936 Bool.false 64022462 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 190396763 67108864 226375608064910080 72057594037927936 0 Ns564p1823 Ns564p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 64022462 67108864 Ns564p1823 Ns564p112 174043967351 137438953472 20500001 20480000 (Ns564p1827 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns564p1829 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz250) 32011231 33554432 40399 10485760000 35171885 35172170 33554432 (@Enclosure.Real.IsNear.neg qz250 Bool.true 32011231 33554432 40399 10485760000 (Ns564p1816 (Ns564p1828 rfl rfl) rfl)) 

noncomputable def Ns564p1830 := Ns564p1814 (@Enclosure.Real.IsNear.neg qz732 Bool.false 70344055 67108864 285 67108864 (@Ns564p1815 285 67108864 (Ns564p1829 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns564p1831 := @Enclosure.Real.IsNear.recentre' qz251 Bool.true 12381998 33554432 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz355 qz352 qz546)

noncomputable def Ns564p1832 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 130777889)) qz396) Bool.true 130777889 67108864 

noncomputable def Ns564p1833 := nat_lit 308790562135864464342872120005 

noncomputable def Ns564p1834 := nat_lit 4308127107540428633014913330066549 

noncomputable def Ns564p1835 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns564p1833 Ns564p218 Ns564p1834 

noncomputable abbrev qz254 := qz546

noncomputable def Ns564p1836 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 349200095286391 

noncomputable abbrev qz547 := (@HSub.hSub Real Real Real qz592 qz731 qz724)

noncomputable abbrev qz255 := qz547

noncomputable def Ns564p1837 := @Enclosure.Real.IsNear.subLit_tf qz255 qz31 278831351108727 1125899906842624 159642595 140737488355328 1 16 

noncomputable abbrev qz548 := qz731

noncomputable abbrev qz256 := qz548

noncomputable def Ns564p1838 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz242 229561679571849 1125899906842624 75756515 140737488355328 15151293 33554432 5 8388608 

noncomputable def Ns564p1839 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 15151293 33554432 5 8388608 15151293 33554432 5 8388608 229561679571849 1125899906842624 

noncomputable def Ns564p1840 := nat_lit 2422249264189418915820736952501831582916366123261850202934467604804784877781302128189153827347421244801 

noncomputable def Ns564p1841 := nat_lit 25027177460753420627114020589622057190208678445469205298411049093939744762595103482944334119873921 

noncomputable def Ns564p1842 := nat_lit 14611470614522529089525669903401330993009507343322369849769689830130433609816425493288555859345053363585 

noncomputable def Ns564p1843 := BSN.cos_dyadic_bound_t 130777889 67108864 4 3 33554432 10240000 Ns564p1840 Ns564p665 Ns564p1841 Ns564p1842 Ns564p668 Ns564p1841 12381998 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 130777889) (BSN.cosEvenQ 67108864) 0 3 Ns564p1840 Ns564p665 Ns564p1841 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 130777889) (BSN.cosOddQ 67108864) 0 3 Ns564p1842 Ns564p668 Ns564p1841 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns564p1844 := @Ns564p1831 155697152 21474836480000 6190999 16777216 9503 1310720000 (@Ns564p1832 15 2097152 Bool.true 12381998 33554432 1 10240000 (@Ns564p1835 Ns564p659 130777889 67108864 15 2097152 (@Ns564p1836 1125899906842624 159642595 140737488355328 Ns564p1833 Ns564p218 Ns564p1834 Ns564p659 RS565to576.d55 (@Ns564p1837 0 1 5587201524582256 349200095286391 1125899906842624 159642595 140737488355328 (@Ns564p1838 9356027610245904728064 278831351108727 1125899906842624 159642595 140737488355328 (@Ns564p1839 75756515 140737488355328 (Ns564p1821 rfl rfl) (Ns564p1821 rfl rfl) rfl) (Ns564p1821 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 130777889 67108864) (BSN.cos_neg_of_bound 130777889 67108864 Bool.true 12381998 33554432 1 10240000 (Ns564p1843 rfl rfl)) rfl rfl) 

noncomputable def Ns564p1845 := @Ns564p1806 24590249107132795589 Ns564p1714 (Ns564p1807 qz33 (@Enclosure.Real.IsNear.of_eq qz729 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 19018151 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz241 (BSN.t_div_two_pi_nonneg qz240 974151 1000 qz243)) Ns564p1811) rfl) (@Ns564p1812 1125899906842624 1290125960207 140737488355328000 (BSN.correction_mk qz242 (BSN.cos_two_pi_p_ne_zero_mk qz240 974151 1000 12 qz243 rfl rfl (@BSN.floor_sqrt_eq_dec qz240 974151 1000 12 qz243 rfl rfl rfl))) (@Ns564p1813 67108864 6190999 16777216 9503 1310720000 435499974160945 1125899906842624 1290125960207 140737488355328000 Ns564p1830 (Ns564p1844 rfl) rfl)) 

noncomputable def Ns564p1846 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (hardyZApproximantRS₀ qz240) Bool.true 36351216173365039849207 75557863725914323419136 9383457302876000635589 Ns564p1714 (@Eq.refl Real (hardyZApproximantRS₀ qz240)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (@HMul.hMul Real Real Real qz5 qz725 (Zeta.RiemannSiegel.correction qz242))) Bool.true 36351216173365039849207 75557863725914323419136 9383457302876000635589 Ns564p1714 (BSN.hardyZApproximantRS₀_eq qz240 12 (@BSN.floor_sqrt_eq_dec qz240 974151 1000 12 qz243 rfl rfl rfl)) (@Ns564p1716 36351216173365039849207 75557863725914323419136 9383457302876000635589 Ns564p1714 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12)) Bool.true 24930113 67108864 265995 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (Ns564p1805 (Ns564p1804 rfl rfl rfl rfl) rfl rfl)) (Ns564p1845 rfl) rfl rfl)) 

theorem RS565to576.d71 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz240) Bool.true 36351216173365039849207 75557863725914323419136 9383457302876000635589 Ns564p1714 := Ns564p1846 

noncomputable def RS565to576.d72 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz549 := (RS565to576.d3 qz587 qz606 (@Enclosure.dec_le_dec qz587 qz606 959413 1000 960663 1000 (@Eq.refl Real qz587) qz610 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz549)

noncomputable def Ns564p1847 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 2626190217423252840919 9444732965739290427392 5782760412465224775607 Ns564p85 

noncomputable abbrev qz550 := (@Enclosure.dec_le_dec qz587 qz606 959413 1000 960663 1000 (@Eq.refl Real qz587) qz610 rfl rfl rfl)

noncomputable abbrev qz258 := qz550

noncomputable def Ns564p1848 := @Enclosure.Real.IsNear.neg_val qz257 2626190217423252840919 9444732965739290427392 5782760412465224775607 Ns564p85 (Ns564p1847 (RS565to576.d4 qz4 qz35 qz258) RS565to576.d57) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz549)

noncomputable def Ns564p1849 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz35) Bool.false 617268659107640507351301 75557863725914323419136 46310669198825874469591 Ns564p235 

noncomputable def Ns564p1850 := @Enclosure.Real.IsNear.pos_val qz259 617268659107640507351301 75557863725914323419136 46310669198825874469591 Ns564p235 (Ns564p1849 (RS565to576.d58 qz4 qz35 qz258) RS565to576.d59) rfl 

noncomputable def Ns564p1851 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 959413 1000 959413 1000 

noncomputable def Ns564p1852 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2626190217423252840919 9444732965739290427392 5782760412465224775607 

noncomputable def Ns564p1853 := @Ns564p1852 Ns564p85 446371901 10737418240 1213 10737418240 (Ns564p1847 (RS565to576.d4 qz4 qz35 qz258) RS565to576.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable def Ns564p1854 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz35 959413 1000 960663 1000 

noncomputable def Ns564p1855 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 617268659107640507351301 75557863725914323419136 46310669198825874469591 

noncomputable def Ns564p1856 := @Ns564p1855 Ns564p235 446371901 10737418240 1213 10737418240 (Ns564p1849 (RS565to576.d58 qz4 qz35 qz258) RS565to576.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz549

noncomputable def Ns564p1857 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 959413 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns564p1848 rfl rfl) (Ns564p1850 rfl rfl)) (Ns564p1851 qz11 qz11 rfl rfl rfl rfl (Ns564p1853 rfl)) (Ns564p1854 qz11 qz38 rfl rfl rfl rfl (Ns564p1856 rfl)) 

noncomputable abbrev qz551 := (RS565to576.d3 qz606 qz618 (@Enclosure.dec_le_dec qz606 qz618 960663 1000 962536 1000 qz610 qz622 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns564p1858 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz35) Bool.false 617268659107640507351301 75557863725914323419136 46310669198825874469591 Ns564p235 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz606 qz618 960663 1000 962536 1000 qz610 qz622 rfl rfl rfl)

noncomputable abbrev qz262 := qz552

noncomputable def Ns564p1859 := @Enclosure.Real.IsNear.pos_val qz261 617268659107640507351301 75557863725914323419136 46310669198825874469591 Ns564p235 (Ns564p1858 (RS565to576.d4 qz35 qz62 qz262) RS565to576.d59) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns564p1860 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz62) Bool.true 41989003351974195146529 18889465931478580854784 231965605172202339069 236118324143482260684800 

noncomputable def Ns564p1861 := @Enclosure.Real.IsNear.neg_val qz263 41989003351974195146529 18889465931478580854784 231965605172202339069 236118324143482260684800 (Ns564p1860 (RS565to576.d58 qz35 qz62 qz262) RS565to576.d61) rfl 

noncomputable def Ns564p1862 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz35 959413 1000 960663 1000 

noncomputable def Ns564p1863 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 617268659107640507351301 75557863725914323419136 46310669198825874469591 

noncomputable def Ns564p1864 := @Ns564p1863 Ns564p235 446371901 10737418240 1213 10737418240 (Ns564p1858 (RS565to576.d4 qz35 qz62 qz262) RS565to576.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable def Ns564p1865 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz62 959413 1000 962536 1000 

noncomputable def Ns564p1866 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 41989003351974195146529 18889465931478580854784 231965605172202339069 

noncomputable def Ns564p1867 := @Ns564p1866 236118324143482260684800 446371901 10737418240 1213 10737418240 (Ns564p1860 (RS565to576.d58 qz35 qz62 qz262) RS565to576.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz551

noncomputable def Ns564p1868 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz35 960663 1000 qz38 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns564p1859 rfl rfl) (Ns564p1861 rfl rfl)) (Ns564p1862 qz11 qz38 rfl rfl rfl rfl (Ns564p1864 rfl)) (Ns564p1865 qz11 qz65 rfl rfl rfl rfl (Ns564p1867 rfl)) 

noncomputable abbrev qz553 := (RS565to576.d3 qz618 qz630 (@Enclosure.dec_le_dec qz618 qz630 962536 1000 963395 1000 qz622 qz634 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns564p1869 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz62) Bool.true 41989003351974195146529 18889465931478580854784 231965605172202339069 236118324143482260684800 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz618 qz630 962536 1000 963395 1000 qz622 qz634 rfl rfl rfl)

noncomputable abbrev qz266 := qz554

noncomputable def Ns564p1870 := @Enclosure.Real.IsNear.neg_val qz265 41989003351974195146529 18889465931478580854784 231965605172202339069 236118324143482260684800 (Ns564p1869 (RS565to576.d4 qz62 qz80 qz266) RS565to576.d61) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns564p1871 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz80) Bool.false 24916926543106959545709 151115727451828646838272 92858666110287566815941 Ns564p539 

noncomputable def Ns564p1872 := @Enclosure.Real.IsNear.pos_val qz267 24916926543106959545709 151115727451828646838272 92858666110287566815941 Ns564p539 (Ns564p1871 (RS565to576.d58 qz62 qz80 qz266) RS565to576.d62) rfl 

noncomputable def Ns564p1873 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz62 959413 1000 962536 1000 

noncomputable def Ns564p1874 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 41989003351974195146529 18889465931478580854784 231965605172202339069 

noncomputable def Ns564p1875 := @Ns564p1874 236118324143482260684800 446371901 10737418240 1213 10737418240 (Ns564p1869 (RS565to576.d4 qz62 qz80 qz266) RS565to576.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable def Ns564p1876 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz80 959413 1000 963395 1000 

noncomputable def Ns564p1877 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 24916926543106959545709 151115727451828646838272 92858666110287566815941 

noncomputable def Ns564p1878 := @Ns564p1877 Ns564p539 446371901 10737418240 1213 10737418240 (Ns564p1871 (RS565to576.d58 qz62 qz80 qz266) RS565to576.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz553

noncomputable def Ns564p1879 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz62 962536 1000 qz65 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns564p1870 rfl rfl) (Ns564p1872 rfl rfl)) (Ns564p1873 qz11 qz65 rfl rfl rfl rfl (Ns564p1875 rfl)) (Ns564p1876 qz11 qz83 rfl rfl rfl rfl (Ns564p1878 rfl)) 

noncomputable abbrev qz555 := (RS565to576.d3 qz630 qz640 (@Enclosure.dec_le_dec qz630 qz640 963395 1000 964019 1000 qz634 qz644 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns564p1880 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz80) Bool.false 24916926543106959545709 151115727451828646838272 92858666110287566815941 Ns564p539 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz630 qz640 963395 1000 964019 1000 qz634 qz644 rfl rfl rfl)

noncomputable abbrev qz270 := qz556

noncomputable def Ns564p1881 := @Enclosure.Real.IsNear.pos_val qz269 24916926543106959545709 151115727451828646838272 92858666110287566815941 Ns564p539 (Ns564p1880 (RS565to576.d4 qz80 qz98 qz270) RS565to576.d62) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns564p1882 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz98) Bool.true 20807425878902920277389 18889465931478580854784 11614054648035921106963 Ns564p673 

noncomputable def Ns564p1883 := @Enclosure.Real.IsNear.neg_val qz271 20807425878902920277389 18889465931478580854784 11614054648035921106963 Ns564p673 (Ns564p1882 (RS565to576.d58 qz80 qz98 qz270) RS565to576.d63) rfl 

noncomputable def Ns564p1884 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz80 959413 1000 963395 1000 

noncomputable def Ns564p1885 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 24916926543106959545709 151115727451828646838272 92858666110287566815941 

noncomputable def Ns564p1886 := @Ns564p1885 Ns564p539 446371901 10737418240 1213 10737418240 (Ns564p1880 (RS565to576.d4 qz80 qz98 qz270) RS565to576.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable def Ns564p1887 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz98 959413 1000 964019 1000 

noncomputable def Ns564p1888 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 20807425878902920277389 18889465931478580854784 11614054648035921106963 

noncomputable def Ns564p1889 := @Ns564p1888 Ns564p673 446371901 10737418240 1213 10737418240 (Ns564p1882 (RS565to576.d58 qz80 qz98 qz270) RS565to576.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz555

noncomputable def Ns564p1890 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz80 963395 1000 qz83 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns564p1881 rfl rfl) (Ns564p1883 rfl rfl)) (Ns564p1884 qz11 qz83 rfl rfl rfl rfl (Ns564p1886 rfl)) (Ns564p1887 qz11 qz101 rfl rfl rfl rfl (Ns564p1889 rfl)) 

noncomputable abbrev qz557 := (RS565to576.d3 qz640 qz650 (@Enclosure.dec_le_dec qz640 qz650 964019 1000 965657 1000 qz644 qz654 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns564p1891 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz98) Bool.true 20807425878902920277389 18889465931478580854784 11614054648035921106963 Ns564p673 

noncomputable abbrev qz558 := (@Enclosure.dec_le_dec qz640 qz650 964019 1000 965657 1000 qz644 qz654 rfl rfl rfl)

noncomputable abbrev qz274 := qz558

noncomputable def Ns564p1892 := @Enclosure.Real.IsNear.neg_val qz273 20807425878902920277389 18889465931478580854784 11614054648035921106963 Ns564p673 (Ns564p1891 (RS565to576.d4 qz98 qz116 qz274) RS565to576.d63) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns564p1893 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz116) Bool.false 174547576089430841864291 151115727451828646838272 93057502150610495569091 Ns564p539 

noncomputable def Ns564p1894 := @Enclosure.Real.IsNear.pos_val qz275 174547576089430841864291 151115727451828646838272 93057502150610495569091 Ns564p539 (Ns564p1893 (RS565to576.d58 qz98 qz116 qz274) RS565to576.d64) rfl 

noncomputable def Ns564p1895 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz98 959413 1000 964019 1000 

noncomputable def Ns564p1896 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 20807425878902920277389 18889465931478580854784 11614054648035921106963 

noncomputable def Ns564p1897 := @Ns564p1896 Ns564p673 446371901 10737418240 1213 10737418240 (Ns564p1891 (RS565to576.d4 qz98 qz116 qz274) RS565to576.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable def Ns564p1898 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz116 959413 1000 965657 1000 

noncomputable def Ns564p1899 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 174547576089430841864291 151115727451828646838272 93057502150610495569091 

noncomputable def Ns564p1900 := @Ns564p1899 Ns564p539 446371901 10737418240 1213 10737418240 (Ns564p1893 (RS565to576.d58 qz98 qz116 qz274) RS565to576.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz557

noncomputable def Ns564p1901 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz98 964019 1000 qz101 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns564p1892 rfl rfl) (Ns564p1894 rfl rfl)) (Ns564p1895 qz11 qz101 rfl rfl rfl rfl (Ns564p1897 rfl)) (Ns564p1898 qz11 qz119 rfl rfl rfl rfl (Ns564p1900 rfl)) 

noncomputable abbrev qz559 := (RS565to576.d3 qz650 qz660 (@Enclosure.dec_le_dec qz650 qz660 965657 1000 966905 1000 qz654 qz664 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns564p1902 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz116) Bool.false 174547576089430841864291 151115727451828646838272 93057502150610495569091 Ns564p539 

noncomputable abbrev qz560 := (@Enclosure.dec_le_dec qz650 qz660 965657 1000 966905 1000 qz654 qz664 rfl rfl rfl)

noncomputable abbrev qz278 := qz560

noncomputable def Ns564p1903 := @Enclosure.Real.IsNear.pos_val qz277 174547576089430841864291 151115727451828646838272 93057502150610495569091 Ns564p539 (Ns564p1902 (RS565to576.d4 qz116 qz134 qz278) RS565to576.d64) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns564p1904 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz134) Bool.true 129220237587835819045017 75557863725914323419136 46583743073819237506363 Ns564p235 

noncomputable def Ns564p1905 := @Enclosure.Real.IsNear.neg_val qz279 129220237587835819045017 75557863725914323419136 46583743073819237506363 Ns564p235 (Ns564p1904 (RS565to576.d58 qz116 qz134 qz278) RS565to576.d65) rfl 

noncomputable def Ns564p1906 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz116 959413 1000 965657 1000 

noncomputable def Ns564p1907 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 174547576089430841864291 151115727451828646838272 93057502150610495569091 

noncomputable def Ns564p1908 := @Ns564p1907 Ns564p539 446371901 10737418240 1213 10737418240 (Ns564p1902 (RS565to576.d4 qz116 qz134 qz278) RS565to576.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable def Ns564p1909 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz134 959413 1000 966905 1000 

noncomputable def Ns564p1910 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 129220237587835819045017 75557863725914323419136 46583743073819237506363 

noncomputable def Ns564p1911 := @Ns564p1910 Ns564p235 446371901 10737418240 1213 10737418240 (Ns564p1904 (RS565to576.d58 qz116 qz134 qz278) RS565to576.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz559

noncomputable def Ns564p1912 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz116 965657 1000 qz119 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns564p1903 rfl rfl) (Ns564p1905 rfl rfl)) (Ns564p1906 qz11 qz119 rfl rfl rfl rfl (Ns564p1908 rfl)) (Ns564p1909 qz11 qz137 rfl rfl rfl rfl (Ns564p1911 rfl)) 

noncomputable abbrev qz561 := (RS565to576.d3 qz660 qz670 (@Enclosure.dec_le_dec qz660 qz670 966905 1000 968152 1000 qz664 qz674 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns564p1913 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz134) Bool.true 129220237587835819045017 75557863725914323419136 46583743073819237506363 Ns564p235 

noncomputable abbrev qz562 := (@Enclosure.dec_le_dec qz660 qz670 966905 1000 968152 1000 qz664 qz674 rfl rfl rfl)

noncomputable abbrev qz282 := qz562

noncomputable def Ns564p1914 := @Enclosure.Real.IsNear.neg_val qz281 129220237587835819045017 75557863725914323419136 46583743073819237506363 Ns564p235 (Ns564p1913 (RS565to576.d4 qz134 qz152 qz282) RS565to576.d65) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns564p1915 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz152) Bool.false 10208052352768296560197 4722366482869645213696 91093739486467995203 92233720368547758080000 

noncomputable def Ns564p1916 := @Enclosure.Real.IsNear.pos_val qz283 10208052352768296560197 4722366482869645213696 91093739486467995203 92233720368547758080000 (Ns564p1915 (RS565to576.d58 qz134 qz152 qz282) RS565to576.d66) rfl 

noncomputable def Ns564p1917 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz134 959413 1000 966905 1000 

noncomputable def Ns564p1918 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 129220237587835819045017 75557863725914323419136 46583743073819237506363 

noncomputable def Ns564p1919 := @Ns564p1918 Ns564p235 446371901 10737418240 1213 10737418240 (Ns564p1913 (RS565to576.d4 qz134 qz152 qz282) RS565to576.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable def Ns564p1920 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz152 959413 1000 968152 1000 

noncomputable def Ns564p1921 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 10208052352768296560197 4722366482869645213696 91093739486467995203 

noncomputable def Ns564p1922 := @Ns564p1921 92233720368547758080000 446371901 10737418240 1213 10737418240 (Ns564p1915 (RS565to576.d58 qz134 qz152 qz282) RS565to576.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz561

noncomputable def Ns564p1923 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz134 966905 1000 qz137 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns564p1914 rfl rfl) (Ns564p1916 rfl rfl)) (Ns564p1917 qz11 qz137 rfl rfl rfl rfl (Ns564p1919 rfl)) (Ns564p1920 qz11 qz155 rfl rfl rfl rfl (Ns564p1922 rfl)) 

noncomputable abbrev qz563 := (RS565to576.d3 qz670 qz680 (@Enclosure.dec_le_dec qz670 qz680 968152 1000 969399 1000 qz674 qz684 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns564p1924 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz152) Bool.false 10208052352768296560197 4722366482869645213696 91093739486467995203 92233720368547758080000 

noncomputable abbrev qz564 := (@Enclosure.dec_le_dec qz670 qz680 968152 1000 969399 1000 qz674 qz684 rfl rfl rfl)

noncomputable abbrev qz286 := qz564

noncomputable def Ns564p1925 := @Enclosure.Real.IsNear.pos_val qz285 10208052352768296560197 4722366482869645213696 91093739486467995203 92233720368547758080000 (Ns564p1924 (RS565to576.d4 qz152 qz170 qz286) RS565to576.d66) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns564p1926 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz170) Bool.true 480407083131468574639661 151115727451828646838272 747164958888777249967 755578637259143234191360 

noncomputable def Ns564p1927 := @Enclosure.Real.IsNear.neg_val qz287 480407083131468574639661 151115727451828646838272 747164958888777249967 755578637259143234191360 (Ns564p1926 (RS565to576.d58 qz152 qz170 qz286) RS565to576.d67) rfl 

noncomputable def Ns564p1928 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz152 959413 1000 968152 1000 

noncomputable def Ns564p1929 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 10208052352768296560197 4722366482869645213696 91093739486467995203 

noncomputable def Ns564p1930 := @Ns564p1929 92233720368547758080000 446371901 10737418240 1213 10737418240 (Ns564p1924 (RS565to576.d4 qz152 qz170 qz286) RS565to576.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable def Ns564p1931 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz170 959413 1000 969399 1000 

noncomputable def Ns564p1932 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 480407083131468574639661 151115727451828646838272 747164958888777249967 

noncomputable def Ns564p1933 := @Ns564p1932 755578637259143234191360 446371901 10737418240 1213 10737418240 (Ns564p1926 (RS565to576.d58 qz152 qz170 qz286) RS565to576.d67) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz563

noncomputable def Ns564p1934 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz152 968152 1000 qz155 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns564p1925 rfl rfl) (Ns564p1927 rfl rfl)) (Ns564p1928 qz11 qz155 rfl rfl rfl rfl (Ns564p1930 rfl)) (Ns564p1931 qz11 qz173 rfl rfl rfl rfl (Ns564p1933 rfl)) 

noncomputable abbrev qz733 := (@Enclosure.dec_le_dec qz778 qz782 969399 1000 970646 1000 (@Eq.refl Real qz778) (@Eq.refl Real qz782) rfl rfl rfl)

noncomputable abbrev qz565 := (RS565to576.d3 qz680 qz690 qz733)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz565)

noncomputable def Ns564p1935 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz170) Bool.true 480407083131468574639661 151115727451828646838272 747164958888777249967 755578637259143234191360 

noncomputable abbrev qz566 := qz733

noncomputable abbrev qz290 := qz566

noncomputable def Ns564p1936 := @Enclosure.Real.IsNear.neg_val qz289 480407083131468574639661 151115727451828646838272 747164958888777249967 755578637259143234191360 (Ns564p1935 (RS565to576.d4 qz170 qz188 qz290) RS565to576.d67) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz565)

noncomputable def Ns564p1937 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz188) Bool.false 958281230415081343687 590295810358705651712 5844424010051473510661 Ns564p85 

noncomputable def Ns564p1938 := @Enclosure.Real.IsNear.pos_val qz291 958281230415081343687 590295810358705651712 5844424010051473510661 Ns564p85 (Ns564p1937 (RS565to576.d58 qz170 qz188 qz290) RS565to576.d68) rfl 

noncomputable def Ns564p1939 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz170 959413 1000 969399 1000 

noncomputable def Ns564p1940 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 480407083131468574639661 151115727451828646838272 747164958888777249967 

noncomputable def Ns564p1941 := @Ns564p1940 755578637259143234191360 446371901 10737418240 1213 10737418240 (Ns564p1935 (RS565to576.d4 qz170 qz188 qz290) RS565to576.d67) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable def Ns564p1942 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz188 959413 1000 970646 1000 

noncomputable def Ns564p1943 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 958281230415081343687 590295810358705651712 5844424010051473510661 

noncomputable def Ns564p1944 := @Ns564p1943 Ns564p85 446371901 10737418240 1213 10737418240 (Ns564p1937 (RS565to576.d58 qz170 qz188 qz290) RS565to576.d68) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz565

noncomputable def Ns564p1945 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz170 969399 1000 qz173 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns564p1936 rfl rfl) (Ns564p1938 rfl rfl)) (Ns564p1939 qz11 qz173 rfl rfl rfl rfl (Ns564p1941 rfl)) (Ns564p1942 qz11 qz191 rfl rfl rfl rfl (Ns564p1944 rfl)) 

noncomputable abbrev qz734 := (@Enclosure.dec_le_dec qz782 qz786 970646 1000 972516 1000 (@Eq.refl Real qz782) qz789 rfl rfl rfl)

noncomputable abbrev qz567 := (RS565to576.d3 qz690 qz700 qz734)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz567)

noncomputable def Ns564p1946 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz188) Bool.false 958281230415081343687 590295810358705651712 5844424010051473510661 Ns564p85 

noncomputable abbrev qz568 := qz734

noncomputable abbrev qz294 := qz568

noncomputable def Ns564p1947 := @Enclosure.Real.IsNear.pos_val qz293 958281230415081343687 590295810358705651712 5844424010051473510661 Ns564p85 (Ns564p1946 (RS565to576.d4 qz188 qz206 qz294) RS565to576.d68) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz567)

noncomputable def Ns564p1948 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz206) Bool.true 274882575854225374744329 75557863725914323419136 374722857462059260211 377789318629571617095680 

noncomputable def Ns564p1949 := @Enclosure.Real.IsNear.neg_val qz295 274882575854225374744329 75557863725914323419136 374722857462059260211 377789318629571617095680 (Ns564p1948 (RS565to576.d58 qz188 qz206 qz294) RS565to576.d69) rfl 

noncomputable def Ns564p1950 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz188 959413 1000 970646 1000 

noncomputable def Ns564p1951 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 958281230415081343687 590295810358705651712 5844424010051473510661 

noncomputable def Ns564p1952 := @Ns564p1951 Ns564p85 446371901 10737418240 1213 10737418240 (Ns564p1946 (RS565to576.d4 qz188 qz206 qz294) RS565to576.d68) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable def Ns564p1953 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz206 959413 1000 972516 1000 

noncomputable def Ns564p1954 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 274882575854225374744329 75557863725914323419136 374722857462059260211 

noncomputable def Ns564p1955 := @Ns564p1954 377789318629571617095680 446371901 10737418240 1213 10737418240 (Ns564p1948 (RS565to576.d58 qz188 qz206 qz294) RS565to576.d69) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz567

noncomputable def Ns564p1956 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz188 970646 1000 qz191 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns564p1947 rfl rfl) (Ns564p1949 rfl rfl)) (Ns564p1950 qz11 qz191 rfl rfl rfl rfl (Ns564p1952 rfl)) (Ns564p1953 qz11 qz209 rfl rfl rfl rfl (Ns564p1955 rfl)) 

noncomputable abbrev qz735 := (@Enclosure.dec_le_dec qz786 qz791 972516 1000 973528 1000 qz789 qz794 rfl rfl rfl)

noncomputable abbrev qz569 := (RS565to576.d3 qz700 qz711 qz735)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz569)

noncomputable def Ns564p1957 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz206) Bool.true 274882575854225374744329 75557863725914323419136 374722857462059260211 377789318629571617095680 

noncomputable abbrev qz570 := qz735

noncomputable abbrev qz298 := qz570

noncomputable def Ns564p1958 := @Enclosure.Real.IsNear.neg_val qz297 274882575854225374744329 75557863725914323419136 374722857462059260211 377789318629571617095680 (Ns564p1957 (RS565to576.d4 qz206 qz223 qz298) RS565to576.d69) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz569)

noncomputable def Ns564p1959 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz223) Bool.false 35106133330937697635705 75557863725914323419136 23443794552531169042767 Ns564p1589 

noncomputable def Ns564p1960 := @Enclosure.Real.IsNear.pos_val qz299 35106133330937697635705 75557863725914323419136 23443794552531169042767 Ns564p1589 (Ns564p1959 (RS565to576.d58 qz206 qz223 qz298) RS565to576.d70) rfl 

noncomputable def Ns564p1961 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz206 959413 1000 972516 1000 

noncomputable def Ns564p1962 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 274882575854225374744329 75557863725914323419136 374722857462059260211 

noncomputable def Ns564p1963 := @Ns564p1962 377789318629571617095680 446371901 10737418240 1213 10737418240 (Ns564p1957 (RS565to576.d4 qz206 qz223 qz298) RS565to576.d69) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable def Ns564p1964 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz223 959413 1000 973528 1000 

noncomputable def Ns564p1965 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 35106133330937697635705 75557863725914323419136 23443794552531169042767 

noncomputable def Ns564p1966 := @Ns564p1965 Ns564p1589 446371901 10737418240 1213 10737418240 (Ns564p1959 (RS565to576.d58 qz206 qz223 qz298) RS565to576.d70) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz569

noncomputable def Ns564p1967 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz206 972516 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns564p1958 rfl rfl) (Ns564p1960 rfl rfl)) (Ns564p1961 qz11 qz209 rfl rfl rfl rfl (Ns564p1963 rfl)) (Ns564p1964 qz11 qz226 rfl rfl rfl rfl (Ns564p1966 rfl)) 

noncomputable abbrev qz801 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 973528 1000) (Enclosure.sfrac Bool.false 974151 1000) 973528 1000 974151 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 973528 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 974151 1000)) rfl rfl rfl)

noncomputable abbrev qz736 := qz801

noncomputable abbrev qz571 := (RS565to576.d3 qz711 qz722 qz736)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz571)

noncomputable def Ns564p1968 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz223) Bool.false 35106133330937697635705 75557863725914323419136 23443794552531169042767 Ns564p1589 

noncomputable abbrev qz572 := qz736

noncomputable abbrev qz302 := qz572

noncomputable def Ns564p1969 := @Enclosure.Real.IsNear.pos_val qz301 35106133330937697635705 75557863725914323419136 23443794552531169042767 Ns564p1589 (Ns564p1968 (RS565to576.d4 qz223 qz240 qz302) RS565to576.d70) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz571)

noncomputable def Ns564p1970 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz240) Bool.true 36351216173365039849207 75557863725914323419136 9383457302876000635589 Ns564p1714 

noncomputable def Ns564p1971 := @Enclosure.Real.IsNear.neg_val qz303 36351216173365039849207 75557863725914323419136 9383457302876000635589 Ns564p1714 (Ns564p1970 (RS565to576.d58 qz223 qz240 qz302) RS565to576.d71) rfl 

noncomputable def Ns564p1972 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz223 959413 1000 973528 1000 

noncomputable def Ns564p1973 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 35106133330937697635705 75557863725914323419136 23443794552531169042767 

noncomputable def Ns564p1974 := @Ns564p1973 Ns564p1589 446371901 10737418240 1213 10737418240 (Ns564p1968 (RS565to576.d4 qz223 qz240 qz302) RS565to576.d70) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable def Ns564p1975 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz240 959413 1000 974151 1000 

noncomputable def Ns564p1976 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 36351216173365039849207 75557863725914323419136 9383457302876000635589 

noncomputable def Ns564p1977 := @Ns564p1976 Ns564p1714 446371901 10737418240 1213 10737418240 (Ns564p1970 (RS565to576.d58 qz223 qz240 qz302) RS565to576.d71) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 446371901 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS565to576.d60) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz571

noncomputable def Ns564p1978 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz223 973528 1000 qz226 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns564p1969 rfl rfl) (Ns564p1971 rfl rfl)) (Ns564p1972 qz11 qz226 rfl rfl rfl rfl (Ns564p1974 rfl)) (Ns564p1975 qz11 qz243 rfl rfl rfl rfl (Ns564p1977 rfl)) 

noncomputable def Ns564p1979 := @List.cons RS565to576.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns564p1967)) (@List.cons RS565to576.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns564p1978)) (@List.nil RS565to576.d0)) 

noncomputable def Ns564p1980 := @List.cons RS565to576.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns564p1945)) (@List.cons RS565to576.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns564p1956)) Ns564p1979) 

noncomputable def Ns564p1981 := @List.cons RS565to576.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns564p1923)) (@List.cons RS565to576.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns564p1934)) Ns564p1980) 

noncomputable def Ns564p1982 := @List.cons RS565to576.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns564p1901)) (@List.cons RS565to576.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns564p1912)) Ns564p1981) 

noncomputable def Ns564p1983 := @List.cons RS565to576.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns564p1879)) (@List.cons RS565to576.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns564p1890)) Ns564p1982) 

noncomputable def Ns564p1984 := @List.cons RS565to576.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns564p1857)) (@List.cons RS565to576.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns564p1868)) Ns564p1983) 

noncomputable abbrev qz573 := (RS565to576.d2 qz680 qz690 qz733)

noncomputable abbrev qz737 := (RS565to576.d2 qz786 qz791 (@Enclosure.dec_le_dec qz786 qz791 972516 1000 973528 1000 qz789 qz794 rfl rfl rfl))

noncomputable abbrev qz738 := (@List.cons RS565to576.d1 (RS565to576.d2 qz791 qz796 qz801) (@List.nil RS565to576.d1))

noncomputable abbrev qz574 := (@List.cons RS565to576.d1 (RS565to576.d2 qz690 qz700 qz734) (@List.cons RS565to576.d1 qz737 qz738))

noncomputable abbrev qz305 := (@List.cons RS565to576.d1 (RS565to576.d2 qz474 qz487 qz564) (@List.cons RS565to576.d1 qz573 qz574))

noncomputable def Ns564p1985 := @List.cons RS565to576.d1 (RS565to576.d2 qz116 qz134 qz278) (@List.cons RS565to576.d1 (RS565to576.d2 qz134 qz152 qz282) qz305) 

noncomputable abbrev qz306 := (RS565to576.d2 qz435 qz448 qz558)

noncomputable def Ns564p1986 := @List.IsChain.cons_cons RS565to576.d1 RS565to576.d72 qz306 (RS565to576.d2 qz116 qz134 qz278) (@List.cons RS565to576.d1 (RS565to576.d2 qz134 qz152 qz282) qz305) 

noncomputable def Ns564p1987 := @List.IsChain.cons_cons RS565to576.d1 RS565to576.d72 (RS565to576.d2 qz116 qz134 qz278) (RS565to576.d2 qz134 qz152 qz282) qz305 (@Enclosure.dec_le_dec qz134 qz134 966905 1000 966905 1000 qz137 qz137 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS565to576.d2 qz474 qz487 qz564)

noncomputable abbrev qz308 := qz573

noncomputable abbrev qz309 := qz574

noncomputable abbrev qz575 := (RS565to576.d2 qz690 qz700 qz734)

noncomputable abbrev qz310 := qz575

noncomputable abbrev qz576 := (@List.cons RS565to576.d1 qz737 qz738)

noncomputable abbrev qz311 := qz576

noncomputable abbrev qz577 := qz737

noncomputable abbrev qz312 := qz577

noncomputable abbrev qz578 := qz738

noncomputable abbrev qz313 := qz578

noncomputable abbrev qz739 := (RS565to576.d2 qz791 qz796 qz801)

noncomputable abbrev qz579 := qz739

noncomputable abbrev qz314 := qz579

noncomputable def Ns564p1988 := @List.IsChain.cons_cons RS565to576.d1 RS565to576.d72 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz170 qz170 969399 1000 969399 1000 qz173 qz173 rfl rfl rfl) (@List.IsChain.cons_cons RS565to576.d1 RS565to576.d72 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz188 qz188 970646 1000 970646 1000 qz191 qz191 rfl rfl rfl) (@List.IsChain.cons_cons RS565to576.d1 RS565to576.d72 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz206 qz206 972516 1000 972516 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS565to576.d1 RS565to576.d72 qz312 qz314 (@List.nil RS565to576.d1) (@Enclosure.dec_le_dec qz223 qz223 973528 1000 973528 1000 qz226 qz226 rfl rfl rfl) (@List.IsChain.singleton RS565to576.d1 RS565to576.d72 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS565to576.d1 qz573 qz574)

noncomputable def Ns564p1989 := @List.IsChain.cons_cons RS565to576.d1 RS565to576.d72 (RS565to576.d2 qz134 qz152 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz152 qz152 968152 1000 968152 1000 qz155 qz155 rfl rfl rfl) Ns564p1988 

noncomputable def Ns564p1990 := @List.IsChain.cons_cons RS565to576.d1 RS565to576.d72 (RS565to576.d2 qz4 qz35 qz258) (RS565to576.d2 qz35 qz62 qz262) (@List.cons RS565to576.d1 (RS565to576.d2 qz62 qz80 qz266) (@List.cons RS565to576.d1 (RS565to576.d2 qz80 qz98 qz270) (@List.cons RS565to576.d1 qz306 Ns564p1985))) (@Enclosure.dec_le_dec qz35 qz35 960663 1000 960663 1000 qz38 qz38 rfl rfl rfl) (@List.IsChain.cons_cons RS565to576.d1 RS565to576.d72 (RS565to576.d2 qz35 qz62 qz262) (RS565to576.d2 qz62 qz80 qz266) (@List.cons RS565to576.d1 (RS565to576.d2 qz80 qz98 qz270) (@List.cons RS565to576.d1 qz306 Ns564p1985)) (@Enclosure.dec_le_dec qz62 qz62 962536 1000 962536 1000 qz65 qz65 rfl rfl rfl) (@List.IsChain.cons_cons RS565to576.d1 RS565to576.d72 (RS565to576.d2 qz62 qz80 qz266) (RS565to576.d2 qz80 qz98 qz270) (@List.cons RS565to576.d1 qz306 Ns564p1985) (@Enclosure.dec_le_dec qz80 qz80 963395 1000 963395 1000 qz83 qz83 rfl rfl rfl) (@List.IsChain.cons_cons RS565to576.d1 RS565to576.d72 (RS565to576.d2 qz80 qz98 qz270) qz306 Ns564p1985 (@Enclosure.dec_le_dec qz98 qz98 964019 1000 964019 1000 qz101 qz101 rfl rfl rfl) (Ns564p1986 (@Enclosure.dec_le_dec qz116 qz116 965657 1000 965657 1000 qz119 qz119 rfl rfl rfl) (Ns564p1987 Ns564p1989))))) 

noncomputable abbrev qz580 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz581 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns564p1984 Ns564p1990)

noncomputable abbrev qz582 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns564p1984 Ns564p1990))

theorem RS565to576.d73 : Zeta.Certificates.BatchSpec 12 959413 1000 974151 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz580 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz580 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz580 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz580 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz580 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz240)))) qz581 (@And.intro (@Eq Nat (@List.length qz580 qz582) 12) (And (@Eq (Option Real) (@Option.map qz580 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz580 qz582)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz580 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz580 qz582)) (@Option.some Real qz240))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz580 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz580 qz582)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz580 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz580 qz582)) (@Option.some Real qz240)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz240))))

theorem solution : Zeta.Certificates.BatchSpec 12 959413 1000 974151 1000 := RS565to576.d73
#print axioms solution
#check solution
